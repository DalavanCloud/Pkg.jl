# This file is a part of Julia. License is MIT: https://julialang.org/license

module REPLMode

using Markdown
using UUIDs

import REPL
import REPL: LineEdit, REPLCompletions

import ..devdir, ..Types.casesensitive_isdir, ..TOML
using ..Types, ..Display, ..Operations, ..API, ..Registry

#################
# Git revisions #
#################
struct Rev
    rev::String
end

###########
# Options #
###########
struct OptionSpec
    name::String
    short_name::Union{Nothing,String}
    api::Pair{Symbol, Any}
    takes_arg::Bool
end

@enum(OptionClass, OPT_ARG, OPT_SWITCH)
function OptionSpec(;name::String,
                    short_name::Union{Nothing,String}=nothing,
                    takes_arg::Bool=false,
                    api::Pair{Symbol,<:Any})::OptionSpec
    # TODO assert names matching lex regex
    # assert now so that you don't fail at user time
    # see function `REPLMode.APIOptions`
    takes_arg && @assert hasmethod(api.second, Tuple{String})
    return OptionSpec(name, short_name, api, takes_arg)
end

const OptionDeclaration = Vector{Pair{Symbol,Any}}
function OptionSpecs(decs::Vector{OptionDeclaration})::Dict{String, OptionSpec}
    specs = Dict()
    for x in decs
        opt_spec = OptionSpec(;x...)
        @assert get(specs, opt_spec.name, nothing) === nothing # don't overwrite
        specs[opt_spec.name] = opt_spec
        if opt_spec.short_name !== nothing
            @assert get(specs, opt_spec.short_name, nothing) === nothing # don't overwrite
            specs[opt_spec.short_name] = opt_spec
        end
    end
    return specs
end

struct Option
    val::String
    argument::Union{Nothing,String}
    Option(val::AbstractString) = new(val, nothing)
    Option(val::AbstractString, arg::Union{Nothing,String}) = new(val, arg)
end
Base.show(io::IO, opt::Option) = print(io, "--$(opt.val)", opt.argument == nothing ? "" : "=$(opt.argument)")

function parse_option(word::AbstractString)::Option
    m = match(r"^(?: -([a-z]) | --([a-z]{2,})(?:\s*=\s*(\S*))? )$"ix, word)
    m == nothing && pkgerror("malformed option: ", repr(word))
    option_name = (m.captures[1] != nothing ? m.captures[1] : m.captures[2])
    option_arg = (m.captures[3] == nothing ? nothing : String(m.captures[3]))
    return Option(option_name, option_arg)
end

################
# Command Spec #
################
@enum(CommandKind, CMD_HELP, CMD_RM, CMD_ADD, CMD_DEVELOP, CMD_UP,
                   CMD_STATUS, CMD_TEST, CMD_GC, CMD_BUILD, CMD_PIN,
                   CMD_FREE, CMD_GENERATE, CMD_RESOLVE, CMD_PRECOMPILE,
                   CMD_INSTANTIATE, CMD_ACTIVATE, CMD_PREVIEW,
                   CMD_REGISTRY_ADD, CMD_REGISTRY_RM, CMD_REGISTRY_UP, CMD_REGISTRY_STATUS,
                   )
@enum(ArgClass, ARG_RAW, ARG_PKG, ARG_VERSION, ARG_REV, ARG_ALL)
struct ArgSpec
    count::Pair
    parser::Function
end

const CommandDeclaration = Vector{Pair{Symbol,Any}}
struct CommandSpec
    kind::CommandKind
    canonical_name::String
    short_name::Union{Nothing,String}
    handler::Union{Nothing,Function}
    argument_spec::ArgSpec
    option_specs::Dict{String, OptionSpec}
    completions::Union{Nothing,Function}
    description::String
    help::Union{Nothing, Markdown.MD}
end

function SuperSpecs(compound_commands)::Dict{String,Dict{String,CommandSpec}}
    super_specs = Dict()
    for x in compound_commands
        sub_specs = CommandSpecs(x.second)
        name = x.first
        @assert get(super_specs, name, nothing) === nothing # don't overwrite commands
        super_specs[name] = sub_specs
    end
    return super_specs
end

function CommandSpec(;kind::Union{Nothing,CommandKind}=nothing,
                     name::String="",
                     short_name::Union{String,Nothing}=nothing,
                     handler::Union{Nothing,Function}=nothing,
                     option_spec::Vector{OptionDeclaration}=OptionDeclaration[],
                     help::Union{Nothing, Markdown.MD}=nothing,
                     description::String="",
                     completions::Union{Nothing,Function}=nothing,
                     arg_count::Pair=(0=>0),
                     arg_parser::Function=unwrap,
                     )::CommandSpec
    @assert kind !== nothing "Register and specify a `CommandKind`"
    @assert !isempty(name) "Supply a canonical name"
    @assert !isempty(description) "Supply a description"
    # TODO assert isapplicable completions dict, string
    return CommandSpec(kind, name, short_name, handler, ArgSpec(arg_count, arg_parser),
                       OptionSpecs(option_spec), completions, description, help)
end

# populate a dictionary: command_name -> command_spec
function CommandSpecs(declarations::Vector{CommandDeclaration})::Dict{String,CommandSpec}
    specs = Dict()
    for dec in declarations
        spec = CommandSpec(;dec...)
        specs[spec.canonical_name] = spec
        spec.short_name !== nothing && (specs[spec.short_name] = spec)
    end
    return specs
end

################
# REPL parsing #
################
struct QString
    raw::String
    isquoted::Bool
end

Base.@kwdef mutable struct Statement
    super::Union{Nothing, String}                  = nothing
    spec::Union{Nothing, CommandSpec}              = nothing
    options::Union{Vector{Option}, Vector{String}} = String[]
    arguments::Vector{QString}                     = QString[]
    preview::Bool                                  = false
end

unwrap(xs::Vector{QString}) = map(x -> x.raw, xs)
wrap_option(option::String)  = length(option) == 1 ? "-$option" : "--$option"
is_opt(word::AbstractString) = first(word) == '-' && word != "-"

############################
# Package/registry parsing #
############################
include(joinpath("REPL","argument_parsers.jl"))

function tokenize(cmd::String)
    cmd = replace(replace(cmd, "\r\n" => "; "), "\n" => "; ") # for multiline commands
    qstrings = lex(cmd)
    statements = foldl(qstrings; init=[QString[]]) do collection, next
        (next.raw == ";" && !next.isquoted) ?
            push!(collection, QString[]) :
            push!(collection[end], next)
        return collection
    end
    return statements
end

function core_parse(words::Vector{QString}; only_cmd=false)
    # prelude
    statement = Statement()
    word = nothing
    function next_word!()
        isempty(words) && return false
        word = popfirst!(words)
        return true
    end

    # begin parsing
    next_word!() || return statement, ((word === nothing) ? nothing : word.raw)
    if word.raw == "preview"
        statement.preview = true
        next_word!() || return statement, word.raw
    end

    super = get(super_specs, word.raw, nothing)
    if super !== nothing # explicit
        statement.super = word.raw
        next_word!() || return statement, word.raw
        command = get(super, word.raw, nothing)
        command !== nothing || return statement, word.raw
    else # try implicit package
        super = super_specs["package"]
        command = get(super, word.raw, nothing)
        command !== nothing || return statement, word.raw
    end
    statement.spec = command

    only_cmd && return statement, word.raw # hack to hook in `help` command

    next_word!() || return statement, word.raw

    while is_opt(word.raw)
        push!(statement.options, word.raw)
        next_word!() || return statement, word.raw
    end

    pushfirst!(words, word)
    statement.arguments = words
    return statement, words[end].raw
end

function parse(input::String)
    statements = Statement[]
    for words in tokenize(input)
        isempty(words) && continue
        statement, _ = core_parse(words)
        statement.spec === nothing && pkgerror("could not determine command")
        statement.options = map(parse_option, statement.options)
        push!(statements, statement)
    end
    return statements
end

function lex(cmd::String)::Vector{QString}
    in_doublequote = false
    in_singlequote = false
    qstrings = QString[]
    token_in_progress = Char[]

    push_token!(is_quoted) = begin
        push!(qstrings, QString(String(token_in_progress), is_quoted))
        empty!(token_in_progress)
    end

    for c in cmd
        if c == '"'
            if in_singlequote # raw char
                push!(token_in_progress, c)
            else # delimiter
                in_doublequote ? push_token!(true) : push_token!(false)
                in_doublequote = !in_doublequote
            end
        elseif c == '\''
            if in_doublequote # raw char
                push!(token_in_progress, c)
            else # delimiter
                in_singlequote ? push_token!(true) : push_token!(false)
                in_singlequote = !in_singlequote
            end
        elseif c == ' '
            if in_doublequote || in_singlequote # raw char
                push!(token_in_progress, c)
            else # delimiter
                push_token!(false)
            end
        elseif c == ';'
            if in_doublequote || in_singlequote # raw char
                push!(token_in_progress, c)
            else # special delimiter
                push_token!(false)
                push!(qstrings, QString(";", false))
            end
        else
            push!(token_in_progress, c)
        end
    end
    (in_doublequote || in_singlequote) ? pkgerror("unterminated quote") : push_token!(false)
    # to avoid complexity in the main loop, empty tokens are allowed above and
    # filtered out before returning
    return filter(x->!isempty(x.raw), qstrings)
end

###########
# Command #
###########
const APIOptions = Dict{Symbol, Any}
Base.@kwdef struct Command
    spec::Union{Nothing,CommandSpec} = nothing
    options::APIOptions              = APIOptions()
    arguments::Vector                = []
    preview::Bool                    = false
end

function APIOptions(options::Vector{Option},
                    specs::Dict{String, OptionSpec},
                    )::APIOptions
    api_options = Dict{Symbol, Any}()
    for option in options
        spec = specs[option.val]
        api_options[spec.api.first] = spec.takes_arg ?
            spec.api.second(option.argument) :
            spec.api.second
    end
    return api_options
end

function enforce_option(option::Option, specs::Dict{String,OptionSpec})
    spec = get(specs, option.val, nothing)
    spec !== nothing ||
        pkgerror("option '$(option.val)' is not a valid option")
    if spec.takes_arg
        option.argument !== nothing ||
            pkgerror("option '$(option.val)' expects an argument, but no argument given")
    else # option is a switch
        option.argument === nothing ||
            pkgerror("option '$(option.val)' does not take an argument, but '$(option.argument)' given")
    end
end

"""
checks:
- options are understood by the given command
- options do not conflict (e.g. `rm --project --manifest`)
- options which take an argument are given arguments
- options which do not take arguments are not given arguments
"""
function enforce_option(options::Vector{Option}, specs::Dict{String,OptionSpec})
    unique_keys = Symbol[]
    get_key(opt::Option) = specs[opt.val].api.first

    # per option checking
    foreach(x->enforce_option(x,specs), options)
    # checking for compatible options
    for opt in options
        key = get_key(opt)
        if key in unique_keys
            conflicting = filter(opt->get_key(opt) == key, options)
            pkgerror("Conflicting options: $conflicting")
        else
            push!(unique_keys, key)
        end
    end
end

"""
Final parsing (and checking) step.
This step is distinct from `parse` in that it relies on the command specifications.
"""
function Command(statement::Statement)::Command
    arg_spec = statement.spec.argument_spec
    opt_spec = statement.spec.option_specs
    # arguments
    arguments = arg_spec.parser(statement.arguments)
    if !(arg_spec.count.first <= length(arguments) <= arg_spec.count.second)
        pkgerror("Wrong number of arguments")
    end
    # options
    enforce_option(statement.options, opt_spec)
    options = APIOptions(statement.options, opt_spec)
    return Command(statement.spec, options, arguments, statement.preview)
end

Context!(ctx::APIOptions)::Context = Types.Context!(collect(ctx))

#############
# Execution #
#############
function do_cmd(repl::REPL.AbstractREPL, input::String; do_rethrow=false)
    try
        statements = parse(input)
        commands   = map(Command, statements)
        foreach(cmd -> do_cmd!(cmd, repl), commands)
    catch err
        do_rethrow && rethrow()
        if err isa PkgError || err isa ResolverError
            Base.display_error(repl.t.err_stream, ErrorException(sprint(showerror, err)), Ptr{Nothing}[])
        else
            Base.display_error(repl.t.err_stream, err, Base.catch_backtrace())
        end
    end
end

function do_cmd!(command::Command, repl)
    context = Dict{Symbol,Any}(:preview => command.preview)

    # REPL specific commands
    if command.spec.kind == CMD_HELP
        return Base.invokelatest(do_help!, command, repl)
    end

    # API commands
    # TODO is invokelatest still needed?
    if applicable(command.spec.handler, context, command.arguments, command.options)
        Base.invokelatest(command.spec.handler, context, command.arguments, command.options)
    else
        Base.invokelatest(command.spec.handler, command.arguments, command.options)
    end
end

function parse_command(words::Vector{QString})
    statement, word = core_parse(words; only_cmd=true)
    if statement.super === nothing && statement.spec === nothing
        pkgerror("invalid input: `$word` is not a command")
    end
    return statement.spec === nothing ?  statement.super : statement.spec
end

function do_help!(command::Command, repl::REPL.AbstractREPL)
    disp = REPL.REPLDisplay(repl)
    if isempty(command.arguments)
        Base.display(disp, help)
        return
    end
    help_md = md""

    cmd = parse_command(command.arguments)
    if cmd isa String
        # gather all helps for super spec `cmd`
        all_specs = sort!(unique(values(super_specs[cmd]));
                          by=(spec->spec.canonical_name))
        for spec in all_specs
            isempty(help_md.content) || push!(help_md.content, md"---")
            push!(help_md.content, spec.help)
        end
    elseif cmd isa CommandSpec
        push!(help_md.content, cmd.help)
    end
    !isempty(command.arguments) && @warn "More than one command specified, only rendering help for first"
    Base.display(disp, help_md)
end

# TODO set default Display.status keyword: mode = PKGMODE_COMBINED
do_status!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.status(Context!(ctx), args, mode=get(api_opts, :mode, PKGMODE_COMBINED))

# TODO , test recursive dependencies as on option.
function do_test!(ctx::APIOptions, args::Vector, api_opts::APIOptions)
    foreach(arg -> arg.mode = PKGMODE_MANIFEST, args)
    API.test(Context!(ctx), args; collect(api_opts)...)
end

do_precompile!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.precompile(Context!(ctx))

do_resolve!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.resolve(Context!(ctx))

do_gc!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.gc(Context!(ctx); collect(api_opts)...)

do_instantiate!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.instantiate(Context!(ctx); collect(api_opts)...)

do_generate!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.generate(Context!(ctx), args[1])

do_build!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.build(Context!(ctx), args; collect(api_opts)...)

do_rm!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.rm(Context!(ctx), args; collect(api_opts)...)

do_free!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.free(Context!(ctx), args; collect(api_opts)...)

do_up!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.up(Context!(ctx), args; collect(api_opts)...)

function do_activate!(args::Vector, api_opts::APIOptions)
    if isempty(args)
        API.activate()
    else
        API.activate(expanduser(args[1]); collect(api_opts)...)
    end
end

function do_pin!(ctx::APIOptions, args::Vector, api_opts::APIOptions)
    for arg in args
        # TODO not sure this is correct
        if arg.version.ranges[1].lower != arg.version.ranges[1].upper
            pkgerror("pinning a package requires a single version, not a versionrange")
        end
    end
    API.pin(Context!(ctx), args; collect(api_opts)...)
end

do_add!(ctx::APIOptions, args::Vector, api_opts::APIOptions) = 
    API.add(Context!(ctx), args; collect(api_opts)...)

do_develop!(ctx::APIOptions, args::Vector, api_opts::APIOptions) =
    API.develop(Context!(ctx), args; collect(api_opts)...)

# registry commands
function do_registry_add!(ctx::APIOptions, args::Vector, api_opts::APIOptions)
    Registry.add(Context!(ctx), args)
end

function do_registry_rm!(ctx::APIOptions, args::Vector, api_opts::APIOptions)
    Registry.rm(Context!(ctx), args)
end

function do_registry_up!(ctx::APIOptions, args::Vector, api_opts::APIOptions)
    if isempty(args)
        return Registry.update(Context!(ctx))
    else
        return Registry.update(Context!(ctx), args)
    end
end

function do_registry_status!(#=ctx::APIOptions,=# args::Vector, api_opts::APIOptions)
    return Registry.status()
end

######################
# REPL mode creation #
######################

# Provide a string macro pkg"cmd" that can be used in the same way
# as the REPLMode `pkg> cmd`. Useful for testing and in environments
# where we do not have a REPL, e.g. IJulia.
struct MiniREPL <: REPL.AbstractREPL
    display::TextDisplay
    t::REPL.Terminals.TTYTerminal
end
function MiniREPL()
    MiniREPL(TextDisplay(stdout), REPL.Terminals.TTYTerminal(get(ENV, "TERM", Sys.iswindows() ? "" : "dumb"), stdin, stdout, stderr))
end
REPL.REPLDisplay(repl::MiniREPL) = repl.display


const minirepl = Ref{MiniREPL}()

__init__() = minirepl[] = MiniREPL()

macro pkg_str(str::String)
    :($(do_cmd)(minirepl[], $str; do_rethrow=true))
end

pkgstr(str::String) = do_cmd(minirepl[], str; do_rethrow=true)

struct PkgCompletionProvider <: LineEdit.CompletionProvider end

function LineEdit.complete_line(c::PkgCompletionProvider, s)
    partial = REPL.beforecursor(s.input_buffer)
    full = LineEdit.input_string(s)
    ret, range, should_complete = completions(full, lastindex(partial))
    return ret, partial[range], should_complete
end

#######################
# COMMAND COMPLETIONS #
#######################
function complete_activate(options, partial, i1, i2)
    possible = String[]
    shared = get(options, :shared, false)
    if shared
        for depot in Base.DEPOT_PATH
            envdir = joinpath(depot, "environments")
            isdir(envdir) || continue
            append!(possible, readdir(envdir))
        end
        return possible
    else
        return complete_local_dir(partial, i1, i2)
    end
end

function complete_local_dir(s, i1, i2)
    if !isempty(s) && s[1] == '~'
        return String[expanduser(s)], i1:i2, true
    end

    cmp = REPL.REPLCompletions.complete_path(s, i2)
    completions = [REPL.REPLCompletions.completion_text(p) for p in cmp[1]]
    completions = filter!(x -> isdir(s[1:prevind(s, first(cmp[2])-i1+1)]*x), completions)
    return completions, cmp[2], !isempty(completions)
end

function complete_remote_package(partial)
    cmp = String[]
    julia_version = VERSION
    for reg in Types.collect_registries()
        data = Types.read_registry(joinpath(reg.path, "Registry.toml"))
        for (uuid, pkginfo) in data["packages"]
            name = pkginfo["name"]
            if startswith(name, partial)
                compat_data = Operations.load_package_data_raw(
                    VersionSpec, joinpath(reg.path, pkginfo["path"], "Compat.toml"))
                supported_julia_versions = VersionSpec(VersionRange[])
                for (ver_range, compats) in compat_data
                    for (compat, v) in compats
                        if compat == "julia"
                            union!(supported_julia_versions, VersionSpec(v))
                        end
                    end
                end
                if VERSION in supported_julia_versions
                    push!(cmp, name)
                end
            end
        end
    end
    return cmp
end

function canonical_names()
    # add "package" commands
    xs = [(spec.canonical_name => spec) for spec in unique(values(super_specs["package"]))]
    sort!(xs, by=first)
    # add other super commands, e.g. "registry"
    for (super, specs) in super_specs
        super != "package" || continue # skip "package"
        temp = [(join([super, spec.canonical_name], " ") => spec) for spec in unique(values(specs))]
        append!(xs, sort!(temp, by=first))
    end
    return xs
end

function complete_help(options, partial)
    names = String[]
    for cmds in values(super_specs)
         append!(names, [spec.canonical_name for spec in values(cmds)])
    end
    return sort!(unique!(append!(names, collect(keys(super_specs)))))
end

function complete_installed_packages(options, partial)
    env = try EnvCache()
    catch err
        err isa PkgError || rethrow()
        return String[]
    end
    mode = get(options, :mode, PKGMODE_PROJECT)
    return mode == PKGMODE_PROJECT ?
        collect(keys(env.project.deps)) :
        unique!([entry.name for (uuid, entry) in env.manifest])
end

function complete_add_dev(options, partial, i1, i2)
    comps, idx, _ = complete_local_dir(partial, i1, i2)
    if occursin(Base.Filesystem.path_separator_re, partial)
        return comps, idx, !isempty(comps)
    end
    comps = vcat(comps, complete_remote_package(partial))
    comps = vcat(comps, filter(x->startswith(x,partial) && !(x in comps),
                               collect(values(Types.stdlib()))))
    return comps, idx, !isempty(comps)
end

function default_commands()
    names = collect(keys(super_specs))
    append!(names, map(x -> getproperty(x, :canonical_name), values(super_specs["package"])))
    return sort(unique(names))
end

########################
# COMPLETION INTERFACE #
########################
function complete_command(statement::Statement, final::Bool, on_sub::Bool)
    if statement.super !== nothing
        if (!on_sub && final) || (on_sub && !final)
            # last thing determined was the super -> complete canonical names of subcommands
            specs = super_specs[statement.super]
            names = map(x -> getproperty(x, :canonical_name), values(specs))
            return sort(unique(names))
        end
    end
    # complete default names
    return default_commands()
end

complete_opt(opt_specs) =
    unique(sort(map(wrap_option,
                    map(x -> getproperty(x, :name),
                        collect(values(opt_specs))))))

function complete_argument(spec::CommandSpec,
                           options::Vector{String},
                           partial::AbstractString,
                           offset::Int,
                           index::Int,
                           )
    if spec.completions === nothing
        return String[]
    end
    # finish parsing opts
    opts = APIOptions(map(parse_option, options), spec.option_specs)
    if applicable(spec.completions, opts, partial, offset, index)
        return spec.completions(opts, partial, offset, index)
    end
    return spec.completions(opts, partial)
end

function _completions(input, final, offset, index)
    words = tokenize(input)[end]
    word_count = length(words)
    statement, partial = core_parse(words)
    final && (partial = "") # last token is finalized -> no partial
    # number of tokens which specify the command
    command_size = count([statement.preview, statement.super !== nothing, true])
    command_is_focused() = !((word_count == command_size && final) || word_count > command_size)

    if statement.spec === nothing # spec not determined -> complete command
        !command_is_focused() && return String[], 0:-1, false
        x = complete_command(statement, final, word_count == (statement.preview ? 3 : 2))
    else
        command_is_focused() && return String[], 0:-1, false

        if final # complete arg by default
            x = complete_argument(statement.spec, statement.options, partial, offset, index)
        else # complete arg or opt depending on last token
            x = is_opt(partial) ?
                complete_opt(statement.spec.option_specs) :
                complete_argument(statement.spec, statement.options, partial, offset, index)
        end
    end

    # In the case where the completion function wants to deal with indices, it will return a fully
    # computed completion tuple, just return it
    # Else, the completions function will just deal with strings and will return a Vector{String}
    if isa(x, Tuple)
        return x
    else
        possible = filter(possible -> startswith(possible, partial), x)
        return possible, offset:index, !isempty(possible)
    end
end

function completions(full, index)::Tuple{Vector{String},UnitRange{Int},Bool}
    pre = full[1:index]
    # empty input -> complete commands
    if isempty(pre)
        return default_commands(), 0:-1, false
    end
    # parse input
    last = split(pre, ' ', keepempty=true)[end]
    offset = isempty(last) ? index+1 : last.offset+1
    final = isempty(last) # is the cursor still attached to the final token?
    return _completions(pre, final, offset, index)
end

prev_project_file = nothing
prev_project_timestamp = nothing
prev_prefix = ""

function promptf()
    global prev_project_timestamp, prev_prefix, prev_project_file
    project_file = try
        Types.find_project_file()
    catch
        nothing
    end
    prefix = ""
    if project_file !== nothing
        if prev_project_file == project_file && prev_project_timestamp == mtime(project_file)
            prefix = prev_prefix
        else
            project = try
                Types.read_project(project_file)
            catch
                nothing
            end
            if project !== nothing
                projname = project.name
                if projname !== nothing
                    name = projname
                else
                    name = basename(dirname(project_file))
                end
                prefix = string("(", name, ") ")
                prev_prefix = prefix
                prev_project_timestamp = mtime(project_file)
                prev_project_file = project_file
            end
        end
    end
    return prefix * "pkg> "
end

# Set up the repl Pkg REPLMode
function create_mode(repl, main)
    pkg_mode = LineEdit.Prompt(promptf;
        prompt_prefix = repl.options.hascolor ? Base.text_colors[:blue] : "",
        prompt_suffix = "",
        complete = PkgCompletionProvider(),
        sticky = true)

    pkg_mode.repl = repl
    hp = main.hist
    hp.mode_mapping[:pkg] = pkg_mode
    pkg_mode.hist = hp

    search_prompt, skeymap = LineEdit.setup_search_keymap(hp)
    prefix_prompt, prefix_keymap = LineEdit.setup_prefix_keymap(hp, pkg_mode)

    pkg_mode.on_done = (s, buf, ok) -> begin
        ok || return REPL.transition(s, :abort)
        input = String(take!(buf))
        REPL.reset(repl)
        do_cmd(repl, input)
        REPL.prepare_next(repl)
        REPL.reset_state(s)
        s.current_mode.sticky || REPL.transition(s, main)
    end

    mk = REPL.mode_keymap(main)

    shell_mode = nothing
    for mode in Base.active_repl.interface.modes
        if mode isa LineEdit.Prompt
            mode.prompt == "shell> " && (shell_mode = mode)
        end
    end

    repl_keymap = Dict()
    if shell_mode != nothing
        repl_keymap[';'] = function (s,o...)
            if isempty(s) || position(LineEdit.buffer(s)) == 0
                buf = copy(LineEdit.buffer(s))
                LineEdit.transition(s, shell_mode) do
                    LineEdit.state(s, shell_mode).input_buffer = buf
                end
            else
                LineEdit.edit_insert(s, ';')
            end
        end
    end

    b = Dict{Any,Any}[
        skeymap, repl_keymap, mk, prefix_keymap, LineEdit.history_keymap,
        LineEdit.default_keymap, LineEdit.escape_defaults
    ]
    pkg_mode.keymap_dict = LineEdit.keymap(b)
    return pkg_mode
end

function repl_init(repl)
    main_mode = repl.interface.modes[1]
    pkg_mode = create_mode(repl, main_mode)
    push!(repl.interface.modes, pkg_mode)
    keymap = Dict{Any,Any}(
        ']' => function (s,args...)
            if isempty(s) || position(LineEdit.buffer(s)) == 0
                buf = copy(LineEdit.buffer(s))
                LineEdit.transition(s, pkg_mode) do
                    LineEdit.state(s, pkg_mode).input_buffer = buf
                end
            else
                LineEdit.edit_insert(s, ']')
            end
        end
    )
    main_mode.keymap_dict = LineEdit.keymap_merge(main_mode.keymap_dict, keymap)
    return
end

########
# SPEC #
########
include(joinpath("REPL", "command_declarations.jl"))
super_specs = SuperSpecs(command_declarations)

function gen_help()
    help = md"""
**Welcome to the Pkg REPL-mode**. To return to the `julia>` prompt, either press
backspace when the input line is empty or press Ctrl+C.

**Synopsis**

    pkg> cmd [opts] [args]

Multiple commands can be given on the same line by interleaving a `;` between the commands.

**Commands**
"""
    for (command, spec) in canonical_names()
        push!(help.content, Markdown.parse("`$command`: $(spec.description)"))
    end
    return help
end

const help = gen_help()

end #module
