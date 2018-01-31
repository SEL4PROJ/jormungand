(*:maxLineLen=78:*)

theory Sessions
imports Base
begin

chapter \<open>Isabelle sessions and build management \label{ch:session}\<close>

text \<open>
  An Isabelle \<^emph>\<open>session\<close> consists of a collection of related theories that may
  be associated with formal documents (\chref{ch:present}). There is also a
  notion of \<^emph>\<open>persistent heap\<close> image to capture the state of a session,
  similar to object-code in compiled programming languages. Thus the concept
  of session resembles that of a ``project'' in common IDE environments, but
  the specific name emphasizes the connection to interactive theorem proving:
  the session wraps-up the results of user-interaction with the prover in a
  persistent form.

  Application sessions are built on a given parent session, which may be built
  recursively on other parents. Following this path in the hierarchy
  eventually leads to some major object-logic session like \<open>HOL\<close>, which itself
  is based on \<open>Pure\<close> as the common root of all sessions.

  Processing sessions may take considerable time. Isabelle build management
  helps to organize this efficiently. This includes support for parallel build
  jobs, in addition to the multithreaded theory and proof checking that is
  already provided by the prover process itself.
\<close>


section \<open>Session ROOT specifications \label{sec:session-root}\<close>

text \<open>
  Session specifications reside in files called \<^verbatim>\<open>ROOT\<close> within certain
  directories, such as the home locations of registered Isabelle components or
  additional project directories given by the user.

  The ROOT file format follows the lexical conventions of the \<^emph>\<open>outer syntax\<close>
  of Isabelle/Isar, see also @{cite "isabelle-isar-ref"}. This defines common
  forms like identifiers, names, quoted strings, verbatim text, nested
  comments etc. The grammar for @{syntax session_chapter} and @{syntax
  session_entry} is given as syntax diagram below; each ROOT file may contain
  multiple specifications like this. Chapters help to organize browser info
  (\secref{sec:info}), but have no formal meaning. The default chapter is
  ``\<open>Unsorted\<close>''.

  Isabelle/jEdit @{cite "isabelle-jedit"} includes a simple editing mode
  \<^verbatim>\<open>isabelle-root\<close> for session ROOT files, which is enabled by default for any
  file of that name.

  @{rail \<open>
    @{syntax_def session_chapter}: @'chapter' @{syntax name}
    ;

    @{syntax_def session_entry}: @'session' spec '=' (@{syntax name} '+')? body
    ;
    body: description? options? (theories+) \<newline> files? (document_files*)
    ;
    spec: @{syntax name} groups? dir?
    ;
    groups: '(' (@{syntax name} +) ')'
    ;
    dir: @'in' @{syntax name}
    ;
    description: @'description' @{syntax text}
    ;
    options: @'options' opts
    ;
    opts: '[' ( (@{syntax name} '=' value | @{syntax name}) + ',' ) ']'
    ;
    value: @{syntax name} | @{syntax real}
    ;
    theories: @'theories' opts? ( @{syntax name} * )
    ;
    files: @'files' (@{syntax name}+)
    ;
    document_files: @'document_files' ('(' dir ')')? (@{syntax name}+)
  \<close>}

  \<^descr> \isakeyword{session}~\<open>A = B + body\<close> defines a new session \<open>A\<close> based on
  parent session \<open>B\<close>, with its content given in \<open>body\<close> (theories and auxiliary
  source files). Note that a parent (like \<open>HOL\<close>) is mandatory in practical
  applications: only Isabelle/Pure can bootstrap itself from nothing.

  All such session specifications together describe a hierarchy (tree) of
  sessions, with globally unique names. The new session name \<open>A\<close> should be
  sufficiently long and descriptive to stand on its own in a potentially large
  library.

  \<^descr> \isakeyword{session}~\<open>A (groups)\<close> indicates a collection of groups where
  the new session is a member. Group names are uninterpreted and merely follow
  certain conventions. For example, the Isabelle distribution tags some
  important sessions by the group name called ``\<open>main\<close>''. Other projects may
  invent their own conventions, but this requires some care to avoid clashes
  within this unchecked name space.

  \<^descr> \isakeyword{session}~\<open>A\<close>~\isakeyword{in}~\<open>dir\<close> specifies an explicit
  directory for this session; by default this is the current directory of the
  \<^verbatim>\<open>ROOT\<close> file.

  All theories and auxiliary source files are located relatively to the
  session directory. The prover process is run within the same as its current
  working directory.

  \<^descr> \isakeyword{description}~\<open>text\<close> is a free-form annotation for this
  session.

  \<^descr> \isakeyword{options}~\<open>[x = a, y = b, z]\<close> defines separate options
  (\secref{sec:system-options}) that are used when processing this session,
  but \<^emph>\<open>without\<close> propagation to child sessions. Note that \<open>z\<close> abbreviates \<open>z =
  true\<close> for Boolean options.

  \<^descr> \isakeyword{theories}~\<open>options names\<close> specifies a block of theories that
  are processed within an environment that is augmented by the given options,
  in addition to the global session options given before. Any number of blocks
  of \isakeyword{theories} may be given. Options are only active for each
  \isakeyword{theories} block separately.

  \<^descr> \isakeyword{files}~\<open>files\<close> lists additional source files that are involved
  in the processing of this session. This should cover anything outside the
  formal content of the theory sources. In contrast, files that are loaded
  formally within a theory, e.g.\ via @{command "ML_file"}, need not be
  declared again.

  \<^descr> \isakeyword{document_files}~\<open>(\<close>\isakeyword{in}~\<open>base_dir) files\<close> lists
  source files for document preparation, typically \<^verbatim>\<open>.tex\<close> and \<^verbatim>\<open>.sty\<close> for
  {\LaTeX}. Only these explicitly given files are copied from the base
  directory to the document output directory, before formal document
  processing is started (see also \secref{sec:tool-document}). The local path
  structure of the \<open>files\<close> is preserved, which allows to reconstruct the
  original directory hierarchy of \<open>base_dir\<close>.

  \<^descr> \isakeyword{document_files}~\<open>files\<close> abbreviates
  \isakeyword{document_files}~\<open>(\<close>\isakeyword{in}~\<open>document) files\<close>, i.e.\
  document sources are taken from the base directory \<^verbatim>\<open>document\<close> within the
  session root directory.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  See \<^file>\<open>~~/src/HOL/ROOT\<close> for a diversity of practically relevant situations,
  although it uses relatively complex quasi-hierarchic naming conventions like
  \<^verbatim>\<open>HOL-SPARK\<close>, \<^verbatim>\<open>HOL-SPARK-Examples\<close>. An alternative is to use unqualified
  names that are relatively long and descriptive, as in the Archive of Formal
  Proofs (\<^url>\<open>http://afp.sourceforge.net\<close>), for example.
\<close>


section \<open>System build options \label{sec:system-options}\<close>

text \<open>
  See \<^file>\<open>~~/etc/options\<close> for the main defaults provided by the Isabelle
  distribution. Isabelle/jEdit @{cite "isabelle-jedit"} includes a simple
  editing mode \<^verbatim>\<open>isabelle-options\<close> for this file-format.

  The following options are particularly relevant to build Isabelle sessions,
  in particular with document preparation (\chref{ch:present}).

    \<^item> @{system_option_def "browser_info"} controls output of HTML browser
    info, see also \secref{sec:info}.

    \<^item> @{system_option_def "document"} specifies the document output format,
    see @{tool document} option \<^verbatim>\<open>-o\<close> in \secref{sec:tool-document}. In
    practice, the most relevant values are \<^verbatim>\<open>document=false\<close> or
    \<^verbatim>\<open>document=pdf\<close>.

    \<^item> @{system_option_def "document_output"} specifies an alternative
    directory for generated output of the document preparation system; the
    default is within the @{setting "ISABELLE_BROWSER_INFO"} hierarchy as
    explained in \secref{sec:info}. See also @{tool mkroot}, which generates a
    default configuration with output readily available to the author of the
    document.

    \<^item> @{system_option_def "document_variants"} specifies document variants as
    a colon-separated list of \<open>name=tags\<close> entries, corresponding to @{tool
    document} options \<^verbatim>\<open>-n\<close> and \<^verbatim>\<open>-t\<close>.

    For example, \<^verbatim>\<open>document_variants=document:outline=/proof,/ML\<close> indicates
    two documents: the one called \<^verbatim>\<open>document\<close> with default tags, and the other
    called \<^verbatim>\<open>outline\<close> where proofs and ML sections are folded.

    Document variant names are just a matter of conventions. It is also
    possible to use different document variant names (without tags) for
    different document root entries, see also \secref{sec:tool-document}.

    \<^item> @{system_option_def "threads"} determines the number of worker threads
    for parallel checking of theories and proofs. The default \<open>0\<close> means that a
    sensible maximum value is determined by the underlying hardware. For
    machines with many cores or with hyperthreading, this is often requires
    manual adjustment (on the command-line or within personal settings or
    preferences, not within a session \<^verbatim>\<open>ROOT\<close>).

    \<^item> @{system_option_def "checkpoint"} helps to fine-tune the global heap
    space management. This is relevant for big sessions that may exhaust the
    small 32-bit address space of the ML process (which is used by default).
    When the option is enabled for some \isakeyword{theories} block, a full
    sharing stage of immutable values in memory happens \<^emph>\<open>before\<close> loading the
    specified theories.

    \<^item> @{system_option_def "condition"} specifies a comma-separated list of
    process environment variables (or Isabelle settings) that are required for
    the subsequent theories to be processed. Conditions are considered
    ``true'' if the corresponding environment value is defined and non-empty.

    \<^item> @{system_option_def "timeout"} and @{system_option_def "timeout_scale"}
    specify a real wall-clock timeout for the session as a whole: the two
    values are multiplied and taken as the number of seconds. Typically,
    @{system_option "timeout"} is given for individual sessions, and
    @{system_option "timeout_scale"} as global adjustment to overall hardware
    performance.

    The timer is controlled outside the ML process by the JVM that runs
    Isabelle/Scala. Thus it is relatively reliable in canceling processes that
    get out of control, even if there is a deadlock without CPU time usage.

    \<^item> @{system_option_def "profiling"} specifies a mode for global ML
    profiling. Possible values are the empty string (disabled), \<^verbatim>\<open>time\<close> for
    @{ML profile_time} and \<^verbatim>\<open>allocations\<close> for @{ML profile_allocations}.
    Results appear near the bottom of the session log file.

  The @{tool_def options} tool prints Isabelle system options. Its
  command-line usage is:
  @{verbatim [display]
\<open>Usage: isabelle options [OPTIONS] [MORE_OPTIONS ...]

  Options are:
    -b           include $ISABELLE_BUILD_OPTIONS
    -g OPTION    get value of OPTION
    -l           list options
    -x FILE      export to FILE in YXML format

  Report Isabelle system options, augmented by MORE_OPTIONS given as
  arguments NAME=VAL or NAME.\<close>}

  The command line arguments provide additional system options of the form
  \<open>name\<close>\<^verbatim>\<open>=\<close>\<open>value\<close> or \<open>name\<close> for Boolean options.

  Option \<^verbatim>\<open>-b\<close> augments the implicit environment of system options by the ones
  of @{setting ISABELLE_BUILD_OPTIONS}, cf.\ \secref{sec:tool-build}.

  Option \<^verbatim>\<open>-g\<close> prints the value of the given option. Option \<^verbatim>\<open>-l\<close> lists all
  options with their declaration and current value.

  Option \<^verbatim>\<open>-x\<close> specifies a file to export the result in YXML format, instead
  of printing it in human-readable form.
\<close>


section \<open>Invoking the build process \label{sec:tool-build}\<close>

text \<open>
  The @{tool_def build} tool invokes the build process for Isabelle sessions.
  It manages dependencies between sessions, related sources of theories and
  auxiliary files, and target heap images. Accordingly, it runs instances of
  the prover process with optional document preparation. Its command-line
  usage is:\<^footnote>\<open>Isabelle/Scala provides the same functionality via
  \<^verbatim>\<open>isabelle.Build.build\<close>.\<close>
  @{verbatim [display]
\<open>Usage: isabelle build [OPTIONS] [SESSIONS ...]

  Options are:
    -D DIR       include session directory and select its sessions
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -R           operate on requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -k KEYWORD   check theory sources for conflicts with proposed keywords
    -l           list session source files
    -n           no build -- test dependencies only
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s           system build mode: produce output in ISABELLE_HOME
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and manage Isabelle sessions, depending on implicit settings:

  ISABELLE_BUILD_OPTIONS="..."

  ML_PLATFORM="..."
  ML_HOME="..."
  ML_SYSTEM="..."
  ML_OPTIONS="..."\<close>}

  \<^medskip>
  Isabelle sessions are defined via session ROOT files as described in
  (\secref{sec:session-root}). The totality of sessions is determined by
  collecting such specifications from all Isabelle component directories
  (\secref{sec:components}), augmented by more directories given via options
  \<^verbatim>\<open>-d\<close>~\<open>DIR\<close> on the command line. Each such directory may contain a session
  \<^verbatim>\<open>ROOT\<close> file with several session specifications.

  Any session root directory may refer recursively to further directories of
  the same kind, by listing them in a catalog file \<^verbatim>\<open>ROOTS\<close> line-by-line. This
  helps to organize large collections of session specifications, or to make
  \<^verbatim>\<open>-d\<close> command line options persistent (say within
  \<^verbatim>\<open>$ISABELLE_HOME_USER/ROOTS\<close>).

  \<^medskip>
  The subset of sessions to be managed is determined via individual \<open>SESSIONS\<close>
  given as command-line arguments, or session groups that are given via one or
  more options \<^verbatim>\<open>-g\<close>~\<open>NAME\<close>. Option \<^verbatim>\<open>-a\<close> selects all sessions. The build tool
  takes session dependencies into account: the set of selected sessions is
  completed by including all ancestors.

  \<^medskip>
  One or more options \<^verbatim>\<open>-x\<close>~\<open>NAME\<close> specify sessions to be excluded. All
  descendents of excluded sessions are removed from the selection as specified
  above. Option \<^verbatim>\<open>-X\<close> is analogous to this, but excluded sessions are
  specified by session group membership.

  \<^medskip>
  Option \<^verbatim>\<open>-R\<close> reverses the selection in the sense that it refers to its
  requirements: all ancestor sessions excluding the original selection. This
  allows to prepare the stage for some build process with different options,
  before running the main build itself (without option \<^verbatim>\<open>-R\<close>).

  \<^medskip>
  Option \<^verbatim>\<open>-D\<close> is similar to \<^verbatim>\<open>-d\<close>, but selects all sessions that are defined
  in the given directories.

  \<^medskip>
  The build process depends on additional options
  (\secref{sec:system-options}) that are passed to the prover eventually. The
  settings variable @{setting_ref ISABELLE_BUILD_OPTIONS} allows to provide
  additional defaults, e.g.\ \<^verbatim>\<open>ISABELLE_BUILD_OPTIONS="document=pdf threads=4"\<close>.
  Moreover, the environment of system build options may be augmented on the
  command line via \<^verbatim>\<open>-o\<close>~\<open>name\<close>\<^verbatim>\<open>=\<close>\<open>value\<close> or \<^verbatim>\<open>-o\<close>~\<open>name\<close>, which abbreviates
  \<^verbatim>\<open>-o\<close>~\<open>name\<close>\<^verbatim>\<open>=true\<close> for Boolean options. Multiple occurrences of \<^verbatim>\<open>-o\<close> on
  the command-line are applied in the given order.

  \<^medskip>
  Option \<^verbatim>\<open>-b\<close> ensures that heap images are produced for all selected
  sessions. By default, images are only saved for inner nodes of the hierarchy
  of sessions, as required for other sessions to continue later on.

  \<^medskip>
  Option \<^verbatim>\<open>-c\<close> cleans all descendants of the selected sessions before
  performing the specified build operation.

  \<^medskip>
  Option \<^verbatim>\<open>-n\<close> omits the actual build process after the preparatory stage
  (including optional cleanup). Note that the return code always indicates the
  status of the set of selected sessions.

  \<^medskip>
  Option \<^verbatim>\<open>-j\<close> specifies the maximum number of parallel build jobs (prover
  processes). Each prover process is subject to a separate limit of parallel
  worker threads, cf.\ system option @{system_option_ref threads}.

  \<^medskip>
  Option \<^verbatim>\<open>-N\<close> enables cyclic shuffling of NUMA CPU nodes. This may help
  performance tuning on Linux servers with separate CPU/memory modules.

  \<^medskip>
  Option \<^verbatim>\<open>-s\<close> enables \<^emph>\<open>system mode\<close>, which means that resulting heap images
  and log files are stored in @{path "$ISABELLE_HOME/heaps"} instead of the
  default location @{setting ISABELLE_OUTPUT} (which is normally in @{setting
  ISABELLE_HOME_USER}, i.e.\ the user's home directory).

  \<^medskip>
  Option \<^verbatim>\<open>-v\<close> increases the general level of verbosity. Option \<^verbatim>\<open>-l\<close> lists
  the source files that contribute to a session.

  \<^medskip>
  Option \<^verbatim>\<open>-k\<close> specifies a newly proposed keyword for outer syntax (multiple
  uses allowed). The theory sources are checked for conflicts wrt.\ this
  hypothetical change of syntax, e.g.\ to reveal occurrences of identifiers
  that need to be quoted.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Build a specific logic image:
  @{verbatim [display] \<open>isabelle build -b HOLCF\<close>}

  \<^smallskip>
  Build the main group of logic images:
  @{verbatim [display] \<open>isabelle build -b -g main\<close>}

  \<^smallskip>
  Provide a general overview of the status of all Isabelle sessions, without
  building anything:
  @{verbatim [display] \<open>isabelle build -a -n -v\<close>}

  \<^smallskip>
  Build all sessions with HTML browser info and PDF document preparation:
  @{verbatim [display] \<open>isabelle build -a -o browser_info -o document=pdf\<close>}

  \<^smallskip>
  Build all sessions with a maximum of 8 parallel prover processes and 4
  worker threads each (on a machine with many cores):
  @{verbatim [display] \<open>isabelle build -a -j8 -o threads=4\<close>}

  \<^smallskip>
  Build some session images with cleanup of their descendants, while retaining
  their ancestry:
  @{verbatim [display] \<open>isabelle build -b -c HOL-Algebra HOL-Word\<close>}

  \<^smallskip>
  Clean all sessions without building anything:
  @{verbatim [display] \<open>isabelle build -a -n -c\<close>}

  \<^smallskip>
  Build all sessions from some other directory hierarchy, according to the
  settings variable \<^verbatim>\<open>AFP\<close> that happens to be defined inside the Isabelle
  environment:
  @{verbatim [display] \<open>isabelle build -D '$AFP'\<close>}

  \<^smallskip>
  Inform about the status of all sessions required for AFP, without building
  anything yet:
  @{verbatim [display] \<open>isabelle build -D '$AFP' -R -v -n\<close>}
\<close>

end
