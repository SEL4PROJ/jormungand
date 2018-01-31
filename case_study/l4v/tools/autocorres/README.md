Note to maintainer: sync with tools/release_files/README

AutoCorres
==========

AutoCorres is a tool that assists reasoning about C programs
in [Isabelle/HOL][1]. In particular, it uses Norrish's
[C-to-Isabelle parser][2] to parse C into Isabelle, and then
abstracts the result to produce a result that is (hopefully)
more pleasant to reason about.

  [1]: https://www.cl.cam.ac.uk/research/hvg/Isabelle/
  [2]: https://ssrg.nicta.com.au/software/TS/c-parser/



Contents of this README
-----------------------

  * Installation
  * Quickstart
  * Development and reporting bugs
  * Options
  * Examples
  * Publications



Installation
------------

AutoCorres is packaged as a theory for Isabelle2016-1:

    https://isabelle.in.tum.de

To build it, type

    isabelle build -d . AutoCorres

in the root of the L4v repository. This builds the C parser and AutoCorres itself.
There is also a test suite, which can be run using:

    make AutoCorresTest

in tools/autocorres.



Quickstart
----------

A brief tutorial can be found in doc/quickstart.
Run `make AutoCorresDoc` to generate a readable PDF document of
the tutorial.



Development and reporting bugs
------------------------------

AutoCorres is currently maintained by Japheth Lim <Japheth.Lim@nicta.com.au>.

Additionally, the latest development version is available on GitHub
as part of the L4.verified project:

    https://github.com/seL4/l4v (in tools/autocorres)



Options
-------

AutoCorres supports a variety of options, which are used as follows:

    autocorres [option, key=val, list=a b c d] "path/to/file.c"

`path/to/file.c` is the same path given to `install_C_file`, and
AutoCorres will define the translated functions in the C-parser's
generated locale (named `file`).

The options are:

  * `no_heap_abs = FUNC_NAMES`: Disable _heap abstraction_
    on the given list of functions.

  * `force_heap_abs = FUNC_NAMES`: Attempt _heap abstraction_
    on the given list of functions, even if AutoCorres' heuristics
    believes that they cannot be lifted.

  * `heap_abs_syntax`: Enable experimental heap abstraction
    syntactic sugar.

  * `skip_heap_abs`: Completely disable _heap abstraction_.

  * `unsigned_word_abs = FUNC_NAMES`: Use _word abstraction_
    on unsigned integers in the given functions.

  * `no_signed_word_abs = FUNC_NAMES`: Disable signed
    _word abstraction_ on the given list of functions.

  * `skip_word_abs`: Completely disable _word abstraction_.

  * `ts_rules = RULES`: Enable _type strengthening_ to the
    following types. Possible types include `pure` (pure
    functional), `option` (option monad without state), `gets` (option
    monad with state) and `nondet` (non-deterministic state monad).

  * `ts_force RULE_NAME = FUNC_NAMES`: Force the given
    functions to be type-strengthened to the given type,
    even if a "better" type could otherwise be used.
    See `tests/examples/type_strengthen_tricks.thy`.

  * `scope = FUNC_NAMES`: Only translate the given functions
    and their callees, up to depth `scope_depth`.
    AutoCorres can be invoked multiple times to translate
    parts of a program. See `tests/examples/Incremental.thy`.

  * `scope_depth = N`: Call depth for `scope`.

Name compatibility options (see `tests/examples/AC_Rename.thy`):

  * `lifted_globals_field_prefix="foo"`, `lifted_globals_field_suffix="foo"`:
    Override generated names for global variables during heap abstraction.
    The default is `f` -> `f_''` (i.e. prefix="", suffix="_''").

  * `function_name_prefix="foo"`, `function_name_suffix="foo"`:
    Override generated names for abstracted functions.
    The default is `f` -> `f'` (i.e. prefix="", suffix="'").

Less common options (mainly for debugging):

  * `keep_going`: Attempt to ignore certain non-critical
    errors.

  * `trace_heap_lift = FUNC_NAMES`: Trace the _heap abstraction_
    process for each of the given functions. The traces
    are stored in the Isabelle theory and can be quite large.
    See `tests/examples/TraceDemo.thy`.

  * `trace_word_abs = FUNC_NAMES`: As above, but traces
    _word abstraction_.

  * `trace_opt`: As above, but traces internal simplification
    phases (for all functions).

  * `no_opt`: Disable some optimisation passes that simplify
    the AutoCorres output.

  * `gen_word_heaps`: Force _heap abstraction_ to create
    abstract heaps for standard `word` types
    (`word8`, `word16`, `word32`, `word64`) even if they
    are not needed.

The following options are for interfacing with the seL4 proofs.

  * `c_locale = NAME`: Run in this locale, rather than the default locale
    created by the C-parser. This locale must behave like the C-parser
    one except that the function bodies may be different.

  * `no_c_termination`: Generate SIMPL wrappers and correspondence
    proofs that do not require program termination for the SIMPL source.

An example of invoking AutoCorres with _all_ of the options
is as follows:

    autocorres [
        no_heap_abs = a b,
        force_heap_abs = c d,
        gen_word_heaps,
        skip_heap_abs,  (* mutually exclusive with previous options *)
        heap_abs_syntax,

        unsigned_word_abs = f g h,
        no_signed_word_abs = i j k,
        skip_word_abs,  (* mutually exclusive with previous options *)

        ts_rules = pure nondet,
        ts_force nondet = l m n,

        scope = o p q,
        scope_depth = 5,
        keep_going,
        c_locale = "my_locale",
        no_c_termination,
        trace_heap_lift = c d,
        trace_word_abs = f h i,
        no_opt,

        lifted_globals_field_prefix="my_global_",
        lifted_globals_field_suffix="",
        function_name_prefix="my_func_",
        function_name_suffix=""
        ] "filename.c"



Examples
--------

Some examples are in the `tests/examples` directory.

Many of these examples are quick-and-dirty proofs, and should not
necessary be considered the best style.

None-the-less, some of the examples available are, in approximate
increasing level of difficulty:

  * `Simple.thy`: Proofs of some simple functions, including
    `max` and `gcd`.

  * `Swap.thy`: Proof of a simple `swap` function.

  * `MultByAdd.thy`: Proof of a function that carries out
    multiplication using addition.

  * `Factorial.thy`: Proof of a factorial function, using
    several different methods.

  * `FibProof.thy`: Proof of the Fibonacci function, using
    several different methods.

  * `ListRev.thy`: Proof of a function that carries out an
    in-place linked list reversal.

  * `CList.thy`: Another list reversal, based on a proof by
    Mehta and Nipkow. See [the paper][3].

  * `IsPrime.thy`: Proof of a function that determines if
    the input number is prime.

  * `Memset.thy`: Proof of a C `memset` implementation.

  * `Quicksort.thy`: Proof of a simple quicksort
    implementation on an array of `int`s.

  * `BinarySearch.thy`: Proof of a function that determines
    if a sorted input array of `unsigned int` contains the
    given `unsigned int`.

  * `SchorrWaite.thy`: Proof a C implementation of the
    Schorr-Waite algorithm, using Mehta and Nipkow's
    high-level proof. See [the paper][3].

  * `Memcpy.thy`: Proof of a C `memcpy` implementation.
    The proof connects the C parser's byte-level heap
    with AutoCorres's type-safe heap representation.

There are also some examples that aren't about program proofs,
but demonstrate AutoCorres features:

  * `AC_Rename.thy`: how to change AutoCorres-generated names.

  * `TraceDemo.thy`: how to use the (experimental) tracing.

  * `type_strengthen_tricks.thy`: configuring type-strengthening.

  * `Incremental.thy`: (experimental) support for incremental translation.



Publications
------------

L1 (SimplConv), L2 (LocalVarExtract) and TS (TypeStrengthen) were described in

    "Bridging the gap: Automatic verified abstraction of C"
    David Greenaway, June Andronick, Gerwin Klein
    Proceedings of the Third International
            Conference on Interactive Theorem Proving (ITP), August 2012.
    https://ssrg.nicta.com.au/publications/nictaabstracts/5662.pdf

HL (heap abstraction) and WA (word abstraction) were described in

  [3]:
    "Don’t sweat the small stuff --- Formal verification of C code without the pain"
    David Greenaway, Japheth Lim, June Andronick, Gerwin Klein
    Proceedings of the 35th ACM SIGPLAN Conference on
            Programming Language Design and Implementation. ACM, June 2014.
    https://ssrg.nicta.com.au/publications/nictaabstracts/7629.pdf

A more comprehensive source is

    "Automated proof-producing abstraction of C code"
    David Greenaway
    PhD thesis, March 2015.
    https://ssrg.nicta.com.au/publications/nictaabstracts/8758.pdf
