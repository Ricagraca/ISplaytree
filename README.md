## Building

### Step 1: Creating an opam switch

_If opam is not already installed:_ See instructions [there][install-opam] to
install it; then:

    opam init --comp=4.09.1
    eval $(opam config env)

(This will create a `~/.opam` directory.)

_If opam is already installed:_ Create a new switch for the project:

    opam switch iris-time-proofs --alias-of 4.09.1                  # for opam 1.x
    opam switch create iris-time-proofs ocaml-base-compiler.4.09.1  # for opam 2.x
    eval $(opam config env)

### Step 2: Installing the dependencies

In an opam switch as created above, the commands

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    make build-dep

will pin and install the dependencies at the correct version.

If you want to browse the Coq development using CoqIDE (a graphical, interactive
toplevel for Coq), install it as well:

    opam install coqide

### Step 3: Compiling the proof scripts

When all required libraries can be found (e.g. in an opam switch as configured
above), compile the proof scripts with:

    make -j4

Other recipes are available, such as `all`, `clean` and `userinstall`.

To create an archive of the project:

    ./make_archive.sh

[install-opam]: https://opam.ocaml.org/doc/Install.html

## Index of modules

Important modules are highlighted.

 *  `Misc`: some basic things
 *  `Auth_nat`, `Auth_max_nat`: simple lemmas about the authoritative resources on
    (ℕ, +) and (ℕ, max)
 *  `heap_lang/` directory: the toy language under study
 *  `Reduction`: generic lemmas about reduction, safety, closedness, fresh
    locations…
 *  `Tactics`: helper tactics to reduce concrete terms
 *  __`Translation`: definition of the translation and syntactic lemmas about
    it__
 *  __`Simulation`: generic definition of `tick`; operational lemmas about the
    translation with that `tick`__
 *  __`TimeCredits`: interface, implementation, and proof of soundness for time
    credits (plus proof-mode tactics `wp_tick_*`)__
 *  __`TimeCreditsAltProofs`: alternative proofs for the soundness theorem of
    time credits__
 *  __`TimeReceipts`: interface, implementation, and proof of soundness for time
    receipts, both exclusive and persistent (plus proof-mode tactics)__
 *  __`Combined`: logical system providing both time credits and time receipts
    at the same time__
 *  `Examples`: a very simple example illustrating the use of time credits to
    specify a program with lists
 *  __`Thunks`: implementation of timed thunks using time credits__
 *  __`ClockIntegers`: reconstruction of Clochard’s integer types (`onetime` and
    `peano`) using time receipts__
 *  __`union_find/` directory: application of the combined system to a
    union-find program__

### From ESOP paper to Coq proofs

#### Generic translation and “tick”

The basic properties of the translation are proven in `Translation.v` (for
example, `translation_subst`).

In `Simulation.v`:

 *  Lemma 1 (“Reduction Preservation”) is `simulation_exec_success`.
 *  Lemma 2 (“Immediate Safety Preservation”) is `safe_translation__safe_here`.
 *  Lemma 3 (“Safety Preservation”) is `adequate_translation__nadequate` (in the
    Coq development, by contrast with the paper, not only do we prove safety of
    programs, but also their _adequacy_ with respect to some formula φ; this is
    not a difficult property to transfer anyway).

#### Time credits

In `TimeCredits.v`:

 *  Lemma 4 (“Credit Exhaustion”) is `simulation_step_failure`.
 *  Lemma 5 (“Safety Preservation, Strengthened”) is presented in
    `TimeCreditsAltProofs.v`, as `adequate_tctranslation__nadequate`; the main
    development in `TimeCredits.v` uses a slightly weaker version, named
    `adequate_tctranslation__adequate_and_bounded`.
 *  Lemma 6 (“Time Credit Initialization”) does not have an exact counterpart in
    the Coq development, but corresponds roughly to a portion of the proof of
    `spec_tctranslation__adequate_translation`. The fact that our implementation
    matches the interface is stated by `TC_implementation`.
 *  Theorem 1 (“Soundness of Iris^$ ”) is
    `abstract_spec_tctranslation__adequate_and_bounded`.

#### Time receipts

In `TimeReceipts.v`:

 *  Lemma 7 (“Time Receipt Initialization”) lemma does not have an exact
    counterpart in the Coq development, but corresponds roughly to a portion of
    the proof of `spec_trtranslation__adequate_translation`. The fact that our
    implementation matches the interface is stated by `TR_implementation`.
 *  Theorem 2 (“Soundness of Iris^⧗ ”) is
    `abstract_spec_trtranslation__adequate`.

#### Marrying time credits and time receipts

In `Combined.v`:

 *  Theorem 3 (“Soundness of Iris^$⧗ ”) is `tctr_sound_abstract`.
# ISplaytree
# ISplaytree
