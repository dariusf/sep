Sep is a small and extensible separation logic library.
It was inspired by CFML/Separation Logic Foundations and includes a number of generalisations and extensions.

- LibFmap: a small overlay for mathlib's Finmap, adding more lemmas
- FmapTactics: solvers for disjointness goals and finite map equalities
- HProp: separation logic heap propositions, parametric over some type of values using a typeclass, and with nice notation
- Xsimpl: provides the xsimpl tactic, which simplifies and solves separation logic entailments
- FrameInference: extends xsimpl with biabduction
- SymExec: extends frame inference with Infer-style biabductive symbolic execution
- Hoare: a Hoare triple interface to symbolic execution

How xsimpl works

xsimpl iterates the following phases, with normalization at the start and between each phase:

- Normalization associates separating conjunction and wands to the right, removes emp, turns pure propositions into existentials, float existentials. It is interleaved between each step and produces the rough normal form `∃ x, ∃ (_: pure), H ✶ (H1 -✶ H2)`
- Extraction: this pulls existentials and pure facts on the left into the proof context
- Instantiation: instantiates existentials on the right with metavariables (hopefully to be solved using unification) and turns pure facts into subgoals
- Cancellation: bubble each matching atom on the left and right (seen as ✶-delimited lists) to the front and cancels them
- Cancellation of wands: forward-chaining on the left

It may not solve goals and will leave them in a simplified state.
Unrecognised atoms (shape predicates, metavariables) will be ignored.

Extensibility

xsimpl_core_with allows specifying what happens to ignored atoms.

For example, xsimpl_granular_frames extends it with biabduction, via two more iterated phases, xsimpl_abduce_step and xsimpl_frame_step, which handle metavariables on the left and right respectively.
To use xsimpl_frame_step as an example, if no more cancellation can take place and there is a metavariable on the right, xsimpl_frame_step will unify it with `atom_from_the_left ✶ ?new_var`.
The atom will then be cancelled by a subsequent iteration, and the process repeats until we have `emp ✶ ?antiframe ==> emp ✶ ?frame`.
This "granular" approach allows the frame and anti-frame can be simultaneously inferred; otherwise, both metavariables could unify with each other.

SymExec

This adds rules for forall/wand, which are needed for Hoare triples.
sym_exec works only with concrete pre- and postconditions while sym_exec_abduce allows biabduction.
