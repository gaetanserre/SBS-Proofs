### SBS Proofs
Lean 4 proofs associated with the paper [Stein Boltzmann Sampling: A Variational Approach for Global Optimization](https://proceedings.mlr.press/v258/serre25a.html) by G. Serré, A. Kalogeratos, and N. Vayatis.

We formalized the definition of a generic RKHS and the induced product RKHS in [RKHS.Basic.lean](SBSProofs/RKHS/Basic.lean). We created the `DensityMeasure` typeclass, that encapsulates a measure and its density w.r.t. the Lebesgue measure, and we proved classical measure theory results using either this typeclass or standard Lean's measure that was not available yet in Mathlib. See [Measure.lean](SBSProofs/Measure.lean) for the definition of the typeclass and the proofs.

#### Usage
- Install Lean. See instruction [here](https://leanprover-community.github.io/get_started.html);
- Clone the repo;
- Run `lake exe cache get`;
- Visualize the proofs using the extension for Emacs or Visual Studio Code, or use the `.html` files.
