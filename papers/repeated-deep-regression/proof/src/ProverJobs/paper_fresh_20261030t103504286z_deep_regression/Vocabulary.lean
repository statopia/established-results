import Lean
import Mathlib

namespace PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression

-- Shared append-only definitions for the root theorem and every Math node.
-- Node Formalize may add def/abbrev/structure/class/inductive declarations here.

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

/-- The Rademacher law on `ℝ`: the uniform distribution on `{-1, 1}`. -/
noncomputable def rademacherLaw : MeasureTheory.Measure ℝ :=
  (1 / 2 : ENNReal) •
    (MeasureTheory.Measure.dirac (-1 : ℝ) + MeasureTheory.Measure.dirac (1 : ℝ))

/-- The finite-class Rademacher supremum
`sup_{f ∈ Fs} |(nm)⁻¹ ∑_{i,j} σ_ij ω * (f (X_ij ω) - f° (X_ij ω))|`,
with value `0` for the empty class (the sup over the empty set in `ℝ`). -/
noncomputable def rademacherFiniteSup {ΩS Ω : Type*} {n m : ℕ}
    (X : Fin n × Fin m → ΩS → Ω) (f0 : Ω → ℝ)
    (sigma : Fin n × Fin m → ΩS → ℝ) (ω : ΩS) (Fs : Finset (Ω → ℝ)) : ℝ :=
  ⨆ f ∈ (Fs : Set (Ω → ℝ)),
    |(1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, sigma ij ω * (f (X ij ω) - f0 (X ij ω))|

end Statlib.Imported

