import Lean
import Mathlib

namespace PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315

-- Shared append-only definitions for the root theorem and every Math node.
-- Node Formalize may add def/abbrev/structure/class/inductive declarations here.

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

/-- The paper's combined-vector map, taken on the array families evaluated at a single
outcome `ω` together with the means.  Its `j`-th coordinate is
`n^{-1/2} ∑_i x_{ij} - n^{1/2} μX_j + d (m^{-1/2} ∑_i y_{ij}) - d m^{1/2} μY_j`,
i.e. the `ω`-level form of the Base.lean combined vectors `partXY` (with the `X`/`Y`
arrays) and `partFG` (with the `F`/`G` arrays). -/
noncomputable def combVec {n m p : ℕ} (d : ℝ) (μX μY : Fin p → ℝ)
    (xs : Fin n → (Fin p → ℝ)) (ys : Fin m → (Fin p → ℝ)) : Fin p → ℝ :=
  fun j => (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, xs i j - Real.sqrt (n : ℝ) * μX j
            + d * ((Real.sqrt (m : ℝ))⁻¹ * ∑ i : Fin m, ys i j)
            - d * Real.sqrt (m : ℝ) * μY j

end Statlib.Imported

