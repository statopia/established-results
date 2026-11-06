import Lean
import Mathlib

namespace PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529

-- Shared append-only definitions for the root theorem and every Math node.
-- Node Formalize may add def/abbrev/structure/class/inductive declarations here.

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

/-- The matrix unit `e_i e_jᵀ ∈ ℝ^{m×n}`: the matrix with a single `1` at position `(i,j)`. -/
def matrixUnit {m n : ℕ} (i : Fin m) (j : Fin n) : Matrix (Fin m) (Fin n) ℝ :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- The coordinate vector `g_{ij} = ((b_p)_{ij})_{p=1}^{D} ∈ ℝ^D` of the family
`b : Fin D → ℝ^{m×n}` at the entry `(i,j)`. -/
def tangentCoords {m n D : ℕ} (b : Fin D → Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n) : Fin D → ℝ :=
  fun p => b p i j

end Statlib.Imported

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

/-- The real-valued entropy `Ent_tau(phi) = ∫ x, phi x * Real.log (phi x) ∂tau - m * Real.log m`
of a nonnegative function `phi` under the measure `tau`, where `m = ∫ x, phi x ∂tau`.
The convention `0 * Real.log 0 = 0` holds in Lean since `Real.log 0 = 0`. -/
noncomputable def entReal {α : Type*} [MeasurableSpace α] (τ : MeasureTheory.Measure α)
    (φ : α → ℝ) : ℝ :=
  (∫ x, φ x * Real.log (φ x) ∂τ) - (∫ x, φ x ∂τ) * Real.log (∫ x, φ x ∂τ)

/-- The entropy block of a nonnegative function `phi` under the measure `tau`, encoded in
`ENNReal`.  With `m = ∫ x, phi x ∂tau`, `P = ∫⁻ x, ENNReal.ofReal (phi x * Real.log (phi x))
∂tau` and `N = ∫⁻ x, ENNReal.ofReal (-(phi x * Real.log (phi x))) ∂tau`, it is defined as
`(P + ENNReal.ofReal (-(m * Real.log m))) - (N + ENNReal.ofReal (m * Real.log m))`
(subtraction in `ENNReal` is the truncated subtraction).  When `phi` is measurable, nonnegative
and integrable and the Gibbs inequality holds (so that the truncated subtraction does not
truncate), this is the `ENNReal` encoding of the extended-real entropy
`Ent_tau(phi) = ∫ x, phi x * Real.log (phi x) ∂tau - m * Real.log m ∈ [0, inf]`. -/
noncomputable def entBlock {α : Type*} [MeasurableSpace α] (τ : MeasureTheory.Measure α)
    (φ : α → ℝ) : ENNReal :=
  ((∫⁻ x, ENNReal.ofReal (φ x * Real.log (φ x)) ∂τ) +
      ENNReal.ofReal (-((∫ x, φ x ∂τ) * Real.log (∫ x, φ x ∂τ))))
    - ((∫⁻ x, ENNReal.ofReal (-(φ x * Real.log (φ x))) ∂τ) +
        ENNReal.ofReal ((∫ x, φ x ∂τ) * Real.log (∫ x, φ x ∂τ)))

end Statlib.Imported

