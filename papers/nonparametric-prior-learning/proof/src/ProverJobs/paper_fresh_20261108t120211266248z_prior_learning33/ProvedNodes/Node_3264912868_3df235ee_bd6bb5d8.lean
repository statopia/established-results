import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3264912868_3df235ee : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : Type*) (bH : HilbertBasis ι ℝ H) (mu : ι → ℝ)
    (hmu : ∀ i : ι, 0 < mu i)
    (t : ℝ) (a b : H)
    (ha : HScaleNorm bH mu t a < ⊤) (hb : HScaleNorm bH mu t b < ⊤),
    HScaleNorm bH mu t (a - b) < ⊤ := by
  /- @proof-region region.target-node.session.5f0c5433e7e641cb begin -/
  intro H _ _ _ ι bH mu hmu t a b ha hb
  have hpoint : ∀ i : ι,
      ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) (a - b)) ^ 2)
        ≤ (ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2)
            + ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2))
          + (ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2)
            + ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2)) := by
    intro i
    have hc0 : 0 ≤ Real.rpow (mu i) (-t) := Real.rpow_nonneg (le_of_lt (hmu i)) (-t)
    have hx : 0 ≤ (inner ℝ (bH i) a) ^ 2 := sq_nonneg _
    have hy : 0 ≤ (inner ℝ (bH i) b) ^ 2 := sq_nonneg _
    have hcx : 0 ≤ Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2 := mul_nonneg hc0 hx
    have hcy : 0 ≤ Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2 := mul_nonneg hc0 hy
    have hinner : inner ℝ (bH i) (a - b) = inner ℝ (bH i) a - inner ℝ (bH i) b := inner_sub_right (bH i) a b
    have hsq : (inner ℝ (bH i) a - inner ℝ (bH i) b) ^ 2
        ≤ 2 * (inner ℝ (bH i) a) ^ 2 + 2 * (inner ℝ (bH i) b) ^ 2 := by
      nlinarith [sq_nonneg (inner ℝ (bH i) a + inner ℝ (bH i) b)]
    have hbound : Real.rpow (mu i) (-t) * (inner ℝ (bH i) (a - b)) ^ 2
        ≤ (Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2 + Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2)
          + (Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2 + Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2) := by
      rw [hinner]
      have h1 : Real.rpow (mu i) (-t) * (inner ℝ (bH i) a - inner ℝ (bH i) b) ^ 2
          ≤ Real.rpow (mu i) (-t) * (2 * (inner ℝ (bH i) a) ^ 2 + 2 * (inner ℝ (bH i) b) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hc0
      nlinarith [h1]
    calc ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) (a - b)) ^ 2)
        ≤ ENNReal.ofReal ((Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2 + Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2)
            + (Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2 + Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2)) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = (ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2) + ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2))
            + (ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2) + ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2)) := by
          rw [ENNReal.ofReal_add (by linarith [hcx]) (by linarith [hcy]),
              ENNReal.ofReal_add hcx hcx, ENNReal.ofReal_add hcy hcy]
  have hle : HScaleNorm bH mu t (a - b)
      ≤ (HScaleNorm bH mu t a + HScaleNorm bH mu t a)
        + (HScaleNorm bH mu t b + HScaleNorm bH mu t b) := by
    unfold HScaleNorm
    calc ∑' i, ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) (a - b)) ^ 2)
        ≤ ∑' i, ((ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2)
              + ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2))
            + (ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2)
              + ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2))) :=
          ENNReal.tsum_le_tsum hpoint
      _ = (∑' i, ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2)
            + ∑' i, ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) a) ^ 2))
          + (∑' i, ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2)
            + ∑' i, ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2)) := by
          simp only [ENNReal.tsum_add]
  have hfin : (HScaleNorm bH mu t a + HScaleNorm bH mu t a)
      + (HScaleNorm bH mu t b + HScaleNorm bH mu t b) < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ha, ha⟩, ENNReal.add_lt_top.mpr ⟨hb, hb⟩⟩
  exact lt_of_le_of_lt hle hfin
  /- @proof-region region.target-node.session.5f0c5433e7e641cb end -/

end Statlib.Imported
end

