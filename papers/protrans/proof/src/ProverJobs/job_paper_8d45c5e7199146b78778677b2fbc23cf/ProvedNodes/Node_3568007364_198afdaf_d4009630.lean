import Lean
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Vocabulary
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Base

namespace PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_3568007364_198afdaf : ∀ {ι : Type} (s : Finset ι) (w A : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hA : ∀ i ∈ s, 0 ≤ A i) (m : ℕ) (hm : 1 ≤ m),
    (∑ i ∈ s, w i * A i) ^ m ≤ (∑ i ∈ s, w i) ^ (m - 1) * ∑ i ∈ s, w i * (A i) ^ m := by
  /- @proof-region region.target-node.session.732b4a5860b3eb0f begin -/
  intro ι s w A hw hA m hm
  by_cases hW0 : ∑ i ∈ s, w i = 0
  · have hw0 : ∀ i ∈ s, w i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => hw i hi)).1 hW0
    have hS : ∑ i ∈ s, w i * A i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hw0 i hi, zero_mul]
    have hS' : ∑ i ∈ s, w i * (A i) ^ m = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hw0 i hi, zero_mul]
    rw [hS, hS', hW0]
    simp [show m ≠ 0 by omega]
  · have hWpos : 0 < ∑ i ∈ s, w i :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun i hi => hw i hi)) (Ne.symm hW0)
    have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ m) := convexOn_pow m
    have hp_nn : ∀ i ∈ s, 0 ≤ w i / (∑ j ∈ s, w j) :=
      fun i hi => div_nonneg (hw i hi) hWpos.le
    have hp_sum : ∑ i ∈ s, w i / (∑ j ∈ s, w j) = 1 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      field_simp [hWpos.ne']
    have hmem : ∀ i ∈ s, A i ∈ Set.Ici (0 : ℝ) :=
      fun i hi => (show (0 : ℝ) ≤ A i from hA i hi)
    have hJ := hconv.map_sum_le (t := s) (w := fun i => w i / (∑ j ∈ s, w j)) (p := A)
      hp_nn hp_sum hmem
    change (∑ i ∈ s, w i / (∑ j ∈ s, w j) * A i) ^ m
      ≤ ∑ i ∈ s, w i / (∑ j ∈ s, w j) * (A i) ^ m at hJ
    have hL : ∑ i ∈ s, w i / (∑ j ∈ s, w j) * A i
        = (∑ i ∈ s, w i * A i) / (∑ j ∈ s, w j) := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hR : ∑ i ∈ s, w i / (∑ j ∈ s, w j) * (A i) ^ m
        = (∑ i ∈ s, w i * (A i) ^ m) / (∑ j ∈ s, w j) := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hL, hR] at hJ
    have hJ2 : (∑ i ∈ s, w i * A i) ^ m / (∑ j ∈ s, w j) ^ m
        ≤ (∑ i ∈ s, w i * (A i) ^ m) / (∑ j ∈ s, w j) := by
      simpa [div_pow] using hJ
    have hP : (∑ i ∈ s, w i * A i) ^ m
        ≤ ((∑ i ∈ s, w i * (A i) ^ m) / (∑ j ∈ s, w j)) * (∑ j ∈ s, w j) ^ m :=
      (div_le_iff₀ (pow_pos hWpos m)).mp hJ2
    have hEq : ((∑ i ∈ s, w i * (A i) ^ m) / (∑ j ∈ s, w j)) * (∑ j ∈ s, w j) ^ m
        = (∑ j ∈ s, w j) ^ (m - 1) * (∑ i ∈ s, w i * (A i) ^ m) := by
      have hWpow : (∑ j ∈ s, w j) ^ m
          = (∑ j ∈ s, w j) ^ (m - 1) * (∑ j ∈ s, w j) := by
        conv_lhs => rw [show m = (m - 1) + 1 from (Nat.sub_add_cancel hm).symm]
        rw [pow_succ]
      rw [hWpow]
      field_simp [hWpos.ne'] <;> ring
    rw [hEq] at hP
    exact hP
  /- @proof-region region.target-node.session.732b4a5860b3eb0f end -/

end Statlib.Imported

