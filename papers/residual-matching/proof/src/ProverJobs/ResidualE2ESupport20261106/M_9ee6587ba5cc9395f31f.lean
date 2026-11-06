import Statlib.HighDim.MatrixAnalysis.FrobeniusNormSvdRelation
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_270675543_d5eed0a7 : ∀ (m n : ℕ) (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B)
    (M A : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ (i : Fin m) (j : Fin n), M i j = 0 ∨ M i j = 1)
    (hA : ∀ (i : Fin m) (j : Fin n), |A i j| ≤ B),
    @norm (Matrix (Fin m) (Fin n) ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm
      ((fun i j => M i j * A i j / Real.sqrt ((m : ℝ) * p)) : Matrix (Fin m) (Fin n) ℝ)
      ≤ Real.sqrt ((n : ℝ) / p) * B := by
  /- @proof-region region.target-node.session.4755e91d6bdd9cd8 begin -/
  intro m n p B hp hB M A hM hA
  set c : ℝ := Real.sqrt ((m : ℝ) * p) with hc
  set T : Matrix (Fin m) (Fin n) ℝ := (fun i j => M i j * A i j / c) with hT
  change ‖T‖ ≤ Real.sqrt ((n : ℝ) / p) * B
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hT0 : T = 0 := by
      funext i
      exact i.elim0
    rw [hT0, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) hB
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hT0 : T = 0 := by
        funext i j
        exact j.elim0
      rw [hT0, norm_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) hB
    · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hc_pos : 0 < c := by
        rw [hc]
        exact Real.sqrt_pos.mpr (mul_pos hmR hp)
      have hc_sq : c ^ 2 = (m : ℝ) * p := by
        rw [hc]
        exact Real.sq_sqrt (le_of_lt (mul_pos hmR hp))
      have hTapp : ∀ i j, T i j = M i j * A i j / c := fun i j => congrFun (congrFun hT i) j
      have hmin : 0 < min m n := lt_min hm hn
      have hne : Nonempty (Fin m) ∨ Nonempty (Fin n) := Or.inl ⟨⟨0, hm⟩⟩
      obtain ⟨hsv_eq, hsv_nonneg, hsv_anti, hsv_rank⟩ :=
        Statlib.HighDim.MatrixAnalysis.singular_value_properties T hne
      have hbridge : ‖T‖ ≤ Real.sqrt (∑ i, ∑ j, T i j ^ 2) := by
        have h1 : (Statlib.HighDim.MatrixAnalysis.singularValues T ⟨0, hmin⟩) ^ 2
            ≤ ∑ i, (Statlib.HighDim.MatrixAnalysis.singularValues T i) ^ 2 := by
          exact Finset.single_le_sum (s := Finset.univ)
            (f := fun i => (Statlib.HighDim.MatrixAnalysis.singularValues T i) ^ 2)
            (a := ⟨0, hmin⟩) (fun k _ => sq_nonneg _) (Finset.mem_univ _)
        have h2 : Statlib.HighDim.MatrixAnalysis.singularValues T ⟨0, hmin⟩
            ≤ Real.sqrt (∑ i, (Statlib.HighDim.MatrixAnalysis.singularValues T i) ^ 2) := by
          have hs0 : 0 ≤ Statlib.HighDim.MatrixAnalysis.singularValues T ⟨0, hmin⟩ := hsv_nonneg _
          calc Statlib.HighDim.MatrixAnalysis.singularValues T ⟨0, hmin⟩
              = Real.sqrt ((Statlib.HighDim.MatrixAnalysis.singularValues T ⟨0, hmin⟩) ^ 2) := (Real.sqrt_sq hs0).symm
            _ ≤ Real.sqrt (∑ i, (Statlib.HighDim.MatrixAnalysis.singularValues T i) ^ 2) := Real.sqrt_le_sqrt h1
        have h3 : Real.sqrt (∑ i, (Statlib.HighDim.MatrixAnalysis.singularValues T i) ^ 2)
            = Real.sqrt (∑ i, ∑ j, T i j ^ 2) := by
          rw [(Statlib.HighDim.MatrixAnalysis.frobenius_norm_svd_relation T).1]
        calc ‖T‖ = Statlib.HighDim.MatrixAnalysis.singularValues T ⟨0, hmin⟩ := (hsv_eq hmin).symm
          _ ≤ Real.sqrt (∑ i, (Statlib.HighDim.MatrixAnalysis.singularValues T i) ^ 2) := h2
          _ = Real.sqrt (∑ i, ∑ j, T i j ^ 2) := h3
      have hterm : ∀ i j, T i j ^ 2 ≤ (B / c) ^ 2 := by
        intro i j
        have hMabs : |M i j| ≤ 1 := by
          rcases hM i j with h | h <;> rw [h] <;> norm_num
        have hnum : |M i j| * |A i j| ≤ B := by
          have h := mul_le_mul hMabs (hA i j) (abs_nonneg (A i j)) (by norm_num : (0 : ℝ) ≤ 1)
          simpa using h
        have habs : |T i j| ≤ B / c := by
          rw [hTapp i j, abs_div, abs_mul, abs_of_pos hc_pos, div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (le_of_lt hc_pos))
        have hbc : 0 ≤ B / c := div_nonneg hB (le_of_lt hc_pos)
        have hsq : T i j ^ 2 = |T i j| ^ 2 := (sq_abs _).symm
        rw [hsq]
        nlinarith [habs, hbc, abs_nonneg (T i j)]
      have hstep1 : (∑ i, ∑ j, T i j ^ 2) ≤ ∑ i : Fin m, ∑ j : Fin n, (B / c) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact hterm i j
      have hstep2 : (∑ _i : Fin m, ∑ _j : Fin n, (B / c) ^ 2)
          = (m : ℝ) * (n : ℝ) * (B / c) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      have hstep3 : (m : ℝ) * (n : ℝ) * (B / c) ^ 2 = ((n : ℝ) / p) * B ^ 2 := by
        have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
        have hp0 : p ≠ 0 := ne_of_gt hp
        rw [div_pow, hc_sq]
        field_simp
      have hsum_le : (∑ i, ∑ j, T i j ^ 2) ≤ ((n : ℝ) / p) * B ^ 2 := by
        calc (∑ i, ∑ j, T i j ^ 2) ≤ ∑ i : Fin m, ∑ j : Fin n, (B / c) ^ 2 := hstep1
          _ = (m : ℝ) * (n : ℝ) * (B / c) ^ 2 := hstep2
          _ = ((n : ℝ) / p) * B ^ 2 := hstep3
      have hsqrt_final : Real.sqrt (((n : ℝ) / p) * B ^ 2) = Real.sqrt ((n : ℝ) / p) * B := by
        rw [Real.sqrt_mul (div_nonneg (Nat.cast_nonneg n) (le_of_lt hp)), Real.sqrt_sq hB]
      calc ‖T‖ ≤ Real.sqrt (∑ i, ∑ j, T i j ^ 2) := hbridge
        _ ≤ Real.sqrt (((n : ℝ) / p) * B ^ 2) := Real.sqrt_le_sqrt hsum_le
        _ = Real.sqrt ((n : ℝ) / p) * B := hsqrt_final
  /- @proof-region region.target-node.session.4755e91d6bdd9cd8 end -/

end Statlib.Imported

