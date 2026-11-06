import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_255c3f19f3d661abe31b

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1754230237_929ddf96 : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {Ωm : Type*} [MeasurableSpace Ωm] (P : Measure Ωm) [IsProbabilityMeasure P]
    (Om : Fin m → Fin n → Ωm → ℝ)
    (hOm_meas : ∀ i j, Measurable (Om i j))
    (hOm_indep : ProbabilityTheory.iIndepFun (fun ij : Fin m × Fin n => Om ij.1 ij.2) P)
    (hOm_bin : ∀ i j, ∀ᵐ ω ∂P, Om i j ω = 0 ∨ Om i j ω = 1)
    (hOm_int : ∀ i j, MeasureTheory.Integrable (Om i j) P)
    (hOm_mean : ∀ i j, ∫ ω, Om i j ω ∂P = p),
    (∀ (v1 w1 : Fin m → ℝ) (v2 w2 : Fin n → ℝ),
      (∑ i : Fin m, (v1 i) ^ 2) + (∑ j : Fin n, (v2 j) ^ 2) = 1 →
      (∑ i : Fin m, (w1 i) ^ 2) + (∑ j : Fin n, (w2 j) ^ 2) = 1 →
      ((∫ ω, ((∑ i : Fin m, ∑ j : Fin n,
            v1 i * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w2 j)
          + (∑ j : Fin n, ∑ i : Fin m,
            v2 j * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w1 i)) ^ 2 ∂P)
        = ((1 - p) / (m : ℝ)) * (((∑ i : Fin m, (v1 i) ^ 2) * (∑ j : Fin n, (w2 j) ^ 2))
          + 2 * ((∑ i : Fin m, v1 i * w1 i) * (∑ j : Fin n, v2 j * w2 j))
          + ((∑ j : Fin n, (v2 j) ^ 2) * (∑ i : Fin m, (w1 i) ^ 2))))
      ∧ ((∫ ω, ((∑ i : Fin m, ∑ j : Fin n,
            v1 i * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w2 j)
          + (∑ j : Fin n, ∑ i : Fin m,
            v2 j * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w1 i)) ^ 2 ∂P)
        ≤ (1 - p) / (m : ℝ)))
    ∧ (∀ (v1 : Fin m → ℝ) (w2 : Fin n → ℝ),
      (∑ i : Fin m, (v1 i) ^ 2) = 1 → (∑ j : Fin n, (w2 j) ^ 2) = 1 →
      (∫ ω, (∑ i : Fin m, ∑ j : Fin n,
          v1 i * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w2 j) ^ 2 ∂P)
        = (1 - p) / (m : ℝ))
    ∧ (IsLUB {r : ℝ | ∃ (v1 : Fin m → ℝ), ∃ (w1 : Fin m → ℝ),
          ∃ (v2 : Fin n → ℝ), ∃ (w2 : Fin n → ℝ),
        (∑ i : Fin m, (v1 i) ^ 2) + (∑ j : Fin n, (v2 j) ^ 2) = 1 ∧
        (∑ i : Fin m, (w1 i) ^ 2) + (∑ j : Fin n, (w2 j) ^ 2) = 1 ∧
        r = Real.sqrt ((∫ ω, ((∑ i : Fin m, ∑ j : Fin n,
              v1 i * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w2 j)
            + (∑ j : Fin n, ∑ i : Fin m,
              v2 j * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w1 i)) ^ 2 ∂P))}
      (Real.sqrt ((1 - p) / (m : ℝ)))) := by
  /- @proof-region region.target-node.session.4ebcbedd36aa8ed1 begin -/
  intro m n hm hn hnm p hp0 hp1 Omega _ P _ Om hOm_meas hOm_indep hOm_bin hOm_int hOm_mean
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hs : 0 < Real.sqrt ((m:ℝ) * p) := Real.sqrt_pos.mpr (mul_pos hmR hp0)
  have key : ∀ a : Fin m → Fin n → ℝ,
      (∫ ω, (∑ i, ∑ j, a i j * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)))^2 ∂P)
        = (1-p)/(m:ℝ) * ∑ i, ∑ j, (a i j)^2 :=
    statopia_math_node_3684688107_efbf5172 m n hm hn p hp0 hp1 P Om hOm_meas hOm_indep hOm_bin hOm_int hOm_mean
  have hP1 : ∀ (v1 w1 : Fin m → ℝ) (v2 w2 : Fin n → ℝ),
      (∑ i : Fin m, (v1 i) ^ 2) + (∑ j : Fin n, (v2 j) ^ 2) = 1 →
      (∑ i : Fin m, (w1 i) ^ 2) + (∑ j : Fin n, (w2 j) ^ 2) = 1 →
      ((∫ ω, ((∑ i : Fin m, ∑ j : Fin n, v1 i * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w2 j) + (∑ j : Fin n, ∑ i : Fin m, v2 j * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w1 i)) ^ 2 ∂P) = ((1 - p) / (m : ℝ)) * (((∑ i : Fin m, (v1 i) ^ 2) * (∑ j : Fin n, (w2 j) ^ 2)) + 2 * ((∑ i : Fin m, v1 i * w1 i) * (∑ j : Fin n, v2 j * w2 j)) + ((∑ j : Fin n, (v2 j) ^ 2) * (∑ i : Fin m, (w1 i) ^ 2)))) ∧
      ((∫ ω, ((∑ i : Fin m, ∑ j : Fin n, v1 i * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w2 j) + (∑ j : Fin n, ∑ i : Fin m, v2 j * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w1 i)) ^ 2 ∂P) ≤ (1 - p) / (m : ℝ)) := by
    intro v1 w1 v2 w2 h1 h2
    have hTint : (∫ ω, ((∑ i, ∑ j, v1 i * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * w2 j) + (∑ j, ∑ i, v2 j * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * w1 i))^2 ∂P)
        = (1-p)/(m:ℝ) * ∑ i, ∑ j, (v1 i * w2 j + v2 j * w1 i)^2 := by
      rw [show (∫ ω, ((∑ i, ∑ j, v1 i * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * w2 j) + (∑ j, ∑ i, v2 j * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * w1 i))^2 ∂P)
            = (∫ ω, (∑ i, ∑ j, (v1 i * w2 j + v2 j * w1 i) * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)))^2 ∂P) from by
        apply integral_congr_ae
        filter_upwards with ω
        have e1 : (∑ i, ∑ j, v1 i * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * w2 j)
            = (∑ i, ∑ j, (v1 i * w2 j) * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p))) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          ring
        have e2 : (∑ j, ∑ i, v2 j * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * w1 i)
            = (∑ i, ∑ j, (v2 j * w1 i) * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          ring
        have e3 : ((∑ i, ∑ j, v1 i * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * w2 j) + (∑ j, ∑ i, v2 j * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * w1 i))
            = (∑ i, ∑ j, (v1 i * w2 j + v2 j * w1 i) * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p))) := by
          rw [e1, e2]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro j _
          ring
        rw [e3]]
      exact key (fun i j => v1 i * w2 j + v2 j * w1 i)
    have hSq : (∑ i, ∑ j, (v1 i * w2 j + v2 j * w1 i)^2)
        = (((∑ i, (v1 i)^2) * (∑ j, (w2 j)^2)) + 2 * ((∑ i, v1 i * w1 i) * (∑ j, v2 j * w2 j)) + ((∑ j, (v2 j)^2) * (∑ i, (w1 i)^2))) := by
      have h_expand : (∑ i, ∑ j, (v1 i * w2 j + v2 j * w1 i)^2)
          = (∑ i, ∑ j, ((v1 i * w2 j)^2 + 2 * (v1 i * w2 j) * (v2 j * w1 i) + (v2 j * w1 i)^2)) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        ring
      have hAD : (∑ i, ∑ j, (v1 i * w2 j)^2) = (∑ i, (v1 i)^2) * (∑ j, (w2 j)^2) := by
        simp only [mul_pow]
        rw [Finset.sum_mul_sum]
      have hBC : (∑ i, ∑ j, (v2 j * w1 i)^2) = (∑ j, (v2 j)^2) * (∑ i, (w1 i)^2) := by
        rw [Finset.sum_comm]
        simp only [mul_pow]
        rw [Finset.sum_mul_sum]
      have hMid : (∑ i, ∑ j, 2 * (v1 i * w2 j) * (v2 j * w1 i)) = 2 * ((∑ i, v1 i * w1 i) * (∑ j, v2 j * w2 j)) := by
        have s1 : (∑ i, ∑ j, 2 * (v1 i * w2 j) * (v2 j * w1 i)) = (∑ i, ∑ j, (2 * (v1 i * w1 i)) * (v2 j * w2 j)) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          ring
        have hR : (∑ i, ∑ j, (2 * (v1 i * w1 i)) * (v2 j * w2 j)) = 2 * ((∑ i, v1 i * w1 i) * (∑ j, v2 j * w2 j)) := by
          rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
          ring
        rw [s1, hR]
      rw [h_expand]
      simp only [Finset.sum_add_distrib]
      rw [hAD, hMid, hBC]
    refine ⟨?_, ?_⟩
    · rw [hTint, hSq]
    · rw [hTint, hSq]
      have hParens : (∑ i, (v1 i)^2) * (∑ j, (w2 j)^2) + 2 * ((∑ i, v1 i * w1 i) * (∑ j, v2 j * w2 j)) + (∑ j, (v2 j)^2) * (∑ i, (w1 i)^2) ≤ 1 := by
        have hCS1 : (∑ i, v1 i * w1 i)^2 ≤ (∑ i, (v1 i)^2) * (∑ i, (w1 i)^2) := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v1 w1
        have hCS2 : (∑ j, v2 j * w2 j)^2 ≤ (∑ j, (v2 j)^2) * (∑ j, (w2 j)^2) := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v2 w2
        nlinarith [h1, h2, hCS1, hCS2, sq_nonneg ((∑ i, v1 i * w1 i) - (∑ j, v2 j * w2 j))]
      have hnn : 0 ≤ (1 - p) / (m:ℝ) := div_nonneg (by linarith) (le_of_lt hmR)
      calc (1 - p) / (m:ℝ) * ((∑ i, (v1 i)^2) * (∑ j, (w2 j)^2) + 2 * ((∑ i, v1 i * w1 i) * (∑ j, v2 j * w2 j)) + (∑ j, (v2 j)^2) * (∑ i, (w1 i)^2))
          ≤ (1 - p) / (m:ℝ) * 1 := mul_le_mul_of_nonneg_left hParens hnn
        _ = (1 - p) / (m:ℝ) := mul_one _
  have hP2 : ∀ (v1 : Fin m → ℝ) (w2 : Fin n → ℝ),
      (∑ i : Fin m, (v1 i) ^ 2) = 1 →
      (∑ j : Fin n, (w2 j) ^ 2) = 1 →
      (∫ ω, (∑ i : Fin m, ∑ j : Fin n, v1 i * ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) * w2 j) ^ 2 ∂P) = (1 - p) / (m : ℝ) := by
    intro v1 w2 h1 h2
    have hsum : (∑ i, ∑ j, (v1 i * w2 j)^2) = 1 := by
      have hfac : (∑ i, ∑ j, (v1 i * w2 j)^2) = (∑ i, (v1 i)^2) * (∑ j, (w2 j)^2) := by
        simp only [mul_pow]
        rw [Finset.sum_mul_sum]
      rw [hfac, h1, h2, mul_one]
    have h := key (fun i j => v1 i * w2 j)
    rw [hsum, mul_one] at h
    rw [show (∫ ω, (∑ i, ∑ j, v1 i * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * w2 j)^2 ∂P)
          = (∫ ω, (∑ i, ∑ j, (v1 i * w2 j) * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)))^2 ∂P) from by
      apply integral_congr_ae
      filter_upwards with ω
      rw [show (∑ i, ∑ j, v1 i * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * w2 j)
            = (∑ i, ∑ j, (v1 i * w2 j) * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p))) from by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        ring]]
    exact h
  refine ⟨?_, ?_, ?_⟩
  · intro v1 w1 v2 w2 h1 h2
    exact hP1 v1 w1 v2 w2 h1 h2
  · exact hP2
  · refine ⟨?_, ?_⟩
    · rintro x ⟨v1, w1, v2, w2, h1v, h2v, rfl⟩
      exact Real.sqrt_le_sqrt (hP1 v1 w1 v2 w2 h1v h2v).2
    · intro b hb
      apply hb
      let a_m : Fin m := ⟨0, hm⟩
      let a_n : Fin n := ⟨0, hn⟩
      set e : Fin m → ℝ := fun i => if i = a_m then 1 else 0 with he
      set f : Fin n → ℝ := fun j => if j = a_n then 1 else 0 with hf
      have hSe : (∑ i, (e i)^2) = 1 := by simp [he]
      have hWf : (∑ j, (f j)^2) = 1 := by simp [hf]
      refine ⟨e, (0:Fin m → ℝ), (0:Fin n → ℝ), f, ?_, ?_, ?_⟩
      · rw [hSe]; simp
      · rw [hWf]; simp
      · have hval : (∫ ω, ((∑ i, ∑ j, e i * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * f j) + (∑ j, ∑ i, (0:Fin n → ℝ) j * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * (0:Fin m → ℝ) i))^2 ∂P) = (1-p)/(m:ℝ) := by
          rw [show (∫ ω, ((∑ i, ∑ j, e i * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * f j) + (∑ j, ∑ i, (0:Fin n → ℝ) j * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * (0:Fin m → ℝ) i))^2 ∂P)
                = (∫ ω, (∑ i, ∑ j, e i * ((Om i j ω - p) / Real.sqrt ((m:ℝ)*p)) * f j)^2 ∂P) from by
            apply integral_congr_ae
            filter_upwards with ω
            simp]
          exact hP2 e f hSe hWf
        rw [hval]
  /- @proof-region region.target-node.session.4ebcbedd36aa8ed1 end -/

end

end Statlib.Imported

