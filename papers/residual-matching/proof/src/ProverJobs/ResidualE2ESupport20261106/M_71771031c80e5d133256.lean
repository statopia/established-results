import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_4766fd488fd085f402a1
import ProverJobs.ResidualE2ESupport20261106.M_73de5b2b167acb9070b6
import ProverJobs.ResidualE2ESupport20261106.M_4211b63131040117e12f
import ProverJobs.ResidualE2ESupport20261106.M_67053ae31fee5cdf634e

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
theorem statopia_math_node_2157505147_d4ab740e : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {Ωm : Type*} [MeasurableSpace Ωm] (P : Measure Ωm) [IsProbabilityMeasure P]
    (Om : Fin m → Fin n → Ωm → ℝ)
    (hOm_meas : ∀ i j, Measurable (Om i j))
    (hOm_indep : iIndepFun (fun ij : Fin m × Fin n => Om ij.1 ij.2) P)
    (hOm_bin : ∀ i j, ∀ᵐ ω ∂P, Om i j ω = 0 ∨ Om i j ω = 1)
    (hOm_int : ∀ i j, Integrable (Om i j) P)
    (hOm_mean : ∀ i j, ∫ ω, Om i j ω ∂P = p),
    let xi : Fin m → Fin n → Ωm → ℝ :=
      fun i j ω => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)
    let D : Fin m → Fin n → Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
      fun i j => Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
          (matrixUnit i j) (matrixUnit i j).transpose
          (0 : Matrix (Fin n) (Fin n) ℝ))
    let Xt : Ωm → Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
      fun ω => Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
          (Matrix.of (fun i j => xi i j ω))
          (Matrix.of (fun i j => xi i j ω)).transpose
          (0 : Matrix (Fin n) (Fin n) ℝ))
    let cov : Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
      Matrix.of (fun a b => ∫ ω, (Xt ω * Xt ω) a b ∂P)
    Matrix.of (fun i k => ∫ ω, ∑ j : Fin n, xi i j ω * xi k j ω ∂P)
        = ((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ) ∧
      Matrix.of (fun j l => ∫ ω, ∑ i : Fin m, xi i j ω * xi i l ω ∂P)
        = (1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ) ∧
      cov = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ))
          (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin m) ℝ)
          ((1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ))) ∧
      specNorm cov = 1 - p ∧
      Real.sqrt (specNorm cov) = Real.sqrt (1 - p) ∧
      max ((n : ℝ) * (1 - p) / (m : ℝ)) (1 - p) = 1 - p ∧
      (∀ (v1 w1 : Fin m → ℝ) (v2 w2 : Fin n → ℝ),
        (∑ i : Fin m, (v1 i) ^ 2) + (∑ j : Fin n, (v2 j) ^ 2) = 1 →
        (∑ i : Fin m, (w1 i) ^ 2) + (∑ j : Fin n, (w2 j) ^ 2) = 1 →
        (∫ ω, ((∑ i : Fin m, ∑ j : Fin n, v1 i * xi i j ω * w2 j)
            + (∑ j : Fin n, ∑ i : Fin m, v2 j * xi i j ω * w1 i)) ^ 2 ∂P)
          = ((1 - p) / (m : ℝ)) *
              (((∑ i : Fin m, (v1 i) ^ 2) * (∑ j : Fin n, (w2 j) ^ 2))
                + 2 * ((∑ i : Fin m, v1 i * w1 i) * (∑ j : Fin n, v2 j * w2 j))
                + ((∑ j : Fin n, (v2 j) ^ 2) * (∑ i : Fin m, (w1 i) ^ 2)))
        ∧ (∫ ω, ((∑ i : Fin m, ∑ j : Fin n, v1 i * xi i j ω * w2 j)
            + (∑ j : Fin n, ∑ i : Fin m, v2 j * xi i j ω * w1 i)) ^ 2 ∂P)
          ≤ (1 - p) / (m : ℝ)) ∧
      (∀ (v1 : Fin m → ℝ) (w2 : Fin n → ℝ),
        (∑ i : Fin m, (v1 i) ^ 2) = 1 → (∑ j : Fin n, (w2 j) ^ 2) = 1 →
        (∫ ω, (∑ i : Fin m, ∑ j : Fin n, v1 i * xi i j ω * w2 j) ^ 2 ∂P)
          = (1 - p) / (m : ℝ)) ∧
      (IsLUB {r : ℝ | ∃ (v1 : Fin m → ℝ), ∃ (w1 : Fin m → ℝ),
          ∃ (v2 : Fin n → ℝ), ∃ (w2 : Fin n → ℝ),
        (∑ i : Fin m, (v1 i) ^ 2) + (∑ j : Fin n, (v2 j) ^ 2) = 1 ∧
        (∑ i : Fin m, (w1 i) ^ 2) + (∑ j : Fin n, (w2 j) ^ 2) = 1 ∧
        r = Real.sqrt (∫ ω, ((∑ i : Fin m, ∑ j : Fin n, v1 i * xi i j ω * w2 j)
            + (∑ j : Fin n, ∑ i : Fin m, v2 j * xi i j ω * w1 i)) ^ 2 ∂P)}
        (Real.sqrt ((1 - p) / (m : ℝ)))) ∧
      (∀ (i : Fin m) (j : Fin n), ∫ ω, xi i j ω ∂P = 0) ∧
      (∀ (ij : Fin m × Fin n) (a b : Fin (m + n)),
        ∫ ω, (xi ij.1 ij.2 ω • D ij.1 ij.2) a b ∂P = 0) ∧
      (iIndepFun (fun (ij : Fin m × Fin n) => fun ω => xi ij.1 ij.2 ω • D ij.1 ij.2) P) ∧
      (∀ ω : Ωm, Xt ω = ∑ ij : Fin m × Fin n, xi ij.1 ij.2 ω • D ij.1 ij.2) ∧
      (∀ (i : Fin m) (j : Fin n), (D i j).transpose = D i j) ∧
      (∀ (i : Fin m) (j : Fin n), specNorm (D i j) = 1) ∧
      (∀ (i : Fin m) (j : Fin n) (ω : Ωm),
        specNorm (xi i j ω • D i j) = |xi i j ω|) ∧
      (∀ᵐ ω ∂P, ∀ (i : Fin m) (j : Fin n),
        |xi i j ω| ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p)) ∧
      (max p (1 - p) / Real.sqrt ((m : ℝ) * p) ≤ 1 / Real.sqrt ((m : ℝ) * p)) ∧
      (0 < max p (1 - p) / Real.sqrt ((m : ℝ) * p)) ∧
      (∀ᵐ ω ∂P, ∀ (i : Fin m) (j : Fin n),
        specNorm (xi i j ω • D i j) ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p)) ∧
      (∀ᵐ ω ∂P, ∀ (i : Fin m) (j : Fin n),
        specNorm (xi i j ω • D i j) ≤ 1 / Real.sqrt ((m : ℝ) * p)) ∧
      Real.sqrt (specNorm cov) ≤ 1 ∧
      Real.sqrt ((1 - p) / (m : ℝ)) ≤ 1 / Real.sqrt (m : ℝ) := by
  /- @proof-region region.target-node.session.8de0f09899ca3555 begin -/
  intro m n hm hn hnm p hp0 hp1 Ωm instΩ P instP Om hOm_meas hOm_indep hOm_bin hOm_int hOm_mean
  have hmom := statopia_math_node_3069358588_912211ca m n hm hn hnm p hp0 hp1 P Om hOm_meas hOm_indep hOm_bin hOm_int hOm_mean
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcov := statopia_math_node_3857640630_330b31cd m n hm hn hnm p hp0 hp1 P Om hOm_meas hOm_int hmom.1 hmom.2
  have hquad := statopia_math_node_1754230237_929ddf96 m n hm hn hnm p hp0 hp1 P Om hOm_meas hOm_indep hOm_bin hOm_int hOm_mean
  have hD := statopia_math_node_360940608_79944c4e m n hm hn hnm p hp0 hp1 P Om
  have h17 : ∀ᵐ ω ∂P, ∀ (i : Fin m) (j : Fin n),
      |((Om i j ω - p) / Real.sqrt ((m : ℝ) * p))|
        ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p) := by
    refine MeasureTheory.ae_all_iff.mpr (fun i => ?_)
    refine MeasureTheory.ae_all_iff.mpr (fun j => ?_)
    have hs : 0 < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.mpr (mul_pos hmR hp0)
    have hspos : 0 ≤ (Real.sqrt ((m : ℝ) * p))⁻¹ := le_of_lt (inv_pos.mpr hs)
    filter_upwards [hOm_bin i j] with ω hω
    have hbound : |Om i j ω - p| ≤ max p (1 - p) := by
      rcases hω with h | h
      · rw [h, zero_sub, abs_neg, abs_of_pos hp0]
        exact le_max_left p (1 - p)
      · rw [h, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - p)]
        exact le_max_right p (1 - p)
    calc |(Om i j ω - p) / Real.sqrt ((m : ℝ) * p)|
        = |Om i j ω - p| * (Real.sqrt ((m : ℝ) * p))⁻¹ := by
          rw [div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hs)]
      _ ≤ max p (1 - p) * (Real.sqrt ((m : ℝ) * p))⁻¹ :=
          mul_le_mul_of_nonneg_right hbound hspos
      _ = max p (1 - p) / Real.sqrt ((m : ℝ) * p) := by rw [div_eq_mul_inv]
  have h18 : max p (1 - p) / Real.sqrt ((m : ℝ) * p) ≤ 1 / Real.sqrt ((m : ℝ) * p) := by
    have hs : 0 < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.mpr (mul_pos hmR hp0)
    have hmax : max p (1 - p) ≤ 1 := max_le hp1 (by linarith)
    rw [div_le_iff₀ hs, one_div, inv_mul_cancel₀ (ne_of_gt hs)]
    exact hmax
  have h20 : ∀ᵐ ω ∂P, ∀ (i : Fin m) (j : Fin n),
      specNorm (((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) •
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (matrixUnit i j)
            (matrixUnit i j).transpose (0 : Matrix (Fin n) (Fin n) ℝ)))
        ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p) := by
    filter_upwards [h17] with ω hω
    intro i j
    rw [hD.2.2.2 i j ω]
    exact hω i j
  have hxi0 : ∀ (i : Fin m) (j : Fin n),
      (∫ ω, (Om i j ω - p) / Real.sqrt ((m : ℝ) * p) ∂P) = 0 := by
    intro i j
    have hz : (∫ ω, (Om i j ω - p) ∂P) = 0 := by
      rw [integral_sub (hOm_int i j) (integrable_const p), hOm_mean i j]
      simp
    simp only [div_eq_mul_inv]
    rw [MeasureTheory.integral_mul_const, hz, zero_mul]
  have hindep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ωm) =>
      (((Om ij.1 ij.2 ω - p) / Real.sqrt ((m : ℝ) * p)) •
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (matrixUnit ij.1 ij.2)
            (matrixUnit ij.1 ij.2).transpose (0 : Matrix (Fin n) (Fin n) ℝ)))) P :=
    ProbabilityTheory.iIndepFun.comp hOm_indep
      (fun ij x => ((x - p) / Real.sqrt ((m : ℝ) * p)) •
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (matrixUnit ij.1 ij.2)
            (matrixUnit ij.1 ij.2).transpose (0 : Matrix (Fin n) (Fin n) ℝ)))
      (fun ij => by
        have hsc : Measurable (fun x : ℝ => (x - p) / Real.sqrt ((m : ℝ) * p)) :=
          (measurable_id.sub measurable_const).div_const _
        exact hsc.smul measurable_const)
  refine ⟨hmom.1, hmom.2, hcov.1,
    (by
      refine (Real.sqrt_inj ?_ ?_).mp hcov.2
      · exact norm_nonneg _
      · linarith),
    hcov.2,
    (by
      have h1 : (0 : ℝ) ≤ 1 - p := by linarith
      have h2 : (n : ℝ) * (1 - p) / (m : ℝ) ≤ 1 - p := by
        rw [div_le_iff₀ hmR]
        have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
        have hmul : (n : ℝ) * (1 - p) ≤ (m : ℝ) * (1 - p) :=
          mul_le_mul_of_nonneg_right hnm' h1
        linarith
      exact max_eq_right h2),
    hquad.1,
    hquad.2.1, hquad.2.2,
    hxi0,
    (fun ij a b => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [MeasureTheory.integral_mul_const, hxi0 ij.1 ij.2, zero_mul]),
    hindep, hD.1, hD.2.1, hD.2.2.1, hD.2.2.2,
    h17,
    h18,
    (by
      exact div_pos (lt_of_lt_of_le hp0 (le_max_left p (1 - p)))
        (Real.sqrt_pos.mpr (mul_pos hmR hp0))),
    h20,
    (by
      filter_upwards [h20] with ω hω
      exact fun i j => le_trans (hω i j) h18),
    (by
      dsimp only
      rw [hcov.2]
      calc Real.sqrt (1 - p) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one),
    (by
      have h1 : (0 : ℝ) ≤ 1 - p := by linarith
      rw [Real.sqrt_div h1]
      have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
      have hle : Real.sqrt (1 - p) ≤ 1 := by
        calc Real.sqrt (1 - p) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
          _ = 1 := Real.sqrt_one
      rw [div_le_iff₀ hsm, one_div, inv_mul_cancel₀ (ne_of_gt hsm)]
      exact hle)⟩
  /- @proof-region region.target-node.session.8de0f09899ca3555 end -/

end

end Statlib.Imported

