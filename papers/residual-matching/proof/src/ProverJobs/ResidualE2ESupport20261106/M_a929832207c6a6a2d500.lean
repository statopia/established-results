import Lean
import ProverJobs.ResidualE2ESupport20261106.M_1ea39172008eded92d2a

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
theorem statopia_math_node_1118446036_e2b0a0d7 : ∀ (rho : ℝ) (hrho : 0 < rho)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0),
    ∃ CL : ℝ, 0 < CL ∧ ∃ N1 : ℕ, 3 ≤ N1 ∧
      ∀ (m n : ℕ), 1 ≤ n → n ≤ m → N1 ≤ m →
        rho ≤ (n : ℝ) / (m : ℝ) → (n : ℝ) / (m : ℝ) ≤ 1 →
        ∀ (p : ℝ), 0 ≤ p → p ≤ 1 →
          (m : ℝ) * p ≥ Real.rpow (Real.log (m : ℝ)) alpha0 →
          ∀ {Ωm : Type*} [MeasurableSpace Ωm] (P : Measure Ωm) [IsProbabilityMeasure P]
            (Om : Fin m → Fin n → Ωm → ℝ),
            (∀ (i : Fin m) (j : Fin n), Measurable (Om i j)) →
            iIndepFun (fun (ij : Fin m × Fin n) => Om ij.1 ij.2) P →
            (∀ (i : Fin m) (j : Fin n), ∀ᵐ ω ∂P, Om i j ω = 0 ∨ Om i j ω = 1) →
            (∀ (i : Fin m) (j : Fin n), Integrable (Om i j) P) →
            (∀ (i : Fin m) (j : Fin n), ∫ ω, Om i j ω ∂P = p) →
            1 - ENNReal.ofReal ((1 / 2 : ℝ) * (n : ℝ) ^ (-4 : ℤ)) ≤
              P {ω | specNorm (Wmask p (fun i j => Om i j ω))
                    ≤ CL * Real.sqrt ((m : ℝ) / p)} := by
  intro rho hrho alpha0 halpha0
  obtain ⟨CL, hCLpos, N1, hN1, hmain⟩ :=
    statopia_math_node_1400306846_f9cab3da rho hrho alpha0 halpha0
  refine ⟨CL, hCLpos, N1, hN1, ?_⟩
  intro m n hn hnm hmN hratio hratio_one p hp0 hp1 hgrowth Ωm hMS P hP Om
    hOm_meas hOm_indep hOm_bin hOm_int hOm_mean
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (le_trans hN1 hmN : (3 : ℕ) ≤ m)
  have hmpos : (0 : ℝ) < (m : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hm3
  have hm1 : (1 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hm3
  have hp_pos : 0 < p := by
    have hr : 0 < (Real.log (m : ℝ)).rpow alpha0 :=
      Real.rpow_pos_of_pos (Real.log_pos hm1) alpha0
    have hmul : (0 : ℝ) < (m : ℝ) * p := lt_of_lt_of_le hr hgrowth
    nlinarith [hmul, hmpos]
  have h1 : Real.sqrt ((m : ℝ) / p) * Real.sqrt p = Real.sqrt (m : ℝ) := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hmpos hp_pos))]
    congr 1
    field_simp
  have h3 : Real.sqrt ((m : ℝ) / p) * p = Real.sqrt (m : ℝ) * Real.sqrt p := by
    nlinarith [h1, Real.sq_sqrt (le_of_lt hp_pos), Real.sqrt_pos.2 hp_pos,
      Real.sqrt_pos.2 hmpos]
  have h2 : Real.sqrt ((m : ℝ) / p) / (Real.sqrt (m : ℝ) * Real.sqrt p) = 1 / p := by
    field_simp
    linarith [h3]
  have hX : ∀ ω : Ωm, Wmask p (fun i j => Om i j ω)
      = Real.sqrt ((m : ℝ) / p) •
        (fun i j => (Om i j ω - p) / (Real.sqrt (m : ℝ) * Real.sqrt p)) := by
    intro ω
    funext i j
    simp only [Wmask, Pi.smul_apply, smul_eq_mul]
    rw [show Real.sqrt ((m : ℝ) / p) *
          ((Om i j ω - p) / (Real.sqrt (m : ℝ) * Real.sqrt p))
        = (Om i j ω - p) * (Real.sqrt ((m : ℝ) / p) /
          (Real.sqrt (m : ℝ) * Real.sqrt p)) by ring]
    rw [h2]
    field_simp
  have hspec : ∀ (c : ℝ) (A : Matrix (Fin m) (Fin n) ℝ),
      specNorm (c • A) = |c| * specNorm A := by
    intro c A
    simp only [specNorm, map_smul, norm_smul, Real.norm_eq_abs]
  have hsqmp : Real.sqrt ((m : ℝ) * p) = Real.sqrt (m : ℝ) * Real.sqrt p := by
    rw [Real.sqrt_mul (le_of_lt hmpos)]
  have hsub : {ω : Ωm | specNorm (Matrix.of (fun i j =>
        (Om i j ω - p) / Real.sqrt ((m : ℝ) * p))) ≤ CL}
      ⊆ {ω : Ωm | specNorm (Wmask p (fun i j => Om i j ω))
          ≤ CL * Real.sqrt ((m : ℝ) / p)} := by
    intro ω hω
    have hA : Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p))
        = fun i j => (Om i j ω - p) / (Real.sqrt (m : ℝ) * Real.sqrt p) := by
      funext i j
      show (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)
        = (Om i j ω - p) / (Real.sqrt (m : ℝ) * Real.sqrt p)
      rw [hsqmp]
    have hc : 0 < Real.sqrt ((m : ℝ) / p) := Real.sqrt_pos.2 (div_pos hmpos hp_pos)
    have hspec' : specNorm (Wmask p (fun i j => Om i j ω))
        = Real.sqrt ((m : ℝ) / p) * specNorm (fun i j =>
            (Om i j ω - p) / (Real.sqrt (m : ℝ) * Real.sqrt p)) := by
      rw [hX ω, hspec, abs_of_nonneg (Real.sqrt_nonneg ((m : ℝ) / p))]
    have hle : specNorm (fun i j =>
        (Om i j ω - p) / (Real.sqrt (m : ℝ) * Real.sqrt p)) ≤ CL := by
      simpa only [Set.mem_setOf_eq, hA] using hω
    rw [Set.mem_setOf_eq, hspec']
    have hkey : 0 ≤ Real.sqrt ((m : ℝ) / p) *
        (CL - specNorm (fun i j => (Om i j ω - p) / (Real.sqrt (m : ℝ) * Real.sqrt p))) :=
      mul_nonneg (le_of_lt hc) (sub_nonneg.2 hle)
    nlinarith [hkey]
  calc 1 - ENNReal.ofReal ((1 / 2) * (n : ℝ) ^ (-4 : ℤ))
      ≤ P {ω : Ωm | specNorm (Matrix.of (fun i j =>
            (Om i j ω - p) / Real.sqrt ((m : ℝ) * p))) ≤ CL} :=
        hmain m n hn hnm hmN hratio p hp0 hp1 hgrowth (Ωm := Ωm) P Om
          hOm_meas hOm_indep hOm_bin hOm_int hOm_mean
    _ ≤ P {ω : Ωm | specNorm (Wmask p (fun i j => Om i j ω))
            ≤ CL * Real.sqrt ((m : ℝ) / p)} := measure_mono hsub

end

end Statlib.Imported

#print axioms Statlib.Imported.statopia_math_node_1118446036_e2b0a0d7

