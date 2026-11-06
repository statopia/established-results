import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3553486712_c6cf8bba : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ)
    (hXi_sq_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
    (hXi_mean : ∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0)
    (hXi_var : ∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ)
    (h : Fin m × Fin n) (h' : Fin m × Fin n),
    Integrable (fun ω => maskedScaled p (Xi ω) (Mask ω) h.1 h.2) μ ∧
    (∫ ω, maskedScaled p (Xi ω) (Mask ω) h.1 h.2 ∂μ = 0) ∧
    Integrable (fun ω => maskedScaled p (Xi ω) (Mask ω) h.1 h.2
      * maskedScaled p (Xi ω) (Mask ω) h'.1 h'.2) μ ∧
    (∫ ω, maskedScaled p (Xi ω) (Mask ω) h.1 h.2
        * maskedScaled p (Xi ω) (Mask ω) h'.1 h'.2 ∂μ
      = if h = h' then 1 / (m : ℝ) else 0) := by
  /- @proof-region region.target-node.session.de85e0f8a80930d9 begin -/
  intro m n hm hn p hp hp1 Ω instΩ μ instP Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep
    hXi_mean hXi_var hMask_meas hMask_val hMask_law hMask_indep hIndep h h'

  haveI : IsProbabilityMeasure μ := instP
  set c : ℝ := (Real.sqrt ((m : ℝ) * p))⁻¹ with hc_def
  have hmasked : ∀ (i : Fin m) (j : Fin n) (ω : Ω),
      maskedScaled p (Xi ω) (Mask ω) i j = Mask ω i j * Xi ω i j * c := by
    intro i j ω
    unfold maskedScaled
    rw [div_eq_mul_inv, ← hc_def]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (fun ω => maskedScaled p (Xi ω) (Mask ω) h.1 h.2)
        = (fun ω => Mask ω h.1 h.2 * Xi ω h.1 h.2 * c) from funext (fun ω => hmasked h.1 h.2 ω)]
    have hG : Integrable (fun ω => Mask ω h.1 h.2 * Xi ω h.1 h.2) μ := by
      refine Integrable.mono' (hXi_int h.1 h.2).norm ?_ ?_
      · exact (hMask_meas h.1 h.2).aestronglyMeasurable.mul (hXi_int h.1 h.2).aestronglyMeasurable
      · filter_upwards with ω
        rw [norm_mul]
        have hb : ‖Mask ω h.1 h.2‖ ≤ 1 := by
          rcases hMask_val h.1 h.2 ω with h0 | h1
          · rw [h0]; simp
          · rw [h1]; simp
        calc ‖Mask ω h.1 h.2‖ * ‖Xi ω h.1 h.2‖
            ≤ 1 * ‖Xi ω h.1 h.2‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
          _ = ‖Xi ω h.1 h.2‖ := one_mul _
    exact hG.mul_const c
  · rw [show (∫ ω, maskedScaled p (Xi ω) (Mask ω) h.1 h.2 ∂μ)
        = ∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 * c ∂μ from
          integral_congr_ae (Filter.Eventually.of_forall (fun ω => hmasked h.1 h.2 ω))]
    rw [show (∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 * c ∂μ)
        = (∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 ∂μ) * c from
          integral_mul_const c (fun ω => Mask ω h.1 h.2 * Xi ω h.1 h.2)]
    have hMask_int : Integrable (fun ω => Mask ω h.1 h.2) μ := by
      refine Integrable.mono' (integrable_const (1:ℝ)) ?_ ?_
      · exact (hMask_meas h.1 h.2).aestronglyMeasurable
      · filter_upwards with ω
        rcases hMask_val h.1 h.2 ω with h0 | h1
        · rw [h0]; simp
        · rw [h1]; simp
    have hind_pair : IndepFun (fun ω => Mask ω h.1 h.2) (fun ω => Xi ω h.1 h.2) μ := by
      have h1 : IndepFun (fun ω => Xi ω h.1 h.2) (fun ω => Mask ω h.1 h.2) μ := by
        have hcomp := hIndep.comp (measurable_pi_apply h) (measurable_pi_apply h)
        simpa only [Function.comp_apply] using hcomp
      exact h1.symm
    have hprod : ∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 ∂μ = 0 := by
      have hfact : ∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 ∂μ
          = (∫ ω, Mask ω h.1 h.2 ∂μ) * (∫ ω, Xi ω h.1 h.2 ∂μ) :=
        hind_pair.integral_mul_eq_mul_integral (hMask_meas h.1 h.2).aestronglyMeasurable (hXi_meas h.1 h.2).aestronglyMeasurable
      rw [hfact, hXi_mean h.1 h.2, mul_zero]
    rw [hprod, zero_mul]
  · rw [show (fun ω => maskedScaled p (Xi ω) (Mask ω) h.1 h.2
          * maskedScaled p (Xi ω) (Mask ω) h'.1 h'.2)
        = (fun ω => (Mask ω h.1 h.2 * Xi ω h.1 h.2 * c) * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2 * c))
        from funext (fun ω => by rw [hmasked h.1 h.2 ω, hmasked h'.1 h'.2 ω])]
    rw [show (fun ω => (Mask ω h.1 h.2 * Xi ω h.1 h.2 * c) * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2 * c))
        = (fun ω => (Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2)) * (c * c))
        from funext (fun ω => by ring)]
    have hGG' : Integrable (fun ω => Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2)) μ := by
      refine Integrable.mono' ((hXi_sq_int h.1 h.2).add (hXi_sq_int h'.1 h'.2)) ?_ ?_
      · exact ((hMask_meas h.1 h.2).mul (hXi_meas h.1 h.2)).aestronglyMeasurable.mul (((hMask_meas h'.1 h'.2).mul (hXi_meas h'.1 h'.2)).aestronglyMeasurable)
      · filter_upwards with ω
        have ha : ‖Mask ω h.1 h.2‖ ≤ 1 := by
          rcases hMask_val h.1 h.2 ω with h0 | h1
          · rw [h0]; simp
          · rw [h1]; simp
        have hb : ‖Mask ω h'.1 h'.2‖ ≤ 1 := by
          rcases hMask_val h'.1 h'.2 ω with h0 | h1
          · rw [h0]; simp
          · rw [h1]; simp
        have hxnn : (0:ℝ) ≤ ‖Xi ω h.1 h.2‖ := norm_nonneg _
        have hynn : (0:ℝ) ≤ ‖Xi ω h'.1 h'.2‖ := norm_nonneg _
        have hxs : ‖Xi ω h.1 h.2‖^2 = Xi ω h.1 h.2^2 := by rw [Real.norm_eq_abs, sq_abs]
        have hys : ‖Xi ω h'.1 h'.2‖^2 = Xi ω h'.1 h'.2^2 := by rw [Real.norm_eq_abs, sq_abs]
        calc ‖Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2)‖
            = ‖Mask ω h.1 h.2‖ * ‖Xi ω h.1 h.2‖ * (‖Mask ω h'.1 h'.2‖ * ‖Xi ω h'.1 h'.2‖) := by simp only [norm_mul]
          _ ≤ (1 * ‖Xi ω h.1 h.2‖) * (1 * ‖Xi ω h'.1 h'.2‖) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) ?_ ?_
              · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
              · exact mul_nonneg zero_le_one (norm_nonneg _)
          _ = ‖Xi ω h.1 h.2‖ * ‖Xi ω h'.1 h'.2‖ := by ring
          _ ≤ Xi ω h.1 h.2 ^ 2 + Xi ω h'.1 h'.2 ^ 2 := by nlinarith [sq_nonneg (‖Xi ω h.1 h.2‖ - ‖Xi ω h'.1 h'.2‖), hxnn, hynn, hxs, hys]
    exact hGG'.mul_const (c * c)
  · rw [show (fun ω => maskedScaled p (Xi ω) (Mask ω) h.1 h.2
          * maskedScaled p (Xi ω) (Mask ω) h'.1 h'.2)
        = (fun ω => (Mask ω h.1 h.2 * Xi ω h.1 h.2 * c) * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2 * c))
        from funext (fun ω => by rw [hmasked h.1 h.2 ω, hmasked h'.1 h'.2 ω])]
    rw [show (fun ω => (Mask ω h.1 h.2 * Xi ω h.1 h.2 * c) * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2 * c))
        = (fun ω => (Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2)) * (c * c))
        from funext (fun ω => by ring)]
    rw [show (∫ ω, (Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2)) * (c * c) ∂μ)
        = (∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2) ∂μ) * (c * c)
        from integral_mul_const (c * c) (fun ω => Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2))]
    by_cases hh : h = h'
    · rw [if_pos hh]
      subst h'
      have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have hmpos : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le zero_lt_one hm1
      have hmp : (0:ℝ) < (m:ℝ) * p := mul_pos hmpos hp
      have hcc : c * c = ((m:ℝ) * p)⁻¹ := by
        rw [hc_def, ← pow_two, inv_pow, Real.sq_sqrt (le_of_lt hmp)]
      have hMask_mean : ∫ ω, Mask ω h.1 h.2 ∂μ = p := by
        have hmeas : MeasurableSet {ω | Mask ω h.1 h.2 = 1} := (hMask_meas h.1 h.2) (measurableSet_singleton 1)
        have hind : (fun ω => Mask ω h.1 h.2) = {ω | Mask ω h.1 h.2 = 1}.indicator (fun _ => (1:ℝ)) := by
          funext ω
          rcases hMask_val h.1 h.2 ω with h0 | h1
          · simp [h0]
          · simp [h1]
        rw [hind, MeasureTheory.integral_indicator hmeas]
        change ∫ x in {ω | Mask ω h.1 h.2 = 1}, (1:ℝ) ∂μ = p
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
        rw [show μ.real {ω | Mask ω h.1 h.2 = 1} = (μ {ω | Mask ω h.1 h.2 = 1}).toReal from rfl]
        rw [hMask_law h.1 h.2, ENNReal.toReal_ofReal (le_of_lt hp)]
      have hindM2 : IndepFun (fun ω => Mask ω h.1 h.2) (fun ω => Xi ω h.1 h.2 ^ 2) μ := by
        have h2 : IndepFun (fun ω => Xi ω h.1 h.2 ^ 2) (fun ω => Mask ω h.1 h.2) μ := by
          have hcomp := hIndep.comp ((measurable_pi_apply h).pow_const 2) (measurable_pi_apply h)
          simpa only [Function.comp_apply] using hcomp
        exact h2.symm
      have hSix : ∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 ^ 2 ∂μ = p := by
        have hfac : ∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 ^ 2 ∂μ
            = (∫ ω, Mask ω h.1 h.2 ∂μ) * (∫ ω, Xi ω h.1 h.2 ^ 2 ∂μ) :=
          hindM2.integral_mul_eq_mul_integral (hMask_meas h.1 h.2).aestronglyMeasurable ((hXi_meas h.1 h.2).pow_const 2).aestronglyMeasurable
        rw [hfac, hXi_var h.1 h.2, mul_one, hMask_mean]
      have hcong : ∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h.1 h.2 * Xi ω h.1 h.2) ∂μ
          = ∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        have ha : Mask ω h.1 h.2 * Mask ω h.1 h.2 = Mask ω h.1 h.2 := by
          rcases hMask_val h.1 h.2 ω with h0 | h1
          · rw [h0]; ring
          · rw [h1]; ring
        calc Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h.1 h.2 * Xi ω h.1 h.2)
            = (Mask ω h.1 h.2 * Mask ω h.1 h.2) * (Xi ω h.1 h.2 * Xi ω h.1 h.2) := by ring
          _ = Mask ω h.1 h.2 * (Xi ω h.1 h.2 * Xi ω h.1 h.2) := by rw [ha]
          _ = Mask ω h.1 h.2 * Xi ω h.1 h.2 ^ 2 := by ring
      rw [hcong, hSix, hcc]
      have hpne : p ≠ 0 := ne_of_gt hp
      have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmpos
      have hmpne : (m:ℝ) * p ≠ 0 := ne_of_gt hmp
      field_simp
    · rw [if_neg hh]
      have hfour : ∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2) ∂μ = 0 := by
        have hcong : ∫ ω, Mask ω h.1 h.2 * Xi ω h.1 h.2 * (Mask ω h'.1 h'.2 * Xi ω h'.1 h'.2) ∂μ
            = ∫ ω, (Xi ω h.1 h.2 * Xi ω h'.1 h'.2) * (Mask ω h.1 h.2 * Mask ω h'.1 h'.2) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          ring
        rw [hcong]
        have hind4 : IndepFun (fun ω => Xi ω h.1 h.2 * Xi ω h'.1 h'.2) (fun ω => Mask ω h.1 h.2 * Mask ω h'.1 h'.2) μ := by
          have hcomp := hIndep.comp ((measurable_pi_apply h).mul (measurable_pi_apply h')) ((measurable_pi_apply h).mul (measurable_pi_apply h'))
          simpa only [Function.comp_apply] using hcomp
        have hfac4 : ∫ ω, (Xi ω h.1 h.2 * Xi ω h'.1 h'.2) * (Mask ω h.1 h.2 * Mask ω h'.1 h'.2) ∂μ
            = (∫ ω, Xi ω h.1 h.2 * Xi ω h'.1 h'.2 ∂μ) * (∫ ω, Mask ω h.1 h.2 * Mask ω h'.1 h'.2 ∂μ) :=
          hind4.integral_mul_eq_mul_integral ((hXi_meas h.1 h.2).mul (hXi_meas h'.1 h'.2)).aestronglyMeasurable ((hMask_meas h.1 h.2).mul (hMask_meas h'.1 h'.2)).aestronglyMeasurable
        rw [hfac4]
        have hXiXi' : ∫ ω, Xi ω h.1 h.2 * Xi ω h'.1 h'.2 ∂μ = 0 := by
          have hfac2 : ∫ ω, Xi ω h.1 h.2 * Xi ω h'.1 h'.2 ∂μ
              = (∫ ω, Xi ω h.1 h.2 ∂μ) * (∫ ω, Xi ω h'.1 h'.2 ∂μ) :=
            (hXi_indep.indepFun hh).integral_mul_eq_mul_integral (hXi_meas h.1 h.2).aestronglyMeasurable (hXi_meas h'.1 h'.2).aestronglyMeasurable
          rw [hfac2, hXi_mean h.1 h.2, zero_mul]
        rw [hXiXi', zero_mul]
      rw [hfour, zero_mul]
  /- @proof-region region.target-node.session.de85e0f8a80930d9 end -/

end Statlib.Imported

