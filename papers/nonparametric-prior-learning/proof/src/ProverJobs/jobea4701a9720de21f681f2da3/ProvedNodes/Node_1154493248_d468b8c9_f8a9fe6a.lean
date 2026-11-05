import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_1154493248_d468b8c9 : ∀ {U : Type*} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν]
    (y : U → ℝ≥0∞) (hy : Measurable y) (hy_int : ∫⁻ u, y u ∂ν = 1)
    (c : ℝ≥0∞) (hc : c ≠ ⊤),
    ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((c * y u).toReal)) ∂ν
      = ENNReal.ofReal (InformationTheory.klFun c.toReal)
        + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((y u).toReal)) ∂ν := by
  /- @proof-region region.target-node.session.dd0293ffa346072b begin -/
  intro U _ ν _ y hy hy_int c hc
  have hklFun : ∀ t : ℝ, InformationTheory.klFun t = t * Real.log t + 1 - t := by
    intro t
    unfold InformationTheory.klFun
    ring
  have hklFun_zero : InformationTheory.klFun 0 = 1 := by
    rw [hklFun]
    simp
  have hklFun_one : InformationTheory.klFun 1 = 0 := by
    rw [hklFun]
    simp
  have hklFun_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ InformationTheory.klFun t := by
    intro t ht
    rw [hklFun]
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]
      simp
    · have hinv : 1 - t⁻¹ ≤ Real.log t := by
        have h₁ := Real.log_le_sub_one_of_pos (inv_pos.mpr h)
        rw [Real.log_inv] at h₁
        linarith
      have hmul := mul_le_mul_of_nonneg_left hinv (le_of_lt h)
      have hkey : t * t⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h)
      nlinarith
  set y' : U → ℝ := fun u => (y u).toReal with hy'_def
  set c' : ℝ := c.toReal with hc'_def
  have hy'_nonneg : ∀ u, 0 ≤ y' u := fun u => ENNReal.toReal_nonneg
  have hy'_meas : Measurable y' := ENNReal.measurable_toReal.comp hy
  have hc'_nonneg : 0 ≤ c' := ENNReal.toReal_nonneg
  have hc'_ofReal : ENNReal.ofReal c' = c := ENNReal.ofReal_toReal hc
  have hcy : ∀ u, (c * y u).toReal = c' * y' u := fun u => ENNReal.toReal_mul
  have hy_top : ∀ᵐ u ∂ν, y u < ⊤ :=
    MeasureTheory.ae_lt_top hy (by rw [hy_int]; exact ENNReal.one_ne_top)
  have hy'_lint : ∫⁻ u, ENNReal.ofReal (y' u) ∂ν = 1 := by
    rw [← hy_int]
    exact lintegral_congr_ae (hy_top.mono fun u hu => ENNReal.ofReal_toReal hu.ne)
  have hy'_intble : Integrable y' ν := by
    refine ⟨hy'_meas.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have h : ∫⁻ u, ENNReal.ofReal ‖y' u‖ ∂ν = ∫⁻ u, ENNReal.ofReal (y' u) ∂ν := by
      refine lintegral_congr fun u => ?_
      rw [Real.norm_of_nonneg (hy'_nonneg u)]
    rw [h, hy'_lint]
    exact ENNReal.one_lt_top
  have hy'_integral : ∫ u, y' u ∂ν = 1 := by
    rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
      (Filter.Eventually.of_forall fun u => hy'_nonneg u) hy'_intble, hy'_lint]
    exact ENNReal.toReal_one
  have hmul_id : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → InformationTheory.klFun (a * b)
      = b * InformationTheory.klFun a + a * InformationTheory.klFun b + (1 - a) * (1 - b) := by
    intro a b ha hb
    obtain h | h := eq_or_lt_of_le ha
    · rw [← h]
      simp only [zero_mul]
      rw [hklFun_zero]
      ring
    obtain h2 | h2 := eq_or_lt_of_le hb
    · rw [← h2]
      simp only [mul_zero, zero_mul]
      rw [hklFun_zero]
      ring
    rw [hklFun (a * b), hklFun a, hklFun b, Real.log_mul (ne_of_gt h) (ne_of_gt h2)]
    ring
  have hklFun_meas : Measurable InformationTheory.klFun := by
    have h : InformationTheory.klFun = fun t : ℝ => t * Real.log t + 1 - t := funext hklFun
    rw [h]
    exact ((measurable_id.mul Real.measurable_log).add measurable_const).sub measurable_id
  set sp : U → ℝ := fun u => max ((1 - c') * (1 - y' u)) 0 with hsp_def
  set sm : U → ℝ := fun u => max (-((1 - c') * (1 - y' u))) 0 with hsm_def
  have hs_meas : Measurable fun u => (1 - c') * (1 - y' u) :=
    measurable_const.mul (measurable_const.sub hy'_meas)
  have hmax_id : ∀ a : ℝ, a = max a 0 - max (-a) 0 := by
    intro a
    rcases le_total a 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  have hsp_meas : Measurable sp := by
    rw [hsp_def]
    exact hs_meas.max (measurable_const : Measurable fun _ : U => (0 : ℝ))
  have hsm_meas : Measurable sm := by
    rw [hsm_def]
    exact hs_meas.neg.max (measurable_const : Measurable fun _ : U => (0 : ℝ))
  have hsp_nonneg : ∀ u, 0 ≤ sp u := by
    intro u
    rw [hsp_def]
    exact le_max_right _ 0
  have hsm_nonneg : ∀ u, 0 ≤ sm u := by
    intro u
    rw [hsm_def]
    exact le_max_right _ 0
  have hdecomp : ∀ u, (1 - c') * (1 - y' u) = sp u - sm u := by
    intro u
    rw [hsp_def, hsm_def]
    exact hmax_id _
  have hpt : ∀ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) + ENNReal.ofReal (sm u)
      = ENNReal.ofReal (y' u * InformationTheory.klFun c')
        + ENNReal.ofReal (c' * InformationTheory.klFun (y' u)) + ENNReal.ofReal (sp u) := by
    intro u
    have hid := hmul_id c' (y' u) hc'_nonneg (hy'_nonneg u)
    have hdec' : (1 - c') * (1 - y' u) = sp u - sm u := hdecomp u
    rw [hdec'] at hid
    have hreal : InformationTheory.klFun (c' * y' u) + sm u
        = y' u * InformationTheory.klFun c' + c' * InformationTheory.klFun (y' u) + sp u := by
      linarith
    have hK : 0 ≤ InformationTheory.klFun (c' * y' u) :=
      hklFun_nonneg _ (mul_nonneg hc'_nonneg (hy'_nonneg u))
    have hA : 0 ≤ y' u * InformationTheory.klFun c' :=
      mul_nonneg (hy'_nonneg u) (hklFun_nonneg _ hc'_nonneg)
    have hB : 0 ≤ c' * InformationTheory.klFun (y' u) :=
      mul_nonneg hc'_nonneg (hklFun_nonneg _ (hy'_nonneg u))
    calc ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) + ENNReal.ofReal (sm u)
        = ENNReal.ofReal (InformationTheory.klFun (c' * y' u) + sm u) :=
          (ENNReal.ofReal_add hK (hsm_nonneg u)).symm
      _ = ENNReal.ofReal (y' u * InformationTheory.klFun c'
            + c' * InformationTheory.klFun (y' u) + sp u) := by rw [hreal]
      _ = ENNReal.ofReal (y' u * InformationTheory.klFun c'
            + c' * InformationTheory.klFun (y' u)) + ENNReal.ofReal (sp u) :=
          ENNReal.ofReal_add (add_nonneg hA hB) (hsp_nonneg u)
      _ = (ENNReal.ofReal (y' u * InformationTheory.klFun c')
            + ENNReal.ofReal (c' * InformationTheory.klFun (y' u))) + ENNReal.ofReal (sp u) := by
          rw [ENNReal.ofReal_add hA hB]
  have hInt_eq : ∫⁻ u, (ENNReal.ofReal (InformationTheory.klFun (c' * y' u))
        + ENNReal.ofReal (sm u)) ∂ν
      = ∫⁻ u, (ENNReal.ofReal (y' u * InformationTheory.klFun c')
          + ENNReal.ofReal (c' * InformationTheory.klFun (y' u)) + ENNReal.ofReal (sp u)) ∂ν :=
    lintegral_congr hpt
  have hK_meas : Measurable fun u => ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) :=
    ENNReal.measurable_ofReal.comp (hklFun_meas.comp (measurable_const.mul hy'_meas))
  have hsm_ofReal_meas : Measurable fun u => ENNReal.ofReal (sm u) :=
    ENNReal.measurable_ofReal.comp hsm_meas
  have hA_meas : Measurable fun u => ENNReal.ofReal (y' u * InformationTheory.klFun c') :=
    ENNReal.measurable_ofReal.comp (hy'_meas.mul measurable_const)
  have hB_meas : Measurable fun u => ENNReal.ofReal (c' * InformationTheory.klFun (y' u)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hklFun_meas.comp hy'_meas))
  have hsp_ofReal_meas : Measurable fun u => ENNReal.ofReal (sp u) :=
    ENNReal.measurable_ofReal.comp hsp_meas
  have hπ₁ : ∫⁻ u, ENNReal.ofReal (y' u * InformationTheory.klFun c') ∂ν
      = ENNReal.ofReal (InformationTheory.klFun c') := by
    have hone : ∫⁻ u, ENNReal.ofReal (y' u * InformationTheory.klFun c') ∂ν
        = ∫⁻ u, ENNReal.ofReal (y' u) * ENNReal.ofReal (InformationTheory.klFun c') ∂ν :=
      lintegral_congr fun u => ENNReal.ofReal_mul (hy'_nonneg u)
    rw [hone, MeasureTheory.lintegral_mul_const, hy'_lint, one_mul]
    exact ENNReal.measurable_ofReal.comp hy'_meas
  have hπ₂ : ∫⁻ u, ENNReal.ofReal (c' * InformationTheory.klFun (y' u)) ∂ν
      = c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν := by
    have hone : ∫⁻ u, ENNReal.ofReal (c' * InformationTheory.klFun (y' u)) ∂ν
        = ∫⁻ u, c * ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν := by
      refine lintegral_congr fun u => ?_
      rw [ENNReal.ofReal_mul hc'_nonneg, hc'_ofReal]
    rw [hone, MeasureTheory.lintegral_const_mul]
    exact ENNReal.measurable_ofReal.comp (hklFun_meas.comp hy'_meas)
  have hreal_univ : ν.real Set.univ = 1 := by simp
  have hconst : ∫ u, (1 : ℝ) ∂ν = 1 := by
    rw [MeasureTheory.integral_const, hreal_univ]
    simp
  have hs_intble : Integrable (fun u => (1 - c') * (1 - y' u)) ν := by
    have h : Integrable (fun u => (1 - c') - (1 - c') * y' u) ν :=
      (integrable_const (1 - c')).sub (hy'_intble.const_mul (1 - c'))
    refine h.congr ?_
    filter_upwards with u
    ring
  have hs_zero : ∫ u, (1 - c') * (1 - y' u) ∂ν = 0 := by
    rw [MeasureTheory.integral_const_mul]
    have h1 : ∫ u, (1 - y' u) ∂ν = 0 := by
      rw [MeasureTheory.integral_sub (integrable_const (1 : ℝ)) hy'_intble, hconst, hy'_integral]
      ring
    rw [h1, mul_zero]
  have hclamp : ∀ r : ℝ, ENNReal.ofReal r = ENNReal.ofReal (max r 0) := by
    intro r
    rcases le_total r 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h]
      simp
    · rw [max_eq_left h]
  have habs : ∀ u, |(1 - c') * (1 - y' u)| = sp u + sm u := by
    intro u
    rw [hsp_def, hsm_def]
    dsimp only
    rcases le_total ((1 - c') * (1 - y' u)) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]
      ring
  have hfin_sp : ∫⁻ u, ENNReal.ofReal (sp u) ∂ν < ⊤ := by
    have h := hs_intble.2
    rw [MeasureTheory.hasFiniteIntegral_iff_norm] at h
    have heq : ∫⁻ u, ENNReal.ofReal ‖(1 - c') * (1 - y' u)‖ ∂ν
        = ∫⁻ u, (ENNReal.ofReal (sp u) + ENNReal.ofReal (sm u)) ∂ν := by
      refine lintegral_congr fun u => ?_
      rw [Real.norm_eq_abs, habs u, ENNReal.ofReal_add (hsp_nonneg u) (hsm_nonneg u)]
    rw [heq, MeasureTheory.lintegral_add_left hsp_ofReal_meas] at h
    exact (ENNReal.add_lt_top.mp h).1
  have hfin_sm : ∫⁻ u, ENNReal.ofReal (sm u) ∂ν < ⊤ := by
    have h := hs_intble.2
    rw [MeasureTheory.hasFiniteIntegral_iff_norm] at h
    have heq : ∫⁻ u, ENNReal.ofReal ‖(1 - c') * (1 - y' u)‖ ∂ν
        = ∫⁻ u, (ENNReal.ofReal (sm u) + ENNReal.ofReal (sp u)) ∂ν := by
      refine lintegral_congr fun u => ?_
      rw [Real.norm_eq_abs, habs u, ENNReal.ofReal_add (hsp_nonneg u) (hsm_nonneg u), add_comm]
    rw [heq, MeasureTheory.lintegral_add_left hsm_ofReal_meas] at h
    exact (ENNReal.add_lt_top.mp h).1
  have hsp_eq_sm : ∫⁻ u, ENNReal.ofReal (sp u) ∂ν = ∫⁻ u, ENNReal.ofReal (sm u) ∂ν := by
    have hpos := MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part (μ := ν) hs_intble
    have e1 : ∫⁻ u, ENNReal.ofReal (sp u) ∂ν
        = ∫⁻ u, ENNReal.ofReal ((1 - c') * (1 - y' u)) ∂ν := by
      refine lintegral_congr fun u => ?_
      rw [hsp_def, ← hclamp]
    have e2 : ∫⁻ u, ENNReal.ofReal (sm u) ∂ν
        = ∫⁻ u, ENNReal.ofReal (-((1 - c') * (1 - y' u))) ∂ν := by
      refine lintegral_congr fun u => ?_
      rw [hsm_def, ← hclamp]
    rw [hs_zero, ← e1, ← e2] at hpos
    have h0 : (∫⁻ u, ENNReal.ofReal (sp u) ∂ν).toReal
        = (∫⁻ u, ENNReal.ofReal (sm u) ∂ν).toReal := by linarith
    have hA := (ENNReal.ofReal_toReal hfin_sp.ne).symm
    have hB := (ENNReal.ofReal_toReal hfin_sm.ne).symm
    rw [hA, hB, h0]
  have hL : ∫⁻ u, (ENNReal.ofReal (InformationTheory.klFun (c' * y' u))
        + ENNReal.ofReal (sm u)) ∂ν
      = ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν
        + ∫⁻ u, ENNReal.ofReal (sm u) ∂ν :=
    MeasureTheory.lintegral_add_left hK_meas _
  have hR : ∫⁻ u, (ENNReal.ofReal (y' u * InformationTheory.klFun c')
        + ENNReal.ofReal (c' * InformationTheory.klFun (y' u)) + ENNReal.ofReal (sp u)) ∂ν
      = (∫⁻ u, ENNReal.ofReal (y' u * InformationTheory.klFun c') ∂ν
          + ∫⁻ u, ENNReal.ofReal (c' * InformationTheory.klFun (y' u)) ∂ν)
        + ∫⁻ u, ENNReal.ofReal (sp u) ∂ν := by
    rw [MeasureTheory.lintegral_add_left (hA_meas.add hB_meas),
      MeasureTheory.lintegral_add_left hA_meas]
  have hchain : ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν
        + ∫⁻ u, ENNReal.ofReal (sm u) ∂ν
      = (ENNReal.ofReal (InformationTheory.klFun c')
          + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν)
        + ∫⁻ u, ENNReal.ofReal (sp u) ∂ν := by
    rw [← hL, hInt_eq, hR, hπ₁, hπ₂]
  rw [hsp_eq_sm] at hchain
  have hcancel : ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν
      = ENNReal.ofReal (InformationTheory.klFun c')
        + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν := by
    by_cases ha : (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν) = ⊤
    · have hb : ENNReal.ofReal (InformationTheory.klFun c')
          + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν = ⊤ := by
        by_contra hb
        have hbm : ENNReal.ofReal (InformationTheory.klFun c')
            + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν < ⊤ :=
          lt_of_le_of_ne le_top hb
        have hfinb : (ENNReal.ofReal (InformationTheory.klFun c')
              + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν)
            + ∫⁻ u, ENNReal.ofReal (sm u) ∂ν < ⊤ := by
          rw [ENNReal.add_lt_top]
          exact ⟨hbm, hfin_sm⟩
        have hfina : (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν)
            + ∫⁻ u, ENNReal.ofReal (sm u) ∂ν < ⊤ := by
          rw [hchain]
          exact hfinb
        exact absurd ha (ENNReal.add_lt_top.mp hfina).1.ne
      rw [ha, hb]
    · have hlt_a : (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν) < ⊤ :=
        lt_of_le_of_ne le_top ha
      have hfin_a : (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν)
          + ∫⁻ u, ENNReal.ofReal (sm u) ∂ν < ⊤ := by
        rw [ENNReal.add_lt_top]
        exact ⟨hlt_a, hfin_sm⟩
      have hfin_b : (ENNReal.ofReal (InformationTheory.klFun c')
            + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν)
          + ∫⁻ u, ENNReal.ofReal (sm u) ∂ν < ⊤ := hchain ▸ hfin_a
      have hlt_b : ENNReal.ofReal (InformationTheory.klFun c')
          + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν < ⊤ :=
        (ENNReal.add_lt_top.mp hfin_b).1
      have hkey : (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν).toReal
          = (ENNReal.ofReal (InformationTheory.klFun c')
              + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν).toReal := by
        have e1 : ENNReal.ofReal ((∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν).toReal
              + (∫⁻ u, ENNReal.ofReal (sm u) ∂ν).toReal)
            = (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν)
              + ∫⁻ u, ENNReal.ofReal (sm u) ∂ν := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hfin_sm.ne]
        have e2 : ENNReal.ofReal ((ENNReal.ofReal (InformationTheory.klFun c')
                + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν).toReal
              + (∫⁻ u, ENNReal.ofReal (sm u) ∂ν).toReal)
            = (ENNReal.ofReal (InformationTheory.klFun c')
                + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν)
              + ∫⁻ u, ENNReal.ofReal (sm u) ∂ν := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hlt_b.ne, ENNReal.ofReal_toReal hfin_sm.ne]
        have e3 : ENNReal.ofReal ((∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν).toReal
              + (∫⁻ u, ENNReal.ofReal (sm u) ∂ν).toReal)
            = ENNReal.ofReal ((ENNReal.ofReal (InformationTheory.klFun c')
                + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν).toReal
                + (∫⁻ u, ENNReal.ofReal (sm u) ∂ν).toReal) := by
          rw [e1, hchain, e2]
        have e4 := congrArg ENNReal.toReal e3
        rw [ENNReal.toReal_ofReal (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
          ENNReal.toReal_ofReal (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)] at e4
        linarith
      calc ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν
          = ENNReal.ofReal ((∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν).toReal) :=
            (ENNReal.ofReal_toReal ha).symm
        _ = ENNReal.ofReal ((ENNReal.ofReal (InformationTheory.klFun c')
              + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν).toReal) := by
            rw [hkey]
        _ = ENNReal.ofReal (InformationTheory.klFun c')
              + c * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν :=
            ENNReal.ofReal_toReal hlt_b.ne
  have hgoalR : ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((y u).toReal)) ∂ν
      = ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (y' u)) ∂ν := by
    refine lintegral_congr fun u => ?_
    rw [show (y u).toReal = y' u from rfl]
  have hgoalL : ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((c * y u).toReal)) ∂ν
      = ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun (c' * y' u)) ∂ν := by
    refine lintegral_congr fun u => ?_
    rw [hcy u]
  rw [hgoalL, hgoalR, hcancel]
  /- @proof-region region.target-node.session.dd0293ffa346072b end -/

end
end Statlib.Imported
