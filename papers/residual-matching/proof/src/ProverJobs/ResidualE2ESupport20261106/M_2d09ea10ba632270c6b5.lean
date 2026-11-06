import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
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
theorem statopia_math_node_1142199188_2b6c5b39 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (p Kt : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) (hKt : 0 < Kt)
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ i j, Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ i j, Integrable (fun ω => Xi ω i j) μ)
    (hXi_sq_int : ∀ i j, Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_mean : ∀ i j, ∫ ω, Xi ω i j ∂μ = 0)
    (hXi_var : ∀ i j, ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
    (hXi_tail : ∀ i j (t : ℝ), 0 < t →
      μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (hMask_meas : ∀ i j, Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ i j ω, Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ i j, μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
    (∀ i j, Integrable (fun ω => |Xi ω i j| ^ 3) μ ∧
        ∫ ω, |Xi ω i j| ^ 3 ∂μ ≤ 12 * Kt ^ 3) ∧
      (∑ i : Fin m, ∑ j : Fin n, (∫ ω, |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3 ∂μ))
        ≤ ((m : ℝ) + (n : ℝ)) * (24 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹) := by
  /- @proof-region region.target-node.session.74fe7cf15d98e525 begin -/
  intro Ω _ μ _ m n hm hn p Kt hp_pos hp_le hKt Xi Mask hXi_meas hXi_int hXi_sq_int hXi_mean
    hXi_var hXi_tail hMask_meas hMask_val hMask_law hIndep
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmp : (0 : ℝ) < (m : ℝ) * p := mul_pos hmR hp_pos
  have hConc1 : ∀ i j, Integrable (fun ω => |Xi ω i j| ^ 3) μ ∧
      ∫ ω, |Xi ω i j| ^ 3 ∂μ ≤ 12 * Kt ^ 3 := by
    intro i j
    have hpiece : ∀ x : ℝ, 0 ≤ x →
        ∫⁻ s in Set.Ioo (0:ℝ) x, ENNReal.ofReal (3 * s ^ 2) = ENNReal.ofReal (x ^ 3) := by
      intro x hx
      have hcont : ContinuousOn (fun s : ℝ => 3 * s ^ 2) (Set.Icc (0:ℝ) x) :=
        (by fun_prop : Continuous fun s : ℝ => 3 * s ^ 2).continuousOn
      have hIcc : IntegrableOn (fun s : ℝ => 3 * s ^ 2) (Set.Icc (0:ℝ) x) :=
        ContinuousOn.integrableOn_Icc hcont
      have hIntOn : IntegrableOn (fun s : ℝ => 3 * s ^ 2) (Set.Ioo (0:ℝ) x) :=
        hIcc.mono_set Set.Ioo_subset_Icc_self
      have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo (0:ℝ) x)] (fun s : ℝ => 3 * s ^ 2) :=
        Filter.Eventually.of_forall (fun s => by positivity)
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntOn hnonneg]
      congr 1
      have hII : IntervalIntegrable (fun s : ℝ => 3 * s ^ 2) volume 0 x :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) hx).mpr hIcc
      have h3 : ∫ s in (0:ℝ)..x, 3 * s ^ 2 = x ^ 3 := by
        have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) x, HasDerivAt (fun t : ℝ => t ^ 3) (3 * s ^ 2) s := by
          intro s _
          simpa using hasDerivAt_pow 3 s
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hII]
        simp
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo (f := fun s : ℝ => 3 * s ^ 2),
        ← intervalIntegral.integral_of_le hx]
      exact h3
    set S : Set (Ω × ℝ) := {p | (0:ℝ) < p.2} ∩ {p | p.2 - |Xi p.1 i j| < 0} with hS
    set G : Ω × ℝ → ENNReal :=
      fun p => S.indicator (fun p : Ω × ℝ => ENNReal.ofReal (3 * p.2 ^ 2)) p with hG
    have hSmeas : MeasurableSet S := by
      rw [hS]
      have h1 : MeasurableSet {p : Ω × ℝ | (0:ℝ) < p.2} := measurable_snd measurableSet_Ioi
      have h2 : MeasurableSet {p : Ω × ℝ | p.2 - |Xi p.1 i j| < 0} :=
        (measurable_snd.sub ((hXi_meas i j).abs.comp measurable_fst)) measurableSet_Iio
      exact h1.inter h2
    have hGmeas : AEMeasurable G (μ.prod volume) := by
      rw [hG]
      have hval : Measurable fun p : Ω × ℝ => ENNReal.ofReal (3 * p.2 ^ 2) :=
        ENNReal.continuous_ofReal.measurable.comp (by
          have h : Measurable fun p : Ω × ℝ => (3:ℝ) * (p.2 * p.2) :=
            measurable_const.mul (measurable_snd.mul measurable_snd)
          simpa [pow_two] using h)
      exact (hval.indicator hSmeas).aemeasurable
    have hstep1 : ∫⁻ ω, ENNReal.ofReal (|Xi ω i j| ^ 3) ∂μ
        = ∫⁻ ω, ∫⁻ s, G (ω, s) ∂volume ∂μ := by
      apply MeasureTheory.lintegral_congr
      intro ω
      have hfun : (fun s : ℝ => G (ω, s))
          = (Set.Ioo (0:ℝ) |Xi ω i j|).indicator (fun s : ℝ => ENNReal.ofReal (3 * s ^ 2)) := by
        funext s
        by_cases h1 : 0 < s <;> by_cases h2 : s < |Xi ω i j|
        · simp [hG, hS, h1, h2]
        · simp [hG, hS, h1, h2]
        · simp [hG, hS, h1, h2]
        · simp [hG, hS, h1, h2]
      rw [hfun, MeasureTheory.lintegral_indicator measurableSet_Ioo]
      exact (hpiece |Xi ω i j| (abs_nonneg _)).symm
    have hstep2 : ∫⁻ ω, ∫⁻ s, G (ω, s) ∂volume ∂μ = ∫⁻ s, ∫⁻ ω, G (ω, s) ∂μ ∂volume := by
      have h := MeasureTheory.lintegral_lintegral_swap (f := fun ω s => G (ω, s))
        (by simpa using hGmeas)
      simpa using h
    have hstep3 : ∫⁻ s, ∫⁻ ω, G (ω, s) ∂μ ∂volume
        = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (3 * s ^ 2) * μ {ω | s < |Xi ω i j|} := by
      rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi]
      apply MeasureTheory.lintegral_congr
      intro s
      by_cases hs : 0 < s
      · have hfun : (fun ω => G (ω, s))
            = ({ω : Ω | s < |Xi ω i j|}).indicator (fun _ => ENNReal.ofReal (3 * s ^ 2)) := by
          funext ω
          by_cases h2 : s < |Xi ω i j|
          · simp [hG, hS, hs, h2]
          · simp [hG, hS, hs, h2]
        have hset : MeasurableSet {ω : Ω | s < |Xi ω i j|} :=
          (hXi_meas i j).abs measurableSet_Ioi
        rw [hfun, MeasureTheory.lintegral_indicator_const hset (ENNReal.ofReal (3 * s ^ 2)),
          Set.indicator_of_mem (Set.mem_Ioi.mpr hs)]
      · simp [hG, hS, hs]
    have hIntExp : IntegrableOn (fun s : ℝ => 3 * s ^ 2 * (2 * Real.exp (-(1 / Kt * s))))
        (Set.Ioi 0) := by
      have hbase : IntegrableOn (fun s : ℝ => s ^ 2 * Real.exp (-(1 / Kt * s))) (Set.Ioi 0) := by
        have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2) (b := 1 / Kt)
          (by norm_num) (by norm_num) (by positivity)
        simpa [Real.rpow_two, Real.rpow_one, neg_mul] using h
      have h2 : (fun s : ℝ => 3 * s ^ 2 * (2 * Real.exp (-(1 / Kt * s))))
          = fun s : ℝ => (6:ℝ) * (s ^ 2 * Real.exp (-(1 / Kt * s))) := by
        funext s
        ring
      rw [h2]
      exact hbase.const_mul 6
    have hvalInt : ∫ s in Set.Ioi (0:ℝ), 3 * s ^ 2 * (2 * Real.exp (-(1 / Kt * s)))
        = 12 * Kt ^ 3 := by
      have hgen : ∫ s in Set.Ioi (0:ℝ), s ^ 2 * Real.exp (-(1 / Kt * s)) = Kt ^ 3 * 2 := by
        have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1 / Kt)
          (by norm_num) (by positivity)
        have h3 : (3:ℝ) - 1 = ((2:ℕ) : ℝ) := by norm_num
        simp only [h3, Real.rpow_natCast] at h
        rw [h]
        have hΓ : Real.Gamma 3 = 2 := by
          have h2 := Real.Gamma_nat_eq_factorial 2
          rw [show (3:ℝ) = ((2:ℕ):ℝ) + 1 by norm_num]
          rw [h2]
          norm_num
        rw [hΓ]
        have hK : (1:ℝ) / (1 / Kt) = Kt := by
          field_simp
        rw [hK]
        have h3' : (3:ℝ) = ((3:ℕ) : ℝ) := by norm_num
        simp only [h3', Real.rpow_natCast]
      have h6 : ∫ s in Set.Ioi (0:ℝ), 3 * s ^ 2 * (2 * Real.exp (-(1 / Kt * s)))
          = 6 * ∫ s in Set.Ioi (0:ℝ), s ^ 2 * Real.exp (-(1 / Kt * s)) := by
        have hpt6 : (fun s : ℝ => 3 * s ^ 2 * (2 * Real.exp (-(1 / Kt * s))))
            = fun s : ℝ => (6:ℝ) * (s ^ 2 * Real.exp (-(1 / Kt * s))) := by
          funext s
          ring
        rw [hpt6, MeasureTheory.integral_const_mul]
      rw [h6, hgen]
      ring
    have hstep4 : ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (3 * s ^ 2) * μ {ω | s < |Xi ω i j|}
        ≤ ENNReal.ofReal (12 * Kt ^ 3) := by
      have hmono : ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (3 * s ^ 2) * μ {ω | s < |Xi ω i j|}
          ≤ ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (3 * s ^ 2) *
              ENNReal.ofReal (2 * Real.exp (-s / Kt)) := by
        rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi,
          ← MeasureTheory.lintegral_indicator measurableSet_Ioi]
        apply MeasureTheory.lintegral_mono
        intro s
        by_cases hs : 0 < s
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hs), Set.indicator_of_mem (Set.mem_Ioi.mpr hs)]
          exact mul_le_mul_left' (hXi_tail i j s hs) _
        · rw [Set.indicator_of_notMem (by simpa using hs),
            Set.indicator_of_notMem (by simpa using hs)]
      refine le_trans hmono ?_
      have hfin : ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (3 * s ^ 2) *
            ENNReal.ofReal (2 * Real.exp (-s / Kt)) = ENNReal.ofReal (12 * Kt ^ 3) := by
        have hpt : ∀ s : ℝ, ENNReal.ofReal (3 * s ^ 2) * ENNReal.ofReal (2 * Real.exp (-s / Kt))
            = ENNReal.ofReal (3 * s ^ 2 * (2 * Real.exp (-s / Kt))) := by
          intro s
          rw [← ENNReal.ofReal_mul (by positivity)]
        simp only [hpt]
        have hpt2 : ∀ s : ℝ, 3 * s ^ 2 * (2 * Real.exp (-s / Kt))
            = 3 * s ^ 2 * (2 * Real.exp (-(1 / Kt * s))) := by
          intro s
          rw [show -s / Kt = -(1 / Kt * s) by ring]
        simp only [hpt2]
        have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
            (fun s : ℝ => 3 * s ^ 2 * (2 * Real.exp (-(1 / Kt * s)))) :=
          Filter.Eventually.of_forall (fun s => by positivity)
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntExp hnonneg]
        rw [hvalInt]
      rw [hfin]
    have hkey : ∫⁻ ω, ENNReal.ofReal (|Xi ω i j| ^ 3) ∂μ ≤ ENNReal.ofReal (12 * Kt ^ 3) := by
      rw [hstep1, hstep2, hstep3]
      exact hstep4
    have hne : ∫⁻ ω, ENNReal.ofReal (|Xi ω i j| ^ 3) ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkey
    have hInt : Integrable (fun ω => |Xi ω i j| ^ 3) μ := by
      refine ⟨?_, ?_⟩
      · exact ((by fun_prop : Continuous fun y : ℝ => |y| ^ 3).measurable.comp
          (hXi_meas i j)).aestronglyMeasurable
      · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
        have hnorm : ∫⁻ a, ENNReal.ofReal ‖|Xi a i j| ^ 3‖ ∂μ
            = ∫⁻ a, ENNReal.ofReal (|Xi a i j| ^ 3) ∂μ := by
          apply MeasureTheory.lintegral_congr
          intro a
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
        rw [hnorm]
        exact lt_top_iff_ne_top.mpr hne
    refine ⟨hInt, ?_⟩
    have hnn : 0 ≤ ∫ ω, |Xi ω i j| ^ 3 ∂μ :=
      MeasureTheory.integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3)
    have h1 : ENNReal.ofReal (∫ ω, |Xi ω i j| ^ 3 ∂μ) ≤ ENNReal.ofReal (12 * Kt ^ 3) := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg _) 3))]
      exact hkey
    have h2 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr h1
    rwa [ENNReal.toReal_ofReal hnn, ENNReal.toReal_ofReal (by positivity)] at h2
  have hConc2 : (∑ i : Fin m, ∑ j : Fin n,
        (∫ ω, |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3 ∂μ))
      ≤ ((m : ℝ) + (n : ℝ)) * (24 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹) := by
    have hterm : ∀ i j, (∫ ω, |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3 ∂μ)
        ≤ 12 * Kt ^ 3 * p * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹ := by
      intro i j
      obtain ⟨hInt3, hBnd3⟩ := hConc1 i j
      have hspos : 0 < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.2 hmp
      have hmeasset : MeasurableSet {ω : Ω | Mask ω i j = 1} :=
        (hMask_meas i j) (measurableSet_singleton 1)
      have hpt : ∀ ω, |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3
          = Mask ω i j * |Xi ω i j| ^ 3 * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹ := by
        intro ω
        rcases hMask_val i j ω with h | h
        · rw [maskedScaled, h]
          simp
        · rw [maskedScaled, h]
          simp only [one_mul, abs_div, abs_of_pos hspos, div_pow, div_eq_mul_inv, abs_mul, abs_inv,
            mul_pow, inv_pow]
      have hMaskInd : (fun ω => Mask ω i j)
          = ({ω : Ω | Mask ω i j = 1} : Set Ω).indicator (fun _ => (1 : ℝ)) := by
        funext ω
        rcases hMask_val i j ω with h | h
        · rw [h, Set.indicator_of_notMem (by simp [h])]
        · rw [h, Set.indicator_of_mem (by simpa using h)]
      have hMaskInt : Integrable (fun ω => Mask ω i j) μ := by
        rw [hMaskInd]
        exact (integrable_const (1 : ℝ)).indicator hmeasset
      have hMaskval : ∫ ω, Mask ω i j ∂μ = p := by
        have hnonneg : 0 ≤ᵐ[μ] (fun ω => Mask ω i j) := by
          filter_upwards with ω
          rcases hMask_val i j ω with h | h <;> simp [h]
        rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
          hnonneg hMaskInt]
        have hli : ∫⁻ ω, ENNReal.ofReal (Mask ω i j) ∂μ = ENNReal.ofReal p := by
          have hpt2 : ∀ ω, ENNReal.ofReal (Mask ω i j)
              = ({ω : Ω | Mask ω i j = 1} : Set Ω).indicator (fun _ => (1 : ENNReal)) ω := by
            intro ω
            rcases hMask_val i j ω with h | h
            · rw [h, ENNReal.ofReal_zero, Set.indicator_of_notMem (by simp [h])]
            · rw [h, ENNReal.ofReal_one, Set.indicator_of_mem (by simpa using h)]
          simp only [hpt2]
          rw [MeasureTheory.lintegral_indicator_const hmeasset (1 : ENNReal), one_mul]
          exact hMask_law i j
        rw [hli, ENNReal.toReal_ofReal hp_pos.le]
      have hproj : IndepFun (fun ω => Mask ω i j) (fun ω => Xi ω i j) μ := by
        have hφ : Measurable (fun v : Fin m × Fin n → ℝ => v (i, j)) :=
          measurable_pi_apply (X := fun _ : Fin m × Fin n => ℝ) (i, j)
        have h2 := hIndep.symm.comp
          (φ := fun v : Fin m × Fin n → ℝ => v (i, j))
          (ψ := fun v : Fin m × Fin n → ℝ => v (i, j)) hφ hφ
        simpa [Function.comp] using h2
      have hcomp : IndepFun (fun ω => Mask ω i j) (fun ω => |Xi ω i j| ^ 3) μ := by
        have hψ : Measurable (fun y : ℝ => |y| ^ 3) :=
          (by fun_prop : Continuous fun y : ℝ => |y| ^ 3).measurable
        have h2 := hproj.comp (φ := id) (ψ := fun y : ℝ => |y| ^ 3) measurable_id hψ
        simpa [Function.comp] using h2
      have hprod : ∫ ω, Mask ω i j * |Xi ω i j| ^ 3 ∂μ
          = (∫ ω, Mask ω i j ∂μ) * (∫ ω, |Xi ω i j| ^ 3 ∂μ) := by
        have h2 := hcomp.integral_fun_comp_mul_comp (f := id) (g := id)
          (by measurability) (by measurability) aestronglyMeasurable_id aestronglyMeasurable_id
        simpa using h2
      calc (∫ ω, |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3 ∂μ)
          = ∫ ω, Mask ω i j * |Xi ω i j| ^ 3 * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹ ∂μ := by
            simp only [hpt]
        _ = (∫ ω, Mask ω i j * |Xi ω i j| ^ 3 ∂μ) * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹ := by
            rw [MeasureTheory.integral_mul_const]
        _ = ((∫ ω, Mask ω i j ∂μ) * (∫ ω, |Xi ω i j| ^ 3 ∂μ))
              * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹ := by
            rw [hprod]
        _ = (p * (∫ ω, |Xi ω i j| ^ 3 ∂μ)) * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹ := by
            rw [hMaskval]
        _ ≤ (p * (12 * Kt ^ 3)) * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹ := by
            have hinv : 0 ≤ (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹ := by positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBnd3 hp_pos.le) hinv
        _ = 12 * Kt ^ 3 * p * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹ := by ring
    have hsum1 : (∑ i : Fin m, ∑ j : Fin n,
          (∫ ω, |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3 ∂μ))
        ≤ ∑ i : Fin m, ∑ j : Fin n,
            (12 * Kt ^ 3 * p * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hterm i j
    have hsum2 : (∑ i : Fin m, ∑ j : Fin n,
          (12 * Kt ^ 3 * p * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹))
        = ((m : ℝ) * (n : ℝ)) * (12 * Kt ^ 3 * p * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    refine le_trans hsum1 ?_
    rw [hsum2]
    have hS2 : Real.sqrt ((m : ℝ) * p) ^ 2 = (m : ℝ) * p := Real.sq_sqrt hmp.le
    have hSpos : 0 < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.2 hmp
    have hSne : Real.sqrt ((m : ℝ) * p) ≠ 0 := ne_of_gt hSpos
    apply le_of_mul_le_mul_right _ (pow_pos hSpos 3)
    have h4 : ((m : ℝ) * (n : ℝ)) * (12 * Kt ^ 3 * p * (Real.sqrt ((m : ℝ) * p) ^ 3)⁻¹)
          * Real.sqrt ((m : ℝ) * p) ^ 3 = (m : ℝ) * (n : ℝ) * (12 * Kt ^ 3 * p) := by
      field_simp
    have hS3 : Real.sqrt ((m : ℝ) * p) ^ 3
        = (m : ℝ) * p * Real.sqrt ((m : ℝ) * p) := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hS2]
    have h5 : ((m : ℝ) + (n : ℝ)) * (24 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹)
          * Real.sqrt ((m : ℝ) * p) ^ 3
        = ((m : ℝ) + (n : ℝ)) * (24 * Kt ^ 3 * ((m : ℝ) * p)) := by
      rw [hS3]
      field_simp
    rw [h4, h5]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfac : (0 : ℝ) < 12 * Kt ^ 3 * p * (m : ℝ) := by positivity
    have hlhs : (m : ℝ) * (n : ℝ) * (12 * Kt ^ 3 * p)
        = (12 * Kt ^ 3 * p * (m : ℝ)) * (n : ℝ) := by ring
    have hrhs : ((m : ℝ) + (n : ℝ)) * (24 * Kt ^ 3 * ((m : ℝ) * p))
        = (12 * Kt ^ 3 * p * (m : ℝ)) * (2 * ((m : ℝ) + (n : ℝ))) := by ring
    rw [hlhs, hrhs]
    apply mul_le_mul_of_nonneg_left _ hfac.le
    linarith
  exact ⟨hConc1, hConc2⟩
  /- @proof-region region.target-node.session.74fe7cf15d98e525 end -/

end Statlib.Imported

