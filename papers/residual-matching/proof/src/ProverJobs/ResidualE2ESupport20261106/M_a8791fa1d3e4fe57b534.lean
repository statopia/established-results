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
theorem statopia_math_node_895243969_77380b6a : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → ℝ) (Kt : ℝ) (L : ℝ) (hKt : 0 < Kt) (hL : 0 < L)
    (hXi_meas : Measurable ξ)
    (hXi_int : Integrable ξ μ)
    (hXi_mean : ∫ ω, ξ ω ∂μ = 0)
    (hXi_sq_int : Integrable (fun ω => (ξ ω) ^ 2) μ)
    (hXi_var : ∫ ω, (ξ ω) ^ 2 ∂μ = 1)
    (hXi_tail : ∀ t : ℝ, 0 < t → μ {ω | t < |ξ ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (htrunc_int : Integrable (fun ω => ξ ω * (if |ξ ω| ≤ L then (1 : ℝ) else 0)) μ)
    (htail_int : Integrable (fun ω => (ξ ω) ^ 2 * (if |ξ ω| ≤ L then (0 : ℝ) else 1)) μ),
    |∫ ω, ξ ω * (if |ξ ω| ≤ L then (1 : ℝ) else 0) ∂μ|
        ≤ 2 * (L + Kt) * Real.exp (-L / Kt) ∧
      ∫ ω, (ξ ω) ^ 2 * (if |ξ ω| ≤ L then (0 : ℝ) else 1) ∂μ
        ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) := by
  /- @proof-region region.target-node.session.b1d1ab7351e29a87 begin -/
  intro Ω _ μ _ xi Kt L hKt hL hxi_meas hxi_int hxi_mean hxi_sq_int hxi_var hxi_tail h_trunc_int h_tail_int
  have hKtne : Kt ≠ 0 := ne_of_gt hKt
  have intA : ∫ x in Set.Ioi L, 2 * Real.exp (-x / Kt) = 2 * Kt * Real.exp (-L / Kt) := by
    have hderiv : ∀ x ∈ Set.Ici L,
        HasDerivAt (fun t : ℝ => -2 * Kt * Real.exp (-t / Kt)) (2 * Real.exp (-x / Kt)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => -t / Kt) (-1 / Kt) x :=
        (hasDerivAt_id x).neg.div_const Kt
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t / Kt))
          (Real.exp (-x / Kt) * (-1 / Kt)) x := by
        have hc := HasDerivAt.comp x (Real.hasDerivAt_exp (-x / Kt)) h1
        simpa using hc
      have h3 : HasDerivAt (fun t : ℝ => -2 * Kt * Real.exp (-t / Kt))
          (-2 * Kt * (Real.exp (-x / Kt) * (-1 / Kt))) x := h2.const_mul (-2 * Kt)
      have hcoef : -2 * Kt * (-1 / Kt) = 2 := by
        field_simp
      have hv : -2 * Kt * (Real.exp (-x / Kt) * (-1 / Kt)) = 2 * Real.exp (-x / Kt) := by
        calc -2 * Kt * (Real.exp (-x / Kt) * (-1 / Kt))
            = (-2 * Kt * (-1 / Kt)) * Real.exp (-x / Kt) := by ring
          _ = 2 * Real.exp (-x / Kt) := by rw [hcoef]
      rw [hv] at h3
      exact h3
    have hmono : ∀ x ∈ Set.Ioi L, (0:ℝ) ≤ 2 * Real.exp (-x / Kt) := fun x _ => by positivity
    have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-t / Kt)) Filter.atTop (nhds 0) := by
      have hphi : Filter.Tendsto (fun t : ℝ => (1 / Kt) * t) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hphi
      have heq : (fun t : ℝ => Real.exp (-t / Kt)) = (fun t : ℝ => Real.exp (-((1 / Kt) * t))) := by
        funext t; ring_nf
      rw [heq]; exact h
    have hlim : Filter.Tendsto (fun t : ℝ => -2 * Kt * Real.exp (-t / Kt)) Filter.atTop (nhds 0) := by
      have h := hexp.const_mul (-2 * Kt)
      simpa using h
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hmono hlim]
    ring
  constructor
  · have hImeas : Measurable (fun ω : Ω => if |xi ω| ≤ L then (0:ℝ) else 1) :=
      Measurable.ite (measurableSet_le hxi_meas.abs measurable_const) measurable_const measurable_const
    have hg_int : Integrable (fun ω : Ω => xi ω * (if |xi ω| ≤ L then (0:ℝ) else 1)) μ := by
      have h1 : Integrable (fun ω : Ω => xi ω - xi ω * (if |xi ω| ≤ L then (1:ℝ) else 0)) μ :=
        hxi_int.sub h_trunc_int
      refine h1.congr (Filter.Eventually.of_forall (fun ω => ?_))
      by_cases hc : (|xi ω| ≤ L) <;> simp [hc]
    have hfeq : (∫ ω, xi ω * (if |xi ω| ≤ L then (1:ℝ) else 0) ∂μ)
        = - ∫ ω, xi ω * (if |xi ω| ≤ L then (0:ℝ) else 1) ∂μ := by
      have hsum : (∫ ω, xi ω ∂μ) = (∫ ω, xi ω * (if |xi ω| ≤ L then (1:ℝ) else 0) ∂μ)
          + (∫ ω, xi ω * (if |xi ω| ≤ L then (0:ℝ) else 1) ∂μ) := by
        rw [← MeasureTheory.integral_add h_trunc_int hg_int]
        rw [show (fun a : Ω => xi a * (if |xi a| ≤ L then (1:ℝ) else 0)
            + xi a * (if |xi a| ≤ L then (0:ℝ) else 1)) = fun a => xi a from by
          funext ω
          by_cases hc : (|xi ω| ≤ L) <;> simp [hc]]
      rw [hxi_mean] at hsum
      linarith
    have hstep : |∫ ω, xi ω * (if |xi ω| ≤ L then (1:ℝ) else 0) ∂μ|
        ≤ ∫ ω, |xi ω| * (if |xi ω| ≤ L then (0:ℝ) else 1) ∂μ := by
      rw [hfeq]
      simp only [abs_neg]
      have habs := MeasureTheory.abs_integral_le_integral_abs
        (μ := μ) (f := fun ω => xi ω * (if |xi ω| ≤ L then (0:ℝ) else 1))
      have hcongr : (fun ω : Ω => |xi ω * (if |xi ω| ≤ L then (0:ℝ) else 1)|)
          = (fun ω : Ω => |xi ω| * (if |xi ω| ≤ L then (0:ℝ) else 1)) := by
        funext ω
        by_cases hc : (|xi ω| ≤ L) <;> simp [abs_mul, hc]
      rw [hcongr] at habs
      exact habs
    refine le_trans hstep ?_
    set G : Ω → ℝ := fun ω => |xi ω| * (if |xi ω| ≤ L then (0:ℝ) else 1) with hGdef
    have hG_nonneg : 0 ≤ᶠ[ae μ] G := by
      rw [hGdef]
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hc : (|xi ω| ≤ L) <;> simp [hc])
    have hG_aemeas : AEMeasurable G μ := by
      rw [hGdef]
      exact (hxi_meas.abs.mul hImeas).aemeasurable
    have hG_aesm : AEStronglyMeasurable G μ := AEMeasurable.aestronglyMeasurable hG_aemeas
    have hlc : (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ) = ∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < G a} :=
      MeasureTheory.lintegral_eq_lintegral_meas_lt μ hG_nonneg hG_aemeas
    have hpt : ∀ t ∈ Set.Ioi (0:ℝ), μ {a : Ω | t < G a}
        ≤ ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      by_cases hc : t ≤ L
      · have hsub : {a : Ω | t < G a} ⊆ {a : Ω | L < |xi a|} := by
          intro a ha
          simp only [Set.mem_setOf_eq, hGdef] at ha ⊢
          by_cases hca : (|xi a| ≤ L)
          · rw [if_pos hca] at ha
            simp at ha
            linarith
          · exact lt_of_not_ge hca
        calc μ {a : Ω | t < G a} ≤ μ {a : Ω | L < |xi a|} := measure_mono hsub
          _ ≤ ENNReal.ofReal (2 * Real.exp (-L / Kt)) := hxi_tail L hL
          _ = ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)) := by rw [max_eq_left hc]
      · have hLt : L < t := lt_of_not_ge hc
        have hsub : {a : Ω | t < G a} ⊆ {a : Ω | t < |xi a|} := by
          intro a ha
          simp only [Set.mem_setOf_eq, hGdef] at ha ⊢
          by_cases hca : (|xi a| ≤ L)
          · rw [if_pos hca] at ha
            simp at ha
            linarith
          · rwa [if_neg hca, mul_one] at ha
        calc μ {a : Ω | t < G a} ≤ μ {a : Ω | t < |xi a|} := measure_mono hsub
          _ ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)) := hxi_tail t ht
          _ = ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)) := by rw [max_eq_right hLt.le]
    have hbound : (∫⁻ t in Set.Ioi (0:ℝ), μ {a : Ω | t < G a})
        ≤ ENNReal.ofReal (2 * (L + Kt) * Real.exp (-L / Kt)) := by
      have hzero : ∀ {s : Set ℝ} {g : ℝ → ENNReal} {x : ℝ}, x ∉ s → s.indicator g x = 0 := by
        intro s g x hx
        simp [Set.indicator, hx]
      have key : ∀ (a C : ℝ) (f : ℝ → ℝ),
          AEStronglyMeasurable f (volume.restrict (Set.Ioi a)) →
          0 ≤ᶠ[ae (volume.restrict (Set.Ioi a))] f →
          (∫ x in Set.Ioi a, f x) = C → C ≠ 0 →
          ∫⁻ x in Set.Ioi a, ENNReal.ofReal (f x) = ENNReal.ofReal C := by
        intro a C f hsm hnn hval hC0
        have h := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (μ := volume.restrict (Set.Ioi a)) hnn hsm
        rw [hval] at h
        have hne : (∫⁻ x in Set.Ioi a, ENNReal.ofReal (f x)) ≠ ⊤ := by
          intro ht
          rw [ht] at h
          exact hC0 (by simpa using h)
        rw [h, ENNReal.ofReal_toReal hne]
      have hFcont : Continuous (fun t : ℝ => 2 * Real.exp (-(max L t) / Kt)) := by
        have hm : Continuous (fun t : ℝ => max L t) := continuous_const.max continuous_id
        exact continuous_const.mul (Real.continuous_exp.comp (hm.neg.div_const Kt))
      have hFmeas : Measurable (fun t : ℝ => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))) :=
        Measurable.ennreal_ofReal hFcont.measurable
      have hHmeas : Measurable ((Set.Ioc (0:ℝ) L).indicator
          (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))) :=
        hFmeas.indicator measurableSet_Ioc
      have hmono : (∫⁻ t in Set.Ioi (0:ℝ), μ {a : Ω | t < G a})
          ≤ ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)) := by
        have h1 : (∫⁻ t in Set.Ioi (0:ℝ), μ {a : Ω | t < G a})
            = ∫⁻ t, (Set.Ioi (0:ℝ)).indicator (fun t => μ {a : Ω | t < G a}) t :=
          (MeasureTheory.lintegral_indicator measurableSet_Ioi
            (f := fun t => μ {a : Ω | t < G a})).symm
        have h2 : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))
            = ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
                (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))) t :=
          (MeasureTheory.lintegral_indicator measurableSet_Ioi
            (f := fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))).symm
        rw [h1, h2]
        exact MeasureTheory.lintegral_mono (fun t => by
          by_cases ht : t ∈ Set.Ioi (0:ℝ)
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
            exact hpt t ht
          · change (if t ∈ Set.Ioi (0:ℝ) then μ {a : Ω | t < G a} else 0)
              ≤ (if t ∈ Set.Ioi (0:ℝ) then ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)) else 0)
            rw [if_neg ht, if_neg ht])
      have hsplit : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))
          = (∫⁻ t in Set.Ioc (0:ℝ) L, ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))
            + (∫⁻ t in Set.Ioi L, ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))) := by
        rw [show (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))
            = ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
                (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))) t from
          (MeasureTheory.lintegral_indicator measurableSet_Ioi
            (f := fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))).symm]
        rw [show (fun t => (Set.Ioi (0:ℝ)).indicator
              (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))) t)
            = fun t => ((Set.Ioc (0:ℝ) L).indicator
                (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))
              + (Set.Ioi L).indicator
                (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))) t from by
          funext t
          simp only [Pi.add_apply]
          by_cases ht : t ∈ Set.Ioi (0:ℝ)
          · by_cases hL' : t ≤ L
            · rw [Set.indicator_of_mem ht,
                Set.indicator_of_mem (show t ∈ Set.Ioc (0:ℝ) L from ⟨ht, hL'⟩),
                hzero (show t ∉ Set.Ioi L from not_lt.mpr hL'), add_zero]
            · have hLt' : L < t := lt_of_not_ge hL'
              rw [Set.indicator_of_mem ht,
                hzero (show t ∉ Set.Ioc (0:ℝ) L from fun hc => absurd hc.2 (not_le.mpr hLt')),
                Set.indicator_of_mem (show t ∈ Set.Ioi L from hLt'), zero_add]
          · rw [hzero ht, hzero (show t ∉ Set.Ioc (0:ℝ) L from fun hc => ht hc.1),
              hzero (show t ∉ Set.Ioi L from fun hc => ht (lt_trans hL hc)), add_zero]]
        simp only [Pi.add_apply]
        rw [show (∫⁻ t, (Set.Ioc (0:ℝ) L).indicator
                (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))) t
              + (Set.Ioi L).indicator (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))) t)
            = (∫⁻ t, (Set.Ioc (0:ℝ) L).indicator
                (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))) t)
              + (∫⁻ t, (Set.Ioi L).indicator
                (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))) t) from
          MeasureTheory.lintegral_add_left hHmeas
            ((Set.Ioi L).indicator (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))))]
        rw [MeasureTheory.lintegral_indicator measurableSet_Ioc
              (f := fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt))),
            MeasureTheory.lintegral_indicator measurableSet_Ioi
              (f := fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))]
      have hp1 : (∫⁻ t in Set.Ioc (0:ℝ) L, ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))
          = ENNReal.ofReal (2 * Real.exp (-L / Kt) * L) := by
        rw [← MeasureTheory.lintegral_indicator measurableSet_Ioc
          (f := fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))]
        rw [show (Set.Ioc (0:ℝ) L).indicator (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))
            = (Set.Ioc (0:ℝ) L).indicator (fun _ => ENNReal.ofReal (2 * Real.exp (-L / Kt))) from by
          funext t
          by_cases ht : t ∈ Set.Ioc (0:ℝ) L
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, max_eq_left ht.2]
          · rw [hzero ht, hzero ht]]
        rw [MeasureTheory.lintegral_indicator measurableSet_Ioc
          (f := fun _ => ENNReal.ofReal (2 * Real.exp (-L / Kt)))]
        show (∫⁻ _ : ℝ, ENNReal.ofReal (2 * Real.exp (-L / Kt)) ∂(volume.restrict (Set.Ioc (0:ℝ) L)))
            = ENNReal.ofReal (2 * Real.exp (-L / Kt) * L)
        rw [MeasureTheory.lintegral_const]
        have hvol : (volume.restrict (Set.Ioc (0:ℝ) L)) Set.univ = ENNReal.ofReal L := by
          rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc,
            sub_zero]
        rw [hvol, ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 * Real.exp (-L / Kt) by positivity)]
      have hp2 : (∫⁻ t in Set.Ioi L, ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))
          = ENNReal.ofReal (2 * Kt * Real.exp (-L / Kt)) := by
        rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi
          (f := fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))]
        rw [show (Set.Ioi L).indicator (fun t => ENNReal.ofReal (2 * Real.exp (-(max L t) / Kt)))
            = (Set.Ioi L).indicator (fun t => ENNReal.ofReal (2 * Real.exp (-t / Kt))) from by
          funext t
          by_cases ht : t ∈ Set.Ioi L
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, max_eq_right (le_of_lt ht)]
          · rw [hzero ht, hzero ht]]
        rw [MeasureTheory.lintegral_indicator measurableSet_Ioi
          (f := fun t => ENNReal.ofReal (2 * Real.exp (-t / Kt)))]
        have hcont2 : Continuous (fun t : ℝ => 2 * Real.exp (-t / Kt)) := by
          have hlin : Continuous (fun t : ℝ => -t / Kt) := continuous_id.neg.div_const Kt
          exact continuous_const.mul (Real.continuous_exp.comp hlin)
        have hsm2 : AEStronglyMeasurable (fun t : ℝ => 2 * Real.exp (-t / Kt))
            (volume.restrict (Set.Ioi L)) :=
          Measurable.aestronglyMeasurable hcont2.measurable
        have hnn2 : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi L))] (fun t : ℝ => 2 * Real.exp (-t / Kt)) :=
          Filter.Eventually.of_forall (fun t => by positivity)
        have hCne : (2 * Kt * Real.exp (-L / Kt)) ≠ 0 := ne_of_gt (by positivity)
        exact key L (2 * Kt * Real.exp (-L / Kt)) (fun t : ℝ => 2 * Real.exp (-t / Kt))
          hsm2 hnn2 intA hCne
      have harith : ENNReal.ofReal (2 * Real.exp (-L / Kt) * L)
            + ENNReal.ofReal (2 * Kt * Real.exp (-L / Kt))
          = ENNReal.ofReal (2 * (L + Kt) * Real.exp (-L / Kt)) := by
        rw [← ENNReal.ofReal_add (show (0:ℝ) ≤ 2 * Real.exp (-L / Kt) * L by positivity)
          (show (0:ℝ) ≤ 2 * Kt * Real.exp (-L / Kt) by positivity)]
        congr 1
        ring
      refine hmono.trans_eq ?_
      rw [hsplit, hp1, hp2]
      exact harith
    have hGint : ∫ ω, G ω ∂μ = (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae hG_nonneg hG_aesm
    calc ∫ ω, G ω ∂μ = (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ).toReal := hGint
      _ = (∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < G a}).toReal := by rw [hlc]
      _ ≤ (ENNReal.ofReal (2 * (L + Kt) * Real.exp (-L / Kt))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      _ = 2 * (L + Kt) * Real.exp (-L / Kt) := ENNReal.toReal_ofReal (by positivity)
  · have hL2pos : (0:ℝ) < L^2 := by positivity
    have intB : ∫ t in Set.Ioi (L^2), 2 * Real.exp (-Real.sqrt t / Kt) = 4 * Kt * (L + Kt) * Real.exp (-L / Kt) := by
      have hderiv : ∀ x ∈ Set.Ici (L^2),
          HasDerivAt (fun t : ℝ => -4 * Kt * ((Real.sqrt t + Kt) * Real.exp (-Real.sqrt t / Kt)))
            (2 * Real.exp (-Real.sqrt x / Kt)) x := by
        intro x hx
        have hxpos : 0 < x := lt_of_lt_of_le hL2pos hx
        have hx0 : x ≠ 0 := ne_of_gt hxpos
        have hs0 : Real.sqrt x ≠ 0 := by
          intro h
          have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hxpos)
          rw [h] at hsq
          simp at hsq
          linarith
        have hs : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt x)) x :=
          Real.hasDerivAt_sqrt hx0
        have hu : HasDerivAt (fun t : ℝ => Real.sqrt t + Kt) (1 / (2 * Real.sqrt x)) x := by
          have h := hs.add (hasDerivAt_const x Kt)
          simpa only [add_zero] using h
        have hv' : HasDerivAt (fun t : ℝ => -Real.sqrt t / Kt) (-(1 / (2 * Real.sqrt x)) / Kt) x := by
          simpa using (hs.neg).div_const Kt
        have hw : HasDerivAt (fun t : ℝ => Real.exp (-Real.sqrt t / Kt))
            (Real.exp (-Real.sqrt x / Kt) * (-(1 / (2 * Real.sqrt x)) / Kt)) x := by
          have hc := HasDerivAt.comp x (Real.hasDerivAt_exp (-Real.sqrt x / Kt)) hv'
          simpa using hc
        have hprod : HasDerivAt (fun t : ℝ => (Real.sqrt t + Kt) * Real.exp (-Real.sqrt t / Kt))
            ((1 / (2 * Real.sqrt x)) * Real.exp (-Real.sqrt x / Kt)
              + (Real.sqrt x + Kt) * (Real.exp (-Real.sqrt x / Kt) * (-(1 / (2 * Real.sqrt x)) / Kt))) x := by
          simpa using hu.mul hw
        have hsc : HasDerivAt (fun t : ℝ => -4 * Kt * ((Real.sqrt t + Kt) * Real.exp (-Real.sqrt t / Kt)))
            (-4 * Kt * ((1 / (2 * Real.sqrt x)) * Real.exp (-Real.sqrt x / Kt)
              + (Real.sqrt x + Kt) * (Real.exp (-Real.sqrt x / Kt) * (-(1 / (2 * Real.sqrt x)) / Kt)))) x := by
          simpa using hprod.const_mul (-4 * Kt)
        have hcoef : -4 * Kt * ((1 / (2 * Real.sqrt x)) + (Real.sqrt x + Kt) * (-(1 / (2 * Real.sqrt x)) / Kt)) = 2 := by
          have hs2 : (2 * Real.sqrt x) ≠ 0 := mul_ne_zero two_ne_zero hs0
          field_simp
          ring
        have hv : -4 * Kt * ((1 / (2 * Real.sqrt x)) * Real.exp (-Real.sqrt x / Kt)
              + (Real.sqrt x + Kt) * (Real.exp (-Real.sqrt x / Kt) * (-(1 / (2 * Real.sqrt x)) / Kt)))
            = 2 * Real.exp (-Real.sqrt x / Kt) := by
          calc -4 * Kt * ((1 / (2 * Real.sqrt x)) * Real.exp (-Real.sqrt x / Kt)
              + (Real.sqrt x + Kt) * (Real.exp (-Real.sqrt x / Kt) * (-(1 / (2 * Real.sqrt x)) / Kt)))
              = (-4 * Kt * ((1 / (2 * Real.sqrt x)) + (Real.sqrt x + Kt) * (-(1 / (2 * Real.sqrt x)) / Kt)))
                * Real.exp (-Real.sqrt x / Kt) := by ring
            _ = 2 * Real.exp (-Real.sqrt x / Kt) := by rw [hcoef]
        rw [hv] at hsc
        exact hsc
      have hmonoB : ∀ x ∈ Set.Ioi (L^2), (0:ℝ) ≤ 2 * Real.exp (-Real.sqrt x / Kt) :=
        fun x _ => by positivity
      have hlimB : Filter.Tendsto (fun t : ℝ => -4 * Kt * ((Real.sqrt t + Kt) * Real.exp (-Real.sqrt t / Kt)))
          Filter.atTop (nhds 0) := by
        have hexpB : Filter.Tendsto (fun u : ℝ => Real.exp (-u / Kt)) Filter.atTop (nhds 0) := by
          have hphi : Filter.Tendsto (fun u : ℝ => (1 / Kt) * u) Filter.atTop Filter.atTop :=
            Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
          have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hphi
          have heq : (fun u : ℝ => Real.exp (-u / Kt)) = (fun u : ℝ => Real.exp (-((1 / Kt) * u))) := by
            funext u; ring_nf
          rw [heq]; exact h
        have hu1 : Filter.Tendsto (fun u : ℝ => u * Real.exp (-u / Kt)) Filter.atTop (nhds 0) := by
          have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1/Kt) (by positivity)
          have heq : (fun u : ℝ => u * Real.exp (-u / Kt))
              = (fun x : ℝ => x ^ (1:ℝ) * Real.exp (-(1/Kt) * x)) := by
            funext u
            rw [Real.rpow_one]
            ring_nf
          rw [heq]; exact h
        have hsum : Filter.Tendsto (fun u : ℝ => (u + Kt) * Real.exp (-u / Kt)) Filter.atTop (nhds 0) := by
          have heq : (fun u : ℝ => (u + Kt) * Real.exp (-u / Kt))
              = (fun u : ℝ => u * Real.exp (-u / Kt) + Kt * Real.exp (-u / Kt)) := by
            funext u; ring
          rw [heq]
          have h := hu1.add (hexpB.const_mul Kt)
          simpa using h
        have hphi2 : Filter.Tendsto (fun u : ℝ => -4 * Kt * ((u + Kt) * Real.exp (-u / Kt))) Filter.atTop (nhds 0) := by
          have h := hsum.const_mul (-4 * Kt)
          simpa using h
        have hsqrt_top : Filter.Tendsto (fun t : ℝ => Real.sqrt t) Filter.atTop Filter.atTop :=
          Real.map_sqrt_atTop.le
        have hcomp := hphi2.comp hsqrt_top
        simpa using hcomp
      rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hmonoB hlimB]
      rw [Real.sqrt_sq hL.le]
      ring
    have hsq_meas : Measurable (fun ω : Ω => (xi ω)^2) := by
      have h := hxi_meas.mul hxi_meas
      simpa only [sq] using h
    have hImeas : Measurable (fun ω : Ω => if |xi ω| ≤ L then (0:ℝ) else 1) :=
      Measurable.ite (measurableSet_le hxi_meas.abs measurable_const) measurable_const measurable_const
    set G2 : Ω → ℝ := fun ω => (xi ω)^2 * (if |xi ω| ≤ L then (0:ℝ) else 1) with hG2def
    have hG2_nonneg : 0 ≤ᶠ[ae μ] G2 := by
      rw [hG2def]
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hc : (|xi ω| ≤ L)
        · simp [hc]
        · simp [hc]
          positivity)
    have hG2_aemeas : AEMeasurable G2 μ := by
      rw [hG2def]
      exact (hsq_meas.mul hImeas).aemeasurable
    have hG2_aesm : AEStronglyMeasurable G2 μ := AEMeasurable.aestronglyMeasurable hG2_aemeas
    have hlc2 : (∫⁻ ω, ENNReal.ofReal (G2 ω) ∂μ) = ∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < G2 a} :=
      MeasureTheory.lintegral_eq_lintegral_meas_lt μ hG2_nonneg hG2_aemeas
    have hpt2 : ∀ t ∈ Set.Ioi (0:ℝ), μ {a : Ω | t < G2 a}
        ≤ ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      by_cases hc : t ≤ L^2
      · have hsub : {a : Ω | t < G2 a} ⊆ {a : Ω | L < |xi a|} := by
          intro a ha
          simp only [Set.mem_setOf_eq, hG2def] at ha ⊢
          by_cases hca : (|xi a| ≤ L)
          · rw [if_pos hca, mul_zero] at ha
            linarith
          · exact lt_of_not_ge hca
        calc μ {a : Ω | t < G2 a} ≤ μ {a : Ω | L < |xi a|} := measure_mono hsub
          _ ≤ ENNReal.ofReal (2 * Real.exp (-L / Kt)) := hxi_tail L hL
          _ = ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)) := by
              rw [if_pos hc]
      · have hsub : {a : Ω | t < G2 a} ⊆ {a : Ω | Real.sqrt t < |xi a|} := by
          intro a ha
          simp only [Set.mem_setOf_eq, hG2def] at ha ⊢
          by_cases hca : (|xi a| ≤ L)
          · rw [if_pos hca, mul_zero] at ha
            linarith
          · rw [if_neg hca, mul_one] at ha
            have h1 : Real.sqrt t < Real.sqrt ((xi a)^2) := Real.sqrt_lt_sqrt (le_of_lt ht0) ha
            rwa [Real.sqrt_sq_eq_abs] at h1
        have hsqrtpos : (0:ℝ) < Real.sqrt t := by
          rcases lt_or_eq_of_le (Real.sqrt_nonneg t) with h | h
          · exact h
          · exfalso
            have hz : Real.sqrt t = 0 := h.symm
            have ht_eq : t = 0 := by
              rw [← Real.sq_sqrt (le_of_lt ht0), hz]
              ring
            linarith
        calc μ {a : Ω | t < G2 a} ≤ μ {a : Ω | Real.sqrt t < |xi a|} := measure_mono hsub
          _ ≤ ENNReal.ofReal (2 * Real.exp (-Real.sqrt t / Kt)) := hxi_tail (Real.sqrt t) hsqrtpos
          _ = ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)) := by
              rw [if_neg hc]
    have hbound2 : (∫⁻ t in Set.Ioi (0:ℝ), μ {a : Ω | t < G2 a})
        ≤ ENNReal.ofReal ((2 * L^2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt)) := by
      have hzero : ∀ {s : Set ℝ} {g : ℝ → ENNReal} {x : ℝ}, x ∉ s → s.indicator g x = 0 := by
        intro s g x hx
        simp [Set.indicator, hx]
      have key : ∀ (a C : ℝ) (f : ℝ → ℝ),
          AEStronglyMeasurable f (volume.restrict (Set.Ioi a)) →
          0 ≤ᶠ[ae (volume.restrict (Set.Ioi a))] f →
          (∫ x in Set.Ioi a, f x) = C → C ≠ 0 →
          ∫⁻ x in Set.Ioi a, ENNReal.ofReal (f x) = ENNReal.ofReal C := by
        intro a C f hsm hnn hval hC0
        have h := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (μ := volume.restrict (Set.Ioi a)) hnn hsm
        rw [hval] at h
        have hne : (∫⁻ x in Set.Ioi a, ENNReal.ofReal (f x)) ≠ ⊤ := by
          intro ht
          rw [ht] at h
          exact hC0 (by simpa using h)
        rw [h, ENNReal.ofReal_toReal hne]
      have hcontB : Continuous (fun t : ℝ => 2 * Real.exp (-Real.sqrt t / Kt)) := by
        have hlin : Continuous (fun t : ℝ => -Real.sqrt t / Kt) := (Real.continuous_sqrt.neg).div_const Kt
        exact continuous_const.mul (Real.continuous_exp.comp hlin)
      have hFBmeas : Measurable (fun t : ℝ => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))) := by
        apply Measurable.ennreal_ofReal
        exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const hcontB.measurable
      have hHmeasB : Measurable ((Set.Ioc (0:ℝ) (L^2)).indicator
          (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))) :=
        hFBmeas.indicator measurableSet_Ioc
      have hmono2 : (∫⁻ t in Set.Ioi (0:ℝ), μ {a : Ω | t < G2 a})
          ≤ ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)) := by
        have h1 : (∫⁻ t in Set.Ioi (0:ℝ), μ {a : Ω | t < G2 a})
            = ∫⁻ t, (Set.Ioi (0:ℝ)).indicator (fun t => μ {a : Ω | t < G2 a}) t :=
          (MeasureTheory.lintegral_indicator measurableSet_Ioi
            (f := fun t => μ {a : Ω | t < G2 a})).symm
        have h2 : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))
            = ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
                (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))) t :=
          (MeasureTheory.lintegral_indicator measurableSet_Ioi
            (f := fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))).symm
        rw [h1, h2]
        exact MeasureTheory.lintegral_mono (fun t => by
          by_cases ht : t ∈ Set.Ioi (0:ℝ)
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
            exact hpt2 t ht
          · rw [hzero ht, hzero ht])
      have hsplit2 : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))
          = (∫⁻ t in Set.Ioc (0:ℝ) (L^2), ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))
            + (∫⁻ t in Set.Ioi (L^2), ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))) := by
        rw [show (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))
            = ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
                (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))) t from
          (MeasureTheory.lintegral_indicator measurableSet_Ioi
            (f := fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))).symm]
        rw [show (fun t => (Set.Ioi (0:ℝ)).indicator
              (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))) t)
            = fun t => ((Set.Ioc (0:ℝ) (L^2)).indicator
                (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))
              + (Set.Ioi (L^2)).indicator
                (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))) t from by
          funext t
          simp only [Pi.add_apply]
          by_cases ht : t ∈ Set.Ioi (0:ℝ)
          · by_cases hL' : t ≤ L^2
            · rw [Set.indicator_of_mem ht,
                Set.indicator_of_mem (show t ∈ Set.Ioc (0:ℝ) (L^2) from ⟨ht, hL'⟩),
                hzero (show t ∉ Set.Ioi (L^2) from not_lt.mpr hL'), add_zero]
            · have hLt' : L^2 < t := lt_of_not_ge hL'
              rw [Set.indicator_of_mem ht,
                hzero (show t ∉ Set.Ioc (0:ℝ) (L^2) from fun hc => absurd hc.2 (not_le.mpr hLt')),
                Set.indicator_of_mem (show t ∈ Set.Ioi (L^2) from hLt'), zero_add]
          · rw [hzero ht, hzero (show t ∉ Set.Ioc (0:ℝ) (L^2) from fun hc => ht hc.1),
              hzero (show t ∉ Set.Ioi (L^2) from fun hc => ht (lt_trans hL2pos hc)), add_zero]]
        simp only [Pi.add_apply]
        rw [show (∫⁻ t, (Set.Ioc (0:ℝ) (L^2)).indicator
                (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))) t
              + (Set.Ioi (L^2)).indicator
                (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))) t)
            = (∫⁻ t, (Set.Ioc (0:ℝ) (L^2)).indicator
                (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))) t)
              + (∫⁻ t, (Set.Ioi (L^2)).indicator
                (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))) t) from
          MeasureTheory.lintegral_add_left hHmeasB
            ((Set.Ioi (L^2)).indicator
              (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))))]
        rw [MeasureTheory.lintegral_indicator measurableSet_Ioc
              (f := fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt))),
            MeasureTheory.lintegral_indicator measurableSet_Ioi
              (f := fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))]
      have hp1B : (∫⁻ t in Set.Ioc (0:ℝ) (L^2), ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))
          = ENNReal.ofReal (2 * Real.exp (-L / Kt) * L^2) := by
        rw [← MeasureTheory.lintegral_indicator measurableSet_Ioc
          (f := fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))]
        rw [show (Set.Ioc (0:ℝ) (L^2)).indicator
              (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))
            = (Set.Ioc (0:ℝ) (L^2)).indicator (fun _ => ENNReal.ofReal (2 * Real.exp (-L / Kt))) from by
          funext t
          by_cases ht : t ∈ Set.Ioc (0:ℝ) (L^2)
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, if_pos ht.2]
          · rw [hzero ht, hzero ht]]
        rw [MeasureTheory.lintegral_indicator measurableSet_Ioc
          (f := fun _ => ENNReal.ofReal (2 * Real.exp (-L / Kt)))]
        show (∫⁻ _ : ℝ, ENNReal.ofReal (2 * Real.exp (-L / Kt)) ∂(volume.restrict (Set.Ioc (0:ℝ) (L^2))))
            = ENNReal.ofReal (2 * Real.exp (-L / Kt) * L^2)
        rw [MeasureTheory.lintegral_const]
        have hvol : (volume.restrict (Set.Ioc (0:ℝ) (L^2))) Set.univ = ENNReal.ofReal (L^2) := by
          rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc,
            sub_zero]
        rw [hvol, ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 * Real.exp (-L / Kt) by positivity)]
      have hp2B : (∫⁻ t in Set.Ioi (L^2), ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))
          = ENNReal.ofReal (4 * Kt * (L + Kt) * Real.exp (-L / Kt)) := by
        rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi
          (f := fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))]
        rw [show (Set.Ioi (L^2)).indicator
              (fun t => ENNReal.ofReal (if t ≤ L^2 then 2 * Real.exp (-L / Kt) else 2 * Real.exp (-Real.sqrt t / Kt)))
            = (Set.Ioi (L^2)).indicator (fun t => ENNReal.ofReal (2 * Real.exp (-Real.sqrt t / Kt))) from by
          funext t
          by_cases ht : t ∈ Set.Ioi (L^2)
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, if_neg (not_le.mpr ht)]
          · rw [hzero ht, hzero ht]]
        rw [MeasureTheory.lintegral_indicator measurableSet_Ioi
          (f := fun t => ENNReal.ofReal (2 * Real.exp (-Real.sqrt t / Kt)))]
        have hsm2 : AEStronglyMeasurable (fun t : ℝ => 2 * Real.exp (-Real.sqrt t / Kt))
            (volume.restrict (Set.Ioi (L^2))) :=
          Measurable.aestronglyMeasurable hcontB.measurable
        have hnn2 : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (L^2)))] (fun t : ℝ => 2 * Real.exp (-Real.sqrt t / Kt)) :=
          Filter.Eventually.of_forall (fun t => by positivity)
        have hCne : (4 * Kt * (L + Kt) * Real.exp (-L / Kt)) ≠ 0 := ne_of_gt (by positivity)
        exact key (L^2) (4 * Kt * (L + Kt) * Real.exp (-L / Kt))
          (fun t : ℝ => 2 * Real.exp (-Real.sqrt t / Kt)) hsm2 hnn2 intB hCne
      have harith2 : ENNReal.ofReal (2 * Real.exp (-L / Kt) * L^2)
            + ENNReal.ofReal (4 * Kt * (L + Kt) * Real.exp (-L / Kt))
          = ENNReal.ofReal ((2 * L^2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt)) := by
        rw [← ENNReal.ofReal_add (show (0:ℝ) ≤ 2 * Real.exp (-L / Kt) * L^2 by positivity)
          (show (0:ℝ) ≤ 4 * Kt * (L + Kt) * Real.exp (-L / Kt) by positivity)]
        congr 1
        ring
      refine hmono2.trans_eq ?_
      rw [hsplit2, hp1B, hp2B]
      exact harith2
    have hG2int : ∫ ω, G2 ω ∂μ = (∫⁻ ω, ENNReal.ofReal (G2 ω) ∂μ).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae hG2_nonneg hG2_aesm
    calc ∫ ω, G2 ω ∂μ = (∫⁻ ω, ENNReal.ofReal (G2 ω) ∂μ).toReal := hG2int
      _ = (∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < G2 a}).toReal := by rw [hlc2]
      _ ≤ (ENNReal.ofReal ((2 * L^2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound2
      _ = (2 * L^2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) := ENNReal.toReal_ofReal (by positivity)
  /- @proof-region region.target-node.session.b1d1ab7351e29a87 end -/

end Statlib.Imported

