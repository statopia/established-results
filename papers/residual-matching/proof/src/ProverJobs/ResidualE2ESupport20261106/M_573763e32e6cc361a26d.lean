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
theorem statopia_math_node_606857656_cfd8aebb : ∀ (μ ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    [MeasureTheory.IsFiniteMeasure ν]
    (hmass : μ Set.univ = ν Set.univ)
    (d : ℝ)
    (hF : ∀ x : ℝ, |(μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal| ≤ d)
    (z : ℂ) (hz : 0 < z.im),
    ‖(∫ x, ((x : ℂ) - z)⁻¹ ∂μ) - (∫ x, ((x : ℂ) - z)⁻¹ ∂ν)‖
      ≤ d * (Real.pi / z.im) := by
  /- @proof-region region.target-node.session.363a550d11323621 begin -/
  intro μ ν _ _ hmass d hF z hz
  have hd : 0 ≤ d := le_trans (abs_nonneg _) (hF 0)
  set a : ℝ := z.re with ha
  set b : ℝ := z.im with hb
  have hbpos : 0 < b := hb.symm ▸ hz
  have hzne : ∀ t : ℝ, ((t : ℂ) - z) ≠ 0 := by
    intro t h
    have h2 := congrArg Complex.im h
    simp at h2
    linarith [hz]
  have hGnorm : ∀ t : ℝ, ‖(((t : ℂ) - z)^2)⁻¹‖ = ((t - a)^2 + b^2)⁻¹ := by
    intro t
    have hsq : ‖(t : ℂ) - z‖^2 = (t - a)^2 + b^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
        zero_sub]
      rw [← ha, ← hb]
      ring
    rw [norm_inv, norm_pow, hsq]
  have hQpos : ∀ t : ℝ, 0 < (t - a)^2 + b^2 := by
    intro t
    nlinarith [sq_nonneg (t - a)]
  have hIint : MeasureTheory.Integrable (fun t : ℝ => ((t - a)^2 + b^2)⁻¹) := by
    have hcont : Continuous fun t : ℝ => ((t - a)^2 + b^2)⁻¹ := by
      apply Continuous.inv₀ (f := fun t : ℝ => (t - a)^2 + b^2)
      · fun_prop
      · intro t
        exact (hQpos t).ne'
    have hk : MeasureTheory.Integrable (fun t : ℝ => (1 + t^2)⁻¹) := by
      by_contra hcon
      have h0 : (∫ t : ℝ, (1 + t^2)⁻¹) = 0 := MeasureTheory.integral_undef hcon
      rw [integral_univ_inv_one_add_sq] at h0
      exact Real.pi_pos.ne' h0
    have key : ∀ t : ℝ,
        ((t - a)^2 + b^2)⁻¹ ≤ ((1 + 2*a^2 + 2*b^2) / b^2) * (1 + t^2)⁻¹ := by
      intro t
      have hK : (0:ℝ) < 1 + 2*a^2 + 2*b^2 := by positivity
      have hKne : (1 + 2*a^2 + 2*b^2) ≠ 0 := hK.ne'
      have hQne : ((t - a)^2 + b^2) ≠ 0 := (hQpos t).ne'
      have hA : (0:ℝ) < 1 + t^2 := by positivity
      have h1 : 1 + t^2 ≤ (1 + 2*a^2) + 2*(t-a)^2 := by
        nlinarith [sq_nonneg (t - 2*a)]
      have h2 : b^2 * ((1 + 2*a^2) + 2*(t-a)^2) ≤ (1 + 2*a^2 + 2*b^2) * ((t - a)^2 + b^2) := by
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 1 + 2*a^2) (sq_nonneg (t - a)),
          sq_nonneg b, sq_nonneg (b^2)]
      have hq : b^2 * (1 + t^2) ≤ (1 + 2*a^2 + 2*b^2) * ((t - a)^2 + b^2) := by
        nlinarith [h1, h2, sq_nonneg b]
      have h3 : (1:ℝ) / ((1 + 2*a^2 + 2*b^2) * ((t - a)^2 + b^2)) ≤ 1 / (b^2 * (1 + t^2)) :=
        one_div_le_one_div_of_le (by positivity) hq
      have h4 := mul_le_mul_of_nonneg_left h3 (le_of_lt hK)
      have e1 : (1 + 2*a^2 + 2*b^2) *
          (1 / ((1 + 2*a^2 + 2*b^2) * ((t - a)^2 + b^2))) = ((t - a)^2 + b^2)⁻¹ := by
        field_simp
      have e2 : (1 + 2*a^2 + 2*b^2) * (1 / (b^2 * (1 + t^2))) =
          ((1 + 2*a^2 + 2*b^2) / b^2) * (1 + t^2)⁻¹ := by
        field_simp
      rw [e1, e2] at h4
      exact h4
    refine MeasureTheory.Integrable.mono'
      (hk.const_mul ((1 + 2*a^2 + 2*b^2) / b^2)) hcont.measurable.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hQpos t))]
    exact key t
  have hIval : (∫ t : ℝ, ((t - a)^2 + b^2)⁻¹) = Real.pi / b := by
    have hbne : b ≠ 0 := hbpos.ne'
    have hIntEq : ∀ n : ℕ, (∫ t in (a - (n:ℝ))..(a + (n:ℝ)), ((t - a)^2 + b^2)⁻¹)
        = b⁻¹ * (Real.arctan ((n:ℝ) / b) - Real.arctan ((-(n:ℝ)) / b)) := by
      intro n
      have hcomp := intervalIntegral.integral_comp_add_right
        (a := a - (n:ℝ)) (b := a + (n:ℝ)) (f := fun x : ℝ => (x^2 + b^2)⁻¹) (-a)
      rw [show (a - (n:ℝ)) + (-a) = -(n:ℝ) by ring,
          show (a + (n:ℝ)) + (-a) = (n:ℝ) by ring] at hcomp
      rw [show (fun t : ℝ => ((t - a)^2 + b^2)⁻¹) = fun t : ℝ => ((t + -a)^2 + b^2)⁻¹ from
        funext (fun t => by rw [sub_eq_add_neg])]
      rw [hcomp]
      rw [show (fun x : ℝ => (x^2 + b^2)⁻¹) = fun x : ℝ => (b^2 + x^2)⁻¹ from
        funext (fun x => by rw [add_comm (x^2) (b^2)])]
      exact integral_inv_sq_add_sq hbne
    have hconv : Filter.Tendsto
        (fun n : ℕ => ∫ t in (a - (n:ℝ))..(a + (n:ℝ)), ((t - a)^2 + b^2)⁻¹)
        Filter.atTop (nhds (∫ t : ℝ, ((t - a)^2 + b^2)⁻¹)) := by
      have hDCT0 : Filter.Tendsto
          (fun n : ℕ => ∫ t, (Set.Ioc (a - (n:ℝ)) (a + (n:ℝ))).indicator
            (fun t : ℝ => ((t - a)^2 + b^2)⁻¹) t)
          Filter.atTop (nhds (∫ t : ℝ, ((t - a)^2 + b^2)⁻¹)) := by
        refine MeasureTheory.tendsto_integral_of_dominated_convergence
          (fun t : ℝ => ((t - a)^2 + b^2)⁻¹) ?_ hIint ?_ ?_
        · intro n
          exact hIint.aestronglyMeasurable.indicator measurableSet_Ioc
        · intro n
          filter_upwards with t
          rw [Set.indicator_apply]
          by_cases h : t ∈ Set.Ioc (a - (n:ℝ)) (a + (n:ℝ))
          · rw [if_pos h, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hQpos t))]
          · rw [if_neg h, norm_zero]
            positivity
        · filter_upwards with t
          have hev1 : ∀ᶠ n : ℕ in Filter.atTop, a - t < (n:ℝ) :=
            tendsto_natCast_atTop_atTop.eventually (Filter.eventually_gt_atTop (a - t))
          have hev2 : ∀ᶠ n : ℕ in Filter.atTop, t - a ≤ (n:ℝ) :=
            tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop (t - a))
          have hEq : (fun n : ℕ => (Set.Ioc (a - (n:ℝ)) (a + (n:ℝ))).indicator
              (fun t : ℝ => ((t - a)^2 + b^2)⁻¹) t) =ᶠ[Filter.atTop]
              (fun _ => ((t - a)^2 + b^2)⁻¹) := by
            filter_upwards [hev1, hev2] with n h1 h2
            rw [sub_lt_iff_lt_add, add_comm (↑n : ℝ) t] at h1
            rw [sub_le_iff_le_add, add_comm (↑n : ℝ) a] at h2
            have hlt : a - (n:ℝ) < t := by
              rw [sub_lt_iff_lt_add]
              exact h1
            exact Set.indicator_of_mem (f := fun t : ℝ => ((t - a)^2 + b^2)⁻¹)
              (Set.mem_Ioc.mpr ⟨hlt, h2⟩)
          exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
      refine Filter.Tendsto.congr' ?_ hDCT0
      filter_upwards with n
      rw [MeasureTheory.integral_indicator measurableSet_Ioc]
      exact (intervalIntegral.integral_of_le (by
        have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith)).symm
    have hlim : Filter.Tendsto
        (fun n : ℕ => b⁻¹ * (Real.arctan ((n:ℝ) / b) - Real.arctan ((-(n:ℝ)) / b)))
        Filter.atTop (nhds (Real.pi / b)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (n:ℝ) / b) Filter.atTop Filter.atTop := by
        have hstep : Filter.Tendsto (fun n : ℕ => b⁻¹ * (n:ℝ)) Filter.atTop Filter.atTop :=
          tendsto_natCast_atTop_atTop.const_mul_atTop (inv_pos.mpr hbpos)
        simpa [div_eq_mul_inv, mul_comm] using hstep
      have h2 : Filter.Tendsto (fun n : ℕ => Real.arctan ((n:ℝ) / b)) Filter.atTop
          (nhds (Real.pi / 2)) :=
        (Real.tendsto_arctan_atTop.comp h1).mono_right nhdsWithin_le_nhds
      have hfun : (fun n : ℕ => b⁻¹ * (Real.arctan ((n:ℝ) / b) - Real.arctan ((-(n:ℝ)) / b)))
          = fun n : ℕ => b⁻¹ * (2 * Real.arctan ((n:ℝ) / b)) := by
        funext n
        rw [show (-(n:ℝ)) / b = -((n:ℝ) / b) by ring, Real.arctan_neg]
        ring
      rw [hfun]
      have h3 := (h2.const_mul 2).const_mul b⁻¹
      have hval : b⁻¹ * (2 * (Real.pi / 2)) = Real.pi / b := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [hval] at h3
      exact h3
    have hlim' : Filter.Tendsto
        (fun n : ℕ => ∫ t in (a - (n:ℝ))..(a + (n:ℝ)), ((t - a)^2 + b^2)⁻¹)
        Filter.atTop (nhds (Real.pi / b)) := by
      refine Filter.Tendsto.congr' ?_ hlim
      exact Filter.Eventually.of_forall (fun n => (hIntEq n).symm)
    exact tendsto_nhds_unique hconv hlim'
  have hGcont : Continuous fun t : ℝ => (((t : ℂ) - z)^2)⁻¹ := by
    apply Continuous.inv₀ (f := fun t : ℝ => ((t : ℂ) - z)^2)
    · fun_prop
    · intro t
      exact pow_ne_zero 2 (hzne t)
  have hGint : MeasureTheory.Integrable (fun t : ℝ => (((t : ℂ) - z)^2)⁻¹) := by
    have hnormint : MeasureTheory.Integrable (fun t : ℝ => ‖(((t : ℂ) - z)^2)⁻¹‖) := by
      have hEq : (fun t : ℝ => ‖(((t : ℂ) - z)^2)⁻¹‖) = fun t : ℝ => ((t - a)^2 + b^2)⁻¹ :=
        funext hGnorm
      rw [hEq]
      exact hIint
    exact (MeasureTheory.integrable_norm_iff hGcont.measurable.aestronglyMeasurable).mp hnormint
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => -(((s : ℂ) - z)⁻¹)) (((t : ℂ) - z)^2)⁻¹ t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ) - z) (1 : ℂ) t := by
      have h := Complex.ofRealCLM.hasDerivAt (x := t)
      have h2 := h.sub_const z
      simpa using h2
    have hid : HasDerivAt (fun w : ℂ => w) (1 : ℂ) ((t : ℂ) - z) := hasDerivAt_id _
    have hinv0 := hid.inv (hzne t)
    have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-1 / ((t : ℂ) - z) ^ 2) ((t : ℂ) - z) := by
      simpa using hinv0
    have hcomp := HasDerivAt.comp t hinv h0
    have h3 := hcomp.neg
    simpa [one_div, neg_div] using h3
  have hFTC : ∀ x N : ℝ, x ≤ N →
      (∫ t in x..N, (((t : ℂ) - z)^2)⁻¹) = -(((N : ℂ) - z)⁻¹) + ((x : ℂ) - z)⁻¹ := by
    intro x N _
    have h := intervalIntegral.integral_deriv_mul_eq_sub
      (u := fun s : ℝ => -(((s : ℂ) - z)⁻¹)) (u' := fun s : ℝ => (((s : ℂ) - z)^2)⁻¹)
      (v := fun _ : ℝ => (1 : ℂ)) (v' := fun _ : ℝ => 0)
      (fun s _ => hderiv s) (fun s _ => hasDerivAt_const s 1)
      (hGcont.intervalIntegrable x N) intervalIntegrable_const
    simpa using h
  have hvol : ∀ x : ℝ, (volume : Measure ℝ) ({x} : Set ℝ) = 0 := by
    intro x
    have h1 : ({x} : Set ℝ) ⊆ Set.Icc x x := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
    have h2 : (volume : Measure ℝ) ({x} : Set ℝ) ≤ (volume : Measure ℝ) (Set.Icc x x) :=
      MeasureTheory.measure_mono h1
    rw [Real.volume_Icc] at h2
    simpa using h2
  have hae : ∀ x : ℝ, ∀ᵐ t ∂(volume : Measure ℝ), t ≠ x := by
    intro x
    change ({t : ℝ | t ≠ x} ∈ MeasureTheory.ae (volume : Measure ℝ))
    rw [MeasureTheory.mem_ae_iff]
    have hcompl : ({t : ℝ | t ≠ x} : Set ℝ)ᶜ = {x} := by
      ext t
      simp
    rw [hcompl]
    exact hvol x
  have hIci : ∀ x : ℝ,
      (∫ t in Set.Ici x, (((t : ℂ) - z)^2)⁻¹) = ∫ t in Set.Ioi x, (((t : ℂ) - z)^2)⁻¹ := by
    intro x
    rw [← MeasureTheory.integral_indicator measurableSet_Ici,
      ← MeasureTheory.integral_indicator measurableSet_Ioi]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae x] with t ht
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : x ≤ t
    · have h2 : x < t := lt_of_le_of_ne h (Ne.symm ht)
      simp [Set.mem_Ici, Set.mem_Ioi, h, h2]
    · have h2 : ¬ x < t := fun hlt => h (le_of_lt hlt)
      simp [Set.mem_Ici, Set.mem_Ioi, h, h2]
  have hkl : Filter.Tendsto (fun n : ℕ => ((((n : ℝ)) : ℂ) - z)⁻¹) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmain : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hg : Filter.Tendsto (fun n : ℕ => 2 * ((n : ℝ))⁻¹) Filter.atTop (nhds 0) := by
      simpa using hmain.const_mul 2
    have hbd : ∀ᶠ n : ℕ in Filter.atTop, ‖((((n : ℝ)) : ℂ) - z)⁻¹‖ ≤ 2 * ((n : ℝ))⁻¹ := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually
        (Filter.eventually_ge_atTop (2 * ‖z‖ + 1))] with n hn
      rw [norm_inv]
      have hz0 : (0:ℝ) ≤ 2 * ‖z‖ := by positivity
      have hnr0 : (0:ℝ) < (n : ℝ) := by linarith
      have hw : (n : ℝ) / 2 ≤ ‖((((n : ℝ)) : ℂ)) - z‖ := by
        have h1 : ‖((((n : ℝ)) : ℂ))‖ = (n : ℝ) := by simp
        have h2 : ‖((((n : ℝ)) : ℂ)) - z + z‖ ≤ ‖((((n : ℝ)) : ℂ)) - z‖ + ‖z‖ :=
          norm_add_le _ _
        rw [sub_add_cancel] at h2
        linarith
      have hpos : (0:ℝ) < (n : ℝ) / 2 := by linarith
      calc (‖((((n : ℝ)) : ℂ)) - z‖)⁻¹ ≤ ((n : ℝ) / 2)⁻¹ := by
            simpa using one_div_le_one_div_of_le hpos hw
        _ = 2 * ((n : ℝ))⁻¹ := by
            rw [div_eq_mul_inv, mul_inv, inv_inv, mul_comm]
    exact squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) hbd hg
  have hrepr : ∀ (ρ : Measure ℝ) [MeasureTheory.IsFiniteMeasure ρ],
      (∫ x, ((x : ℂ) - z)⁻¹ ∂ρ) = ∫ t, (ρ (Set.Iic t)).toReal • (((t : ℂ) - z)^2)⁻¹ := by
    intro ρ _
    have hK : ∀ x : ℝ, ((x : ℂ) - z)⁻¹ = ∫ t in Set.Ici x, (((t : ℂ) - z)^2)⁻¹ := by
      intro x
      have hbound2 : Filter.Tendsto
          (fun n : ℕ => -((((n : ℝ)) : ℂ) - z)⁻¹ + ((x : ℂ) - z)⁻¹) Filter.atTop
          (nhds ((x : ℂ) - z)⁻¹) := by
        have h1 := hkl.neg
        have h2 := h1.add_const (((x : ℂ) - z)⁻¹)
        simpa using h2
      have hlim2 : Filter.Tendsto
          (fun n : ℕ => ∫ t in x..(n:ℝ), (((t : ℂ) - z)^2)⁻¹) Filter.atTop
          (nhds ((x : ℂ) - z)⁻¹) := by
        refine Filter.Tendsto.congr' ?_ hbound2
        filter_upwards [tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop x)]
          with n hn
        exact (hFTC x (n:ℝ) hn).symm
      have hlim1 : Filter.Tendsto
          (fun n : ℕ => ∫ t in x..(n:ℝ), (((t : ℂ) - z)^2)⁻¹) Filter.atTop
          (nhds (∫ t in Set.Ioi x, (((t : ℂ) - z)^2)⁻¹)) := by
        have hDCT : Filter.Tendsto
            (fun n : ℕ => ∫ t in Set.Ioc x (n:ℝ), (((t : ℂ) - z)^2)⁻¹) Filter.atTop
            (nhds (∫ t in Set.Ioi x, (((t : ℂ) - z)^2)⁻¹)) := by
          have h0 : Filter.Tendsto
              (fun n : ℕ => ∫ t, (Set.Ioc x (n:ℝ)).indicator
                (fun s : ℝ => (((s : ℂ) - z)^2)⁻¹) t) Filter.atTop
              (nhds (∫ t, (Set.Ioi x).indicator
                (fun s : ℝ => (((s : ℂ) - z)^2)⁻¹) t)) := by
            refine MeasureTheory.tendsto_integral_of_dominated_convergence
              (fun t : ℝ => ‖(((t : ℂ) - z)^2)⁻¹‖) ?_ hGint.norm ?_ ?_
            · intro n
              exact hGint.aestronglyMeasurable.indicator measurableSet_Ioc
            · intro n
              filter_upwards with t
              rw [Set.indicator_apply]
              by_cases h : t ∈ Set.Ioc x (n:ℝ)
              · rw [if_pos h]
              · rw [if_neg h, norm_zero]
                positivity
            · filter_upwards with t
              by_cases h : x < t
              · have hev : ∀ᶠ n : ℕ in Filter.atTop, t ≤ (n:ℝ) :=
                  tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop t)
                have hEq : (fun n : ℕ => (Set.Ioc x (n:ℝ)).indicator
                    (fun s : ℝ => (((s : ℂ) - z)^2)⁻¹) t) =ᶠ[Filter.atTop]
                    (fun _ => (((t : ℂ) - z)^2)⁻¹) := by
                  filter_upwards [hev] with n hn
                  exact Set.indicator_of_mem (f := fun s : ℝ => (((s : ℂ) - z)^2)⁻¹)
                    (Set.mem_Ioc.mpr ⟨h, hn⟩)
                have htarget : (Set.Ioi x).indicator (fun s : ℝ => (((s : ℂ) - z)^2)⁻¹) t
                    = (((t : ℂ) - z)^2)⁻¹ :=
                  Set.indicator_of_mem (f := fun s : ℝ => (((s : ℂ) - z)^2)⁻¹) h
                rw [htarget]
                exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
              · have hEq : (fun n : ℕ => (Set.Ioc x (n:ℝ)).indicator
                    (fun s : ℝ => (((s : ℂ) - z)^2)⁻¹) t) =ᶠ[Filter.atTop]
                    (fun _ => (0 : ℂ)) := by
                  filter_upwards with n
                  simp [Set.indicator_apply, Set.mem_Ioc, h]
                have htarget : (Set.Ioi x).indicator (fun s : ℝ => (((s : ℂ) - z)^2)⁻¹) t = 0 := by
                  simp [Set.indicator_apply, Set.mem_Ioi, h]
                rw [htarget]
                exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
          simp only [MeasureTheory.integral_indicator measurableSet_Ioc,
            MeasureTheory.integral_indicator measurableSet_Ioi] at h0
          exact h0
        refine Filter.Tendsto.congr' ?_ hDCT
        filter_upwards [tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop x)]
          with n hn
        exact (intervalIntegral.integral_of_le hn).symm
      have hIoi : (∫ t in Set.Ioi x, (((t : ℂ) - z)^2)⁻¹) = ((x : ℂ) - z)⁻¹ :=
        tendsto_nhds_unique hlim1 hlim2
      rw [hIci x]
      exact hIoi.symm
    have hmeas_le : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
      measurableSet_le measurable_fst measurable_snd
    have hfun_eq : (Function.uncurry (fun x t : ℝ => if x ≤ t then (((t : ℂ) - z)^2)⁻¹ else 0))
        = {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p : ℝ × ℝ => (((p.2 : ℂ) - z)^2)⁻¹) := by
      funext p
      simp [Function.uncurry, Set.indicator_apply]
    have hΦmeas : MeasureTheory.AEStronglyMeasurable
        (Function.uncurry (fun x t : ℝ => if x ≤ t then (((t : ℂ) - z)^2)⁻¹ else 0))
        (ρ.prod volume) := by
      rw [hfun_eq]
      exact (hGcont.measurable.comp measurable_snd).aestronglyMeasurable.indicator hmeas_le
    have hboundint : MeasureTheory.Integrable (fun p : ℝ × ℝ => ‖(((p.2 : ℂ) - z)^2)⁻¹‖)
        (ρ.prod volume) := by
      have h1 : MeasureTheory.Integrable
          (fun p : ℝ × ℝ => (1:ℝ) * ‖(((p.2 : ℂ) - z)^2)⁻¹‖) (ρ.prod volume) :=
        MeasureTheory.Integrable.mul_prod (μ := ρ) (ν := (volume : Measure ℝ))
          (f := fun _ : ℝ => (1:ℝ)) (g := fun t : ℝ => ‖(((t : ℂ) - z)^2)⁻¹‖)
          (integrable_const (1:ℝ)) hGint.norm
      simpa using h1
    have hΦint : MeasureTheory.Integrable
        (Function.uncurry (fun x t : ℝ => if x ≤ t then (((t : ℂ) - z)^2)⁻¹ else 0))
        (ρ.prod volume) := by
      refine MeasureTheory.Integrable.mono' hboundint hΦmeas ?_
      filter_upwards with p
      by_cases h : p.1 ≤ p.2
      · simp [Function.uncurry, h]
      · simp [Function.uncurry, h]
    have hswap := MeasureTheory.integral_integral_swap (μ := ρ) (ν := (volume : Measure ℝ))
      (f := fun x t : ℝ => if x ≤ t then (((t : ℂ) - z)^2)⁻¹ else 0) hΦint
    have hL : (∫ x, ∫ t, (if x ≤ t then (((t : ℂ) - z)^2)⁻¹ else 0) ∂volume ∂ρ)
        = ∫ x, ((x : ℂ) - z)⁻¹ ∂ρ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∫ t : ℝ, (if x ≤ t then (((t : ℂ) - z)^2)⁻¹ else 0)) = ((x : ℂ) - z)⁻¹
      have hfun : (fun t : ℝ => if x ≤ t then (((t : ℂ) - z)^2)⁻¹ else 0)
          = (Set.Ici x).indicator (fun t : ℝ => (((t : ℂ) - z)^2)⁻¹) := by
        funext t
        simp [Set.indicator_apply, Set.mem_Ici]
      rw [hfun, MeasureTheory.integral_indicator measurableSet_Ici]
      exact (hK x).symm
    have hR : (∫ t, ∫ x, (if x ≤ t then (((t : ℂ) - z)^2)⁻¹ else 0) ∂ρ ∂volume)
        = ∫ t, (ρ (Set.Iic t)).toReal • (((t : ℂ) - z)^2)⁻¹ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show (∫ x : ℝ, (if x ≤ t then (((t : ℂ) - z)^2)⁻¹ else 0) ∂ρ)
        = (ρ (Set.Iic t)).toReal • (((t : ℂ) - z)^2)⁻¹
      have hfun : (fun x : ℝ => if x ≤ t then (((t : ℂ) - z)^2)⁻¹ else 0)
          = (Set.Iic t).indicator (fun _ : ℝ => (((t : ℂ) - z)^2)⁻¹) := by
        funext x
        simp [Set.indicator_apply, Set.mem_Iic]
      rw [hfun, MeasureTheory.integral_indicator measurableSet_Iic]
      simp
      exact Or.inl rfl
    exact hL.symm.trans (hswap.trans hR)
  have hInt : ∀ (ρ : Measure ℝ) [MeasureTheory.IsFiniteMeasure ρ],
      MeasureTheory.Integrable (fun t : ℝ => (ρ (Set.Iic t)).toReal • (((t : ℂ) - z)^2)⁻¹) := by
    intro ρ _
    have hmeas : Measurable fun t : ℝ => (ρ (Set.Iic t)).toReal := by
      have hmono : Monotone fun t : ℝ => ρ (Set.Iic t) := by
        intro s t hst
        exact MeasureTheory.measure_mono (fun y hy => le_trans hy hst)
      exact ENNReal.measurable_toReal.comp hmono.measurable
    have hbd : ∀ t : ℝ, ‖(ρ (Set.Iic t)).toReal • (((t : ℂ) - z)^2)⁻¹‖
        ≤ (ρ Set.univ).toReal * ((t - a)^2 + b^2)⁻¹ := by
      intro t
      rw [norm_smul, Real.norm_eq_abs, hGnorm t]
      have hle : (ρ (Set.Iic t)).toReal ≤ (ρ Set.univ).toReal :=
        ENNReal.toReal_mono (MeasureTheory.measure_ne_top ρ Set.univ)
          (MeasureTheory.measure_mono (Set.subset_univ _))
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    refine MeasureTheory.Integrable.mono' (hIint.const_mul (ρ Set.univ).toReal) ?_ ?_
    · exact (hmeas.smul hGcont.measurable).aestronglyMeasurable
    · filter_upwards with t
      exact hbd t
  have hdiff : (∫ t, (μ (Set.Iic t)).toReal • (((t : ℂ) - z)^2)⁻¹)
      - (∫ t, (ν (Set.Iic t)).toReal • (((t : ℂ) - z)^2)⁻¹)
      = ∫ t, ((μ (Set.Iic t)).toReal - (ν (Set.Iic t)).toReal) • (((t : ℂ) - z)^2)⁻¹ := by
    rw [← MeasureTheory.integral_sub (hInt μ) (hInt ν)]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t => (sub_smul _ _ _).symm)
  rw [hrepr μ, hrepr ν, hdiff]
  have hbnd : ∀ᵐ t : ℝ,
      ‖((μ (Set.Iic t)).toReal - (ν (Set.Iic t)).toReal) • (((t : ℂ) - z)^2)⁻¹‖
        ≤ d * ((t - a)^2 + b^2)⁻¹ := by
    filter_upwards with t
    rw [norm_smul, Real.norm_eq_abs, hGnorm t]
    exact mul_le_mul (hF t) le_rfl (by positivity) hd
  have hcalc : (∫ t : ℝ, d * ((t - a)^2 + b^2)⁻¹) = d * (Real.pi / z.im) := by
    rw [MeasureTheory.integral_const_mul, hIval, hb]
  exact (MeasureTheory.norm_integral_le_of_norm_le (hIint.const_mul d) hbnd).trans (le_of_eq hcalc)
  /- @proof-region region.target-node.session.363a550d11323621 end -/

end Statlib.Imported

