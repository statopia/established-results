import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Vocabulary
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Base

namespace PaperProofTasks.paper_fresh_20261101t120354916065z_dcf

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261101t120354916065z_dcf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1857258558_235502cf : ∀ (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t),
    IntegrableOn (fun s : ℝ => s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c)))
        (Set.Ioi (0 : ℝ)) volume ∧
      ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c)) ≤
        (t ^ 3 / 3 + 3 * (t + Real.sqrt c) ^ 3) * Real.exp (-(t ^ 2) / (2 * c)) := by
  /- @proof-region region.target-node.session.036ff574f897e995 begin -/
  intro c t hc ht
  have hcne : c ≠ 0 := ne_of_gt hc
  set E : ℝ := Real.exp (-(t ^ 2) / (2 * c)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, ← Real.exp_zero]
    refine Real.exp_le_exp_of_le ?_
    rw [neg_div]
    exact neg_nonpos.mpr (div_nonneg (sq_nonneg t) (by linarith))
  have hfx : Continuous (fun s : ℝ => s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))) := by
    have hmax : Continuous fun s : ℝ => max s t := continuous_id.max continuous_const
    have h1 : Continuous fun s : ℝ => -((max s t) ^ 2) / (2 * c) :=
      (hmax.pow 2).neg.div_const (2 * c)
    exact (continuous_id.pow 2).mul (Real.continuous_exp.comp h1)
  have hIntA : IntegrableOn (fun s : ℝ => s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c)))
      (Set.Ioc (0 : ℝ) t) volume := by
    refine ContinuousOn.integrableOn_of_subset_isCompact hfx.continuousOn
      (isCompact_Icc (a := (0 : ℝ)) (b := t)) measurableSet_Ioc Set.Ioc_subset_Icc_self ?_
    have hfin : volume (Set.Icc (0 : ℝ) t) < ⊤ :=
      (isCompact_Icc (a := (0 : ℝ)) (b := t)).measure_lt_top
    exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.Ioc_subset_Icc_self) hfin)
  have h2c : (0 : ℝ) < 2 * c := by linarith
  have h2c : (0 : ℝ) < 2 * c := by linarith
  have hexp_atBot : Filter.Tendsto Real.exp Filter.atBot (nhds 0) := by
    show Filter.map Real.exp Filter.atBot ≤ nhds 0
    rw [Real.map_exp_atBot]
    exact nhdsWithin_le_nhds
  have hexp_tendsto : Filter.Tendsto (fun s : ℝ => Real.exp (-(s ^ 2) / (2 * c)))
      Filter.atTop (nhds 0) := by
    have hin : Filter.Tendsto (fun s : ℝ => -(s ^ 2) / (2 * c)) Filter.atTop Filter.atBot := by
      rw [Filter.tendsto_atBot]
      intro b
      filter_upwards [Filter.eventually_ge_atTop (max (-b * (2 * c)) 1)] with s hs
      have hK : -b * (2 * c) ≤ s := le_trans (le_max_left _ _) hs
      have h1s : (1 : ℝ) ≤ s := le_trans (le_max_right _ _) hs
      have hs2 : -b * (2 * c) ≤ s ^ 2 := by nlinarith
      have hkey : -b ≤ s ^ 2 / (2 * c) := by
        rw [le_div_iff₀ h2c]
        linarith
      rw [neg_div]
      linarith
    exact hexp_atBot.comp hin
  have hcub_pos : Filter.Tendsto (fun s : ℝ => c * (s ^ 2 + 2 * c) * Real.exp (-(s ^ 2) / (2 * c)))
      Filter.atTop (nhds 0) := by
    have hinv : Filter.Tendsto (fun s : ℝ => s⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
    have hinvsq : Filter.Tendsto (fun s : ℝ => (s ^ 2)⁻¹) Filter.atTop (nhds 0) := by
      have h := hinv.mul hinv
      have h2 : (fun s : ℝ => (s ^ 2)⁻¹) = fun s : ℝ => s⁻¹ * s⁻¹ := by
        funext s
        show (s ^ 2)⁻¹ = s⁻¹ * s⁻¹
        rw [pow_two, mul_inv_rev]
      rw [← h2] at h
      simpa using h
    have hg : Filter.Tendsto (fun s : ℝ => 48 * c ^ 3 / s ^ 2) Filter.atTop (nhds 0) := by
      have h := hinvsq.const_mul (48 * c ^ 3)
      simpa [div_eq_mul_inv] using h
    have hsmall : ∀ s : ℝ, max (max (48 * c ^ 3) (2 * c)) 1 ≤ s →
        c * (s ^ 2 + 2 * c) * Real.exp (-(s ^ 2) / (2 * c)) ≤ 48 * c ^ 3 / s ^ 2 := by
      intro s hs
      have hA : 48 * c ^ 3 ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
      have hB : 2 * c ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
      have hC : (1 : ℝ) ≤ s := le_trans (le_max_right _ _) hs
      have hspos : (0 : ℝ) < s := by linarith
      have hs2c : 2 * c ≤ s ^ 2 := by nlinarith
      have hexp1 : Real.exp (-(s ^ 2) / (4 * c)) ≤ 4 * c / s ^ 2 := by
        have hu : (0 : ℝ) < 1 + s ^ 2 / (4 * c) := by positivity
        have hexppos : (0 : ℝ) < Real.exp (s ^ 2 / (4 * c)) := Real.exp_pos _
        have h4c : (0 : ℝ) < 4 * c := by linarith
        have hA1 : Real.exp (-(s ^ 2) / (4 * c)) ≤ 1 / (1 + s ^ 2 / (4 * c)) := by
          rw [neg_div, Real.exp_neg, ← one_div]
          rw [div_le_div_iff₀ hexppos hu]
          have := Real.add_one_le_exp (s ^ 2 / (4 * c))
          linarith
        have hB1 : 1 / (1 + s ^ 2 / (4 * c)) ≤ 4 * c / s ^ 2 := by
          rw [div_le_div_iff₀ hu (by positivity : (0 : ℝ) < s ^ 2)]
          have hkey : 4 * c * (s ^ 2 / (4 * c)) = s ^ 2 := by field_simp
          nlinarith [hkey]
        linarith [hA1, hB1]
      have hexp2 : Real.exp (-(s ^ 2) / (2 * c)) ≤ 16 * c ^ 2 / s ^ 4 := by
        have hsq : Real.exp (-(s ^ 2) / (4 * c)) * Real.exp (-(s ^ 2) / (4 * c))
            = Real.exp (-(s ^ 2) / (2 * c)) := by
          rw [← Real.exp_add]
          congr 1
          field_simp
          ring
        rw [← hsq]
        have h4 : (0 : ℝ) ≤ 4 * c / s ^ 2 := by positivity
        calc Real.exp (-(s ^ 2) / (4 * c)) * Real.exp (-(s ^ 2) / (4 * c))
            ≤ (4 * c / s ^ 2) * (4 * c / s ^ 2) :=
              mul_le_mul hexp1 hexp1 (le_of_lt (Real.exp_pos _)) h4
          _ = 16 * c ^ 2 / s ^ 4 := by
              field_simp
              ring
      have hstep1 : c * (s ^ 2 + 2 * c) ≤ 3 * c * s ^ 2 := by nlinarith
      have h1 : c * (s ^ 2 + 2 * c) * Real.exp (-(s ^ 2) / (2 * c))
          ≤ (3 * c * s ^ 2) * (16 * c ^ 2 / s ^ 4) :=
        mul_le_mul hstep1 hexp2 (le_of_lt (Real.exp_pos _)) (by positivity)
      have h2 : (3 * c * s ^ 2) * (16 * c ^ 2 / s ^ 4) = 48 * c ^ 3 / s ^ 2 := by
        field_simp
        ring
      linarith [h1, h2]
    have htrunc : Filter.Tendsto
        (fun s : ℝ => if max (max (48 * c ^ 3) (2 * c)) 1 ≤ s then
          c * (s ^ 2 + 2 * c) * Real.exp (-(s ^ 2) / (2 * c)) else 0)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero ?_ ?_ hg
      · intro s
        by_cases hs : max (max (48 * c ^ 3) (2 * c)) 1 ≤ s
        · rw [if_pos hs]; positivity
        · rw [if_neg hs]
      · intro s
        by_cases hs : max (max (48 * c ^ 3) (2 * c)) 1 ≤ s
        · rw [if_pos hs]; exact hsmall s hs
        · rw [if_neg hs]; positivity
    have heq : (fun s : ℝ => if max (max (48 * c ^ 3) (2 * c)) 1 ≤ s then
          c * (s ^ 2 + 2 * c) * Real.exp (-(s ^ 2) / (2 * c)) else 0)
        =ᶠ[Filter.atTop] (fun s : ℝ => c * (s ^ 2 + 2 * c) * Real.exp (-(s ^ 2) / (2 * c))) := by
      filter_upwards [Filter.eventually_ge_atTop (max (max (48 * c ^ 3) (2 * c)) 1)] with s hs
      rw [if_pos hs]
    exact Filter.Tendsto.congr' heq htrunc
  have hcub_tendsto :
      Filter.Tendsto (fun s : ℝ => -(c * (s ^ 2 + 2 * c)) * Real.exp (-(s ^ 2) / (2 * c)))
        Filter.atTop (nhds 0) := by
    have h := hcub_pos.neg
    simpa [neg_mul] using h
  have hderiv1 : ∀ x ∈ Set.Ici t,
      HasDerivAt (fun s : ℝ => -c * Real.exp (-(s ^ 2) / (2 * c)))
        (x * Real.exp (-(x ^ 2) / (2 * c))) x := by
    intro x _
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hin : HasDerivAt (fun s : ℝ => -(s ^ 2) / (2 * c)) (-(2 * x) / (2 * c)) x :=
      hsq.neg.div_const (2 * c)
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(s ^ 2) / (2 * c)))
        (Real.exp (-(x ^ 2) / (2 * c)) * (-(2 * x) / (2 * c))) x :=
      (Real.hasDerivAt_exp _).comp x hin
    have hG : HasDerivAt (fun s : ℝ => -c * Real.exp (-(s ^ 2) / (2 * c)))
        (-c * (Real.exp (-(x ^ 2) / (2 * c)) * (-(2 * x) / (2 * c)))) x :=
      hexp.const_mul (-c)
    have heq : -c * (Real.exp (-(x ^ 2) / (2 * c)) * (-(2 * x) / (2 * c)))
        = x * Real.exp (-(x ^ 2) / (2 * c)) := by
      field_simp
    rw [heq] at hG
    exact hG
  have hnn1 : ∀ x ∈ Set.Ioi t, (0 : ℝ) ≤ x * Real.exp (-(x ^ 2) / (2 * c)) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_of_le_of_lt ht hx)
    exact mul_nonneg hx0 (le_of_lt (Real.exp_pos _))
  have hlim1 : Filter.Tendsto (fun s : ℝ => -c * Real.exp (-(s ^ 2) / (2 * c)))
      Filter.atTop (nhds 0) := by
    have h := hexp_tendsto.const_mul (-c)
    simpa using h
  have hint1 : IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2) / (2 * c))) (Set.Ioi t) volume :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (g := fun s : ℝ => -c * Real.exp (-(s ^ 2) / (2 * c)))
      (g' := fun s : ℝ => s * Real.exp (-(s ^ 2) / (2 * c)))
      (a := t) (l := 0) hderiv1 hnn1 hlim1
  have hInt1 : ∫ x in Set.Ioi t, x * Real.exp (-(x ^ 2) / (2 * c)) = c * E := by
    have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
      (g := fun s : ℝ => -c * Real.exp (-(s ^ 2) / (2 * c)))
      (g' := fun s : ℝ => s * Real.exp (-(s ^ 2) / (2 * c)))
      (a := t) (l := 0) hderiv1 hnn1 hlim1
    rw [h]
    simp only [hE]
    ring
  have hderiv3 : ∀ x ∈ Set.Ici t,
      HasDerivAt (fun s : ℝ => -(c * (s ^ 2 + 2 * c)) * Real.exp (-(s ^ 2) / (2 * c)))
        (x ^ 3 * Real.exp (-(x ^ 2) / (2 * c))) x := by
    intro x _
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hpoly : HasDerivAt (fun s : ℝ => s ^ 2 + 2 * c) (2 * x) x :=
      hsq.add_const (2 * c)
    have hin : HasDerivAt (fun s : ℝ => -(s ^ 2) / (2 * c)) (-(2 * x) / (2 * c)) x :=
      hsq.neg.div_const (2 * c)
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(s ^ 2) / (2 * c)))
        (Real.exp (-(x ^ 2) / (2 * c)) * (-(2 * x) / (2 * c))) x :=
      (Real.hasDerivAt_exp _).comp x hin
    have hu : HasDerivAt (fun s : ℝ => -(c * (s ^ 2 + 2 * c))) (-(c * (2 * x))) x :=
      (hpoly.const_mul c).neg
    have hG : HasDerivAt (fun s : ℝ => -(c * (s ^ 2 + 2 * c)) * Real.exp (-(s ^ 2) / (2 * c)))
        (-(c * (2 * x)) * Real.exp (-(x ^ 2) / (2 * c)) +
          (-(c * (x ^ 2 + 2 * c))) * (Real.exp (-(x ^ 2) / (2 * c)) * (-(2 * x) / (2 * c)))) x :=
      hu.mul hexp
    have heq : -(c * (2 * x)) * Real.exp (-(x ^ 2) / (2 * c)) +
          (-(c * (x ^ 2 + 2 * c))) * (Real.exp (-(x ^ 2) / (2 * c)) * (-(2 * x) / (2 * c)))
        = x ^ 3 * Real.exp (-(x ^ 2) / (2 * c)) := by
      field_simp
      ring
    rw [heq] at hG
    exact hG
  have hnn3 : ∀ x ∈ Set.Ioi t, (0 : ℝ) ≤ x ^ 3 * Real.exp (-(x ^ 2) / (2 * c)) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_of_le_of_lt ht hx)
    exact mul_nonneg (pow_nonneg hx0 3) (le_of_lt (Real.exp_pos _))
  have hint3 : IntegrableOn (fun x : ℝ => x ^ 3 * Real.exp (-(x ^ 2) / (2 * c))) (Set.Ioi t) volume :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (g := fun s : ℝ => -(c * (s ^ 2 + 2 * c)) * Real.exp (-(s ^ 2) / (2 * c)))
      (g' := fun s : ℝ => s ^ 3 * Real.exp (-(s ^ 2) / (2 * c)))
      (a := t) (l := 0) hderiv3 hnn3 hcub_tendsto
  have hInt3 : ∫ x in Set.Ioi t, x ^ 3 * Real.exp (-(x ^ 2) / (2 * c)) = c * (t ^ 2 + 2 * c) * E := by
    have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
      (g := fun s : ℝ => -(c * (s ^ 2 + 2 * c)) * Real.exp (-(s ^ 2) / (2 * c)))
      (g' := fun s : ℝ => s ^ 3 * Real.exp (-(s ^ 2) / (2 * c)))
      (a := t) (l := 0) hderiv3 hnn3 hcub_tendsto
    rw [h]
    simp only [hE]
    ring
  have hsc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsc0 : (0 : ℝ) ≤ Real.sqrt c := le_of_lt hsc
  have hscne : Real.sqrt c ≠ 0 := ne_of_gt hsc
  have hsqc : Real.sqrt c * Real.sqrt c = c := by
    rw [← pow_two]
    exact Real.sq_sqrt (le_of_lt hc)
  have hpt : ∀ x ∈ Set.Ioi t, x ^ 2 * Real.exp (-(x ^ 2) / (2 * c)) ≤
      Real.sqrt c * (x * Real.exp (-(x ^ 2) / (2 * c))) +
        1 / Real.sqrt c * (x ^ 3 * Real.exp (-(x ^ 2) / (2 * c))) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_of_le_of_lt ht hx)
    have hkey : x ^ 2 ≤ Real.sqrt c * x + 1 / Real.sqrt c * x ^ 3 := by
      have hmain : x ^ 2 * Real.sqrt c ≤
          (Real.sqrt c * x + 1 / Real.sqrt c * x ^ 3) * Real.sqrt c := by
        have hdiv : (1 / Real.sqrt c * x ^ 3) * Real.sqrt c = x ^ 3 := by field_simp
        have hquad : (0 : ℝ) ≤ x ^ 2 - Real.sqrt c * x + c := by
          nlinarith [sq_nonneg (x - Real.sqrt c / 2), hsqc]
        have hx3 : x * (x ^ 2 - Real.sqrt c * x + c) = x ^ 3 - Real.sqrt c * x ^ 2 + c * x := by
          ring
        have hnn2 : (0 : ℝ) ≤ x ^ 3 - Real.sqrt c * x ^ 2 + c * x := by
          rw [← hx3]
          exact mul_nonneg hx0 hquad
        nlinarith [hnn2, hdiv, hsqc]
      exact le_of_mul_le_mul_right hmain hsc
    have hexpnn : (0 : ℝ) ≤ Real.exp (-(x ^ 2) / (2 * c)) := le_of_lt (Real.exp_pos _)
    calc x ^ 2 * Real.exp (-(x ^ 2) / (2 * c))
        ≤ (Real.sqrt c * x + 1 / Real.sqrt c * x ^ 3) * Real.exp (-(x ^ 2) / (2 * c)) :=
          mul_le_mul_of_nonneg_right hkey hexpnn
      _ = Real.sqrt c * (x * Real.exp (-(x ^ 2) / (2 * c))) +
            1 / Real.sqrt c * (x ^ 3 * Real.exp (-(x ^ 2) / (2 * c))) := by ring
  have hMA : Integrable (fun x : ℝ => Real.sqrt c * (x * Real.exp (-(x ^ 2) / (2 * c))))
      (volume.restrict (Set.Ioi t)) := hint1.const_mul _
  have hMB : Integrable (fun x : ℝ => 1 / Real.sqrt c * (x ^ 3 * Real.exp (-(x ^ 2) / (2 * c))))
      (volume.restrict (Set.Ioi t)) := hint3.const_mul _
  have hM : Integrable (fun x : ℝ => Real.sqrt c * (x * Real.exp (-(x ^ 2) / (2 * c))) +
      1 / Real.sqrt c * (x ^ 3 * Real.exp (-(x ^ 2) / (2 * c))))
      (volume.restrict (Set.Ioi t)) := hMA.add hMB
  have htail2 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / (2 * c)))
      (volume.restrict (Set.Ioi t)) := by
    have hcont : Continuous fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / (2 * c)) := by
      have h1 : Continuous fun x : ℝ => -(x ^ 2) / (2 * c) :=
        (continuous_id.pow 2).neg.div_const (2 * c)
      exact (continuous_id.pow 2).mul (Real.continuous_exp.comp h1)
    refine MeasureTheory.Integrable.mono' hM hcont.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ x ^ 2 * Real.exp (-(x ^ 2) / (2 * c)) by positivity)] using hpt x hx
  have htailble : ∫ x in Set.Ioi t, x ^ 2 * Real.exp (-(x ^ 2) / (2 * c))
      ≤ Real.sqrt c * (c * E) + 1 / Real.sqrt c * (c * (t ^ 2 + 2 * c) * E) := by
    have hmono : ∫ x in Set.Ioi t, x ^ 2 * Real.exp (-(x ^ 2) / (2 * c))
        ≤ ∫ x in Set.Ioi t, Real.sqrt c * (x * Real.exp (-(x ^ 2) / (2 * c))) +
            1 / Real.sqrt c * (x ^ 3 * Real.exp (-(x ^ 2) / (2 * c))) := by
      refine MeasureTheory.setIntegral_mono_ae_restrict htail2 hM ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpt x hx
    have hIntM : ∫ x in Set.Ioi t, Real.sqrt c * (x * Real.exp (-(x ^ 2) / (2 * c))) +
        1 / Real.sqrt c * (x ^ 3 * Real.exp (-(x ^ 2) / (2 * c)))
        = Real.sqrt c * (c * E) + 1 / Real.sqrt c * (c * (t ^ 2 + 2 * c) * E) := by
      rw [MeasureTheory.integral_add hMA hMB, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, hInt1, hInt3]
    linarith [hmono, hIntM]
  have htailf : ∫ x in Set.Ioi t, x ^ 2 * Real.exp (-(x ^ 2) / (2 * c))
      ≤ 3 * (t + Real.sqrt c) ^ 3 * E := by
    refine le_trans htailble ?_
    have hLHS : Real.sqrt c * (c * E) + 1 / Real.sqrt c * (c * (t ^ 2 + 2 * c) * E)
        = (3 * (Real.sqrt c * c) + Real.sqrt c * t ^ 2) * E := by
      field_simp
      nlinarith [hsqc]
    have hexp3 : (t + Real.sqrt c) ^ 3
        = t ^ 3 + 3 * t ^ 2 * Real.sqrt c + 3 * t * c + c * Real.sqrt c := by
      have h1 : (t + Real.sqrt c) ^ 3
          = t ^ 3 + 3 * t ^ 2 * Real.sqrt c + 3 * t * (Real.sqrt c * Real.sqrt c) +
              Real.sqrt c * (Real.sqrt c * Real.sqrt c) := by ring
      rw [h1, hsqc]
      ring
    have hineq : 3 * (Real.sqrt c * c) + Real.sqrt c * t ^ 2 ≤ 3 * (t + Real.sqrt c) ^ 3 := by
      rw [hexp3]
      nlinarith [hsc0, sq_nonneg t, mul_nonneg ht hsc0, mul_nonneg (mul_nonneg ht ht) hsc0]
    rw [hLHS]
    exact mul_le_mul_of_nonneg_right hineq (le_of_lt hEpos)
  have htailFmax : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-((max x t) ^ 2) / (2 * c)))
      (Set.Ioi t) volume := by
    refine MeasureTheory.Integrable.mono' hM hfx.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hxmax : max x t = x := max_eq_left (le_of_lt hx)
    have hp := hpt x hx
    rw [hxmax]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ x ^ 2 * Real.exp (-(x ^ 2) / (2 * c)) by positivity)] using hp
  have hhead : ∫ x in (0 : ℝ)..t, x ^ 2 * Real.exp (-((max x t) ^ 2) / (2 * c)) = t ^ 3 / 3 * E := by
    rw [intervalIntegral.integral_of_le ht]
    have hcongr : Set.EqOn (fun x : ℝ => x ^ 2 * Real.exp (-((max x t) ^ 2) / (2 * c)))
        (fun x : ℝ => E * x ^ 2) (Set.Ioc (0 : ℝ) t) := by
      intro x hx
      have hxt : x ≤ t := hx.2
      show x ^ 2 * Real.exp (-((max x t) ^ 2) / (2 * c)) = E * x ^ 2
      rw [max_eq_right hxt, hE]
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hcongr,
      MeasureTheory.integral_const_mul]
    have hpow : ∫ x in Set.Ioc (0 : ℝ) t, x ^ 2 = t ^ 3 / 3 := by
      rw [← intervalIntegral.integral_of_le ht]
      have hp := integral_pow (a := (0 : ℝ)) (b := t) 2
      rw [hp]
      norm_num
    rw [hpow]
    ring
  have hsplit : (∫ x in (0 : ℝ)..t, x ^ 2 * Real.exp (-((max x t) ^ 2) / (2 * c))) +
      ∫ x in Set.Ioi t, x ^ 2 * Real.exp (-((max x t) ^ 2) / (2 * c)) =
      ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-((max x t) ^ 2) / (2 * c)) :=
    intervalIntegral.integral_interval_add_Ioi' (hfx.intervalIntegrable 0 t) htailFmax
  have hIntFinal : ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-((max x t) ^ 2) / (2 * c))
      ≤ (t ^ 3 / 3 + 3 * (t + Real.sqrt c) ^ 3) * E := by
    rw [← hsplit]
    have htailcongr : ∫ x in Set.Ioi t, x ^ 2 * Real.exp (-((max x t) ^ 2) / (2 * c))
        = ∫ x in Set.Ioi t, x ^ 2 * Real.exp (-(x ^ 2) / (2 * c)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      show x ^ 2 * Real.exp (-((max x t) ^ 2) / (2 * c)) = x ^ 2 * Real.exp (-(x ^ 2) / (2 * c))
      rw [max_eq_left (le_of_lt hx)]
    rw [hhead, htailcongr]
    calc t ^ 3 / 3 * E + ∫ x in Set.Ioi t, x ^ 2 * Real.exp (-(x ^ 2) / (2 * c))
        ≤ t ^ 3 / 3 * E + 3 * (t + Real.sqrt c) ^ 3 * E := by linarith [htailf]
      _ = (t ^ 3 / 3 + 3 * (t + Real.sqrt c) ^ 3) * E := by ring
  have hseteq : Set.Ioc (0 : ℝ) t ∪ Set.Ioi t = Set.Ioi (0 : ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h1)
      · exact h1
      · exact lt_of_le_of_lt ht h1
    · intro hx
      by_cases h : x ≤ t
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  refine ⟨?_, ?_⟩
  · rw [← hseteq]
    exact hIntA.union htailFmax
  · exact hIntFinal
  /- @proof-region region.target-node.session.036ff574f897e995 end -/

end Statlib.Imported

