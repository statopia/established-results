import Statlib.HypothesisTesting.Nonparametric.MannWhitney
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
theorem statopia_math_node_1249221228_c96b816c : ∀ (m n : ℕ) (ν : MeasureTheory.Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν]
    (Kt L : ℝ) (hKt : 0 < Kt) (hL0 : 0 ≤ L) (hKL : Kt ≤ L)
    (i : Fin m) (j : Fin n)
    (hTail : ∀ t : ℝ, 0 < t →
      ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|} ≤
        ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (hVar : ∫ x, (x i j) ^ 2 ∂ν = 1),
    ∫ x, (x i j) ^ 2 * (if L < |x i j| then (1 : ℝ) else 0) ∂ν ≤
      4 * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
  /- @proof-region region.target-node.session.057ad986d3fb7b2d begin -/
  intro m n ν hν Kt L hKt hL0 hKL i j hTail hVar
  haveI := hν
  have hKtne : Kt ≠ 0 := ne_of_gt hKt
  have hLpos : 0 < L := by linarith
  have hYmeas : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j) := by fun_prop
  have hρmeas : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => max (|x i j| - L) 0) :=
    (hYmeas.abs.sub measurable_const).max measurable_const
  have hsqadd : ∀ x : Matrix (Fin m) (Fin n) ℝ, |x i j| ≤ (x i j) ^ 2 + 1 := by
    intro x
    nlinarith [sq_nonneg (|x i j| - 1 / 2), sq_abs (x i j), abs_nonneg (x i j)]
  have hIntY2 : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2) ν := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hVar
    norm_num at hVar
  have hIntG : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2 + 1) ν :=
    hIntY2.add (integrable_const 1)
  have hLconst : Measurable (fun _ : Matrix (Fin m) (Fin n) ℝ => L) := measurable_const
  have hsetInd : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|} :=
    measurableSet_lt hLconst hYmeas.abs
  have hindmeas : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => if L < |x i j| then (1 : ℝ) else 0) := by
    have hconst : Measurable (fun _ : Matrix (Fin m) (Fin n) ℝ => (1 : ℝ)) := measurable_const
    have h := Measurable.indicator hconst hsetInd
    simpa only [Set.indicator_apply, Set.mem_setOf_eq] using h
  have hInt1 : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => L ^ 2 * (if L < |x i j| then (1 : ℝ) else 0)) ν := by
    refine Integrable.mono' (integrable_const (L ^ 2)) (measurable_const.mul hindmeas).aestronglyMeasurable ?_
    filter_upwards with x
    by_cases hx : L < |x i j|
    · rw [if_pos hx, mul_one]
      simp
    · rw [if_neg hx, mul_zero, norm_zero]
      positivity
  have hIntρ : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => max (|x i j| - L) 0) ν := by
    refine Integrable.mono' hIntG hρmeas.aestronglyMeasurable ?_
    filter_upwards with x
    have h1 : max (|x i j| - L) 0 ≤ |x i j| := max_le (by linarith) (abs_nonneg _)
    have hb := hsqadd x
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ max (|x i j| - L) 0 from le_max_right _ _)]
    linarith
  have hIntρ2 : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (max (|x i j| - L) 0) ^ 2) ν := by
    have hmeas2 : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => (max (|x i j| - L) 0) ^ 2) := by
      have h := hρmeas.mul hρmeas
      simpa only [Pi.mul_apply, pow_two] using h
    refine Integrable.mono' hIntG hmeas2.aestronglyMeasurable ?_
    filter_upwards with x
    have h1 : max (|x i j| - L) 0 ≤ |x i j| := max_le (by linarith) (abs_nonneg _)
    have h2 : (0 : ℝ) ≤ max (|x i j| - L) 0 := le_max_right _ _
    have hb := hsqadd x
    have h3 : (0 : ℝ) ≤ |x i j| := abs_nonneg _
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (max (|x i j| - L) 0) ^ 2 by positivity)]
    nlinarith [h1, h2, hb, h3, sq_abs (x i j)]
  have hIntρc : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => 2 * L * (max (|x i j| - L) 0)) ν :=
    hIntρ.const_mul (2 * L)
  have hid : ∀ x : Matrix (Fin m) (Fin n) ℝ,
      (x i j) ^ 2 * (if L < |x i j| then (1 : ℝ) else 0)
        = L ^ 2 * (if L < |x i j| then (1 : ℝ) else 0)
          + (max (|x i j| - L) 0) ^ 2 + 2 * L * (max (|x i j| - L) 0) := by
    intro x
    by_cases hx : L < |x i j|
    · rw [if_pos hx, max_eq_left (show (0 : ℝ) ≤ |x i j| - L by linarith), ← sq_abs (x i j)]
      ring
    · rw [if_neg hx, max_eq_right (show |x i j| - L ≤ 0 by linarith [not_lt.mp hx])]
      ring
  have hb1 : ∫ x, L ^ 2 * (if L < |x i j| then (1 : ℝ) else 0) ∂ν ≤ 2 * L ^ 2 * Real.exp (-L / Kt) := by
    have hfun : (fun x : Matrix (Fin m) (Fin n) ℝ => L ^ 2 * (if L < |x i j| then (1 : ℝ) else 0))
        = (fun x => L ^ 2 * ({x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}.indicator (fun _ => (1 : ℝ)) x)) := by
      funext x
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    have hbase : ∫ x, ({x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}.indicator (fun _ => (1 : ℝ)) x) ∂ν
        = (ν {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}).toReal :=
      (Statlib.HypothesisTesting.measure_eq_integral_indicator hsetInd).symm
    have hbound : (ν {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}).toReal ≤ 2 * Real.exp (-L / Kt) := by
      have hne : ENNReal.ofReal (2 * Real.exp (-L / Kt)) ≠ ⊤ := ENNReal.ofReal_ne_top
      have h2 := ENNReal.toReal_mono hne (hTail L hLpos)
      rwa [ENNReal.toReal_ofReal (by positivity)] at h2
    rw [hfun, integral_const_mul, hbase]
    calc L ^ 2 * (ν {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}).toReal
        ≤ L ^ 2 * (2 * Real.exp (-L / Kt)) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 2 * L ^ 2 * Real.exp (-L / Kt) := by ring
  have hbρ : ∫ x, max (|x i j| - L) 0 ∂ν ≤ 2 * Kt * Real.exp (-L / Kt) := by
    have hnn : 0 ≤ᵐ[ν] (fun x : Matrix (Fin m) (Fin n) ℝ => max (|x i j| - L) 0) :=
      Filter.Eventually.of_forall (fun x => le_max_right _ _)
    have hA : AEMeasurable (fun x : Matrix (Fin m) (Fin n) ℝ => max (|x i j| - L) 0) ν :=
      hρmeas.aemeasurable
    have hlc := MeasureTheory.lintegral_eq_lintegral_meas_lt (μ := ν)
      (f := fun x : Matrix (Fin m) (Fin n) ℝ => max (|x i j| - L) 0) hnn hA
    have hbridge :
        (∫⁻ x, ENNReal.ofReal (max (|x i j| - L) 0) ∂ν).toReal
          = ∫ x, max (|x i j| - L) 0 ∂ν :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg hnn hIntρ
    have hbnd : ∀ t : ℝ, 0 < t →
        ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0}
          ≤ ENNReal.ofReal (2 * (Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t))) := by
      intro t ht
      have hsub : {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0} ⊆ {a | L + t < |a i j|} := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rcases lt_max_iff.mp ha with h | h
        · linarith
        · linarith
      have harg : -(L + t) / Kt = -L / Kt + -(1 / Kt) * t := by
        rw [div_eq_mul_inv]
        ring
      have hexp : Real.exp (-(L + t) / Kt) = Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t) := by
        rw [← Real.exp_add, ← harg]
      have hfin : ENNReal.ofReal (2 * Real.exp (-(L + t) / Kt))
          = ENNReal.ofReal (2 * (Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t))) := by
        rw [hexp]
      exact (measure_mono hsub).trans ((hTail (L + t) (by linarith)).trans (le_of_eq hfin))
    have hmono :
        ∫⁻ t in Set.Ioi 0, ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0}
          ≤ ∫⁻ t in Set.Ioi 0,
              ENNReal.ofReal (2 * (Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t))) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbnd t ht
    have hIntE : Integrable (fun t : ℝ => 2 * (Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t)))
        (volume.restrict (Set.Ioi 0)) := by
      have hb : Integrable (fun t : ℝ => Real.exp (-(1 / Kt) * t)) (volume.restrict (Set.Ioi 0)) :=
        exp_neg_integrableOn_Ioi 0 (b := 1 / Kt) (by positivity)
      exact (hb.const_mul (Real.exp (-L / Kt))).const_mul 2
    have hIntExp : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 / Kt) * t) = Kt := by
      have hpos : (0 : ℝ) < 1 / Kt := by positivity
      rw [integral_exp_mul_Ioi (a := -(1 / Kt)) (by linarith) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp
    have hEval :
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (2 * (Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t)))
          = ENNReal.ofReal (2 * Kt * Real.exp (-L / Kt)) := by
      have hnn2 : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
          (fun t : ℝ => 2 * (Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t))) :=
        Filter.Eventually.of_forall (fun t => by positivity)
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntE hnn2]
      congr 1
      rw [integral_const_mul, integral_const_mul, hIntExp]
      ring
    have hstep :
        (∫⁻ t in Set.Ioi 0, ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0}).toReal
          ≤ 2 * Kt * Real.exp (-L / Kt) := by
      have h1 : (∫⁻ t in Set.Ioi 0, ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0}).toReal
          ≤ (∫⁻ t in Set.Ioi 0,
              ENNReal.ofReal (2 * (Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t)))).toReal :=
        ENNReal.toReal_mono (by rw [hEval]; exact ENNReal.ofReal_ne_top) hmono
      rwa [hEval, ENNReal.toReal_ofReal (by positivity)] at h1
    calc ∫ x, max (|x i j| - L) 0 ∂ν
        = (∫⁻ t in Set.Ioi 0, ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0}).toReal := by
          rw [← hbridge, hlc]
      _ ≤ 2 * Kt * Real.exp (-L / Kt) := hstep
  have hbρ2 : ∫ x, (max (|x i j| - L) 0) ^ 2 ∂ν ≤ 8 * Kt ^ 2 * Real.exp (-L / Kt) := by
    have h2Kt : (2 : ℝ) * Kt ≠ 0 := by
      have hpos : (0 : ℝ) < 2 * Kt := by linarith
      exact ne_of_gt hpos
    have hnn : 0 ≤ᵐ[ν] (fun x : Matrix (Fin m) (Fin n) ℝ => max (|x i j| - L) 0) :=
      Filter.Eventually.of_forall (fun x => le_max_right _ _)
    have hA : AEMeasurable (fun x : Matrix (Fin m) (Fin n) ℝ => max (|x i j| - L) 0) ν :=
      hρmeas.aemeasurable
    have hrpow := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul (μ := ν)
      (f := fun x : Matrix (Fin m) (Fin n) ℝ => max (|x i j| - L) 0) hnn hA (p := 2) (by norm_num)
    have hrpow' : ∫⁻ x, ENNReal.ofReal ((max (|x i j| - L) 0) ^ (2 : ℝ)) ∂ν
        = ENNReal.ofReal 2 * ∫⁻ t in Set.Ioi 0,
            ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1)) :=
      hrpow
    have hbridge : (∫⁻ x, ENNReal.ofReal ((max (|x i j| - L) 0) ^ 2) ∂ν).toReal
        = ∫ x, (max (|x i j| - L) 0) ^ 2 ∂ν :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
        (Filter.Eventually.of_forall (fun x => sq_nonneg (max (|x i j| - L) 0))) hIntρ2
    have heq : ∫⁻ x, ENNReal.ofReal ((max (|x i j| - L) 0) ^ 2) ∂ν
        = ∫⁻ x, ENNReal.ofReal ((max (|x i j| - L) 0) ^ (2 : ℝ)) ∂ν := by
      simp only [Real.rpow_two]
    have ht1 : ∀ t : ℝ, t ^ ((2 : ℝ) - 1) = t := by
      intro t
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    have hkey : ∀ u : ℝ, 0 ≤ u → u * Real.exp (-u) ≤ 1 / 2 := by
      intro u hu
      have h1 : 1 + u / 2 ≤ Real.exp (u / 2) := by linarith [Real.add_one_le_exp (u / 2)]
      have hpos2 : (0 : ℝ) ≤ 1 + u / 2 := by linarith
      have h2 : (1 + u / 2) ^ 2 ≤ (Real.exp (u / 2)) ^ 2 := by
        nlinarith [h1, hpos2, Real.exp_pos (u / 2), sq_nonneg (Real.exp (u / 2) - (1 + u / 2))]
      have h3 : (Real.exp (u / 2)) ^ 2 = Real.exp u := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have h4 : (1 + u / 2) ^ 2 * Real.exp (-u) ≤ 1 := by
        have hposn : (0 : ℝ) < Real.exp (-u) := Real.exp_pos (-u)
        have h5 := mul_le_mul_of_nonneg_right h2 (le_of_lt hposn)
        rw [h3, ← Real.exp_add, add_neg_cancel, Real.exp_zero] at h5
        exact h5
      have h6 : 2 * u ≤ (1 + u / 2) ^ 2 := by nlinarith [sq_nonneg (1 - u / 2)]
      have hposn : (0 : ℝ) < Real.exp (-u) := Real.exp_pos (-u)
      have h7 : 2 * u * Real.exp (-u) ≤ (1 + u / 2) ^ 2 * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h6 (le_of_lt hposn)
      nlinarith [h4, h7]
    have hpt : ∀ t : ℝ, 0 < t →
        2 * Real.exp (-(L + t) / Kt) * t ≤ 2 * Kt * Real.exp (-L / Kt) * Real.exp (-(1 / (2 * Kt)) * t) := by
      intro t ht
      have h2Ktpos : (0 : ℝ) < 2 * Kt := by linarith
      have ht2 : 0 ≤ t / (2 * Kt) := by positivity
      have hb1 : t / (2 * Kt) * Real.exp (-(t / (2 * Kt))) ≤ 1 / 2 := hkey _ ht2
      have hb2 : (2 * Kt) * (t / (2 * Kt) * Real.exp (-(t / (2 * Kt)))) ≤ (2 * Kt) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hb1 (le_of_lt h2Ktpos)
      have hb3 : (2 * Kt) * (t / (2 * Kt)) = t := by field_simp
      have hb4 : (2 * Kt) * (t / (2 * Kt) * Real.exp (-(t / (2 * Kt))))
          = t * Real.exp (-(t / (2 * Kt))) := by
        rw [← mul_assoc, hb3]
      have hb5 : (2 * Kt) * (1 / 2) = Kt := by ring
      have hu : t * Real.exp (-(t / (2 * Kt))) ≤ Kt := by linarith [hb2, hb4, hb5]
      have he1 : -(1 / (2 * Kt)) * t = -(t / (2 * Kt)) := by field_simp
      have harg : -(L + t) / Kt = -L / Kt + (-(t / (2 * Kt)) + -(t / (2 * Kt))) := by
        field_simp
        ring
      have hexp : Real.exp (-(L + t) / Kt)
          = Real.exp (-L / Kt) * (Real.exp (-(t / (2 * Kt))) * Real.exp (-(t / (2 * Kt)))) := by
        rw [← Real.exp_add, ← Real.exp_add, ← harg]
      have hupper : 2 * (Real.exp (-L / Kt) * (Real.exp (-(t / (2 * Kt))) * Real.exp (-(t / (2 * Kt))))) * t
          ≤ 2 * Kt * Real.exp (-L / Kt) * Real.exp (-(t / (2 * Kt))) := by
        have h1 : (2 * Real.exp (-L / Kt) * Real.exp (-(t / (2 * Kt))))
              * (t * Real.exp (-(t / (2 * Kt))))
            ≤ (2 * Real.exp (-L / Kt) * Real.exp (-(t / (2 * Kt)))) * Kt :=
          mul_le_mul_of_nonneg_left hu (by positivity)
        nlinarith [h1]
      calc 2 * Real.exp (-(L + t) / Kt) * t
          = 2 * (Real.exp (-L / Kt) * (Real.exp (-(t / (2 * Kt))) * Real.exp (-(t / (2 * Kt))))) * t := by
            rw [hexp]
        _ ≤ 2 * Kt * Real.exp (-L / Kt) * Real.exp (-(t / (2 * Kt))) := hupper
        _ = 2 * Kt * Real.exp (-L / Kt) * Real.exp (-(1 / (2 * Kt)) * t) := by rw [he1]
    have hmono :
        ∫⁻ t in Set.Ioi 0,
            ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))
          ≤ ∫⁻ t in Set.Ioi 0,
              ENNReal.ofReal (2 * Kt * Real.exp (-L / Kt) * Real.exp (-(1 / (2 * Kt)) * t)) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hsub : {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0} ⊆ {a | L + t < |a i j|} := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rcases lt_max_iff.mp ha with h | h
        · linarith
        · linarith
      have htail2 : ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0}
          ≤ ENNReal.ofReal (2 * Real.exp (-(L + t) / Kt)) :=
        (measure_mono hsub).trans (hTail (L + t) (by linarith))
      have hstep1 : ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))
          ≤ ENNReal.ofReal (2 * Real.exp (-(L + t) / Kt) * t) := by
        have h1 : ENNReal.ofReal (t ^ ((2 : ℝ) - 1)) = ENNReal.ofReal t := by rw [ht1 t]
        rw [h1]
        calc ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0} * ENNReal.ofReal t
            ≤ ENNReal.ofReal (2 * Real.exp (-(L + t) / Kt)) * ENNReal.ofReal t :=
              mul_le_mul_of_nonneg_right htail2 (zero_le _)
          _ = ENNReal.ofReal (2 * Real.exp (-(L + t) / Kt) * t) :=
              (ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * Real.exp (-(L + t) / Kt) by positivity)).symm
      exact hstep1.trans (ENNReal.ofReal_le_ofReal (hpt t ht0))
    have hIntE2 : Integrable (fun t : ℝ => 2 * Kt * Real.exp (-L / Kt) * Real.exp (-(1 / (2 * Kt)) * t))
        (volume.restrict (Set.Ioi 0)) := by
      have hb : Integrable (fun t : ℝ => Real.exp (-(1 / (2 * Kt)) * t)) (volume.restrict (Set.Ioi 0)) :=
        exp_neg_integrableOn_Ioi 0 (b := 1 / (2 * Kt)) (by positivity)
      exact hb.const_mul (2 * Kt * Real.exp (-L / Kt))
    have hIntExp2 : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 / (2 * Kt)) * t) = 2 * Kt := by
      have hpos : (0 : ℝ) < 1 / (2 * Kt) := by positivity
      rw [integral_exp_mul_Ioi (a := -(1 / (2 * Kt))) (by linarith) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp
    have hEval2 : ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (2 * Kt * Real.exp (-L / Kt) * Real.exp (-(1 / (2 * Kt)) * t))
        = ENNReal.ofReal (4 * Kt ^ 2 * Real.exp (-L / Kt)) := by
      have hnn3 : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
          (fun t : ℝ => 2 * Kt * Real.exp (-L / Kt) * Real.exp (-(1 / (2 * Kt)) * t)) :=
        Filter.Eventually.of_forall (fun t => by positivity)
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntE2 hnn3]
      congr 1
      rw [integral_const_mul, hIntExp2]
      ring
    have hLbound :
        (∫⁻ t in Set.Ioi 0,
            ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1)))
          ≤ ENNReal.ofReal (4 * Kt ^ 2 * Real.exp (-L / Kt)) := hmono.trans (le_of_eq hEval2)
    have hfin :
        (ENNReal.ofReal 2 * ∫⁻ t in Set.Ioi 0,
            ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))).toReal
          ≤ 8 * Kt ^ 2 * Real.exp (-L / Kt) := by
      have h2 : (ENNReal.ofReal 2 * (∫⁻ t in Set.Ioi 0,
            ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1)))).toReal
          ≤ (ENNReal.ofReal 2 * ENNReal.ofReal (4 * Kt ^ 2 * Real.exp (-L / Kt))).toReal := by
        refine ENNReal.toReal_mono ?_ (mul_le_mul_left' hLbound _)
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
        exact ENNReal.ofReal_ne_top
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)] at h2
      rw [ENNReal.toReal_ofReal (by positivity)] at h2
      nlinarith [h2]
    calc ∫ x, (max (|x i j| - L) 0) ^ 2 ∂ν
        = (∫⁻ x, ENNReal.ofReal ((max (|x i j| - L) 0) ^ 2) ∂ν).toReal := hbridge.symm
      _ = (∫⁻ x, ENNReal.ofReal ((max (|x i j| - L) 0) ^ (2 : ℝ)) ∂ν).toReal := by rw [heq]
      _ = (ENNReal.ofReal 2 * ∫⁻ t in Set.Ioi 0,
            ν {a : Matrix (Fin m) (Fin n) ℝ | t < max (|a i j| - L) 0} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))).toReal := by
          rw [hrpow']
      _ ≤ 8 * Kt ^ 2 * Real.exp (-L / Kt) := hfin
  have hbρc : ∫ x, 2 * L * (max (|x i j| - L) 0) ∂ν ≤ 4 * L * Kt * Real.exp (-L / Kt) := by
    rw [integral_const_mul]
    calc 2 * L * ∫ x, max (|x i j| - L) 0 ∂ν
        ≤ 2 * L * (2 * Kt * Real.exp (-L / Kt)) :=
          mul_le_mul_of_nonneg_left hbρ (by positivity)
      _ = 4 * L * Kt * Real.exp (-L / Kt) := by ring
  have hAB : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => L ^ 2 * (if L < |x i j| then (1 : ℝ) else 0) + (max (|x i j| - L) 0) ^ 2) ν :=
    hInt1.add hIntρ2
  have hsplit1 : ∫ x, (L ^ 2 * (if L < |x i j| then (1 : ℝ) else 0) + (max (|x i j| - L) 0) ^ 2 + 2 * L * (max (|x i j| - L) 0)) ∂ν
      = ∫ x, (L ^ 2 * (if L < |x i j| then (1 : ℝ) else 0) + (max (|x i j| - L) 0) ^ 2) ∂ν
        + ∫ x, 2 * L * (max (|x i j| - L) 0) ∂ν :=
    MeasureTheory.integral_add hAB hIntρc
  have hsplit2 : ∫ x, (L ^ 2 * (if L < |x i j| then (1 : ℝ) else 0) + (max (|x i j| - L) 0) ^ 2) ∂ν
      = ∫ x, L ^ 2 * (if L < |x i j| then (1 : ℝ) else 0) ∂ν + ∫ x, (max (|x i j| - L) 0) ^ 2 ∂ν :=
    MeasureTheory.integral_add hInt1 hIntρ2
  simp only [hid]
  rw [hsplit1, hsplit2]
  have hsum : ∫ x, L ^ 2 * (if L < |x i j| then (1 : ℝ) else 0) ∂ν
        + ∫ x, (max (|x i j| - L) 0) ^ 2 ∂ν + ∫ x, 2 * L * (max (|x i j| - L) 0) ∂ν
      ≤ 2 * L ^ 2 * Real.exp (-L / Kt) + 8 * Kt ^ 2 * Real.exp (-L / Kt)
        + 4 * L * Kt * Real.exp (-L / Kt) := by
    linarith [hb1, hbρ2, hbρc]
  refine le_trans hsum ?_
  have hcoef : (2 * L ^ 2 + 8 * Kt ^ 2) + 4 * L * Kt ≤ 4 * (L + Kt) ^ 2 := by
    nlinarith [hKL, hKt, mul_le_mul_of_nonneg_left hKL (le_of_lt hKt)]
  calc 2 * L ^ 2 * Real.exp (-L / Kt) + 8 * Kt ^ 2 * Real.exp (-L / Kt) + 4 * L * Kt * Real.exp (-L / Kt)
      = ((2 * L ^ 2 + 8 * Kt ^ 2) + 4 * L * Kt) * Real.exp (-L / Kt) := by ring
    _ ≤ 4 * (L + Kt) ^ 2 * Real.exp (-L / Kt) :=
        mul_le_mul_of_nonneg_right hcoef (le_of_lt (Real.exp_pos _))
  /- @proof-region region.target-node.session.057ad986d3fb7b2d end -/

end Statlib.Imported

