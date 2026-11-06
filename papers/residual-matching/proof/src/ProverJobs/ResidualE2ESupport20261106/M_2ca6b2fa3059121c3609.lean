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
theorem statopia_math_node_983993472_4468443a : ∀ (m n : ℕ) (ν : MeasureTheory.Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν]
    (Kt L : ℝ) (hKt : 0 < Kt) (hL0 : 0 ≤ L) (i : Fin m) (j : Fin n)
    (hTail : ∀ t : ℝ, 0 < t →
      ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|} ≤
        ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (hVar : ∫ x, (x i j) ^ 2 ∂ν = 1),
    ∫ x, |x i j| * (if L < |x i j| then (1 : ℝ) else 0) ∂ν ≤
      2 * (L + Kt) * Real.exp (-L / Kt) := by
  /- @proof-region region.target-node.session.a21bba8101745e17 begin -/
  intro m n ν hν Kt L hKt hL0 i j hTail hVar
  haveI := hν
  have hmY : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j) := by fun_prop
  have hin2 : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2) ν := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hVar
    norm_num at hVar
  have hY : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j) ν := by
    refine Integrable.mono (hin2.add (integrable_const (1 : ℝ))) hmY.aestronglyMeasurable ?_
    filter_upwards with x
    have hb : |x i j| ≤ (x i j) ^ 2 + 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg ((x i j) - 1 / 2), sq_nonneg ((x i j) + 1 / 2)]
    simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x i j) ^ 2 + 1)] using hb
  have habs : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => |x i j|) ν := hY.abs
  have hmYabs : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => |x i j|) := hmY.abs
  have hmeasT : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|} :=
    measurableSet_lt measurable_const hmYabs
  have hind : ∀ z : Matrix (Fin m) (Fin n) ℝ,
      (if L < |z i j| then (1 : ℝ) else 0) =
        {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : L < |z i j| <;> simp [Set.indicator, hz]
  have hIndMeas : Measurable (fun z : Matrix (Fin m) (Fin n) ℝ => (if L < |z i j| then (1 : ℝ) else 0)) := by
    have h2 : Measurable ({x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}.indicator (fun _ => (1 : ℝ))) :=
      (measurable_const : Measurable fun _ : Matrix (Fin m) (Fin n) ℝ => (1 : ℝ)).indicator hmeasT
    exact h2
  have hIntInd : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => L * (if L < |x i j| then (1 : ℝ) else 0)) ν := by
    refine Integrable.mono habs (hIndMeas.const_mul L).aestronglyMeasurable ?_
    filter_upwards with x
    have hb : |L * (if L < |x i j| then (1 : ℝ) else 0)| ≤ |x i j| := by
      by_cases hx : L < |x i j|
      · rw [if_pos hx, mul_one, abs_of_nonneg hL0]
        linarith
      · rw [if_neg hx, mul_zero, abs_zero]
        exact abs_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (x i j))] using hb
  set ρ : Matrix (Fin m) (Fin n) ℝ → ℝ := fun x => max (|x i j| - L) 0
  have hmρ : Measurable ρ := (hmYabs.sub measurable_const).max measurable_const
  have hρ_nonneg : 0 ≤ᶠ[ae ν] ρ := Filter.Eventually.of_forall fun x => le_max_right _ _
  have hpt : ∀ x : Matrix (Fin m) (Fin n) ℝ,
      |x i j| * (if L < |x i j| then (1 : ℝ) else 0) =
        ρ x + L * (if L < |x i j| then (1 : ℝ) else 0) := by
    intro x
    have hρx : ρ x = max (|x i j| - L) 0 := rfl
    rw [hρx]
    by_cases hx : L < |x i j|
    · have h1 : 0 ≤ |x i j| - L := by linarith
      simp only [if_pos hx, mul_one, max_eq_left h1]
      ring
    · have h1 : |x i j| - L ≤ 0 := by linarith [not_lt.mp hx]
      simp only [if_neg hx, mul_zero, add_zero, max_eq_right h1]
  have hρ_int : Integrable ρ ν := by
    refine Integrable.mono habs hmρ.aestronglyMeasurable ?_
    filter_upwards with x
    have hρx : ρ x = max (|x i j| - L) 0 := rfl
    have hnn : 0 ≤ max (|x i j| - L) 0 := le_max_right _ _
    have hle : max (|x i j| - L) 0 ≤ |x i j| := by
      by_cases h3 : |x i j| - L ≤ 0
      · rw [max_eq_right h3]
        exact abs_nonneg _
      · rw [max_eq_left (by linarith)]
        linarith
    rw [hρx]
    simpa [Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg (abs_nonneg (x i j))] using hle

  have hsum : ∫ x, |x i j| * (if L < |x i j| then (1 : ℝ) else 0) ∂ν
      = ∫ x, ρ x ∂ν + ∫ x, L * (if L < |x i j| then (1 : ℝ) else 0) ∂ν := by
    rw [← MeasureTheory.integral_add hρ_int hIntInd]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hρbound : ∫ x, ρ x ∂ν ≤ 2 * Kt * Real.exp (-L / Kt) := by
    have hlc : ∫⁻ x, ENNReal.ofReal (ρ x) ∂ν
        = ∫⁻ t in Set.Ioi (0 : ℝ), ν {x : Matrix (Fin m) (Fin n) ℝ | t < ρ x} :=
      MeasureTheory.lintegral_eq_lintegral_meas_lt ν hρ_nonneg hmρ.aemeasurable
    have hmono : ∫⁻ t in Set.Ioi (0 : ℝ), ν {x : Matrix (Fin m) (Fin n) ℝ | t < ρ x}
        ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t)) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      have hsub : {x : Matrix (Fin m) (Fin n) ℝ | t < ρ x} ⊆ {x : Matrix (Fin m) (Fin n) ℝ | L + t < |x i j|} := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        have hx' : t < max (|x i j| - L) 0 := hx
        by_cases h3 : |x i j| - L ≤ 0
        · rw [max_eq_right h3] at hx'
          linarith
        · rw [max_eq_left (by linarith)] at hx'
          linarith
      calc ν {x : Matrix (Fin m) (Fin n) ℝ | t < ρ x}
          ≤ ν {x : Matrix (Fin m) (Fin n) ℝ | L + t < |x i j|} := measure_mono hsub
        _ ≤ ENNReal.ofReal (2 * Real.exp (-(L + t) / Kt)) := hTail (L + t) (by linarith)
        _ = ENNReal.ofReal (2 * Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t)) := by
            congr 1
            have hexp : -(L + t) / Kt = -L / Kt + -(1 / Kt) * t := by
              field_simp
              ring
            rw [hexp, Real.exp_add]
            ring
    have hInt1 : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t))
        = ENNReal.ofReal (2 * Kt * Real.exp (-L / Kt)) := by
      have hint : MeasureTheory.IntegrableOn
          (fun t : ℝ => 2 * Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t)) (Set.Ioi 0) := by
        have h0 : (0 : ℝ) < 1 / Kt := by positivity
        have hb := (exp_neg_integrableOn_Ioi (0 : ℝ) (b := 1 / Kt) h0).const_mul (2 * Real.exp (-L / Kt))
        simpa using hb
      have hnn : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
          0 ≤ 2 * Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t) :=
        Filter.Eventually.of_forall fun t => by positivity
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
      congr 1
      have hval : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 / Kt) * t) = Kt := by
        have h0 : (0 : ℝ) < 1 / Kt := by positivity
        rw [integral_exp_mul_Ioi (a := -(1 / Kt)) (by linarith) (0 : ℝ), mul_zero, Real.exp_zero]
        have hdiv : -(1 : ℝ) / (-(1 / Kt)) = Kt := by field_simp
        exact hdiv
      calc ∫ t in Set.Ioi (0 : ℝ), 2 * Real.exp (-L / Kt) * Real.exp (-(1 / Kt) * t)
          = 2 * Real.exp (-L / Kt) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 / Kt) * t) := by
              rw [MeasureTheory.integral_const_mul (2 * Real.exp (-L / Kt))]
        _ = 2 * Real.exp (-L / Kt) * Kt := by rw [hval]
        _ = 2 * Kt * Real.exp (-L / Kt) := by ring
    have hb2 : ∫⁻ x, ENNReal.ofReal (ρ x) ∂ν ≤ ENNReal.ofReal (2 * Kt * Real.exp (-L / Kt)) := by
      rw [hlc]
      exact le_trans hmono (le_of_eq hInt1)
    have hconv : (∫⁻ x, ENNReal.ofReal (ρ x) ∂ν).toReal = ∫ x, ρ x ∂ν :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg hρ_nonneg hρ_int
    rw [← hconv]
    calc (∫⁻ x, ENNReal.ofReal (ρ x) ∂ν).toReal
        ≤ (ENNReal.ofReal (2 * Kt * Real.exp (-L / Kt))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb2
      _ = 2 * Kt * Real.exp (-L / Kt) := ENNReal.toReal_ofReal (by positivity)
  have hindbound : ∫ x, L * (if L < |x i j| then (1 : ℝ) else 0) ∂ν ≤ 2 * L * Real.exp (-L / Kt) := by
    simp only [hind]
    rw [MeasureTheory.integral_const_mul]
    rw [← Statlib.HypothesisTesting.measure_eq_integral_indicator hmeasT]
    have hmeas : (ν {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}).toReal ≤ 2 * Real.exp (-L / Kt) := by
      rcases eq_or_lt_of_le hL0 with h0 | hpos
      · subst h0
        have h1 : ν {x : Matrix (Fin m) (Fin n) ℝ | (0 : ℝ) < |x i j|} ≤ 1 := by
          calc ν {x : Matrix (Fin m) (Fin n) ℝ | (0 : ℝ) < |x i j|} ≤ ν Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have h2 : (ν {x : Matrix (Fin m) (Fin n) ℝ | (0 : ℝ) < |x i j|}).toReal ≤ 1 := by
          calc (ν {x : Matrix (Fin m) (Fin n) ℝ | (0 : ℝ) < |x i j|}).toReal
              ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) h1
            _ = 1 := by simp
        refine h2.trans ?_
        rw [neg_zero, zero_div, Real.exp_zero]
        norm_num

      · have h1 := hTail L hpos
        calc (ν {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}).toReal
            ≤ (ENNReal.ofReal (2 * Real.exp (-L / Kt))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
          _ = 2 * Real.exp (-L / Kt) := ENNReal.toReal_ofReal (by positivity)
    calc L * (ν {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}).toReal
        ≤ L * (2 * Real.exp (-L / Kt)) := mul_le_mul_of_nonneg_left hmeas hL0
      _ = 2 * L * Real.exp (-L / Kt) := by ring
  rw [hsum]
  calc ∫ x, ρ x ∂ν + ∫ x, L * (if L < |x i j| then (1 : ℝ) else 0) ∂ν
      ≤ 2 * Kt * Real.exp (-L / Kt) + 2 * L * Real.exp (-L / Kt) := add_le_add hρbound hindbound
    _ = 2 * (L + Kt) * Real.exp (-L / Kt) := by ring
  /- @proof-region region.target-node.session.a21bba8101745e17 end -/

end Statlib.Imported

