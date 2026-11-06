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
theorem statopia_math_node_2383725196_b3e083bc : ∀ {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (Kt : ℝ) (hKt : 0 < Kt) (hX : Measurable X)
    (htail : ∀ t : ℝ, 0 < t →
      mu {omega | t < |X omega|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / Kt)))),
    Integrable (fun omega => |X omega| ^ 3) mu ∧
      (∫ omega, |X omega| ^ 3 ∂mu) ≤ 12 * Kt ^ 3 := by
  /- @proof-region region.target-node.session.f3a2c1ac25520385 begin -/
  intro Omega _ mu _ X Kt hKt hX htail
  have hint : ∀ a : ℝ, ∫ s in (0:ℝ)..a, 3 * s ^ 2 = a ^ 3 := by
    intro a
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) a, HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
      intro x _
      simpa using hasDerivAt_pow 3 x
    have hintble : IntervalIntegrable (fun s : ℝ => 3 * s ^ 2) volume (0:ℝ) a :=
      ((continuous_const : Continuous fun _ : ℝ => (3 : ℝ)).mul
        (continuous_id.pow 2)).intervalIntegrable 0 a
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintble
    simpa using hftc
  have hlayer : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ 3) ∂mu
      = ∫⁻ t in Set.Ioi (0:ℝ), mu {a | t < |X a|} * ENNReal.ofReal (3 * t ^ 2) := by
    have hcomp : ∫⁻ ω, ENNReal.ofReal (∫ s in (0:ℝ)..|X ω|, 3 * s ^ 2) ∂mu
        = ∫⁻ t in Set.Ioi (0:ℝ), mu {a | t < |X a|} * ENNReal.ofReal (3 * t ^ 2) :=
      MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul (μ := mu)
        (f := fun ω : Omega => |X ω|) (g := fun s : ℝ => 3 * s ^ 2)
        (Filter.Eventually.of_forall fun ω => abs_nonneg (X ω))
        hX.abs.aemeasurable
        (fun t _ => ((continuous_const : Continuous fun _ : ℝ => (3 : ℝ)).mul
          (continuous_id.pow 2)).intervalIntegrable 0 t)
        (Filter.Eventually.of_forall fun t => by positivity)
    rw [← hcomp]
    simp only [hint]
  have hbound : ∫⁻ t in Set.Ioi (0:ℝ), mu {a | t < |X a|} * ENNReal.ofReal (3 * t ^ 2)
      ≤ ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * t ^ 2 * Real.exp (-(t / Kt))) := by
    apply MeasureTheory.lintegral_mono_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    calc mu {a | t < |X a|} * ENNReal.ofReal (3 * t ^ 2)
        ≤ ENNReal.ofReal (2 * Real.exp (-(t / Kt))) * ENNReal.ofReal (3 * t ^ 2) :=
          mul_le_mul' (htail t ht) le_rfl
      _ = ENNReal.ofReal (6 * t ^ 2 * Real.exp (-(t / Kt))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hGauss_lint : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * t ^ 2 * Real.exp (-(t / Kt)))
      = ENNReal.ofReal (12 * Kt ^ 3) := by
    have hIntVal : ∫ t in Set.Ioi (0:ℝ), 6 * t ^ 2 * Real.exp (-(t / Kt)) = 12 * Kt ^ 3 := by
      have hkey : ∫ t in Set.Ioi (0:ℝ), 6 * t ^ 2 * Real.exp (-(1 / Kt) * t) = 12 * Kt ^ 3 := by
        have hderiv : ∀ x ∈ Set.Ici (0:ℝ),
            HasDerivAt (fun y : ℝ => ((-6) * Kt) * ((y + Kt) * (y + Kt) + Kt ^ 2) * Real.exp (-(1 / Kt) * y))
              (6 * x ^ 2 * Real.exp (-(1 / Kt) * x)) x := by
          intro x _
          have hb : HasDerivAt (fun y : ℝ => y + Kt) 1 x := by
            simpa using (hasDerivAt_id x).add_const Kt
          have hbb : HasDerivAt (fun y : ℝ => (y + Kt) * (y + Kt)) (1 * (x + Kt) + (x + Kt) * 1) x :=
            hb.mul hb
          have hP : HasDerivAt (fun y : ℝ => (y + Kt) * (y + Kt) + Kt ^ 2)
              (1 * (x + Kt) + (x + Kt) * 1) x :=
            hbb.add_const (Kt ^ 2)
          have hPc : HasDerivAt (fun y : ℝ => ((-6) * Kt) * ((y + Kt) * (y + Kt) + Kt ^ 2))
              (((-6) * Kt) * (1 * (x + Kt) + (x + Kt) * 1)) x :=
            hP.const_mul (((-6) * Kt))
          have hE : HasDerivAt (fun y : ℝ => Real.exp (-(1 / Kt) * y))
              (Real.exp (-(1 / Kt) * x) * (-(1 / Kt))) x := by
            have hlin : HasDerivAt (fun y : ℝ => -(1 / Kt) * y) (-(1 / Kt)) x := by
              simpa using (hasDerivAt_id x).const_mul (-(1 / Kt))
            exact hlin.exp
          have hprod := hPc.mul hE
          have hgoal : (((-6) * Kt) * (1 * (x + Kt) + (x + Kt) * 1)) * Real.exp (-(1 / Kt) * x)
              + (((-6) * Kt) * ((x + Kt) * (x + Kt) + Kt ^ 2)) * (Real.exp (-(1 / Kt) * x) * (-(1 / Kt)))
              = 6 * x ^ 2 * Real.exp (-(1 / Kt) * x) := by
            have hKtne : Kt ≠ 0 := ne_of_gt hKt
            field_simp
            ring
          rw [hgoal] at hprod
          exact hprod
        have hnonneg : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ 6 * x ^ 2 * Real.exp (-(1 / Kt) * x) := by
          intro x _
          positivity
        have hlim : Filter.Tendsto
            (fun y : ℝ => ((-6) * Kt) * ((y + Kt) * (y + Kt) + Kt ^ 2) * Real.exp (-(1 / Kt) * y))
            Filter.atTop (nhds 0) := by
          have h0 : Filter.Tendsto (fun x : ℝ => Real.exp (-(1 / Kt) * x)) Filter.atTop (nhds 0) := by
            simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / Kt) (by positivity)
          have h1 : Filter.Tendsto (fun x : ℝ => x * Real.exp (-(1 / Kt) * x)) Filter.atTop (nhds 0) := by
            simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / Kt) (by positivity)
          have h2 : Filter.Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-(1 / Kt) * x)) Filter.atTop (nhds 0) := by
            simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (1 / Kt) (by positivity)
          have hcomb : Filter.Tendsto (fun x : ℝ => -(6 * Kt) * (x ^ 2 * Real.exp (-(1 / Kt) * x))
              - (12 * Kt ^ 2) * (x * Real.exp (-(1 / Kt) * x))
              - (12 * Kt ^ 3) * Real.exp (-(1 / Kt) * x)) Filter.atTop (nhds 0) := by
            have h := ((h2.const_mul (-(6 * Kt))).sub (h1.const_mul (12 * Kt ^ 2))).sub
              (h0.const_mul (12 * Kt ^ 3))
            simpa using h
          have heq : (fun y : ℝ => ((-6) * Kt) * ((y + Kt) * (y + Kt) + Kt ^ 2) * Real.exp (-(1 / Kt) * y))
              = fun x : ℝ => -(6 * Kt) * (x ^ 2 * Real.exp (-(1 / Kt) * x))
                - (12 * Kt ^ 2) * (x * Real.exp (-(1 / Kt) * x))
                - (12 * Kt ^ 3) * Real.exp (-(1 / Kt) * x) := by
            funext y
            ring
          rw [heq]
          exact hcomb
        have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
          (g := fun y : ℝ => ((-6) * Kt) * ((y + Kt) * (y + Kt) + Kt ^ 2) * Real.exp (-(1 / Kt) * y))
          (g' := fun x : ℝ => 6 * x ^ 2 * Real.exp (-(1 / Kt) * x))
          (a := (0:ℝ)) (l := (0:ℝ)) hderiv hnonneg hlim
        rw [hFTC]
        have hg0 : (fun y : ℝ => ((-6) * Kt) * ((y + Kt) * (y + Kt) + Kt ^ 2) * Real.exp (-(1 / Kt) * y)) 0
            = -12 * Kt ^ 3 := by
          simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, mul_one]
          ring
        rw [hg0]
        ring
      have hfun : (fun t : ℝ => 6 * t ^ 2 * Real.exp (-(t / Kt)))
          = fun t : ℝ => 6 * t ^ 2 * Real.exp (-(1 / Kt) * t) := by
        funext t
        have harg : -(t / Kt) = -(1 / Kt) * t := by
          rw [one_div, div_eq_mul_inv]
          ring
        rw [harg]
      rw [hfun]
      exact hkey
    have hcont : Continuous fun t : ℝ => 6 * t ^ 2 * Real.exp (-(t / Kt)) := by fun_prop
    have hIntEq : ∫ t in Set.Ioi (0:ℝ), 6 * t ^ 2 * Real.exp (-(t / Kt))
        = (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * t ^ 2 * Real.exp (-(t / Kt)))).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (Set.Ioi (0:ℝ)))
        (f := fun t : ℝ => 6 * t ^ 2 * Real.exp (-(t / Kt)))
        (Filter.Eventually.of_forall fun t => by positivity) hcont.measurable.aestronglyMeasurable
    rw [hIntVal] at hIntEq
    have hne : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * t ^ 2 * Real.exp (-(t / Kt)))) ≠ ⊤ := by
      intro htop
      rw [htop] at hIntEq
      simp only [ENNReal.toReal_top] at hIntEq
      have hpos : (0:ℝ) < 12 * Kt ^ 3 := by positivity
      linarith
    have h1 : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * t ^ 2 * Real.exp (-(t / Kt)))
        = ENNReal.ofReal ((∫⁻ t in Set.Ioi (0:ℝ),
            ENNReal.ofReal (6 * t ^ 2 * Real.exp (-(t / Kt)))).toReal) :=
      (ENNReal.ofReal_toReal hne).symm
    have h2 : ENNReal.ofReal ((∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal (6 * t ^ 2 * Real.exp (-(t / Kt)))).toReal)
        = ENNReal.ofReal (12 * Kt ^ 3) := by
      rw [← hIntEq]
    exact h1.trans h2
  have hlin : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ 3) ∂mu ≤ ENNReal.ofReal (12 * Kt ^ 3) := by
    rw [hlayer]
    exact le_trans hbound (le_of_eq hGauss_lint)
  have hmeas : AEStronglyMeasurable (fun ω : Omega => |X ω| ^ 3) mu :=
    (hX.abs.pow_const 3).aestronglyMeasurable
  have hfin : HasFiniteIntegral (fun ω : Omega => |X ω| ^ 3) mu := by
    refine (MeasureTheory.hasFiniteIntegral_iff_ofReal (μ := mu)
      (Filter.Eventually.of_forall fun ω => by positivity)).mpr ?_
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  constructor
  · exact ⟨hmeas, hfin⟩
  · have hI : ∫ ω, |X ω| ^ 3 ∂mu = (∫⁻ ω, ENNReal.ofReal (|X ω| ^ 3) ∂mu).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω => by positivity) hmeas
    calc ∫ ω, |X ω| ^ 3 ∂mu = (∫⁻ ω, ENNReal.ofReal (|X ω| ^ 3) ∂mu).toReal := hI
      _ ≤ (ENNReal.ofReal (12 * Kt ^ 3)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
      _ = 12 * Kt ^ 3 := ENNReal.toReal_ofReal (by positivity)
  /- @proof-region region.target-node.session.f3a2c1ac25520385 end -/

end Statlib.Imported

