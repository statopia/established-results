import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_bfd32cde8e43b4eecc52

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
theorem statopia_math_node_384144625_a59c7546 : ∀ (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus) (h_rhoMinus_le : rhoMinus ≤ 1)
    (rho : ℝ) (h_rho_lo : rhoMinus ≤ rho) (h_rho_hi : rho ≤ 1),
    (∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u) = 1 ∧
    (∀ t : ℝ, t ≤ mpLambdaMinus rho → mpTail rho t = 1) ∧
    (∀ x : ℝ, mpLambdaPlus rho ≤ x →
      (∫ u in (mpLambdaMinus rho)..x, rootedMPDensity rho u) = 1) := by
  /- @proof-region region.target-node.session.e39e7ba2491c65d6 begin -/
  intro rhoMinus h_rhoMinus_pos h_rhoMinus_le rho h_rho_lo h_rho_hi
  have hρlam : mpLambdaMinus rho ≤ mpLambdaPlus rho := by
    have h := Real.sqrt_nonneg rho
    unfold mpLambdaMinus mpLambdaPlus
    linarith
  have hleft : ∀ u : ℝ, u ≤ mpLambdaMinus rho → rootedMPDensity rho u = 0 := by
    intro u hu
    unfold rootedMPDensity
    by_cases hmem : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho
    · have h1 : mpLambdaMinus rho ≤ u := hmem.1
      have hueq : u = mpLambdaMinus rho := le_antisymm hu h1
      subst hueq
      simp [hρlam]
    · simp [hmem]
  have hright : ∀ u : ℝ, mpLambdaPlus rho ≤ u → rootedMPDensity rho u = 0 := by
    intro u hu
    unfold rootedMPDensity
    by_cases hmem : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho
    · have h2 : u ≤ mpLambdaPlus rho := hmem.2
      have hueq : u = mpLambdaPlus rho := le_antisymm h2 hu
      subst hueq
      simp [hρlam]
    · simp [hmem]
  have hrho_pos : 0 < rho := lt_of_lt_of_le h_rhoMinus_pos h_rho_lo
  have hsqrt_le_one : Real.sqrt rho ≤ 1 := by
    simpa using Real.sqrt_le_sqrt h_rho_hi
  have hlamnn : 0 ≤ mpLambdaMinus rho := by
    unfold mpLambdaMinus
    linarith
  have hAn : (0 : ℝ) ≤ mpLambdaMinus rho ^ 2 := sq_nonneg _
  have hBn : (0 : ℝ) ≤ mpLambdaPlus rho ^ 2 := sq_nonneg _
  have hAleB : mpLambdaMinus rho ^ 2 ≤ mpLambdaPlus rho ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hlamnn hρlam
  have hMnn : (0 : ℝ) ≤ 1 / Real.pi * Real.sqrt (mpLambdaPlus rho ^ 2) / rho := by positivity
  have hmeas : Measurable (rootedMPDensity rho) := by
    unfold rootedMPDensity
    have hp : Measurable fun x : ℝ =>
        (mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2) := by
      measurability
    have hs : Measurable fun x : ℝ =>
        Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) :=
      Real.continuous_sqrt.measurable.comp hp
    have hin : MeasurableSet {x : ℝ | mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho} :=
      (measurableSet_le measurable_const measurable_id).inter
        (measurableSet_le measurable_id measurable_const)
    have hif : Measurable fun x : ℝ =>
        (if mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho then (1 : ℝ) else 0) :=
      Measurable.ite hin measurable_const measurable_const
    exact ((measurable_const.mul hs).div (measurable_const.mul measurable_id)).mul hif
  have hbound : ∀ u : ℝ, |rootedMPDensity rho u|
      ≤ 1 / Real.pi * Real.sqrt (mpLambdaPlus rho ^ 2) / rho := by
    intro u
    have hsqrt_le :
        Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2))
          ≤ Real.sqrt (mpLambdaPlus rho ^ 2) * |u| := by
      have h4 : (mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)
          ≤ mpLambdaPlus rho ^ 2 * u ^ 2 := by
        by_cases hB' : 0 ≤ u ^ 2 - mpLambdaMinus rho ^ 2
        · have hA : mpLambdaPlus rho ^ 2 - u ^ 2 ≤ mpLambdaPlus rho ^ 2 := by
            linarith [sq_nonneg u]
          have hs1 : (mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)
              ≤ mpLambdaPlus rho ^ 2 * (u ^ 2 - mpLambdaMinus rho ^ 2) :=
            mul_le_mul_of_nonneg_right hA hB'
          have hs2 : mpLambdaPlus rho ^ 2 * (u ^ 2 - mpLambdaMinus rho ^ 2)
              ≤ mpLambdaPlus rho ^ 2 * u ^ 2 := by
            have hBA : (0 : ℝ) ≤ mpLambdaPlus rho ^ 2 * mpLambdaMinus rho ^ 2 := mul_nonneg hBn hAn
            nlinarith
          linarith
        · have hB'lt : u ^ 2 - mpLambdaMinus rho ^ 2 < 0 := not_le.mp hB'
          have hA : (0 : ℝ) ≤ mpLambdaPlus rho ^ 2 - u ^ 2 := by
            have h2 : u ^ 2 ≤ mpLambdaMinus rho ^ 2 := by linarith
            linarith
          have hs1 : (mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hA (le_of_lt hB'lt)
          have hBu : (0 : ℝ) ≤ mpLambdaPlus rho ^ 2 * u ^ 2 := mul_nonneg hBn (sq_nonneg u)
          linarith
      calc Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2))
          ≤ Real.sqrt (mpLambdaPlus rho ^ 2 * u ^ 2) := Real.sqrt_le_sqrt h4
        _ = Real.sqrt (mpLambdaPlus rho ^ 2) * |u| := by
            rw [Real.sqrt_mul hBn, Real.sqrt_sq_eq_abs u]
    have hπpos : (0 : ℝ) < 1 / Real.pi := by positivity
    rcases eq_or_ne u 0 with hu0 | hu0
    · subst hu0
      have hz : rootedMPDensity rho 0 = 0 := by
        unfold rootedMPDensity
        simp
      rw [hz, abs_zero]
      exact hMnn
    · by_cases hmem : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho
      · have key : |rootedMPDensity rho u| = (1 / Real.pi) *
            (Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2))
              / (rho * |u|)) := by
          unfold rootedMPDensity
          rw [if_pos hmem, mul_one, abs_div, abs_mul, abs_mul,
            abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
            abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hrho_pos]
          ring
        have hden : (0 : ℝ) ≤ (rho * |u|)⁻¹ := by positivity
        have hstep : Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2))
              / (rho * |u|) ≤ (Real.sqrt (mpLambdaPlus rho ^ 2) * |u|) / (rho * |u|) := by
          simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hsqrt_le hden
        have hstep2 : (1 / Real.pi) * ((Real.sqrt (mpLambdaPlus rho ^ 2) * |u|) / (rho * |u|))
            = 1 / Real.pi * Real.sqrt (mpLambdaPlus rho ^ 2) / rho := by
          rw [mul_div_mul_right _ _ (abs_ne_zero.mpr hu0)]
          ring
        rw [key]
        exact le_trans (mul_le_mul_of_nonneg_left hstep (le_of_lt hπpos)) (le_of_eq hstep2)
      · have hz : rootedMPDensity rho u = 0 := by
          unfold rootedMPDensity
          rw [if_neg hmem]
          simp
        rw [hz, abs_zero]
        exact hMnn
  have hIntOn : ∀ a b : ℝ, a ≤ b → IntegrableOn (rootedMPDensity rho) (Set.Ioc a b) volume := by
    intro a b hab
    have hgc : IntervalIntegrable (fun _ : ℝ => 1 / Real.pi * Real.sqrt (mpLambdaPlus rho ^ 2) / rho)
        volume a b := intervalIntegral.intervalIntegrable_const
    have hg : Integrable (fun _ : ℝ => 1 / Real.pi * Real.sqrt (mpLambdaPlus rho ^ 2) / rho)
        (volume.restrict (Set.Ioc a b)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hgc
    refine MeasureTheory.Integrable.mono hg ?_ ?_
    · exact hmeas.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · refine Filter.Eventually.of_forall (fun u => ?_)
      simpa only [Real.norm_eq_abs, abs_of_nonneg hMnn] using hbound u
  have hmass : (∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u) = 1 :=
    statopia_math_node_503473485_2877602c rho hrho_pos h_rho_hi
  refine ⟨hmass, ?_, ?_⟩
  · intro t ht
    have hzero : (∫ u in t..(mpLambdaMinus rho), rootedMPDensity rho u) = 0 := by
      have hcong : ∀ u ∈ Set.uIcc t (mpLambdaMinus rho), rootedMPDensity rho u = (0 : ℝ) := by
        intro u hu
        have hu' : u ≤ mpLambdaMinus rho := by
          rw [Set.uIcc_of_le ht] at hu
          exact hu.2
        exact hleft u hu'
      rw [intervalIntegral.integral_congr hcong]
      simp
    have hI1 : IntervalIntegrable (rootedMPDensity rho) volume t (mpLambdaMinus rho) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr (hIntOn t (mpLambdaMinus rho) ht)
    have hI2 : IntervalIntegrable (rootedMPDensity rho) volume (mpLambdaMinus rho) (mpLambdaPlus rho) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hρlam).mpr (hIntOn _ _ hρlam)
    have hadj : (∫ u in t..(mpLambdaMinus rho), rootedMPDensity rho u)
        + (∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u)
        = ∫ u in t..(mpLambdaPlus rho), rootedMPDensity rho u :=
      intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    unfold mpTail
    linarith
  · intro x hx
    have hzero : (∫ u in (mpLambdaPlus rho)..x, rootedMPDensity rho u) = 0 := by
      have hcong : ∀ u ∈ Set.uIcc (mpLambdaPlus rho) x, rootedMPDensity rho u = (0 : ℝ) := by
        intro u hu
        have hu' : mpLambdaPlus rho ≤ u := by
          rw [Set.uIcc_of_le hx] at hu
          exact hu.1
        exact hright u hu'
      rw [intervalIntegral.integral_congr hcong]
      simp
    have hI1 : IntervalIntegrable (rootedMPDensity rho) volume (mpLambdaMinus rho) (mpLambdaPlus rho) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hρlam).mpr (hIntOn _ _ hρlam)
    have hI2 : IntervalIntegrable (rootedMPDensity rho) volume (mpLambdaPlus rho) x :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr (hIntOn _ _ hx)
    have hadj : (∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u)
        + (∫ u in (mpLambdaPlus rho)..x, rootedMPDensity rho u)
        = ∫ u in (mpLambdaMinus rho)..x, rootedMPDensity rho u :=
      intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    linarith
  /- @proof-region region.target-node.session.e39e7ba2491c65d6 end -/

end Statlib.Imported

