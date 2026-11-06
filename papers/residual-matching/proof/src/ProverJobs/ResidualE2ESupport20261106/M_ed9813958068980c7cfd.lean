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
theorem statopia_math_node_431073706_88ea41c7 : (∫ u in (0 : ℝ)..2, Real.sqrt ((4 - u ^ 2) * u ^ 2) / u) = Real.pi := by
  /- @proof-region region.target-node.session.9374e783e77d8308 begin -/
  have step1 : ∫ u in (0:ℝ)..2, Real.sqrt ((4 - u ^ 2) * u ^ 2) / u = ∫ u in (0:ℝ)..2, Real.sqrt (4 - u ^ 2) := by
    simp only [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 2 by norm_num)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
    intro x hx
    obtain ⟨hx0, hx2⟩ := hx
    have h4 : (0:ℝ) ≤ 4 - x ^ 2 := by nlinarith
    have hxne : x ≠ 0 := ne_of_gt hx0
    change Real.sqrt ((4 - x ^ 2) * x ^ 2) / x = Real.sqrt (4 - x ^ 2)
    rw [Real.sqrt_mul h4, Real.sqrt_sq (le_of_lt hx0)]
    field_simp
  have step2 : ∫ u in (0:ℝ)..2, Real.sqrt (4 - u ^ 2) = ∫ θ in (0:ℝ)..(Real.pi / 2), Real.sqrt (4 - (2 * Real.sin θ) ^ 2) * (2 * Real.cos θ) := by
    have h := intervalIntegral.integral_comp_mul_deriv
      (a := (0:ℝ)) (b := Real.pi / 2)
      (f := fun θ : ℝ => 2 * Real.sin θ) (f' := fun θ : ℝ => 2 * Real.cos θ)
      (g := fun y : ℝ => Real.sqrt (4 - y ^ 2))
      (fun x _ => (Real.hasDerivAt_sin x).const_mul 2)
      ((continuous_const.mul Real.continuous_cos).continuousOn)
      (by continuity)
    simpa [Function.comp, Real.sin_zero, Real.sin_pi_div_two] using h.symm
  have step3 : ∫ θ in (0:ℝ)..(Real.pi / 2), Real.sqrt (4 - (2 * Real.sin θ) ^ 2) * (2 * Real.cos θ) = Real.pi := by
    have hcongr : ∫ θ in (0:ℝ)..(Real.pi / 2), Real.sqrt (4 - (2 * Real.sin θ) ^ 2) * (2 * Real.cos θ)
        = ∫ θ in (0:ℝ)..(Real.pi / 2), (2 + 2 * Real.cos (2 * θ)) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hmem : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
        exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc hmem
      change Real.sqrt (4 - (2 * Real.sin θ) ^ 2) * (2 * Real.cos θ) = 2 + 2 * Real.cos (2 * θ)
      have hsq : 4 - (2 * Real.sin θ) ^ 2 = (2 * Real.cos θ) ^ 2 := by
        rw [show (2 * Real.sin θ) ^ 2 = 4 * Real.sin θ ^ 2 by ring,
          show (2 * Real.cos θ) ^ 2 = 4 * Real.cos θ ^ 2 by ring]
        linarith [Real.sin_sq_add_cos_sq θ]
      rw [hsq, Real.sqrt_sq (by linarith : (0:ℝ) ≤ 2 * Real.cos θ), Real.cos_two_mul θ]
      ring
    refine hcongr.trans ?_
    have hd : ∀ x ∈ Set.uIcc (0:ℝ) (Real.pi / 2),
        HasDerivAt (fun θ : ℝ => 2 * θ + Real.sin (2 * θ)) (2 + 2 * Real.cos (2 * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 x := by
        simpa using (hasDerivAt_id (x : ℝ)).const_mul (2:ℝ)
      have h2 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.cos (2 * x) * 2) x := h1.sin
      have h3 : HasDerivAt (fun θ : ℝ => 2 * θ + Real.sin (2 * θ)) (2 + Real.cos (2 * x) * 2) x :=
        h1.add h2
      convert h3 using 1
      ring
    have hi : IntervalIntegrable (fun θ : ℝ => 2 + 2 * Real.cos (2 * θ)) volume (0:ℝ) (Real.pi / 2) := by
      apply Continuous.intervalIntegrable
      exact (continuous_const : Continuous fun _ : ℝ => (2:ℝ)).add
        ((continuous_const : Continuous fun _ : ℝ => (2:ℝ)).mul
          (Real.continuous_cos.comp ((continuous_const : Continuous fun _ : ℝ => (2:ℝ)).mul continuous_id)))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
    show 2 * (Real.pi / 2) + Real.sin (2 * (Real.pi / 2)) - (2 * 0 + Real.sin (2 * 0)) = Real.pi
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    simp
  exact step1.trans (step2.trans step3)
  /- @proof-region region.target-node.session.9374e783e77d8308 end -/

end Statlib.Imported

