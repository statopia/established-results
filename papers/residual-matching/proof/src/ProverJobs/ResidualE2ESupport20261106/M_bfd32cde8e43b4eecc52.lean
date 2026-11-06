import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_a3eac809b2fd830d0330
import ProverJobs.ResidualE2ESupport20261106.M_ed9813958068980c7cfd

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
theorem statopia_math_node_503473485_2877602c : ∀ (rho : ℝ) (h_pos : 0 < rho) (h_le : rho ≤ 1),
    (∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u) = 1 := by
  /- @proof-region region.target-node.session.3f96eec08f7d457a begin -/
  intro rho h_pos h_le
  have hs0 : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hs1 : Real.sqrt rho ≤ 1 := by
    simpa using Real.sqrt_le_sqrt h_le
  have hlam : mpLambdaMinus rho ≤ mpLambdaPlus rho := by
    simp only [mpLambdaMinus, mpLambdaPlus]
    linarith
  have hstep1 :
      (∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u)
        = ∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho),
            ((1 / Real.pi) *
                Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) /
              (rho * u)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho := by
      rwa [Set.uIcc_of_le hlam] at hx
    simp only [rootedMPDensity, if_pos hx', mul_one]
  rw [hstep1]
  have hlamM : 0 ≤ mpLambdaMinus rho := by
    simp only [mpLambdaMinus]
    linarith
  have hlamP : 0 ≤ mpLambdaPlus rho := by
    simp only [mpLambdaPlus]
    linarith
  rcases lt_or_eq_of_le h_le with hlt | heq
  · have hkey :=
      statopia_math_node_341608398_1b1c7b47 (mpLambdaMinus rho ^ 2) (mpLambdaPlus rho ^ 2)
        (by
          have hs2 : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt (le_of_lt h_pos)
          have hsr : Real.sqrt rho < 1 := by nlinarith [hs2, hs0]
          have hposM : 0 < mpLambdaMinus rho := by
            simp only [mpLambdaMinus]
            linarith
          exact pow_pos hposM 2)
        (by
          have h1 : 0 ≤ mpLambdaPlus rho - mpLambdaMinus rho := by linarith
          have h2 : 0 ≤ mpLambdaPlus rho + mpLambdaMinus rho := by linarith
          nlinarith [mul_nonneg h1 h2])
    rw [Real.sqrt_sq hlamM, Real.sqrt_sq hlamP] at hkey
    have hfac :
        (∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho),
            ((1 / Real.pi) *
                Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) /
              (rho * u)))
          = (1 / (Real.pi * rho)) *
              ∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho),
                Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / u := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hfac, hkey]
    have hs_sq : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt (le_of_lt h_pos)
    have hsum : (mpLambdaMinus rho ^ 2 + mpLambdaPlus rho ^ 2) / 2 = 1 + rho := by
      simp only [mpLambdaMinus, mpLambdaPlus]
      nlinarith [hs_sq]
    have hprod : Real.sqrt (mpLambdaMinus rho ^ 2 * mpLambdaPlus rho ^ 2) = 1 - rho := by
      have hmul : mpLambdaMinus rho * mpLambdaPlus rho = 1 - rho := by
        simp only [mpLambdaMinus, mpLambdaPlus]
        nlinarith [hs_sq]
      calc Real.sqrt (mpLambdaMinus rho ^ 2 * mpLambdaPlus rho ^ 2)
          = Real.sqrt ((mpLambdaMinus rho * mpLambdaPlus rho) ^ 2) := by ring_nf
        _ = mpLambdaMinus rho * mpLambdaPlus rho := Real.sqrt_sq (by positivity)
        _ = 1 - rho := hmul
    rw [hsum, hprod]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hrne : rho ≠ 0 := ne_of_gt h_pos
    field_simp
    try ring
  · subst heq
    have h0 : mpLambdaMinus 1 = 0 := by simp [mpLambdaMinus]
    have h2 : mpLambdaPlus 1 = 2 := by
      simp [mpLambdaPlus]
      norm_num
    rw [h0, h2]
    have hquarter :
        (∫ u in (0 : ℝ)..2, Real.sqrt ((4 - u ^ 2) * u ^ 2) / u) = Real.pi :=
      statopia_math_node_431073706_88ea41c7
    have hfac :
        (∫ u in (0 : ℝ)..2,
            ((1 / Real.pi) * Real.sqrt ((2 ^ 2 - u ^ 2) * (u ^ 2 - (0 : ℝ) ^ 2)) / (1 * u)))
          = (1 / Real.pi) * ∫ u in (0 : ℝ)..2, Real.sqrt ((4 - u ^ 2) * u ^ 2) / u := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      have e1 : (2 : ℝ) ^ 2 - x ^ 2 = 4 - x ^ 2 := by ring
      have e2 : x ^ 2 - (0 : ℝ) ^ 2 = x ^ 2 := by ring
      simp only [e1, e2, one_mul]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hfac, hquarter]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    try ring
  /- @proof-region region.target-node.session.3f96eec08f7d457a end -/

end Statlib.Imported

