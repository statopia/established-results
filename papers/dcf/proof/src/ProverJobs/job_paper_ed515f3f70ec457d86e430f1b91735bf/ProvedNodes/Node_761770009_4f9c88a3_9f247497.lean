import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1071239738_ed21f8b0_7ef4fb93

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_761770009_4f9c88a3 : ∀ (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (hbeta : 0 < beta) (y : Fin p → ℝ),
    let F : (Fin p → ℝ) → ℝ :=
      fun w => beta⁻¹ * Real.log (∑ q : Fin p, Real.exp (beta * (w q - y q)));
      (∀ w, HasFDerivAt F (fderiv ℝ F w) w) ∧
        (∀ w, ‖fderiv ℝ F w‖ ≤ 1) ∧
        (∀ w, HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) w) w) ∧
        (∀ w, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ 2 * beta) := by
  /- @proof-region region.target-node.session.5cef60784ca94dc4 begin -/
  intro p hp beta hbeta y
  have hne : (Finset.univ : Finset (Fin p)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hS_pos : ∀ w : Fin p → ℝ, 0 < ∑ q : Fin p, Real.exp (beta * (w q - y q)) := by
    intro w
    exact Finset.sum_pos (fun q _ => Real.exp_pos _) hne
  have he_deriv : ∀ (q : Fin p) (w : Fin p → ℝ),
      HasFDerivAt (fun w : Fin p → ℝ => Real.exp (beta * (w q - y q)))
        (Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)) w := by
    intro q w
    have h1 : HasFDerivAt (fun w : Fin p → ℝ => w q) (ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ) w := by
      simpa using (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ) (x := w))
    have h2 : HasFDerivAt (fun w : Fin p → ℝ => beta * (w q - y q))
        (beta • ContinuousLinearMap.proj q) w :=
      (h1.sub_const (y q)).const_mul beta
    have h3 := HasDerivAt.comp_hasFDerivAt (x := w)
      (Real.hasDerivAt_exp (beta * (w q - y q))) h2
    simpa [Function.comp] using h3
  let S : (Fin p → ℝ) → ℝ := fun w => ∑ q : Fin p, Real.exp (beta * (w q - y q))
  let dS : (Fin p → ℝ) → ((Fin p → ℝ) →L[ℝ] ℝ) :=
    fun w => ∑ q : Fin p, Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)
  let dS2 : (Fin p → ℝ) → ((Fin p → ℝ) →L[ℝ] ((Fin p → ℝ) →L[ℝ] ℝ)) :=
    fun w => ∑ q : Fin p,
      (Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)).smulRight
        (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)
  let F : (Fin p → ℝ) → ℝ := fun w => beta⁻¹ * Real.log (S w)
  change (∀ w, HasFDerivAt F (fderiv ℝ F w) w) ∧ (∀ w, ‖fderiv ℝ F w‖ ≤ 1) ∧
    (∀ w, HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) w) w) ∧
    (∀ w, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ 2 * beta)
  have key : ∀ (t : Finset (Fin p)) (w : Fin p → ℝ),
      HasFDerivAt (fun w : Fin p → ℝ => ∑ q ∈ t, Real.exp (beta * (w q - y q)))
        (∑ q ∈ t, Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)) w := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro w
      simpa using (ContinuousLinearMap.hasFDerivAt (0 : (Fin p → ℝ) →L[ℝ] ℝ) (x := w))
    · intro a s ha ih w
      simpa [Finset.sum_insert ha] using (he_deriv a w).add (ih w)
  have hS_deriv : ∀ w, HasFDerivAt S (dS w) w := fun w => by
    simpa only [S, dS] using key Finset.univ w
  have hS_ne : ∀ w, S w ≠ 0 := fun w => ne_of_gt (hS_pos w)
  have hlog_deriv : ∀ w, HasFDerivAt (fun w => Real.log (S w)) ((S w)⁻¹ • dS w) w := by
    intro w
    exact (hS_deriv w).log (hS_ne w)
  let dF : (Fin p → ℝ) → ((Fin p → ℝ) →L[ℝ] ℝ) := fun w => beta⁻¹ • ((S w)⁻¹ • dS w)
  have hF_deriv : ∀ w, HasFDerivAt F (dF w) w := by
    intro w
    simpa only [F, dF, smul_eq_mul, Pi.smul_apply] using (hlog_deriv w).const_smul (beta⁻¹)
  have hF_fderiv : ∀ w, fderiv ℝ F w = dF w := fun w => (hF_deriv w).fderiv
  have hproj : ∀ q : Fin p, ‖(ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
    intro q
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro u
    simpa using norm_le_pi_norm u q
  have hS_bound : ∀ w, ‖dS w‖ ≤ beta * S w := by
    intro w
    have hM : (0 : ℝ) ≤ beta * S w := by
      have h : 0 < beta * S w := mul_pos hbeta (by simpa [S] using hS_pos w)
      linarith
    refine ContinuousLinearMap.opNorm_le_bound (dS w) hM ?_
    intro u
    have happ : (dS w) u = ∑ q : Fin p, Real.exp (beta * (w q - y q)) * (beta * u q) := by
      simp only [dS, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [happ]
    have hb1 : ∀ q : Fin p,
        ‖Real.exp (beta * (w q - y q)) * (beta * u q)‖
          ≤ Real.exp (beta * (w q - y q)) * beta * ‖u‖ := by
      intro q
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hbeta]
      have hu : |u q| ≤ ‖u‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm u q
      calc Real.exp (beta * (w q - y q)) * (beta * |u q|)
          ≤ Real.exp (beta * (w q - y q)) * (beta * ‖u‖) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
              exact mul_le_mul_of_nonneg_left hu (le_of_lt hbeta)
        _ = Real.exp (beta * (w q - y q)) * beta * ‖u‖ := by ring
    calc ‖∑ q : Fin p, Real.exp (beta * (w q - y q)) * (beta * u q)‖
        ≤ ∑ q : Fin p, ‖Real.exp (beta * (w q - y q)) * (beta * u q)‖ := norm_sum_le _ _
      _ ≤ ∑ q : Fin p, Real.exp (beta * (w q - y q)) * beta * ‖u‖ := Finset.sum_le_sum (fun q _ => hb1 q)
      _ = (∑ q : Fin p, Real.exp (beta * (w q - y q)) * beta) * ‖u‖ := by rw [Finset.sum_mul]
      _ = beta * S w * ‖u‖ := by
            rw [← Finset.sum_mul]
            have hSe : (∑ q : Fin p, Real.exp (beta * (w q - y q))) = S w := rfl
            rw [hSe, mul_comm (S w) beta]
  have hF1 : ∀ w, ‖fderiv ℝ F w‖ ≤ 1 := by
    intro w
    rw [hF_fderiv w]
    have hbpos : (0 : ℝ) < beta⁻¹ := inv_pos.mpr hbeta
    have hSp : (0 : ℝ) < S w := by simpa [S] using hS_pos w
    have hSin : (0 : ℝ) < (S w)⁻¹ := inv_pos.mpr hSp
    have hnorm : ‖dF w‖ = beta⁻¹ * ((S w)⁻¹ * ‖dS w‖) := by
      show ‖beta⁻¹ • ((S w)⁻¹ • dS w)‖ = beta⁻¹ * ((S w)⁻¹ * ‖dS w‖)
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hbpos, abs_of_pos hSin]
    rw [hnorm]
    have h1 : beta⁻¹ * ((S w)⁻¹ * ‖dS w‖) ≤ beta⁻¹ * ((S w)⁻¹ * (beta * S w)) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hbpos)
      exact mul_le_mul_of_nonneg_left (hS_bound w) (le_of_lt hSin)
    have hsimp : (S w)⁻¹ * (beta * S w) = beta := by
      rw [mul_comm beta (S w), ← mul_assoc, inv_mul_cancel₀ (hS_ne w), one_mul]
    have h2 : beta⁻¹ * ((S w)⁻¹ * (beta * S w)) = 1 := by
      rw [hsimp, inv_mul_cancel₀ (ne_of_gt hbeta)]
    calc beta⁻¹ * ((S w)⁻¹ * ‖dS w‖)
        ≤ beta⁻¹ * ((S w)⁻¹ * (beta * S w)) := h1
      _ = 1 := h2
  have hterm2 : ∀ (q : Fin p) (w : Fin p → ℝ),
      HasFDerivAt
        (fun w : Fin p → ℝ => Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ))
        ((Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)).smulRight
          (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)) w := by
    intro q w
    exact (he_deriv q w).smul_const (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)
  have key2 : ∀ (t : Finset (Fin p)) (w : Fin p → ℝ),
      HasFDerivAt
        (fun w : Fin p → ℝ => ∑ q ∈ t, Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ))
        (∑ q ∈ t, (Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)).smulRight
          (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)) w := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro w
      simpa using (ContinuousLinearMap.hasFDerivAt (0 : (Fin p → ℝ) →L[ℝ] ((Fin p → ℝ) →L[ℝ] ℝ)) (x := w))
    · intro a s ha ih w
      simpa [Finset.sum_insert ha] using (hterm2 a w).add (ih w)
  have hdS2_deriv : ∀ w, HasFDerivAt dS (dS2 w) w := fun w => by
    simpa only [dS, dS2] using key2 Finset.univ w
  have hLnorm : ∀ q : Fin p, ‖(beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)‖ ≤ beta := by
    intro q
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hbeta]
    calc beta * ‖(ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)‖ ≤ beta * 1 := by
          apply mul_le_mul_of_nonneg_left (hproj q) (le_of_lt hbeta)
      _ = beta := by ring
  have hS2_bound : ∀ w, ‖dS2 w‖ ≤ beta ^ 2 * S w := by
    intro w
    have hterm : ∀ q : Fin p,
        ‖(Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)).smulRight
            (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)‖
          ≤ Real.exp (beta * (w q - y q)) * beta ^ 2 := by
      intro q
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (beta * (w q - y q)) * ‖(beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)‖
              * ‖(beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)‖
          ≤ Real.exp (beta * (w q - y q)) * beta * beta := by
              apply mul_le_mul _ (hLnorm q) (norm_nonneg _) _
              · exact mul_le_mul_of_nonneg_left (hLnorm q) (le_of_lt (Real.exp_pos _))
              · exact mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt hbeta)
        _ = Real.exp (beta * (w q - y q)) * beta ^ 2 := by ring
    have hstep1 : ‖dS2 w‖ ≤ ∑ q : Fin p,
        ‖(Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)).smulRight
            (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)‖ := by
      rw [show dS2 w = ∑ q : Fin p,
        (Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)).smulRight
          (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ) from rfl]
      exact norm_sum_le Finset.univ (fun q =>
        (Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)).smulRight
          (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ))
    calc ‖dS2 w‖ ≤ ∑ q : Fin p,
        ‖(Real.exp (beta * (w q - y q)) • (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)).smulRight
            (beta • ContinuousLinearMap.proj q : (Fin p → ℝ) →L[ℝ] ℝ)‖ := hstep1
      _ ≤ ∑ q : Fin p, Real.exp (beta * (w q - y q)) * beta ^ 2 := Finset.sum_le_sum (fun q _ => hterm q)
      _ = (∑ q : Fin p, Real.exp (beta * (w q - y q))) * beta ^ 2 := by rw [Finset.sum_mul]
      _ = beta ^ 2 * S w := by
            rw [show (∑ q : Fin p, Real.exp (beta * (w q - y q))) = S w from rfl, mul_comm (S w) (beta ^ 2)]
  have hA_deriv : ∀ w, HasFDerivAt (fun w => (S w)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)) w := by
    intro w
    simpa using HasFDerivAt.comp w (hasFDerivAt_inv (hS_ne w)) (hS_deriv w)
  have hN_deriv : ∀ w, HasFDerivAt (fun w => (S w)⁻¹ • dS w)
      ((S w)⁻¹ • dS2 w + ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)).smulRight (dS w)) w := by
    intro w
    exact HasFDerivAt.smul (hA_deriv w) (hdS2_deriv w)
  let dF2 : (Fin p → ℝ) → ((Fin p → ℝ) →L[ℝ] ((Fin p → ℝ) →L[ℝ] ℝ)) :=
    fun w => beta⁻¹ • ((S w)⁻¹ • dS2 w + ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)).smulRight (dS w))
  have hdF2_deriv : ∀ w, HasFDerivAt dF (dF2 w) w := by
    intro w
    have h := (hN_deriv w).const_smul (beta⁻¹)
    simpa only [dF, dF2, Pi.smul_apply] using h
  have hfderiv2 : ∀ w, fderiv ℝ dF w = dF2 w := fun w => (hdF2_deriv w).fderiv
  refine ⟨?_, hF1, ?_, ?_⟩
  · intro w
    rw [hF_fderiv w]
    exact hF_deriv w
  · intro w
    rw [show fderiv ℝ F = dF from funext hF_fderiv, hfderiv2 w]
    exact hdF2_deriv w
  · intro w
    rw [show fderiv ℝ F = dF from funext hF_fderiv, hfderiv2 w]
    exact statopia_math_node_1071239738_ed21f8b0 p beta S dS dS2 hbeta hS_pos hS_bound hS2_bound w
  /- @proof-region region.target-node.session.5cef60784ca94dc4 end -/

end

end Statlib.Imported

