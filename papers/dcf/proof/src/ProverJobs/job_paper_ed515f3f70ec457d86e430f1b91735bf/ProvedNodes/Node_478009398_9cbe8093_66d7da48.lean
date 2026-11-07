import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

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
theorem statopia_math_node_478009398_9cbe8093 : ∀ (p : ℕ) (hp : 0 < p)
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (phi beta : ℝ) (hphi : 1 ≤ phi) (hbeta : 0 ≤ beta) (y : Fin p → ℝ),
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ w : Fin p → ℝ,
        ‖fderiv ℝ (fun w : Fin p → ℝ =>
          phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))) w‖ ≤ M) ∧
      Continuous (fderiv ℝ (fun w : Fin p → ℝ =>
        phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j))))))) := by
  /- @proof-region region.target-node.session.ec024bb72ac806a7 begin -/
  intro p hp phi0 hphi0_cont hphi0_left hphi0_right phi beta hphi hbeta y
  haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  let S : (Fin p → ℝ) → ℝ := fun w => ∑ j : Fin p, Real.exp (beta * (w j - y j))
  let s : (Fin p → ℝ) → ℝ := fun w => phi * (beta⁻¹ * Real.log (S w))
  show ∃ M : ℝ, 0 ≤ M ∧
      (∀ w : Fin p → ℝ, ‖fderiv ℝ (fun w : Fin p → ℝ => phi0 (s w)) w‖ ≤ M) ∧
      Continuous (fderiv ℝ (fun w : Fin p → ℝ => phi0 (s w)))
  have hSpos : ∀ w : Fin p → ℝ, 0 < S w := by
    intro w
    show 0 < ∑ j : Fin p, Real.exp (beta * (w j - y j))
    exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hphi0_diff : Differentiable ℝ phi0 := hphi0_cont.differentiable (by norm_num)
  have hfderiv_cont : Continuous (fderiv ℝ phi0) := hphi0_cont.continuous_fderiv (by norm_num)
  have hvan : ∀ z : ℝ, (z < 0 ∨ 1 < z) → fderiv ℝ phi0 z = 0 := by
    intro z hz
    rcases hz with hz | hz
    · have hmem : {x : ℝ | phi0 x = (1 : ℝ)} ∈ nhds z :=
        Filter.mem_of_superset (isOpen_Iio.mem_nhds hz) (fun x hx => hphi0_left x (le_of_lt hx))
      exact ((hasFDerivAt_const (1 : ℝ) z).congr_of_eventuallyEq hmem).fderiv
    · have hmem : {x : ℝ | phi0 x = (0 : ℝ)} ∈ nhds z :=
        Filter.mem_of_superset (isOpen_Ioi.mem_nhds hz) (fun x hx => hphi0_right x (le_of_lt hx))
      exact ((hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq hmem).fderiv
  have hbound0 : ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ z : ℝ, ‖fderiv ℝ phi0 z‖ ≤ M0 := by
    have hcontn : Continuous (fun z : ℝ => ‖fderiv ℝ phi0 z‖) := hfderiv_cont.norm
    obtain ⟨z0, _, hz0max⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_isMaxOn
        ⟨(0 : ℝ), le_refl 0, by norm_num⟩ (fun x _ => hcontn.continuousAt.continuousWithinAt)
    refine ⟨‖fderiv ℝ phi0 z0‖, norm_nonneg _, fun z => ?_⟩
    by_cases hmem : z ∈ Set.Icc (0 : ℝ) 1
    · exact hz0max hmem
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
      rw [hvan z hmem]
      simpa using norm_nonneg (fderiv ℝ phi0 z0)
  obtain ⟨M0, hM0nn, hM0bound⟩ := hbound0
  let T : (Fin p → ℝ) → ((Fin p → ℝ) →L[ℝ] ℝ) :=
    fun w => ∑ j : Fin p, Real.exp (beta * (w j - y j)) • (beta • ContinuousLinearMap.proj j)
  have hproj_bound : ∀ j : Fin p,
      ‖(beta • ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ)‖ ≤ beta := by
    intro j
    refine ContinuousLinearMap.opNorm_le_bound
      (beta • (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ)) hbeta (fun x => ?_)
    have h1 : (beta • (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ)) x = beta * x j := by
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [h1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hbeta]
    have h2 : |x j| ≤ ‖x‖ := by simpa using norm_le_pi_norm x j
    exact mul_le_mul_of_nonneg_left h2 hbeta
  have hderivS : ∀ w : Fin p → ℝ, HasFDerivAt S (T w) w := by
    intro w
    have h : ∀ j : Fin p, HasFDerivAt (fun w : Fin p → ℝ => Real.exp (beta * (w j - y j)))
        (Real.exp (beta * (w j - y j)) •
          (beta • (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ))) w := by
      intro j
      have hlin : HasFDerivAt
          (fun w : Fin p → ℝ => (beta • (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ)) w)
          (beta • (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ)) w :=
        ContinuousLinearMap.hasFDerivAt (beta • (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ))
      have hB : HasFDerivAt (fun w : Fin p → ℝ => beta * (w j - y j))
          (beta • (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ)) w := by
        have := hlin.sub_const (beta * y j)
        simpa [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
          mul_sub] using this
      exact hB.exp
    have hsum := HasFDerivAt.sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin p))) => h j)
    have hfun : (∑ i : Fin p, fun w : Fin p → ℝ => Real.exp (beta * (w i - y i)))
        = fun w : Fin p → ℝ => ∑ i : Fin p, Real.exp (beta * (w i - y i)) := by
      funext w
      simp only [Finset.sum_apply]
    rw [hfun] at hsum
    exact hsum
  have hderivs : ∀ w : Fin p → ℝ, HasFDerivAt s (phi • (beta⁻¹ • ((S w)⁻¹ • T w))) w := by
    intro w
    have h1 : HasFDerivAt (fun w : Fin p → ℝ => Real.log (S w)) ((S w)⁻¹ • T w) w :=
      (hderivS w).log (ne_of_gt (hSpos w))
    exact (h1.const_mul beta⁻¹).const_mul phi
  have hs_cont : Continuous s := continuous_iff_continuousAt.mpr (fun w => (hderivs w).continuousAt)
  have hTsum : ∀ w : Fin p → ℝ, ‖T w‖ ≤ S w * beta := by
    intro w
    have h1 : ‖T w‖ ≤
        ∑ j : Fin p, ‖Real.exp (beta * (w j - y j)) • (beta • ContinuousLinearMap.proj j)‖ :=
      norm_sum_le Finset.univ _
    have h2 : ∑ j : Fin p,
        ‖Real.exp (beta * (w j - y j)) •
          (beta • (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ))‖ ≤ S w * beta := by
      calc ∑ j : Fin p,
            ‖Real.exp (beta * (w j - y j)) •
              (beta • (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ))‖
          ≤ ∑ j : Fin p, Real.exp (beta * (w j - y j)) * beta := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_left (hproj_bound j) (le_of_lt (Real.exp_pos _))
        _ = S w * beta := by rw [Finset.sum_mul]
    exact le_trans h1 h2
  have hinvT : ∀ w : Fin p → ℝ, ‖(S w)⁻¹ • T w‖ ≤ beta := by
    intro w
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hSpos w))]
    calc (S w)⁻¹ * ‖T w‖ ≤ (S w)⁻¹ * (S w * beta) :=
          mul_le_mul_of_nonneg_left (hTsum w) (le_of_lt (inv_pos.mpr (hSpos w)))
      _ = beta := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hSpos w)), one_mul]
  have hinner : ∀ w : Fin p → ℝ, ‖(S w)⁻¹‖ * ‖T w‖ ≤ beta := by
    intro w
    rw [← norm_smul]
    exact hinvT w
  have hbound_s : ∀ w : Fin p → ℝ, ‖fderiv ℝ s w‖ ≤ ‖phi‖ * ‖beta⁻¹‖ * beta := by
    intro w
    rw [(hderivs w).fderiv]
    calc ‖phi • (beta⁻¹ • ((S w)⁻¹ • T w))‖
        = ‖phi‖ * ‖beta⁻¹‖ * (‖(S w)⁻¹‖ * ‖T w‖) := by
          rw [norm_smul, norm_smul, norm_smul, mul_assoc]
      _ ≤ ‖phi‖ * ‖beta⁻¹‖ * beta :=
          mul_le_mul_of_nonneg_left (hinner w) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hScont : Continuous S := by
    show Continuous fun w : Fin p → ℝ => ∑ j : Fin p, Real.exp (beta * (w j - y j))
    fun_prop
  have hTcont : Continuous T := by
    show Continuous fun w : Fin p → ℝ =>
      ∑ j : Fin p, Real.exp (beta * (w j - y j)) • (beta • ContinuousLinearMap.proj j)
    fun_prop
  have hfderivs_cont : Continuous (fderiv ℝ s) := by
    have hform : fderiv ℝ s = fun w : Fin p → ℝ => phi • (beta⁻¹ • ((S w)⁻¹ • T w)) :=
      funext (fun w => (hderivs w).fderiv)
    rw [hform]
    have h1 : Continuous fun w : Fin p → ℝ => (S w)⁻¹ := hScont.inv₀ (fun w => ne_of_gt (hSpos w))
    exact continuous_const.smul (continuous_const.smul (h1.smul hTcont))
  have hsdata : ∃ C : ℝ, 0 ≤ C ∧ (∀ w : Fin p → ℝ, ‖fderiv ℝ s w‖ ≤ C) ∧
      Continuous (fderiv ℝ s) :=
    ⟨‖phi‖ * ‖beta⁻¹‖ * beta,
      mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbeta, hbound_s, hfderivs_cont⟩
  obtain ⟨C, hCnn, hCbound, hfderivs_cont⟩ := hsdata
  have hchain : ∀ w : Fin p → ℝ,
      fderiv ℝ (fun w : Fin p → ℝ => phi0 (s w)) w = (fderiv ℝ phi0 (s w)).comp (fderiv ℝ s w) := by
    intro w
    have h1 : HasFDerivAt phi0 (fderiv ℝ phi0 (s w)) (s w) := (hphi0_diff (s w)).hasFDerivAt
    have h2 : HasFDerivAt s (fderiv ℝ s w) w := (hderivs w).differentiableAt.hasFDerivAt
    have hd : HasDerivAt phi0 ((fderiv ℝ phi0 (s w)) 1) (s w) := h1.hasDerivAt
    have h3 : HasFDerivAt (fun w : Fin p → ℝ => phi0 (s w))
        (((fderiv ℝ phi0 (s w)) 1) • fderiv ℝ s w) w :=
      HasDerivAt.comp_hasFDerivAt w hd h2
    have hs : ((fderiv ℝ phi0 (s w)) 1) • fderiv ℝ s w
        = (fderiv ℝ phi0 (s w)).comp (fderiv ℝ s w) := by
      ext v
      have key : ((fderiv ℝ phi0 (s w)).comp (fderiv ℝ s w)) v
          = ((fderiv ℝ s w) v) * ((fderiv ℝ phi0 (s w)) 1) := by
        show (fderiv ℝ phi0 (s w)) ((fderiv ℝ s w) v)
            = ((fderiv ℝ s w) v) * ((fderiv ℝ phi0 (s w)) 1)
        conv_lhs => rw [show (fderiv ℝ s w) v = ((fderiv ℝ s w) v) • (1 : ℝ) by simp]
        rw [ContinuousLinearMap.map_smul, smul_eq_mul]
      rw [key, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [← hs]
    exact h3.fderiv
  refine ⟨M0 * C, mul_nonneg hM0nn hCnn, ?_, ?_⟩
  · intro w
    rw [hchain w]
    calc ‖(fderiv ℝ phi0 (s w)).comp (fderiv ℝ s w)‖
        ≤ ‖fderiv ℝ phi0 (s w)‖ * ‖fderiv ℝ s w‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M0 * C := mul_le_mul (hM0bound (s w)) (hCbound w) (norm_nonneg _) hM0nn
  · rw [show fderiv ℝ (fun w : Fin p → ℝ => phi0 (s w))
        = fun w => (fderiv ℝ phi0 (s w)).comp (fderiv ℝ s w) from funext hchain]
    exact (hfderiv_cont.comp hs_cont).clm_comp hfderivs_cont
  /- @proof-region region.target-node.session.ec024bb72ac806a7 end -/

end

end Statlib.Imported

