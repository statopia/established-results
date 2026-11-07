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
theorem statopia_math_node_108072969_a1eba6a6 : ∀ (phi0 : ℝ → ℝ)
    (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0),
    ∃ M1 M2 : ℝ,
      0 ≤ M1 ∧ 0 ≤ M2 ∧
        (∀ t : ℝ, |deriv phi0 t| ≤ M1) ∧
        (∀ t : ℝ, |deriv (deriv phi0) t| ≤ M2) ∧
        Continuous (fun t : ℝ => deriv phi0 t) ∧
        Continuous (fun t : ℝ => deriv (deriv phi0) t) := by
  /- @proof-region region.target-node.session.86d2b4f31ed6315c begin -/
  intro phi0 hphi0_cont hphi0_left hphi0_right
  let Φ : ℝ × ℝ → ℝ := fun p => (fderiv ℝ phi0 p.1) p.2
  have hΦ2 : ContDiff ℝ 2 Φ := hphi0_cont.contDiff_fderiv_apply (by norm_num)
  have hΦ_cont : Continuous Φ := hΦ2.continuous
  have hΦfderiv_cont : Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ Φ q.1) q.2) :=
    hΦ2.continuous_fderiv_apply (by norm_num)
  have hderiv_cont : Continuous (fun t : ℝ => deriv phi0 t) := by
    have hpath : Continuous (fun t : ℝ => ((t, (1 : ℝ)) : ℝ × ℝ)) := by continuity
    have heq : (fun t : ℝ => deriv phi0 t) = Φ ∘ (fun t : ℝ => ((t, (1 : ℝ)) : ℝ × ℝ)) := by
      funext t
      rw [Function.comp_apply]
      exact (fderiv_apply_one_eq_deriv (f := phi0) (x := t)).symm
    rw [heq]
    exact hΦ_cont.comp hpath
  have hderiv2_eq : ∀ t : ℝ, deriv (deriv phi0) t = (fderiv ℝ Φ ((t, (1 : ℝ)) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) := by
    intro t
    have hdiffAt : DifferentiableAt ℝ Φ ((t, (1 : ℝ)) : ℝ × ℝ) :=
      hΦ2.contDiffAt.differentiableAt (by norm_num)
    have hF : HasFDerivAt Φ (fderiv ℝ Φ ((t, (1 : ℝ)) : ℝ × ℝ)) ((t, (1 : ℝ)) : ℝ × ℝ) :=
      hdiffAt.hasFDerivAt
    have hg : HasDerivAt (fun s : ℝ => ((s, (1 : ℝ)) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) t := by
      have hL : HasFDerivAt (⇑(ContinuousLinearMap.toSpanSingleton ℝ ((1 : ℝ), (0 : ℝ)))) (ContinuousLinearMap.toSpanSingleton ℝ ((1 : ℝ), (0 : ℝ))) t :=
        ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ ((1 : ℝ), (0 : ℝ)))
      have hshift : HasFDerivAt (fun p : ℝ × ℝ => p - (-((0 : ℝ), (1 : ℝ)))) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) (⇑(ContinuousLinearMap.toSpanSingleton ℝ ((1 : ℝ), (0 : ℝ))) t) :=
        hasFDerivAt_sub_const (-((0 : ℝ), (1 : ℝ)) : ℝ × ℝ)
      have hv := (hshift.comp t hL).hasDerivAt
      have hfuneq : ((fun p : ℝ × ℝ => p - (-((0 : ℝ), (1 : ℝ)))) ∘ (⇑(ContinuousLinearMap.toSpanSingleton ℝ ((1 : ℝ), (0 : ℝ))))) = (fun s : ℝ => ((s, (1 : ℝ)) : ℝ × ℝ)) := by
        funext s
        simp
      have hvaleq : (ContinuousLinearMap.id ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.toSpanSingleton ℝ ((1 : ℝ), (0 : ℝ))) (1 : ℝ) = ((1 : ℝ), (0 : ℝ)) := by
        simp
      rw [hfuneq, hvaleq] at hv
      exact hv
    have hcomp := hF.comp_hasDerivAt t hg
    have hfun : Φ ∘ (fun s : ℝ => ((s, (1 : ℝ)) : ℝ × ℝ)) = deriv phi0 := by
      funext s
      rw [Function.comp_apply]
      exact fderiv_apply_one_eq_deriv (f := phi0) (x := s)
    rw [hfun] at hcomp
    exact hcomp.deriv
  have hderiv2_cont : Continuous (fun t : ℝ => deriv (deriv phi0) t) := by
    have hpath : Continuous (fun t : ℝ => (((t, (1 : ℝ)) : ℝ × ℝ), (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ))) := by continuity
    have heq : (fun t : ℝ => deriv (deriv phi0) t) =
        (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ Φ q.1) q.2) ∘
          (fun t : ℝ => (((t, (1 : ℝ)) : ℝ × ℝ), (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ))) := by
      funext t
      rw [Function.comp_apply]
      exact hderiv2_eq t
    rw [heq]
    exact hΦfderiv_cont.comp hpath
  have hderiv_zero_left : ∀ t : ℝ, t < 0 → deriv phi0 t = 0 := by
    intro t ht
    have hev : Filter.EventuallyEq (nhds t) phi0 (fun _ => (1 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      exact hphi0_left s (le_of_lt hs)
    rw [hev.deriv_eq, deriv_const]
  have hderiv_zero_right : ∀ t : ℝ, 1 < t → deriv phi0 t = 0 := by
    intro t ht
    have hev : Filter.EventuallyEq (nhds t) phi0 (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact hphi0_right s (le_of_lt hs)
    rw [hev.deriv_eq, deriv_const]
  have hderiv2_zero_left : ∀ t : ℝ, t < 0 → deriv (deriv phi0) t = 0 := by
    intro t ht
    have hev : Filter.EventuallyEq (nhds t) (deriv phi0) (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      exact hderiv_zero_left s hs
    rw [hev.deriv_eq, deriv_const]
  have hderiv2_zero_right : ∀ t : ℝ, 1 < t → deriv (deriv phi0) t = 0 := by
    intro t ht
    have hev : Filter.EventuallyEq (nhds t) (deriv phi0) (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact hderiv_zero_right s hs
    rw [hev.deriv_eq, deriv_const]
  obtain ⟨x1, _, hx1max⟩ := (ConditionallyCompleteLinearOrder.isCompact_Icc (0 : ℝ) 1).exists_isMaxOn
    (⟨0, by simp⟩ : (Set.Icc (0 : ℝ) 1).Nonempty) (f := fun t => |deriv phi0 t|)
    (by intro t _; exact hderiv_cont.abs.continuousAt.continuousWithinAt)
  obtain ⟨x2, _, hx2max⟩ := (ConditionallyCompleteLinearOrder.isCompact_Icc (0 : ℝ) 1).exists_isMaxOn
    (⟨0, by simp⟩ : (Set.Icc (0 : ℝ) 1).Nonempty) (f := fun t => |deriv (deriv phi0) t|)
    (by intro t _; exact hderiv2_cont.abs.continuousAt.continuousWithinAt)
  refine ⟨max (|deriv phi0 x1|) 0, max (|deriv (deriv phi0) x2|) 0, le_max_right _ _, le_max_right _ _, ?_, ?_, hderiv_cont, hderiv2_cont⟩
  · intro t
    by_cases hlt : t < 0
    · rw [hderiv_zero_left t hlt, abs_zero]; exact le_max_right _ _
    · have ht0 : 0 ≤ t := by linarith
      by_cases hgt : 1 < t
      · rw [hderiv_zero_right t hgt, abs_zero]; exact le_max_right _ _
      · have ht1 : t ≤ 1 := by linarith
        exact le_trans (hx1max ⟨ht0, ht1⟩) (le_max_left _ _)
  · intro t
    by_cases hlt : t < 0
    · rw [hderiv2_zero_left t hlt, abs_zero]; exact le_max_right _ _
    · have ht0 : 0 ≤ t := by linarith
      by_cases hgt : 1 < t
      · rw [hderiv2_zero_right t hgt, abs_zero]; exact le_max_right _ _
      · have ht1 : t ≤ 1 := by linarith
        exact le_trans (hx2max ⟨ht0, ht1⟩) (le_max_left _ _)
  /- @proof-region region.target-node.session.86d2b4f31ed6315c end -/

end

end Statlib.Imported

