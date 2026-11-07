import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_957869045_16437b4b_7c74bf69

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
theorem statopia_math_node_1967109576_c7239acb : ∀ (phi0 : ℝ → ℝ)
    (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p : ℕ) (hp : 2 ≤ p) (phi : ℝ) (hphi : 1 ≤ phi)
        (y : Fin p → ℝ) (w : Fin p → ℝ) (j : Fin p),
        (let kappa : (Fin p → ℝ) → ℝ :=
          fun w' => phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ *
            Real.log (∑ k : Fin p, Real.exp ((phi * Real.log (p : ℝ)) * (w' k - y k)))));
          |(fderiv ℝ kappa w) (Pi.single j (1 : ℝ))| ≤ C * phi) := by
  /- @proof-region region.target-node.session.6da028d05a98271a begin -/
  intro phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  have hderiv_cont : Continuous (deriv phi0) :=
    hphi0_cont.continuous_deriv (by norm_num)
  have hcontOn : ContinuousOn (deriv phi0) (Set.Icc (0:ℝ) 1) := hderiv_cont.continuousOn
  obtain ⟨C₀, hC₀⟩ :=
    IsCompact.exists_bound_of_continuousOn (s := Set.Icc (0:ℝ) 1) (f := deriv phi0)
      isCompact_Icc hcontOn
  have hCbound : ∀ x : ℝ, |deriv phi0 x| ≤ max C₀ 0 := by
    intro x
    by_cases hin : x ∈ Set.Icc (0:ℝ) 1
    · have hx := hC₀ x hin
      rw [Real.norm_eq_abs] at hx
      exact le_trans hx (le_max_left _ _)
    · have hd0 : deriv phi0 x = 0 := by
        rw [Set.mem_Icc, not_and_or] at hin
        push_neg at hin
        rcases hin with hx | hx
        · have heq : phi0 =ᶠ[nhds x] (fun _ => (1:ℝ)) := by
            apply Filter.eventually_of_mem ((isOpen_Iio : IsOpen (Set.Iio (0:ℝ))).mem_nhds hx)
            intro z hz
            exact hphi0_left z (le_of_lt hz)
          rw [heq.deriv_eq]; simp
        · have heq : phi0 =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
            apply Filter.eventually_of_mem ((isOpen_Ioi : IsOpen (Set.Ioi (1:ℝ))).mem_nhds hx)
            intro z hz
            exact hphi0_right z (le_of_lt hz)
          rw [heq.deriv_eq]; simp
      rw [hd0, abs_zero]
      exact le_max_right _ _
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro p hp phi hphi y w j
  change |(fderiv ℝ (fun w' => phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ *
      Real.log (∑ k : Fin p, Real.exp ((phi * Real.log (p : ℝ)) * (w' k - y k)))))) w)
      (Pi.single j (1 : ℝ))| ≤ max C₀ 0 * phi
  let Kf : (Fin p → ℝ) → ℝ := fun w' => phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ *
      Real.log (∑ k : Fin p, Real.exp ((phi * Real.log (p : ℝ)) * (w' k - y k)))))
  show |(fderiv ℝ Kf w) (Pi.single j (1 : ℝ))| ≤ max C₀ 0 * phi
  have hKcd : ContDiff ℝ 3 Kf :=
    (statopia_math_node_2194576110_d2ad0cef p hp phi hphi phi0 hphi0_cont hphi0_left
      hphi0_right hphi0_range y).1
  have hKdiff : DifferentiableAt ℝ Kf w := hKcd.contDiffAt.differentiableAt (by norm_num)
  have hfd : HasFDerivAt Kf (fderiv ℝ Kf w) w := hKdiff.hasFDerivAt
  let e : Fin p → ℝ := Pi.single j (1:ℝ)
  have hcurve : HasDerivAt (fun t : ℝ => w + t • e) e 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • e) e 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const e
    have hsum := (hasDerivAt_const (0:ℝ) w).add h1
    have hfun : ((fun _ : ℝ => w) + (fun t : ℝ => t • e)) = (fun t : ℝ => w + t • e) := by
      funext t; simp
    rw [hfun, show (0 : Fin p → ℝ) + e = e from zero_add e] at hsum
    exact hsum
  have hfd' : HasFDerivAt Kf (fderiv ℝ Kf w) ((fun t : ℝ => w + t • e) 0) := by
    rw [show (fun t : ℝ => w + t • e) 0 = w from by simp]
    exact hfd
  have hcomp : HasDerivAt (Kf ∘ (fun t : ℝ => w + t • e))
      ((fderiv ℝ Kf w) e) 0 :=
    HasFDerivAt.comp_hasDerivAt (x := (0:ℝ)) hfd' hcurve
  have hchild := statopia_math_node_957869045_16437b4b p hp phi hphi phi0 hphi0_cont y w j
  have hderiv_eq : (fderiv ℝ Kf w) (Pi.single j (1:ℝ)) =
      deriv phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ *
          Real.log (∑ k : Fin p, Real.exp ((phi * Real.log (p : ℝ)) * (w k - y k))))) *
        (phi * (Real.exp ((phi * Real.log (p : ℝ)) * (w j - y j)) /
          (∑ k : Fin p, Real.exp ((phi * Real.log (p : ℝ)) * (w k - y k))))) :=
    hcomp.deriv.symm.trans hchild.deriv
  rw [hderiv_eq]
  set numw : ℝ := Real.exp ((phi * Real.log (p : ℝ)) * (w j - y j)) with hnumw
  set Sw : ℝ := ∑ k : Fin p, Real.exp ((phi * Real.log (p : ℝ)) * (w k - y k)) with hSw
  rw [abs_mul]
  have hphi_pos : (0:ℝ) < phi := lt_of_lt_of_le zero_lt_one hphi
  have hnumw_pos : (0:ℝ) < numw := by rw [hnumw]; exact Real.exp_pos _
  have hSw_pos : (0:ℝ) < Sw := by
    rw [hSw]
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_univ j⟩
  have hnumw_le : numw ≤ Sw := by
    rw [hnumw, hSw]
    exact Finset.single_le_sum (f := fun k : Fin p => Real.exp ((phi * Real.log (p:ℝ)) * (w k - y k))) (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ j)
  have hfrac_nn : (0:ℝ) ≤ numw / Sw := div_nonneg hnumw_pos.le hSw_pos.le
  have hfrac_le : numw / Sw ≤ 1 := (div_le_one hSw_pos).mpr hnumw_le
  have h2 : |phi * (numw / Sw)| ≤ phi := by
    rw [abs_of_nonneg (mul_nonneg hphi_pos.le hfrac_nn)]
    simpa using mul_le_mul_of_nonneg_left hfrac_le hphi_pos.le
  exact mul_le_mul (hCbound _) h2 (abs_nonneg _) (le_max_right _ _)
  /- @proof-region region.target-node.session.6da028d05a98271a end -/

end

end Statlib.Imported

