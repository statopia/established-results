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
theorem statopia_math_node_3262026558_5ae96f6d : ∀ (phi0 : ℝ → ℝ)
    (hcont : ContDiff ℝ 3 phi0)
    (hleft : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hright : ∀ z : ℝ, 1 ≤ z → phi0 z = 0),
    ∃ M1 M2 : ℝ, 0 ≤ M1 ∧ 0 ≤ M2 ∧
      (∀ t : ℝ, ‖fderiv ℝ phi0 t‖ ≤ M1) ∧
      (∀ t : ℝ, ‖fderiv ℝ (fderiv ℝ phi0) t‖ ≤ M2) ∧
      (∀ t : ℝ, HasFDerivAt (fderiv ℝ phi0) (fderiv ℝ (fderiv ℝ phi0) t) t) ∧
      (∀ t : ℝ, HasFDerivAt phi0 (fderiv ℝ phi0 t) t) := by
  /- @proof-region region.target-node.session.b83d954ecaaf4bc7 begin -/
  intro phi0 hcont hleft hright
  have hdiff_phi0 : Differentiable ℝ phi0 := hcont.differentiable (by decide)
  have hphi0_deriv : ∀ t : ℝ, HasFDerivAt phi0 (fderiv ℝ phi0 t) t :=
    fun t => (hdiff_phi0 t).hasFDerivAt
  have hcont_d : Continuous (fderiv ℝ phi0) := hcont.continuous_fderiv (by decide)
  let c : ℝ → ℝ := fun t => fderiv ℝ phi0 t 1
  have hG : ContDiff ℝ 1 (fun p : ℝ × ℝ => (fderiv ℝ phi0 p.1) p.2) :=
    hcont.contDiff_fderiv_apply (m := 1) (by norm_num)
  have he : ContDiff ℝ 1 (fun t : ℝ => (t, (1 : ℝ))) := by fun_prop
  have hc_diff : ContDiff ℝ 1 c := by
    have h := hG.comp he
    simpa only [Function.comp] using h
  have hdeq : fderiv ℝ phi0 = fun t => c t • (1 : ℝ →L[ℝ] ℝ) := by
    funext t
    apply ContinuousLinearMap.ext
    intro x
    have hsm := (fderiv ℝ phi0 t).map_smul x (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at hsm
    have hmap : fderiv ℝ phi0 t x = x * c t := hsm
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    rw [hmap, mul_comm]
  have hd_all : ∀ t : ℝ,
      HasFDerivAt (fderiv ℝ phi0) ((fderiv ℝ c t).smulRight (1 : ℝ →L[ℝ] ℝ)) t := by
    intro t
    have hct : HasFDerivAt c (fderiv ℝ c t) t := (hc_diff.differentiable (by decide) t).hasFDerivAt
    have hconst : HasFDerivAt (fun _ : ℝ => (1 : ℝ →L[ℝ] ℝ)) (0 : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ)) t :=
      hasFDerivAt_const (1 : ℝ →L[ℝ] ℝ) t
    have hsm : HasFDerivAt (fun s => c s • (1 : ℝ →L[ℝ] ℝ)) ((fderiv ℝ c t).smulRight 1) t := by
      simpa using hct.smul hconst
    rw [hdeq]
    exact hsm
  have hderiv : ∀ t : ℝ,
      fderiv ℝ (fderiv ℝ phi0) t = (fderiv ℝ c t).smulRight (1 : ℝ →L[ℝ] ℝ) :=
    fun t => (hd_all t).fderiv
  have hphid : ∀ t : ℝ, HasFDerivAt (fderiv ℝ phi0) (fderiv ℝ (fderiv ℝ phi0) t) t := by
    intro t
    rw [hderiv t]
    exact hd_all t
  have hbound : ∀ t : ℝ, ‖fderiv ℝ (fderiv ℝ phi0) t‖ = ‖fderiv ℝ c t‖ := by
    intro t
    rw [hderiv t, ContinuousLinearMap.norm_smulRight_apply]
    simp
  have hd_left : ∀ t : ℝ, t < 0 → fderiv ℝ phi0 t = 0 := by
    intro t ht
    have hmem : Set.Iio (0 : ℝ) ∈ nhds t := isOpen_Iio.mem_nhds ht
    have heq : phi0 =ᶠ[nhds t] (fun _ => (1 : ℝ)) := by
      filter_upwards [hmem] with y hy
      exact hleft y (le_of_lt hy)
    rw [heq.fderiv_eq]
    simp
  have hd_right : ∀ t : ℝ, 1 < t → fderiv ℝ phi0 t = 0 := by
    intro t ht
    have hmem : Set.Ioi (1 : ℝ) ∈ nhds t := isOpen_Ioi.mem_nhds ht
    have heq : phi0 =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmem] with y hy
      exact hright y (le_of_lt hy)
    rw [heq.fderiv_eq]
    simp
  have hdd_left : ∀ t : ℝ, t < 0 → fderiv ℝ (fderiv ℝ phi0) t = 0 := by
    intro t ht
    have hmem : Set.Iio (0 : ℝ) ∈ nhds t := isOpen_Iio.mem_nhds ht
    have heq : fderiv ℝ phi0 =ᶠ[nhds t] (fun _ => (0 : ℝ →L[ℝ] ℝ)) := by
      filter_upwards [hmem] with y hy
      exact hd_left y hy
    rw [heq.fderiv_eq]
    simp
  have hdd_right : ∀ t : ℝ, 1 < t → fderiv ℝ (fderiv ℝ phi0) t = 0 := by
    intro t ht
    have hmem : Set.Ioi (1 : ℝ) ∈ nhds t := isOpen_Ioi.mem_nhds ht
    have heq : fderiv ℝ phi0 =ᶠ[nhds t] (fun _ => (0 : ℝ →L[ℝ] ℝ)) := by
      filter_upwards [hmem] with y hy
      exact hd_right y hy
    rw [heq.fderiv_eq]
    simp
  have hcd_left : ∀ t < 0, fderiv ℝ c t = 0 := by
    intro t ht
    have hmem : Set.Iio (0 : ℝ) ∈ nhds t := isOpen_Iio.mem_nhds ht
    have heq : c =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmem] with y hy
      show fderiv ℝ phi0 y 1 = 0
      rw [hd_left y hy]; simp
    rw [heq.fderiv_eq]; simp
  have hcd_right : ∀ t : ℝ, 1 < t → fderiv ℝ c t = 0 := by
    intro t ht
    have hmem : Set.Ioi (1 : ℝ) ∈ nhds t := isOpen_Ioi.mem_nhds ht
    have heq : c =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmem] with y hy
      show fderiv ℝ phi0 y 1 = 0
      rw [hd_right y hy]; simp
    rw [heq.fderiv_eq]; simp
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).image hcont_d.norm |>.bddAbove
  obtain ⟨B2, hB2⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).image (hc_diff.continuous_fderiv (by decide)).norm
      |>.bddAbove
  refine ⟨max B1 0, max B2 0, le_max_right _ _, le_max_right _ _, ?_, ?_, hphid, hphi0_deriv⟩
  · intro t
    rcases lt_or_ge t 0 with h | h
    · rw [hd_left t h]; simp
    · rcases le_or_gt t 1 with h1 | h1
      · exact le_trans (hB1 ⟨t, Set.mem_Icc.mpr ⟨h, h1⟩, rfl⟩) (le_max_left _ _)
      · rw [hd_right t h1]; simp
  · intro t
    rcases lt_or_ge t 0 with h | h
    · rw [hbound t, hcd_left t h]; simp
    · rcases le_or_gt t 1 with h1 | h1
      · rw [hbound t]
        exact le_trans (hB2 ⟨t, Set.mem_Icc.mpr ⟨h, h1⟩, rfl⟩) (le_max_left _ _)
      · rw [hbound t, hcd_right t h1]; simp
  /- @proof-region region.target-node.session.b83d954ecaaf4bc7 end -/

end

end Statlib.Imported

