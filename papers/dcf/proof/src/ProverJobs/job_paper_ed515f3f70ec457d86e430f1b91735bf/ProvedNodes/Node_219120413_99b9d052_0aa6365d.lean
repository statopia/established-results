import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3262026558_5ae96f6d_ab73e3f4
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_761770009_4f9c88a3_9f247497

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
theorem statopia_math_node_219120413_99b9d052 : ∀ (p : ℕ) (hp : 2 ≤ p) (phi : ℝ) (hphi : 1 ≤ phi)
    (phi0 : ℝ → ℝ) (hcont : ContDiff ℝ 3 phi0)
    (hleft : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hright : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hrange : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (y : Fin p → ℝ) (j : Fin p),
    ∃ C : ℝ, ∀ (k : Fin p) (w : Fin p → ℝ),
      ‖(fderiv ℝ (fun z : Fin p → ℝ =>
          (fderiv ℝ (fun w' : Fin p → ℝ =>
            phi0 (phi * (((phi * Real.log (p : ℝ)))⁻¹ *
              Real.log (∑ q : Fin p, Real.exp (((phi * Real.log (p : ℝ))) * (w' q - y q)))))) z)
            (Pi.single j (1 : ℝ))) w) (Pi.single k (1 : ℝ))‖ ≤ C := by
  /- @proof-region region.target-node.session.0828ba0b3b1636a1 begin -/
  intro p hp phi hphi phi0 hcont hleft hright hrange y j
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have h2 : (1 : ℕ) < p := lt_of_lt_of_le (by norm_num) hp
    exact_mod_cast h2
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hphi0 : (0 : ℝ) < phi := by linarith
  let β : ℝ := phi * Real.log (p : ℝ)
  have hβpos : 0 < β := mul_pos hphi0 hlogp
  let S : (Fin p → ℝ) → ℝ := fun w => ∑ q, Real.exp (β * (w q - y q))
  have hSpos : ∀ w, 0 < S w := by
    intro w
    haveI : Nonempty (Fin p) := ⟨⟨0, lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hp⟩⟩
    exact Finset.sum_pos (fun q _ => Real.exp_pos _) Finset.univ_nonempty
  let F : (Fin p → ℝ) → ℝ := fun w => β⁻¹ * Real.log (S w)
  let s : (Fin p → ℝ) → ℝ := fun w => phi * F w
  let κ : (Fin p → ℝ) → ℝ := fun w => phi0 (s w)
  obtain ⟨hFdiff, hF1, hFd, hF2⟩ :=
    statopia_math_node_761770009_4f9c88a3 p hp β hβpos y
  obtain ⟨M₁, M₂, hM1nn, hM2nn, hM1, hM2, hphid, hphi0diff⟩ :=
    statopia_math_node_3262026558_5ae96f6d phi0 hcont hleft hright
  have hs_eq : ∀ w, fderiv ℝ s w = phi • fderiv ℝ F w := by
    intro w
    exact ((hFdiff w).const_mul phi).fderiv
  have hs_diff : ∀ w, HasFDerivAt s (fderiv ℝ s w) w := by
    intro w
    have h : HasFDerivAt s (phi • fderiv ℝ F w) w := (hFdiff w).const_mul phi
    rw [hs_eq w]
    exact h
  have hs1 : ∀ w, ‖fderiv ℝ s w‖ ≤ phi := by
    intro w
    rw [hs_eq w, norm_smul, Real.norm_eq_abs, abs_of_pos hphi0]
    calc phi * ‖fderiv ℝ F w‖ ≤ phi * 1 := mul_le_mul_of_nonneg_left (hF1 w) (le_of_lt hphi0)
      _ = phi := mul_one phi
  have hs2d : ∀ w, HasFDerivAt (fderiv ℝ s) (phi • fderiv ℝ (fderiv ℝ F) w) w := by
    intro w
    have h : HasFDerivAt (fun y => phi • fderiv ℝ F y) (phi • fderiv ℝ (fderiv ℝ F) w) w :=
      (hFd w).const_smul phi
    exact h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (funext fun y => hs_eq y))
  have hs2 : ∀ (w : Fin p → ℝ) (z : Fin p → ℝ),
      ‖(fderiv ℝ (fderiv ℝ s) w) z‖ ≤ (2 * phi * β) * ‖z‖ := by
    intro w z
    have h : fderiv ℝ (fderiv ℝ s) w = phi • fderiv ℝ (fderiv ℝ F) w := (hs2d w).fderiv
    have hz : (phi • fderiv ℝ (fderiv ℝ F) w) z = phi • ((fderiv ℝ (fderiv ℝ F) w) z) := rfl
    rw [h, hz, norm_smul, Real.norm_eq_abs, abs_of_pos hphi0]
    calc phi * ‖(fderiv ℝ (fderiv ℝ F) w) z‖ ≤ phi * (‖fderiv ℝ (fderiv ℝ F) w‖ * ‖z‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (le_of_lt hphi0)
      _ ≤ phi * ((2 * β) * ‖z‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hF2 w) (norm_nonneg z)) (le_of_lt hphi0)
      _ = 2 * phi * β * ‖z‖ := by ring
  have hsd : ∀ w, HasFDerivAt (fderiv ℝ s) (fderiv ℝ (fderiv ℝ s) w) w := by
    intro w
    have h : fderiv ℝ (fderiv ℝ s) w = phi • fderiv ℝ (fderiv ℝ F) w := (hs2d w).fderiv
    rw [h]
    exact hs2d w
  have hκeq : ∀ z, fderiv ℝ κ z = (fderiv ℝ phi0 (s z)).comp (fderiv ℝ s z) := by
    intro z
    exact ((hphi0diff (s z)).comp z (hs_diff z)).fderiv
  refine ⟨M₂ * phi ^ 2 + 2 * M₁ * phi * β, fun k w => ?_⟩
  have hc : HasFDerivAt (fun y => fderiv ℝ phi0 (s y))
      ((fderiv ℝ (fderiv ℝ phi0) (s w)).comp (fderiv ℝ s w)) w :=
    (hphid (s w)).comp w (hs_diff w)
  have hA : HasFDerivAt (fun y => (fderiv ℝ s y) (Pi.single j 1))
      ((fderiv ℝ (fderiv ℝ s) w).flip (Pi.single j 1)) w := by
    have h2 : HasFDerivAt (fun _ : Fin p → ℝ => (Pi.single j (1 : ℝ) : Fin p → ℝ))
        (fderiv ℝ (fun _ : Fin p → ℝ => (Pi.single j (1 : ℝ) : Fin p → ℝ)) w) w :=
      (differentiableAt_const _).hasFDerivAt
    simpa using (hsd w).clm_apply h2
  have hgd0 := hc.clm_apply hA
  have hgd : HasFDerivAt (fun z => (fderiv ℝ κ z) (Pi.single j 1))
      ((fderiv ℝ phi0 (s w)).comp ((fderiv ℝ (fderiv ℝ s) w).flip (Pi.single j 1)) +
        ((fderiv ℝ (fderiv ℝ phi0) (s w)).comp (fderiv ℝ s w)).flip
          ((fderiv ℝ s w) (Pi.single j 1))) w := by
    refine hgd0.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext z
    show (fderiv ℝ κ z) (Pi.single j 1) =
      (fderiv ℝ phi0 (s z)) ((fderiv ℝ s z) (Pi.single j 1))
    rw [hκeq z, ContinuousLinearMap.comp_apply]
  rw [hgd.fderiv]
  have hvk : ‖(Pi.single k (1 : ℝ) : Fin p → ℝ)‖ ≤ 1 := by
    rw [Pi.norm_single]
    norm_num
  have hvj : ‖(Pi.single j (1 : ℝ) : Fin p → ℝ)‖ ≤ 1 := by
    rw [Pi.norm_single]
    norm_num
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  have hP : ‖(fderiv ℝ phi0 (s w)) ((fderiv ℝ (fderiv ℝ s) w) (Pi.single k 1) (Pi.single j 1))‖ ≤
      M₁ * (2 * phi * β) := by
    have hX : ‖(fderiv ℝ (fderiv ℝ s) w) (Pi.single k 1) (Pi.single j 1)‖ ≤ 2 * phi * β := by
      have h1 : ‖(fderiv ℝ (fderiv ℝ s) w) (Pi.single k 1)‖ ≤
          (2 * phi * β) * ‖(Pi.single k (1 : ℝ) : Fin p → ℝ)‖ := hs2 w _
      calc ‖(fderiv ℝ (fderiv ℝ s) w) (Pi.single k 1) (Pi.single j 1)‖
          ≤ ‖(fderiv ℝ (fderiv ℝ s) w) (Pi.single k 1)‖ *
              ‖(Pi.single j (1 : ℝ) : Fin p → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ((2 * phi * β) * ‖(Pi.single k (1 : ℝ) : Fin p → ℝ)‖) *
              ‖(Pi.single j (1 : ℝ) : Fin p → ℝ)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ ((2 * phi * β) * 1) * 1 := by
            have h0 : (0 : ℝ) ≤ 2 * phi * β := by positivity
            have hstep : (2 * phi * β) * ‖(Pi.single k (1 : ℝ) : Fin p → ℝ)‖ ≤
                (2 * phi * β) * 1 := mul_le_mul_of_nonneg_left hvk h0
            calc ((2 * phi * β) * ‖(Pi.single k (1 : ℝ) : Fin p → ℝ)‖) *
                  ‖(Pi.single j (1 : ℝ) : Fin p → ℝ)‖
                ≤ ((2 * phi * β) * 1) * ‖(Pi.single j (1 : ℝ) : Fin p → ℝ)‖ :=
                  mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
              _ ≤ ((2 * phi * β) * 1) * 1 :=
                  mul_le_mul_of_nonneg_left hvj (by positivity)
        _ = 2 * phi * β := by ring
    calc ‖(fderiv ℝ phi0 (s w)) ((fderiv ℝ (fderiv ℝ s) w) (Pi.single k 1) (Pi.single j 1))‖
        ≤ ‖fderiv ℝ phi0 (s w)‖ *
            ‖(fderiv ℝ (fderiv ℝ s) w) (Pi.single k 1) (Pi.single j 1)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ M₁ * (2 * phi * β) :=
          mul_le_mul (hM1 (s w)) hX (norm_nonneg _) (le_trans (norm_nonneg _) (hM1 (s w)))
  have hQ : ‖(fderiv ℝ (fderiv ℝ phi0) (s w)) ((fderiv ℝ s w) (Pi.single k 1))
      ((fderiv ℝ s w) (Pi.single j 1))‖ ≤ M₂ * phi ^ 2 := by
    have hzk : ‖(fderiv ℝ s w) (Pi.single k 1)‖ ≤ phi := by
      calc ‖(fderiv ℝ s w) (Pi.single k 1)‖ ≤
            ‖fderiv ℝ s w‖ * ‖(Pi.single k (1 : ℝ) : Fin p → ℝ)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ phi * 1 := mul_le_mul (hs1 w) hvk (norm_nonneg _) (le_of_lt hphi0)
        _ = phi := mul_one phi
    have hzj : ‖(fderiv ℝ s w) (Pi.single j 1)‖ ≤ phi := by
      calc ‖(fderiv ℝ s w) (Pi.single j 1)‖ ≤
            ‖fderiv ℝ s w‖ * ‖(Pi.single j (1 : ℝ) : Fin p → ℝ)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ phi * 1 := mul_le_mul (hs1 w) hvj (norm_nonneg _) (le_of_lt hphi0)
        _ = phi := mul_one phi
    have hinner : ‖(fderiv ℝ (fderiv ℝ phi0) (s w)) ((fderiv ℝ s w) (Pi.single k 1))‖ ≤
        M₂ * phi :=
      calc ‖(fderiv ℝ (fderiv ℝ phi0) (s w)) ((fderiv ℝ s w) (Pi.single k 1))‖
          ≤ ‖fderiv ℝ (fderiv ℝ phi0) (s w)‖ * ‖(fderiv ℝ s w) (Pi.single k 1)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M₂ * phi := mul_le_mul (hM2 (s w)) hzk (norm_nonneg _) hM2nn
    calc ‖(fderiv ℝ (fderiv ℝ phi0) (s w)) ((fderiv ℝ s w) (Pi.single k 1))
          ((fderiv ℝ s w) (Pi.single j 1))‖
        ≤ ‖(fderiv ℝ (fderiv ℝ phi0) (s w)) ((fderiv ℝ s w) (Pi.single k 1))‖ *
            ‖(fderiv ℝ s w) (Pi.single j 1)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M₂ * phi) * phi :=
          mul_le_mul hinner hzj (norm_nonneg _) (mul_nonneg hM2nn (le_of_lt hphi0))
      _ = M₂ * phi ^ 2 := by ring
  refine le_trans (norm_add_le _ _) (le_trans (add_le_add hP hQ) (le_of_eq ?_))
  ring
  /- @proof-region region.target-node.session.0828ba0b3b1636a1 end -/

end

end Statlib.Imported

