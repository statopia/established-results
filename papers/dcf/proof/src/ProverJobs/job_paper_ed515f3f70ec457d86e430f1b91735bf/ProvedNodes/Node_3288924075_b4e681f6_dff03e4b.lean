import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ExternalNodes.Node_df9285a2e94441188459

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
theorem statopia_math_node_3288924075_b4e681f6 : ∀ (phi0 : ℝ → ℝ)
    (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1),
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ) (hp : 0 < Real.log (p : ℝ)) (phi : ℝ) (hphi : 1 ≤ phi)
        (y : Fin p → ℝ),
        (let beta : ℝ := phi * Real.log (p : ℝ)
         let kappa : (Fin p → ℝ) → ℝ :=
           fun w => phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
         ∃ Q : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ,
           (∀ (j k l : Fin p) (w : Fin p → ℝ), 0 ≤ Q j k l w) ∧
           (∀ (d : Fin 3 → Fin p) (w : Fin p → ℝ),
             |iteratedFDeriv ℝ 3 kappa w (fun t : Fin 3 => Pi.single (d t) (1 : ℝ))| ≤
               Q (d 0) (d 1) (d 2) w) ∧
           (∀ w : Fin p → ℝ,
             ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p, Q j k l w ≤
               C * (phi ^ 3 + phi ^ 2 * beta + phi * beta ^ 2)) ∧
           (∀ w : Fin p → ℝ,
             ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p, Q j k l w ≤
               (3 * C / (Real.log 2) ^ 2) * phi * beta ^ 2) ∧
           (∀ (w wtilde : Fin p → ℝ), beta * maxAbs wtilde ≤ 1 → ∀ (j k l : Fin p),
             Q j k l w ≤ C * Q j k l (w + wtilde) ∧
               Q j k l (w + wtilde) ≤ C * Q j k l w)) := by
  /- @proof-region region.target-node.session.7741c80b105737c7 begin -/
  intro phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  obtain ⟨C2, hC2ge1, -, hC2phi⟩ :=
    PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported.paper_370f7a68a9a1447a9d903f9a55f08bd5
  obtain ⟨C1, C3, hC1ge1, hC3ge1, hC13⟩ :=
    hC2phi phi0 hphi0_range hphi0_cont hphi0_left hphi0_right
  have hC1le : C1 ≤ max C1 (max (C1 * C2) C3) := le_max_left _ _
  have hC12le : C1 * C2 ≤ max C1 (max (C1 * C2) C3) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hC3le : C3 ≤ max C1 (max (C1 * C2) C3) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hC12nonneg : (0 : ℝ) ≤ C1 * C2 := by nlinarith [hC1ge1, hC2ge1]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2sqpos : (0 : ℝ) < (Real.log 2) ^ 2 := pow_pos hlog2pos 2
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog2sqle3 : (Real.log 2) ^ 2 ≤ 3 := by nlinarith
  have hcoef : C1 * C2 ≤ 3 * max C1 (max (C1 * C2) C3) / (Real.log 2) ^ 2 := by
    rw [le_div_iff₀ hlog2sqpos]
    have h1 : C1 * C2 * (Real.log 2) ^ 2 ≤ C1 * C2 * 3 :=
      mul_le_mul_of_nonneg_left hlog2sqle3 hC12nonneg
    have h2 : C1 * C2 * 3 ≤ max C1 (max (C1 * C2) C3) * 3 :=
      mul_le_mul_of_nonneg_right hC12le (by norm_num)
    linarith
  refine ⟨max C1 (max (C1 * C2) C3), ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith : (0 : ℝ) < C1) hC1le
  intro p hp phi hphi y
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h] at hp
      exact absurd hp (by simp)
    · exact h
  obtain ⟨Q, hQnn, hQbd, hQ1, hQ2, hQ3⟩ := hC13 p hp0 hp phi hphi y
  refine ⟨Q, hQnn, ?_, ?_, ?_, ?_⟩
  · intro d w
    have hvec : (fun t : Fin 3 => (Pi.single (d t) (1 : ℝ) : Fin p → ℝ))
        = (fun t : Fin 3 => (Pi.single (![d 0, d 1, d 2] t) (1 : ℝ) : Fin p → ℝ)) := by
      funext t
      fin_cases t <;> simp
    have hb :
        iteratedFDeriv ℝ 3 (fun w : Fin p → ℝ =>
            phi0 (phi * ((phi * Real.log (p : ℝ))⁻¹ *
              Real.log (∑ j : Fin p, Real.exp ((phi * Real.log (p : ℝ)) * (w j - y j)))))) w
          (fun t : Fin 3 => Pi.single (![d 0, d 1, d 2] t) (1 : ℝ))
        = PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported.kappaThird
            p phi y phi0 (d 0) (d 1) (d 2) w := by
      unfold PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported.kappaThird
      rfl
    rw [hvec, hb]
    exact hQbd (d 0) (d 1) (d 2) w
  · intro w
    have hphi0 : (0 : ℝ) ≤ phi := by linarith
    have hbeta0 : (0 : ℝ) ≤ phi * Real.log (p : ℝ) := mul_nonneg hphi0 (le_of_lt hp)
    have hX : (0 : ℝ) ≤
        phi ^ 3 + phi ^ 2 * (phi * Real.log (p : ℝ)) + phi * (phi * Real.log (p : ℝ)) ^ 2 := by
      have h4 : (0 : ℝ) ≤ phi ^ 3 := by positivity
      have h5 : (0 : ℝ) ≤ phi ^ 2 * (phi * Real.log (p : ℝ)) := mul_nonneg (by positivity) hbeta0
      have h6 : (0 : ℝ) ≤ phi * (phi * Real.log (p : ℝ)) ^ 2 := mul_nonneg hphi0 (by positivity)
      linarith
    calc ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p, Q j k l w
        ≤ C1 * (phi ^ 3 + phi ^ 2 * (phi * Real.log (p : ℝ)) +
            phi * (phi * Real.log (p : ℝ)) ^ 2) := hQ1 w
      _ ≤ max C1 (max (C1 * C2) C3) * (phi ^ 3 + phi ^ 2 * (phi * Real.log (p : ℝ)) +
            phi * (phi * Real.log (p : ℝ)) ^ 2) := mul_le_mul_of_nonneg_right hC1le hX
  · intro w
    have hphi0 : (0 : ℝ) ≤ phi := by linarith
    have hY : (0 : ℝ) ≤ phi * (phi * Real.log (p : ℝ)) ^ 2 :=
      mul_nonneg hphi0 (by positivity)
    calc ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p, Q j k l w
        ≤ (C1 * C2) * (phi * (phi * Real.log (p : ℝ)) ^ 2) := hQ2 w
      _ ≤ (3 * max C1 (max (C1 * C2) C3) / (Real.log 2) ^ 2) *
            (phi * (phi * Real.log (p : ℝ)) ^ 2) := mul_le_mul_of_nonneg_right hcoef hY
      _ = (3 * max C1 (max (C1 * C2) C3) / (Real.log 2) ^ 2) * phi *
            (phi * Real.log (p : ℝ)) ^ 2 := by ring
  · intro w wtilde hstab j k l
    have hphi0 : (0 : ℝ) ≤ phi := by linarith
    have hbeta0 : (0 : ℝ) ≤ phi * Real.log (p : ℝ) := mul_nonneg hphi0 (le_of_lt hp)
    have hb : ∀ r : Fin p, |wtilde r| * (phi * Real.log (p : ℝ)) ≤ 1 := by
      intro r
      haveI : Nonempty (Fin p) := ⟨r⟩
      have hbdd : BddAbove (Set.range fun j : Fin p => |wtilde j|) :=
        ⟨∑ j : Fin p, |wtilde j|, by
          rintro _ ⟨j, rfl⟩
          exact Finset.single_le_sum (f := fun i : Fin p => |wtilde i|) (fun i _ => abs_nonneg (wtilde i)) (Finset.mem_univ j)⟩
      have hle : |wtilde r| ≤ maxAbs wtilde := by
        show |wtilde r| ≤ ⨆ j : Fin p, |wtilde j|
        exact le_ciSup hbdd r
      calc |wtilde r| * (phi * Real.log (p : ℝ))
          ≤ maxAbs wtilde * (phi * Real.log (p : ℝ)) := mul_le_mul_of_nonneg_right hle hbeta0
        _ = (phi * Real.log (p : ℝ)) * maxAbs wtilde := by ring
        _ ≤ 1 := hstab
    obtain ⟨h1, h2⟩ := hQ3 j k l w wtilde hb
    exact ⟨le_trans h1 (mul_le_mul_of_nonneg_right hC3le (hQnn j k l (w + wtilde))),
      le_trans h2 (mul_le_mul_of_nonneg_right hC3le (hQnn j k l w))⟩
  /- @proof-region region.target-node.session.7741c80b105737c7 end -/

end

end Statlib.Imported

