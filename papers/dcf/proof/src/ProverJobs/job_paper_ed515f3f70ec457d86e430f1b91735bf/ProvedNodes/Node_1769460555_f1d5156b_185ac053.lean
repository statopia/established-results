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
theorem statopia_math_node_1769460555_f1d5156b : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (p : ℕ)
    (Zs : Ω → Fin p → ℝ)
    (hZs_meas : ∀ k : Fin p, Measurable (fun x : Ω => Zs x k))
    (hZs3 : ∀ k : Fin p, Integrable (fun x : Ω => |Zs x k| ^ 3) P)
    (Zd : Ω → ℝ)
    (hZd_meas : Measurable (fun x : Ω => Zd x))
    (hZd3 : Integrable (fun x : Ω => |Zd x| ^ 3) P)
    (c : ℝ) (hc : 0 ≤ c),
    Integrable (fun x : Ω => ∑ k : Fin p, ∑ l : Fin p,
      c * |Zs x k| * |Zs x l| * |Zd x|) P := by
  /- @proof-region region.target-node.session.3c2a222b28b04178 begin -/
  intro Ω inst P p Zs hZs_meas hZs3 Zd hZd_meas hZd3 c hc
  have hsummand : ∀ k l : Fin p, Integrable (fun x : Ω => c * |Zs x k| * |Zs x l| * |Zd x|) P := by
    intro k l
    have hbound : Integrable (fun x : Ω => 16 * c * (|Zs x k| ^ 3 + |Zs x l| ^ 3 + |Zd x| ^ 3)) P := by
      have hcube : Integrable (fun x : Ω => |Zs x k| ^ 3 + |Zs x l| ^ 3 + |Zd x| ^ 3) P :=
        ((hZs3 k).add (hZs3 l)).add hZd3
      exact hcube.const_mul (16 * c)
    have hmeas : AEStronglyMeasurable (fun x : Ω => c * |Zs x k| * |Zs x l| * |Zd x|) P :=
      (((measurable_const.mul (hZs_meas k).abs).mul (hZs_meas l).abs).mul hZd_meas.abs).aestronglyMeasurable
    refine hbound.mono' ?_ ?_
    · exact hmeas
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have ha : (0 : ℝ) ≤ |Zs x k| := abs_nonneg _
      have hb : (0 : ℝ) ≤ |Zs x l| := abs_nonneg _
      have hd : (0 : ℝ) ≤ |Zd x| := abs_nonneg _
      have h0 : (0 : ℝ) ≤ c * |Zs x k| * |Zs x l| * |Zd x| :=
        mul_nonneg (mul_nonneg (mul_nonneg hc ha) hb) hd
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      have hac : |Zs x k| ^ 2 * |Zd x| ≤ (2 * |Zs x k| ^ 3 + |Zd x| ^ 3) / 3 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * |Zs x k| + |Zd x| by linarith)
          (sq_nonneg (|Zs x k| - |Zd x|))]
      have hbc : |Zs x l| ^ 2 * |Zd x| ≤ (2 * |Zs x l| ^ 3 + |Zd x| ^ 3) / 3 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * |Zs x l| + |Zd x| by linarith)
          (sq_nonneg (|Zs x l| - |Zd x|))]
      have hab : |Zs x k| * |Zs x l| * |Zd x| ≤ (|Zs x k| ^ 2 + |Zs x l| ^ 2) * |Zd x| := by
        nlinarith [mul_nonneg hd (sq_nonneg (|Zs x k| - |Zs x l|))]
      have hstep : (|Zs x k| ^ 2 + |Zs x l| ^ 2) * |Zd x| ≤
          (2 * |Zs x k| ^ 3 + |Zd x| ^ 3) / 3 + (2 * |Zs x l| ^ 3 + |Zd x| ^ 3) / 3 := by
        rw [add_mul]
        linarith [hac, hbc]
      have hfinal : (2 * |Zs x k| ^ 3 + |Zd x| ^ 3) / 3 + (2 * |Zs x l| ^ 3 + |Zd x| ^ 3) / 3 ≤
          16 * (|Zs x k| ^ 3 + |Zs x l| ^ 3 + |Zd x| ^ 3) := by
        nlinarith [pow_nonneg ha 3, pow_nonneg hb 3, pow_nonneg hd 3]
      have hbnd : |Zs x k| * |Zs x l| * |Zd x| ≤
          16 * (|Zs x k| ^ 3 + |Zs x l| ^ 3 + |Zd x| ^ 3) :=
        le_trans hab (le_trans hstep hfinal)
      calc c * |Zs x k| * |Zs x l| * |Zd x| = c * (|Zs x k| * |Zs x l| * |Zd x|) := by ring
        _ ≤ c * (16 * (|Zs x k| ^ 3 + |Zs x l| ^ 3 + |Zd x| ^ 3)) :=
            mul_le_mul_of_nonneg_left hbnd hc
        _ = 16 * c * (|Zs x k| ^ 3 + |Zs x l| ^ 3 + |Zd x| ^ 3) := by ring
  have hinner : ∀ k : Fin p, Integrable (fun x : Ω => ∑ l : Fin p, c * |Zs x k| * |Zs x l| * |Zd x|) P := by
    intro k
    simpa using MeasureTheory.integrable_finset_sum
      (f := fun l x => c * |Zs x k| * |Zs x l| * |Zd x|) (Finset.univ : Finset (Fin p))
      (fun l _ => hsummand k l)
  simpa using MeasureTheory.integrable_finset_sum
    (f := fun k x => ∑ l : Fin p, c * |Zs x k| * |Zs x l| * |Zd x|) (Finset.univ : Finset (Fin p))
    (fun k _ => hinner k)
  /- @proof-region region.target-node.session.3c2a222b28b04178 end -/

end

end Statlib.Imported

