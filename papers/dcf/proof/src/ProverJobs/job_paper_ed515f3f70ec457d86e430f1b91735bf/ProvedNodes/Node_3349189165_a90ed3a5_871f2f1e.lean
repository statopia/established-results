import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1357572546_def39e20_7c767bcc
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3642255598_3496c7f2_0cc19571

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
theorem statopia_math_node_3349189165_a90ed3a5 : ∀ (b : ℝ) (hb : 0 < b),
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
        (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
        (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
        (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
        (hX : ∀ i : Fin n, Measurable (X i)) (hY : ∀ i : Fin m, Measurable (Y i))
        (hF : ∀ i : Fin n, Measurable (F i)) (hG : ∀ i : Fin m, Measurable (G i))
        (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
        (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
        (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
        (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
        (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
        (hX3 : ∀ (i : Fin n) (j : Fin p),
          Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
        (hY3 : ∀ (i : Fin m) (j : Fin p),
          Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
        (hF3 : ∀ (i : Fin n) (j : Fin p),
          Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
        (hG3 : ∀ (i : Fin m) (j : Fin p),
          Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
        (hFcov : ∀ i : Fin n,
          IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
        (hGcov : ∀ i : Fin m,
          IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
        (hbvar : ∀ (j : Fin p), b ≤ ∫ (ω : Ω),
          combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j ^ 2 ∂P),
        ∀ (y : Fin p → ℝ) (w : ℝ), 0 ≤ w →
          (P {ω : Ω |
              -(w) < (⨆ j : Fin p,
                (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ∧
              (⨆ j : Fin p,
                (combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j - y j)) ≤ w}).toReal
            ≤ Cb * w * (Real.sqrt (Real.log (p : ℝ)) + 1) := by
  /- @proof-region region.target-node.session.9d287f231646e3b9 begin -/
  intro b hb
  obtain ⟨Cb, hCbpos, hCb⟩ := statopia_math_node_1357572546_def39e20 b hb
  refine ⟨Cb, hCbpos, ?_⟩
  intro Ω _ P _ n m p delta muX muY X Y F G hn hm hp hX hY hF hG hindep hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov hbvar y w hw
  obtain ⟨hB, hdiag⟩ :=
    statopia_math_node_3642255598_3496c7f2 b Ω P n m p delta muX muY X Y F G hn hm hp
      hX hY hF hG hindep hXmean hYmean hXL2 hYL2 hFcov hGcov hbvar
  exact hCb p (Nat.succ_le_of_lt hp) P
    (fun ω j => combVec n m (delta n m) muX muY (fun i => F i ω) (fun i => G i ω) j) _
    hB hdiag y w hw
  /- @proof-region region.target-node.session.9d287f231646e3b9 end -/

end

end Statlib.Imported

