import Lean
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Vocabulary
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Base

namespace PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e

open _root_.PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2082055502_c6d14abe : ∀ {Ω : Type*} [MeasurableSpace Ω]
    {Idx : Type*} {β : Type*} [MeasurableSpace β]
    (mu : Measure Ω) (F : Idx → Ω → β) (hF : iIndepFun F mu)
    {Idx2 : Type*} (e : Idx2 → Idx) (he : Function.Injective e),
    iIndepFun (fun i => F (e i)) mu ∧
      ∀ (I1 I2 : Type) (G : I1 ⊕ I2 → Ω → β), iIndepFun G mu →
        iIndepFun (fun r => G (Sum.inl r)) mu ∧
          iIndepFun (fun j => G (Sum.inr j)) mu := by
  /- @proof-region region.target-node.session.b1cc078c02f7d950 begin -/
  intro Ω instΩ Idx β instβ mu F hF Idx2 e he
  haveI : MeasurableSpace Ω := instΩ
  haveI : MeasurableSpace β := instβ
  exact ⟨iIndepFun.precomp he hF, fun I1 I2 G hG =>
    ⟨iIndepFun.precomp Sum.inl_injective hG,
      iIndepFun.precomp Sum.inr_injective hG⟩⟩
  /- @proof-region region.target-node.session.b1cc078c02f7d950 end -/

end

end Statlib.Imported

