import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base

namespace PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported

noncomputable section
universe u
open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1150318497_1ef0c7ba : ∀ {k n m : ℕ} (hk : 0 < k) (hn : 0 < n) (hm : 0 < m)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X F : Fin n → Ω → (Fin k → ℝ)) (Y G : Fin m → Ω → (Fin k → ℝ))
    {ι : Type*} (e : ι ≃ (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))
    (jointFam : ι → Ω → (Fin k → ℝ))
    (hjoint : ∀ i : ι, jointFam i = allVec X Y F G (e i)),
    iIndepFun (allVec X Y F G) μ ↔ iIndepFun jointFam μ := by
  /- @proof-region region.target-node.session.5003094584340cfb begin -/
  intro k n m hk hn hm Ω hΩ μ hμ X F Y G ι e jointFam hjoint
  have hfam : jointFam = fun i => allVec X Y F G (e i) := funext fun i => hjoint i
  rw [hfam]
  constructor
  · intro h
    exact iIndepFun.precomp (g := ⇑e) e.injective h
  · intro h
    have h2 := iIndepFun.precomp (f := fun i => allVec X Y F G (e i)) (g := ⇑e.symm)
      e.symm.injective h
    simpa only [Equiv.apply_symm_apply] using h2
  /- @proof-region region.target-node.session.5003094584340cfb end -/

end Statlib.Imported

end

