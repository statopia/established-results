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
theorem statopia_math_node_591627577_6ac29b55 : ∀ (k n m : ℕ) (hk : 0 < k) (hn : 0 < n) (hm : 0 < m)
    (d : ℝ) (μX μY : Fin k → ℝ)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (X F : Fin n → Ω → (Fin k → ℝ)) (Y G : Fin m → Ω → (Fin k → ℝ)),
    (∀ (ω : Ω) (j : Fin k),
        combVec d μX μY (fun i => X i ω) (fun i => Y i ω) j = partXY X Y μX μY d ω j)
    ∧ (∀ (ω : Ω) (j : Fin k),
        combVec d μX μY (fun i => F i ω) (fun i => G i ω) j = partFG F G μX μY d ω j)
    ∧ (∀ j : Fin k,
        (fun ω => combVec d μX μY (fun i => X i ω) (fun i => Y i ω) j ^ 2)
          = (fun ω => partXY X Y μX μY d ω j ^ 2))
    ∧ (∀ j : Fin k,
        Integrable (fun ω => combVec d μX μY (fun i => X i ω) (fun i => Y i ω) j ^ 2) μ
          ↔ Integrable (fun ω => partXY X Y μX μY d ω j ^ 2) μ)
    ∧ ((⨅ j : Fin k, ∫ ω, combVec d μX μY (fun i => X i ω) (fun i => Y i ω) j ^ 2 ∂μ)
        = ⨅ j : Fin k, ∫ ω, partXY X Y μX μY d ω j ^ 2 ∂μ)
    ∧ (∀ j : Fin k,
        (fun ω => combVec d μX μY (fun i => F i ω) (fun i => G i ω) j ^ 2)
          = (fun ω => partFG F G μX μY d ω j ^ 2))
    ∧ (∀ j : Fin k,
        Integrable (fun ω => combVec d μX μY (fun i => F i ω) (fun i => G i ω) j ^ 2) μ
          ↔ Integrable (fun ω => partFG F G μX μY d ω j ^ 2) μ)
    ∧ ((⨅ j : Fin k, ∫ ω, combVec d μX μY (fun i => F i ω) (fun i => G i ω) j ^ 2 ∂μ)
        = ⨅ j : Fin k, ∫ ω, partFG F G μX μY d ω j ^ 2 ∂μ) := by
  /- @proof-region region.target-node.session.9db45742451ee101 begin -/
  intro k n m hk hn hm d μX μY Ω inst μ X F Y G
  have hXY : ∀ (ω : Ω) (j : Fin k),
      combVec d μX μY (fun i => X i ω) (fun i => Y i ω) j = partXY X Y μX μY d ω j := by
    intro ω j
    rfl
  have hFG : ∀ (ω : Ω) (j : Fin k),
      combVec d μX μY (fun i => F i ω) (fun i => G i ω) j = partFG F G μX μY d ω j := by
    intro ω j
    rfl
  have hsqXY : ∀ j : Fin k,
      (fun ω => combVec d μX μY (fun i => X i ω) (fun i => Y i ω) j ^ 2)
        = (fun ω => partXY X Y μX μY d ω j ^ 2) := by
    intro j
    funext ω
    rw [hXY ω j]
  have hsqFG : ∀ j : Fin k,
      (fun ω => combVec d μX μY (fun i => F i ω) (fun i => G i ω) j ^ 2)
        = (fun ω => partFG F G μX μY d ω j ^ 2) := by
    intro j
    funext ω
    rw [hFG ω j]
  refine ⟨hXY, hFG, hsqXY, ?_, ?_, hsqFG, ?_, ?_⟩
  · intro j
    simp only [hsqXY j]
  · simp only [hsqXY]
  · intro j
    simp only [hsqFG j]
  · simp only [hsqFG]
  /- @proof-region region.target-node.session.9db45742451ee101 end -/

end Statlib.Imported

end

