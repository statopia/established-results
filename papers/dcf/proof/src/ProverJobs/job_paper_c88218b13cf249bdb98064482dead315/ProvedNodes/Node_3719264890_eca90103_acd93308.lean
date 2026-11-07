import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.ProvedNodes.Node_591627577_6ac29b55_ac010883

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
theorem statopia_math_node_3719264890_eca90103 : ∀ (k n m : ℕ) (hk : 0 < k) (hn : 0 < n) (hm : 0 < m)
    (d : ℝ) (μX μY : Fin k → ℝ)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X F : Fin n → Ω → (Fin k → ℝ)) (Y G : Fin m → Ω → (Fin k → ℝ)),
    (∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ y : Fin k → ℝ,
        |(μ {ω : Ω | (Real.sqrt v • combVec d μX μY (fun i => X i ω) (fun i => Y i ω)
              + Real.sqrt (1 - v) • combVec d μX μY (fun i => F i ω) (fun i => G i ω)) ≤ y}).toReal
            - (μ {ω : Ω | combVec d μX μY (fun i => F i ω) (fun i => G i ω) ≤ y}).toReal|
          = |(μ {ω : Ω | (Real.sqrt v • partXY X Y μX μY d ω
                + Real.sqrt (1 - v) • partFG F G μX μY d ω) ≤ y}).toReal
            - (μ {ω : Ω | partFG F G μX μY d ω ≤ y}).toReal|)
    ∧ ((⨆ v ∈ Set.Icc (0 : ℝ) 1, ⨆ y : Fin k → ℝ,
          |(μ {ω : Ω | (Real.sqrt v • combVec d μX μY (fun i => X i ω) (fun i => Y i ω)
                + Real.sqrt (1 - v) • combVec d μX μY (fun i => F i ω) (fun i => G i ω)) ≤ y}).toReal
              - (μ {ω : Ω | combVec d μX μY (fun i => F i ω) (fun i => G i ω) ≤ y}).toReal|)
        = (⨆ v ∈ Set.Icc (0 : ℝ) 1, ⨆ y : Fin k → ℝ,
          |(μ {ω : Ω | (Real.sqrt v • partXY X Y μX μY d ω
                + Real.sqrt (1 - v) • partFG F G μX μY d ω) ≤ y}).toReal
              - (μ {ω : Ω | partFG F G μX μY d ω ≤ y}).toReal|))
    ∧ (∀ phi : ℝ, 1 ≤ phi →
        ((⨆ j : Fin k, (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, |X i ω j - μX j| ^ 3 ∂μ) = Lstat μ X μX)
        ∧ (((n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, (if Real.sqrt (n : ℝ) / (4 * phi * Real.log (k : ℝ))
                < (⨆ j : Fin k, |X i ω j - μX j|)
              then (⨆ j : Fin k, |X i ω j - μX j|) ^ 3 else 0) ∂μ
            + (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, (if Real.sqrt (n : ℝ) / (4 * phi * Real.log (k : ℝ))
                < (⨆ j : Fin k, |F i ω j - μX j|)
              then (⨆ j : Fin k, |F i ω j - μX j|) ^ 3 else 0) ∂μ)
          = MstatN μ X F μX phi)
        ∧ ((if d = 0 then 0
            else (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, (if Real.sqrt (m : ℝ) / (4 * |d| * phi * Real.log (k : ℝ))
                    < (⨆ j : Fin k, |Y i ω j - μY j|)
                  then (⨆ j : Fin k, |Y i ω j - μY j|) ^ 3 else 0) ∂μ
              + (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, (if Real.sqrt (m : ℝ) / (4 * |d| * phi * Real.log (k : ℝ))
                    < (⨆ j : Fin k, |G i ω j - μY j|)
                  then (⨆ j : Fin k, |G i ω j - μY j|) ^ 3 else 0) ∂μ)
          = MstatM μ Y G μY phi d)) := by
  /- @proof-region region.target-node.session.df6d98b800290537 begin -/
  intro k n m hk hn hm d μX μY Ω hΩ μ hμ X F Y G
  obtain ⟨hXY, hFG, _⟩ :=
    @statopia_math_node_591627577_6ac29b55 k n m hk hn hm d μX μY Ω hΩ μ X F Y G
  have hcomb : ∀ ω : Ω,
      combVec d μX μY (fun i => X i ω) (fun i => Y i ω) = partXY X Y μX μY d ω :=
    fun ω => funext (hXY ω)
  have hcombF : ∀ ω : Ω,
      combVec d μX μY (fun i => F i ω) (fun i => G i ω) = partFG F G μX μY d ω :=
    fun ω => funext (hFG ω)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv y
    simp only [hcomb, hcombF]
  · simp only [hcomb, hcombF]
  · intro phi hphi
    exact ⟨rfl, rfl, rfl⟩
  /- @proof-region region.target-node.session.df6d98b800290537 end -/

end Statlib.Imported

end

