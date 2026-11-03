import Lean
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Vocabulary
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Base
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.ProvedNodes.Node_2778848356_36628207_4a15a483
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.ProvedNodes.Node_3331897167_3f7edc77_88546067
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.ExternalNodes.Node_823fbb6926464c629003

namespace PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e



open _root_.PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_1884859470_ed2c3864 : ∀ (L : ℝ) (hL : 0 < L),
    ∃ Vprime : ℝ, 0 < Vprime ∧
      ∀ (q : ℕ) (hq : 1 ≤ q) (p : ℕ) (hp : 1 ≤ p)
        (f : (Fin q → ℝ) → (Fin p → ℝ)) (hf : Measurable f)
        (P : Measure ((Fin q → ℝ) × (Fin p → ℝ))) (hP : IsProbabilityMeasure P),
        (∀ i : Fin p, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i) P) →
        (∀ j : Fin q, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 j) P) →
        (∀ k : Fin p, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k) P) →
        (∀ i : Fin p, ∫ z, z.2 i ∂P = 0) →
        (∀ j : Fin q, ∫ z, z.1 j ∂P = 0) →
        (∀ k : Fin p, ∫ z, f z.1 k ∂P = 0) →
        (∀ i : Fin p,
          HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i)
            (Real.toNNReal (L ^ 2)) P) →
        (∀ j : Fin q,
          HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 j)
            (Real.toNNReal (L ^ 2)) P) →
        (∀ k : Fin p,
          HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k)
            (Real.toNNReal (L ^ 2)) P) →
        (∀ (i j : Fin p),
          Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
            (f z.1 i + z.2 i) * (f z.1 j + z.2 j)) P) →
        ∀ (N : ℕ), 1 ≤ N →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
        ∀ (rows : Fin N → Ω → (Fin q → ℝ) × (Fin p → ℝ)),
          (∀ l : Fin N, Measurable (rows l)) →
          (∀ l : Fin N, Measure.map (rows l) μ = P) →
          ∀ (l : Fin N) (i j : Fin p) (r : ℕ), 2 ≤ r →
            (∫ ω, |(f ((rows l ω).1) i + (rows l ω).2 i) *
                    (f ((rows l ω).1) j + (rows l ω).2 j) - SigmaX f P i j| ^ r ∂μ)
              ≤ (r.factorial : ℝ) * Vprime ^ r := by
  /- @proof-region region.target-node.session.b5a7679aa2f352a6 begin -/
  intro L hL
  obtain ⟨V, hVpos, hbound⟩ := statopia_math_node_3331897167_3f7edc77 L hL
  refine ⟨V, hVpos, ?_⟩
  intro q hq p hp f hf P hP hEint hHint hfHint hE0 hH0 hfH0 hEsg hHsg hfsg hprod
    N hN Ω instOmega μ hμ rows hrows hmap l i j r hr
  haveI : IsProbabilityMeasure P := hP
  haveI : IsProbabilityMeasure μ := hμ
  have hmeas : Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
      (f z.1 i + z.2 i) * (f z.1 j + z.2 j) - SigmaX f P i j) :=
    (statopia_math_node_2778848356_36628207 q hq p hp f hf P hprod N hN Ω μ
      rows hrows hmap).2.1 i j
  have hg_meas : Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
      |(f z.1 i + z.2 i) * (f z.1 j + z.2 j) - SigmaX f P i j| ^ r) :=
    (continuous_abs.pow r).measurable.comp hmeas
  have hg_sm : StronglyMeasurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
      |(f z.1 i + z.2 i) * (f z.1 j + z.2 j) - SigmaX f P i j| ^ r) :=
    hg_meas.stronglyMeasurable
  have key : (∫ ω, |(f ((rows l ω).1) i + (rows l ω).2 i) *
        (f ((rows l ω).1) j + (rows l ω).2 j) - SigmaX f P i j| ^ r ∂μ)
      = ∫ z, |(f z.1 i + z.2 i) * (f z.1 j + z.2 j) - SigmaX f P i j| ^ r ∂P := by
    calc (∫ ω, |(f ((rows l ω).1) i + (rows l ω).2 i) *
          (f ((rows l ω).1) j + (rows l ω).2 j) - SigmaX f P i j| ^ r ∂μ)
        = ∫ y, |(f y.1 i + y.2 i) * (f y.1 j + y.2 j) - SigmaX f P i j| ^ r
            ∂(Measure.map (rows l) μ) :=
          (MeasureTheory.integral_map_of_stronglyMeasurable (hrows l) hg_sm).symm
      _ = ∫ z, |(f z.1 i + z.2 i) * (f z.1 j + z.2 j) - SigmaX f P i j| ^ r ∂P := by
            rw [hmap l]
  rw [key]
  exact hbound q hq p hp f hf P hP hEint hHint hfHint hE0 hH0 hfH0 hEsg hHsg hfsg hprod i j r hr
  /- @proof-region region.target-node.session.b5a7679aa2f352a6 end -/

end Statlib.Imported

