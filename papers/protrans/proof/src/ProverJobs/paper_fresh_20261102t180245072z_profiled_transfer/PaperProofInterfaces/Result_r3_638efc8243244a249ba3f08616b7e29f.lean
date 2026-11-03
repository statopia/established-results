import Statlib.StatFoundation.Vocabulary.OrliczNorm
import Lean
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Vocabulary
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.ProvedNodes
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Base

namespace PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28

open MeasureTheory ProbabilityTheory ENNReal
open scoped ENNReal Matrix
open Statlib.StatFoundation.Vocabulary
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
universe u

theorem paper_6ff987a9c5974b249aed2ac5c2c60b28 :
    ∀ (q : ℕ), 1 ≤ q → ∀ (L : ℝ), 0 < L → ∀ (c : ℝ), 0 < c →
      ∃ C_H N_H : ℝ, 0 < C_H ∧ 0 < N_H ∧
        ∀ (p : ℕ), 2 ≤ p →
        ∀ (N : ℕ), 1 ≤ N → N_H * Real.log (p : ℝ) ≤ (N : ℝ) →
          ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (ν : Measure ((Fin q → ℝ) × (Fin p → ℝ))) [IsProbabilityMeasure ν]
            (f : (Fin q → ℝ) → (Fin p → ℝ))
            (E : Fin N → Ω → Fin p → ℝ) (H : Fin N → Ω → Fin q → ℝ),
            iIndepFun (fun i ω => (H i ω, E i ω)) μ →
            (∀ i, Measure.map (fun ω => (H i ω, E i ω)) μ = ν) →
            (∀ i j, Measurable (fun ω => E i ω j)) →
            (∀ i l, Measurable (fun ω => H i ω l)) →
            (∀ i j, Measurable (fun ω => f (H i ω) j)) →
            (∀ i j, Integrable (fun ω => E i ω j) μ) →
            (∀ i l, Integrable (fun ω => H i ω l) μ) →
            (∀ i j, Integrable (fun ω => f (H i ω) j) μ) →
            (∀ i j, ∫ ω, E i ω j ∂μ = 0) →
            (∀ i l, ∫ ω, H i ω l ∂μ = 0) →
            (∀ i j, ∫ ω, f (H i ω) j ∂μ = 0) →
            (∀ i j, subgaussianOrliczNorm (fun ω => E i ω j) μ ≤ ENNReal.ofReal L) →
            (∀ i l, subgaussianOrliczNorm (fun ω => H i ω l) μ ≤ ENNReal.ofReal L) →
            (∀ i j, subgaussianOrliczNorm (fun ω => f (H i ω) j) μ ≤ ENNReal.ofReal L) →
            (∀ i j l, Integrable (fun ω => E i ω j * H i ω l) μ) →
            (∀ i j l, ∫ ω, E i ω j * H i ω l ∂μ = 0) →
            (∀ j l, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 j * z.1 l) ν) →

            μ ({ω : Ω | ∃ (j : Fin p) (l : Fin q),
                    C_H * Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) <
                      |((N : ℝ)⁻¹) * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l|} ∪
                {ω : Ω | ∃ (j : Fin p) (l : Fin q),
                    C_H * Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) <
                      |((N : ℝ)⁻¹) * (∑ i : Fin N, E i ω j * H i ω l)|})
              ≤ ENNReal.ofReal ((p : ℝ) ^ (-c) / 20)
:= by
  /- @proof-region region.root.ce3233ea2d36 begin -/
  intro q hq L hL c hc
  obtain ⟨C_H, hC_H, N_H, hN_H, hbound⟩ :=
    statopia_math_node_2829730235_b80926fc q hq L hL c hc
  refine ⟨C_H, hC_H, N_H, hN_H, ?_⟩
  intro p hp N hN1 hNlog Ω _ μ _ ν _ f E H hIndep hLaw hEmeas hHmeas hfmeas
    hEint hHint hfint hEz hHz hfz hEsg hHsg hfsg hEHint hEH0 hφint
  exact hbound p hp N hN1 hNlog Ω μ ν f E H hIndep hLaw hEmeas hHmeas hfmeas hEint hHint
    hfint hEz hHz hfz hEsg hHsg hfsg hEHint hEH0 hφint
  /- @proof-region region.root.ce3233ea2d36 end -/

-- Paper root revision c5fc1632-b848-4e23-bfa1-6724505d389c

