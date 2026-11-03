import Statlib.Nonparametric.Spectral.Embedding
import Lean
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Vocabulary
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Base

namespace PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28

open MeasureTheory ProbabilityTheory ENNReal
open scoped ENNReal Matrix
open Statlib.StatFoundation.Vocabulary
open _root_.PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported

open MeasureTheory ProbabilityTheory ENNReal
open scoped ENNReal Matrix
open Statlib.StatFoundation.Vocabulary
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
universe u

set_option autoImplicit false in
theorem statopia_math_node_3975489229_33218fe7 : ∀ (N p q : ℕ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure ((Fin q → ℝ) × (Fin p → ℝ))) [IsProbabilityMeasure ν]
    (f : (Fin q → ℝ) → (Fin p → ℝ))
    (E : Fin N → Ω → Fin p → ℝ) (H : Fin N → Ω → Fin q → ℝ)
    (hindep : iIndepFun (fun i ω => (H i ω, E i ω)) μ)
    (hlaw : ∀ i, Measure.map (fun ω => (H i ω, E i ω)) μ = ν)
    (hH_meas : ∀ (i : Fin N) (l : Fin q), Measurable (fun ω => H i ω l))
    (hE_meas : ∀ (i : Fin N) (j : Fin p), Measurable (fun ω => E i ω j))
    (hInt : ∀ (j : Fin p) (l : Fin q),
      Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 j * z.1 l) ν),
    (∀ (j : Fin p) (l : Fin q),
      iIndepFun (fun i ω => f (H i ω) j * H i ω l - (Mf f ν) j l) μ) ∧
    (∀ (j : Fin p) (l : Fin q),
      iIndepFun (fun i ω => E i ω j * H i ω l) μ) := by
  /- @proof-region region.target-node.session.56d1f8632cc4e07f begin -/
  intro N p q Ω _ μ _ ν _ f E H hindep hlaw hH_meas hE_meas hInt
  have hHm : ∀ i, Measurable (fun ω => H i ω) :=
    fun i => measurable_pi_iff.mpr (fun l => hH_meas i l)
  have hEm : ∀ i, Measurable (fun ω => E i ω) :=
    fun i => measurable_pi_iff.mpr (fun j => hE_meas i j)
  have hφae : ∀ i, AEMeasurable (fun ω => (H i ω, E i ω)) μ :=
    fun i => (Measurable.prodMk (hHm i) (hEm i)).aemeasurable
  constructor
  · intro j l
    have hG : AEMeasurable
        (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 j * z.1 l) ν :=
      (hInt j l).aemeasurable
    have hind1 : iIndepFun (fun i ω => f (H i ω) j * H i ω l) μ :=
      iIndepFun.comp₀ hindep
        (fun (_ : Fin N) (z : (Fin q → ℝ) × (Fin p → ℝ)) => f z.1 j * z.1 l)
        hφae (fun i => by simpa only [hlaw i] using hG)
    exact iIndepFun.comp hind1 (fun (_ : Fin N) (x : ℝ) => x - (Mf f ν) j l)
      (fun _ => by measurability)
  · intro j l
    exact iIndepFun.comp hindep
      (fun (_ : Fin N) (z : (Fin q → ℝ) × (Fin p → ℝ)) => z.2 j * z.1 l)
      (fun _ => by measurability)
  /- @proof-region region.target-node.session.56d1f8632cc4e07f end -/

end Statlib.Imported

