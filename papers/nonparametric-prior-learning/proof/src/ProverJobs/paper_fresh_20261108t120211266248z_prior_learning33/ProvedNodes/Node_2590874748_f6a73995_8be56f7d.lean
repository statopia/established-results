import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1218121120_7255afae_cddb3a58
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_189267838_542a0222_7a0c245e

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33


open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2590874748_f6a73995 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc_pos : ∀ k : ℕ, 0 < c k)
    (mu nu : Measure U) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (m_mu m_nu : U)
    (hmarg_mu : ∀ n : ℕ,
      MeasureTheory.Measure.map (fun u : U => fun i : Fin n => inner ℝ (e i) u) mu
        = MeasureTheory.Measure.pi
            (fun i : Fin n =>
              ProbabilityTheory.gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩))
    (hsigma2 : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2))
    (hsum : ∀ᵐ u ∂mu,
      Summable (fun k : ℕ => (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu)))
    (hcyl : ∀ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C →
      nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C)
        = ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
            ENNReal.ofReal
              (Real.exp
                ((∑ i : Fin n,
                    ((inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) *
                        (inner ℝ (e i) u - inner ℝ (e i) m_mu))
                      / c i)
                  - (∑ i : Fin n, (inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) ^ 2 / (2 * c i)))) ∂mu), nu = mu.withDensity (fun u : U =>
        ENNReal.ofReal
          (Real.exp
            ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
              - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2))) := by
  /- @proof-region region.target-node.session.2ec9301f20a849e7 begin -/
  intro U instNG instIPS instCS instSep instMS instBS e c hc_pos mu nu instPM instPN m_mu m_nu
    hmarg_mu hsigma2 hsum hcyl
  classical
  let a : ℕ → ℝ := fun k => (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu)
  let X : U → ℕ → ℝ := fun u k => inner ℝ (e k) (u - m_mu)
  let ρn : ℕ → U → ENNReal := fun n u =>
    ENNReal.ofReal (Real.exp ((∑ i : Fin n, a i * X u i) - (∑ i : Fin n, a i ^ 2 * c i) / 2))
  let ρ : U → ENNReal := fun u =>
    ENNReal.ofReal
      (Real.exp ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
        - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2))
  have hρn_int : ∀ n : ℕ, ∫⁻ u, ENNReal.ofReal
      (Real.exp
        ((∑ i : Fin n,
            ((inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) * (inner ℝ (e i) u - inner ℝ (e i) m_mu)) / c i)
          - (∑ i : Fin n, (inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) ^ 2 / (2 * c i)))) ∂mu = 1 := by
    intro n
    simpa using (hcyl n Set.univ MeasurableSet.univ).symm

  have hgen : (inferInstance : MeasurableSpace U) = MeasurableSpace.generateFrom
      {s : Set U | ∃ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C ∧
        s = (fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C} :=
    statopia_math_node_1218121120_7255afae U e
  have hpi : IsPiSystem
      {s : Set U | ∃ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C ∧
        s = (fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C} := by
    intro s hs t ht _hne
    obtain ⟨n, C, hC, rfl⟩ := hs
    obtain ⟨m, D, hD, rfl⟩ := ht
    rcases le_total n m with hnm | hmn
    · refine ⟨m, (fun x : Fin m → ℝ => fun i : Fin n => x (Fin.castLE hnm i)) ⁻¹' C ∩ D, ?_, ?_⟩
      · exact MeasurableSet.inter
          (hC.preimage (measurable_pi_iff.mpr fun i => measurable_pi_apply (Fin.castLE hnm i))) hD
      · ext u
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by simpa [Fin.castLE] using h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by simpa [Fin.castLE] using h1, h2⟩
    · refine ⟨n, C ∩ (fun x : Fin n → ℝ => fun i : Fin m => x (Fin.castLE hmn i)) ⁻¹' D, ?_, ?_⟩
      · exact MeasurableSet.inter hC
          (hD.preimage (measurable_pi_iff.mpr fun i => measurable_pi_apply (Fin.castLE hmn i)))
      · ext u
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by simpa [Fin.castLE] using h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by simpa [Fin.castLE] using h2⟩
  have hdens : ∀ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C →
      nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C)
        = (mu.withDensity ρ) ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C) :=
    statopia_math_node_189267838_542a0222 U e c hc_pos mu nu m_mu m_nu hmarg_mu hsigma2 hsum hcyl
  refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion (μ := nu) (ν := mu.withDensity ρ)
    {s : Set U | ∃ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C ∧
      s = (fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C}
    (fun _ : ℕ => (Set.univ : Set U)) hgen hpi (by ext x; simp)
    (fun _ => ⟨0, Set.univ, MeasurableSet.univ, by simp⟩) (fun _ => by simp) ?_
  intro s hs
  obtain ⟨n, C, hC, rfl⟩ := hs
  exact hdens n C hC
  /- @proof-region region.target-node.session.2ec9301f20a849e7 end -/

end Statlib.Imported
end

