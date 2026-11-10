import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2535765968_adf0fe99_17cf80be
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2590874748_f6a73995_8be56f7d
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3076668657_2d2dfc66_7e264470
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_4190851802_dd7b3e47_812a2222
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_488254885_6df2d178_79332d6b
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_659555420_43074f04_a6ad3ba0

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
theorem statopia_math_node_303701622_51d4ad9b : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc_pos : ∀ k : ℕ, 0 < c k)
    (mu nu : Measure U) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu_gauss : ProbabilityTheory.IsGaussian mu)
    (hnu_gauss : ProbabilityTheory.IsGaussian nu)
    (m_mu m_nu : U)
    (hmu_mean : ∀ v : U, (∫ u, inner ℝ v u ∂mu) = inner ℝ v m_mu)
    (hnu_mean : ∀ v : U, (∫ u, inner ℝ v u ∂nu) = inner ℝ v m_nu)
    (hmu_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v m_mu) * (inner ℝ w u - inner ℝ w m_mu) ∂mu)
        = ∑' k : ℕ, c k * inner ℝ (e k) v * inner ℝ (e k) w)
    (hnu_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v m_nu) * (inner ℝ w u - inner ℝ w m_nu) ∂nu)
        = ∑' k : ℕ, c k * inner ℝ (e k) v * inner ℝ (e k) w)
    (hsigma2 : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)),
    nu = mu.withDensity (fun u : U =>
      ENNReal.ofReal
        (Real.exp
          ((Filter.limsup
              (fun n : ℕ => ∑ k ∈ Finset.range n,
                (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
              Filter.atTop)
            - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2))) := by
  /- @proof-region region.target-node.session.6b7911a3db1fe1ab begin -/
  intro U instNA instIPS instCS instSep instMS instBorel e c hc_pos mu nu hmuP hnuP
    hmu_gauss hnu_gauss m_mu m_nu hmu_mean hnu_mean hmu_cov hnu_cov hsigma2
  classical
  let a : ℕ → ℝ := fun k => (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu)
  let X : U → ℕ → ℝ := fun u k => inner ℝ (e k) (u - m_mu)
  let σ2 : ℝ := ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2
  let rho : U → ℝ≥0∞ := fun u =>
    ENNReal.ofReal
      (Real.exp
        ((Filter.limsup
            (fun n : ℕ => ∑ k ∈ Finset.range n,
              (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
            Filter.atTop)
          - σ2 / 2))
  have hlim :=
    statopia_math_node_659555420_43074f04 U e c hc_pos mu hmu_gauss m_mu m_nu
      hmu_mean hmu_cov hsigma2
  have hrho_meas :=
    statopia_math_node_4190851802_dd7b3e47 U e c hc_pos mu hmu_gauss m_mu m_nu
      hmu_mean hmu_cov hsigma2
  have hmap_mu : ∀ n : ℕ,
      Measure.map (fun u : U => fun i : Fin n => inner ℝ (e i) u) mu
        = Measure.pi
            (fun i : Fin n => gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩) :=
    fun n =>
      statopia_math_node_488254885_6df2d178 U e c hc_pos mu hmu_gauss m_mu hmu_mean hmu_cov n
  have hmap_nu : ∀ n : ℕ,
      Measure.map (fun u : U => fun i : Fin n => inner ℝ (e i) u) nu
        = Measure.pi
            (fun i : Fin n => gaussianReal (inner ℝ (e i) m_nu) ⟨c i, le_of_lt (hc_pos i)⟩) :=
    fun n =>
      statopia_math_node_488254885_6df2d178 U e c hc_pos nu hnu_gauss m_nu hnu_mean hnu_cov n
  have hshift : ∀ n : ℕ,
      Measure.map (fun u : U => fun i : Fin n => inner ℝ (e i) u) nu
        = (Measure.map (fun u : U => fun i : Fin n => inner ℝ (e i) u) mu).withDensity
            (fun x : Fin n → ℝ => ENNReal.ofReal
              (Real.exp
                ((∑ k : Fin n,
                    ((inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) * (x k - inner ℝ (e k) m_mu))
                      / c k)
                  - (∑ k : Fin n, (inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) ^ 2 / (2 * c k))))) := by
    intro n
    rw [hmap_nu n, hmap_mu n]
    refine statopia_math_node_2535765968_adf0fe99 (Fin n)
      (fun k => ⟨c k, le_of_lt (hc_pos k)⟩) ?_ (fun k => inner ℝ (e k) m_mu)
      (fun k => inner ℝ (e k) m_nu)
    intro k h
    have h0 : (⟨c k, le_of_lt (hc_pos k)⟩ : NNReal) = 0 := h
    have h1 : c k = 0 := by
      simpa using congrArg (fun x : NNReal => (x : ℝ)) h0
    exact absurd h1 (ne_of_gt (hc_pos k))
  let hn : ∀ n : ℕ, (Fin n → ℝ) → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal
      (Real.exp
        ((∑ k : Fin n,
            ((inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) * (x k - inner ℝ (e k) m_mu)) / c k)
          - (∑ k : Fin n, (inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) ^ 2 / (2 * c k))))
  have hcyl : ∀ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C →
      nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C)
        = ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
            hn n ((fun u : U => fun i : Fin n => inner ℝ (e i) u) u) ∂mu := by
    intro n C hC
    have hπ : Measurable (fun u : U => fun i : Fin n => inner ℝ (e i) u) := by
      refine measurable_pi_iff.mpr (fun i => ?_)
      have hcont : Continuous fun u : U => inner ℝ (e i) u := by
        simpa only [coe_innerSL_apply] using (innerSL ℝ (e i)).continuous
      exact hcont.measurable
    have hhn : Measurable (hn n) := by
      have hF : Measurable fun x : Fin n → ℝ =>
          (∑ k : Fin n,
              ((inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) * (x k - inner ℝ (e k) m_mu)) / c k)
            - (∑ k : Fin n, (inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) ^ 2 / (2 * c k)) := by
        refine Measurable.sub ?_ measurable_const
        refine Finset.measurable_sum _ (fun k _ => ?_)
        have h1 : Measurable fun x : Fin n → ℝ => x k - inner ℝ (e k) m_mu :=
          (measurable_pi_apply k).sub measurable_const
        have h2 : Measurable fun x : Fin n → ℝ =>
            (inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) * (x k - inner ℝ (e k) m_mu) :=
          measurable_const.mul h1
        exact h2.div_const (c k)
      exact (Real.measurable_exp.comp hF).ennreal_ofReal
    have hshift_hn : Measure.map (fun u : U => fun i : Fin n => inner ℝ (e i) u) nu
        = (Measure.map (fun u : U => fun i : Fin n => inner ℝ (e i) u) mu).withDensity (hn n) :=
      hshift n
    rw [← Measure.map_apply hπ hC, hshift_hn, withDensity_apply (hn n) hC,
      setLIntegral_map hC hhn hπ]
  have hint1 : ∀ n : ℕ,
      ∫⁻ u, hn n ((fun u : U => fun i : Fin n => inner ℝ (e i) u) u) ∂mu = 1 := by
    intro n
    simpa using (hcyl n Set.univ MeasurableSet.univ).symm
  have hσ2n : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)
      atTop (𝓝 σ2) := by
    have h := hsigma2.hasSum.tendsto_sum_nat
    simpa [σ2] using h
  have hn_eq : ∀ (n : ℕ) (u : U),
      hn n ((fun u : U => fun i : Fin n => inner ℝ (e i) u) u)
        = ENNReal.ofReal
            (Real.exp
              ((∑ k ∈ Finset.range n,
                  (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
                - (∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2)) := by
    intro n u
    have hS1 :
        (∑ k : Fin n,
            ((inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) *
                ((fun u : U => fun i : Fin n => inner ℝ (e i) u) u k
                  - inner ℝ (e k) m_mu)) / c k)
          = ∑ k ∈ Finset.range n,
              (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu) := by
      have hstep :
          (∑ k : Fin n,
              ((inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) *
                  ((fun u : U => fun i : Fin n => inner ℝ (e i) u) u k
                    - inner ℝ (e k) m_mu)) / c k)
            = ∑ k : Fin n,
              (fun m : ℕ => ((inner ℝ (e m) m_nu - inner ℝ (e m) m_mu) *
                (inner ℝ (e m) u - inner ℝ (e m) m_mu)) / c m) k :=
        Finset.sum_congr rfl (fun k _ => rfl)
      rw [hstep, Fin.sum_univ_eq_sum_range
        (fun m : ℕ => ((inner ℝ (e m) m_nu - inner ℝ (e m) m_mu) *
          (inner ℝ (e m) u - inner ℝ (e m) m_mu)) / c m) n]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have h1 : inner ℝ (e k) m_nu - inner ℝ (e k) m_mu = inner ℝ (e k) (m_nu - m_mu) :=
        (inner_sub_right (e k) m_nu m_mu).symm
      have h2 : inner ℝ (e k) u - inner ℝ (e k) m_mu = inner ℝ (e k) (u - m_mu) :=
        (inner_sub_right (e k) u m_mu).symm
      rw [h1, h2, div_eq_mul_inv]
      ring
    have hS2 :
        (∑ k : Fin n, (inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) ^ 2 / (2 * c k))
          = (∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2 := by
      have hstep :
          (∑ k : Fin n, (inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) ^ 2 / (2 * c k))
            = ∑ k : Fin n,
              (fun m : ℕ => (inner ℝ (e m) m_nu - inner ℝ (e m) m_mu) ^ 2 / (2 * c m)) k :=
        Finset.sum_congr rfl (fun k _ => rfl)
      rw [hstep, Fin.sum_univ_eq_sum_range
        (fun m : ℕ => (inner ℝ (e m) m_nu - inner ℝ (e m) m_mu) ^ 2 / (2 * c m)) n,
        Finset.sum_div]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have h1 : inner ℝ (e k) m_nu - inner ℝ (e k) m_mu = inner ℝ (e k) (m_nu - m_mu) :=
        (inner_sub_right (e k) m_nu m_mu).symm
      have hc : c k ≠ 0 := ne_of_gt (hc_pos k)
      rw [h1]
      field_simp
    have key :
        ((∑ k : Fin n,
            ((inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) *
                ((fun u : U => fun i : Fin n => inner ℝ (e i) u) u k
                  - inner ℝ (e k) m_mu)) / c k)
          - (∑ k : Fin n, (inner ℝ (e k) m_nu - inner ℝ (e k) m_mu) ^ 2 / (2 * c k)))
        = ((∑ k ∈ Finset.range n,
              (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
            - (∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2) := by
      rw [hS1, hS2]
    exact congrArg (fun r => ENNReal.ofReal (Real.exp r)) key
  have hcyl' : ∀ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C →
      nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C)
        = ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
            ENNReal.ofReal
              (Real.exp
                ((∑ k ∈ Finset.range n,
                    (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
                  - (∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)
                      / 2)) ∂mu := by
    intro n C hC
    rw [hcyl n C hC]
    simp only [hn_eq n]
  have hexp : ∀ᵐ u ∂mu, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
        - (∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2) atTop
      (𝓝 ((Filter.limsup
            (fun n : ℕ => ∑ k ∈ Finset.range n,
              (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
            atTop) - σ2 / 2)) := by
    filter_upwards [hlim] with u hu
    obtain ⟨L, hL⟩ := hu
    have hls : (Filter.limsup
        (fun n : ℕ => ∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu)) atTop) = L :=
      hL.limsup_eq
    rw [hls]
    exact hL.sub (hσ2n.div_const 2)
  have hconv_real : ∀ᵐ u ∂mu, Tendsto (fun n : ℕ =>
      Real.exp ((∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
        - (∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2)) atTop
      (𝓝 (Real.exp ((Filter.limsup
            (fun n : ℕ => ∑ k ∈ Finset.range n,
              (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
            atTop) - σ2 / 2))) := by
    filter_upwards [hexp] with u hu
    exact (Real.continuous_exp.continuousAt).tendsto.comp hu
  have hkey : nu = mu.withDensity rho :=
    statopia_math_node_3076668657_2d2dfc66 U e c hc_pos mu nu m_mu m_nu hmap_mu hsigma2 hlim
      hcyl'
  exact hkey
  /- @proof-region region.target-node.session.6b7911a3db1fe1ab end -/

end Statlib.Imported
end

