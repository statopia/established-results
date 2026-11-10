import Statlib.StatFoundation.BasicAnalysis.CompactSelfAdjoint
import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1715789988_72947f49_3e99b995
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2987999044_12269b33_978f3216
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3533682767_61f7e27b_99c420a2
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_412237305_0915aba3_c91723d3
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_4230448783_12afbf86_2cf22502
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_842457010_92ed615e_9ed0bfe8

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
theorem statopia_math_node_3664839893_07e7a1c0 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc : ∀ k : ℕ, 0 < c k)
    (μ : Measure U) [IsProbabilityMeasure μ]
    (hmu_gauss : ProbabilityTheory.IsGaussian μ)
    (ν : Measure U) [IsProbabilityMeasure ν]
    (hnu_gauss : ProbabilityTheory.IsGaussian ν)
    (mUM mNU : U)
    (hmean_mu : ∀ v : U, ∫ u, inner ℝ v u ∂μ = inner ℝ v mUM)
    (hmean_nu : ∀ v : U, ∫ u, inner ℝ v u ∂ν = inner ℝ v mNU)
    (hcov_mu : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) *
        (inner ℝ (e l) u - inner ℝ (e l) mUM) ∂μ = if k = l then c k else 0)
    (hcov_nu : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mNU) *
        (inner ℝ (e l) u - inner ℝ (e l) mNU) ∂ν = if k = l then c k else 0)
    (hint1_mu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2_mu : ∀ v w : U,
      Integrable (fun u : U => (inner ℝ v u - inner ℝ v mUM) * (inner ℝ w u - inner ℝ w mUM)) μ)
    (hint1_nu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) ν)
    (hint2_nu : ∀ v w : U,
      Integrable (fun u : U => (inner ℝ v u - inner ℝ v mNU) * (inner ℝ w u - inner ℝ w mNU)) ν)
    (hsum : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)),
    (let F : ℕ → MeasurableSpace U := fun n =>
        MeasurableSpace.comap (fun u : U => fun k : Fin n => inner ℝ (e k) (u - mUM))
          (by infer_instance)
      let h : ℕ → U → ℝ := fun n u =>
        Real.exp ((∑ k ∈ Finset.range n,
            (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)
      let sigma2 : ℝ := ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2
      (∀ n : ℕ,
          (∀ u : U, 0 < h n u) ∧
          Integrable (h n) μ ∧
          @Measurable U ℝ (F n) (by infer_instance) (h n)) ∧
        (⨆ n : ℕ, ∫⁻ u : U, (ENNReal.ofReal (h n u)) ^ 2 ∂μ ≤
          ENNReal.ofReal (Real.exp sigma2)) ∧
        (ENNReal.ofReal (Real.exp sigma2) < ⊤) ∧
        (∀ (n : ℕ) (B : Set U), @MeasurableSet U (F n) B →
          ∫ u in B, h (n + 1) u ∂μ = ∫ u in B, h n u ∂μ) ∧
        ∃ ρ : U → ℝ≥0∞,
          Measurable ρ ∧
          (∀ᵐ u ∂μ, Tendsto (fun n : ℕ => ENNReal.ofReal (h n u)) atTop (𝓝 (ρ u))) ∧
          Tendsto (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal |h n u - (ρ u).toReal| ∂μ)
            atTop (𝓝 0) ∧
          (∫⁻ u : U, ρ u ∂μ = 1) ∧
          (∫⁻ u : U, (ρ u) ^ 2 ∂μ = ENNReal.ofReal (Real.exp sigma2)) ∧
          (∀ᵐ u ∂μ, ∃ x : ℝ,
            Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
                (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
              atTop (𝓝 x) ∧
            ρ u = ENNReal.ofReal (Real.exp (x - sigma2 / 2)) ∧
            ρ u ≠ ⊤)) := by
  /- @proof-region region.target-node.session.d7159d6c6cfa4e93 begin -/
  intro U _ _ _ _ _ _ e c hc μ _ hmu_gauss ν _ hnu_gauss mUM mNU hmean_mu hmean_nu hcov_mu
    hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
  have hgnn : ∀ k : ℕ, 0 ≤ (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 := fun k =>
    mul_nonneg (le_of_lt (inv_pos.mpr (hc k))) (sq_nonneg _)
  have hsigma_nonneg : 0 ≤ ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 :=
    le_trans (hgnn 0)
      (Statlib.StatFoundation.BasicAnalysis.single_le_tsum_of_nonneg
        (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) 0 hgnn hsum)
  have hAn : ∀ n : ℕ, ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2
      ≤ ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 := by
    intro n
    have hENN :
        ENNReal.ofReal (∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)
          ≤ ENNReal.ofReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hgnn k),
        ENNReal.ofReal_tsum_of_nonneg hgnn hsum]
      exact ENNReal.sum_le_tsum _
    exact (ENNReal.ofReal_le_ofReal_iff hsigma_nonneg).1 hENN
  have hS : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)
      atTop (𝓝 (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) :=
    (hasSum_iff_tendsto_nat_of_nonneg hgnn _).1 hsum.hasSum
  have hmc : ∀ n : ℕ, @Measurable U ℝ
      (MeasurableSpace.comap (fun u : U => fun k : Fin n => inner ℝ (e k) (u - mUM))
        (inferInstance : MeasurableSpace (Fin n → ℝ)))
      (inferInstance : MeasurableSpace ℝ)
      (fun u : U => Real.exp ((∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
        - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) := by
    intro n
    set Gc : (Fin n → ℝ) → ℝ := fun x =>
        Real.exp ((∑ k : Fin n, (c (k : ℕ))⁻¹ * inner ℝ (e (k : ℕ)) (mNU - mUM) * x k)
          - (2 : ℝ)⁻¹ * ∑ k : Fin n, (c (k : ℕ))⁻¹ * (inner ℝ (e (k : ℕ)) (mNU - mUM)) ^ 2)
      with hGcdef
    have hGc : Measurable Gc := by
      rw [hGcdef]
      measurability
    have hkey : (fun u : U =>
          Real.exp ((∑ k ∈ Finset.range n,
            (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
            - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))
        = fun u : U => Gc (fun k : Fin n => inner ℝ (e (k : ℕ)) (u - mUM)) := by
      funext u
      rw [hGcdef]
      have hc1 :
          (∑ k : Fin n, (c (k : ℕ))⁻¹ * inner ℝ (e (k : ℕ)) (mNU - mUM) * inner ℝ (e (k : ℕ)) (u - mUM))
            = ∑ k ∈ Finset.range n, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM) :=
        Fin.sum_univ_eq_sum_range
          (fun k => (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) n
      have hc2 :
          (∑ k : Fin n, (c (k : ℕ))⁻¹ * (inner ℝ (e (k : ℕ)) (mNU - mUM)) ^ 2)
            = ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 :=
        Fin.sum_univ_eq_sum_range (fun k => (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) n
      show Real.exp ((∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)
        = Real.exp
          ((∑ k : Fin n, (c (k : ℕ))⁻¹ * inner ℝ (e (k : ℕ)) (mNU - mUM) * inner ℝ (e (k : ℕ)) (u - mUM))
            - (2 : ℝ)⁻¹ * ∑ k : Fin n, (c (k : ℕ))⁻¹ * (inner ℝ (e (k : ℕ)) (mNU - mUM)) ^ 2)
      rw [hc1, hc2]
    rw [hkey]
    intro s hs
    exact ⟨Gc ⁻¹' s, hGc hs, rfl⟩
  have hmart : ∀ (n : ℕ) (B : Set U),
      @MeasurableSet U
        (MeasurableSpace.comap (fun u : U => fun k : Fin n => inner ℝ (e k) (u - mUM))
          (inferInstance : MeasurableSpace (Fin n → ℝ))) B →
      ∫ u in B, Real.exp ((∑ k ∈ Finset.range (n + 1),
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
        - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1),
          (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) ∂μ
        = ∫ u in B, Real.exp ((∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
        - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) ∂μ := by
    intro n B hB
    obtain ⟨S, hS, hBS⟩ := hB
    set T : ({k : ℕ // k ∈ Finset.range n} → ℝ) → (Fin n → ℝ) :=
      fun g i => g ⟨(i : ℕ), Finset.mem_range.mpr i.2⟩ - inner ℝ (e (i : ℕ)) mUM with hT
    set R : ({k : ℕ // k ∈ Finset.range (n + 1)} → ℝ) → ({k : ℕ // k ∈ Finset.range n} → ℝ) :=
      fun g k => g ⟨(k : ℕ), Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp k.2))⟩
      with hR
    have hTmeas : Measurable T := by
      rw [hT]
      measurability
    have hRmeas : Measurable R := by
      rw [hR]
      measurability
    have hpt : ∀ u : U,
        T (R (fun k : {k : ℕ // k ∈ Finset.range (n + 1)} => inner ℝ (e (k : ℕ)) u))
          = fun i : Fin n => inner ℝ (e (i : ℕ)) (u - mUM) := by
      intro u
      funext i
      rw [hT, hR]
      simp only [inner_sub_right]
    have hBM : B = (fun u : U => fun k : {k : ℕ // k ∈ Finset.range (n + 1)} =>
          inner ℝ (e (k : ℕ)) u) ⁻¹' (R ⁻¹' (T ⁻¹' S)) := by
      rw [← hBS]
      ext u
      simp only [Set.mem_preimage]
      rw [hpt u]
    have hdep1 := statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
      hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
      (Finset.range (n + 1))
    have hdep0 := statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
      hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
      (Finset.range n)
    have hm1 : MeasurableSet (R ⁻¹' (T ⁻¹' S)) := (hS.preimage hTmeas).preimage hRmeas
    have hm0 : MeasurableSet (T ⁻¹' S) := hS.preimage hTmeas
    have hnu1 := hdep1.2.2.1 (R ⁻¹' (T ⁻¹' S)) hm1
    have hnu0 := hdep0.2.2.1 (T ⁻¹' S) hm0
    have hpt0 : ∀ u : U, T (fun k : {k : ℕ // k ∈ Finset.range n} => inner ℝ (e (k : ℕ)) u)
        = fun i : Fin n => inner ℝ (e (i : ℕ)) (u - mUM) := by
      intro u
      funext i
      rw [hT]
      simp only [inner_sub_right]
    have hset1 : (fun u : U => fun k : {k : ℕ // k ∈ Finset.range (n + 1)} =>
        inner ℝ (e (k : ℕ)) u) ⁻¹' (R ⁻¹' (T ⁻¹' S)) = B := hBM.symm
    have hset0 : (fun u : U => fun k : {k : ℕ // k ∈ Finset.range n} =>
        inner ℝ (e (k : ℕ)) u) ⁻¹' (T ⁻¹' S) = B := by
      rw [← hBS]
      ext u
      simp only [Set.mem_preimage]
      rw [hpt0 u]
    have hL1 : ∫⁻ u in B, ENNReal.ofReal (Real.exp ((∑ k ∈ Finset.range (n + 1),
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1),
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∂μ = ν B := by
      rw [← hset1]
      exact hnu1.symm
    have hL0 : ∫⁻ u in B, ENNReal.ofReal (Real.exp ((∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∂μ = ν B := by
      rw [← hset0]
      exact hnu0.symm
    have hL : ∫⁻ u in B, ENNReal.ofReal (Real.exp ((∑ k ∈ Finset.range (n + 1),
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1),
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∂μ
        = ∫⁻ u in B, ENNReal.ofReal (Real.exp ((∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∂μ := by
      rw [hL1, hL0]
    have hne1 : ν B ≠ ⊤ := by
      first
        | exact measure_ne_top ν B
        | exact ne_top_of_le_ne_top (by simp)
            (by simpa using measure_mono (Set.subset_univ B : B ⊆ Set.univ))
    have hi1 : Integrable (fun u : U => Real.exp ((∑ k ∈ Finset.range (n + 1),
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1),
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) (μ.restrict B) :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hdep1.1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => (hdep1.2.1 u).le)).1 (by
          rw [hL1]
          exact hne1)
    have hi0 : Integrable (fun u : U => Real.exp ((∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) (μ.restrict B) :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hdep0.1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => (hdep0.2.1 u).le)).1 (by
          rw [hL0]
          exact hne1)
    have hb1 : (∫⁻ u in B, ENNReal.ofReal (Real.exp ((∑ k ∈ Finset.range (n + 1),
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1),
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∂μ).toReal
        = ∫ u in B, Real.exp ((∑ k ∈ Finset.range (n + 1),
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1),
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) ∂μ :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
        (Filter.Eventually.of_forall fun u => (hdep1.2.1 u).le) hi1
    have hb0 : (∫⁻ u in B, ENNReal.ofReal (Real.exp ((∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∂μ).toReal
        = ∫ u in B, Real.exp ((∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) ∂μ :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
        (Filter.Eventually.of_forall fun u => (hdep0.2.1 u).le) hi0
    rw [← hb1, ← hb0, hL]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_, ?_⟩
    · exact (statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
        hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
        (Finset.range n)).2.1
    · have hdep := statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
        hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
        (Finset.range n)
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hdep.1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => (hdep.2.1 u).le)).1 ?_
      rw [hdep.2.2.2.1]
      simp
    · exact hmc n
  · refine iSup_le fun n => ?_
    rw [(statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
      hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
      (Finset.range n)).2.2.2.2]
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).2 (Real.exp_le_exp.2 (hAn n))
  · exact ENNReal.ofReal_lt_top
  · exact hmart
  · have hξmeas : ∀ k : ℕ, Measurable (fun u : U => inner ℝ (e k) (u - mUM)) := fun k =>
      ((innerSL ℝ (e k)).continuous.comp (continuous_id.sub continuous_const)).measurable
    have hξint : ∀ k : ℕ, Integrable (fun u : U => inner ℝ (e k) (u - mUM)) μ := fun k => by
      simpa only [inner_sub_right] using
        (hint1_mu (e k)).sub (integrable_const (inner ℝ (e k) mUM))
    have hξmean : ∀ k : ℕ, ∫ u : U, inner ℝ (e k) (u - mUM) ∂μ = 0 := fun k => by
      have h : ∫ u : U, (inner ℝ (e k) u - inner ℝ (e k) mUM) ∂μ = 0 := by
        rw [MeasureTheory.integral_sub (hint1_mu (e k)) (integrable_const _), hmean_mu (e k)]
        simp
      simpa only [inner_sub_right] using h
    have hξsq : ∀ k : ℕ, Integrable (fun u : U => (inner ℝ (e k) (u - mUM)) ^ 2) μ := fun k => by
      simpa only [inner_sub_right, pow_two] using hint2_mu (e k) (e k)
    have hcoord := statopia_math_node_412237305_0915aba3 U e c hc μ hmu_gauss mUM hmean_mu hcov_mu
      hint1_mu hint2_mu
    have hbmeas : ∀ k : ℕ,
        AEMeasurable (fun u : U =>
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) μ := fun k =>
      ((hξmeas k).const_mul ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM))).aemeasurable
    have hindep : iIndepFun
        (fun k : ℕ => fun u : U =>
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) μ :=
      hcoord.1.comp (fun k x => (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * x)
        (fun k => measurable_const.mul measurable_id)
    have hbint : ∀ k : ℕ,
        Integrable (fun u : U =>
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) μ := fun k =>
      (hξint k).const_mul ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM))
    have hbmean : ∀ k : ℕ,
        ∫ u : U, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM) ∂μ = 0 :=
      fun k => by
        rw [MeasureTheory.integral_const_mul, hξmean k, mul_zero]
    have hbsq : ∀ k : ℕ,
        Integrable (fun u : U =>
          ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) ^ 2) μ := fun k => by
      have h : Integrable (fun u : U =>
          ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM)))
            * (inner ℝ (e k) (u - mUM) ^ 2)) μ :=
        (hξsq k).const_mul
          ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM)))
      have hfc : (fun u : U =>
            ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) ^ 2)
          = fun u : U =>
            ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM)))
              * (inner ℝ (e k) (u - mUM) ^ 2) := funext fun u => by ring
      rw [hfc]
      exact h
    have hbvar : ∀ k : ℕ,
        ∫ u : U, ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) ^ 2 ∂μ
          = (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 := fun k => by
      have hsq : ∫ u : U, (inner ℝ (e k) (u - mUM)) ^ 2 ∂μ = c k := (hcoord.2.2.1 k).2
      have hfun : (fun u : U =>
            ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) ^ 2)
          = fun u : U =>
            ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM)))
              * (inner ℝ (e k) (u - mUM) ^ 2) := funext fun u => by ring
      rw [hfun, MeasureTheory.integral_const_mul, hsq]
      have hck : c k ≠ 0 := ne_of_gt (hc k)
      calc ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM))) * c k
          = ((c k)⁻¹ * (c k)⁻¹ * c k)
              * (inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (mNU - mUM)) := by
            ring
        _ = (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (mNU - mUM)) := by
            rw [mul_assoc (c k)⁻¹ (c k)⁻¹ (c k), inv_mul_cancel₀ hck, mul_one]
        _ = (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 := by rw [pow_two]
    have hscore : ∀ᵐ u ∂μ, ∃ x : ℝ, Tendsto (fun n : ℕ =>
        ∑ k ∈ Finset.range n, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
        atTop (𝓝 x) :=
      statopia_math_node_3533682767_61f7e27b U μ
        (fun k : ℕ => fun u : U => (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
        (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)
        hbmeas hindep hbint hbmean hbsq hbvar hgnn hsum
    have hfmeas : ∀ n : ℕ, Measurable (fun u : U => ∑ k ∈ Finset.range n,
        (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) := fun n => by
      clear hmc hmart hcoord hξint hξmean hξsq hbmeas hindep hbint hbmean hbsq hbvar hscore
      measurability
    obtain ⟨G, hG, hGconv⟩ := statopia_math_node_1715789988_72947f49 μ
      (fun n : ℕ => fun u : U => ∑ k ∈ Finset.range n,
        (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
      hfmeas hscore
    have hor : ∀ (g : ℕ → ℝ) (L : ℝ), 0 < L → Tendsto g atTop (𝓝 L) →
        Tendsto (fun n : ℕ => ENNReal.ofReal (g n)) atTop (𝓝 (ENNReal.ofReal L)) := by
      intro g L hL hg
      refine tendsto_order.2 ⟨?_, ?_⟩
      · intro a' ha'
        have htop : a' ≠ ⊤ := ne_of_lt (lt_trans ha' ENNReal.ofReal_lt_top)
        have h1 : ENNReal.ofReal a'.toReal < ENNReal.ofReal L := by
          rw [ENNReal.ofReal_toReal htop]
          exact ha'
        have h2 : a'.toReal < L := (ENNReal.ofReal_lt_ofReal_iff hL).1 h1
        filter_upwards [(tendsto_order.1 hg).1 a'.toReal h2,
          (tendsto_order.1 hg).1 0 hL] with n hn hn0
        rw [← ENNReal.ofReal_toReal htop]
        exact (ENNReal.ofReal_lt_ofReal_iff').2 ⟨hn, hn0⟩
      · intro a' ha'
        by_cases htop : a' = ⊤
        · rw [htop]
          exact Filter.Eventually.of_forall fun n => ENNReal.ofReal_lt_top
        · have h1 : ENNReal.ofReal L < ENNReal.ofReal a'.toReal := by
            rw [ENNReal.ofReal_toReal htop]
            exact ha'
          have h2 : L < a'.toReal := ((ENNReal.ofReal_lt_ofReal_iff').1 h1).1
          have h3 : 0 < a'.toReal := ((ENNReal.ofReal_lt_ofReal_iff').1 h1).2
          filter_upwards [(tendsto_order.1 hg).2 a'.toReal h2] with n hn
          rw [← ENNReal.ofReal_toReal htop]
          exact (ENNReal.ofReal_lt_ofReal_iff').2 ⟨hn, h3⟩
    set ρ : U → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (G u
      - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)) with hρ
    set hfun : ℕ → U → ℝ := fun n u => Real.exp ((∑ k ∈ Finset.range n,
        (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
        - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) with hhfun
    have haeconv : ∀ᵐ u ∂μ, Tendsto (fun n : ℕ => ENNReal.ofReal (hfun n u)) atTop (𝓝 (ρ u)) := by
      filter_upwards [hGconv] with u hgu
      have hρu : ρ u = ENNReal.ofReal (Real.exp (G u
          - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)) := by
        simp only [hρ]
      rw [hρu]
      refine hor (fun n : ℕ => Real.exp ((∑ k ∈ Finset.range n,
        (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
        - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))
        (Real.exp (G u - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2))
        (Real.exp_pos _) ?_
      have h1 : Tendsto (fun n : ℕ =>
          (∑ k ∈ Finset.range n, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
            - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
              (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) atTop
          (𝓝 (G u - (2 : ℝ)⁻¹ * (∑' k : ℕ,
            (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) := by
        have h := hgu.add (hS.const_mul (-(2 : ℝ)⁻¹))
        simpa [sub_eq_add_neg, neg_mul] using h
      have h2 := (Real.continuous_exp.tendsto _).comp h1
      have hT : (2 : ℝ)⁻¹ * (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)
          = (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2 := by ring
      rw [hT] at h2
      exact h2
    have hvitali := statopia_math_node_4230448783_12afbf86 μ hfun ρ
      (ENNReal.ofReal (Real.exp (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)))
      (fun n => by
        have h : Measurable (fun u : U => hfun n u) :=
          Real.continuous_exp.measurable.comp ((hfmeas n).sub measurable_const)
        exact h.aemeasurable)
      (fun n => Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
      (fun n => (statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
        hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
        (Finset.range n)).2.2.2.1)
      (fun n => by
        have hgoal : ∫⁻ u : U, (ENNReal.ofReal (hfun n u)) ^ 2 ∂μ
            = ENNReal.ofReal (Real.exp (∑ k ∈ Finset.range n,
                (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) :=
          (statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
            hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
            (Finset.range n)).2.2.2.2
        rw [hgoal]
        exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).2 (Real.exp_le_exp.2 (hAn n)))
      haeconv (ne_of_lt ENNReal.ofReal_lt_top)
    refine ⟨ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hρ]
      exact ENNReal.measurable_ofReal.comp
        ((Real.continuous_exp.measurable).comp (hG.sub measurable_const))
    · exact haeconv
    · exact hvitali.1
    · exact hvitali.2
    · have hcme : ∀ n : ℕ, Measurable (fun u : U => fun k : Fin n => inner ℝ (e k) (u - mUM)) :=
        fun n => measurable_pi_iff.2 fun k => hξmeas k
      have hFle : ∀ n : ℕ,
          MeasurableSpace.comap (fun u : U => fun k : Fin n => inner ℝ (e k) (u - mUM))
            (inferInstance : MeasurableSpace (Fin n → ℝ))
          ≤ (inferInstance : MeasurableSpace U) := by
        intro n
        rw [MeasurableSpace.le_def]
        intro S hS
        obtain ⟨T, hT, rfl⟩ := hS
        exact hT.preimage (hcme n)
      have hFmono : ∀ n : ℕ,
          MeasurableSpace.comap (fun u : U => fun k : Fin n => inner ℝ (e k) (u - mUM))
            (inferInstance : MeasurableSpace (Fin n → ℝ))
          ≤ MeasurableSpace.comap (fun u : U => fun k : Fin (n + 1) => inner ℝ (e k) (u - mUM))
            (inferInstance : MeasurableSpace (Fin (n + 1) → ℝ)) := by
        intro n
        rw [MeasurableSpace.le_def]
        intro S hS
        obtain ⟨T, hT, rfl⟩ := hS
        exact ⟨(fun g : Fin (n + 1) → ℝ => fun k : Fin n =>
            g ⟨(k : ℕ), Nat.lt_succ_of_lt k.2⟩) ⁻¹' T,
          hT.preimage (measurable_pi_iff.2 fun k =>
            (measurable_pi_apply (⟨(k : ℕ), Nat.lt_succ_of_lt k.2⟩ : Fin (n + 1))
              : Measurable (fun g : Fin (n + 1) → ℝ =>
                  g ⟨(k : ℕ), Nat.lt_succ_of_lt k.2⟩))), rfl⟩
      have hpt : ∀ n : ℕ, (fun u : U => ENNReal.ofReal ((hfun n u) ^ 2))
          = fun u : U => (ENNReal.ofReal (hfun n u)) ^ 2 := fun n =>
        funext fun u => ENNReal.ofReal_pow (Real.exp_pos _).le 2
      have hL2 : ∀ n : ℕ, ∫⁻ u : U, (ENNReal.ofReal (hfun n u)) ^ 2 ∂μ
          = ENNReal.ofReal (Real.exp (∑ k ∈ Finset.range n,
              (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) := fun n =>
        (statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
          hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
          (Finset.range n)).2.2.2.2
      have hint : ∀ n : ℕ, Integrable (fun u : U => (hfun n u) ^ 2) μ := by
        intro n
        have hm : Measurable (fun u : U => hfun n u) :=
          Real.continuous_exp.measurable.comp ((hfmeas n).sub measurable_const)
        refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
          (f := fun u : U => (hfun n u) ^ 2)
          (by simpa only [pow_two] using (hm.mul hm).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun u => sq_nonneg (hfun n u))).1 ?_
        rw [hpt n, hL2 n]
        exact ENNReal.ofReal_lt_top.ne
      have hmom : Tendsto (fun n : ℕ => ∫ u : U, (hfun n u) ^ 2 ∂μ) atTop
          (𝓝 (Real.exp (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) := by
        have hval : ∀ n : ℕ, ∫ u : U, (hfun n u) ^ 2 ∂μ
            = Real.exp (∑ k ∈ Finset.range n,
                (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) := by
          intro n
          rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
            (Filter.Eventually.of_forall fun u => sq_nonneg (hfun n u)) (hint n)]
          rw [hpt n, hL2 n, ENNReal.toReal_ofReal (Real.exp_pos _).le]
        simpa only [hval] using
          (Real.continuous_exp.tendsto
            (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)).comp hS
      exact statopia_math_node_2987999044_12269b33 (U) (μ)
        (fun n : ℕ => MeasurableSpace.comap (fun u : U => fun k : Fin n => inner ℝ (e k) (u - mUM))
          (inferInstance : MeasurableSpace (Fin n → ℝ)))
        hFmono hFle hfun ρ
        (Real.exp (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))
        hmc hint hmart
        (fun n => Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
        hmom haeconv
    · filter_upwards [hscore, hGconv] with u hu hgu
      refine ⟨G u, hgu, ?_, ?_⟩
      · simp only [hρ]
      · have hρu : ρ u = ENNReal.ofReal (Real.exp (G u
            - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)) := by
          simp only [hρ]
        rw [hρu]
        exact ne_of_lt ENNReal.ofReal_lt_top
  /- @proof-region region.target-node.session.d7159d6c6cfa4e93 end -/

end Statlib.Imported
end

