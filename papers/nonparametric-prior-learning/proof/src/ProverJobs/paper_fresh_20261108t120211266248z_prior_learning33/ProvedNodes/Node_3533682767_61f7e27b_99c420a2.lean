import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

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
theorem statopia_math_node_3533682767_61f7e27b : ∀ (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ)
    (hX_meas : ∀ k : ℕ, AEMeasurable (X k) μ)
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_int : ∀ k : ℕ, Integrable (X k) μ)
    (hX_mean : ∀ k : ℕ, ∫ ω, X k ω ∂μ = 0)
    (hX_sq_int : ∀ k : ℕ, Integrable (fun ω => (X k ω) ^ 2) μ)
    (hX_var : ∀ k : ℕ, ∫ ω, (X k ω) ^ 2 ∂μ = v k)
    (hv_nonneg : ∀ k : ℕ, 0 ≤ v k)
    (hv_summable : Summable v),
    ∀ᵐ ω ∂μ, ∃ x : ℝ,
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, X k ω) atTop (𝓝 x) := by
  /- @proof-region region.target-node.session.33ffdb0d003c4b88 begin -/
  intro Ω instΩ μ instμ X v hX_meas hX_indep hX_int hX_mean hX_sq_int hX_var hv_nonneg hv_summable
  let Y : ℕ → Ω → ℝ := fun k => (hX_meas k).choose
  have hY_meas : ∀ k, Measurable (Y k) := fun k => (hX_meas k).choose_spec.1
  have hY_ae : ∀ k, X k =ᵐ[μ] Y k := fun k => (hX_meas k).choose_spec.2
  have hY_sm : ∀ k, StronglyMeasurable (Y k) := fun k => (hY_meas k).stronglyMeasurable
  have hY_indep : iIndepFun Y μ := hX_indep.congr (fun k => hY_ae k)
  let T : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range (n+1), Y k ω
  let ℱ : Filtration ℕ instΩ := Filtration.natural Y hY_sm
  have hY_int : ∀ k, Integrable (Y k) μ := fun k => (hX_int k).congr (hY_ae k)
  have hY_mean : ∀ k, ∫ ω, Y k ω ∂μ = 0 := fun k => by
    rw [← integral_congr_ae (hY_ae k)]
    exact hX_mean k
  have hY_sq : ∀ k, Integrable (fun ω => (Y k ω) ^ 2) μ := fun k => by
    refine (hX_sq_int k).congr ?_
    filter_upwards [hY_ae k] with ω hh
    rw [hh]
  have hY_var : ∀ k, ∫ ω, (Y k ω) ^ 2 ∂μ = v k := fun k => by
    have h : (fun ω => (Y k ω) ^ 2) =ᵐ[μ] (fun ω => (X k ω) ^ 2) := by
      filter_upwards [hY_ae k] with ω hh
      rw [hh]
    rw [integral_congr_ae h, hX_var k]
  have hY_memLp : ∀ k, MemLp (Y k) 2 μ := fun k =>
    (memLp_two_iff_integrable_sq (hY_meas k).aestronglyMeasurable).mpr (hY_sq k)
  have hVarY : ∀ k, variance (Y k) μ = v k := fun k => by
    have h2 := variance_eq_sub (X := Y k) (hY_memLp k)
    rw [hY_mean k] at h2
    simp only [Pi.pow_apply] at h2
    norm_num at h2
    rw [hY_var k] at h2
    exact h2
  have hVarSum : ∀ s : Finset ℕ, variance (∑ i ∈ s, Y i) μ = ∑ k ∈ s, v k := by
    intro s
    rw [IndepFun.variance_sum (fun i _ => hY_memLp i) (fun i _ j _ hij => hY_indep.indepFun hij)]
    exact Finset.sum_congr rfl (fun k _ => hVarY k)
  have hsecond : ∀ s : Finset ℕ, ∫ ω, (∑ k ∈ s, Y k ω) ^ 2 ∂μ = ∑ k ∈ s, v k := by
    intro s
    have hmem : MemLp (∑ k ∈ s, Y k) 2 μ := memLp_finset_sum' s (fun i _ => hY_memLp i)
    have h1 : ∫ ω, ∑ k ∈ s, Y k ω ∂μ = 0 := by
      rw [integral_finset_sum]
      · simp [hY_mean]
      · exact fun k _ => hY_int k
    have h2 := variance_eq_sub (X := ∑ k ∈ s, Y k) hmem
    simp only [Pi.pow_apply, Finset.sum_apply] at h2
    rw [hVarSum s, h1] at h2
    simp at h2
    exact h2.symm
  have hT_int : ∀ n, Integrable (T n) μ := by
    intro n
    exact integrable_finset_sum (Finset.range (n+1)) (fun k _ => hY_int k)
  have hFi : ∀ i : ℕ, ℱ i = ⨆ j, ⨆ (_ : j ≤ i), MeasurableSpace.comap (Y j) Real.measurableSpace :=
    fun i => rfl
  have hYmeas : ∀ k i : ℕ, k ≤ i → Measurable[ℱ i] (Y k) := by
    intro k i hki
    have hck : MeasurableSpace.comap (Y k) Real.measurableSpace ≤ ℱ i := by
      rw [hFi i]
      exact le_trans
        (le_iSup (fun _ : k ≤ i => MeasurableSpace.comap (Y k) Real.measurableSpace) hki)
        (le_iSup (fun j => ⨆ (_ : j ≤ i), MeasurableSpace.comap (Y j) Real.measurableSpace) k)
    exact measurable_iff_comap_le.mpr hck
  have hT_adapt : StronglyAdapted ℱ T := by
    intro i
    exact (Finset.measurable_sum (Finset.range (i+1))
      (fun k hk => hYmeas k i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))).stronglyMeasurable
  have hT_cond : ∀ i j : ℕ, i ≤ j → T i =ᵐ[μ] μ[T j | ℱ i] := by
    intro i j hij
    have hbridge : T j = ∑ i ∈ Finset.range (j+1), Y i := by
      funext ω
      show (∑ k ∈ Finset.range (j+1), Y k ω) = (∑ i ∈ Finset.range (j+1), Y i) ω
      rw [Finset.sum_apply]
    have h1 : μ[T j | ℱ i] =ᵐ[μ] ∑ k ∈ Finset.range (j+1), μ[Y k | ℱ i] := by
      rw [hbridge]
      exact condExp_finset_sum (fun k _ => hY_int k) (ℱ i)
    have hterm : ∀ k : ℕ, ∀ᵐ ω ∂μ, μ[Y k | ℱ i] ω = if k ≤ i then Y k ω else 0 := by
      intro k
      by_cases hk : k ≤ i
      · have h : μ[Y k | ℱ i] = Y k :=
          condExp_of_stronglyMeasurable (ℱ.le i) (hYmeas k i hk).stronglyMeasurable (hY_int k)
        filter_upwards with ω
        rw [h, if_pos hk]
      · have h : μ[Y k | ℱ i] =ᵐ[μ] fun _ => ∫ ω, Y k ω ∂μ :=
          iIndepFun.condExp_natural_ae_eq_of_lt (f := Y) hY_sm hY_indep (not_le.mp hk)
        filter_upwards [h] with ω hω
        rw [hω, hY_mean k, if_neg hk]
    have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, μ[Y k | ℱ i] ω = if k ≤ i then Y k ω else 0 :=
      MeasureTheory.ae_all_iff.mpr hterm
    have h2 : (∑ k ∈ Finset.range (j+1), μ[Y k | ℱ i]) =ᵐ[μ] T i := by
      filter_upwards [hall] with ω hcase
      simp only [Finset.sum_apply]
      have hstep : ∑ k ∈ Finset.range (j+1), μ[Y k | ℱ i] ω
          = ∑ k ∈ Finset.range (j+1), (if k ≤ i then Y k ω else 0) :=
        Finset.sum_congr rfl (fun k _ => hcase k)
      have hsub : Finset.range (i+1) ⊆ Finset.range (j+1) := by
        intro k hk
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ hij))
      have hzero : ∀ k ∈ Finset.range (j+1), k ∉ Finset.range (i+1) →
          (if k ≤ i then Y k ω else 0) = 0 := by
        intro k _ hk2
        rw [if_neg]
        intro hki
        exact hk2 (Finset.mem_range.mpr (Nat.lt_succ_of_le hki))
      have hone : ∀ k ∈ Finset.range (i+1), (if k ≤ i then Y k ω else 0) = Y k ω := by
        intro k hk
        rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
      calc ∑ k ∈ Finset.range (j+1), μ[Y k | ℱ i] ω
          = ∑ k ∈ Finset.range (j+1), (if k ≤ i then Y k ω else 0) := hstep
        _ = ∑ k ∈ Finset.range (i+1), (if k ≤ i then Y k ω else 0) :=
            (Finset.sum_subset hsub hzero).symm
        _ = ∑ k ∈ Finset.range (i+1), Y k ω := Finset.sum_congr rfl hone
    exact (h1.trans h2).symm
  have hsub : Submartingale T ℱ μ :=
    ⟨hT_adapt, fun i j hij => (hT_cond i j hij).le, hT_int⟩
  have hTendsto : ∀ᵐ ω ∂μ, ∃ x : ℝ, Tendsto (fun n : ℕ => T n ω) atTop (𝓝 x) := by
    have hlim : Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m, v k) atTop (𝓝 (∑' k, v k)) :=
      hv_summable.hasSum.tendsto_sum_nat
    have hSnn : 0 ≤ ∑' k, v k :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (Eventually.of_forall fun m => Finset.sum_nonneg fun k _ => hv_nonneg k)
    have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range (n+1), v k ≤ ∑' k, v k := by
      intro n
      refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
      filter_upwards [eventually_ge_atTop (n+1)] with m hm
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hv_nonneg k)
      intro k hk
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hm)
    set W : ℝ := (∑' k, v k) ^ (2:ℝ)⁻¹ with hWdef
    have hWnn : 0 ≤ W := Real.rpow_nonneg hSnn (2:ℝ)⁻¹
    refine hsub.exists_ae_tendsto_of_bdd (R := ⟨W, hWnn⟩) ?_
    intro n
    have key : eLpNorm (T n) 1 μ ≤ ENNReal.ofReal W := by
      have hMp' : MemLp (∑ i ∈ Finset.range (n+1), Y i) 2 μ :=
        memLp_finset_sum' (Finset.range (n+1)) (fun k _ => hY_memLp k)
      have hTeq : T n = ∑ i ∈ Finset.range (n+1), Y i := by
        funext ω
        show (∑ k ∈ Finset.range (n+1), Y k ω) = (∑ i ∈ Finset.range (n+1), Y i) ω
        rw [Finset.sum_apply]
      have hMp : MemLp (T n) 2 μ := hTeq.symm ▸ hMp'
      have hmeas : Measurable (T n) :=
        Finset.measurable_sum (Finset.range (n+1)) (fun k _ => hY_meas k)
      have h12 : eLpNorm (T n) 1 μ ≤ eLpNorm (T n) 2 μ := by
        have h := MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (f := T n)
          (p := 1) (q := 2) (by norm_num) hmeas.aestronglyMeasurable
        simpa using h
      refine le_trans h12 ?_
      have heq : eLpNorm (T n) 2 μ
          = ENNReal.ofReal ((∫ ω, ‖T n ω‖ ^ (2:ℝ) ∂μ) ^ (2:ℝ)⁻¹) := by
        have h := MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (μ := μ) (f := T n) (p := 2)
          (by norm_num) (by norm_num) hMp
        simpa using h
      have hInt : ∫ ω, ‖T n ω‖ ^ (2:ℝ) ∂μ = ∑ k ∈ Finset.range (n+1), v k := by
        have hc : (fun ω => ‖T n ω‖ ^ (2:ℝ)) = fun ω => (T n ω) ^ 2 := by
          funext ω
          simp [Real.norm_eq_abs, sq_abs]
        rw [hc]
        exact hsecond (Finset.range (n+1))
      rw [heq, hInt]
      refine ENNReal.ofReal_le_ofReal ?_
      exact Real.rpow_le_rpow (Finset.sum_nonneg fun k _ => hv_nonneg k) (hpart n) (by norm_num)
    exact key.trans (le_of_eq (ENNReal.ofReal_eq_coe_nnreal hWnn))
  have hae : ∀ᵐ ω ∂μ, ∀ k : ℕ, X k ω = Y k ω := MeasureTheory.ae_all_iff.mpr hY_ae
  have hshift : ∀ᵐ ω ∂μ, ∃ x : ℝ, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n+1), X k ω) atTop (𝓝 x) := by
    filter_upwards [hTendsto, hae] with ω hω hXY
    obtain ⟨x, hx⟩ := hω
    refine ⟨x, ?_⟩
    have hfun : (fun n : ℕ => ∑ k ∈ Finset.range (n+1), X k ω) = (fun n : ℕ => T n ω) := by
      funext n
      exact Finset.sum_congr rfl (fun k _ => hXY k)
    rw [hfun]
    exact hx
  filter_upwards [hshift] with ω hω
  obtain ⟨x, hx⟩ := hω
  exact ⟨x, (tendsto_add_atTop_iff_nat 1).mp hx⟩
  /- @proof-region region.target-node.session.33ffdb0d003c4b88 end -/

end Statlib.Imported
end

