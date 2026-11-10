import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3664839893_07e7a1c0_85f524ed
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
theorem statopia_math_node_1939896492_b20f2010 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
    (hsum : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))
    (ρ : U → ℝ≥0∞) (hρ_meas : Measurable ρ)
    (hρ_limit : ∀ᵐ u ∂μ,
      Tendsto (fun n : ℕ => ENNReal.ofReal
        (Real.exp ((∑ k ∈ Finset.range n,
            (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
              (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) atTop (𝓝 (ρ u)))
    (F : Finset ℕ) (B : Set ({k : ℕ // k ∈ F} → ℝ)) (hB : MeasurableSet B),
    ∫⁻ u in {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ∈ B}, ρ u ∂μ
      = ν {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ∈ B} := by
  /- @proof-region region.target-node.session.1216f0779453d5fa begin -/
  intro U _ _ _ _ _ _ e c hc μ _ hmu_gauss ν _ hnu_gauss mUM mNU hmean_mu hmean_nu
    hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum ρ hρ_meas hρ_limit F B hB
  set hFn : ℕ → U → ℝ := (fun n u => Real.exp ((∑ k ∈ Finset.range n,
        ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM)) * inner ℝ (e k) (u - mUM))
      - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) with hhFn
  set A : Set U := {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ∈ B} with hA
  obtain ⟨m, hFm⟩ : ∃ m : ℕ, ∀ k ∈ F, k ∈ Finset.range m := by
    refine ⟨F.sup id + 1, fun k hk => ?_⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  set proj : ({k : ℕ // k ∈ Finset.range m} → ℝ) → ({k : ℕ // k ∈ F} → ℝ) :=
    fun x k => x ⟨k.1, hFm k.1 k.2⟩ with hproj
  set B' : Set ({k : ℕ // k ∈ Finset.range m} → ℝ) := proj ⁻¹' B with hB'
  set S : Set U := {u : U | (fun k : {k : ℕ // k ∈ Finset.range m} => inner ℝ (e k) u) ∈ B'} with hS
  have hproj_coord : ∀ u : U, proj (fun k : {k : ℕ // k ∈ Finset.range m} => inner ℝ (e k) u)
      = (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) := by
    intro u
    funext k
    simp [hproj]
  have hSA : S = A := by
    ext u
    rw [hS, hA]
    simp only [Set.mem_setOf_eq, hB', Set.mem_preimage]
    rw [hproj_coord u]
  have hproj_meas : Measurable proj := by
    rw [hproj]
    refine measurable_pi_iff.mpr fun k => ?_
    exact measurable_pi_apply (X := fun _ => ℝ)
      (⟨k.1, hFm k.1 k.2⟩ : {k : ℕ // k ∈ Finset.range m})
  have hB'meas : MeasurableSet B' := by
    rw [hB']
    exact hproj_meas hB
  have hAmeas : MeasurableSet A := by
    rw [hA]
    have hcyl : Measurable fun u : U => (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) := by
      refine measurable_pi_iff.mpr fun k => ?_
      simpa only [coe_innerSL_apply] using (innerSL ℝ (e k)).continuous.measurable
    exact hcyl hB
  obtain ⟨hD2mono, -, -, hD2comap, ρ', -, hρ'ae, -, hρ'int, -, -⟩ :=
    statopia_math_node_3664839893_07e7a1c0 U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
      hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
  obtain ⟨-, -, hD1den, -, -⟩ :=
    statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
      hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum (Finset.range m)
  have hFn_meas : ∀ n : ℕ, Measurable (fun u : U => ENNReal.ofReal (hFn n u)) := by
    intro n
    exact (statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
      hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
      (Finset.range n)).1.ennreal_ofReal
  have hD1int_n : ∀ n : ℕ, ∫⁻ u : U, ENNReal.ofReal (hFn n u) ∂μ = 1 :=
    fun n => (statopia_math_node_842457010_92ed615e U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
      hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
      (Finset.range n)).2.2.2.1
  have hshift : ∀ (v u : U), inner ℝ v (u - mUM) + inner ℝ v mUM = inner ℝ v u := by
    intro v u
    rw [inner_sub_right]
    ring
  have hSmeas : ∀ k : ℕ, m ≤ k →
      MeasurableSet[MeasurableSpace.comap
        (fun u : U => fun j : Fin k => inner ℝ (e (j : ℕ)) (u - mUM))
        (inferInstance : MeasurableSpace (Fin k → ℝ))] S := by
    intro k hk
    have hlt : ∀ j : {j : ℕ // j ∈ Finset.range m}, j.1 < k := by
      intro j
      have hj := Finset.mem_range.mp j.2
      omega
    set Tk : Set (Fin k → ℝ) :=
      {x | (fun j : {j : ℕ // j ∈ Finset.range m} => x ⟨j.1, hlt j⟩ + inner ℝ (e j) mUM) ∈ B'}
      with hTk
    have hTk_meas : MeasurableSet Tk := by
      rw [hTk]
      have hmap : Measurable fun x : Fin k → ℝ =>
          (fun j : {j : ℕ // j ∈ Finset.range m} => x ⟨j.1, hlt j⟩ + inner ℝ (e j) mUM) := by
        refine measurable_pi_iff.mpr fun j => ?_
        exact (measurable_pi_apply (X := fun _ => ℝ) (⟨j.1, hlt j⟩ : Fin k)).add measurable_const
      exact hmap hB'meas
    have hSeq : S = (fun u : U => fun j : Fin k => inner ℝ (e (j : ℕ)) (u - mUM)) ⁻¹' Tk := by
      rw [hS, hTk]
      ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      have hfun : (fun j : {j : ℕ // j ∈ Finset.range m} =>
          inner ℝ (e ((⟨j.1, hlt j⟩ : Fin k) : ℕ)) (u - mUM) + inner ℝ (e j) mUM)
          = (fun j : {j : ℕ // j ∈ Finset.range m} => inner ℝ (e j) u) := by
        funext j
        exact hshift (e j) u
      rw [hfun]
    rw [hSeq]
    exact (measurable_iff_comap_le.mpr le_rfl) hTk_meas
  have hstep : ∀ k : ℕ, m ≤ k →
      ∫⁻ u in S, ENNReal.ofReal (hFn (k + 1) u) ∂μ = ∫⁻ u in S, ENNReal.ofReal (hFn k u) ∂μ := by
    intro k hk
    have hreal : ∫ u in S, hFn (k + 1) u ∂μ = ∫ u in S, hFn k u ∂μ :=
      hD2comap k S (hSmeas k hk)
    have hfin : ∀ j : ℕ, Integrable (hFn j) (μ.restrict S) :=
      fun j => ((hD2mono j).2.1).mono_measure Measure.restrict_le_self
    have hnn : ∀ j : ℕ, 0 ≤ᵐ[μ.restrict S] hFn j :=
      fun j => ae_restrict_of_ae (Filter.Eventually.of_forall fun u => le_of_lt ((hD2mono j).1 u))
    have hb1 : ENNReal.ofReal (∫ u in S, hFn (k + 1) u ∂μ)
        = ∫⁻ u in S, ENNReal.ofReal (hFn (k + 1) u) ∂μ :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfin (k + 1)) (hnn (k + 1))
    have hb2 : ENNReal.ofReal (∫ u in S, hFn k u ∂μ)
        = ∫⁻ u in S, ENNReal.ofReal (hFn k u) ∂μ :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfin k) (hnn k)
    rw [← hb1, ← hb2, hreal]
  have hmart : ∀ n : ℕ, m ≤ n →
      ∫⁻ u in S, ENNReal.ofReal (hFn n u) ∂μ = ∫⁻ u in S, ENNReal.ofReal (hFn m u) ∂μ :=
    fun n hn => Nat.le_induction rfl (fun k _ ih => by rw [hstep k ‹m ≤ k›, ih]) n hn
  have hvalA : ∀ n : ℕ, m ≤ n → ∫⁻ u in A, ENNReal.ofReal (hFn n u) ∂μ = ν A := by
    intro n hn
    have h2 : ∫⁻ u in S, ENNReal.ofReal (hFn n u) ∂μ
        = ∫⁻ u in S, ENNReal.ofReal (hFn m u) ∂μ := hmart n hn
    have h3 : ∫⁻ u in S, ENNReal.ofReal (hFn m u) ∂μ = ν S := by
      rw [hS, hD1den B' hB'meas]
    have h1 : ∫⁻ u in A, ENNReal.ofReal (hFn n u) ∂μ
        = ∫⁻ u in S, ENNReal.ofReal (hFn n u) ∂μ := by rw [hSA]
    rw [h1, h2, h3, hSA]
  have hble : ∫⁻ u in A, ENNReal.ofReal (hFn m u) ∂μ ≤ 1 := by
    calc ∫⁻ u in A, ENNReal.ofReal (hFn m u) ∂μ
        ≤ ∫⁻ u in Set.univ, ENNReal.ofReal (hFn m u) ∂μ := lintegral_mono_set (Set.subset_univ A)
      _ = ∫⁻ u, ENNReal.ofReal (hFn m u) ∂μ := setLIntegral_univ _
      _ = 1 := hD1int_n m
  have hνA_eq : ν A = ∫⁻ u in A, ENNReal.ofReal (hFn m u) ∂μ := (hvalA m le_rfl).symm
  have hcm_le : ν A ≤ 1 := by
    rw [hνA_eq]
    exact hble
  have hcm_top : ν A ≠ ⊤ := by
    rw [hνA_eq]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hble
  have hcompl_val : ∀ n : ℕ, m ≤ n → ∫⁻ u in Aᶜ, ENNReal.ofReal (hFn n u) ∂μ = 1 - ν A := by
    intro n hn
    rw [setLIntegral_compl (s := A) (f := fun u => ENNReal.ofReal (hFn n u)) hAmeas
      (by rw [hvalA n hn]; exact hcm_top)]
    rw [hvalA n hn, hD1int_n n]
  have hρρ' : ρ =ᵐ[μ] ρ' := by
    filter_upwards [hρ_limit, hρ'ae] with u hu hu'
    exact tendsto_nhds_unique hu hu'
  have hAA : ∫⁻ u in A, ρ u ∂μ = ∫⁻ u in A, ρ' u ∂μ := by
    refine lintegral_congr_ae ?_
    exact ae_restrict_of_ae hρρ'
  have hFatouA : ∫⁻ u in A, ρ' u ∂μ ≤ ν A := by
    have hmain := lintegral_liminf_le (μ := μ.restrict A)
      (f := fun n u => ENNReal.ofReal (hFn (n + m) u)) (fun n => hFn_meas (n + m))
    have hlim : ∫⁻ a, Filter.liminf (fun n => ENNReal.ofReal (hFn (n + m) a)) atTop ∂(μ.restrict A)
        = ∫⁻ a, ρ' a ∂(μ.restrict A) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hρ'ae] with a ha
      have hcomp : Tendsto (fun n : ℕ => ENNReal.ofReal (hFn (n + m) a)) atTop (𝓝 (ρ' a)) :=
        ha.comp (tendsto_add_atTop_nat m)
      exact hcomp.liminf_eq
    have hseq : (fun n => ∫⁻ a, ENNReal.ofReal (hFn (n + m) a) ∂(μ.restrict A))
        = fun _ => ν A := by
      funext n
      exact hvalA (n + m) (Nat.le_add_left m n)
    have hlim2 : Filter.liminf (fun n => ∫⁻ a, ENNReal.ofReal (hFn (n + m) a) ∂(μ.restrict A)) atTop
        = ν A := by
      rw [hseq]
      exact tendsto_const_nhds.liminf_eq
    rw [hlim, hlim2] at hmain
    exact hmain
  have hFatouAc : ∫⁻ u in Aᶜ, ρ' u ∂μ ≤ 1 - ν A := by
    have hmain := lintegral_liminf_le (μ := μ.restrict Aᶜ)
      (f := fun n u => ENNReal.ofReal (hFn (n + m) u)) (fun n => hFn_meas (n + m))
    have hlim : ∫⁻ a, Filter.liminf (fun n => ENNReal.ofReal (hFn (n + m) a)) atTop ∂(μ.restrict Aᶜ)
        = ∫⁻ a, ρ' a ∂(μ.restrict Aᶜ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hρ'ae] with a ha
      have hcomp : Tendsto (fun n : ℕ => ENNReal.ofReal (hFn (n + m) a)) atTop (𝓝 (ρ' a)) :=
        ha.comp (tendsto_add_atTop_nat m)
      exact hcomp.liminf_eq
    have hseq : (fun n => ∫⁻ a, ENNReal.ofReal (hFn (n + m) a) ∂(μ.restrict Aᶜ))
        = fun _ => 1 - ν A := by
      funext n
      exact hcompl_val (n + m) (Nat.le_add_left m n)
    have hlim2 : Filter.liminf (fun n => ∫⁻ a, ENNReal.ofReal (hFn (n + m) a) ∂(μ.restrict Aᶜ)) atTop
        = 1 - ν A := by
      rw [hseq]
      exact tendsto_const_nhds.liminf_eq
    rw [hlim, hlim2] at hmain
    exact hmain
  have hxtop : ∫⁻ u in A, ρ' u ∂μ ≠ ⊤ := ne_top_of_le_ne_top hcm_top hFatouA
  have hx_le_1 : ∫⁻ u in A, ρ' u ∂μ ≤ 1 := le_trans hFatouA hcm_le
  have hyx : ∫⁻ u in Aᶜ, ρ' u ∂μ = 1 - ∫⁻ u in A, ρ' u ∂μ := by
    have h := setLIntegral_compl (s := A) (f := ρ') hAmeas hxtop
    rw [hρ'int] at h
    exact h
  have hxy : ∫⁻ u in A, ρ' u ∂μ + ∫⁻ u in Aᶜ, ρ' u ∂μ = 1 := by
    rw [hyx]
    exact add_tsub_cancel_of_le hx_le_1
  have hcm_split : ν A + (1 - ν A) = 1 := add_tsub_cancel_of_le hcm_le
  have hy_top : ∫⁻ u in Aᶜ, ρ' u ∂μ ≠ ⊤ := by
    intro h
    have h1 := hxy
    rw [h, add_top] at h1
    exact ENNReal.one_ne_top h1.symm
  have hmid_le : ν A + ∫⁻ u in Aᶜ, ρ' u ∂μ ≤ ν A + (1 - ν A) :=
    add_le_add le_rfl hFatouAc
  have hmid_ge : ν A + (1 - ν A) ≤ ν A + ∫⁻ u in Aᶜ, ρ' u ∂μ := by
    rw [hcm_split, ← hxy]
    exact add_le_add hFatouA le_rfl
  have hy_eq : ∫⁻ u in Aᶜ, ρ' u ∂μ = 1 - ν A :=
    (ENNReal.add_right_inj hcm_top).mp (le_antisymm hmid_le hmid_ge)
  have hfin : ∫⁻ u in A, ρ' u ∂μ + ∫⁻ u in Aᶜ, ρ' u ∂μ
      = ν A + ∫⁻ u in Aᶜ, ρ' u ∂μ :=
    calc ∫⁻ u in A, ρ' u ∂μ + ∫⁻ u in Aᶜ, ρ' u ∂μ = 1 := hxy
      _ = ν A + (1 - ν A) := hcm_split.symm
      _ = ν A + ∫⁻ u in Aᶜ, ρ' u ∂μ := by rw [hy_eq]
  have hx_eq : ∫⁻ u in A, ρ' u ∂μ = ν A := (ENNReal.add_left_inj hy_top).mp hfin
  have hfinal : ∫⁻ u in A, ρ u ∂μ = ν A := by
    rw [hAA, hx_eq]
  simpa only [hA] using hfinal
  /- @proof-region region.target-node.session.1216f0779453d5fa end -/

end Statlib.Imported
end

