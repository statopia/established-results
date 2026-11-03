import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.ExternalNodes.Node_ef1c67bde1d7453089df
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Vocabulary
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.ProvedNodes
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Base

namespace PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ModelShiftLasso

theorem thm_upper_bound_of_eta
    (q : ℕ) (hq : 1 ≤ q)
    (L L_eps C_phi B_phi C_s s_delta c : ℝ)
    (hL : 0 < L) (hL_eps : 0 < L_eps) (hC_phi : 0 < C_phi) (hB_phi : 0 < B_phi)
    (hC_s : 0 < C_s) (hs_delta : 0 ≤ s_delta) (hc : 0 < c) :
    ∃ N_0 C_1 C_2 : ℝ, 0 < N_0 ∧ 0 < C_1 ∧ 0 < C_2 ∧
      ∀ (p : ℕ) (hp : 2 ≤ p) (K : ℕ) (hK : 1 ≤ K)
        (n_t : ℕ) (hn_t : 0 < n_t) (n_s : Fin K → ℕ) (hn_s : ∀ k, 0 < n_s k)
        (hn_st : n_t ≤ ∑ k, n_s k)
        (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (f : (Fin q → ℝ) → (Fin p → ℝ)) (hf : Measurable f)
        (βt : Fin p → ℝ) (φt : Fin q → ℝ)
        (βs : Fin K → Fin p → ℝ) (φs : Fin K → Fin q → ℝ)
        (Xt : Fin n_t → Ω → Fin p → ℝ) (Ht : Fin n_t → Ω → Fin q → ℝ)
        (Et : Fin n_t → Ω → Fin p → ℝ) (Yt : Fin n_t → Ω → ℝ) (εt : Fin n_t → Ω → ℝ)
        (Xs : (k : Fin K) → Fin (n_s k) → Ω → Fin p → ℝ)
        (Hs : (k : Fin K) → Fin (n_s k) → Ω → Fin q → ℝ)
        (Es : (k : Fin K) → Fin (n_s k) → Ω → Fin p → ℝ)
        (Ys : (k : Fin K) → Fin (n_s k) → Ω → ℝ)
        (εs : (k : Fin K) → Fin (n_s k) → Ω → ℝ)
        
        (hXt : ∀ i, Measurable (Xt i)) (hHt : ∀ i, Measurable (Ht i))
        (hEt : ∀ i, Measurable (Et i)) (hYt : ∀ i, Measurable (Yt i))
        (hεt : ∀ i, Measurable (εt i))
        (hXs : ∀ k i, Measurable (Xs k i)) (hHs : ∀ k i, Measurable (Hs k i))
        (hEs : ∀ k i, Measurable (Es k i)) (hYs : ∀ k i, Measurable (Ys k i))
        (hεs : ∀ k i, Measurable (εs k i))
        
        (hX_model_t : ∀ i ω, Xt i ω = f (Ht i ω) + Et i ω)
        (hY_model_t : ∀ i ω, Yt i ω = vdot (Xt i ω) βt + vdot (Ht i ω) φt + εt i ω)
        (hX_model_s : ∀ k i ω, Xs k i ω = f (Hs k i ω) + Es k i ω)
        (hY_model_s : ∀ k i ω,
          Ys k i ω = vdot (Xs k i ω) (βs k) + vdot (Hs k i ω) (φs k) + εs k i ω)
        
        (hIndep : iIndepFun (rowObs n_s Et Ht εt Es Hs εs) μ)
        
        (hSameLaw : ∀ a b,
          IdentDistrib (rowPair n_s Et Ht Es Hs a) (rowPair n_s Et Ht Es Hs b) μ μ)
        
        (hcentEt : ∀ i j, Integrable (fun ω => Et i ω j) μ ∧ ∫ ω, Et i ω j ∂μ = 0)
        (hcentHt : ∀ i j, Integrable (fun ω => Ht i ω j) μ ∧ ∫ ω, Ht i ω j ∂μ = 0)
        (hcentfHt : ∀ i j,
          Integrable (fun ω => f (Ht i ω) j) μ ∧ ∫ ω, f (Ht i ω) j ∂μ = 0)
        
        (hsubEt : ∀ i j, HasSubGaussNorm L (fun ω => Et i ω j) μ)
        (hsubHt : ∀ i j, HasSubGaussNorm L (fun ω => Ht i ω j) μ)
        (hsubfHt : ∀ i j, HasSubGaussNorm L (fun ω => f (Ht i ω) j) μ)
        
        (hEHorth : ∀ i a b, Integrable (fun ω => Et i ω a * Ht i ω b) μ ∧
          ∫ ω, Et i ω a * Ht i ω b ∂μ = 0)
        
        
        (hcentEs : ∀ k i j, Integrable (fun ω => Es k i ω j) μ ∧ ∫ ω, Es k i ω j ∂μ = 0)
        (hcentHs : ∀ k i j, Integrable (fun ω => Hs k i ω j) μ ∧ ∫ ω, Hs k i ω j ∂μ = 0)
        (hcentfHs : ∀ k i j,
          Integrable (fun ω => f (Hs k i ω) j) μ ∧ ∫ ω, f (Hs k i ω) j ∂μ = 0)
        (hsubEs : ∀ k i j, HasSubGaussNorm L (fun ω => Es k i ω j) μ)
        (hsubHs : ∀ k i j, HasSubGaussNorm L (fun ω => Hs k i ω j) μ)
        (hsubfHs : ∀ k i j, HasSubGaussNorm L (fun ω => f (Hs k i ω) j) μ)
        (hEHorth_s : ∀ k i a b, Integrable (fun ω => Es k i ω a * Hs k i ω b) μ ∧
          ∫ ω, Es k i ω a * Hs k i ω b ∂μ = 0)


        
        (hnoiseIndep_t : ∀ i, IndepFun (εt i) (fun ω => (Et i ω, Ht i ω)) μ)
        (hnoiseIndep_s : ∀ k i, IndepFun (εs k i) (fun ω => (Es k i ω, Hs k i ω)) μ)
        
        (hcentεt : ∀ i, Integrable (εt i) μ ∧ ∫ ω, εt i ω ∂μ = 0)
        (hcentεs : ∀ k i, Integrable (εs k i) μ ∧ ∫ ω, εs k i ω ∂μ = 0)
        
        (var : ℝ) (hvar_nn : 0 ≤ var)
        (hvar_t : ∀ i, variance (εt i) μ = var)
        (hvar_s : ∀ k i, variance (εs k i) μ = var)
        
        (hsubεt : ∀ i, HasSubGaussNorm L_eps (εt i) μ)
        (hsubεs : ∀ k i, HasSubGaussNorm L_eps (εs k i) μ)
        
        (hphi_bar : l2n (fun j => phiBar n_s φs j - φt j)
          ≤ C_phi * Real.sqrt (Real.log (p : ℝ) / (n_t : ℝ)))
        
        (hphi_het : ∀ k, l2n (fun j => φs k j - φt j) ≤ B_phi)
        
        (βinit : Ω → Fin p → ℝ) (hβinit : Measurable βinit)
        
        (s_eta : ℕ) (hs_eta_p : s_eta ≤ p)
        (hS_eta : (supportFinset (etaZero n_s βt βs)).card ≤ s_eta)
        
        (hspread : ∀ k, l1n (fun j => βs k j - betaBar n_s βs j) ≤ s_delta)
        
        (C_r : ℝ) (hC_r : 0 < C_r)
        
        (hN0 : N_0 * Real.log (p : ℝ) ≤ (n_t : ℝ))
        
        (lam : ℝ)
        (hlam : 4 * (C_1 * Real.sqrt (q : ℝ) * l2n φt + C_2)
            * Real.sqrt (Real.log (p : ℝ) / (n_t : ℝ)) ≤ lam)
        (hlam_pos : 0 < 4 * (C_1 * Real.sqrt (q : ℝ) * l2n φt + C_2)
            * Real.sqrt (Real.log (p : ℝ) / (n_t : ℝ))),
        let eta0 : Fin p → ℝ := etaZero n_s βt βs
        let S_eta : Finset (Fin p) := supportFinset eta0
        let betaS : Fin p → ℝ := betaBar n_s βs
        let Rset : Set Ω := REvent Xt S_eta C_r
        let Iset : Set Ω := IEvent βinit betaS C_s
        let Good : Ω → Prop := fun ω =>
          GoodAt n_s (fun i => Xt i ω) (fun i => Yt i ω) (fun k i => Xs k i ω)
            (fun k i => Ys k i ω) (βinit ω) eta0 C_r lam s_eta
        ∃ G : Set Ω, MeasurableSet G ∧
          ((1 : ℝ) - (p : ℝ) ^ (-c) ≤ μ.real G) ∧
          (∀ ω, ω ∈ G → ω ∈ Rset → ω ∈ Iset → Good ω) ∧
          ((1 : ℝ) - (p : ℝ) ^ (-c) - μ.real Rsetᶜ - μ.real Isetᶜ
            ≤ μ.real {ω | Good ω})
:= by
  /- @proof-region region.root.2e87d2466253 begin -/
  classical
  obtain ⟨Cx, Cδ, CH, Cd, Cε, N0g, hCx, hCδ, hCH, hCd, hCε, hN0g, hmain⟩ :=
    PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.paper_106ef041a01147028d56a10b8f69010e c hc q hq (L ^ 2) (L_eps ^ 2) (pow_pos hL 2) (pow_pos hL_eps 2)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hsq : (0 : ℝ) < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq0
  have hLM : (0 : ℝ) < 4 * L ^ 2 := by nlinarith [hL, sq_nonneg L]
  have hB0 : (0 : ℝ) <
      2 * Cx * C_s + Cδ * s_delta + Cd * B_phi * Real.sqrt (q : ℝ) +
        (4 * L ^ 2) * C_phi * Real.sqrt (q : ℝ) + Cε := by
    nlinarith [mul_pos hCx hC_s, mul_pos (mul_pos hCd hB_phi) hsq,
      mul_pos (mul_pos hLM hC_phi) hsq, hCε, mul_nonneg (le_of_lt hCδ) hs_delta]
  refine ⟨max N0g 1, 8 * CH,
    2 * (2 * Cx * C_s + Cδ * s_delta + Cd * B_phi * Real.sqrt (q : ℝ) +
      (4 * L ^ 2) * C_phi * Real.sqrt (q : ℝ) + Cε) + Cε, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · linarith
  · linarith
  · intro p hp K hK n_t hn_t n_s hn_s hn_st Ω instΩ μ instμ f hf βt φt βs φs Xt Ht Et Yt epsT Xs Hs Es Ys epsS
    intro hXt hHt hEt hYt hεt hXs hHs hEs hYs hεs hX_model_t hY_model_t hX_model_s hY_model_s hIndep hSameLaw hcentEt hcentHt hcentfHt hsubEt hsubHt hsubfHt hEHorth hcentEs hcentHs hcentfHs hsubEs hsubHs hsubfHs hEHorth_s hnoiseIndep_t hnoiseIndep_s hcentεt hcentεs var hvar_nn hvar_t hvar_s hsubεt hsubεs hphi_bar hphi_het βinit hβinit s_eta hs_eta_p hS_eta hspread C_r hC_r hN0 lam hlam hlam_pos
    set nsTot : ℝ := ((∑ k, n_s k : ℕ) : ℝ) with hnsTot
    have hnsTot_eq : nsTot = ∑ k, (n_s k : ℝ) := by
      rw [hnsTot, Nat.cast_sum]
    haveI hKne : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
    have hsum_pos : 0 < ∑ k, n_s k :=
      Finset.sum_pos (fun k _ => hn_s k) Finset.univ_nonempty
    have hnsTot_pos : 0 < nsTot := by
      rw [hnsTot]
      exact_mod_cast hsum_pos
    set i0 : Fin n_t := ⟨0, hn_t⟩ with hi0
    set Prow : Measure ((Fin p → ℝ) × (Fin q → ℝ)) :=
      Measure.map (fun ω => (Et i0 ω, Ht i0 ω)) μ with hProw
    have hProwAEM : AEMeasurable (fun ω => (Et i0 ω, Ht i0 ω)) μ := by
      obtain ⟨hae, -, -⟩ := hSameLaw (Sum.inl i0) (Sum.inl i0)
      simpa [rowPair] using hae
    haveI hProwProb : IsProbabilityMeasure Prow := by
      rw [hProw]
      exact MeasureTheory.Measure.isProbabilityMeasure_map hProwAEM
    have hmapT : ∀ r : Fin n_t, Measure.map (fun ω => (Et r ω, Ht r ω)) μ = Prow := by
      intro r
      rw [hProw]
      obtain ⟨-, -, hmap⟩ := hSameLaw (Sum.inl r) (Sum.inl i0)
      simpa [rowPair] using hmap
    have hmapS : ∀ (k : Fin K) (r : Fin (n_s k)),
        Measure.map (fun ω => (Es k r ω, Hs k r ω)) μ = Prow := by
      intro k r
      rw [hProw]
      obtain ⟨-, -, hmap⟩ := hSameLaw (Sum.inr ⟨k, r⟩) (Sum.inl i0)
      simpa [rowPair] using hmap
    have hmapTμ : ∀ r : Fin n_t,
        Measure.map (fun ω => (Et r ω, Ht r ω)) μ = Measure.map (fun ω => (Et i0 ω, Ht i0 ω)) μ := by
      intro r
      obtain ⟨-, -, hmap⟩ := hSameLaw (Sum.inl r) (Sum.inl i0)
      simpa [rowPair] using hmap
    set SigmaX : Fin p → Fin p → ℝ :=
      fun i j => ∫ ω, Xt i0 ω i * Xt i0 ω j ∂μ with hSigmaXdef
    set M : Fin p → Fin q → ℝ :=
      fun i j => ∫ ω, Xt i0 ω i * Ht i0 ω j ∂μ with hMdef
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have h12 : (1 : ℕ) ≤ p := le_trans (by norm_num) hp
      exact_mod_cast h12
    have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
    have hnt_le : (n_t : ℝ) ≤ nsTot := by
      rw [hnsTot]
      exact_mod_cast hn_st
    have hN0g_le : N0g * Real.log (p : ℝ) ≤ (n_t : ℝ) := by
      have h1 : N0g ≤ max N0g 1 := le_max_left _ _
      nlinarith [hN0, hlogp, h1]
    have htransInt : ∀ (g : (Fin p → ℝ) × (Fin q → ℝ) → ℝ), Measurable g →
        Integrable (fun ω => g (Et i0 ω, Ht i0 ω)) μ → Integrable g Prow := by
      intro g hg hgi
      rw [hProw, MeasureTheory.integrable_map_measure (g := g)
        (f := fun ω => (Et i0 ω, Ht i0 ω)) hg.aestronglyMeasurable hProwAEM]
      simpa [Function.comp_def] using hgi
    have htransIntegral : ∀ (g : (Fin p → ℝ) × (Fin q → ℝ) → ℝ), Measurable g →
        ∫ x, g x ∂Prow = ∫ ω, g (Et i0 ω, Ht i0 ω) ∂μ := by
      intro g hg
      rw [hProw]
      exact MeasureTheory.integral_map hProwAEM hg.aestronglyMeasurable
    have hprodInt : ∀ (u v : Ω → ℝ), MemLp u 2 μ → MemLp v 2 μ →
        Integrable (fun ω => u ω * v ω) μ := by
      intro u v hu hv
      have h1 : Integrable (fun ω => (u ω) ^ 2) μ := hu.integrable_sq
      have h2 : Integrable (fun ω => (v ω) ^ 2) μ := hv.integrable_sq
      have h3 : Integrable (fun ω => (u ω + v ω) ^ 2) μ := (hu.add hv).integrable_sq
      have h4 : Integrable (fun ω => (u ω + v ω) ^ 2 - (u ω) ^ 2 - (v ω) ^ 2) μ :=
        (h3.sub h1).sub h2
      have hfun : (fun ω => u ω * v ω)
          = fun ω => (1 / 2) * ((u ω + v ω) ^ 2 - (u ω) ^ 2 - (v ω) ^ 2) := by
        funext ω
        ring
      rw [hfun]
      exact h4.const_mul (1 / 2)
    have hMemLpXt : ∀ i : Fin p, MemLp (fun ω => Xt i0 ω i) 2 μ := by
      intro i
      have hF : MemLp (fun ω => f (Ht i0 ω) i) 2 μ := by
        simpa using ProbabilityTheory.HasSubgaussianMGF.memLp
          (show HasSubgaussianMGF (fun ω => f (Ht i0 ω) i) ⟨L ^ 2, sq_nonneg L⟩ μ from
            hsubfHt i0 i) (2 : NNReal)
      have hE : MemLp (fun ω => Et i0 ω i) 2 μ := by
        simpa using ProbabilityTheory.HasSubgaussianMGF.memLp
          (show HasSubgaussianMGF (fun ω => Et i0 ω i) ⟨L ^ 2, sq_nonneg L⟩ μ from
            hsubEt i0 i) (2 : NNReal)
      have hfun : (fun ω => Xt i0 ω i) = fun ω => f (Ht i0 ω) i + Et i0 ω i := by
        funext ω
        simp [hX_model_t i0 ω]
      rw [hfun]
      exact hF.add hE
    have hMemLpHt : ∀ j : Fin q, MemLp (fun ω => Ht i0 ω j) 2 μ := by
      intro j
      simpa using ProbabilityTheory.HasSubgaussianMGF.memLp
        (show HasSubgaussianMGF (fun ω => Ht i0 ω j) ⟨L ^ 2, sq_nonneg L⟩ μ from
          hsubHt i0 j) (2 : NNReal)
    have hconc := hmain p hp K hK Ω μ Prow f hf
      (fun i j => by
        refine htransInt (fun x => (f x.2 i + x.1 i) * (f x.2 j + x.1 j)) (by fun_prop) ?_
        simpa [hX_model_t] using hprodInt _ _ (hMemLpXt i) (hMemLpXt j))
      SigmaX
      (fun i j => (by
        refine (integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))).trans
          (htransIntegral (fun x => (f x.2 i + x.1 i) * (f x.2 j + x.1 j)) (by fun_prop)).symm
        rw [hX_model_t i0 ω]
        rfl))
      (fun i j => by
        refine htransInt (fun x => (f x.2 i + x.1 i) * x.2 j) (by fun_prop) ?_
        simpa [hX_model_t] using hprodInt _ _ (hMemLpXt i) (hMemLpHt j))
      M
      (fun i j => (by
        refine (integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))).trans
          (htransIntegral (fun x => (f x.2 i + x.1 i) * x.2 j) (by fun_prop)).symm
        rw [hX_model_t i0 ω]
        rfl))
      (fun i => htransInt (fun x => x.1 i) (by fun_prop) (hcentEt i0 i).1)
      (fun i => (htransIntegral (fun x => x.1 i) (by fun_prop)).trans (hcentEt i0 i).2)
      (fun j => htransInt (fun x => x.2 j) (by fun_prop) (hcentHt i0 j).1)
      (fun j => (htransIntegral (fun x => x.2 j) (by fun_prop)).trans (hcentHt i0 j).2)
      (fun i => htransInt (fun x => f x.2 i) (by fun_prop) (hcentfHt i0 i).1)
      (fun i => (htransIntegral (fun x => f x.2 i) (by fun_prop)).trans (hcentfHt i0 i).2)
      (fun i => by
        have hb : HasSubgaussianMGF (fun ω => Et i0 ω i) ⟨L ^ 2, sq_nonneg L⟩ μ := hsubEt i0 i
        refine ⟨?_, ?_⟩
        · intro t
          exact htransInt (fun x : (Fin p → ℝ) × (Fin q → ℝ) => Real.exp (t * x.1 i))
            (by fun_prop) (hb.1 t)
        · intro t
          have hI : ∫ x : (Fin p → ℝ) × (Fin q → ℝ), Real.exp (t * x.1 i) ∂Prow =
              ∫ ω, Real.exp (t * Et i0 ω i) ∂μ := by
            rw [htransIntegral (fun x : (Fin p → ℝ) × (Fin q → ℝ) => Real.exp (t * x.1 i))
              (by fun_prop)]
          exact hI.trans_le (hb.2 t))
      (fun j => by
        have hb : HasSubgaussianMGF (fun ω => Ht i0 ω j) ⟨L ^ 2, sq_nonneg L⟩ μ := hsubHt i0 j
        refine ⟨?_, ?_⟩
        · intro t
          exact htransInt (fun x : (Fin p → ℝ) × (Fin q → ℝ) => Real.exp (t * x.2 j))
            (by fun_prop) (hb.1 t)
        · intro t
          have hI : ∫ x : (Fin p → ℝ) × (Fin q → ℝ), Real.exp (t * x.2 j) ∂Prow =
              ∫ ω, Real.exp (t * Ht i0 ω j) ∂μ := by
            rw [htransIntegral (fun x : (Fin p → ℝ) × (Fin q → ℝ) => Real.exp (t * x.2 j))
              (by fun_prop)]
          exact hI.trans_le (hb.2 t))
      (fun i => by
        have hb : HasSubgaussianMGF (fun ω => f (Ht i0 ω) i) ⟨L ^ 2, sq_nonneg L⟩ μ := hsubfHt i0 i
        refine ⟨?_, ?_⟩
        · intro t
          exact htransInt (fun x : (Fin p → ℝ) × (Fin q → ℝ) => Real.exp (t * f x.2 i))
            (by fun_prop) (hb.1 t)
        · intro t
          have hI : ∫ x : (Fin p → ℝ) × (Fin q → ℝ), Real.exp (t * f x.2 i) ∂Prow =
              ∫ ω, Real.exp (t * f (Ht i0 ω) i) ∂μ := by
            rw [htransIntegral (fun x : (Fin p → ℝ) × (Fin q → ℝ) => Real.exp (t * f x.2 i))
              (by fun_prop)]
          exact hI.trans_le (hb.2 t))
      (fun i j => htransInt (fun x => x.1 i * x.2 j) (by fun_prop) (hEHorth i0 i j).1)
      (fun i j => (htransIntegral (fun x => x.1 i * x.2 j) (by fun_prop)).trans (hEHorth i0 i j).2)
      n_t hn_t n_s hn_s nsTot hnsTot_eq βt βs φt φs s_eta hs_eta_p
      s_delta C_phi B_phi hs_delta hC_phi hB_phi
      (by
        simpa [PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.l2norm,
          PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.phiBar,
          PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.aTcoef,
          l2n, l2Sq, phiBar, sourceWeight, hnsTot_eq, Nat.cast_sum] using hphi_bar)
      (fun k => by
        simpa [PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.l2norm,
          l2n, l2Sq] using hphi_het k)
      (fun k => by
        simpa [PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.betaBar,
          betaBar, sourceWeight, l1n, hnsTot_eq, Nat.cast_sum] using hspread k)
      (by
        simpa [PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.eta0Vec,
          etaZero,
          PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.betaBar,
          betaBar, sourceWeight, supportFinset, hnsTot_eq, Nat.cast_sum] using hS_eta)
      Et Ht epsT Es Hs epsS var hvar_nn
      hEt hHt hεt hEs hHs hεs hmapT hmapS
      (by
        have hcomp : iIndepFun (fun a ω =>
            (((rowObs n_s Et Ht epsT Es Hs epsS a ω).1,
              (rowObs n_s Et Ht epsT Es Hs epsS a ω).2.1),
              (rowObs n_s Et Ht epsT Es Hs epsS a ω).2.2)) μ :=
          ProbabilityTheory.iIndepFun.comp hIndep
            (fun (_ : Fin n_t ⊕ ((k : Fin K) × Fin (n_s k)))
                (p : (Fin p → ℝ) × (Fin q → ℝ) × ℝ) => ((p.1, p.2.1), p.2.2))
            (fun _ => by fun_prop)
        exact (ProbabilityTheory.iIndepFun_congr
          (f := fun a ω =>
            (((rowObs n_s Et Ht epsT Es Hs epsS a ω).1,
              (rowObs n_s Et Ht epsT Es Hs epsS a ω).2.1),
              (rowObs n_s Et Ht epsT Es Hs epsS a ω).2.2))
          (g := PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.pooledRow
            Et Ht epsT Es Hs epsS)
          (fun a => Filter.Eventually.of_forall (fun ω => by
            cases a with
            | inl i => rfl
            | inr ki => rfl))).mp hcomp) hnoiseIndep_t hnoiseIndep_s
      (fun i => (hcentεt i).1) (fun k i => (hcentεs k i).1)
      (fun i => (hcentεt i).2) (fun k i => (hcentεs k i).2)
      (fun i => by
        have h2 : MemLp (epsT i) (2 : ENNReal) μ := by
          simpa using ProbabilityTheory.HasSubgaussianMGF.memLp
            (show HasSubgaussianMGF (epsT i) ⟨L_eps ^ 2, sq_nonneg L_eps⟩ μ from hsubεt i)
            (2 : NNReal)
        exact h2.integrable_sq)
      (fun k i => by
        have h2 : MemLp (epsS k i) (2 : ENNReal) μ := by
          simpa using ProbabilityTheory.HasSubgaussianMGF.memLp
            (show HasSubgaussianMGF (epsS k i) ⟨L_eps ^ 2, sq_nonneg L_eps⟩ μ from hsubεs k i)
            (2 : NNReal)
        exact h2.integrable_sq)
      (fun i => by
        have h2 : MemLp (epsT i) (2 : ENNReal) μ := by
          simpa using ProbabilityTheory.HasSubgaussianMGF.memLp
            (show HasSubgaussianMGF (epsT i) ⟨L_eps ^ 2, sq_nonneg L_eps⟩ μ from hsubεt i)
            (2 : NNReal)
        rw [← hvar_t i, ProbabilityTheory.variance_eq_sub h2, (hcentεt i).2]
        simp)
      (fun k i => by
        have h2 : MemLp (epsS k i) (2 : ENNReal) μ := by
          simpa using ProbabilityTheory.HasSubgaussianMGF.memLp
            (show HasSubgaussianMGF (epsS k i) ⟨L_eps ^ 2, sq_nonneg L_eps⟩ μ from hsubεs k i)
            (2 : NNReal)
        rw [← hvar_s k i, ProbabilityTheory.variance_eq_sub h2, (hcentεs k i).2]
        simp)
      (fun i => by simpa [HasSubGaussNorm] using hsubεt i)
      (fun k i => by simpa [HasSubGaussNorm] using hsubεs k i)
      hnt_le hN0g_le
    have hMrow : ∀ j : Fin p,
        Real.sqrt (∑ s : Fin q, (M j s) ^ 2) ≤ (4 * L ^ 2) * Real.sqrt (q : ℝ) := by
      obtain ⟨hint, hmax⟩ :=
        statopia_math_node_3081215765_b752b30e p q (le_trans (by norm_num) hp) hq L hL
          Ω μ (fun ω (j : Fin p) => f (Ht i0 ω) j) (fun ω (s : Fin q) => Ht i0 ω s)
          (fun j => hsubfHt i0 j) (fun s => hsubHt i0 s)
      have hMeq : ∀ (j : Fin p) (s : Fin q),
          M j s = ∫ ω, f (Ht i0 ω) j * Ht i0 ω s ∂μ := by
        intro j s
        have h1 : M j s = ∫ ω, (f (Ht i0 ω) j + Et i0 ω j) * Ht i0 ω s ∂μ := by
          rw [hMdef]
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun ω => by simp [hX_model_t i0 ω]))
        have h2 : ∫ ω, (f (Ht i0 ω) j + Et i0 ω j) * Ht i0 ω s ∂μ
            = ∫ ω, f (Ht i0 ω) j * Ht i0 ω s ∂μ +
              ∫ ω, Et i0 ω j * Ht i0 ω s ∂μ := by
          rw [← MeasureTheory.integral_add (hint j s) (hEHorth i0 j s).1]
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun ω => by ring))
        rw [h1, h2, (hEHorth i0 j s).2, add_zero]
      intro j
      have hbdd : BddAbove (Set.range (fun i : Fin p =>
          |Real.sqrt (∑ s : Fin q, (∫ ω, f (Ht i0 ω) i * Ht i0 ω s ∂μ) ^ 2)|)) :=
        (Set.finite_range _).bddAbove
      have hmax' : sSup (Set.range (fun i : Fin p =>
          |Real.sqrt (∑ s : Fin q, (∫ ω, f (Ht i0 ω) i * Ht i0 ω s ∂μ) ^ 2)|))
          ≤ (4 * L ^ 2) * Real.sqrt (q : ℝ) := hmax
      have hle : |Real.sqrt (∑ s : Fin q, (∫ ω, f (Ht i0 ω) j * Ht i0 ω s ∂μ) ^ 2)|
          ≤ (4 * L ^ 2) * Real.sqrt (q : ℝ) :=
        le_trans (le_csSup hbdd (Set.mem_range_self j)) hmax'
      have hfin : Real.sqrt (∑ s : Fin q, (∫ ω, f (Ht i0 ω) j * Ht i0 ω s ∂μ) ^ 2)
          ≤ (4 * L ^ 2) * Real.sqrt (q : ℝ) := le_trans (le_abs_self _) hle
      have hrew : Real.sqrt (∑ s : Fin q, (M j s) ^ 2)
          = Real.sqrt (∑ s : Fin q, (∫ ω, f (Ht i0 ω) j * Ht i0 ω s ∂μ) ^ 2) := by
        simp only [hMeq j]
      rw [hrew]
      exact hfin
    have hpt : ∀ ω,
        ω ∈ PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.Gset
          f Et Ht epsT Es Hs epsS SigmaX M βs φt φs nsTot Cx Cδ CH Cd Cε s_delta B_phi →
        ω ∈ REvent Xt (supportFinset (etaZero n_s βt βs)) C_r →
        ω ∈ IEvent βinit (betaBar n_s βs) C_s →
        GoodAt n_s (fun i => Xt i ω) (fun i => Yt i ω) (fun k i => Xs k i ω)
          (fun k i => Ys k i ω) (βinit ω) (etaZero n_s βt βs) C_r lam s_eta := by
      intro ω hG hR hI
      have hbeta : l1n (fun j => βinit ω j - betaBar n_s βs j) ≤ C_s := hI
      exact statopia_math_node_2523946026_e3500c8d p q K n_t hp hq hK hn_t
        n_s hn_s hn_st Ω f Xt Ht Et Yt epsT Xs Hs Es Ys epsS
        βt φt βs φs SigmaX M nsTot hnsTot_eq
        Cx Cδ CH Cd Cε C_phi B_phi C_s s_delta lam C_r (4 * L ^ 2)
        hCx hCδ hCH hCd hCε hC_phi hB_phi hC_s hs_delta hLM hC_r
        hlam hlam_pos s_eta hs_eta_p hS_eta (fun j => βinit ω j)
        (fun i j w => by simp [hX_model_t i w])
        hY_model_t
        (fun k i j w => by simp [hX_model_s k i w])
        hY_model_s
        hphi_bar hbeta hMrow ω hG hR
    refine ⟨PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.Gset
        f Et Ht epsT Es Hs epsS SigmaX M βs φt φs nsTot Cx Cδ CH Cd Cε s_delta B_phi,
      ?_, hconc.1, ?_, ?_⟩
    · unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.Gset
      unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.MatSupLe
        PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.VecSupLe
        PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.RowL2Le
      dsimp only
      simp only [← hX_model_t, ← hX_model_s]
      set aT : ℝ :=
        PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.aTcoef p n_t with haT
      set aS : ℝ :=
        PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.aSCoef p nsTot with haS
      have h1 : MeasurableSet (fun ω : Ω => ∀ (i j : Fin p),
          |(∑ r, Xt r ω i * Xt r ω j) / (n_t : ℝ) - SigmaX i j| ≤ Cx * aT) := by
        change MeasurableSet {ω : Ω | ∀ (i j : Fin p),
          |(∑ r, Xt r ω i * Xt r ω j) / (n_t : ℝ) - SigmaX i j| ≤ Cx * aT}
        have hiff : ({ω : Ω | ∀ (i j : Fin p),
            |(∑ r, Xt r ω i * Xt r ω j) / (n_t : ℝ) - SigmaX i j| ≤ Cx * aT} : Set Ω)
            = ⋂ (i : Fin p), ⋂ (j : Fin p),
              {ω : Ω | |(∑ r, Xt r ω i * Xt r ω j) / (n_t : ℝ) - SigmaX i j| ≤ Cx * aT} := by
          apply Set.ext
          intro ω
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rw [hiff]
        refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
        have hpt : ∀ r : Fin n_t, Measurable (fun ω : Ω => Xt r ω i * Xt r ω j) := fun r =>
          ((measurable_pi_apply i).comp (hXt r)).mul ((measurable_pi_apply j).comp (hXt r))
        have hfun : Measurable
            (fun ω : Ω => (∑ r, Xt r ω i * Xt r ω j) / (n_t : ℝ) - SigmaX i j) := by
          have hsum : Measurable (fun ω : Ω => ∑ r, Xt r ω i * Xt r ω j) := by
            simpa using Finset.measurable_sum (Finset.univ : Finset (Fin n_t))
              (f := fun r (ω : Ω) => Xt r ω i * Xt r ω j) (fun r _ => hpt r)
          exact (hsum.div_const (n_t : ℝ)).sub measurable_const
        have habs : {ω : Ω | |(∑ r, Xt r ω i * Xt r ω j) / (n_t : ℝ) - SigmaX i j| ≤ Cx * aT}
            = {ω : Ω | -(Cx * aT) ≤ (∑ r, Xt r ω i * Xt r ω j) / (n_t : ℝ) - SigmaX i j} ∩
              {ω : Ω | (∑ r, Xt r ω i * Xt r ω j) / (n_t : ℝ) - SigmaX i j ≤ Cx * aT} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, abs_le]
        rw [habs]
        exact MeasurableSet.inter (measurableSet_le measurable_const hfun)
          (measurableSet_le hfun measurable_const)
      refine MeasurableSet.inter h1 ?_
      have hgen2 : ∀ (g : Ω → Fin p → Fin p → ℝ) (cst : ℝ),
          (∀ (i j : Fin p), Measurable (fun ω => g ω i j)) →
          MeasurableSet (fun ω : Ω => ∀ (i j : Fin p), |g ω i j| ≤ cst) := by
        intro g cst hg
        change MeasurableSet {ω : Ω | ∀ (i j : Fin p), |g ω i j| ≤ cst}
        have hiff : ({ω : Ω | ∀ (i j : Fin p), |g ω i j| ≤ cst} : Set Ω)
            = ⋂ (i : Fin p), ⋂ (j : Fin p), {ω : Ω | |g ω i j| ≤ cst} := by
          apply Set.ext
          intro ω
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rw [hiff]
        refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
        have habs : {ω : Ω | |g ω i j| ≤ cst}
            = {ω : Ω | -cst ≤ g ω i j} ∩ {ω : Ω | g ω i j ≤ cst} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, abs_le]
        rw [habs]
        exact MeasurableSet.inter (measurableSet_le measurable_const (hg i j))
          (measurableSet_le (hg i j) measurable_const)
      have hgen1 : ∀ (g : Ω → Fin p → ℝ) (cst : ℝ),
          (∀ (i : Fin p), Measurable (fun ω => g ω i)) →
          MeasurableSet (fun ω : Ω => ∀ (i : Fin p), |g ω i| ≤ cst) := by
        intro g cst hg
        change MeasurableSet {ω : Ω | ∀ (i : Fin p), |g ω i| ≤ cst}
        have hiff : ({ω : Ω | ∀ (i : Fin p), |g ω i| ≤ cst} : Set Ω)
            = ⋂ (i : Fin p), {ω : Ω | |g ω i| ≤ cst} := by
          apply Set.ext
          intro ω
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rw [hiff]
        refine MeasurableSet.iInter (fun i => ?_)
        have habs : {ω : Ω | |g ω i| ≤ cst}
            = {ω : Ω | -cst ≤ g ω i} ∩ {ω : Ω | g ω i ≤ cst} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, abs_le]
        rw [habs]
        exact MeasurableSet.inter (measurableSet_le measurable_const (hg i))
          (measurableSet_le (hg i) measurable_const)
      have h2 : MeasurableSet (fun ω : Ω => ∀ (i j : Fin p),
          |(∑ k, ∑ r, Xs k r ω i * Xs k r ω j) / nsTot - SigmaX i j| ≤ Cx * aS) :=
        hgen2 (fun ω i j => (∑ k, ∑ r, Xs k r ω i * Xs k r ω j) / nsTot - SigmaX i j)
          (Cx * aS) (fun i j => by
            have hinner : ∀ k : Fin K,
                Measurable (fun ω : Ω => ∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j) := by
              intro k
              have hterm : ∀ r : Fin (n_s k),
                  Measurable (fun ω : Ω => Xs k r ω i * Xs k r ω j) := fun r =>
                ((measurable_pi_apply i).comp (hXs k r)).mul
                  ((measurable_pi_apply j).comp (hXs k r))
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin (n_s k)))
                (f := fun r (ω : Ω) => Xs k r ω i * Xs k r ω j) (fun r _ => hterm r)
            have hsum2 : Measurable
                (fun ω : Ω => ∑ k : Fin K, ∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j) := by
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin K))
                (f := fun k (ω : Ω) => ∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j)
                (fun k _ => hinner k)
            exact (hsum2.div_const nsTot).sub measurable_const)
      refine MeasurableSet.inter h2 ?_
      have h3 : MeasurableSet (fun ω : Ω => ∀ (i : Fin p),
          |(∑ k : Fin K, (n_s k : ℝ) * ∑ j : Fin p,
              ((∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j) / (n_s k : ℝ) - SigmaX i j) *
                (βs k j - PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.betaBar n_s nsTot βs j)) /
            nsTot| ≤ Cδ * s_delta * aS) := by
        refine hgen1 (fun ω i => (∑ k : Fin K, (n_s k : ℝ) * ∑ j : Fin p,
            ((∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j) / (n_s k : ℝ) - SigmaX i j) *
              (βs k j - PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.betaBar n_s nsTot βs j)) / nsTot)
          (Cδ * s_delta * aS) (fun i => by
            set BB : Fin p → ℝ :=
              PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.betaBar n_s nsTot βs with hBB
            have hterm : ∀ (k : Fin K) (j : Fin p), Measurable (fun ω : Ω =>
                ((∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j) / (n_s k : ℝ) - SigmaX i j) *
                  (βs k j - BB j)) := by
              intro k j
              have hr : Measurable
                  (fun ω : Ω => ∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j) := by
                have hrr : ∀ r : Fin (n_s k),
                    Measurable (fun ω : Ω => Xs k r ω i * Xs k r ω j) := fun r =>
                  ((measurable_pi_apply i).comp (hXs k r)).mul
                    ((measurable_pi_apply j).comp (hXs k r))
                simpa using Finset.measurable_sum (Finset.univ : Finset (Fin (n_s k)))
                  (f := fun r (ω : Ω) => Xs k r ω i * Xs k r ω j) (fun r _ => hrr r)
              exact ((hr.div_const (n_s k : ℝ)).sub measurable_const).mul measurable_const
            have hkj : ∀ k : Fin K, Measurable (fun ω : Ω => ∑ j : Fin p,
                ((∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j) / (n_s k : ℝ) - SigmaX i j) *
                  (βs k j - BB j)) := by
              intro k
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin p))
                (f := fun j (ω : Ω) =>
                  ((∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j) / (n_s k : ℝ) - SigmaX i j) *
                    (βs k j - BB j))
                (fun j _ => hterm k j)
            have hsum3 : Measurable (fun ω : Ω => ∑ k : Fin K, (n_s k : ℝ) * ∑ j : Fin p,
                ((∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j) / (n_s k : ℝ) - SigmaX i j) *
                  (βs k j - BB j)) := by
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin K))
                (f := fun k (ω : Ω) => (n_s k : ℝ) * ∑ j : Fin p,
                  ((∑ r : Fin (n_s k), Xs k r ω i * Xs k r ω j) / (n_s k : ℝ) - SigmaX i j) *
                    (βs k j - BB j))
                (fun k _ => measurable_const.mul (hkj k))
            exact hsum3.div_const nsTot)
      refine MeasurableSet.inter h3 ?_
      have hgenR : ∀ (g : Ω → Fin p → Fin q → ℝ) (cst : ℝ),
          (∀ (i : Fin p) (j : Fin q), Measurable (fun ω => g ω i j)) →
          MeasurableSet (fun ω : Ω => ∀ (i : Fin p),
            Real.sqrt (∑ j : Fin q, (g ω i j) ^ 2) ≤ cst) := by
        intro g cst hg
        change MeasurableSet {ω : Ω | ∀ (i : Fin p), Real.sqrt (∑ j : Fin q, (g ω i j) ^ 2) ≤ cst}
        have hiff : ({ω : Ω | ∀ (i : Fin p), Real.sqrt (∑ j : Fin q, (g ω i j) ^ 2) ≤ cst} : Set Ω)
            = ⋂ (i : Fin p), {ω : Ω | Real.sqrt (∑ j : Fin q, (g ω i j) ^ 2) ≤ cst} := by
          apply Set.ext
          intro ω
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rw [hiff]
        refine MeasurableSet.iInter (fun i => ?_)
        have hS : Measurable (fun ω : Ω => ∑ j : Fin q, (g ω i j) ^ 2) := by
          have hterm : ∀ j : Fin q, Measurable (fun ω : Ω => g ω i j ^ 2) := fun j => by
            simpa [pow_two] using (hg i j).mul (hg i j)
          simpa using Finset.measurable_sum (Finset.univ : Finset (Fin q))
            (f := fun j (ω : Ω) => g ω i j ^ 2) (fun j _ => hterm j)
        exact measurableSet_le (Real.continuous_sqrt.measurable.comp hS) measurable_const
      have h4 : MeasurableSet (fun ω : Ω => ∀ (i : Fin p),
          Real.sqrt (∑ j : Fin q,
            ((∑ r, f (Ht r ω) i * Ht r ω j) / (n_t : ℝ) - M i j) ^ 2) ≤
            CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (n_t : ℝ))) :=
        hgenR (fun ω i j => (∑ r, f (Ht r ω) i * Ht r ω j) / (n_t : ℝ) - M i j)
          (CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (n_t : ℝ)))
          (fun i j => by
            have hsum : Measurable
                (fun ω : Ω => ∑ r : Fin n_t, f (Ht r ω) i * Ht r ω j) := by
              have hterm : ∀ r : Fin n_t,
                  Measurable (fun ω : Ω => f (Ht r ω) i * Ht r ω j) := fun r =>
                ((measurable_pi_apply i).comp (hf.comp (hHt r))).mul
                  ((measurable_pi_apply j).comp (hHt r))
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin n_t))
                (f := fun r (ω : Ω) => f (Ht r ω) i * Ht r ω j) (fun r _ => hterm r)
            exact (hsum.div_const (n_t : ℝ)).sub measurable_const)
      refine MeasurableSet.inter h4 ?_
      have h5 : MeasurableSet (fun ω : Ω => ∀ (i : Fin p),
          Real.sqrt (∑ j : Fin q,
            ((∑ k, ∑ r, f (Hs k r ω) i * Hs k r ω j) / nsTot - M i j) ^ 2) ≤
            CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot)) :=
        hgenR (fun ω i j => (∑ k, ∑ r, f (Hs k r ω) i * Hs k r ω j) / nsTot - M i j)
          (CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot))
          (fun i j => by
            have hk : ∀ k : Fin K, Measurable
                (fun ω : Ω => ∑ r : Fin (n_s k), f (Hs k r ω) i * Hs k r ω j) := by
              intro k
              have hterm : ∀ r : Fin (n_s k),
                  Measurable (fun ω : Ω => f (Hs k r ω) i * Hs k r ω j) := fun r =>
                ((measurable_pi_apply i).comp (hf.comp (hHs k r))).mul
                  ((measurable_pi_apply j).comp (hHs k r))
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin (n_s k)))
                (f := fun r (ω : Ω) => f (Hs k r ω) i * Hs k r ω j) (fun r _ => hterm r)
            have hsum : Measurable (fun ω : Ω => ∑ k : Fin K, ∑ r : Fin (n_s k),
                f (Hs k r ω) i * Hs k r ω j) := by
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin K))
                (f := fun k (ω : Ω) => ∑ r : Fin (n_s k), f (Hs k r ω) i * Hs k r ω j)
                (fun k _ => hk k)
            exact (hsum.div_const nsTot).sub measurable_const)
      refine MeasurableSet.inter h5 ?_
      have h6 : MeasurableSet (fun ω : Ω => ∀ (i : Fin p),
          Real.sqrt (∑ j : Fin q,
            ((∑ r, Et r ω i * Ht r ω j) / (n_t : ℝ)) ^ 2) ≤
            CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (n_t : ℝ))) :=
        hgenR (fun ω i j => (∑ r, Et r ω i * Ht r ω j) / (n_t : ℝ))
          (CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (n_t : ℝ)))
          (fun i j => by
            have hsum : Measurable
                (fun ω : Ω => ∑ r : Fin n_t, Et r ω i * Ht r ω j) := by
              have hterm : ∀ r : Fin n_t,
                  Measurable (fun ω : Ω => Et r ω i * Ht r ω j) := fun r =>
                ((measurable_pi_apply i).comp (hEt r)).mul
                  ((measurable_pi_apply j).comp (hHt r))
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin n_t))
                (f := fun r (ω : Ω) => Et r ω i * Ht r ω j) (fun r _ => hterm r)
            exact hsum.div_const (n_t : ℝ))
      refine MeasurableSet.inter h6 ?_
      have h7 : MeasurableSet (fun ω : Ω => ∀ (i : Fin p),
          Real.sqrt (∑ j : Fin q,
            ((∑ k, ∑ r, Es k r ω i * Hs k r ω j) / nsTot) ^ 2) ≤
            CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot)) :=
        hgenR (fun ω i j => (∑ k, ∑ r, Es k r ω i * Hs k r ω j) / nsTot)
          (CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot))
          (fun i j => by
            have hk : ∀ k : Fin K, Measurable
                (fun ω : Ω => ∑ r : Fin (n_s k), Es k r ω i * Hs k r ω j) := by
              intro k
              have hterm : ∀ r : Fin (n_s k),
                  Measurable (fun ω : Ω => Es k r ω i * Hs k r ω j) := fun r =>
                ((measurable_pi_apply i).comp (hEs k r)).mul
                  ((measurable_pi_apply j).comp (hHs k r))
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin (n_s k)))
                (f := fun r (ω : Ω) => Es k r ω i * Hs k r ω j) (fun r _ => hterm r)
            have hsum : Measurable (fun ω : Ω => ∑ k : Fin K, ∑ r : Fin (n_s k),
                Es k r ω i * Hs k r ω j) := by
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin K))
                (f := fun k (ω : Ω) => ∑ r : Fin (n_s k), Es k r ω i * Hs k r ω j)
                (fun k _ => hk k)
            exact hsum.div_const nsTot)
      refine MeasurableSet.inter h7 ?_
      have h8 : MeasurableSet (fun ω : Ω => ∀ (i : Fin p),
          |(∑ r, Xt r ω i * epsT r ω) / (n_t : ℝ)| ≤
            Cε * Real.sqrt (Real.log (p : ℝ) / (n_t : ℝ))) :=
        hgen1 (fun ω i => (∑ r, Xt r ω i * epsT r ω) / (n_t : ℝ))
          (Cε * Real.sqrt (Real.log (p : ℝ) / (n_t : ℝ)))
          (fun i => by
            have hsum : Measurable
                (fun ω : Ω => ∑ r : Fin n_t, Xt r ω i * epsT r ω) := by
              have hterm : ∀ r : Fin n_t,
                  Measurable (fun ω : Ω => Xt r ω i * epsT r ω) := fun r =>
                ((measurable_pi_apply i).comp (hXt r)).mul (hεt r)
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin n_t))
                (f := fun r (ω : Ω) => Xt r ω i * epsT r ω) (fun r _ => hterm r)
            exact hsum.div_const (n_t : ℝ))
      refine MeasurableSet.inter h8 ?_
      have h9 : MeasurableSet (fun ω : Ω => ∀ (i : Fin p),
          |(∑ k, ∑ r, Xs k r ω i * epsS k r ω) / nsTot| ≤
            Cε * Real.sqrt (Real.log (p : ℝ) / nsTot)) :=
        hgen1 (fun ω i => (∑ k, ∑ r, Xs k r ω i * epsS k r ω) / nsTot)
          (Cε * Real.sqrt (Real.log (p : ℝ) / nsTot))
          (fun i => by
            have hk : ∀ k : Fin K, Measurable
                (fun ω : Ω => ∑ r : Fin (n_s k), Xs k r ω i * epsS k r ω) := by
              intro k
              have hterm : ∀ r : Fin (n_s k),
                  Measurable (fun ω : Ω => Xs k r ω i * epsS k r ω) := fun r =>
                ((measurable_pi_apply i).comp (hXs k r)).mul (hεs k r)
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin (n_s k)))
                (f := fun r (ω : Ω) => Xs k r ω i * epsS k r ω) (fun r _ => hterm r)
            have hsum : Measurable (fun ω : Ω => ∑ k : Fin K, ∑ r : Fin (n_s k),
                Xs k r ω i * epsS k r ω) := by
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin K))
                (f := fun k (ω : Ω) => ∑ r : Fin (n_s k), Xs k r ω i * epsS k r ω)
                (fun k _ => hk k)
            exact hsum.div_const nsTot)
      refine MeasurableSet.inter h9 ?_
      let E : Ω → Fin p → Fin K → Fin q → ℝ := fun ω i k j =>
        (∑ r : Fin (n_s k), Xs k r ω i * Hs k r ω j - (n_s k : ℝ) * M i j) *
          (φs k - φt) j
      refine hgen1 (fun ω i => (∑ k : Fin K, ∑ j : Fin q, E ω i k j) / nsTot)
        (Cd * B_phi * Real.sqrt (q : ℝ) * aS) (fun i => by
          have hEj : ∀ (k : Fin K) (j : Fin q), Measurable (fun ω : Ω => E ω i k j) := by
            intro k j
            have hrr : ∀ r : Fin (n_s k),
                Measurable (fun ω : Ω => Xs k r ω i * Hs k r ω j) := fun r =>
              ((measurable_pi_apply i).comp (hXs k r)).mul
                ((measurable_pi_apply j).comp (hHs k r))
            have hr : Measurable
                (fun ω : Ω => ∑ r : Fin (n_s k), Xs k r ω i * Hs k r ω j) := by
              simpa using Finset.measurable_sum (Finset.univ : Finset (Fin (n_s k)))
                (f := fun r (ω : Ω) => Xs k r ω i * Hs k r ω j) (fun r _ => hrr r)
            show Measurable (fun ω : Ω =>
              (∑ r : Fin (n_s k), Xs k r ω i * Hs k r ω j - (n_s k : ℝ) * M i j) *
                (φs k - φt) j)
            exact (hr.sub measurable_const).mul measurable_const
          have hk : ∀ k : Fin K,
              Measurable (fun ω : Ω => ∑ j : Fin q, E ω i k j) := fun k => by
            simpa using Finset.measurable_sum (Finset.univ : Finset (Fin q))
              (f := fun j (ω : Ω) => E ω i k j) (fun j _ => hEj k j)
          have hsum : Measurable (fun ω : Ω => ∑ k : Fin K, ∑ j : Fin q, E ω i k j) := by
            simpa using Finset.measurable_sum (Finset.univ : Finset (Fin K))
              (f := fun k (ω : Ω) => ∑ j : Fin q, E ω i k j) (fun k _ => hk k)
          exact hsum.div_const nsTot)
    · intro ω hG hR hI
      exact hpt ω hG hR hI
    · set RS : Set Ω := REvent Xt (supportFinset (etaZero n_s βt βs)) C_r with hRS
      set IS : Set Ω := IEvent βinit (betaBar n_s βs) C_s with hIS
      set GG : Set Ω :=
          PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.Gset
            f Et Ht epsT Es Hs epsS SigmaX M βs φt φs nsTot Cx Cδ CH Cd Cε s_delta B_phi
        with hGG
      set GoodS : Set Ω :=
        {ω | GoodAt n_s (fun i => Xt i ω) (fun i => Yt i ω) (fun k i => Xs k i ω)
          (fun k i => Ys k i ω) (βinit ω) (etaZero n_s βt βs) C_r lam s_eta} with hGoodS
      have hconc1 : 1 - (p : ℝ) ^ (-c) ≤ μ.real GG := hconc.1
      have hreal_sub : ∀ s t : Set Ω, μ.real (s ∪ t) ≤ μ.real s + μ.real t := by
        intro s t
        have hs : μ s ≠ ⊤ := measure_ne_top μ s
        have ht : μ t ≠ ⊤ := measure_ne_top μ t
        have hbdd : μ s + μ t ≠ ⊤ := by
          have h1 : μ s ≤ 1 := by simpa using measure_mono (μ := μ) (Set.subset_univ s)
          have h2 : μ t ≤ 1 := by simpa using measure_mono (μ := μ) (Set.subset_univ t)
          refine ne_top_of_le_ne_top (show (2 : ENNReal) ≠ ⊤ by simp) ?_
          calc μ s + μ t ≤ 1 + 1 := add_le_add h1 h2
            _ = 2 := by norm_num
        calc μ.real (s ∪ t) = (μ (s ∪ t)).toReal := rfl
          _ ≤ (μ s + μ t).toReal := ENNReal.toReal_mono hbdd (measure_union_le s t)
          _ = (μ s).toReal + (μ t).toReal := ENNReal.toReal_add hs ht
          _ = μ.real s + μ.real t := rfl
      have hsub : GG ⊆ (GG ∩ RS ∩ IS) ∪ RSᶜ ∪ ISᶜ := by
        intro ω hω
        by_cases hR : ω ∈ RS
        · by_cases hI : ω ∈ IS
          · exact Or.inl (Or.inl ⟨⟨hω, hR⟩, hI⟩)
          · exact Or.inr hI
        · exact Or.inl (Or.inr hR)
      have hmono : μ.real GG ≤ μ.real ((GG ∩ RS ∩ IS) ∪ RSᶜ ∪ ISᶜ) := measureReal_mono hsub
      have hmono2 : μ.real (GG ∩ RS ∩ IS) ≤ μ.real GoodS := by
        refine measureReal_mono ?_
        intro ω hω
        simpa [hGoodS] using hpt ω hω.1.1 hω.1.2 hω.2
      have hchain : μ.real ((GG ∩ RS ∩ IS) ∪ RSᶜ ∪ ISᶜ) ≤
          μ.real (GG ∩ RS ∩ IS) + μ.real RSᶜ + μ.real ISᶜ := by
        rw [Set.union_assoc]
        have h1 := hreal_sub (GG ∩ RS ∩ IS) (RSᶜ ∪ ISᶜ)
        have h2 := hreal_sub (RSᶜ) (ISᶜ)
        linarith [h1, h2]
      linarith [hconc1, hmono, hchain, hmono2]
  /- @proof-region region.root.2e87d2466253 end -/

end ModelShiftLasso

-- Paper root revision 58cc2312-4651-4ca4-9c43-412b7c03e5e5

