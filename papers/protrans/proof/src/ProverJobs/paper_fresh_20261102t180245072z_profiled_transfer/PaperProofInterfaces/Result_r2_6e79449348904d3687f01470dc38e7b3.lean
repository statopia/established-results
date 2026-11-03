import Lean
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.ExternalNodes.Node_de0094f940d84552806c
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Vocabulary
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.ProvedNodes
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Base

namespace PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

theorem paper_8d45c5e7199146b78778677b2fbc23cf :
    ∀ (q : ℕ), 1 ≤ q → ∀ (L : NNReal), 0 < L → ∀ (B : ℝ), 0 ≤ B →
    ∀ (c : ℝ), 0 < c →
    ∃ C_delta N_delta : ℝ, 0 < C_delta ∧ 0 < N_delta ∧
      ∀ (p : ℕ), 2 ≤ p →
      ∀ (K : ℕ), 1 ≤ K →
      ∀ (n_t : ℕ) (hnt : 0 < n_t),
      ∀ (ns : Fin K → ℕ), (∀ k : Fin K, 0 < ns k) →
      ∀ (n_s : ℕ), n_s = (∑ k : Fin K, ns k) → 0 < n_s → n_t ≤ n_s →
      ∀ (s_delta : ℝ), 0 ≤ s_delta →
      ∀ (δ : Fin K → Fin p → ℝ), (∀ k : Fin K, (∑ j : Fin p, |δ k j|) ≤ s_delta) →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : (Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) → Ω → Fin p → ℝ)
        (H : (Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) → Ω → Fin q → ℝ)
        (f : (Fin q → ℝ) → (Fin p → ℝ)),
        
        
        (hf_meas : Measurable f) →


        let Xrow : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k)) → Ω → Fin p → ℝ :=
          fun r ω => f (H r ω) + E r ω;
        
        (∀ r a, Measurable (fun ω => E r ω a)) →
        (∀ r b, Measurable (fun ω => H r ω b)) →
        (∀ r a, Measurable (fun ω => f (H r ω) a)) →
        
        (∀ r a, Integrable (fun ω => E r ω a) μ) →
        (∀ r b, Integrable (fun ω => H r ω b) μ) →
        (∀ r a, Integrable (fun ω => f (H r ω) a) μ) →
        
        iIndepFun (fun r ω => (E r ω, H r ω)) μ →
        
        (∀ r r', IdentDistrib (fun ω => (E r ω, H r ω)) (fun ω => (E r' ω, H r' ω)) μ μ) →
        
        (∀ r a, ∫ ω, E r ω a ∂μ = 0) →
        (∀ r b, ∫ ω, H r ω b ∂μ = 0) →
        (∀ r a, ∫ ω, f (H r ω) a ∂μ = 0) →
        
        (∀ r a, HasSubgaussianMGF (fun ω => E r ω a) L μ) →
        (∀ r b, HasSubgaussianMGF (fun ω => H r ω b) L μ) →
        (∀ r a, HasSubgaussianMGF (fun ω => f (H r ω) a) L μ) →
        
        (∀ r a b, ∫ ω, E r ω a * H r ω b ∂μ = 0) →
        (∀ r a b, Integrable (fun ω => E r ω a * H r ω b) μ) →
        
        (Sigma_X : Matrix (Fin p) (Fin p) ℝ) →
        (∀ a b, Sigma_X a b = ∫ ω, Xrow (Sum.inl ⟨0, hnt⟩) ω a * Xrow (Sum.inl ⟨0, hnt⟩) ω b ∂μ) →
        (∀ a b, Integrable (fun ω => Xrow (Sum.inl ⟨0, hnt⟩) ω a * Xrow (Sum.inl ⟨0, hnt⟩) ω b) μ) →
        (∀ a b, |Sigma_X a b| ≤ B) →
        
        N_delta * Real.log (p : ℝ) ≤ (n_s : ℝ) →
        
        (1 - (p : ℝ) ^ (-c) / 20) ≤
          (μ {ω : Ω | ∀ a : Fin p,
            |((n_s : ℝ))⁻¹ * (∑ k : Fin K, ∑ b : Fin p,
              ((∑ i : Fin (ns k), Xrow (Sum.inr ⟨k, i⟩) ω a * Xrow (Sum.inr ⟨k, i⟩) ω b) -
                (ns k : ℝ) * Sigma_X a b) * δ k b)| ≤
            C_delta * s_delta * Real.sqrt (Real.log (p : ℝ) / (n_s : ℝ))}).toReal
:= by
  /- @proof-region region.root.78937ab6aad7 begin -/
  intro q hq L hL B hB c hc
  obtain ⟨b, hbpos, hb⟩ :=
    PaperProofTasks.job_paper_ebad183ded244602a77f3710a9957efa.Statlib.Imported.paper_ebad183ded244602a77f3710a9957efa
  refine ⟨Real.exp 1 * (32 * (L : ℝ) + B) * Real.sqrt ((c + 8) / b), (c + 8) / b, ?_, ?_, ?_⟩
  · have hL' : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hK0 : (0 : ℝ) < 32 * (L : ℝ) + B := by linarith
    have hcb : (0 : ℝ) < (c + 8) / b := div_pos (by linarith) hbpos
    exact mul_pos (mul_pos (Real.exp_pos 1) hK0) (Real.sqrt_pos.2 hcb)
  · exact div_pos (by linarith) hbpos
  · intro p hp K hK n_t hnt ns hns n_s hn_s hn_s_pos hn_s_nt s_delta hs_delta δ hδ
    intro Ω instΩ μ instμ E H f hf_meas
    dsimp only
    intro hE_meas hH_meas hfH_meas hE_int hH_int hfH_int hindep hident
    intro hE_center hH_center hfH_center hE_subg hH_subg hfH_subg hEH_zero hEH_int
    intro Sigma_X hSigma_def hSigma_int hSigma_bound hNlog
    have hK0 : (0 : ℝ) < 32 * (L : ℝ) + B := by
      have hL' : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
      linarith
    set S : Fin p → Ω → ℝ := fun a ω => ∑ k : Fin K, ∑ b : Fin p,
      ((∑ i : Fin (ns k), (f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
        (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b)) -
        (ns k : ℝ) * Sigma_X a b) * δ k b with hS
    set t : ℝ := Real.exp 1 * (32 * (L : ℝ) + B) * Real.sqrt ((c + 8) / b) * s_delta *
      Real.sqrt (Real.log (p : ℝ) / (n_s : ℝ)) with ht
    change 1 - (p : ℝ) ^ (-c) / 20 ≤
      (μ {ω : Ω | ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t}).toReal
    by_cases hs0 : s_delta = 0
    · have hδ0 : ∀ (k : Fin K) (j : Fin p), δ k j = 0 := by
        intro k j
        have hk : (∑ j' : Fin p, |δ k j'|) ≤ 0 := by simpa [hs0] using hδ k
        have hsingle : |δ k j| ≤ ∑ j' : Fin p, |δ k j'| := by
          simpa using Finset.single_le_sum (f := fun j' : Fin p => |δ k j'|)
            (fun j' _ => abs_nonneg (δ k j')) (Finset.mem_univ j)
        have hz : |δ k j| = 0 := le_antisymm (le_trans hsingle hk) (abs_nonneg (δ k j))
        exact abs_eq_zero.mp hz
      have hS0 : ∀ (a : Fin p) (ω : Ω), S a ω = 0 := by
        intro a ω
        rw [hS]
        simp [hδ0]
      have ht0 : t = 0 := by
        rw [ht, hs0]
        ring
      have huniv : {ω : Ω | ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} = Set.univ := by
        apply Set.eq_univ_of_forall
        intro ω a
        simp [hS0, ht0]
      rw [huniv, measure_univ, ENNReal.toReal_one]
      have hpc : (0 : ℝ) ≤ (p : ℝ) ^ (-c) := by positivity
      linarith
    · have hs_delta_pos : (0 : ℝ) < s_delta :=
        lt_of_le_of_ne hs_delta (by intro h; exact hs0 h.symm)
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hns0 : (0 : ℝ) < (n_s : ℝ) := by exact_mod_cast hn_s_pos
      set V : ℝ := Real.exp 1 * (32 * (L : ℝ) + B) * s_delta with hVdef
      have hV_pos : (0 : ℝ) < V := by
        rw [hVdef]
        exact mul_pos (mul_pos (Real.exp_pos 1) hK0) hs_delta_pos
      have hBern := hb n_s hn_s_pos _ hV_pos (Ω := Ω) μ
      have hcoord : ∀ a : Fin p,
          μ {ω : Ω | t < |((n_s : ℝ))⁻¹ * S a ω|} ≤ ENNReal.ofReal (2 * (p : ℝ) ^ (-(c + 8))) := by
        intro a
        let U : (Σ k : Fin K, Fin (ns k)) → Ω → ℝ := fun ρ ω =>
          (f (H (Sum.inr ρ) ω) a + E (Sum.inr ρ) ω a) *
              (∑ b : Fin p, (f (H (Sum.inr ρ) ω) b + E (Sum.inr ρ) ω b) * δ ρ.1 b) -
            ∑ b : Fin p, Sigma_X a b * δ ρ.1 b
        have hcard : Fintype.card (Σ k : Fin K, Fin (ns k)) = n_s := by
          rw [Fintype.card_sigma]
          simp [hn_s]
        let e : Fin n_s ≃ (Σ k : Fin K, Fin (ns k)) :=
          (finCongr hcard.symm).trans (Fintype.equivFin (Σ k : Fin K, Fin (ns k))).symm
        have hsum_eq : ∀ ω : Ω, S a ω = ∑ l : Fin n_s, U (e l) ω := by
          intro ω
          have hsigma : S a ω = ∑ ρ : (Σ k : Fin K, Fin (ns k)), U ρ ω := by
            have hexp : (∑ ρ : (Σ k : Fin K, Fin (ns k)), U ρ ω)
                = ∑ k : Fin K, ∑ i : Fin (ns k), U ⟨k, i⟩ ω := by
              have key := Finset.sum_sigma' (s := (Finset.univ : Finset (Fin K)))
                (t := fun k => (Finset.univ : Finset (Fin (ns k))))
                (f := fun (k : Fin K) (i : Fin (ns k)) => U ⟨k, i⟩ ω)
              exact key.symm
            rw [hexp]
            simp only [hS, U]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            have hL : (∑ b : Fin p,
                ((∑ i : Fin (ns k),
                    (f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
                      (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b)) -
                  (ns k : ℝ) * Sigma_X a b) * δ k b)
                = (∑ b : Fin p, ∑ i : Fin (ns k),
                    (f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
                      (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b) * δ k b) -
                  (ns k : ℝ) * ∑ b : Fin p, Sigma_X a b * δ k b := by
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl (fun b _ => ?_)
              rw [sub_mul, Finset.sum_mul]
              ring
            have hswap : (∑ i : Fin (ns k), ∑ b : Fin p,
                (f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
                  (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b) * δ k b)
                = ∑ b : Fin p, ∑ i : Fin (ns k),
                  (f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
                    (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b) * δ k b :=
              Finset.sum_comm
            have hR : (∑ i : Fin (ns k),
                ((f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
                    (∑ b : Fin p,
                      (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b) * δ k b) -
                  ∑ b : Fin p, Sigma_X a b * δ k b))
                = (∑ b : Fin p, ∑ i : Fin (ns k),
                    (f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
                      (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b) * δ k b) -
                  (ns k : ℝ) * ∑ b : Fin p, Sigma_X a b * δ k b := by
              have hconst : (∑ _i : Fin (ns k), ∑ b : Fin p, Sigma_X a b * δ k b)
                  = (ns k : ℝ) * ∑ b : Fin p, Sigma_X a b * δ k b := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              have hm : (∑ i : Fin (ns k),
                  (f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
                    (∑ b : Fin p,
                      (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b) * δ k b))
                  = ∑ i : Fin (ns k), ∑ b : Fin p,
                      (f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
                        (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b) * δ k b := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl (fun b _ => by ring)
              have hsub : (∑ i : Fin (ns k),
                  ((f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
                      (∑ b : Fin p,
                        (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b) * δ k b) -
                    ∑ b : Fin p, Sigma_X a b * δ k b))
                  = (∑ i : Fin (ns k),
                      (f (H (Sum.inr ⟨k, i⟩) ω) a + E (Sum.inr ⟨k, i⟩) ω a) *
                        (∑ b : Fin p,
                          (f (H (Sum.inr ⟨k, i⟩) ω) b + E (Sum.inr ⟨k, i⟩) ω b) * δ k b)) -
                    ∑ i : Fin (ns k), ∑ b : Fin p, Sigma_X a b * δ k b :=
                by rw [Finset.sum_sub_distrib]
              rw [hsub, hm, hswap, hconst]
            rw [hL, hR]
          rw [hsigma]
          exact (Equiv.sum_comp e (fun ρ => U ρ ω)).symm
        have hsum_meas : ∀ (s : Finset (Fin p)) (g : Fin p → Ω → ℝ),
            (∀ b ∈ s, Measurable (g b)) → Measurable (fun ω => ∑ b ∈ s, g b ω) := by
          intro s
          induction s using Finset.induction with
          | empty =>
              intro g _
              simpa using (measurable_const : Measurable fun _ : Ω => (0 : ℝ))
          | insert a' s ha ih =>
              intro g hg
              have h1 : Measurable (g a') := hg a' (Finset.mem_insert_self a' s)
              have h2 : Measurable (fun ω => ∑ b ∈ s, g b ω) :=
                ih g (fun b hb => hg b (Finset.mem_insert_of_mem hb))
              have h3 := h1.add h2
              simpa [Finset.sum_insert ha] using h3
        have hU_meas : ∀ l : Fin n_s, Measurable (fun ω => U (e l) ω) := by
          intro l
          have hX : ∀ c : Fin p,
              Measurable (fun ω => f (H (Sum.inr (e l)) ω) c + E (Sum.inr (e l)) ω c) :=
            fun c => (hfH_meas _ c).add (hE_meas _ c)
          have h1 : Measurable
              (fun ω => f (H (Sum.inr (e l)) ω) a + E (Sum.inr (e l)) ω a) := hX a
          have h2 : Measurable (fun ω => ∑ b : Fin p,
              (f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b) * δ (e l).1 b) :=
            hsum_meas Finset.univ
              (fun b ω => (f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b) * δ (e l).1 b)
              (fun b _ => (hX b).mul measurable_const)
          have h3 : Measurable (fun ω => ∑ b : Fin p, Sigma_X a b * δ (e l).1 b) :=
            hsum_meas Finset.univ (fun b _ => Sigma_X a b * δ (e l).1 b)
              (fun b _ => measurable_const)
          show Measurable fun ω =>
            (f (H (Sum.inr (e l)) ω) a + E (Sum.inr (e l)) ω a) *
                (∑ b : Fin p, (f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b) * δ (e l).1 b) -
              ∑ b : Fin p, Sigma_X a b * δ (e l).1 b
          exact (h1.mul h2).sub h3
        have hXsq : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (c : Fin p),
            Integrable (fun ω => ‖f (H r ω) c + E r ω c‖ ^ (2 : ℕ)) μ := by
          intro r c
          have h2 : MemLp (fun ω => f (H r ω) c + E r ω c) ((2 : ℕ) : ENNReal) μ := by
            simpa using ((hfH_subg r c).add (hE_subg r c)).memLp (2 : NNReal)
          exact h2.integrable_norm_pow (by norm_num)
        have hXX_int : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (c d : Fin p),
            Integrable (fun ω => (f (H r ω) c + E r ω c) * (f (H r ω) d + E r ω d)) μ := by
          intro r c d
          refine Integrable.mono
            (g := fun ω => ‖f (H r ω) c + E r ω c‖ ^ (2 : ℕ) +
              ‖f (H r ω) d + E r ω d‖ ^ (2 : ℕ)) ((hXsq r c).add (hXsq r d)) ?_ ?_
          · exact ((hfH_meas r c).add (hE_meas r c)).mul
              ((hfH_meas r d).add (hE_meas r d)) |>.aestronglyMeasurable
          · filter_upwards with ω
            have h1 : ‖(f (H r ω) c + E r ω c) * (f (H r ω) d + E r ω d)‖
                = ‖f (H r ω) c + E r ω c‖ * ‖f (H r ω) d + E r ω d‖ := norm_mul _ _
            have h2 : ‖‖f (H r ω) c + E r ω c‖ ^ (2 : ℕ) +
                  ‖f (H r ω) d + E r ω d‖ ^ (2 : ℕ)‖
                = ‖f (H r ω) c + E r ω c‖ ^ (2 : ℕ) +
                  ‖f (H r ω) d + E r ω d‖ ^ (2 : ℕ) := by
              rw [Real.norm_eq_abs]
              exact abs_of_nonneg (by positivity)
            rw [h1, h2]
            nlinarith [sq_nonneg (‖f (H r ω) c + E r ω c‖ - ‖f (H r ω) d + E r ω d‖)]
        have hU_int : ∀ l : Fin n_s, Integrable (fun ω => U (e l) ω) μ := by
          intro l
          have h1 : Integrable (fun ω => ∑ b : Fin p,
              (f (H (Sum.inr (e l)) ω) a + E (Sum.inr (e l)) ω a) *
                (f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b) * δ (e l).1 b) μ :=
            integrable_finset_sum Finset.univ
              (fun b _ => (hXX_int (Sum.inr (e l)) a b).mul_const _)
          have h2 : Integrable (fun _ : Ω => ∑ b : Fin p, Sigma_X a b * δ (e l).1 b) μ :=
            integrable_const _
          have h3 : Integrable (fun ω =>
              (f (H (Sum.inr (e l)) ω) a + E (Sum.inr (e l)) ω a) *
                (∑ b : Fin p,
                  (f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b) * δ (e l).1 b)) μ := by
            have heq : (fun ω =>
                (f (H (Sum.inr (e l)) ω) a + E (Sum.inr (e l)) ω a) *
                  (∑ b : Fin p,
                    (f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b) * δ (e l).1 b))
                = fun ω => ∑ b : Fin p,
                  (f (H (Sum.inr (e l)) ω) a + E (Sum.inr (e l)) ω a) *
                    (f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b) * δ (e l).1 b := by
              funext ω
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun b _ => by ring)
            rw [heq]
            exact h1
          show Integrable (fun ω =>
            (f (H (Sum.inr (e l)) ω) a + E (Sum.inr (e l)) ω a) *
                (∑ b : Fin p,
                  (f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b) * δ (e l).1 b) -
              ∑ b : Fin p, Sigma_X a b * δ (e l).1 b) μ
          exact h3.sub h2
        have hcenter :=
          statopia_math_node_1960382922_323e449f q p K hq (by omega) hK L hL n_t hnt ns hns n_s
            hn_s hn_s_pos Ω μ E H f hf_meas hE_meas hfH_meas hE_subg hfH_subg hXX_int hident
            Sigma_X hSigma_def δ
        have hU_center : ∀ l : Fin n_s, ∫ ω, U (e l) ω ∂μ = 0 := by
          intro l
          show ∫ ω, ((f (H (Sum.inr (e l)) ω) a + E (Sum.inr (e l)) ω a) *
              (∑ b : Fin p,
                (f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b) * δ (e l).1 b) -
              ∑ b : Fin p, Sigma_X a b * δ (e l).1 b) ∂μ = 0
          exact hcenter.2 (e l) a
        have hU_indep : iIndepFun (fun l : Fin n_s => fun ω => U (e l) ω) μ := by
          have hsum2 : ∀ (s : Finset (Fin p)) (g : Fin p → ((Fin p → ℝ) × (Fin q → ℝ)) → ℝ),
              (∀ b ∈ s, Measurable (g b)) →
              Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) => ∑ b ∈ s, g b z) := by
            intro s
            induction s using Finset.induction with
            | empty =>
                intro g _
                simpa using
                  (measurable_const : Measurable fun _ : (Fin p → ℝ) × (Fin q → ℝ) => (0 : ℝ))
            | insert a' s ha ih =>
                intro g hg
                have h1 : Measurable (g a') := hg a' (Finset.mem_insert_self a' s)
                have h2 : Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) => ∑ b ∈ s, g b z) :=
                  ih g (fun b hb => hg b (Finset.mem_insert_of_mem hb))
                have h3 := h1.add h2
                simpa [Finset.sum_insert ha] using h3
          have hsub : iIndepFun (fun ρ : (Σ k : Fin K, Fin (ns k)) =>
              fun ω => (E (Sum.inr ρ) ω, H (Sum.inr ρ) ω)) μ :=
            ProbabilityTheory.iIndepFun.precomp
              (g := fun ρ : (Σ k : Fin K, Fin (ns k)) =>
                (Sum.inr ρ : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))))
              (fun a₁ a₂ h => by cases h; rfl) hindep
          have hG : ∀ ρ : (Σ k : Fin K, Fin (ns k)),
              Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) =>
                (f z.2 + z.1) a * (∑ b : Fin p, (f z.2 + z.1) b * δ ρ.1 b) -
                  ∑ b : Fin p, Sigma_X a b * δ ρ.1 b) := by
            intro ρ
            have hfst : Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) => z.1) := measurable_fst
            have hsnd : Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) => z.2) := measurable_snd
            have hfz : Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) => f z.2) :=
              hf_meas.comp hsnd
            have hX : ∀ c : Fin p,
                Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) => (f z.2 + z.1) c) := by
              intro c
              have h1 : Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) => f z.2 c) :=
                (measurable_pi_apply c).comp hfz
              have h2 : Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) => z.1 c) :=
                (measurable_pi_apply c).comp hfst
              exact h1.add h2
            have hs1 : Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) =>
                ∑ b : Fin p, (f z.2 + z.1) b * δ ρ.1 b) :=
              hsum2 Finset.univ (fun b z => (f z.2 + z.1) b * δ ρ.1 b)
                (fun b _ => (hX b).mul measurable_const)
            have hs2 : Measurable (fun _ : (Fin p → ℝ) × (Fin q → ℝ) =>
                ∑ b : Fin p, Sigma_X a b * δ ρ.1 b) := measurable_const
            exact (hX a).mul hs1 |>.sub hs2
          have hcomp : iIndepFun (fun ρ : (Σ k : Fin K, Fin (ns k)) => fun ω =>
              (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a *
                  (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b) -
                ∑ b : Fin p, Sigma_X a b * δ ρ.1 b) μ :=
            hsub.comp
              (fun (ρ : Σ k : Fin K, Fin (ns k)) (z : (Fin p → ℝ) × (Fin q → ℝ)) =>
                (f z.2 + z.1) a * (∑ b : Fin p, (f z.2 + z.1) b * δ ρ.1 b) -
                  ∑ b : Fin p, Sigma_X a b * δ ρ.1 b)
              hG
          exact ProbabilityTheory.iIndepFun.precomp (g := fun l : Fin n_s => e l) e.injective hcomp
        have hU_mom : ∀ (l : Fin n_s) (r : ℕ), 2 ≤ r →
            ∫⁻ ω, ENNReal.ofReal (|U (e l) ω| ^ r) ∂μ ≤
              ENNReal.ofReal ((Nat.factorial r : ℝ) * V ^ r) := by
          intro l r hr
          have hbound :=
            (statopia_math_node_2099409397_a58c9b68 q hq p (by omega) K hK L hL B hB n_t hnt ns
                hns n_s hn_s s_delta hs_delta δ hδ Ω μ E H f hf_meas hE_meas hH_meas hfH_meas
                hE_int hH_int hfH_int hindep hident hE_center hH_center hfH_center hE_subg hH_subg
                hfH_subg hEH_zero hEH_int Sigma_X hSigma_def hSigma_int hSigma_bound).2 (e l) a r hr
          have hint : Integrable (fun ω => |U (e l) ω| ^ r) μ := by
            show Integrable (fun ω => |((f (H (Sum.inr (e l)) ω) a + E (Sum.inr (e l)) ω a) *
                (∑ b : Fin p,
                  (f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b) * δ (e l).1 b)) -
                (∑ b : Fin p, Sigma_X a b * δ (e l).1 b)| ^ r) μ
            exact statopia_math_node_1593169820_e4fd9d72 p r (by omega) Ω μ
              (fun ω => f (H (Sum.inr (e l)) ω) a + E (Sum.inr (e l)) ω a)
              ((NNReal.sqrt L + NNReal.sqrt L) ^ 2)
              ((hfH_subg (Sum.inr (e l)) a).add (hE_subg (Sum.inr (e l)) a))
              (fun b ω => f (H (Sum.inr (e l)) ω) b + E (Sum.inr (e l)) ω b)
              ((NNReal.sqrt L + NNReal.sqrt L) ^ 2)
              (fun b => (hfH_subg (Sum.inr (e l)) b).add (hE_subg (Sum.inr (e l)) b))
              (δ (e l).1) (∑ b : Fin p, Sigma_X a b * δ (e l).1 b)
          have hnn : 0 ≤ᶠ[ae μ] (fun ω => |U (e l) ω| ^ r) := by
            filter_upwards with ω
            positivity
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
          exact ENNReal.ofReal_le_ofReal hbound
        have hset : {ω : Ω | t < |((n_s : ℝ))⁻¹ * S a ω|} =
            {ω : Ω | t < |((n_s : ℝ))⁻¹ * ∑ l : Fin n_s, U (e l) ω|} := by
          ext ω
          simp only [Set.mem_setOf_eq]
          rw [hsum_eq ω]
        have ht_pos : (0 : ℝ) < t := by
          rw [ht]
          have hlog : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by linarith)
          have h1 : (0 : ℝ) < Real.sqrt ((c + 8) / b) :=
            Real.sqrt_pos.2 (div_pos (by linarith) hbpos)
          have h2 : (0 : ℝ) < Real.sqrt (Real.log (p : ℝ) / (n_s : ℝ)) :=
            Real.sqrt_pos.2 (div_pos hlog hns0)
          exact mul_pos (mul_pos (mul_pos (mul_pos (Real.exp_pos 1) hK0) h1) hs_delta_pos) h2
        have hA : (0 : ℝ) < Real.exp 1 * (32 * (L : ℝ) + B) := mul_pos (Real.exp_pos 1) hK0
        have htV : t / V = Real.sqrt ((c + 8) / b) * Real.sqrt (Real.log (p : ℝ) / (n_s : ℝ)) := by
          rw [ht, hVdef]
          have hs : s_delta ≠ 0 := ne_of_gt hs_delta_pos
          have hAs : Real.exp 1 * (32 * (L : ℝ) + B) ≠ 0 := ne_of_gt hA
          field_simp
        have hx1 : ((c + 8) / b) * (Real.log (p : ℝ) / (n_s : ℝ)) ≤ 1 := by
          have h2 : (((c + 8) / b) * Real.log (p : ℝ)) / (n_s : ℝ) ≤ 1 := by
            rw [div_le_one hns0]
            exact hNlog
          calc ((c + 8) / b) * (Real.log (p : ℝ) / (n_s : ℝ))
              = (((c + 8) / b) * Real.log (p : ℝ)) / (n_s : ℝ) := by ring
            _ ≤ 1 := h2
        have hq0 : (0 : ℝ) ≤ t / V := by
          rw [htV]
          positivity
        have hq2 : (t / V) ^ 2 ≤ 1 := by
          rw [htV, mul_pow,
            Real.sq_sqrt (x := (c + 8) / b) (by positivity),
            Real.sq_sqrt (x := Real.log (p : ℝ) / (n_s : ℝ)) (by positivity)]
          exact hx1
        have hle1 : t / V ≤ 1 := by
          nlinarith [hq2, hq0, sq_nonneg (t / V - 1)]
        have hmin : min (t ^ 2 / V ^ 2) (t / V) = t ^ 2 / V ^ 2 := by
          have hsq : t ^ 2 / V ^ 2 ≤ t / V := by
            rw [show t ^ 2 / V ^ 2 = (t / V) ^ 2 from by rw [← div_pow]]
            nlinarith [hq2, hq0, hle1]
          exact min_eq_left hsq
        have hexp : Real.exp (-(b * (n_s : ℝ) * min (t ^ 2 / V ^ 2) (t / V))) =
            (p : ℝ) ^ (-(c + 8)) := by
          rw [hmin]
          have harg : b * (n_s : ℝ) * (t ^ 2 / V ^ 2) = (c + 8) * Real.log (p : ℝ) := by
            rw [show t ^ 2 / V ^ 2 = (t / V) ^ 2 from by rw [← div_pow]]
            rw [htV, mul_pow,
              Real.sq_sqrt (x := (c + 8) / b) (by positivity),
              Real.sq_sqrt (x := Real.log (p : ℝ) / (n_s : ℝ)) (by positivity)]
            have hb0 : b ≠ 0 := ne_of_gt hbpos
            have hs0 : (n_s : ℝ) ≠ 0 := ne_of_gt hns0
            field_simp
          rw [harg]
          rw [Real.rpow_def_of_pos hp0]
          congr 1
          ring
        have hmain := hBern (fun l : Fin n_s => fun ω => U (e l) ω)
          hU_meas hU_indep hU_int hU_center hU_mom t ht_pos
        rw [hset]
        have hfinal : (μ {ω : Ω | t < |((n_s : ℝ))⁻¹ * ∑ l : Fin n_s, U (e l) ω|}).toReal ≤
            2 * (p : ℝ) ^ (-(c + 8)) := by
          have h := hmain
          rw [hexp] at h
          simpa using h
        have hfin : μ {ω : Ω | t < |((n_s : ℝ))⁻¹ * ∑ l : Fin n_s, U (e l) ω|} ≠ ⊤ :=
          measure_ne_top μ _
        rw [← ENNReal.ofReal_toReal hfin]
        exact ENNReal.ofReal_le_ofReal hfinal
      have hupper : μ {ω : Ω | ¬ ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} ≤
          ENNReal.ofReal ((p : ℝ) ^ (-c) / 20) := by
        rw [show {ω : Ω | ¬ ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} =
            ⋃ a : Fin p, {ω : Ω | t < |((n_s : ℝ))⁻¹ * S a ω|} from by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall, not_le]]
        calc μ (⋃ a : Fin p, {ω : Ω | t < |((n_s : ℝ))⁻¹ * S a ω|})
            ≤ ∑ a : Fin p, μ {ω : Ω | t < |((n_s : ℝ))⁻¹ * S a ω|} := by
              simpa using measure_biUnion_finset_le (Finset.univ : Finset (Fin p))
                (fun a : Fin p => {ω : Ω | t < |((n_s : ℝ))⁻¹ * S a ω|})
          _ ≤ ∑ a : Fin p, ENNReal.ofReal (2 * (p : ℝ) ^ (-(c + 8))) :=
              Finset.sum_le_sum (fun a _ => hcoord a)
          _ = (p : ENNReal) * ENNReal.ofReal (2 * (p : ℝ) ^ (-(c + 8))) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = ENNReal.ofReal ((p : ℝ) * (2 * (p : ℝ) ^ (-(c + 8)))) := by
              rw [show ENNReal.ofReal ((p : ℝ) * (2 * (p : ℝ) ^ (-(c + 8)))) =
                  ENNReal.ofReal (p : ℝ) * ENNReal.ofReal (2 * (p : ℝ) ^ (-(c + 8))) from
                ENNReal.ofReal_mul (show (0 : ℝ) ≤ (p : ℝ) by positivity),
                ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal ((p : ℝ) ^ (-c) / 20) := by
              apply ENNReal.ofReal_le_ofReal
              have hpc : (0 : ℝ) ≤ (p : ℝ) ^ (-c) := by positivity
              have hp7 : (p : ℝ) ^ (-(7 : ℝ)) ≤ 1 / 128 := by
                have h : (p : ℝ) ^ (-(7 : ℝ)) ≤ (2 : ℝ) ^ (-(7 : ℝ)) :=
                  Real.rpow_le_rpow_of_nonpos (x := (2 : ℝ)) (y := (p : ℝ))
                    (by norm_num) hp2 (by norm_num : (-(7 : ℝ)) ≤ 0)
                have h2 : (2 : ℝ) ^ (-(7 : ℝ)) = 1 / 128 := by
                  rw [Real.rpow_neg_eq_inv_rpow]
                  norm_num
                rwa [h2] at h
              have hsplit : (p : ℝ) * (p : ℝ) ^ (-(c + 8)) =
                  (p : ℝ) ^ (-c) * (p : ℝ) ^ (-(7 : ℝ)) := by
                have h1 : (p : ℝ) ^ (1 + -(c + 8)) = (p : ℝ) * (p : ℝ) ^ (-(c + 8)) := by
                  rw [Real.rpow_add hp0, Real.rpow_one]
                have h2 : (p : ℝ) ^ (-c + -(7 : ℝ)) =
                    (p : ℝ) ^ (-c) * (p : ℝ) ^ (-(7 : ℝ)) := by
                  rw [Real.rpow_add hp0]
                rw [← h1, ← h2]
                congr 1
                ring
              have h3 : (p : ℝ) * (2 * (p : ℝ) ^ (-(c + 8))) =
                  2 * ((p : ℝ) ^ (-c) * (p : ℝ) ^ (-(7 : ℝ))) := by
                rw [show (p : ℝ) * (2 * (p : ℝ) ^ (-(c + 8))) =
                  2 * ((p : ℝ) * (p : ℝ) ^ (-(c + 8))) from by ring, hsplit]
              rw [h3]
              have h4 : 2 * ((p : ℝ) ^ (-c) * (p : ℝ) ^ (-(7 : ℝ))) ≤
                  2 * ((p : ℝ) ^ (-c) * (1 / 128)) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact mul_le_mul_of_nonneg_left hp7 hpc
              have h5 : 2 * ((p : ℝ) ^ (-c) * (1 / 128)) = (p : ℝ) ^ (-c) / 64 := by ring
              have h6 : (p : ℝ) ^ (-c) / 64 ≤ (p : ℝ) ^ (-c) / 20 := by linarith
              linarith
      have hsum : (1 : ENNReal) ≤
          μ {ω : Ω | ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} +
            ENNReal.ofReal ((p : ℝ) ^ (-c) / 20) := by
        have hun : (Set.univ : Set Ω) =
            {ω : Ω | ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} ∪
              {ω : Ω | ¬ ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} := by
          ext ω
          simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq]
          tauto
        calc (1 : ENNReal) = μ (Set.univ : Set Ω) := (measure_univ (μ := μ)).symm
          _ = μ ({ω : Ω | ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} ∪
                {ω : Ω | ¬ ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t}) := by rw [hun]
          _ ≤ μ {ω : Ω | ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} +
                μ {ω : Ω | ¬ ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} :=
              measure_union_le _ _
          _ ≤ μ {ω : Ω | ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} +
                ENNReal.ofReal ((p : ℝ) ^ (-c) / 20) := add_le_add le_rfl hupper
      have hne : μ {ω : Ω | ∀ a : Fin p, |((n_s : ℝ))⁻¹ * S a ω| ≤ t} +
          ENNReal.ofReal ((p : ℝ) ^ (-c) / 20) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, ENNReal.ofReal_ne_top⟩
      have key := ENNReal.toReal_mono hne hsum
      rw [ENNReal.toReal_add (measure_ne_top μ _) ENNReal.ofReal_ne_top, ENNReal.toReal_one,
        ENNReal.toReal_ofReal (by positivity)] at key
      linarith
  /- @proof-region region.root.78937ab6aad7 end -/

end Statlib.Imported

-- Paper root revision 3661e9fb-7d62-42c3-9b26-d025a1c9e457

