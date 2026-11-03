import Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_even_moment_le
import Lean
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Vocabulary
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Base
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.ProvedNodes.Node_3568007364_198afdaf_d4009630
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.ProvedNodes.Node_856880814_cb48915c_4063309f

namespace PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_2099409397_a58c9b68 : ∀ (q : ℕ) (hq : 1 ≤ q)
    (p : ℕ) (hp : 1 ≤ p)
    (K : ℕ) (hK : 1 ≤ K)
    (L : NNReal) (hL : 0 < L)
    (B : ℝ) (hB : 0 ≤ B)
    (n_t : ℕ) (hnt : 0 < n_t)
    (ns : Fin K → ℕ) (hns : ∀ k : Fin K, 0 < ns k)
    (n_s : ℕ) (hn_s : n_s = ∑ k : Fin K, ns k)
    (s_delta : ℝ) (hs_delta : 0 ≤ s_delta)
    (δ : Fin K → Fin p → ℝ) (hδ : ∀ k : Fin K, (∑ j : Fin p, |δ k j|) ≤ s_delta)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : (Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) → Ω → Fin p → ℝ)
    (H : (Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) → Ω → Fin q → ℝ)
    (f : (Fin q → ℝ) → (Fin p → ℝ))
    (hf_meas : Measurable f)
    (hE_meas : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      Measurable (fun ω => E r ω a))
    (hH_meas : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (b : Fin q),
      Measurable (fun ω => H r ω b))
    (hfH_meas : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      Measurable (fun ω => f (H r ω) a))
    (hE_int : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      Integrable (fun ω => E r ω a) μ)
    (hH_int : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (b : Fin q),
      Integrable (fun ω => H r ω b) μ)
    (hfH_int : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      Integrable (fun ω => f (H r ω) a) μ)
    (hindep : iIndepFun (fun r ω => (E r ω, H r ω)) μ)
    (hident : ∀ (r r' : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))),
      IdentDistrib (fun ω => (E r ω, H r ω)) (fun ω => (E r' ω, H r' ω)) μ μ)
    (hE_zero : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      ∫ ω, E r ω a ∂μ = 0)
    (hH_zero : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (b : Fin q),
      ∫ ω, H r ω b ∂μ = 0)
    (hfH_zero : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      ∫ ω, f (H r ω) a ∂μ = 0)
    (hE_subg : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      HasSubgaussianMGF (fun ω => E r ω a) L μ)
    (hH_subg : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (b : Fin q),
      HasSubgaussianMGF (fun ω => H r ω b) L μ)
    (hfH_subg : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      HasSubgaussianMGF (fun ω => f (H r ω) a) L μ)
    (hEH_zero : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p) (b : Fin q),
      ∫ ω, E r ω a * H r ω b ∂μ = 0)
    (hEH_int : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p) (b : Fin q),
      Integrable (fun ω => E r ω a * H r ω b) μ)
    (Sigma_X : Matrix (Fin p) (Fin p) ℝ)
    (hSigma_def : ∀ (a b : Fin p), Sigma_X a b =
      ∫ ω, (f (H (Sum.inl ⟨0, hnt⟩) ω) + E (Sum.inl ⟨0, hnt⟩) ω) a *
        (f (H (Sum.inl ⟨0, hnt⟩) ω) + E (Sum.inl ⟨0, hnt⟩) ω) b ∂μ)
    (hSigma_int : ∀ (a b : Fin p), Integrable (fun ω =>
      (f (H (Sum.inl ⟨0, hnt⟩) ω) + E (Sum.inl ⟨0, hnt⟩) ω) a *
        (f (H (Sum.inl ⟨0, hnt⟩) ω) + E (Sum.inl ⟨0, hnt⟩) ω) b) μ)
    (hSigma_bound : ∀ (a b : Fin p), |Sigma_X a b| ≤ B),
    (∀ (ρ : Σ k : Fin K, Fin (ns k)) (a : Fin p) (m : ℕ), 1 ≤ m →
      ∫ ω, (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a *
          (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b)
        - ∑ b : Fin p, Sigma_X a b * δ ρ.1 b|) ^ m ∂μ
      ≤ ((32 * (L : ℝ) + B) * s_delta * (m : ℝ)) ^ m)
    ∧ (∀ (ρ : Σ k : Fin K, Fin (ns k)) (a : Fin p) (r : ℕ), 2 ≤ r →
      ∫ ω, (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a *
          (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b)
        - ∑ b : Fin p, Sigma_X a b * δ ρ.1 b|) ^ r ∂μ
      ≤ (Nat.factorial r : ℝ) * (Real.exp 1 * (32 * (L : ℝ) + B) * s_delta) ^ r) := by
  /- @proof-region region.target-node.session.6f9755c2d5d64b28 begin -/
  intro q hq p hp K hK L hL B hB n_t hnt ns hns n_s hn_s s_delta hs_delta δ hδ Ω instΩ μ instμ E H f hf_meas hE_meas hH_meas hfH_meas hE_int hH_int hfH_int hindep hident hE_zero hH_zero hfH_zero hE_subg hH_subg hfH_subg hEH_zero hEH_int Sigma_X hSigma_def hSigma_int hSigma_bound
  have key : ∀ (ρ : Σ k : Fin K, Fin (ns k)) (a : Fin p) (m : ℕ), 1 ≤ m →
      ∫ ω, (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a *
          (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b)
        - ∑ b : Fin p, Sigma_X a b * δ ρ.1 b|) ^ m ∂μ
      ≤ ((32 * (L : ℝ) + B) * s_delta * (m : ℝ)) ^ m := by
    intro ρ a m hm
    set σ : ℝ := 2 * Real.sqrt (L:ℝ) with hσdef
    have hLr0 : (0:ℝ) < (L:ℝ) := by simpa using hL
    have hLr : (0:ℝ) ≤ (L:ℝ) := le_of_lt hLr0
    have hσpos : 0 < σ := by
      rw [hσdef]; have h := Real.sqrt_pos_of_pos hLr0; nlinarith
    have hσsq : σ^2 = 4 * (L:ℝ) := by
      rw [hσdef, mul_pow, Real.sq_sqrt hLr]; norm_num
    have hparam_eq : (NNReal.sqrt L + NNReal.sqrt L)^2 = 4 * L := by
      rw [show NNReal.sqrt L + NNReal.sqrt L = 2 * NNReal.sqrt L by rw [two_mul]]
      rw [mul_pow, NNReal.sq_sqrt]; norm_num
    have hcoe : ((↑(4 * L) : ℝ)) = 4 * (L:ℝ) := by push_cast; ring
    have hc : ((↑(4 * L) : ℝ)) = σ^2 := by rw [hcoe, hσdef, mul_pow, Real.sq_sqrt hLr]; norm_num
    have heven : ∀ b : Fin p,
        ∫ ω, |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m) ∂μ
          ≤ 2 * (m.factorial:ℝ) * (8*(L:ℝ))^m := by
      intro b
      have hXsubg : HasSubgaussianMGF (fun ω => f (H (Sum.inr ρ) ω) b + E (Sum.inr ρ) ω b) ((NNReal.sqrt L + NNReal.sqrt L)^2) μ :=
        HasSubgaussianMGF.add (hfH_subg (Sum.inr ρ) b) (hE_subg (Sum.inr ρ) b)
      rw [hparam_eq] at hXsubg
      have hmeas : Measurable (fun ω => f (H (Sum.inr ρ) ω) b + E (Sum.inr ρ) ω b) := by
        simpa using (hfH_meas (Sum.inr ρ) b).add (hE_meas (Sum.inr ρ) b)
      have h2σ : 2 * σ^2 = 8 * (L:ℝ) := by rw [hσsq]; ring
      have hcong : ∫ ω, |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m) ∂μ
          = ∫ ω, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b ^ (2*m) ∂μ := by
        congr 1 with ω
        have hnn : (0:ℝ) ≤ ((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b) ^ (2*m) := by
          rw [pow_mul]; exact pow_nonneg (sq_nonneg _) m
        rw [← abs_pow, abs_of_nonneg hnn]
      calc ∫ ω, |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m) ∂μ
          = ∫ ω, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b ^ (2*m) ∂μ := hcong
        _ ≤ 2 * (m.factorial:ℝ) * (2 * σ^2)^m :=
            Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_even_moment_le μ (fun ω => f (H (Sum.inr ρ) ω) b + E (Sum.inr ρ) ω b) hmeas σ hσpos (4 * L) hc hXsubg m hm
        _ = 2 * (m.factorial:ℝ) * (8*(L:ℝ))^m := by rw [h2σ]
    have hInt_sq : ∀ b : Fin p, Integrable (fun ω => (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b ^ 2) μ := by
      intro b
      have hXsubg2 : HasSubgaussianMGF (fun ω => f (H (Sum.inr ρ) ω) b + E (Sum.inr ρ) ω b) (4 * L) μ := by
        have h := HasSubgaussianMGF.add (hfH_subg (Sum.inr ρ) b) (hE_subg (Sum.inr ρ) b)
        rwa [hparam_eq] at h
      exact MeasureTheory.MemLp.integrable_sq (hXsubg2.memLp 2)
    have hSpow : ∀ ω : Ω, |∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b| ^ m
        ≤ s_delta ^ (m-1) * ∑ b : Fin p, |δ ρ.1 b| * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m := by
      intro ω
      have h1 : |∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b|
          ≤ ∑ b : Fin p, |δ ρ.1 b| * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| := by
        calc |∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b|
            ≤ ∑ b : Fin p, |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ b : Fin p, |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| * |δ ρ.1 b| := by
              apply Finset.sum_congr rfl; intro b _; rw [abs_mul]
          _ = ∑ b : Fin p, |δ ρ.1 b| * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| := by
              apply Finset.sum_congr rfl; intro b _; rw [mul_comm]
      calc |∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b| ^ m
          ≤ (∑ b : Fin p, |δ ρ.1 b| * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)|) ^ m := by
              gcongr
        _ ≤ (∑ b : Fin p, |δ ρ.1 b|) ^ (m-1) * ∑ b : Fin p, |δ ρ.1 b| * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m :=
              statopia_math_node_3568007364_198afdaf Finset.univ (fun b => |δ ρ.1 b|) (fun b => |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)|)
                (fun b _ => abs_nonneg (δ ρ.1 b)) (fun b _ => abs_nonneg ((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)) m hm
        _ ≤ s_delta ^ (m-1) * ∑ b : Fin p, |δ ρ.1 b| * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m := by
              gcongr
              exact hδ ρ.1
    have hInt_2m : ∀ b : Fin p, Integrable (fun ω => |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m)) μ := by
      intro b
      have hXsubg2 : HasSubgaussianMGF (fun ω => f (H (Sum.inr ρ) ω) b + E (Sum.inr ρ) ω b) (4 * L) μ := by
        have h := HasSubgaussianMGF.add (hfH_subg (Sum.inr ρ) b) (hE_subg (Sum.inr ρ) b)
        rwa [hparam_eq] at h
      have hmem := hXsubg2.memLp ((2 * m : ℕ) : NNReal)
      have hne : (2 * m) ≠ 0 := by omega
      exact MeasureTheory.MemLp.integrable_norm_pow (p := 2 * m) hmem hne
    have hXm : ∀ b : Fin p, Measurable (fun ω => (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b) := by
      intro b
      simpa using (hfH_meas (Sum.inr ρ) b).add (hE_meas (Sum.inr ρ) b)
    have hAm : |(∑ b : Fin p, Sigma_X a b * δ ρ.1 b)| ≤ B * s_delta := by
      calc |(∑ b : Fin p, Sigma_X a b * δ ρ.1 b)|
          ≤ ∑ b : Fin p, |Sigma_X a b * δ ρ.1 b| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ b : Fin p, |Sigma_X a b| * |δ ρ.1 b| := by
            apply Finset.sum_congr rfl; intro b _; rw [abs_mul]
        _ ≤ ∑ b : Fin p, B * |δ ρ.1 b| := by
            apply Finset.sum_le_sum; intro b _
            exact mul_le_mul_of_nonneg_right (hSigma_bound a b) (abs_nonneg _)
        _ = B * ∑ b : Fin p, |δ ρ.1 b| := by rw [Finset.mul_sum]
        _ ≤ B * s_delta := mul_le_mul_of_nonneg_left (hδ ρ.1) hB
    have hamgm : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x * y ≤ (1/2) * (x^2 + y^2) := by
      intro x y hx hy; nlinarith [sq_nonneg (x - y)]
    have hInt_prod : ∀ b : Fin p, Integrable (fun ω => |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ m * |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ m) μ := by
      intro b
      have hIg : Integrable (fun ω => (1/2) * (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ (2*m) + |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m))) μ :=
        ((hInt_2m a).add (hInt_2m b)).const_mul (1/2)
      refine hIg.mono ?_ ?_
      · have hP1 : Measurable (fun ω => |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ m) :=
          ((continuous_abs.pow m).measurable).comp (hXm a)
        have hP2 : Measurable (fun ω => |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ m) :=
          ((continuous_abs.pow m).measurable).comp (hXm b)
        exact (hP1.mul hP2).aestronglyMeasurable
      · filter_upwards with ω
        have hn1 : (0:ℝ) ≤ |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ m * |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ m := by positivity
        have hn2 : (0:ℝ) ≤ (1/2) * (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ (2*m) + |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m)) := by positivity
        rw [Real.norm_of_nonneg hn1, Real.norm_of_nonneg hn2]
        have hA2 : |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ (2*m) = (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ m)^2 := by
          rw [show 2*m = m*2 from by ring, pow_mul]
        have hB2 : |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m) = (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ m)^2 := by
          rw [show 2*m = m*2 from by ring, pow_mul]
        rw [hA2, hB2]
        exact hamgm _ _ (pow_nonneg (abs_nonneg _) m) (pow_nonneg (abs_nonneg _) m)
    have hprod : ∀ b : Fin p, ∫ ω, |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ m * |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ m ∂μ ≤ 2 * (m.factorial:ℝ) * (8*(L:ℝ))^m := by
      intro b
      have hIg : Integrable (fun ω => (1/2) * (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ (2*m) + |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m))) μ :=
        ((hInt_2m a).add (hInt_2m b)).const_mul (1/2)
      have hle : ∀ ω, |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ m * |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ m
          ≤ (1/2) * (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ (2*m) + |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m)) := by
        intro ω
        have hA2 : |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ (2*m) = (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ m)^2 := by
          rw [show 2*m = m*2 from by ring, pow_mul]
        have hB2 : |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m) = (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ m)^2 := by
          rw [show 2*m = m*2 from by ring, pow_mul]
        rw [hA2, hB2]
        exact hamgm _ _ (pow_nonneg (abs_nonneg _) m) (pow_nonneg (abs_nonneg _) m)
      have hcalc : ∫ ω, (1/2) * (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a| ^ (2*m) + |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b| ^ (2*m)) ∂μ ≤ 2 * (m.factorial:ℝ) * (8*(L:ℝ))^m := by
        rw [integral_const_mul, integral_add (hInt_2m a) (hInt_2m b)]
        have ha := heven a
        have hb := heven b
        nlinarith [ha, hb]
      exact le_trans (integral_mono (hInt_prod b) hIg hle) hcalc
    have habs_sub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
      intro a b
      calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
        _ ≤ |a| + |-b| := abs_add_le a (-b)
        _ = |a| + |b| := by rw [abs_neg]
    have hxy : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y)^m ≤ (2:ℝ)^(m-1) * (x^m + y^m) := by
      intro x y hx hy
      have hd := statopia_math_node_3568007364_198afdaf (s := Finset.univ) (w := fun _ : Fin 2 => (1:ℝ)) (A := ![x, y])
        (by intro i _; norm_num) (by intro i _; fin_cases i <;> simp [hx, hy]) m hm
      simpa [Fin.sum_univ_two] using hd
    let g : Ω → ℝ := fun ω => (2:ℝ)^(m-1) * (s_delta^(m-1) * (∑ b : Fin p, |δ ρ.1 b| * (|((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m)) + (B * s_delta)^m)
    have h2 : ∀ ω, |(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a * (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b)| ^ m
        ≤ s_delta^(m-1) * ∑ b : Fin p, |δ ρ.1 b| * (|((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m) := by
      intro ω
      rw [abs_mul, mul_pow]
      calc |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * |(∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b)| ^ m
          ≤ |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * (s_delta^(m-1) * ∑ b : Fin p, |δ ρ.1 b| * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m) :=
            mul_le_mul_of_nonneg_left (hSpow ω) (pow_nonneg (abs_nonneg _) m)
        _ = s_delta^(m-1) * ∑ b : Fin p, |δ ρ.1 b| * (|((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m) := by
            rw [mul_comm (|((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m), mul_assoc, Finset.sum_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro b _
            ring
    have hM : |(∑ b : Fin p, Sigma_X a b * δ ρ.1 b)| ^ m ≤ (B * s_delta)^m := by
      have hBs : (0:ℝ) ≤ B * s_delta := mul_nonneg hB hs_delta
      gcongr
    have hpt : ∀ ω, (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a * (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b) - ∑ b : Fin p, Sigma_X a b * δ ρ.1 b|)^m ≤ g ω := by
      intro ω
      have h2ω := h2 ω
      calc (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a * (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b) - ∑ b : Fin p, Sigma_X a b * δ ρ.1 b|)^m
          ≤ (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a * (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b)| + |(∑ b : Fin p, Sigma_X a b * δ ρ.1 b)|)^m := by
            gcongr
            exact habs_sub _ _
        _ ≤ (2:ℝ)^(m-1) * (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a * (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b)|^m + |(∑ b : Fin p, Sigma_X a b * δ ρ.1 b)|^m) :=
            hxy _ _ (abs_nonneg _) (by positivity)
        _ ≤ (2:ℝ)^(m-1) * (s_delta^(m-1) * ∑ b : Fin p, |δ ρ.1 b| * (|((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m) + (B * s_delta)^m) := by
            apply mul_le_mul_of_nonneg_left
            · exact add_le_add h2ω hM
            · positivity
        _ = g ω := by simp only [g]
    have hSum_int : Integrable (fun ω => s_delta^(m-1) * ∑ b : Fin p, |δ ρ.1 b| * (|((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m)) μ :=
      (integrable_finset_sum Finset.univ (fun b _ => (hInt_prod b).const_mul (|δ ρ.1 b|))).const_mul (s_delta^(m-1))
    have hconst_int : Integrable (fun _ : Ω => (B * s_delta)^m) μ := integrable_const _
    have hg_int : Integrable g μ := (hSum_int.add hconst_int).const_mul ((2:ℝ)^(m-1))
    have hSmeas : Measurable (fun ω => ∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b) :=
      Finset.measurable_sum Finset.univ (fun b _ => (hXm b).mul_const (δ ρ.1 b))
    have hUun : Measurable (fun ω => (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a * (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b) - ∑ b : Fin p, Sigma_X a b * δ ρ.1 b) :=
      ((hXm a).mul hSmeas).sub measurable_const
    have hUmeas : Measurable (fun ω => (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a * (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b) - ∑ b : Fin p, Sigma_X a b * δ ρ.1 b|)^m) :=
      (continuous_abs.pow m).measurable.comp hUun
    have hU_int : Integrable (fun ω => (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a * (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b) - ∑ b : Fin p, Sigma_X a b * δ ρ.1 b|)^m) μ := by
      refine hg_int.mono hUmeas.aestronglyMeasurable ?_
      filter_upwards with ω
      rw [Real.norm_of_nonneg (by positivity)]
      exact le_trans (hpt ω) (le_abs_self (g ω))
    have hUb : ∫ ω, (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a * (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b) - ∑ b : Fin p, Sigma_X a b * δ ρ.1 b|)^m ∂μ ≤ ∫ ω, g ω ∂μ :=
      integral_mono hU_int hg_int hpt
    have hval : ∫ ω, g ω ∂μ
        = (2:ℝ)^(m-1) * (s_delta^(m-1) * (∑ b : Fin p, |δ ρ.1 b| * (∫ ω, |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m ∂μ)) + (B * s_delta)^m) := by
      have e : ∫ ω, g ω ∂μ = ∫ ω, (2:ℝ)^(m-1) * (s_delta^(m-1) * ∑ b : Fin p, |δ ρ.1 b| * (|((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m) + (B * s_delta)^m) ∂μ := rfl
      rw [e, integral_const_mul]
      congr 1
      rw [integral_add hSum_int hconst_int]
      congr 1
      · rw [integral_const_mul]
        congr 1
        rw [integral_finset_sum Finset.univ (fun b _ => (hInt_prod b).const_mul (|δ ρ.1 b|))]
        apply Finset.sum_congr rfl
        intro b _
        rw [integral_const_mul]
      · rw [integral_const]; simp
    have hE2nn : (0:ℝ) ≤ 2 * (m.factorial:ℝ) * (8*(L:ℝ))^m :=
      mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (pow_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg L)) m)
    have hJb : (∑ b : Fin p, |δ ρ.1 b| * (∫ ω, |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m ∂μ)) ≤ s_delta * (2 * (m.factorial:ℝ) * (8*(L:ℝ))^m) := by
      have hb : (∑ b : Fin p, |δ ρ.1 b| * (∫ ω, |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a)| ^ m * |((f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b)| ^ m ∂μ)) ≤ ∑ b : Fin p, |δ ρ.1 b| * (2 * (m.factorial:ℝ) * (8*(L:ℝ))^m) := by
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left (hprod b) (abs_nonneg _)
      rw [← Finset.sum_mul] at hb
      exact le_trans hb (mul_le_mul_of_nonneg_right (hδ ρ.1) hE2nn)
    have hg_le : ∫ ω, g ω ∂μ ≤ (2:ℝ)^(m-1) * (s_delta^(m-1) * (s_delta * (2 * (m.factorial:ℝ) * (8*(L:ℝ))^m)) + (B * s_delta)^m) := by
      rw [hval]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hJb (pow_nonneg hs_delta (m-1))
      · rfl
    have hfinal : (2:ℝ)^(m-1) * (s_delta^(m-1) * (s_delta * (2 * (m.factorial:ℝ) * (8*(L:ℝ))^m)) + (B * s_delta)^m) ≤ ((32 * (L : ℝ) + B) * s_delta * (m : ℝ)) ^ m :=
      statopia_math_node_856880814_cb48915c m hm (L:ℝ) B s_delta hLr0 hB hs_delta
    exact le_trans (le_trans hUb hg_le) hfinal
  refine ⟨key, ?_⟩
  intro ρ a r hr
  have hr1 : 1 ≤ r := by omega
  have h1 := key ρ a r hr1
  have hLr : (0:ℝ) < (L:ℝ) := by simpa using hL
  have hKc0 : (0:ℝ) ≤ 32 * (L:ℝ) + B := by nlinarith [hLr, hB]
  have hKS0 : (0:ℝ) ≤ (32 * (L:ℝ) + B) * s_delta := mul_nonneg hKc0 hs_delta
  have hrr : (r:ℝ)^r ≤ (r.factorial:ℝ) * Real.exp (r:ℝ) := by
    have hx : (0:ℝ) ≤ (r:ℝ) := by positivity
    have hterm : ∀ i ∈ Finset.range (r+1), (0:ℝ) ≤ (r:ℝ)^i / (i.factorial:ℝ) := by
      intro i hi; positivity
    have hmem : r ∈ Finset.range (r+1) := Finset.mem_range.mpr (Nat.lt_succ_self r)
    have hsingle : (r:ℝ)^r / (r.factorial:ℝ) ≤ ∑ i ∈ Finset.range (r+1), (r:ℝ)^i / (i.factorial:ℝ) :=
      Finset.single_le_sum (f := fun i => (r:ℝ)^i / (i.factorial:ℝ)) hterm hmem
    have hsum : (∑ i ∈ Finset.range (r+1), (r:ℝ)^i / (i.factorial:ℝ)) ≤ Real.exp (r:ℝ) :=
      Real.sum_le_exp_of_nonneg hx (r+1)
    have hfac : (0:ℝ) < (r.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos r
    have hle_frac : (r:ℝ)^r / (r.factorial:ℝ) ≤ Real.exp (r:ℝ) := le_trans hsingle hsum
    have hle : (r:ℝ)^r ≤ Real.exp (r:ℝ) * (r.factorial:ℝ) := by
      rw [div_le_iff₀ hfac] at hle_frac
      exact hle_frac
    calc (r:ℝ)^r ≤ Real.exp (r:ℝ) * (r.factorial:ℝ) := hle
      _ = (r.factorial:ℝ) * Real.exp (r:ℝ) := by ring
  have hexp : Real.exp (r:ℝ) = (Real.exp 1)^r := by
    have := Real.exp_nat_mul (1:ℝ) r
    simpa using this
  have hmain : (r:ℝ)^r ≤ (r.factorial:ℝ) * (Real.exp 1)^r := by
    rw [← hexp]; exact hrr
  have hpow : (0:ℝ) ≤ ((32 * (L:ℝ) + B) * s_delta)^r := pow_nonneg hKS0 r
  have hmul : ((32 * (L:ℝ) + B) * s_delta)^r * (r:ℝ)^r
      ≤ ((32 * (L:ℝ) + B) * s_delta)^r * ((r.factorial:ℝ) * (Real.exp 1)^r) :=
    mul_le_mul_of_nonneg_left hmain hpow
  calc ∫ ω, (|(f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) a *
          (∑ b : Fin p, (f (H (Sum.inr ρ) ω) + E (Sum.inr ρ) ω) b * δ ρ.1 b)
        - ∑ b : Fin p, Sigma_X a b * δ ρ.1 b|) ^ r ∂μ
      ≤ ((32 * (L : ℝ) + B) * s_delta * (r : ℝ)) ^ r := h1
    _ = ((32 * (L:ℝ) + B) * s_delta)^r * (r:ℝ)^r := by rw [mul_pow]
    _ ≤ ((32 * (L:ℝ) + B) * s_delta)^r * ((r.factorial:ℝ) * (Real.exp 1)^r) := hmul
    _ = (Nat.factorial r : ℝ) * (Real.exp 1 * (32 * (L : ℝ) + B) * s_delta) ^ r := by
        simp only [mul_pow]; ring
  /- @proof-region region.target-node.session.6f9755c2d5d64b28 end -/

end Statlib.Imported

