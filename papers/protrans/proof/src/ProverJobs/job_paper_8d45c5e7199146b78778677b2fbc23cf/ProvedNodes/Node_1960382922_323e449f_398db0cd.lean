import Lean
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Vocabulary
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Base

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
theorem statopia_math_node_1960382922_323e449f : ∀ (q p K : ℕ) (hq : 1 ≤ q) (hp : 1 ≤ p) (hK : 1 ≤ K)
    (L : NNReal) (hL : 0 < L)
    (n_t : ℕ) (hnt : 0 < n_t)
    (ns : Fin K → ℕ) (hns : ∀ k : Fin K, 0 < ns k)
    (n_s : ℕ) (hns_sum : n_s = ∑ k : Fin K, ns k) (hns_pos : 0 < n_s)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : (Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) → Ω → Fin p → ℝ)
    (H : (Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) → Ω → Fin q → ℝ)
    (f : (Fin q → ℝ) → (Fin p → ℝ))
    (hf_meas : Measurable f)
    (hE_meas : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      Measurable (fun ω => E r ω a))
    (hfH_meas : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      Measurable (fun ω => f (H r ω) a))
    (hE_subg : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      HasSubgaussianMGF (fun ω => E r ω a) L μ)
    (hfH_subg : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a : Fin p),
      HasSubgaussianMGF (fun ω => f (H r ω) a) L μ)
    (hX_int : ∀ (r : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))) (a b : Fin p),
      Integrable (fun ω => (f (H r ω) a + E r ω a) * (f (H r ω) b + E r ω b)) μ)
    (hid : ∀ (r r' : Sum (Fin n_t) (Σ k : Fin K, Fin (ns k))),
      IdentDistrib (fun ω => (E r ω, H r ω)) (fun ω => (E r' ω, H r' ω)) μ μ)
    (Sigma_X : Matrix (Fin p) (Fin p) ℝ)
    (hSigma_X : ∀ (a b : Fin p),
      Sigma_X a b = ∫ ω, (f (H (Sum.inl ⟨0, hnt⟩) ω) a + E (Sum.inl ⟨0, hnt⟩) ω a) *
        (f (H (Sum.inl ⟨0, hnt⟩) ω) b + E (Sum.inl ⟨0, hnt⟩) ω b) ∂μ)
    (delta : Fin K → Fin p → ℝ),
    (∀ (rho : Σ k : Fin K, Fin (ns k)) (a b : Fin p),
      ∫ ω, (f (H (Sum.inr rho) ω) a + E (Sum.inr rho) ω a) *
        (f (H (Sum.inr rho) ω) b + E (Sum.inr rho) ω b) ∂μ = Sigma_X a b) ∧
    (∀ (rho : Σ k : Fin K, Fin (ns k)) (a : Fin p),
      ∫ ω, ((f (H (Sum.inr rho) ω) a + E (Sum.inr rho) ω a) *
          (∑ b : Fin p, (f (H (Sum.inr rho) ω) b + E (Sum.inr rho) ω b) * delta rho.1 b) -
          ∑ b : Fin p, Sigma_X a b * delta rho.1 b) ∂μ = 0) := by
  /- @proof-region region.target-node.session.19a65e6e1b684b1a begin -/
  intro q p K hq hp hK L hL n_t hnt ns hns n_s hns_sum hns_pos Ω instΩ μ instμ E H f
    hf_meas hE_meas hfH_meas hE_subg hfH_subg hX_int hid Sigma_X hSigma_X delta
  have h2 : ∀ (rho : Σ k : Fin K, Fin (ns k)) (a b : Fin p),
      ∫ ω, (f (H (Sum.inr rho) ω) a + E (Sum.inr rho) ω a) *
        (f (H (Sum.inr rho) ω) b + E (Sum.inr rho) ω b) ∂μ = Sigma_X a b := by
    intro rho a b
    rw [hSigma_X a b]
    have hu : Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) =>
        (f z.2 + z.1) a * (f z.2 + z.1) b) := by
      have h1 : Measurable (fun z : (Fin p → ℝ) × (Fin q → ℝ) => f z.2 + z.1) :=
        (hf_meas.comp measurable_snd).add measurable_fst
      exact ((measurable_pi_apply a).comp h1).mul ((measurable_pi_apply b).comp h1)
    simpa only [Function.comp_apply] using
      ((hid (Sum.inr rho) (Sum.inl ⟨0, hnt⟩)).comp hu).integral_eq
  refine ⟨h2, ?_⟩
  · intro rho a
    have heq : (fun ω => (f (H (Sum.inr rho) ω) a + E (Sum.inr rho) ω a) *
        (∑ b : Fin p, (f (H (Sum.inr rho) ω) b + E (Sum.inr rho) ω b) * delta rho.1 b))
        = fun ω => ∑ b : Fin p,
            ((f (H (Sum.inr rho) ω) a + E (Sum.inr rho) ω a) *
              (f (H (Sum.inr rho) ω) b + E (Sum.inr rho) ω b)) * delta rho.1 b := by
      funext ω
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    have hA : Integrable (fun ω => (f (H (Sum.inr rho) ω) a + E (Sum.inr rho) ω a) *
        (∑ b : Fin p, (f (H (Sum.inr rho) ω) b + E (Sum.inr rho) ω b) * delta rho.1 b)) μ := by
      rw [heq]
      exact integrable_finset_sum _ (fun b _ => (hX_int (Sum.inr rho) a b).mul_const _)
    have hstep : ∫ ω, (∑ b : Fin p,
            ((f (H (Sum.inr rho) ω) a + E (Sum.inr rho) ω a) *
              (f (H (Sum.inr rho) ω) b + E (Sum.inr rho) ω b)) * delta rho.1 b) ∂μ
        = ∑ b : Fin p, ∫ ω, ((f (H (Sum.inr rho) ω) a + E (Sum.inr rho) ω a) *
              (f (H (Sum.inr rho) ω) b + E (Sum.inr rho) ω b)) * delta rho.1 b ∂μ :=
      integral_finset_sum _ (fun b _ => (hX_int (Sum.inr rho) a b).mul_const _)
    have hsum : ∫ ω, (f (H (Sum.inr rho) ω) a + E (Sum.inr rho) ω a) *
        (∑ b : Fin p, (f (H (Sum.inr rho) ω) b + E (Sum.inr rho) ω b) * delta rho.1 b) ∂μ
        = ∑ b : Fin p, Sigma_X a b * delta rho.1 b := by
      rw [heq, hstep]
      exact Finset.sum_congr rfl (fun b _ => by rw [integral_mul_const, h2 rho a b])
    have hconst : ∫ ω, (∑ b : Fin p, Sigma_X a b * delta rho.1 b) ∂μ
        = ∑ b : Fin p, Sigma_X a b * delta rho.1 b := by
      simp
    rw [integral_sub hA (integrable_const _)]
    rw [hsum]
    rw [hconst]
    exact sub_self _
  /- @proof-region region.target-node.session.19a65e6e1b684b1a end -/

end Statlib.Imported

