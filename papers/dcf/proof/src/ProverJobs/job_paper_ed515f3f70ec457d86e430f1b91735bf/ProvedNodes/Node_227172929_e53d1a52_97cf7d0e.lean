import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_227172929_e53d1a52 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m p : ℕ} (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hX : ∀ i : Fin n, Measurable (X i))
    (hY : ∀ i : Fin m, Measurable (Y i)),
    ∀ j : Fin p,
      ∫ ω, (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P
        = ((∑ i : Fin n, (n : ℝ)⁻¹ • covX P muX X i)
            + ∑ i : Fin m, ((delta n m) ^ 2 * (m : ℝ)⁻¹) • covY P muY Y i) j j := by
  /- @proof-region region.target-node.session.c0f6fd389397d7ea begin -/
  intro Ω instΩ P instP n m p delta muX muY X Y F G hindep hXmean hYmean hXL2 hYL2 hX hY j
  have hn : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) = Real.sqrt (n : ℝ) := by
    have hn' : (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt (n : ℝ) := by
      rw [sq, ← mul_assoc]
      by_cases h0 : Real.sqrt (n : ℝ) = 0
      · simp [h0]
      · rw [inv_mul_cancel₀ h0, one_mul]
    calc (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ)
        = (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ)) ^ 2 := by
          rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      _ = Real.sqrt (n : ℝ) := hn'
  have hm : (Real.sqrt (m : ℝ))⁻¹ * (m : ℝ) = Real.sqrt (m : ℝ) := by
    have hm' : (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ)) ^ 2 = Real.sqrt (m : ℝ) := by
      rw [sq, ← mul_assoc]
      by_cases h0 : Real.sqrt (m : ℝ) = 0
      · simp [h0]
      · rw [inv_mul_cancel₀ h0, one_mul]
    calc (Real.sqrt (m : ℝ))⁻¹ * (m : ℝ)
        = (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ)) ^ 2 := by
          rw [Real.sq_sqrt (Nat.cast_nonneg m)]
      _ = Real.sqrt (m : ℝ) := hm'
  have hXsum : (∑ i : Fin n, muX j) = (n : ℝ) * muX j := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hYsum : (∑ i : Fin m, muY j) = (m : ℝ) * muY j := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hXs : ∀ ω : Ω, (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, X i ω j - Real.sqrt (n : ℝ) * muX j
      = ∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ * (X i ω j - muX j) := by
    intro ω
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hXsum, mul_sub]
    have hstep : (Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) * muX j) = Real.sqrt (n : ℝ) * muX j := by
      rw [← mul_assoc, hn]
    rw [hstep]
  have hYs : ∀ ω : Ω, delta n m * ((Real.sqrt (m : ℝ))⁻¹ * ∑ i : Fin m, Y i ω j)
        - delta n m * Real.sqrt (m : ℝ) * muY j
      = ∑ i : Fin m, (delta n m * (Real.sqrt (m : ℝ))⁻¹) * (Y i ω j - muY j) := by
    intro ω
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hYsum, mul_sub]
    have hstep : (delta n m * (Real.sqrt (m : ℝ))⁻¹) * ((m : ℝ) * muY j)
        = delta n m * Real.sqrt (m : ℝ) * muY j := by
      calc (delta n m * (Real.sqrt (m : ℝ))⁻¹) * ((m : ℝ) * muY j)
          = (delta n m * ((Real.sqrt (m : ℝ))⁻¹ * (m : ℝ))) * muY j := by ring
        _ = delta n m * Real.sqrt (m : ℝ) * muY j := by rw [hm]
    rw [hstep]
    ring
  set c : Fin n ⊕ Fin m → ℝ :=
    Sum.elim (fun _ => (Real.sqrt (n : ℝ))⁻¹) (fun _ => delta n m * (Real.sqrt (m : ℝ))⁻¹) with hc
  set W : Fin n ⊕ Fin m → Ω → ℝ :=
    Sum.elim (fun i ω => X i ω j - muX j) (fun i ω => Y i ω j - muY j) with hW
  set g : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → (Fin p → ℝ) → ℝ :=
    Sum.elim (fun _ v => v j - muX j)
      (Sum.elim (fun _ v => v j - muY j) (Sum.elim (fun _ _ => 0) (fun _ _ => 0))) with hg
  have hgmeas : ∀ t, Measurable (g t) := by
    intro t
    rcases t with i | i | i | i
    · simp only [hg, Sum.elim_inl, Sum.elim_inr]
      exact (measurable_pi_apply j).sub measurable_const
    · simp only [hg, Sum.elim_inl, Sum.elim_inr]
      exact (measurable_pi_apply j).sub measurable_const
    · simp only [hg, Sum.elim_inl, Sum.elim_inr]
      exact measurable_const
    · simp only [hg, Sum.elim_inl, Sum.elim_inr]
      exact measurable_const
  set Wbig : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → Ω → ℝ :=
    fun t => g t ∘ jointFam X Y F G t with hWbig
  have hindWbig : iIndepFun Wbig P := hindep.comp g hgmeas
  have hWind : ∀ t t' : Fin n ⊕ Fin m, t ≠ t' → W t ⟂ᵢ[P] W t' := by
    rintro (i | i) (i' | i') hne
    · have hii : i ≠ i' := fun e => hne (by rw [e])
      exact hindWbig.indepFun (fun e => hii (Sum.inl_injective e))
    · refine hindWbig.indepFun (i := Sum.inl i) (j := Sum.inr (Sum.inl i')) ?_
      intro h
      cases h
    · refine hindWbig.indepFun (i := Sum.inr (Sum.inl i)) (j := Sum.inl i') ?_
      intro h
      cases h
    · have hii : i ≠ i' := fun e => hne (by rw [e])
      exact hindWbig.indepFun (fun e => hii (Sum.inl_injective (Sum.inr_injective e)))
  have hWL2 : ∀ t : Fin n ⊕ Fin m, MemLp (W t) 2 P := by
    rintro (i | i)
    · simp only [hW, Sum.elim_inl]
      exact (hXL2 i j).sub (memLp_const (muX j))
    · simp only [hW, Sum.elim_inr]
      exact (hYL2 i j).sub (memLp_const (muY j))
  have hWmean : ∀ t : Fin n ⊕ Fin m, ∫ ω, W t ω ∂P = 0 := by
    rintro (i | i)
    · simp only [hW, Sum.elim_inl]
      rw [MeasureTheory.integral_sub ((hXL2 i j).integrable (by norm_num))
        (integrable_const (muX j))]
      simp [hXmean i j]
    · simp only [hW, Sum.elim_inr]
      rw [MeasureTheory.integral_sub ((hYL2 i j).integrable (by norm_num))
        (integrable_const (muY j))]
      simp [hYmean i j]
  have hIntPair : ∀ a b : Fin n ⊕ Fin m,
      Integrable (fun ω => (c a * W a ω) * (c b * W b ω)) P := by
    intro a b
    have h1 : (fun ω => (c a * W a ω) * (c b * W b ω))
        = fun ω => (c a * c b) * (W a ω * W b ω) := by
      funext ω
      ring
    rw [h1]
    have h2 : Integrable (fun ω => W a ω * W b ω) P :=
      MeasureTheory.MemLp.integrable_mul (hWL2 a) (hWL2 b)
    simpa [smul_eq_mul] using h2.const_mul (c a * c b)
  have key : ∫ ω, (∑ t : Fin n ⊕ Fin m, c t * W t ω) ^ 2 ∂P
      = ∑ t : Fin n ⊕ Fin m, c t ^ 2 * ∫ ω, (W t ω) ^ 2 ∂P := by
    have hval : ∀ a b : Fin n ⊕ Fin m,
        ∫ ω, (c a * W a ω) * (c b * W b ω) ∂P
          = if a = b then c a ^ 2 * ∫ ω, (W a ω) ^ 2 ∂P else 0 := by
      intro a b
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl]
        have e1 : (fun ω => (c a * W a ω) * (c a * W a ω))
            = fun ω => c a * c a * (W a ω * W a ω) := by
          funext ω
          ring
        rw [e1, MeasureTheory.integral_const_mul]
        have e2 : (∫ ω, W a ω * W a ω ∂P) = ∫ ω, (W a ω) ^ 2 ∂P := by
          congr 1
          funext ω
          ring
        rw [e2]
        ring
      · rw [if_neg hab]
        have e1 : (fun ω => (c a * W a ω) * (c b * W b ω))
            = fun ω => (c a * c b) * (W a ω * W b ω) := by
          funext ω
          ring
        rw [e1, MeasureTheory.integral_const_mul]
        have e2 : (∫ ω, W a ω * W b ω ∂P)
            = (∫ ω, W a ω ∂P) * ∫ ω, W b ω ∂P :=
          ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral (hWind a b hab)
            (hWL2 a).aestronglyMeasurable (hWL2 b).aestronglyMeasurable
        rw [e2, hWmean a, hWmean b]
        ring
    have hsq : (fun ω => (∑ t : Fin n ⊕ Fin m, c t * W t ω) ^ 2)
        = fun ω => ∑ p : (Fin n ⊕ Fin m) × (Fin n ⊕ Fin m),
            (c p.1 * W p.1 ω) * (c p.2 * W p.2 ω) := by
      funext ω
      rw [sq, Finset.sum_mul_sum]
      rw [Fintype.sum_prod_type]
    rw [hsq]
    rw [MeasureTheory.integral_finset_sum Finset.univ (fun p _ => hIntPair p.1 p.2)]
    rw [Finset.sum_congr rfl (fun p _ => hval p.1 p.2)]
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_ite_eq]
  have hcomb : ∀ ω : Ω,
      combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j
        = ∑ t : Fin n ⊕ Fin m, c t * W t ω := by
    intro ω
    rw [hc, hW]
    simp only [combVec, normSum, Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type]
    rw [show (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, X i ω j - Real.sqrt (n : ℝ) * muX j
          + delta n m * ((Real.sqrt (m : ℝ))⁻¹ * ∑ i : Fin m, Y i ω j)
          - delta n m * Real.sqrt (m : ℝ) * muY j
        = ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, X i ω j - Real.sqrt (n : ℝ) * muX j)
          + (delta n m * ((Real.sqrt (m : ℝ))⁻¹ * ∑ i : Fin m, Y i ω j)
            - delta n m * Real.sqrt (m : ℝ) * muY j) from by ring]
    rw [hXs ω, hYs ω]
  have hmain : ∫ ω, (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2 ∂P
      = ∑ t : Fin n ⊕ Fin m, c t ^ 2 * ∫ ω, (W t ω) ^ 2 ∂P := by
    have h1 : (fun ω => (combVec n m (delta n m) muX muY (fun i => X i ω) (fun i => Y i ω) j) ^ 2)
        = fun ω => (∑ t : Fin n ⊕ Fin m, c t * W t ω) ^ 2 := by
      funext ω
      rw [hcomb ω]
    rw [h1]
    exact key
  rw [hmain]
  rw [Fintype.sum_sum_type]
  have hinv2 : (Real.sqrt (n : ℝ))⁻¹ ^ 2 = ((n : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hinv2m : (delta n m * (Real.sqrt (m : ℝ))⁻¹) ^ 2
      = (delta n m) ^ 2 * ((m : ℝ))⁻¹ := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hA : ∀ i : Fin n, c (Sum.inl i) ^ 2 * ∫ ω, (W (Sum.inl i) ω) ^ 2 ∂P
      = ((n : ℝ))⁻¹ * ∫ ω, (X i ω j - muX j) ^ 2 ∂P := by
    intro i
    have hc1 : c (Sum.inl i) = (Real.sqrt (n : ℝ))⁻¹ := by
      simp [hc, Sum.elim_inl, Sum.elim_inr]
    have hW1 : W (Sum.inl i) = fun ω => X i ω j - muX j := by
      simp only [hW, Sum.elim_inl]
    simp only [hc1, hW1, hinv2]
  have hB : ∀ i : Fin m, c (Sum.inr i) ^ 2 * ∫ ω, (W (Sum.inr i) ω) ^ 2 ∂P
      = ((delta n m) ^ 2 * ((m : ℝ))⁻¹) * ∫ ω, (Y i ω j - muY j) ^ 2 ∂P := by
    intro i
    have hc2 : c (Sum.inr i) = delta n m * (Real.sqrt (m : ℝ))⁻¹ := by
      simp [hc, Sum.elim_inl, Sum.elim_inr]
    have hW2 : W (Sum.inr i) = fun ω => Y i ω j - muY j := by
      simp only [hW, Sum.elim_inr]
    simp only [hc2, hW2, hinv2m]
  have hR : ((∑ i : Fin n, (n : ℝ)⁻¹ • covX P muX X i)
              + ∑ i : Fin m, ((delta n m) ^ 2 * (m : ℝ)⁻¹) • covY P muY Y i) j j
      = ∑ i : Fin n, ((n : ℝ))⁻¹ * ∫ ω, (X i ω j - muX j) ^ 2 ∂P
          + ∑ i : Fin m, ((delta n m) ^ 2 * ((m : ℝ))⁻¹) * ∫ ω, (Y i ω j - muY j) ^ 2 ∂P := by
    simp [covX, covY, sq, smul_eq_mul, Matrix.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ => hA i), Finset.sum_congr rfl (fun i _ => hB i), hR]
  /- @proof-region region.target-node.session.c0f6fd389397d7ea end -/

end

end Statlib.Imported

