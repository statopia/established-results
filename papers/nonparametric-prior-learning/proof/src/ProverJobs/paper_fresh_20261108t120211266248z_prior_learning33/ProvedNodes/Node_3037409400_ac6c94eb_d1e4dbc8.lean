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
theorem statopia_math_node_3037409400_ac6c94eb : ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {ι : Type*} (bH : HilbertBasis ι ℝ H) (mu : ι → ℝ) (hmu : ∀ i : ι, 0 < mu i)
    (t : ℝ),
    (∀ p q : H, HScaleNorm bH mu t (p - q) = HScaleNorm bH mu t (q - p)) ∧
    (∀ z z' : H, HScaleNorm bH mu t z < ⊤ → HScaleNorm bH mu t z' < ⊤ →
      HScaleNorm bH mu t (z - z') < ⊤) ∧
    (∀ p q : H, HScaleNorm bH mu (-t) p < ⊤ → HScaleNorm bH mu t q < ⊤ →
      |inner ℝ p q| ≤ (HScaleNorm bH mu (-t) p).toReal ^ (1 / 2 : ℝ) *
        (HScaleNorm bH mu t q).toReal ^ (1 / 2 : ℝ)) ∧
    (∀ p q : H, HScaleNorm bH mu t p < ⊤ → HScaleNorm bH mu t q < ⊤ →
      (HScaleDist bH mu t (p - q) 0).toReal ≤
        (HScaleDist bH mu t p 0).toReal + (HScaleDist bH mu t q 0).toReal) := by
  /- @proof-region region.target-node.session.02b2815b5b887269 begin -/
  refine fun bH mu hmu t => ?_
  have hconv : ∀ (s : ℝ) (z : _), HScaleNorm bH mu s z < ⊤ →
      Summable (fun i => Real.rpow (mu i) (-s) * (inner ℝ (bH i) z) ^ 2) := by
    intro s z hz
    simp only [HScaleNorm] at hz
    have hne : ∑' i, ENNReal.ofReal (Real.rpow (mu i) (-s) * (inner ℝ (bH i) z) ^ 2) ≠ ⊤ := hz.ne
    have hh := ENNReal.hasSum_toReal hne
    have hfun : (fun i => (ENNReal.ofReal (Real.rpow (mu i) (-s) * (inner ℝ (bH i) z) ^ 2)).toReal)
        = (fun i => Real.rpow (mu i) (-s) * (inner ℝ (bH i) z) ^ 2) := by
      funext i
      exact ENNReal.toReal_ofReal (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu i) _)) (sq_nonneg _))
    rw [hfun] at hh
    exact hh.summable
  have hback : ∀ (s : ℝ) (z : _),
      Summable (fun i => Real.rpow (mu i) (-s) * (inner ℝ (bH i) z) ^ 2) →
      HScaleNorm bH mu s z < ⊤ := by
    intro s z hsum
    simp only [HScaleNorm]
    have hkey : (∑' i, ENNReal.ofReal (Real.rpow (mu i) (-s) * (inner ℝ (bH i) z) ^ 2))
        = ENNReal.ofReal (∑' i, Real.rpow (mu i) (-s) * (inner ℝ (bH i) z) ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu i) _)) (sq_nonneg _)) hsum).symm
    rw [hkey]
    exact ENNReal.ofReal_lt_top
  have hsub : ∀ z z' : _, HScaleNorm bH mu t z < ⊤ → HScaleNorm bH mu t z' < ⊤ →
      HScaleNorm bH mu t (z - z') < ⊤ := by
    intro z z' hz hz'
    have hs : Summable (fun i => Real.rpow (mu i) (-t) * (inner ℝ (bH i) z) ^ 2) := hconv t z hz
    have hs' : Summable (fun i => Real.rpow (mu i) (-t) * (inner ℝ (bH i) z') ^ 2) := hconv t z' hz'
    apply hback t (z - z')
    refine Summable.of_nonneg_of_le (f := fun i =>
      (Real.rpow (mu i) (-t) * (inner ℝ (bH i) z) ^ 2 + Real.rpow (mu i) (-t) * (inner ℝ (bH i) z) ^ 2)
      + (Real.rpow (mu i) (-t) * (inner ℝ (bH i) z') ^ 2 + Real.rpow (mu i) (-t) * (inner ℝ (bH i) z') ^ 2))
      (fun i => mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))) (sq_nonneg _)) (fun i => ?_) ?_
    · have hi : inner ℝ (bH i) (z - z') = inner ℝ (bH i) z - inner ℝ (bH i) z' := inner_sub_right _ _ _
      rw [hi]
      have hw : (0:ℝ) ≤ Real.rpow (mu i) (-t) := le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))
      nlinarith [mul_nonneg hw (sq_nonneg (inner ℝ (bH i) z + inner ℝ (bH i) z'))]
    · exact (hs.add hs).add (hs'.add hs')
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p q
    simp only [HScaleNorm]
    apply tsum_congr
    intro i
    congr 1
    simp only [inner_sub_right]
    ring
  · exact hsub
  · intro p q hp hq
    have hps : Summable (fun i => Real.rpow (mu i) t * (inner ℝ (bH i) p) ^ 2) := by
      simpa using hconv (-t) p hp
    have hqs : Summable (fun i => Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2) := hconv t q hq
    have hAval : (HScaleNorm bH mu (-t) p).toReal
        = ∑' i, Real.rpow (mu i) t * (inner ℝ (bH i) p) ^ 2 := by
      simp only [HScaleNorm, neg_neg]
      rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_lt_top.ne)]
      exact tsum_congr (fun i => ENNReal.toReal_ofReal
        (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu i) t)) (sq_nonneg _)))
    have hBval : (HScaleNorm bH mu t q).toReal
        = ∑' i, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2 := by
      simp only [HScaleNorm]
      rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_lt_top.ne)]
      exact tsum_congr (fun i => ENNReal.toReal_ofReal
        (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))) (sq_nonneg _)))
    have hww : ∀ i, Real.rpow (mu i) t * Real.rpow (mu i) (-t) = 1 := by
      intro i
      have h := Real.rpow_add (hmu i) t (-t)
      rw [show t + -t = (0 : ℝ) by ring, Real.rpow_zero] at h
      exact h.symm
    have hcs : ∀ s : Finset _, (∑ i ∈ s, inner ℝ p (bH i) * inner ℝ (bH i) q) ^ 2 ≤
        (∑ i ∈ s, Real.rpow (mu i) t * (inner ℝ (bH i) p) ^ 2)
          * (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2) := by
      intro s
      have hfg : ∀ i, (inner ℝ p (bH i) * Real.sqrt (Real.rpow (mu i) t))
          * (inner ℝ (bH i) q * Real.sqrt (Real.rpow (mu i) (-t)))
          = inner ℝ p (bH i) * inner ℝ (bH i) q := by
        intro i
        have h1 : Real.sqrt (Real.rpow (mu i) t) * Real.sqrt (Real.rpow (mu i) (-t)) = 1 := by
          calc Real.sqrt (Real.rpow (mu i) t) * Real.sqrt (Real.rpow (mu i) (-t))
              = Real.sqrt (Real.rpow (mu i) t * Real.rpow (mu i) (-t)) :=
                (Real.sqrt_mul (le_of_lt (Real.rpow_pos_of_pos (hmu i) t)) (Real.rpow (mu i) (-t))).symm
            _ = Real.sqrt 1 := by rw [hww i]
            _ = 1 := Real.sqrt_one
        calc (inner ℝ p (bH i) * Real.sqrt (Real.rpow (mu i) t))
              * (inner ℝ (bH i) q * Real.sqrt (Real.rpow (mu i) (-t)))
            = inner ℝ p (bH i) * inner ℝ (bH i) q
              * (Real.sqrt (Real.rpow (mu i) t) * Real.sqrt (Real.rpow (mu i) (-t))) := by ring
          _ = inner ℝ p (bH i) * inner ℝ (bH i) q := by rw [h1, mul_one]
      have hf2 : ∀ i, (inner ℝ p (bH i) * Real.sqrt (Real.rpow (mu i) t)) ^ 2
          = Real.rpow (mu i) t * (inner ℝ (bH i) p) ^ 2 := by
        intro i
        have hpw : (0:ℝ) ≤ Real.rpow (mu i) t := le_of_lt (Real.rpow_pos_of_pos (hmu i) t)
        rw [mul_pow, Real.sq_sqrt hpw, real_inner_comm p (bH i)]
        ring
      have hg2 : ∀ i, (inner ℝ (bH i) q * Real.sqrt (Real.rpow (mu i) (-t))) ^ 2
          = Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2 := by
        intro i
        have hqw : (0:ℝ) ≤ Real.rpow (mu i) (-t) := le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))
        rw [mul_pow, Real.sq_sqrt hqw]
        ring
      calc (∑ i ∈ s, inner ℝ p (bH i) * inner ℝ (bH i) q) ^ 2
          = (∑ i ∈ s, (inner ℝ p (bH i) * Real.sqrt (Real.rpow (mu i) t))
              * (inner ℝ (bH i) q * Real.sqrt (Real.rpow (mu i) (-t)))) ^ 2 := by
            rw [Finset.sum_congr rfl (fun i _ => hfg i)]
        _ ≤ (∑ i ∈ s, (inner ℝ p (bH i) * Real.sqrt (Real.rpow (mu i) t)) ^ 2)
              * (∑ i ∈ s, (inner ℝ (bH i) q * Real.sqrt (Real.rpow (mu i) (-t))) ^ 2) :=
            Finset.sum_mul_sq_le_sq_mul_sq s _ _
        _ = (∑ i ∈ s, Real.rpow (mu i) t * (inner ℝ (bH i) p) ^ 2)
              * (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2) := by
            rw [Finset.sum_congr rfl (fun i _ => hf2 i), Finset.sum_congr rfl (fun i _ => hg2 i)]
    have hT1 : Tendsto (fun s : Finset _ => ∑ i ∈ s, inner ℝ p (bH i) * inner ℝ (bH i) q)
        atTop (nhds (inner ℝ p q)) :=
      HilbertBasis.hasSum_inner_mul_inner bH p q
    have hS1 : Tendsto (fun s : Finset _ => ∑ i ∈ s, Real.rpow (mu i) t * (inner ℝ (bH i) p) ^ 2)
        atTop (nhds ((HScaleNorm bH mu (-t) p).toReal)) := by
      rw [hAval]
      exact hps.hasSum
    have hS2 : Tendsto (fun s : Finset _ => ∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2)
        atTop (nhds ((HScaleNorm bH mu t q).toReal)) := by
      rw [hBval]
      exact hqs.hasSum
    have hpoint : ∀ s : Finset _, (∑ i ∈ s, inner ℝ p (bH i) * inner ℝ (bH i) q)
        * (∑ i ∈ s, inner ℝ p (bH i) * inner ℝ (bH i) q)
        ≤ (∑ i ∈ s, Real.rpow (mu i) t * (inner ℝ (bH i) p) ^ 2)
          * (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2) := by
      intro s
      have h := hcs s
      nlinarith [h]
    have hsq : inner ℝ p q * inner ℝ p q
        ≤ (HScaleNorm bH mu (-t) p).toReal * (HScaleNorm bH mu t q).toReal :=
      le_of_tendsto_of_tendsto' (hT1.mul hT1) (hS1.mul hS2) hpoint
    have hsq2 : (inner ℝ p q) ^ 2
        ≤ (HScaleNorm bH mu (-t) p).toReal * (HScaleNorm bH mu t q).toReal := by
      nlinarith [hsq]
    have hC : (HScaleNorm bH mu (-t) p).toReal ^ (1 / 2 : ℝ)
          * (HScaleNorm bH mu t q).toReal ^ (1 / 2 : ℝ)
        = Real.sqrt ((HScaleNorm bH mu (-t) p).toReal * (HScaleNorm bH mu t q).toReal) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul ENNReal.toReal_nonneg]
    rw [← Real.sqrt_sq_eq_abs, hC]
    exact Real.sqrt_le_sqrt hsq2
  · intro p q hp hq
    have hpq : HScaleNorm bH mu t (p - q) < ⊤ := hsub p q hp hq
    have hpsum : Summable (fun i => Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2) := hconv t p hp
    have hqsum : Summable (fun i => Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2) := hconv t q hq
    have hdsum : Summable (fun i => Real.rpow (mu i) (-t) * (inner ℝ (bH i) (p - q)) ^ 2) :=
      hconv t (p - q) hpq
    have hPval : (HScaleNorm bH mu t p).toReal
        = ∑' i, Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2 := by
      simp only [HScaleNorm]
      rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_lt_top.ne)]
      exact tsum_congr (fun i => ENNReal.toReal_ofReal
        (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))) (sq_nonneg _)))
    have hQval : (HScaleNorm bH mu t q).toReal
        = ∑' i, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2 := by
      simp only [HScaleNorm]
      rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_lt_top.ne)]
      exact tsum_congr (fun i => ENNReal.toReal_ofReal
        (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))) (sq_nonneg _)))
    have hDval : (HScaleNorm bH mu t (p - q)).toReal
        = ∑' i, Real.rpow (mu i) (-t) * (inner ℝ (bH i) (p - q)) ^ 2 := by
      simp only [HScaleNorm]
      rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_lt_top.ne)]
      exact tsum_congr (fun i => ENNReal.toReal_ofReal
        (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))) (sq_nonneg _)))
    have hcs2 : ∀ s : Finset _,
        (∑ i ∈ s, Real.rpow (mu i) (-t) * inner ℝ (bH i) p * inner ℝ (bH i) q) ^ 2 ≤
          (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2)
            * (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2) := by
      intro s
      have hfg2 : ∀ i, (Real.sqrt (Real.rpow (mu i) (-t)) * inner ℝ (bH i) p)
          * (Real.sqrt (Real.rpow (mu i) (-t)) * inner ℝ (bH i) q)
          = Real.rpow (mu i) (-t) * inner ℝ (bH i) p * inner ℝ (bH i) q := by
        intro i
        have hsq : Real.sqrt (Real.rpow (mu i) (-t)) * Real.sqrt (Real.rpow (mu i) (-t))
            = Real.rpow (mu i) (-t) := by
          calc Real.sqrt (Real.rpow (mu i) (-t)) * Real.sqrt (Real.rpow (mu i) (-t))
              = (Real.sqrt (Real.rpow (mu i) (-t))) ^ 2 := by ring
            _ = Real.rpow (mu i) (-t) :=
                Real.sq_sqrt (le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t)))
        calc (Real.sqrt (Real.rpow (mu i) (-t)) * inner ℝ (bH i) p)
              * (Real.sqrt (Real.rpow (mu i) (-t)) * inner ℝ (bH i) q)
            = (Real.sqrt (Real.rpow (mu i) (-t)) * Real.sqrt (Real.rpow (mu i) (-t)))
              * (inner ℝ (bH i) p * inner ℝ (bH i) q) := by ring
          _ = Real.rpow (mu i) (-t) * inner ℝ (bH i) p * inner ℝ (bH i) q := by
              rw [hsq]; ring
      have hp2 : ∀ i, (Real.sqrt (Real.rpow (mu i) (-t)) * inner ℝ (bH i) p) ^ 2
          = Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2 := by
        intro i
        have hpw : (0:ℝ) ≤ Real.rpow (mu i) (-t) :=
          le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))
        rw [mul_pow, Real.sq_sqrt hpw]
      have hq2 : ∀ i, (Real.sqrt (Real.rpow (mu i) (-t)) * inner ℝ (bH i) q) ^ 2
          = Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2 := by
        intro i
        have hqw : (0:ℝ) ≤ Real.rpow (mu i) (-t) :=
          le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))
        rw [mul_pow, Real.sq_sqrt hqw]
      calc (∑ i ∈ s, Real.rpow (mu i) (-t) * inner ℝ (bH i) p * inner ℝ (bH i) q) ^ 2
          = (∑ i ∈ s, (Real.sqrt (Real.rpow (mu i) (-t)) * inner ℝ (bH i) p)
              * (Real.sqrt (Real.rpow (mu i) (-t)) * inner ℝ (bH i) q)) ^ 2 := by
            rw [Finset.sum_congr rfl (fun i _ => hfg2 i)]
        _ ≤ (∑ i ∈ s, (Real.sqrt (Real.rpow (mu i) (-t)) * inner ℝ (bH i) p) ^ 2)
              * (∑ i ∈ s, (Real.sqrt (Real.rpow (mu i) (-t)) * inner ℝ (bH i) q) ^ 2) :=
            Finset.sum_mul_sq_le_sq_mul_sq s _ _
        _ = (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2)
              * (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2) := by
            rw [Finset.sum_congr rfl (fun i _ => hp2 i), Finset.sum_congr rfl (fun i _ => hq2 i)]
    have hpoint : ∀ s : Finset _,
        (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) (p - q)) ^ 2)
        ≤ (Real.sqrt (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2)
            + Real.sqrt (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2))
          * (Real.sqrt (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2)
            + Real.sqrt (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2)) := by
      intro s
      set S1 := ∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2 with hS1
      set S2 := ∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2 with hS2
      set Cc := ∑ i ∈ s, Real.rpow (mu i) (-t) * inner ℝ (bH i) p * inner ℝ (bH i) q with hC
      have hS1nn : (0:ℝ) ≤ S1 := by
        rw [hS1]
        exact Finset.sum_nonneg (fun i _ =>
          mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))) (sq_nonneg _))
      have hS2nn : (0:ℝ) ≤ S2 := by
        rw [hS2]
        exact Finset.sum_nonneg (fun i _ =>
          mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu i) (-t))) (sq_nonneg _))
      have hCsq : Cc ^ 2 ≤ S1 * S2 := by
        have h := hcs2 s
        rwa [hC, hS1, hS2]
      have hident : (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) (p - q)) ^ 2)
          = S1 + S2 - 2 * Cc := by
        rw [hS1, hS2, hC, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [inner_sub_right]
        ring
      have hneg : -Cc ≤ Real.sqrt S1 * Real.sqrt S2 := by
        by_cases hC0 : (0:ℝ) ≤ Cc
        · have h0 : (0:ℝ) ≤ Real.sqrt S1 * Real.sqrt S2 :=
            mul_nonneg (Real.sqrt_nonneg S1) (Real.sqrt_nonneg S2)
          linarith
        · have hCn : Cc < 0 := not_le.mp hC0
          have hsq2 : (-Cc) ^ 2 ≤ (Real.sqrt S1 * Real.sqrt S2) ^ 2 := by
            have h2 : (Real.sqrt S1 * Real.sqrt S2) ^ 2 = S1 * S2 := by
              rw [mul_pow, Real.sq_sqrt hS1nn, Real.sq_sqrt hS2nn]
            rw [h2]
            nlinarith [hCsq]
          have hle := Real.sqrt_le_sqrt hsq2
          rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ -Cc),
            Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg S1) (Real.sqrt_nonneg S2))] at hle
          exact hle
      have hS : (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) (p - q)) ^ 2)
          ≤ (Real.sqrt S1 + Real.sqrt S2) * (Real.sqrt S1 + Real.sqrt S2) := by
        nlinarith [hident, hneg, Real.sq_sqrt hS1nn, Real.sq_sqrt hS2nn]
      rwa [hS1, hS2] at hS
    have hLHS : Tendsto (fun s : Finset _ =>
        ∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) (p - q)) ^ 2)
        atTop (nhds ((HScaleNorm bH mu t (p - q)).toReal)) := by
      rw [hDval]
      exact hdsum.hasSum
    have hS1t : Tendsto (fun s : Finset _ =>
        ∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2)
        atTop (nhds ((HScaleNorm bH mu t p).toReal)) := by
      rw [hPval]
      exact hpsum.hasSum
    have hS2t : Tendsto (fun s : Finset _ =>
        ∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2)
        atTop (nhds ((HScaleNorm bH mu t q).toReal)) := by
      rw [hQval]
      exact hqsum.hasSum
    have hr1 : Tendsto (fun s : Finset _ =>
        Real.sqrt (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2))
        atTop (nhds (Real.sqrt ((HScaleNorm bH mu t p).toReal))) :=
      (Real.continuous_sqrt.tendsto ((HScaleNorm bH mu t p).toReal)).comp hS1t
    have hr2 : Tendsto (fun s : Finset _ =>
        Real.sqrt (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2))
        atTop (nhds (Real.sqrt ((HScaleNorm bH mu t q).toReal))) :=
      (Real.continuous_sqrt.tendsto ((HScaleNorm bH mu t q).toReal)).comp hS2t
    have hR : Tendsto (fun s : Finset _ =>
        (Real.sqrt (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2)
          + Real.sqrt (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2))
        * (Real.sqrt (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) p) ^ 2)
          + Real.sqrt (∑ i ∈ s, Real.rpow (mu i) (-t) * (inner ℝ (bH i) q) ^ 2))) atTop
        (nhds ((Real.sqrt ((HScaleNorm bH mu t p).toReal)
            + Real.sqrt ((HScaleNorm bH mu t q).toReal))
          * (Real.sqrt ((HScaleNorm bH mu t p).toReal)
            + Real.sqrt ((HScaleNorm bH mu t q).toReal)))) :=
      (hr1.add hr2).mul (hr1.add hr2)
    have hDle : (HScaleNorm bH mu t (p - q)).toReal
        ≤ (Real.sqrt ((HScaleNorm bH mu t p).toReal) + Real.sqrt ((HScaleNorm bH mu t q).toReal))
          * (Real.sqrt ((HScaleNorm bH mu t p).toReal) + Real.sqrt ((HScaleNorm bH mu t q).toReal)) :=
      le_of_tendsto_of_tendsto' hLHS hR hpoint
    have hPQ : (0:ℝ) ≤ Real.sqrt ((HScaleNorm bH mu t p).toReal)
        + Real.sqrt ((HScaleNorm bH mu t q).toReal) := by
      have h1 := Real.sqrt_nonneg ((HScaleNorm bH mu t p).toReal)
      have h2 := Real.sqrt_nonneg ((HScaleNorm bH mu t q).toReal)
      linarith
    have hfin : Real.sqrt ((HScaleNorm bH mu t (p - q)).toReal)
        ≤ Real.sqrt ((HScaleNorm bH mu t p).toReal)
          + Real.sqrt ((HScaleNorm bH mu t q).toReal) := by
      have h1 : Real.sqrt ((HScaleNorm bH mu t (p - q)).toReal)
          ≤ Real.sqrt ((Real.sqrt ((HScaleNorm bH mu t p).toReal)
              + Real.sqrt ((HScaleNorm bH mu t q).toReal)) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [hDle])
      rwa [Real.sqrt_sq hPQ] at h1
    simp only [HScaleDist, sub_zero]
    simp only [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
    exact hfin
  /- @proof-region region.target-node.session.02b2815b5b887269 end -/

end Statlib.Imported
end

