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
theorem statopia_math_node_2221445841_9c042308 : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ιH : Type*) (bH : HilbertBasis ιH ℝ H) (mu : ιH → ℝ)
    (hmu_pos : ∀ i : ιH, 0 < mu i) (tH : ℝ)
    (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k) (tU : ℝ),
    (∀ v w : H, (HScaleNorm bH mu tH (v + w)) ^ (1 / 2 : ℝ) ≤
      (HScaleNorm bH mu tH v) ^ (1 / 2 : ℝ) + (HScaleNorm bH mu tH w) ^ (1 / 2 : ℝ)) ∧
    (∀ v w : H, (HScaleNorm bH mu tH (v - w)) ^ (1 / 2 : ℝ) ≤
      (HScaleNorm bH mu tH v) ^ (1 / 2 : ℝ) + (HScaleNorm bH mu tH w) ^ (1 / 2 : ℝ)) ∧
    (∀ u1 u2 : U, (UScaleNorm e lam tU (u1 + u2)) ^ (1 / 2 : ℝ) ≤
      (UScaleNorm e lam tU u1) ^ (1 / 2 : ℝ) + (UScaleNorm e lam tU u2) ^ (1 / 2 : ℝ)) ∧
    (∀ u1 u2 : U, (UScaleNorm e lam tU (u1 - u2)) ^ (1 / 2 : ℝ) ≤
      (UScaleNorm e lam tU u1) ^ (1 / 2 : ℝ) + (UScaleNorm e lam tU u2) ^ (1 / 2 : ℝ)) := by
  /- @proof-region region.target-node.session.283b4001a3b5300f begin -/
  intro H hH1 hH2 ιH bH mu hmu_pos tH U hU1 hU2 e lam hlam_pos tU
  have hz : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  have hsqrt_ofReal : ∀ x : ℝ, 0 ≤ x →
      ENNReal.ofReal (Real.sqrt x) = (ENNReal.ofReal x) ^ (1 / 2 : ℝ) := by
    intro x hx
    rcases eq_or_lt_of_le hx with h | h
    · subst h
      rw [Real.sqrt_zero, ENNReal.ofReal_zero, hz]
    · rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_pos h]
  have hSS : ∀ S : ℝ≥0∞, (S ^ 2) ^ (1 / 2 : ℝ) = S := by
    intro S
    rcases eq_or_ne S ⊤ with hT | hT
    · subst hT
      have h2 : (⊤ : ℝ≥0∞) ^ 2 = ⊤ := by simp
      rw [h2, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    · conv_lhs => rw [← ENNReal.ofReal_toReal hT]
      rw [← ENNReal.ofReal_pow ENNReal.toReal_nonneg]
      rw [← hsqrt_ofReal (S.toReal ^ 2) (by positivity)]
      rw [Real.sqrt_sq ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hT]
  have keyH : ∀ (a b : ιH → ℝ),
      (∑' i, ENNReal.ofReal ((a i + b i) ^ 2)) ^ (1 / 2 : ℝ) ≤
        (∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
          (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ) := by
    intro a b
    have hreal : ∀ F : Finset ιH, ∑ i ∈ F, (a i + b i) ^ 2 ≤
        (Real.sqrt (∑ i ∈ F, a i ^ 2) + Real.sqrt (∑ i ∈ F, b i ^ 2)) ^ 2 := by
      intro F
      have hA : 0 ≤ ∑ i ∈ F, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (a i)
      have hB : 0 ≤ ∑ i ∈ F, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (b i)
      have hsA : Real.sqrt (∑ i ∈ F, a i ^ 2) ^ 2 = ∑ i ∈ F, a i ^ 2 := Real.sq_sqrt hA
      have hsB : Real.sqrt (∑ i ∈ F, b i ^ 2) ^ 2 = ∑ i ∈ F, b i ^ 2 := Real.sq_sqrt hB
      have hcs : ∑ i ∈ F, a i * b i ≤
          Real.sqrt (∑ i ∈ F, a i ^ 2) * Real.sqrt (∑ i ∈ F, b i ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt F a b
      have hexp : ∑ i ∈ F, (a i + b i) ^ 2 =
          ∑ i ∈ F, a i ^ 2 + 2 * (∑ i ∈ F, a i * b i) + ∑ i ∈ F, b i ^ 2 := by
        have h1 : ∀ i ∈ F, (a i + b i) ^ 2 = a i ^ 2 + 2 * (a i * b i) + b i ^ 2 :=
          fun i _ => by ring
        rw [Finset.sum_congr rfl h1]
        simp only [Finset.sum_add_distrib]
        rw [Finset.mul_sum]
      nlinarith [hexp, hcs, hsA, hsB]
    have hterm : ∀ F : Finset ιH,
        ∑ i ∈ F, ENNReal.ofReal ((a i + b i) ^ 2) ≤
          ((∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
            (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 := by
      intro F
      have hX : (0 : ℝ) ≤ Real.sqrt (∑ i ∈ F, a i ^ 2) + Real.sqrt (∑ i ∈ F, b i ^ 2) := by
        positivity
      have hbA : ENNReal.ofReal (∑ i ∈ F, a i ^ 2) ≤ ∑' i, ENNReal.ofReal ((a i) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (a i))]
        exact ENNReal.sum_le_tsum F
      have hbB : ENNReal.ofReal (∑ i ∈ F, b i ^ 2) ≤ ∑' i, ENNReal.ofReal ((b i) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (b i))]
        exact ENNReal.sum_le_tsum F
      have hsa : ENNReal.ofReal (Real.sqrt (∑ i ∈ F, a i ^ 2)) ≤
          (∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [hsqrt_ofReal (∑ i ∈ F, a i ^ 2) (Finset.sum_nonneg fun i _ => sq_nonneg (a i))]
        exact ENNReal.rpow_le_rpow hbA (by norm_num)
      have hsb : ENNReal.ofReal (Real.sqrt (∑ i ∈ F, b i ^ 2)) ≤
          (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [hsqrt_ofReal (∑ i ∈ F, b i ^ 2) (Finset.sum_nonneg fun i _ => sq_nonneg (b i))]
        exact ENNReal.rpow_le_rpow hbB (by norm_num)
      have h4 : ENNReal.ofReal (Real.sqrt (∑ i ∈ F, a i ^ 2) + Real.sqrt (∑ i ∈ F, b i ^ 2)) ≤
          (∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
            (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ) :=
        le_trans ENNReal.ofReal_add_le (add_le_add hsa hsb)
      have h5 : (ENNReal.ofReal (Real.sqrt (∑ i ∈ F, a i ^ 2) +
            Real.sqrt (∑ i ∈ F, b i ^ 2))) ^ 2 ≤
          ((∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
            (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_le_mul' h4 h4
      calc ∑ i ∈ F, ENNReal.ofReal ((a i + b i) ^ 2)
          = ENNReal.ofReal (∑ i ∈ F, (a i + b i) ^ 2) :=
            (ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (a i + b i))).symm
        _ ≤ ENNReal.ofReal ((Real.sqrt (∑ i ∈ F, a i ^ 2) +
              Real.sqrt (∑ i ∈ F, b i ^ 2)) ^ 2) := ENNReal.ofReal_le_ofReal (hreal F)
        _ = (ENNReal.ofReal (Real.sqrt (∑ i ∈ F, a i ^ 2) +
              Real.sqrt (∑ i ∈ F, b i ^ 2))) ^ 2 := ENNReal.ofReal_pow hX 2
        _ ≤ ((∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
              (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 := h5
    have hXle : (∑' i, ENNReal.ofReal ((a i + b i) ^ 2)) ≤
        ((∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
          (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [ENNReal.tsum_eq_iSup_sum]
      exact iSup_le hterm
    calc (∑' i, ENNReal.ofReal ((a i + b i) ^ 2)) ^ (1 / 2 : ℝ)
        ≤ (((∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
            (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hXle (by norm_num)
      _ = (∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
            (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ) := hSS _
  have keyU : ∀ (a b : ℕ → ℝ),
      (∑' i, ENNReal.ofReal ((a i + b i) ^ 2)) ^ (1 / 2 : ℝ) ≤
        (∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
          (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ) := by
    intro a b
    have hreal : ∀ F : Finset ℕ, ∑ i ∈ F, (a i + b i) ^ 2 ≤
        (Real.sqrt (∑ i ∈ F, a i ^ 2) + Real.sqrt (∑ i ∈ F, b i ^ 2)) ^ 2 := by
      intro F
      have hA : 0 ≤ ∑ i ∈ F, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (a i)
      have hB : 0 ≤ ∑ i ∈ F, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (b i)
      have hsA : Real.sqrt (∑ i ∈ F, a i ^ 2) ^ 2 = ∑ i ∈ F, a i ^ 2 := Real.sq_sqrt hA
      have hsB : Real.sqrt (∑ i ∈ F, b i ^ 2) ^ 2 = ∑ i ∈ F, b i ^ 2 := Real.sq_sqrt hB
      have hcs : ∑ i ∈ F, a i * b i ≤
          Real.sqrt (∑ i ∈ F, a i ^ 2) * Real.sqrt (∑ i ∈ F, b i ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt F a b
      have hexp : ∑ i ∈ F, (a i + b i) ^ 2 =
          ∑ i ∈ F, a i ^ 2 + 2 * (∑ i ∈ F, a i * b i) + ∑ i ∈ F, b i ^ 2 := by
        have h1 : ∀ i ∈ F, (a i + b i) ^ 2 = a i ^ 2 + 2 * (a i * b i) + b i ^ 2 :=
          fun i _ => by ring
        rw [Finset.sum_congr rfl h1]
        simp only [Finset.sum_add_distrib]
        rw [Finset.mul_sum]
      nlinarith [hexp, hcs, hsA, hsB]
    have hterm : ∀ F : Finset ℕ,
        ∑ i ∈ F, ENNReal.ofReal ((a i + b i) ^ 2) ≤
          ((∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
            (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 := by
      intro F
      have hX : (0 : ℝ) ≤ Real.sqrt (∑ i ∈ F, a i ^ 2) + Real.sqrt (∑ i ∈ F, b i ^ 2) := by
        positivity
      have hbA : ENNReal.ofReal (∑ i ∈ F, a i ^ 2) ≤ ∑' i, ENNReal.ofReal ((a i) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (a i))]
        exact ENNReal.sum_le_tsum F
      have hbB : ENNReal.ofReal (∑ i ∈ F, b i ^ 2) ≤ ∑' i, ENNReal.ofReal ((b i) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (b i))]
        exact ENNReal.sum_le_tsum F
      have hsa : ENNReal.ofReal (Real.sqrt (∑ i ∈ F, a i ^ 2)) ≤
          (∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [hsqrt_ofReal (∑ i ∈ F, a i ^ 2) (Finset.sum_nonneg fun i _ => sq_nonneg (a i))]
        exact ENNReal.rpow_le_rpow hbA (by norm_num)
      have hsb : ENNReal.ofReal (Real.sqrt (∑ i ∈ F, b i ^ 2)) ≤
          (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [hsqrt_ofReal (∑ i ∈ F, b i ^ 2) (Finset.sum_nonneg fun i _ => sq_nonneg (b i))]
        exact ENNReal.rpow_le_rpow hbB (by norm_num)
      have h4 : ENNReal.ofReal (Real.sqrt (∑ i ∈ F, a i ^ 2) + Real.sqrt (∑ i ∈ F, b i ^ 2)) ≤
          (∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
            (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ) :=
        le_trans ENNReal.ofReal_add_le (add_le_add hsa hsb)
      have h5 : (ENNReal.ofReal (Real.sqrt (∑ i ∈ F, a i ^ 2) +
            Real.sqrt (∑ i ∈ F, b i ^ 2))) ^ 2 ≤
          ((∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
            (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_le_mul' h4 h4
      calc ∑ i ∈ F, ENNReal.ofReal ((a i + b i) ^ 2)
          = ENNReal.ofReal (∑ i ∈ F, (a i + b i) ^ 2) :=
            (ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (a i + b i))).symm
        _ ≤ ENNReal.ofReal ((Real.sqrt (∑ i ∈ F, a i ^ 2) +
              Real.sqrt (∑ i ∈ F, b i ^ 2)) ^ 2) := ENNReal.ofReal_le_ofReal (hreal F)
        _ = (ENNReal.ofReal (Real.sqrt (∑ i ∈ F, a i ^ 2) +
              Real.sqrt (∑ i ∈ F, b i ^ 2))) ^ 2 := ENNReal.ofReal_pow hX 2
        _ ≤ ((∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
              (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 := h5
    have hXle : (∑' i, ENNReal.ofReal ((a i + b i) ^ 2)) ≤
        ((∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
          (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [ENNReal.tsum_eq_iSup_sum]
      exact iSup_le hterm
    calc (∑' i, ENNReal.ofReal ((a i + b i) ^ 2)) ^ (1 / 2 : ℝ)
        ≤ (((∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
            (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hXle (by norm_num)
      _ = (∑' i, ENNReal.ofReal ((a i) ^ 2)) ^ (1 / 2 : ℝ) +
            (∑' i, ENNReal.ofReal ((b i) ^ 2)) ^ (1 / 2 : ℝ) := hSS _
  have addH : ∀ v w : H, (HScaleNorm bH mu tH (v + w)) ^ (1 / 2 : ℝ) ≤
      (HScaleNorm bH mu tH v) ^ (1 / 2 : ℝ) + (HScaleNorm bH mu tH w) ^ (1 / 2 : ℝ) := by
    intro v w
    have ht : ∀ i : ιH, Real.rpow (mu i) (-tH) = Real.rpow (mu i) (-tH/2) * Real.rpow (mu i) (-tH/2) := by
      intro i
      have h := Real.rpow_add (hmu_pos i) (-tH/2) (-tH/2)
      rwa [show -tH/2 + -tH/2 = -tH by ring] at h
    have hmul : ∀ (i : ιH) (x : ℝ), (Real.rpow (mu i) (-tH/2) * x)^2 = Real.rpow (mu i) (-tH) * x^2 := by
      intro i x
      rw [ht i, mul_pow]
      ring
    have h1 : HScaleNorm bH mu tH (v + w) =
        ∑' i, ENNReal.ofReal ((Real.rpow (mu i) (-tH/2) * inner ℝ (bH i) v
          + Real.rpow (mu i) (-tH/2) * inner ℝ (bH i) w)^2) := by
      simp only [HScaleNorm]
      apply tsum_congr
      intro i
      rw [inner_add_right, ← hmul i (inner ℝ (bH i) v + inner ℝ (bH i) w), mul_add]
    have h2 : HScaleNorm bH mu tH v =
        ∑' i, ENNReal.ofReal ((Real.rpow (mu i) (-tH/2) * inner ℝ (bH i) v)^2) := by
      simp only [HScaleNorm]
      apply tsum_congr
      intro i
      rw [← hmul i (inner ℝ (bH i) v)]
    have h3 : HScaleNorm bH mu tH w =
        ∑' i, ENNReal.ofReal ((Real.rpow (mu i) (-tH/2) * inner ℝ (bH i) w)^2) := by
      simp only [HScaleNorm]
      apply tsum_congr
      intro i
      rw [← hmul i (inner ℝ (bH i) w)]
    rw [h1, h2, h3]
    exact keyH (fun i => Real.rpow (mu i) (-tH/2) * inner ℝ (bH i) v)
      (fun i => Real.rpow (mu i) (-tH/2) * inner ℝ (bH i) w)
  have subH : ∀ v w : H, (HScaleNorm bH mu tH (v - w)) ^ (1 / 2 : ℝ) ≤
      (HScaleNorm bH mu tH v) ^ (1 / 2 : ℝ) + (HScaleNorm bH mu tH w) ^ (1 / 2 : ℝ) := by
    intro v w
    have hneg : HScaleNorm bH mu tH (-w) = HScaleNorm bH mu tH w := by
      simp only [HScaleNorm]
      apply tsum_congr
      intro i
      rw [inner_neg_right]
      congr 1
      ring
    have h := addH v (-w)
    rw [hneg] at h
    simpa only [sub_eq_add_neg] using h
  have addU : ∀ u1 u2 : U, (UScaleNorm e lam tU (u1 + u2)) ^ (1 / 2 : ℝ) ≤
      (UScaleNorm e lam tU u1) ^ (1 / 2 : ℝ) + (UScaleNorm e lam tU u2) ^ (1 / 2 : ℝ) := by
    intro u1 u2
    have ht : ∀ k : ℕ, Real.rpow (lam k) (-tU) = Real.rpow (lam k) (-tU/2) * Real.rpow (lam k) (-tU/2) := by
      intro k
      have h := Real.rpow_add (hlam_pos k) (-tU/2) (-tU/2)
      rwa [show -tU/2 + -tU/2 = -tU by ring] at h
    have hmul : ∀ (k : ℕ) (x : ℝ), (Real.rpow (lam k) (-tU/2) * x)^2 = Real.rpow (lam k) (-tU) * x^2 := by
      intro k x
      rw [ht k, mul_pow]
      ring
    have h1 : UScaleNorm e lam tU (u1 + u2) =
        ∑' k, ENNReal.ofReal ((Real.rpow (lam k) (-tU/2) * inner ℝ (e k) u1
          + Real.rpow (lam k) (-tU/2) * inner ℝ (e k) u2)^2) := by
      simp only [UScaleNorm]
      apply tsum_congr
      intro k
      rw [inner_add_right, ← hmul k (inner ℝ (e k) u1 + inner ℝ (e k) u2), mul_add]
    have h2 : UScaleNorm e lam tU u1 =
        ∑' k, ENNReal.ofReal ((Real.rpow (lam k) (-tU/2) * inner ℝ (e k) u1)^2) := by
      simp only [UScaleNorm]
      apply tsum_congr
      intro k
      rw [← hmul k (inner ℝ (e k) u1)]
    have h3 : UScaleNorm e lam tU u2 =
        ∑' k, ENNReal.ofReal ((Real.rpow (lam k) (-tU/2) * inner ℝ (e k) u2)^2) := by
      simp only [UScaleNorm]
      apply tsum_congr
      intro k
      rw [← hmul k (inner ℝ (e k) u2)]
    rw [h1, h2, h3]
    exact keyU (fun k => Real.rpow (lam k) (-tU/2) * inner ℝ (e k) u1)
      (fun k => Real.rpow (lam k) (-tU/2) * inner ℝ (e k) u2)
  have subU : ∀ u1 u2 : U, (UScaleNorm e lam tU (u1 - u2)) ^ (1 / 2 : ℝ) ≤
      (UScaleNorm e lam tU u1) ^ (1 / 2 : ℝ) + (UScaleNorm e lam tU u2) ^ (1 / 2 : ℝ) := by
    intro u1 u2
    have hneg : UScaleNorm e lam tU (-u2) = UScaleNorm e lam tU u2 := by
      simp only [UScaleNorm]
      apply tsum_congr
      intro k
      rw [inner_neg_right]
      congr 1
      ring
    have h := addU u1 (-u2)
    rw [hneg] at h
    simpa only [sub_eq_add_neg] using h
  exact ⟨addH, subH, addU, subU⟩
  /- @proof-region region.target-node.session.283b4001a3b5300f end -/

end Statlib.Imported
end

