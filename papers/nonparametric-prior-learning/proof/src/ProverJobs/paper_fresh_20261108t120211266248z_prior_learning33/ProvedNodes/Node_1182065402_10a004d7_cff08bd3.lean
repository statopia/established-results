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
theorem statopia_math_node_1182065402_10a004d7 : ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {ιH : Type*} (bH : HilbertBasis ιH ℝ H) (mu : ιH → ℝ)
    (hmu_pos : ∀ i : ιH, 0 < mu i) (t : ℝ) (a b : H)
    (ha : HScaleNorm bH mu t a ≠ ⊤) (hb : HScaleNorm bH mu t b ≠ ⊤),
    (HScaleDist bH mu t b a).toReal ≤
      (HScaleDist bH mu t b 0).toReal + (HScaleDist bH mu t a 0).toReal := by
  /- @proof-region region.target-node.session.01dc3da7c93b14f8 begin -/
  intro H hN hI ιH bH mu hmu_pos t a b ha hb
  let w : ιH → ℝ := fun i => Real.rpow (mu i) (-t)
  have hw0 : ∀ i, 0 ≤ w i := fun i => le_of_lt (Real.rpow_pos_of_pos (hmu_pos i) _)
  have hsqw : ∀ i, Real.sqrt (w i) ^ 2 = w i := fun i => Real.sq_sqrt (hw0 i)
  let F : ιH → ℝ := fun i => w i * (inner ℝ (bH i) b - inner ℝ (bH i) a) ^ 2
  let G : ιH → ℝ := fun i => w i * (inner ℝ (bH i) b) ^ 2
  let K : ιH → ℝ := fun i => w i * (inner ℝ (bH i) a) ^ 2
  let p : ιH → ℝ := fun i => Real.sqrt (w i) * inner ℝ (bH i) b
  let q : ιH → ℝ := fun i => Real.sqrt (w i) * inner ℝ (bH i) a
  have hFnn : ∀ i, 0 ≤ F i := fun i => mul_nonneg (hw0 i) (sq_nonneg _)
  have hGnn : ∀ i, 0 ≤ G i := fun i => mul_nonneg (hw0 i) (sq_nonneg _)
  have hKnn : ∀ i, 0 ≤ K i := fun i => mul_nonneg (hw0 i) (sq_nonneg _)
  have hp2 : ∀ i, p i ^ 2 = G i := by
    intro i
    show (Real.sqrt (w i) * inner ℝ (bH i) b) ^ 2 = w i * (inner ℝ (bH i) b) ^ 2
    rw [mul_pow, hsqw i]
  have hq2 : ∀ i, q i ^ 2 = K i := by
    intro i
    show (Real.sqrt (w i) * inner ℝ (bH i) a) ^ 2 = w i * (inner ℝ (bH i) a) ^ 2
    rw [mul_pow, hsqw i]
  have hpqF : ∀ i, (p i - q i) ^ 2 = F i := by
    intro i
    show (Real.sqrt (w i) * inner ℝ (bH i) b - Real.sqrt (w i) * inner ℝ (bH i) a) ^ 2
      = w i * (inner ℝ (bH i) b - inner ℝ (bH i) a) ^ 2
    rw [← mul_sub, mul_pow, hsqw i]
  have hXeq : HScaleNorm bH mu t (b - a) = ∑' i, ENNReal.ofReal (F i) := by
    show (∑' i, ENNReal.ofReal (w i * (inner ℝ (bH i) (b - a)) ^ 2))
      = ∑' i, ENNReal.ofReal (F i)
    refine tsum_congr (fun i => ?_)
    show ENNReal.ofReal (w i * (inner ℝ (bH i) (b - a)) ^ 2)
      = ENNReal.ofReal (w i * (inner ℝ (bH i) b - inner ℝ (bH i) a) ^ 2)
    rw [inner_sub_right]
  have hYeq : HScaleNorm bH mu t b = ∑' i, ENNReal.ofReal (G i) := rfl
  have hZeq : HScaleNorm bH mu t a = ∑' i, ENNReal.ofReal (K i) := rfl
  have hGs : ∀ s : Finset ιH, ∑ i ∈ s, G i ≤ (HScaleNorm bH mu t b).toReal := by
    intro s
    have h1 : ENNReal.ofReal (∑ i ∈ s, G i) = ∑ i ∈ s, ENNReal.ofReal (G i) :=
      ENNReal.ofReal_sum_of_nonneg (fun i _ => hGnn i)
    have h2 : ∑ i ∈ s, ENNReal.ofReal (G i) ≤ HScaleNorm bH mu t b := by
      rw [hYeq, ENNReal.tsum_eq_iSup_sum]
      exact le_iSup (fun u : Finset ιH => ∑ a' ∈ u, ENNReal.ofReal (G a')) s
    calc ∑ i ∈ s, G i
        = (ENNReal.ofReal (∑ i ∈ s, G i)).toReal := by
          rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hGnn i))]
      _ = (∑ i ∈ s, ENNReal.ofReal (G i)).toReal := by rw [h1]
      _ ≤ (HScaleNorm bH mu t b).toReal := ENNReal.toReal_mono hb h2
  have hKs : ∀ s : Finset ιH, ∑ i ∈ s, K i ≤ (HScaleNorm bH mu t a).toReal := by
    intro s
    have h1 : ENNReal.ofReal (∑ i ∈ s, K i) = ∑ i ∈ s, ENNReal.ofReal (K i) :=
      ENNReal.ofReal_sum_of_nonneg (fun i _ => hKnn i)
    have h2 : ∑ i ∈ s, ENNReal.ofReal (K i) ≤ HScaleNorm bH mu t a := by
      rw [hZeq, ENNReal.tsum_eq_iSup_sum]
      exact le_iSup (fun u : Finset ιH => ∑ a' ∈ u, ENNReal.ofReal (K a')) s
    calc ∑ i ∈ s, K i
        = (ENNReal.ofReal (∑ i ∈ s, K i)).toReal := by
          rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hKnn i))]
      _ = (∑ i ∈ s, ENNReal.ofReal (K i)).toReal := by rw [h1]
      _ ≤ (HScaleNorm bH mu t a).toReal := ENNReal.toReal_mono ha h2
  have hfin : ∀ s : Finset ιH, ∑ i ∈ s, F i ≤
      (Real.sqrt (HScaleNorm bH mu t b).toReal + Real.sqrt (HScaleNorm bH mu t a).toReal) ^ 2 := by
    intro s
    have hSex : ∑ i ∈ s, F i = ∑ i ∈ s, (p i - q i) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => (hpqF i).symm)
    rw [hSex]
    have hSexp : ∑ i ∈ s, (p i - q i) ^ 2 =
        (∑ i ∈ s, p i ^ 2) + (∑ i ∈ s, q i ^ 2) - 2 * (∑ i ∈ s, p i * q i) := by
      have hstep1 : ∑ i ∈ s, (p i - q i) ^ 2 =
          ∑ i ∈ s, (p i ^ 2 - 2 * (p i * q i) + q i ^ 2) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [hstep1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    have hcs : (∑ i ∈ s, p i * q i) ^ 2 ≤ (∑ i ∈ s, p i ^ 2) * (∑ i ∈ s, q i ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq s p q
    have hA0 : 0 ≤ ∑ i ∈ s, p i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hB0 : 0 ≤ ∑ i ∈ s, q i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hleA : ∑ i ∈ s, p i ^ 2 ≤ (HScaleNorm bH mu t b).toReal := by
      rw [Finset.sum_congr rfl (fun i _ => hp2 i)]
      exact hGs s
    have hleB : ∑ i ∈ s, q i ^ 2 ≤ (HScaleNorm bH mu t a).toReal := by
      rw [Finset.sum_congr rfl (fun i _ => hq2 i)]
      exact hKs s
    have hsqa : Real.sqrt (∑ i ∈ s, p i ^ 2) ^ 2 = ∑ i ∈ s, p i ^ 2 := Real.sq_sqrt hA0
    have hsqb : Real.sqrt (∑ i ∈ s, q i ^ 2) ^ 2 = ∑ i ∈ s, q i ^ 2 := Real.sq_sqrt hB0
    have hra0 : 0 ≤ Real.sqrt (∑ i ∈ s, p i ^ 2) := Real.sqrt_nonneg _
    have hrb0 : 0 ≤ Real.sqrt (∑ i ∈ s, q i ^ 2) := Real.sqrt_nonneg _
    have hkey : ∀ x : ℝ, 0 ≤ x →
        x ^ 2 ≤ (Real.sqrt (∑ i ∈ s, p i ^ 2) * Real.sqrt (∑ i ∈ s, q i ^ 2)) ^ 2 →
        x ≤ Real.sqrt (∑ i ∈ s, p i ^ 2) * Real.sqrt (∑ i ∈ s, q i ^ 2) := by
      intro x hx hsq
      have h1 := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hx, Real.sqrt_sq (mul_nonneg hra0 hrb0)] at h1
    have hCS2 : -(∑ i ∈ s, p i * q i) ≤
        Real.sqrt (∑ i ∈ s, p i ^ 2) * Real.sqrt (∑ i ∈ s, q i ^ 2) := by
      by_cases h : 0 ≤ -(∑ i ∈ s, p i * q i)
      · refine hkey _ h ?_
        nlinarith [hcs, hsqa, hsqb]
      · have h0 : 0 ≤ Real.sqrt (∑ i ∈ s, p i ^ 2) * Real.sqrt (∑ i ∈ s, q i ^ 2) :=
          mul_nonneg hra0 hrb0
        linarith
    have hstep : ∑ i ∈ s, (p i - q i) ^ 2 ≤
        (Real.sqrt (∑ i ∈ s, p i ^ 2) + Real.sqrt (∑ i ∈ s, q i ^ 2)) ^ 2 := by
      nlinarith [hSexp, hCS2, hsqa, hsqb]
    have hmono : Real.sqrt (∑ i ∈ s, p i ^ 2) + Real.sqrt (∑ i ∈ s, q i ^ 2) ≤
        Real.sqrt (HScaleNorm bH mu t b).toReal + Real.sqrt (HScaleNorm bH mu t a).toReal :=
      add_le_add (Real.sqrt_le_sqrt hleA) (Real.sqrt_le_sqrt hleB)
    have hsqle : (Real.sqrt (∑ i ∈ s, p i ^ 2) + Real.sqrt (∑ i ∈ s, q i ^ 2)) ^ 2 ≤
        (Real.sqrt (HScaleNorm bH mu t b).toReal + Real.sqrt (HScaleNorm bH mu t a).toReal) ^ 2 := by
      have h3 : 0 ≤ (Real.sqrt (HScaleNorm bH mu t b).toReal +
          Real.sqrt (HScaleNorm bH mu t a).toReal) -
          (Real.sqrt (∑ i ∈ s, p i ^ 2) + Real.sqrt (∑ i ∈ s, q i ^ 2)) := by linarith
      have h4 : 0 ≤ (Real.sqrt (HScaleNorm bH mu t b).toReal +
          Real.sqrt (HScaleNorm bH mu t a).toReal) +
          (Real.sqrt (∑ i ∈ s, p i ^ 2) + Real.sqrt (∑ i ∈ s, q i ^ 2)) := by linarith
      nlinarith [mul_nonneg h3 h4]
    linarith [hstep, hsqle]
  have hC0fin : 0 ≤ (Real.sqrt (HScaleNorm bH mu t b).toReal +
      Real.sqrt (HScaleNorm bH mu t a).toReal) ^ 2 := sq_nonneg _
  have hAle : HScaleNorm bH mu t (b - a) ≤ ENNReal.ofReal ((Real.sqrt (HScaleNorm bH mu t b).toReal +
      Real.sqrt (HScaleNorm bH mu t a).toReal) ^ 2) := by
    rw [hXeq, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun s => ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hFnn i)]
    exact ENNReal.ofReal_le_ofReal (hfin s)
  have hXle : (HScaleNorm bH mu t (b - a)).toReal ≤
      (Real.sqrt (HScaleNorm bH mu t b).toReal + Real.sqrt (HScaleNorm bH mu t a).toReal) ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal hC0fin hAle
  have hCY0 : 0 ≤ Real.sqrt (HScaleNorm bH mu t b).toReal +
      Real.sqrt (HScaleNorm bH mu t a).toReal :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfin2 : Real.sqrt (HScaleNorm bH mu t (b - a)).toReal ≤
      Real.sqrt (HScaleNorm bH mu t b).toReal + Real.sqrt (HScaleNorm bH mu t a).toReal := by
    have h1 := Real.sqrt_le_sqrt hXle
    rwa [Real.sqrt_sq hCY0] at h1
  have hXr : (HScaleDist bH mu t b a).toReal = Real.sqrt (HScaleNorm bH mu t (b - a)).toReal := by
    rw [HScaleDist, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  have hYr : (HScaleDist bH mu t b 0).toReal = Real.sqrt (HScaleNorm bH mu t b).toReal := by
    rw [HScaleDist, sub_zero, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  have hZr : (HScaleDist bH mu t a 0).toReal = Real.sqrt (HScaleNorm bH mu t a).toReal := by
    rw [HScaleDist, sub_zero, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  rw [hXr, hYr, hZr]
  exact hfin2
  /- @proof-region region.target-node.session.01dc3da7c93b14f8 end -/

end Statlib.Imported
end

