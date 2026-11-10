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
theorem statopia_math_node_54049410_53411e5b : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : Type*) (bH : HilbertBasis ι ℝ H) (mu : ι → ℝ)

    (hmu_pos : ∀ i : ι, 0 < mu i)
    (t : ℝ) (a b : H),
    ENNReal.ofReal (|inner ℝ a b|)
      ≤ (HScaleNorm bH mu (-t) a) ^ (1 / 2 : ℝ) * (HScaleNorm bH mu t b) ^ (1 / 2 : ℝ) := by
  /- @proof-region region.target-node.session.15c4a2018fef1091 begin -/
  intro H _ _ _ ι bH mu hmu_pos t a b
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  set x : ι → ℝ := fun i => Real.rpow (mu i) (t / 2) * inner ℝ (bH i) a with hxdef
  set y : ι → ℝ := fun i => Real.rpow (mu i) (-t / 2) * inner ℝ (bH i) b with hydef
  set A : ℝ≥0∞ := HScaleNorm bH mu (-t) a with hAdef
  set B : ℝ≥0∞ := HScaleNorm bH mu t b with hBdef
  have hx2 : ∀ i : ι, x i ^ 2 = Real.rpow (mu i) t * (inner ℝ (bH i) a) ^ 2 := by
    intro i
    have hpow : (Real.rpow (mu i) (t / 2)) ^ 2 = Real.rpow (mu i) t := by
      have h' : ((mu i) ^ (t / 2)) ^ 2 = (mu i) ^ t := by
        rw [pow_two, ← Real.rpow_add (hmu_pos i), show t / 2 + t / 2 = t by ring]
      exact h'
    simp only [hxdef]
    rw [mul_pow, hpow]
  have hy2 : ∀ i : ι, y i ^ 2 = Real.rpow (mu i) (-t) * (inner ℝ (bH i) b) ^ 2 := by
    intro i
    have hpow : (Real.rpow (mu i) (-t / 2)) ^ 2 = Real.rpow (mu i) (-t) := by
      have h' : ((mu i) ^ (-t / 2)) ^ 2 = (mu i) ^ (-t) := by
        rw [pow_two, ← Real.rpow_add (hmu_pos i), show -t / 2 + -t / 2 = -t by ring]
      exact h'
    simp only [hydef]
    rw [mul_pow, hpow]
  have hxy : ∀ i : ι, x i * y i = inner ℝ a (bH i) * inner ℝ (bH i) b := by
    intro i
    have h1 : Real.rpow (mu i) (t / 2) * Real.rpow (mu i) (-t / 2) = 1 := by
      have h' : (mu i) ^ (t / 2) * (mu i) ^ (-t / 2) = 1 := by
        rw [← Real.rpow_add (hmu_pos i), show t / 2 + -t / 2 = 0 by ring, Real.rpow_zero]
      exact h'
    simp only [hxdef, hydef]
    rw [real_inner_comm (bH i) a, mul_mul_mul_comm, h1, one_mul]
  have hAsum : A = ∑' i : ι, ENNReal.ofReal (x i ^ 2) := by
    rw [hAdef]
    simp only [HScaleNorm, hx2, neg_neg]
  have hBsum : B = ∑' i : ι, ENNReal.ofReal (y i ^ 2) := by
    rw [hBdef]
    simp only [HScaleNorm, hy2]
  have hzero : ∀ (w v : H) (s : ℝ), HScaleNorm bH mu s w = 0 → inner ℝ v w = 0 := by
    intro w v s h
    have hterm : ∀ i : ι,
        ENNReal.ofReal (Real.rpow (mu i) (-s) * (inner ℝ (bH i) w) ^ 2) = 0 := by
      intro i
      have h1 : ENNReal.ofReal (Real.rpow (mu i) (-s) * (inner ℝ (bH i) w) ^ 2)
          ≤ HScaleNorm bH mu s w := by
        have h2 := ENNReal.sum_le_tsum ({i} : Finset ι)
          (f := fun j => ENNReal.ofReal (Real.rpow (mu j) (-s) * (inner ℝ (bH j) w) ^ 2))
        simpa [HScaleNorm] using h2
      rw [h] at h1
      exact le_antisymm h1 (zero_le _)
    have hinner : ∀ i : ι, inner ℝ (bH i) w = 0 := by
      intro i
      have hle : Real.rpow (mu i) (-s) * (inner ℝ (bH i) w) ^ 2 ≤ 0 :=
        ENNReal.ofReal_eq_zero.1 (hterm i)
      have hpos : 0 < Real.rpow (mu i) (-s) := Real.rpow_pos_of_pos (hmu_pos i) (-s)
      have hnn : 0 ≤ Real.rpow (mu i) (-s) * (inner ℝ (bH i) w) ^ 2 :=
        mul_nonneg (le_of_lt hpos) (sq_nonneg _)
      have hsq : (inner ℝ (bH i) w) ^ 2 = 0 := by
        rcases mul_eq_zero.1 (le_antisymm hle hnn) with h' | h'
        · exact absurd h' (ne_of_gt hpos)
        · exact h'
      exact mul_self_eq_zero.1 (by rwa [pow_two] at hsq)
    have hfun : (fun i => inner ℝ v (bH i) * inner ℝ (bH i) w) = fun _ => 0 := by
      funext i
      rw [hinner i, mul_zero]
    have hbw : HasSum (fun i => inner ℝ v (bH i) * inner ℝ (bH i) w) (inner ℝ v w) :=
      bH.hasSum_inner_mul_inner v w
    rw [hfun] at hbw
    exact hbw.unique hasSum_zero
  by_cases hA0 : A = 0
  · have hc : inner ℝ a b = 0 := by
      have h1 : inner ℝ b a = 0 := hzero a b (-t) (by rw [← hAdef]; exact hA0)
      rwa [real_inner_comm a b] at h1
    rw [hc]
    simp
  by_cases hB0 : B = 0
  · have hc : inner ℝ a b = 0 := hzero b a t (by rw [← hBdef]; exact hB0)
    rw [hc]
    simp
  by_cases hAtop : A = ⊤
  · have hBpos : 0 < B := lt_of_le_of_ne (zero_le B) (Ne.symm hB0)
    have hBhalf : 0 < B ^ (1 / 2 : ℝ) := by
      have h := (ENNReal.rpow_lt_rpow_iff (x := 0) (y := B) (z := 1 / 2) hhalf).2 hBpos
      rwa [show (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 from ENNReal.zero_rpow_of_pos hhalf] at h
    rw [hAtop, ENNReal.top_rpow_of_pos hhalf, ENNReal.top_mul (ne_of_gt hBhalf)]
    exact le_top
  by_cases hBtop : B = ⊤
  · have hApos : 0 < A := lt_of_le_of_ne (zero_le A) (Ne.symm hA0)
    have hAhalf : 0 < A ^ (1 / 2 : ℝ) := by
      have h := (ENNReal.rpow_lt_rpow_iff (x := 0) (y := A) (z := 1 / 2) hhalf).2 hApos
      rwa [show (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 from ENNReal.zero_rpow_of_pos hhalf] at h
    rw [hBtop, ENNReal.top_rpow_of_pos hhalf, ENNReal.mul_top (ne_of_gt hAhalf)]
    exact le_top
  have hAid : ENNReal.ofReal (Real.sqrt A.toReal) = A ^ (1 / 2 : ℝ) := by
    have hpos : 0 < A.toReal := ENNReal.toReal_pos hA0 hAtop
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_toReal hAtop]
  have hBid : ENNReal.ofReal (Real.sqrt B.toReal) = B ^ (1 / 2 : ℝ) := by
    have hpos : 0 < B.toReal := ENNReal.toReal_pos hB0 hBtop
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_toReal hBtop]
  have hfin : ∀ s : Finset ι, ENNReal.ofReal (|∑ i ∈ s, x i * y i|)
      ≤ A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by
    intro s
    have hcs : (∑ i ∈ s, x i * y i) ^ 2 ≤ (∑ i ∈ s, x i ^ 2) * ∑ i ∈ s, y i ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s x y
    have hxn : 0 ≤ ∑ i ∈ s, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
    have habs : |∑ i ∈ s, x i * y i|
        ≤ Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ i ∈ s, y i ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hxn]
      exact Real.sqrt_le_sqrt hcs
    have hxs : ENNReal.ofReal (∑ i ∈ s, x i ^ 2) ≤ A := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (x i))]
      rw [hAsum]
      exact ENNReal.sum_le_tsum s
    have hys : ENNReal.ofReal (∑ i ∈ s, y i ^ 2) ≤ B := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (y i))]
      rw [hBsum]
      exact ENNReal.sum_le_tsum s
    have hxK : Real.sqrt (∑ i ∈ s, x i ^ 2) ≤ Real.sqrt A.toReal :=
      Real.sqrt_le_sqrt ((ENNReal.ofReal_le_iff_le_toReal hAtop).1 hxs)
    have hyK : Real.sqrt (∑ i ∈ s, y i ^ 2) ≤ Real.sqrt B.toReal :=
      Real.sqrt_le_sqrt ((ENNReal.ofReal_le_iff_le_toReal hBtop).1 hys)
    calc ENNReal.ofReal (|∑ i ∈ s, x i * y i|)
        ≤ ENNReal.ofReal (Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ i ∈ s, y i ^ 2)) :=
          ENNReal.ofReal_le_ofReal habs
      _ = ENNReal.ofReal (Real.sqrt (∑ i ∈ s, x i ^ 2))
            * ENNReal.ofReal (Real.sqrt (∑ i ∈ s, y i ^ 2)) :=
          ENNReal.ofReal_mul (Real.sqrt_nonneg _)
      _ ≤ ENNReal.ofReal (Real.sqrt A.toReal) * ENNReal.ofReal (Real.sqrt B.toReal) := by
          gcongr
      _ = A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by rw [hAid, hBid]
  have hMeq : A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt A.toReal * Real.sqrt B.toReal) := by
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), hAid, hBid]
  have hb : HasSum (fun i => x i * y i) (inner ℝ a b) := by
    have h0 := bH.hasSum_inner_mul_inner a b
    simpa only [← hxy] using h0
  have hK : |inner ℝ a b| ≤ Real.sqrt A.toReal * Real.sqrt B.toReal := by
    have hbabs : ∀ s : Finset ι,
        |∑ i ∈ s, x i * y i| ≤ Real.sqrt A.toReal * Real.sqrt B.toReal := by
      intro s
      have h1 : ENNReal.ofReal (|∑ i ∈ s, x i * y i|)
          ≤ ENNReal.ofReal (Real.sqrt A.toReal * Real.sqrt B.toReal) := by
        rw [← hMeq]
        exact hfin s
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1 h1
    have hbnd : ∀ s : Finset ι,
        ∑ i ∈ s, x i * y i ≤ Real.sqrt A.toReal * Real.sqrt B.toReal :=
      fun s => le_trans (le_abs_self _) (hbabs s)
    have hbnd2 : ∀ s : Finset ι,
        ∑ i ∈ s, -(x i * y i) ≤ Real.sqrt A.toReal * Real.sqrt B.toReal := by
      intro s
      rw [Finset.sum_neg_distrib]
      exact le_trans (neg_le_abs _) (hbabs s)
    have htend : Tendsto (fun s : Finset ι => ∑ i ∈ s, x i * y i) atTop (𝓝 (inner ℝ a b)) := hb
    have hle1 : inner ℝ a b ≤ Real.sqrt A.toReal * Real.sqrt B.toReal :=
      le_of_tendsto htend (Filter.Eventually.of_forall hbnd)
    have hle2 : -(inner ℝ a b) ≤ Real.sqrt A.toReal * Real.sqrt B.toReal := by
      have htend2 : Tendsto (fun s : Finset ι => ∑ i ∈ s, -(x i * y i)) atTop
          (𝓝 (-(inner ℝ a b))) := hb.neg
      exact le_of_tendsto htend2 (Filter.Eventually.of_forall hbnd2)
    rw [abs_le]
    constructor <;> linarith
  calc ENNReal.ofReal |inner ℝ a b|
      ≤ ENNReal.ofReal (Real.sqrt A.toReal * Real.sqrt B.toReal) := ENNReal.ofReal_le_ofReal hK
    _ = ENNReal.ofReal (Real.sqrt A.toReal) * ENNReal.ofReal (Real.sqrt B.toReal) :=
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)
    _ = A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by rw [hAid, hBid]
  /- @proof-region region.target-node.session.15c4a2018fef1091 end -/

end Statlib.Imported
end

