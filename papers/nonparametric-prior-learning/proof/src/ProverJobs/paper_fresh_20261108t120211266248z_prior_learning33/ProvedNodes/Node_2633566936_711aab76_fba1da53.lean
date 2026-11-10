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
theorem statopia_math_node_2633566936_711aab76 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (hlam_anti : Antitone lam) (Nc : ℕ) (hNc : 0 < Nc) (θ2 : Fin Nc → ℝ)
    (R_u : ℝ) (hR_u : 0 < R_u) (a b : U)
    (ha : UScaleNorm e lam 2 a < ⊤) (hb : UScaleNorm e lam 2 b < ⊤)
    (haR : UScaleNorm e lam 2 a ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal R_u)
    (hbR : UScaleNorm e lam 2 b ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal R_u),
    let c : ℕ → ℝ := fun k => priorEigen lam Nc θ2 k
    let Lambda : ℝ := max 1 (sSup {r : ℝ | ∃ k : Fin Nc, r = lam (k : ℕ) / c (k : ℕ)})
    Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) ∧
      (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ Lambda * (∑' k : ℕ, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) ∧
      Lambda * (∑' k : ℕ, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ Lambda * lam 0 * (∑' k : ℕ, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) ∧
      Lambda * lam 0 * (∑' k : ℕ, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ Lambda * lam 0 * (2 * R_u) ^ 2 := by
  /- @proof-region region.target-node.session.f14dc6733d9abf7d begin -/
  intro U _ _ e lam hlam_pos hlam_anti Nc hNc θ2 R_u hR_u a b ha hb haR hbR
  let c : ℕ → ℝ := fun k => priorEigen lam Nc θ2 k
  let Lambda : ℝ := max 1 (sSup {r : ℝ | ∃ k : Fin Nc, r = lam (k : ℕ) / c (k : ℕ)})
  show Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) ∧
      (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ Lambda * (∑' k : ℕ, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) ∧
      Lambda * (∑' k : ℕ, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ Lambda * lam 0 * (∑' k : ℕ, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) ∧
      Lambda * lam 0 * (∑' k : ℕ, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ Lambda * lam 0 * (2 * R_u) ^ 2
  have hLam : Lambda = max 1 (sSup {r : ℝ | ∃ k : Fin Nc, r = lam (k : ℕ) / c (k : ℕ)}) := rfl
  have hc_eq : ∀ k : ℕ, c k = priorEigen lam Nc θ2 k := fun k => rfl
  have hcpos : ∀ k : ℕ, 0 < c k := by
    intro k
    rw [hc_eq k]
    unfold priorEigen
    split_ifs with h
    · exact Real.exp_pos _
    · exact hlam_pos k
  have hrpow : ∀ k : ℕ, Real.rpow (lam k) (-2) = ((lam k)⁻¹) ^ 2 := by
    intro k
    change (lam k) ^ (-2 : ℝ) = ((lam k)⁻¹) ^ 2
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
  let Fz : U → ℕ → ℝ := fun z k => Real.rpow (lam k) (-2) * (inner ℝ (e k) z) ^ 2
  have hUS : ∀ z : U, UScaleNorm e lam 2 z = ∑' k, ENNReal.ofReal (Fz z k) := fun z => rfl
  have key_summable : ∀ z : U, (∑' k, ENNReal.ofReal (Fz z k)) < ⊤ → Summable (Fz z) := by
    intro z hz
    have hnonneg : ∀ k, 0 ≤ Fz z k := fun k =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt (hlam_pos k)) (-2)) (sq_nonneg _)
    refine summable_of_sum_range_le (f := Fz z)
      (c := (∑' k, ENNReal.ofReal (Fz z k)).toReal) hnonneg ?_
    intro n
    have h1 : ENNReal.ofReal (∑ i ∈ Finset.range n, Fz z i)
        = ∑ i ∈ Finset.range n, ENNReal.ofReal (Fz z i) :=
      ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)
    have h2 : (∑ i ∈ Finset.range n, ENNReal.ofReal (Fz z i))
        ≤ ∑' k, ENNReal.ofReal (Fz z k) := ENNReal.sum_le_tsum _
    calc ∑ i ∈ Finset.range n, Fz z i
        = (ENNReal.ofReal (∑ i ∈ Finset.range n, Fz z i)).toReal := by
          rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hnonneg i))]
      _ = (∑ i ∈ Finset.range n, ENNReal.ofReal (Fz z i)).toReal := by rw [h1]
      _ ≤ (∑' k, ENNReal.ofReal (Fz z k)).toReal := ENNReal.toReal_mono (ne_of_lt hz) h2
  have key_bound : ∀ z : U, (hz : (∑' k, ENNReal.ofReal (Fz z k)) < ⊤) →
      (hzR : (∑' k, ENNReal.ofReal (Fz z k)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal R_u) →
      (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) z) ^ 2) ≤ R_u ^ 2 := by
    intro z hz hzR
    have hnonneg : ∀ k, 0 ≤ Fz z k := fun k =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt (hlam_pos k)) (-2)) (sq_nonneg _)
    have hsum := key_summable z hz
    have hS : 0 ≤ ∑' k, Fz z k := tsum_nonneg hnonneg
    have hofl : ENNReal.ofReal (∑' k, Fz z k) = ∑' k, ENNReal.ofReal (Fz z k) :=
      ENNReal.ofReal_tsum_of_nonneg hnonneg hsum
    have he : (∑' k, ENNReal.ofReal (Fz z k)) ^ (1 / 2 : ℝ)
        = ENNReal.ofReal ((∑' k, Fz z k) ^ (1 / 2 : ℝ)) := by
      rw [← hofl, ENNReal.ofReal_rpow_of_nonneg hS (by norm_num)]
    have hhalf : ENNReal.ofReal ((∑' k, Fz z k) ^ (1 / 2 : ℝ)) ≤ ENNReal.ofReal R_u := by
      rw [← he]; exact hzR
    have hle : (∑' k, Fz z k) ^ (1 / 2 : ℝ) ≤ R_u :=
      (ENNReal.ofReal_le_ofReal_iff (le_of_lt hR_u)).mp hhalf
    have hsq : ((∑' k, Fz z k) ^ (1 / 2 : ℝ)) ^ 2 = ∑' k, Fz z k := by
      have h2 : ((∑' k, Fz z k) ^ (1 / 2 : ℝ)) ^ 2
          = ((∑' k, Fz z k) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by rw [Real.rpow_two]
      rw [h2, ← Real.rpow_mul hS (1 / 2) 2,
        show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
    have hgoal : (∑' k, Fz z k) ≤ R_u ^ 2 := by
      have ht := Real.rpow_nonneg hS (1 / 2 : ℝ)
      have hR0 : (0 : ℝ) ≤ R_u := le_of_lt hR_u
      nlinarith [hsq, hle, ht, hR0]
    calc (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) z) ^ 2)
        = ∑' k, Real.rpow (lam k) (-2) * (inner ℝ (e k) z) ^ 2 := by
          apply tsum_congr
          intro k
          rw [hrpow]
      _ ≤ R_u ^ 2 := hgoal
  have hzA : (∑' k, ENNReal.ofReal (Fz a k)) < ⊤ := by rw [← hUS a]; exact ha
  have hzB : (∑' k, ENNReal.ofReal (Fz b k)) < ⊤ := by rw [← hUS b]; exact hb
  have hzAR : (∑' k, ENNReal.ofReal (Fz a k)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal R_u := by
    rw [← hUS a]; exact haR
  have hzBR : (∑' k, ENNReal.ofReal (Fz b k)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal R_u := by
    rw [← hUS b]; exact hbR
  have hSumA : Summable (fun k => ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2) := by
    have h := key_summable a hzA
    simpa only [Fz, hrpow] using h
  have hSumB : Summable (fun k => ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2) := by
    have h := key_summable b hzB
    simpa only [Fz, hrpow] using h
  have hterm : ∀ k : ℕ, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2
      ≤ 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2)
        + 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2) := by
    intro k
    have hin : inner ℝ (e k) (a - b) = inner ℝ (e k) a - inner ℝ (e k) b := inner_sub_right _ _ _
    have hsq0 : (inner ℝ (e k) (a - b)) ^ 2
        ≤ 2 * (inner ℝ (e k) a) ^ 2 + 2 * (inner ℝ (e k) b) ^ 2 := by
      rw [hin]
      nlinarith [sq_nonneg (inner ℝ (e k) a + inner ℝ (e k) b)]
    calc ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2
        ≤ ((lam k)⁻¹) ^ 2 * (2 * (inner ℝ (e k) a) ^ 2 + 2 * (inner ℝ (e k) b) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq0 (sq_nonneg _)
      _ = 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2)
            + 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2) := by ring
  have h2A : Summable (fun k => 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2)) := by
    have h := hSumA.add hSumA
    simpa [two_mul] using h
  have h2B : Summable (fun k => 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2)) := by
    have h := hSumB.add hSumB
    simpa [two_mul] using h
  have hmaj : Summable (fun k => 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2)
      + 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2)) := h2A.add h2B
  have hSumW : Summable (fun k => ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hterm hmaj
  have tsum_le_of_le : ∀ (f g : ℕ → ℝ), (∀ k, 0 ≤ f k) → (∀ k, f k ≤ g k) →
      Summable f → Summable g → (∑' k, f k) ≤ ∑' k, g k := by
    intro f g hf0 hfg hf hg
    have hg0 : ∀ k, 0 ≤ g k := fun k => le_trans (hf0 k) (hfg k)
    have e1 : ENNReal.ofReal (∑' k, f k) = ∑' k, ENNReal.ofReal (f k) :=
      ENNReal.ofReal_tsum_of_nonneg hf0 hf
    have e2 : ENNReal.ofReal (∑' k, g k) = ∑' k, ENNReal.ofReal (g k) :=
      ENNReal.ofReal_tsum_of_nonneg hg0 hg
    have hm : (∑' k, ENNReal.ofReal (f k)) ≤ ∑' k, ENNReal.ofReal (g k) :=
      ENNReal.tsum_le_tsum (fun k => ENNReal.ofReal_le_ofReal (hfg k))
    rw [← e1, ← e2] at hm
    exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hg0)).mp hm
  have tsum_add_of_nonneg : ∀ (f g : ℕ → ℝ), (∀ k, 0 ≤ f k) → (∀ k, 0 ≤ g k) →
      Summable f → Summable g → (∑' k, (f k + g k)) = (∑' k, f k) + ∑' k, g k := by
    intro f g hf0 hg0 hf hg
    have hfg0 : ∀ k, 0 ≤ f k + g k := fun k => add_nonneg (hf0 k) (hg0 k)
    have e1 : ENNReal.ofReal (∑' k, (f k + g k)) = ∑' k, ENNReal.ofReal (f k + g k) :=
      ENNReal.ofReal_tsum_of_nonneg hfg0 (hf.add hg)
    have e2 : (∑' k, ENNReal.ofReal (f k + g k))
        = ∑' k, (ENNReal.ofReal (f k) + ENNReal.ofReal (g k)) := by
      apply tsum_congr
      intro k
      exact ENNReal.ofReal_add (hf0 k) (hg0 k)
    have e3 : (∑' k, (ENNReal.ofReal (f k) + ENNReal.ofReal (g k)))
        = (∑' k, ENNReal.ofReal (f k)) + ∑' k, ENNReal.ofReal (g k) := ENNReal.tsum_add
    have e4 : (∑' k, ENNReal.ofReal (f k)) = ENNReal.ofReal (∑' k, f k) :=
      (ENNReal.ofReal_tsum_of_nonneg hf0 hf).symm
    have e5 : (∑' k, ENNReal.ofReal (g k)) = ENNReal.ofReal (∑' k, g k) :=
      (ENNReal.ofReal_tsum_of_nonneg hg0 hg).symm
    have key : ENNReal.ofReal (∑' k, (f k + g k))
        = ENNReal.ofReal ((∑' k, f k) + ∑' k, g k) := by
      rw [e1, e2, e3, e4, e5, ENNReal.ofReal_add (tsum_nonneg hf0) (tsum_nonneg hg0)]
    exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hfg0)
      (add_nonneg (tsum_nonneg hf0) (tsum_nonneg hg0))).mp key
  have hboundW : (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) ≤ (2 * R_u) ^ 2 := by
    have hA := key_bound a hzA hzAR
    have hB := key_bound b hzB hzBR
    have hnnA : ∀ k : ℕ, 0 ≤ 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2) :=
      fun k => mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hnnB : ∀ k : ℕ, 0 ≤ 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2) :=
      fun k => mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    calc (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ ∑' k, (2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2)
            + 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2)) :=
          tsum_le_of_le (fun k => ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2)
            (fun k => 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2)
              + 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2))
            (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hterm hSumW hmaj
      _ = (∑' k, 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2))
            + (∑' k, 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2)) :=
          tsum_add_of_nonneg (fun k => 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2))
            (fun k => 2 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2)) hnnA hnnB h2A h2B
      _ = 2 * (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) a) ^ 2)
            + 2 * (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) b) ^ 2) := by
          rw [tsum_mul_left, tsum_mul_left]
      _ ≤ 2 * R_u ^ 2 + 2 * R_u ^ 2 := by linarith [hA, hB]
      _ = (2 * R_u) ^ 2 := by ring
  have hstep : ∀ k : ℕ, (lam k)⁻¹ ≤ lam 0 * ((lam k)⁻¹) ^ 2 := by
    intro k
    have heq : lam k * ((lam k)⁻¹) ^ 2 = (lam k)⁻¹ := by
      rw [sq, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hlam_pos k)), one_mul]
    calc (lam k)⁻¹ = lam k * ((lam k)⁻¹) ^ 2 := heq.symm
      _ ≤ lam 0 * ((lam k)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right (hlam_anti (Nat.zero_le k)) (sq_nonneg _)
  have hterm1 : ∀ k : ℕ, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2
      ≤ lam 0 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) := by
    intro k
    calc (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2
        ≤ (lam 0 * ((lam k)⁻¹) ^ 2) * (inner ℝ (e k) (a - b)) ^ 2 :=
          mul_le_mul_of_nonneg_right (hstep k) (sq_nonneg _)
      _ = lam 0 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) := by ring
  have hmaj1 : Summable (fun k => lam 0 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2)) :=
    Summable.mul_left (lam 0) hSumW
  have hSum1 : Summable (fun k => (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (inv_nonneg.mpr (le_of_lt (hlam_pos k))) (sq_nonneg _))
      hterm1 hmaj1
  have h23 : (∑' k, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
      ≤ lam 0 * (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) := by
    calc (∑' k, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ ∑' k, lam 0 * (((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) :=
          tsum_le_of_le _ _ (fun k => mul_nonneg (inv_nonneg.mpr (le_of_lt (hlam_pos k))) (sq_nonneg _)) hterm1 hSum1 hmaj1
      _ = lam 0 * (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) := tsum_mul_left
  have hbdd : BddAbove {r : ℝ | ∃ k : Fin Nc, r = lam (k : ℕ) / c (k : ℕ)} := by
    have hfin : {r : ℝ | ∃ k : Fin Nc, r = lam (k : ℕ) / c (k : ℕ)}.Finite := by
      refine ((Set.finite_univ (α := Fin Nc)).image
        (fun k : Fin Nc => lam (k : ℕ) / c (k : ℕ))).subset ?_
      rintro r ⟨k, hk⟩
      exact ⟨k, Set.mem_univ k, hk.symm⟩
    exact hfin.bddAbove
  have hsup : ∀ k : Fin Nc, lam (k : ℕ) / c (k : ℕ)
      ≤ sSup {r : ℝ | ∃ j : Fin Nc, r = lam (j : ℕ) / c (j : ℕ)} :=
    fun k => le_csSup hbdd ⟨k, rfl⟩
  have hLpos : 0 ≤ Lambda := by
    rw [hLam]
    exact le_trans zero_le_one (le_max_left 1 _)
  have hbound : ∀ k : ℕ, (c k)⁻¹ ≤ Lambda * (lam k)⁻¹ := by
    intro k
    have hMpos : 0 < max 1 (sSup {r : ℝ | ∃ j : Fin Nc, r = lam (j : ℕ) / c (j : ℕ)}) :=
      lt_of_lt_of_le one_pos (le_max_left 1 _)
    have hkey : lam k / c k
        ≤ max 1 (sSup {r : ℝ | ∃ j : Fin Nc, r = lam (j : ℕ) / c (j : ℕ)}) := by
      by_cases hk : k < Nc
      · exact le_trans (hsup ⟨k, hk⟩) (le_max_right 1 _)
      · have hck : c k = lam k := by
          rw [hc_eq k]; unfold priorEigen; rw [dif_neg hk]
        have h1 : lam k / c k = 1 := by rw [hck, div_self (ne_of_gt (hlam_pos k))]
        rw [h1]
        exact le_max_left 1 _
    have hstep2 : (c k)⁻¹ = (lam k / c k) * (lam k)⁻¹ := by
      have heq : (c k)⁻¹ * lam k = lam k / c k := by rw [div_eq_mul_inv, mul_comm]
      calc (c k)⁻¹ = ((c k)⁻¹ * lam k) * (lam k)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (hlam_pos k)), mul_one]
        _ = (lam k / c k) * (lam k)⁻¹ := by rw [heq]
    rw [hLam, hstep2]
    exact mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr (le_of_lt (hlam_pos k)))
  have hptL : ∀ k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2
      ≤ Lambda * ((lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) := by
    intro k
    calc (c k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2
        ≤ (Lambda * (lam k)⁻¹) * (inner ℝ (e k) (a - b)) ^ 2 :=
          mul_le_mul_of_nonneg_right (hbound k) (sq_nonneg _)
      _ = Lambda * ((lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) := by ring
  have hFirstSum : Summable (fun k => (c k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (le_of_lt (inv_pos.mpr (hcpos k))) (sq_nonneg _))
      hptL (Summable.mul_left Lambda hSum1)
  have hFirstBound : (∑' k, (c k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
      ≤ Lambda * (∑' k, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) :=
    calc (∑' k, (c k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ ∑' k, Lambda * ((lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) :=
          tsum_le_of_le
            (fun k => (c k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
            (fun k => Lambda * ((lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2))
            (fun k => mul_nonneg (le_of_lt (inv_pos.mpr (hcpos k))) (sq_nonneg _))
            hptL hFirstSum (Summable.mul_left Lambda hSum1)
      _ = Lambda * (∑' k, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2) := tsum_mul_left
  have hThird : Lambda * (∑' k, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
      ≤ Lambda * lam 0 * (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left h23 hLpos
    calc Lambda * (∑' k, (lam k)⁻¹ * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ Lambda * (lam 0 * (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2)) := h
      _ = Lambda * lam 0 * (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2) := by ring
  have hFourth : Lambda * lam 0 * (∑' k, ((lam k)⁻¹) ^ 2 * (inner ℝ (e k) (a - b)) ^ 2)
      ≤ Lambda * lam 0 * (2 * R_u) ^ 2 := by
    have hnl : 0 ≤ Lambda * lam 0 := mul_nonneg hLpos (le_of_lt (hlam_pos 0))
    exact mul_le_mul_of_nonneg_left hboundW hnl
  exact ⟨hFirstSum, hFirstBound, hThird, hFourth⟩
  /- @proof-region region.target-node.session.f14dc6733d9abf7d end -/

end Statlib.Imported
end

