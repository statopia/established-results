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
theorem statopia_math_node_2847970413_3f215f33 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (t : ℝ) (ht : 0 ≤ t),
    ∃ B : ℕ → Set {u : U // UScale e lam t u},
      (∀ n : ℕ, ∃ u0 : U, UScale e lam t u0 ∧ ∃ eps : ℝ, 0 < eps ∧
        B n = {v : {u : U // UScale e lam t u} |
          UScaleDist e lam t (v : U) u0 < ENNReal.ofReal eps}) ∧
      ∀ A : Set {u : U // UScale e lam t u},
        (∀ v ∈ A, ∃ eps : ℝ, 0 < eps ∧
          {w : {u : U // UScale e lam t u} |
            UScaleDist e lam t (w : U) (v : U) < ENNReal.ofReal eps} ⊆ A) →
        ∃ s : Set ℕ, A = ⋃ n ∈ s, B n := by
  /- @proof-region region.target-node.session.b59afa6efdae8c97 begin -/
  intro U _ _ e lam hlam_pos hlam_anti t ht
  set D : Set U :=
    ⋃ (N : ℕ), Set.range
      (fun q : (Fin N → ℚ) => ∑ k : Fin N, ((q k : ℚ) : ℝ) • e (k : ℕ)) with hDdef
  have hnorm_add : ∀ x y : U,
      UScaleNorm e lam t (x + y) ≤ 2 * UScaleNorm e lam t x + 2 * UScaleNorm e lam t y := by
    intro x y
    have hterm : ∀ k : ℕ,
        ENNReal.ofReal (lam k ^ (-t) * (inner ℝ (e k) (x + y)) ^ 2)
          ≤ 2 * ENNReal.ofReal (lam k ^ (-t) * (inner ℝ (e k) x) ^ 2)
            + 2 * ENNReal.ofReal (lam k ^ (-t) * (inner ℝ (e k) y) ^ 2) := by
      intro k
      have hc : (0:ℝ) ≤ lam k ^ (-t) := Real.rpow_nonneg (le_of_lt (hlam_pos k)) _
      have hx0 : (0:ℝ) ≤ lam k ^ (-t) * (inner ℝ (e k) x) ^ 2 := mul_nonneg hc (sq_nonneg _)
      have hy0 : (0:ℝ) ≤ lam k ^ (-t) * (inner ℝ (e k) y) ^ 2 := mul_nonneg hc (sq_nonneg _)
      have hsq : (inner ℝ (e k) x + inner ℝ (e k) y) ^ 2
          ≤ 2 * (inner ℝ (e k) x) ^ 2 + 2 * (inner ℝ (e k) y) ^ 2 := by
        nlinarith [sq_nonneg (inner ℝ (e k) x - inner ℝ (e k) y)]
      have hreal : lam k ^ (-t) * (inner ℝ (e k) x + inner ℝ (e k) y) ^ 2
          ≤ 2 * (lam k ^ (-t) * (inner ℝ (e k) x) ^ 2)
            + 2 * (lam k ^ (-t) * (inner ℝ (e k) y) ^ 2) := by
        calc lam k ^ (-t) * (inner ℝ (e k) x + inner ℝ (e k) y) ^ 2
            ≤ lam k ^ (-t) * (2 * (inner ℝ (e k) x) ^ 2 + 2 * (inner ℝ (e k) y) ^ 2) :=
              mul_le_mul_of_nonneg_left hsq hc
          _ = 2 * (lam k ^ (-t) * (inner ℝ (e k) x) ^ 2)
                + 2 * (lam k ^ (-t) * (inner ℝ (e k) y) ^ 2) := by ring
      rw [inner_add_right]
      have h2e : (2 : ENNReal) = ENNReal.ofReal 2 := (ENNReal.ofReal_natCast 2).symm
      have hx' : 2 * ENNReal.ofReal (lam k ^ (-t) * (inner ℝ (e k) x) ^ 2)
          = ENNReal.ofReal (2 * (lam k ^ (-t) * (inner ℝ (e k) x) ^ 2)) := by
        rw [h2e, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      have hy' : 2 * ENNReal.ofReal (lam k ^ (-t) * (inner ℝ (e k) y) ^ 2)
          = ENNReal.ofReal (2 * (lam k ^ (-t) * (inner ℝ (e k) y) ^ 2)) := by
        rw [h2e, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      refine le_trans (ENNReal.ofReal_le_ofReal hreal) (le_of_eq ?_)
      rw [hx', hy', ← ENNReal.ofReal_add (by linarith) (by linarith)]
    have hmain : UScaleNorm e lam t (x + y)
        ≤ ∑' k : ℕ, (2 * ENNReal.ofReal (lam k ^ (-t) * (inner ℝ (e k) x) ^ 2)
            + 2 * ENNReal.ofReal (lam k ^ (-t) * (inner ℝ (e k) y) ^ 2)) :=
      ENNReal.tsum_le_tsum hterm
    simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left] at hmain
    simpa only [UScaleNorm] using hmain
  have hnorm3 : ∀ a b c : U, UScaleNorm e lam t (a - c)
      ≤ 2 * UScaleNorm e lam t (a - b) + 2 * UScaleNorm e lam t (b - c) := by
    intro a b c
    have h : a - c = (a - b) + (b - c) := by abel
    rw [h]
    exact hnorm_add (a - b) (b - c)
  have hsq_bound : ∀ (z : U) (η : ℝ), 0 < η →
      UScaleDist e lam t z 0 < ENNReal.ofReal η →
      UScaleNorm e lam t z ≤ ENNReal.ofReal (η ^ 2) := by
    intro z η hη hz
    have h1 : UScaleNorm e lam t z ^ ((2:ℝ)⁻¹) < ENNReal.ofReal η := by
      rw [show (2:ℝ)⁻¹ = 1/2 by norm_num]
      rw [show UScaleNorm e lam t z ^ (1/2:ℝ) = UScaleDist e lam t z 0 from by
        simp only [UScaleDist, sub_zero]]
      exact hz
    have h2 : UScaleNorm e lam t z ≤ (ENNReal.ofReal η) ^ (2:ℝ) :=
      (ENNReal.rpow_inv_le_iff (z := 2) (by norm_num : (0:ℝ) < 2)).1 (le_of_lt h1)
    have h3 : (ENNReal.ofReal η) ^ (2:ℝ) = ENNReal.ofReal (η ^ 2) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt hη) (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      exact Real.rpow_natCast η 2
    rw [h3] at h2
    exact h2
  have htri : ∀ a b c : U, ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
      UScaleNorm e lam t (a - b) ≤ ENNReal.ofReal u →
      UScaleNorm e lam t (b - c) ≤ ENNReal.ofReal v →
      UScaleDist e lam t (a - c) 0 ≤ ENNReal.ofReal (Real.sqrt (2 * u + 2 * v)) := by
    intro a b c u v hu hv h1 h2
    have h3 : UScaleNorm e lam t (a - c) ≤ ENNReal.ofReal (2 * u + 2 * v) := by
      refine le_trans (hnorm3 a b c) ?_
      have h2e : (2 : ENNReal) = ENNReal.ofReal 2 := (ENNReal.ofReal_natCast 2).symm
      have hu' : 2 * ENNReal.ofReal u = ENNReal.ofReal (2 * u) := by
        rw [h2e, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      have hv' : 2 * ENNReal.ofReal v = ENNReal.ofReal (2 * v) := by
        rw [h2e, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      calc 2 * UScaleNorm e lam t (a - b) + 2 * UScaleNorm e lam t (b - c)
          ≤ 2 * ENNReal.ofReal u + 2 * ENNReal.ofReal v := by gcongr
        _ = ENNReal.ofReal (2 * u + 2 * v) := by
              rw [hu', hv', ← ENNReal.ofReal_add (by linarith) (by linarith)]
    rw [show UScaleDist e lam t (a - c) 0 = (UScaleNorm e lam t (a - c)) ^ (1/2:ℝ) from by
      simp only [UScaleDist, sub_zero]]
    calc (UScaleNorm e lam t (a - c)) ^ (1/2:ℝ)
        ≤ (ENNReal.ofReal (2 * u + 2 * v)) ^ (1/2:ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (2 * u + 2 * v)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by norm_num : (0:ℝ) ≤ 1/2),
              ← Real.sqrt_eq_rpow]
  have hdense : ∀ u : U, UScale e lam t u → ∀ η : ℝ, 0 < η →
      ∃ (N : ℕ) (q : Fin N → ℚ),
        UScaleDist e lam t (u - ∑ k : Fin N, ((q k : ℚ) : ℝ) • e (k : ℕ)) 0
          < ENNReal.ofReal η := by
    intro u hu η hη
    set w : ℕ → ℝ := fun k => lam k ^ (-t) * (inner ℝ (e k) u) ^ 2 with hwdef
    have hw_nn : ∀ k : ℕ, 0 ≤ w k := by
      intro k
      rw [hwdef]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt (hlam_pos k)) _) (sq_nonneg _)
    have hne : (∑' k : ℕ, ENNReal.ofReal (w k)) ≠ ⊤ := by
      have hlt : UScaleNorm e lam t u < ⊤ := hu
      rw [UScaleNorm] at hlt
      exact ne_of_lt hlt
    have hwsum : Summable w := by
      have h := ENNReal.hasSum_toReal hne
      simpa only [ENNReal.toReal_ofReal, hw_nn] using h.summable
    have hpart : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop (𝓝 (∑' i, w i)) :=
      (hasSum_iff_tendsto_nat_of_nonneg hw_nn (∑' i, w i)).1 hwsum.hasSum
    have htail_eq : ∀ n : ℕ, ∑' i, w (i + n) = (∑' i, w i) - ∑ i ∈ Finset.range n, w i := by
      intro n
      have h := Summable.sum_add_tsum_nat_add n hwsum
      linarith
    have htail : Tendsto (fun n => ∑' i, w (i + n)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => (∑' i, w i) - ∑ i ∈ Finset.range n, w i) atTop (𝓝 0) := by
        have hc : Tendsto (fun _ : ℕ => (∑' i, w i)) atTop (𝓝 (∑' i, w i)) := tendsto_const_nhds
        have h3 := hc.sub hpart
        simpa using h3
      rw [show (fun n => ∑' i, w (i + n))
        = fun n => (∑' i, w i) - ∑ i ∈ Finset.range n, w i from funext htail_eq]
      exact h2
    have hquarter : (0:ℝ) < η ^ 2 / 4 := by positivity
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∑' i, w (i + N₀) < η ^ 2 / 4 := by
      obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 htail) (η ^ 2 / 4) hquarter
      refine ⟨N₁, ?_⟩
      have h1 : dist (∑' i, w (i + N₁)) 0 < η ^ 2 / 4 := hN₁ N₁ le_rfl
      rw [Real.dist_eq, sub_zero] at h1
      exact lt_of_le_of_lt (le_abs_self _) h1
    have hrat : ∃ q : Fin N₀ → ℚ, ∑ k : Fin N₀,
        lam (k:ℕ) ^ (-t) * (inner ℝ (e (k:ℕ)) u - (q k : ℝ)) ^ 2 < η ^ 2 / 4 := by
      set sg : ℝ := ∑ k : Fin N₀, lam (k:ℕ) ^ (-t) with hsg
      have hsg0 : 0 ≤ sg := by
        rw [hsg]
        exact Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (le_of_lt (hlam_pos (k:ℕ))) _)
      have hSpos : (0:ℝ) < sg + 1 := by linarith
      have harg : (0:ℝ) < η ^ 2 / 4 / (sg + 1) := by positivity
      set δ' : ℝ := Real.sqrt (η ^ 2 / 4 / (sg + 1)) with hδ'
      have hδ'pos : 0 < δ' := by
        rw [hδ']
        exact Real.sqrt_pos.2 harg
      have hδ'sq : δ' ^ 2 = η ^ 2 / 4 / (sg + 1) := by
        rw [hδ']
        exact Real.sq_sqrt (le_of_lt harg)
      have key : ∀ k : Fin N₀, ∃ q : ℚ,
          lam (k:ℕ) ^ (-t) * (inner ℝ (e (k:ℕ)) u - (q:ℝ)) ^ 2
            ≤ lam (k:ℕ) ^ (-t) * δ' ^ 2 := by
        intro k
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
          (show inner ℝ (e (k:ℕ)) u - δ' < inner ℝ (e (k:ℕ)) u + δ' by linarith)
        refine ⟨q, ?_⟩
        have hsq : (inner ℝ (e (k:ℕ)) u - (q:ℝ)) ^ 2 < δ' ^ 2 := by
          nlinarith [hq1, hq2, hδ'pos]
        exact mul_le_mul_of_nonneg_left (le_of_lt hsq)
          (Real.rpow_nonneg (le_of_lt (hlam_pos (k:ℕ))) _)
      choose q hq using key
      refine ⟨q, ?_⟩
      calc ∑ k : Fin N₀, lam (k:ℕ) ^ (-t) * (inner ℝ (e (k:ℕ)) u - (q k : ℝ)) ^ 2
          ≤ ∑ k : Fin N₀, lam (k:ℕ) ^ (-t) * δ' ^ 2 := Finset.sum_le_sum (fun k _ => hq k)
        _ = sg * δ' ^ 2 := by
              have hfac : ∑ k : Fin N₀, lam (k:ℕ) ^ (-t) * δ' ^ 2
                  = (∑ k : Fin N₀, lam (k:ℕ) ^ (-t)) * δ' ^ 2 := by
                simp only [Finset.sum_mul]
              rw [hsg]
              exact hfac
        _ < δ' ^ 2 * (sg + 1) := by
              have hlt : sg * δ' ^ 2 < (sg + 1) * δ' ^ 2 :=
                mul_lt_mul_of_pos_right (by linarith : sg < sg + 1) (pow_pos hδ'pos 2)
              linarith
        _ = η ^ 2 / 4 := by
              rw [hδ'sq]
              field_simp
    obtain ⟨q, hq⟩ := hrat
    refine ⟨N₀, q, ?_⟩
    set d : U := ∑ k : Fin N₀, ((q k : ℚ) : ℝ) • e (k : ℕ) with hd
    have hdiag : ∀ k : ℕ, inner ℝ (e k) (e k) = 1 := by
      intro k
      rw [real_inner_self_eq_norm_sq, e.orthonormal.norm_eq_one k]
      norm_num
    have hdz : ∀ k : ℕ, N₀ ≤ k → inner ℝ (e k) d = 0 := by
      intro k hk
      rw [hd, inner_sum]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have hne : k ≠ (j : ℕ) := by
        have := j.isLt
        omega
      simp [inner_smul_right, e.orthonormal.inner_eq_zero hne]
    have hdv : ∀ k : Fin N₀, inner ℝ (e (k:ℕ)) d = (q k : ℝ) := by
      intro k
      rw [hd, inner_sum]
      rw [Finset.sum_eq_single k]
      · rw [inner_smul_right, hdiag (k:ℕ), mul_one]
      · intro j _ hjk
        have hne : (k:ℕ) ≠ (j:ℕ) := by
          intro h
          exact hjk (Fin.ext h.symm)
        simp [inner_smul_right, e.orthonormal.inner_eq_zero hne]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    set f : ℕ → ℝ := fun k => lam k ^ (-t) * (inner ℝ (e k) (u - d)) ^ 2 with hf
    have hf_nn : ∀ k : ℕ, 0 ≤ f k := by
      intro k
      rw [hf]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt (hlam_pos k)) _) (sq_nonneg _)
    have hf_tail : ∀ i : ℕ, f (i + N₀) = w (i + N₀) := by
      intro i
      have h0 : inner ℝ (e (i + N₀)) d = 0 := hdz (i + N₀) (by omega)
      rw [hf, hwdef]
      simp only [inner_sub_right, h0, sub_zero]
    have hwshift : Summable (fun i : ℕ => w (i + N₀)) := (summable_nat_add_iff N₀).2 hwsum
    have hfsumm : Summable f := by
      refine (summable_nat_add_iff N₀).1 ?_
      rw [show (fun i : ℕ => f (i + N₀)) = fun i : ℕ => w (i + N₀) from funext hf_tail]
      exact hwshift
    set q' : ℕ → ℚ := fun i => if h : i < N₀ then q ⟨i, h⟩ else 0 with hq'def
    have hq'val : ∀ (i : ℕ) (h : i < N₀), q' i = q ⟨i, h⟩ := by
      intro i h
      rw [hq'def]
      simp only
      rw [dif_pos h]
    have hhead : ∑ i ∈ Finset.range N₀, f i < η ^ 2 / 4 := by
      have hconv1 : ∑ i ∈ Finset.range N₀, f i
          = ∑ i ∈ Finset.range N₀, lam i ^ (-t) * (inner ℝ (e i) u - (q' i : ℝ)) ^ 2 := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        have hdi : inner ℝ (e i) d = (q' i : ℝ) := by
          rw [hq'val i hi]
          exact hdv ⟨i, hi⟩
        rw [hf]
        simp only [inner_sub_right, hdi]
      have hconv2 : ∑ i ∈ Finset.range N₀, lam i ^ (-t) * (inner ℝ (e i) u - (q' i : ℝ)) ^ 2
          = ∑ k : Fin N₀, lam (k:ℕ) ^ (-t) * (inner ℝ (e (k:ℕ)) u - (q' (k:ℕ) : ℝ)) ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range
          (fun i => lam i ^ (-t) * (inner ℝ (e i) u - (q' i : ℝ)) ^ 2) N₀]
      have hconv3 : ∑ k : Fin N₀, lam (k:ℕ) ^ (-t) * (inner ℝ (e (k:ℕ)) u - (q' (k:ℕ) : ℝ)) ^ 2
          = ∑ k : Fin N₀, lam (k:ℕ) ^ (-t) * (inner ℝ (e (k:ℕ)) u - (q k : ℝ)) ^ 2 := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hq'val (k:ℕ) k.isLt]
      calc ∑ i ∈ Finset.range N₀, f i
          = ∑ i ∈ Finset.range N₀, lam i ^ (-t) * (inner ℝ (e i) u - (q' i : ℝ)) ^ 2 := hconv1
        _ = ∑ k : Fin N₀, lam (k:ℕ) ^ (-t) * (inner ℝ (e (k:ℕ)) u - (q' (k:ℕ) : ℝ)) ^ 2 := hconv2
        _ = ∑ k : Fin N₀, lam (k:ℕ) ^ (-t) * (inner ℝ (e (k:ℕ)) u - (q k : ℝ)) ^ 2 := hconv3
        _ < η ^ 2 / 4 := hq
    have htail' : ∑' i : ℕ, f (i + N₀) < η ^ 2 / 4 := by
      rw [show (fun i : ℕ => f (i + N₀)) = fun i : ℕ => w (i + N₀) from funext hf_tail]
      exact hN₀
    have hfin : ∑' k : ℕ, f k < η ^ 2 := by
      have hsplit := Summable.sum_add_tsum_nat_add N₀ hfsumm
      rw [← hsplit]
      linarith
    have hnorm : UScaleNorm e lam t (u - d) < ENNReal.ofReal (η ^ 2) := by
      have hnn : ∀ k : ℕ, 0 ≤ Real.rpow (lam k) (-t) * (inner ℝ (e k) (u - d)) ^ 2 :=
        fun k => mul_nonneg (Real.rpow_nonneg (le_of_lt (hlam_pos k)) _) (sq_nonneg _)
      have hsum : Summable (fun k : ℕ => Real.rpow (lam k) (-t) * (inner ℝ (e k) (u - d)) ^ 2) :=
        hfsumm
      rw [UScaleNorm]
      rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : (0:ℝ) < η ^ 2)).2 hfin
    have h3 : (ENNReal.ofReal η) ^ (2:ℝ) = ENNReal.ofReal (η ^ 2) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt hη) (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      exact Real.rpow_natCast η 2
    have h4 : UScaleNorm e lam t (u - d) ^ ((2:ℝ)⁻¹) < ENNReal.ofReal η := by
      have h5 : UScaleNorm e lam t (u - d) < (ENNReal.ofReal η) ^ (2:ℝ) := by
        rw [h3]
        exact hnorm
      exact (ENNReal.rpow_inv_lt_iff (z := 2) (by norm_num : (0:ℝ) < 2)).2 h5
    rw [show UScaleDist e lam t (u - d) 0 = UScaleNorm e lam t (u - d) ^ (1/2:ℝ) from by
      simp only [UScaleDist, sub_zero]]
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ from by norm_num]
    exact h4
  have hDsub : ∀ d ∈ D, UScale e lam t d := by
    intro d hd
    rw [hDdef] at hd
    simp only [Set.mem_iUnion, Set.mem_range] at hd
    obtain ⟨N, q, rfl⟩ := hd
    set d0 : U := ∑ j : Fin N, ((q j : ℚ) : ℝ) • e (j : ℕ) with hd0
    change UScaleNorm e lam t d0 < ⊤
    have hinner_zero : ∀ k : ℕ, N ≤ k → inner ℝ (e k) d0 = 0 := by
      intro k hk
      rw [hd0, inner_sum]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have hne : k ≠ (j : ℕ) := by
        have := j.isLt
        omega
      simp [inner_smul_right, e.orthonormal.inner_eq_zero hne]
    set g : ℕ → ℝ := fun k => lam k ^ (-t) * (inner ℝ (e k) d0) ^ 2 with hg
    have hg_nonneg : ∀ k : ℕ, 0 ≤ g k := by
      intro k
      rw [hg]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt (hlam_pos k)) _) (sq_nonneg _)
    have hg_zero : ∀ k : ℕ, N ≤ k → g k = 0 := by
      intro k hk
      simp [hg, hinner_zero k hk]
    have hconst : ∀ n ≥ N, ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.range N, g i := by
      intro n
      induction n with
      | zero =>
        intro hk
        have hN0 : N = 0 := by omega
        rw [hN0]
      | succ k ih =>
        intro hk
        rcases Nat.eq_or_lt_of_le hk with heq | hlt
        · rw [heq]
        · have hkN : N ≤ k := by omega
          rw [Finset.sum_range_succ, ih hkN, hg_zero k hkN, add_zero]
    have hev : (fun n => ∑ i ∈ Finset.range n, g i)
        =ᶠ[atTop] (fun _ => ∑ i ∈ Finset.range N, g i) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact hconst n hn
    have hlim : Tendsto (fun n => ∑ i ∈ Finset.range n, g i) atTop
        (𝓝 (∑ i ∈ Finset.range N, g i)) :=
      Tendsto.congr' hev.symm tendsto_const_nhds
    have hsummable : Summable g :=
      (hasSum_iff_tendsto_nat_of_nonneg hg_nonneg _).2 hlim |>.summable
    rw [UScaleNorm]
    exact Summable.tsum_ofReal_lt_top hsummable
  have hScount : ({p : U × ℚ | p.1 ∈ D ∧ 0 < p.2} : Set (U × ℚ)).Countable := by
    have hDc : D.Countable := by
      rw [hDdef]
      exact Set.countable_iUnion (fun N => Set.countable_range _)
    refine Set.Countable.mono ?_ (hDc.prod Set.countable_univ)
    rintro ⟨d, q⟩ ⟨hdd, _⟩
    exact Set.mem_prod.2 ⟨hdd, Set.mem_univ q⟩
  have hSne : ({p : U × ℚ | p.1 ∈ D ∧ 0 < p.2} : Set (U × ℚ)).Nonempty := by
    refine ⟨(0, 1), ?_, by norm_num⟩
    rw [hDdef]
    refine Set.mem_iUnion.2
      ⟨0, Set.mem_range.2 ⟨fun k => absurd k.isLt (Nat.not_lt_zero (k : ℕ)), ?_⟩⟩
    simp
  have hbase : ∀ v : U, UScale e lam t v → ∀ ε : ℝ, 0 < ε →
      ∃ p ∈ ({p : U × ℚ | p.1 ∈ D ∧ 0 < p.2} : Set (U × ℚ)),
        UScaleDist e lam t v p.1 < ENNReal.ofReal (p.2 : ℝ) ∧
        ∀ w : U, UScale e lam t w →
          UScaleDist e lam t w p.1 < ENNReal.ofReal (p.2 : ℝ) →
          UScaleDist e lam t w v < ENNReal.ofReal ε := by
    intro v hv ε hε
    have heven : ∀ x y : U, UScaleNorm e lam t (y - x) = UScaleNorm e lam t (x - y) := by
      intro x y
      simp only [UScaleNorm]
      refine tsum_congr (fun k => ?_)
      simp only [inner_sub_right]
      congr 1
      ring
    have hsym : ∀ x y : U, UScaleDist e lam t (x - y) 0 = UScaleDist e lam t (y - x) 0 := by
      intro x y
      simp only [UScaleDist, sub_zero, heven x y]
    set δ : ℝ := ε / 16 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨N, q, hq⟩ := hdense v hv δ hδpos
    set d0 : U := ∑ k : Fin N, ((q k : ℚ) : ℝ) • e (k : ℕ) with hd0
    have hdD : d0 ∈ D := by
      rw [hDdef]
      exact Set.mem_iUnion.2 ⟨N, Set.mem_range.2 ⟨q, rfl⟩⟩
    have hne : UScaleDist e lam t (v - d0) 0 ≠ ⊤ := (lt_of_lt_of_le hq le_top).ne
    set s : ℝ := (UScaleDist e lam t (v - d0) 0).toReal with hs
    have hsnonneg : 0 ≤ s := by
      rw [hs]; exact ENNReal.toReal_nonneg
    have hdists : UScaleDist e lam t (v - d0) 0 = ENNReal.ofReal s :=
      (ENNReal.ofReal_toReal hne).symm
    have hslt : s < δ := by
      have h1 : ENNReal.ofReal s = UScaleDist e lam t (v - d0) 0 := hdists.symm
      rw [← h1] at hq
      exact (ENNReal.ofReal_lt_ofReal_iff hδpos).1 hq
    obtain ⟨r, hrs, hrδ⟩ := exists_rat_btwn hslt
    have hrposR : (0:ℝ) < (r:ℝ) := lt_of_le_of_lt hsnonneg hrs
    have hrpos : (0:ℚ) < r := by exact_mod_cast hrposR
    have hrle : ENNReal.ofReal (r:ℝ) ≤ ENNReal.ofReal δ :=
      (ENNReal.ofReal_le_ofReal_iff (le_of_lt hδpos)).2 (le_of_lt hrδ)
    have hsmall : UScaleDist e lam t (v - d0) 0 < ENNReal.ofReal (r:ℝ) := by
      rw [hdists]
      exact (ENNReal.ofReal_lt_ofReal_iff hrposR).2 hrs
    have hvball : UScaleDist e lam t v d0 < ENNReal.ofReal (r:ℝ) := by
      rw [show UScaleDist e lam t v d0 = UScaleDist e lam t (v - d0) 0 from by
        simp only [UScaleDist, sub_zero]]
      exact hsmall
    refine ⟨(d0, r), ⟨hdD, hrpos⟩, hvball, ?_⟩
    intro w hw hwd
    have hA : UScaleNorm e lam t (w - d0) ≤ ENNReal.ofReal ((r:ℝ) ^ 2) :=
      hsq_bound (w - d0) (r:ℝ) hrposR (by
        rw [show UScaleDist e lam t (w - d0) 0 = UScaleDist e lam t w d0 from by
          simp only [UScaleDist, sub_zero]]
        exact hwd)
    have hB : UScaleNorm e lam t (d0 - v) ≤ ENNReal.ofReal (δ ^ 2) := by
      rw [heven v d0]
      exact hsq_bound (v - d0) δ hδpos hq
    have hmain : UScaleDist e lam t (w - v) 0
        ≤ ENNReal.ofReal (Real.sqrt (2 * (r:ℝ) ^ 2 + 2 * δ ^ 2)) :=
      htri w d0 v ((r:ℝ) ^ 2) (δ ^ 2) (sq_nonneg _) (sq_nonneg _) hA hB
    have hnum : Real.sqrt (2 * (r:ℝ) ^ 2 + 2 * δ ^ 2) < ε := by
      have h1 : Real.sqrt (2 * (r:ℝ) ^ 2 + 2 * δ ^ 2) ≤ ε / 2 := by
        have h2 : Real.sqrt (2 * (r:ℝ) ^ 2 + 2 * δ ^ 2) ≤ Real.sqrt ((ε / 2) ^ 2) := by
          rw [Real.sqrt_le_sqrt_iff (by positivity : (0:ℝ) ≤ (ε / 2) ^ 2)]
          rw [hδ] at hrδ ⊢
          nlinarith [hrδ, hrposR, hε]
        rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ ε / 2)] at h2
      linarith
    calc UScaleDist e lam t w v
        = UScaleDist e lam t (w - v) 0 := by simp only [UScaleDist, sub_zero]
      _ ≤ ENNReal.ofReal (Real.sqrt (2 * (r:ℝ) ^ 2 + 2 * δ ^ 2)) := hmain
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 hnum
  obtain ⟨f, hfsurj⟩ := (Set.countable_iff_exists_surjective hSne).1 hScount
  let B : ℕ → Set {u : U // UScale e lam t u} := fun n =>
    {v | UScaleDist e lam t (v : U)
        (((f n : {p : U × ℚ | p.1 ∈ D ∧ 0 < p.2}) : U × ℚ)).1
      < ENNReal.ofReal ((((f n : {p : U × ℚ | p.1 ∈ D ∧ 0 < p.2}) : U × ℚ)).2 : ℝ)}
  refine ⟨B, ?_, ?_⟩
  · intro n
    have hmem : (((f n : {p : U × ℚ | p.1 ∈ D ∧ 0 < p.2}) : U × ℚ)).1 ∈ D := (f n).2.1
    have hrpos : 0 < (((f n : {p : U × ℚ | p.1 ∈ D ∧ 0 < p.2}) : U × ℚ)).2 := (f n).2.2
    exact ⟨_, hDsub _ hmem, _, by exact_mod_cast hrpos, rfl⟩
  · intro A hA
    refine ⟨{n : ℕ | B n ⊆ A}, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨ε, hεpos, hεsub⟩ := hA x hx
      obtain ⟨p, hpS, hxd, hball⟩ := hbase (x : U) x.2 ε hεpos
      obtain ⟨n, hn⟩ := hfsurj ⟨p, hpS⟩
      have hfn : (((f n : {p : U × ℚ | p.1 ∈ D ∧ 0 < p.2}) : U × ℚ)) = p := by
        simpa using congrArg Subtype.val hn
      refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
      · intro y hy
        have hy' : UScaleDist e lam t (y : U)
            (((f n : {p : U × ℚ | p.1 ∈ D ∧ 0 < p.2}) : U × ℚ)).1
            < ENNReal.ofReal ((((f n : {p : U × ℚ | p.1 ∈ D ∧ 0 < p.2}) : U × ℚ)).2 : ℝ) := hy
        rw [hfn] at hy'
        exact hεsub (hball (y : U) y.2 hy')
      · have hx' : UScaleDist e lam t (x : U)
            (((f n : {p : U × ℚ | p.1 ∈ D ∧ 0 < p.2}) : U × ℚ)).1
            < ENNReal.ofReal ((((f n : {p : U × ℚ | p.1 ∈ D ∧ 0 < p.2}) : U × ℚ)).2 : ℝ) := by
          rw [hfn]
          exact hxd
        exact hx'
    · intro hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨n, hnA, hxn⟩ := hx
      exact hnA hxn
  /- @proof-region region.target-node.session.b59afa6efdae8c97 end -/

end Statlib.Imported
end

