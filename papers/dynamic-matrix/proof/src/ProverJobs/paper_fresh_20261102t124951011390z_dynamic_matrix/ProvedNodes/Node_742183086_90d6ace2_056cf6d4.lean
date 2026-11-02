import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix

open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_742183086_90d6ace2 : ∀ (Omega : Type*) [MeasurableSpace Omega]
    (m1 m2 T : ℕ) (n : Fin T → ℕ) (hn : ∀ j, 0 < n j)
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : (j : Fin T) → Fin (n j) → Omega → Matrix (Fin m1) (Fin m2) ℝ)
    (hX_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (X j i))
    (xi : (j : Fin T) → Fin (n j) → Omega → ℝ)
    (hxi_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (xi j i))
    (M0 : Fin T → Matrix (Fin m1) (Fin m2) ℝ)
    (Y : (j : Fin T) → Fin (n j) → Omega → ℝ)
    (hY_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (Y j i))
    (hY : ∀ (j : Fin T) (i : Fin (n j)) (om : Omega),
      Y j i om = frobInner (M0 j) (X j i om) + xi j i om)
    (hX2 : ∀ (j : Fin T) (i : Fin (n j)),
      Integrable (fun om => frobNorm (X j i om) ^ 2) P)
    (hXi : ∀ (j : Fin T) (i : Fin (n j)),
      Integrable (fun om => |xi j i om| * frobNorm (X j i om)) P)
    (hXi_zero : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      ∫ om, xi j i om * (X j i om) a b ∂P = 0)
    (hXi_int : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      Integrable (fun om => xi j i om * (X j i om) a b) P)
    (hYX_int : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      Integrable (fun om => Y j i om * (X j i om) a b) P)
    (Sigma : Matrix (Fin m1 × Fin m2) (Fin m1 × Fin m2) ℝ) (hSigma : Sigma.PosDef)
    (w : Fin T → ℝ) (hw_sum : ∑ j : Fin T, w j = 1)
    (hDesign : ∀ (j : Fin T) (M : Matrix (Fin m1) (Fin m2) ℝ),
      (1 / (n j : ℝ)) * ∑ i : Fin (n j), ∫ om, frobInner M (X j i om) ^ 2 ∂P
        = secondMomentForm Sigma M),
    (∀ (om : Omega) (a : Fin m1) (b : Fin m2),
      (∑ j : Fin T, w j • ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i om • X j i om)) a b
        = (∑ a' : Fin m1, ∑ b' : Fin m2,
            Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b')
          + (∑ j : Fin T, w j • DeltaMat P n Y X j om) a b) ∧
    (∀ (om : Omega) (A : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner
        (∑ j : Fin T, w j • ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i om • X j i om)) A
        = (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
            (∑ j : Fin T, w j • M0 j) a b * Sigma (a, b) (a', b') * A a' b')
          + frobInner (∑ j : Fin T, w j • DeltaMat P n Y X j om) A) ∧
    (∀ (A : Matrix (Fin m1) (Fin m2) ℝ),
      (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
          A a b * Sigma (a, b) (a', b') * A a' b')
        = secondMomentForm Sigma A) ∧
    (∀ (om : Omega) (A : Matrix (Fin m1) (Fin m2) ℝ) (lam : ℝ),
      localObj Sigma P n Y X w lam A om
        = secondMomentForm Sigma A
          - 2 * ((∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
                    (∑ j : Fin T, w j • M0 j) a b * Sigma (a, b) (a', b') * A a' b')
                + frobInner (∑ j : Fin T, w j • DeltaMat P n Y X j om) A)
          + lam * Statlib.HighDim.Vocabulary.nuclearNorm A) := by
  /- @proof-region region.target-node.session.9a6de9e5751a9da1 begin -/
  intro Ω instΩ m1 m2 T n hn P instP X hX_m xi hxi_m M0 Y hY_m hY hX2 hXi hXi_zero hXi_int hYX_int Sigma hSigma w hw_sum hDesign
  have hModel := hY
  have hXiZero := hXi_zero
  have hXiInt := hXi_int
  have hsum_prod : ∀ (f : Fin m1 × Fin m2 → ℝ),
      (∑ x : Fin m1 × Fin m2, f x) = ∑ a : Fin m1, ∑ b : Fin m2, f (a, b) := by
    intro f
    rw [← Finset.univ_product_univ (α := Fin m1) (β := Fin m2)]
    rw [Finset.sum_product]
  have hfr : ∀ (Z : Matrix (Fin m1) (Fin m2) ℝ),
      frobNorm Z ^ 2 = ∑ a : Fin m1, ∑ b : Fin m2, Z a b ^ 2 := by
    intro Z
    have hnn : 0 ≤ ∑ a : Fin m1, ∑ b : Fin m2, Z a b ^ 2 :=
      Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (Z a b)))
    simp only [frobNorm]
    exact Real.sq_sqrt hnn
  have hmsum : ∀ {k : ℕ} (s : Finset (Fin k)) (g : Fin k → Ω → ℝ),
      (∀ p ∈ s, Measurable (g p)) → Measurable (fun ω => ∑ p ∈ s, g p ω) := by
    intro k s
    induction s using Finset.induction with
    | empty =>
        intro g _
        simpa using (measurable_const : Measurable fun _ : Ω => (0 : ℝ))
    | insert x s hx ih =>
        intro g hg
        have h1 : Measurable (g x) := hg x (Finset.mem_insert_self x s)
        have h2 : Measurable (fun ω => ∑ p ∈ s, g p ω) :=
          ih g (fun p hp => hg p (Finset.mem_insert_of_mem hp))
        simpa only [Finset.sum_insert hx] using h1.add h2
  have hqInt : ∀ (j : Fin T) (M : Matrix (Fin m1) (Fin m2) ℝ) (i : Fin (n j)),
      Integrable (fun ω => frobInner M (X j i ω) ^ 2) P := by
    intro j M i
    have hentry : ∀ (p : Fin m1) (q : Fin m2), Measurable (fun ω => (X j i ω) p q) := by
      intro p q
      exact (measurable_pi_apply q).comp ((measurable_pi_apply p).comp (hX_m j i))
    have hmeas : Measurable (fun ω => frobInner M (X j i ω)) := by
      have hstep : Measurable (fun ω => ∑ p : Fin m1, ∑ q : Fin m2, M p q * (X j i ω) p q) :=
        hmsum (Finset.univ : Finset (Fin m1))
          (fun p ω => ∑ q : Fin m2, M p q * (X j i ω) p q)
          (fun p _ => hmsum (Finset.univ : Finset (Fin m2))
            (fun q ω => M p q * (X j i ω) p q)
            (fun q _ => measurable_const.mul (hentry p q)))
      simpa only [frobInner] using hstep
    refine Integrable.mono'
      ((hX2 j i).const_mul (∑ p : Fin m1 × Fin m2, (M p.1 p.2) ^ 2))
      (hmeas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    have h1 : frobInner M (X j i ω) = ∑ p : Fin m1 × Fin m2, M p.1 p.2 * (X j i ω) p.1 p.2 := by
      simp only [frobInner]
      exact (hsum_prod (fun p => M p.1 p.2 * (X j i ω) p.1 p.2)).symm
    have h2 : (∑ p : Fin m1 × Fin m2, (X j i ω) p.1 p.2 ^ 2) = frobNorm (X j i ω) ^ 2 := by
      rw [hfr]
      exact hsum_prod (fun p => (X j i ω) p.1 p.2 ^ 2)
    have h3 : frobInner M (X j i ω) ^ 2
        ≤ (∑ p : Fin m1 × Fin m2, (M p.1 p.2) ^ 2) * frobNorm (X j i ω) ^ 2 := by
      rw [h1, ← h2]
      exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m1 × Fin m2))
        (fun p => M p.1 p.2) (fun p => (X j i ω) p.1 p.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h3
  have hconj2 : ∀ A : Matrix (Fin m1) (Fin m2) ℝ,
      (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
          A a b * Sigma (a, b) (a', b') * A a' b') = secondMomentForm Sigma A := by
    intro A
    simp only [secondMomentForm, vecOf, hsum_prod]
  have hfrob_add : ∀ (M N Z : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner (M + N) Z = frobInner M Z + frobInner N Z := by
    intro M N Z
    simp [frobInner, add_mul, Finset.sum_add_distrib]
  have hE : ∀ (y : Fin m1 × Fin m2) (Z : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner (fun a b => if (a, b) = y then (1 : ℝ) else 0) Z = Z y.1 y.2 := by
    intro y Z
    have key : (∑ x : Fin m1 × Fin m2, (if (x.1, x.2) = y then (1 : ℝ) else 0) * Z x.1 x.2)
        = Z y.1 y.2 := by
      refine (Finset.sum_eq_single y ?_ ?_).trans ?_
      · rintro ⟨x1, x2⟩ - hx
        simp [hx]
      · intro hy
        exact absurd (Finset.mem_univ y) hy
      · simp [Prod.mk.eta]
    simp only [frobInner]
    exact (hsum_prod (fun x => (if (x.1, x.2) = y then (1 : ℝ) else 0) * Z x.1 x.2)).symm.trans
      key
  have hsq : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      Integrable (fun ω => (X j i ω) a b ^ 2) P := by
    intro j i a b
    refine (hqInt j (fun a' b' => if (a', b') = (a, b) then (1 : ℝ) else 0) i).congr ?_
    filter_upwards with ω
    rw [hE]
  have hmul : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2)
      (a' : Fin m1) (b' : Fin m2),
      Integrable (fun ω => (X j i ω) a' b' * (X j i ω) a b) P := by
    intro j i a b a' b'
    have hsum : Integrable (fun ω => ((X j i ω) a' b' + (X j i ω) a b) ^ 2) P := by
      refine (hqInt j ((fun p q => if (p, q) = (a', b') then (1 : ℝ) else 0)
        + (fun p q => if (p, q) = (a, b) then (1 : ℝ) else 0)) i).congr ?_
      filter_upwards with ω
      rw [hfrob_add, hE, hE]
    have h4 : Integrable (fun ω => (((X j i ω) a' b' + (X j i ω) a b) ^ 2
        - (X j i ω) a' b' ^ 2 - (X j i ω) a b ^ 2) * (1 / 2)) P :=
      ((hsum.sub (hsq j i a' b')).sub (hsq j i a b)).mul_const (1 / 2)
    refine h4.congr ?_
    filter_upwards with ω
    ring
  have hsymm : ∀ y z : Fin m1 × Fin m2, Sigma y z = Sigma z y := by
    intro y z
    have h := hSigma.isHermitian.apply z y
    simpa using h
  have hsum_apply : ∀ (s : Finset (Fin T)) (g : Fin T → Matrix (Fin m1) (Fin m2) ℝ)
      (a : Fin m1) (b : Fin m2), (∑ j ∈ s, g j) a b = ∑ j ∈ s, g j a b := by
    intro s g a b
    induction s using Finset.induction with
    | empty => simp
    | insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.sum_insert hx]
        simp [ih]
  have hprod : ∀ (j : Fin T) (i : Fin (n j)) (M N : Matrix (Fin m1) (Fin m2) ℝ),
      Integrable (fun ω => frobInner M (X j i ω) * frobInner N (X j i ω)) P := by
    intro j i M N
    have hsq2 : Integrable
        (fun ω => (frobInner M (X j i ω) + frobInner N (X j i ω)) ^ 2) P := by
      refine (hqInt j (M + N) i).congr ?_
      filter_upwards with ω
      rw [hfrob_add]
    have h4 : Integrable (fun ω => ((frobInner M (X j i ω) + frobInner N (X j i ω)) ^ 2
        - frobInner M (X j i ω) ^ 2 - frobInner N (X j i ω) ^ 2) * (1 / 2)) P :=
      ((hsq2.sub (hqInt j M i)).sub (hqInt j N i)).mul_const (1 / 2)
    refine h4.congr ?_
    filter_upwards with ω
    ring
  have hcross : ∀ (M : Matrix (Fin m1) (Fin m2) ℝ) (y : Fin m1 × Fin m2),
      (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
          M a b * Sigma (a, b) (a', b') * (if (a', b') = y then (1 : ℝ) else 0))
        = ∑ a : Fin m1, ∑ b : Fin m2, M a b * Sigma (a, b) y := by
    intro M y
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    have key : ∀ c : ℝ,
        (∑ x : Fin m1 × Fin m2, c * Sigma (a, b) x * (if x = y then (1 : ℝ) else 0))
          = c * Sigma (a, b) y := by
      intro c
      refine (Finset.sum_eq_single y ?_ ?_).trans ?_
      · rintro ⟨x1, x2⟩ - hx
        simp [hx]
      · intro hy
        exact absurd (Finset.mem_univ y) hy
      · simp
    exact (hsum_prod (fun x => M a b * Sigma (a, b) x * (if x = y then (1 : ℝ) else 0))).symm.trans
      (key (M a b))
  have hbilin : ∀ (j : Fin T) (M N : Matrix (Fin m1) (Fin m2) ℝ),
      1 / (n j : ℝ) * ∑ i : Fin (n j), ∫ ω, frobInner M (X j i ω) * frobInner N (X j i ω) ∂P
        = ∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
            M a b * Sigma (a, b) (a', b') * N a' b' := by
    intro j M N
    let B : Matrix (Fin m1) (Fin m2) ℝ → Matrix (Fin m1) (Fin m2) ℝ → ℝ :=
      fun M N => ∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
        M a b * Sigma (a, b) (a', b') * N a' b'
    show 1 / (n j : ℝ) * ∑ i : Fin (n j),
        ∫ ω, frobInner M (X j i ω) * frobInner N (X j i ω) ∂P = B M N
    have hfg : ∀ i : Fin (n j),
        Integrable (fun ω => frobInner M (X j i ω) * frobInner N (X j i ω)) P :=
      fun i => hprod j i M N
    have hf2 : ∀ i : Fin (n j), Integrable (fun ω => frobInner M (X j i ω) ^ 2) P :=
      fun i => hqInt j M i
    have hg2 : ∀ i : Fin (n j), Integrable (fun ω => frobInner N (X j i ω) ^ 2) P :=
      fun i => hqInt j N i
    have hper : ∀ i : Fin (n j),
        ∫ ω, (frobInner M (X j i ω) + frobInner N (X j i ω)) ^ 2 ∂P
          = (∫ ω, frobInner M (X j i ω) ^ 2 ∂P
              + 2 * ∫ ω, frobInner M (X j i ω) * frobInner N (X j i ω) ∂P)
            + ∫ ω, frobInner N (X j i ω) ^ 2 ∂P := by
      intro i
      have key : ∀ ω, (frobInner M (X j i ω) + frobInner N (X j i ω)) ^ 2
          = (frobInner M (X j i ω) ^ 2
              + 2 * (frobInner M (X j i ω) * frobInner N (X j i ω)))
            + frobInner N (X j i ω) ^ 2 := fun ω => by ring
      calc ∫ ω, (frobInner M (X j i ω) + frobInner N (X j i ω)) ^ 2 ∂P
          = ∫ ω, ((frobInner M (X j i ω) ^ 2
              + 2 * (frobInner M (X j i ω) * frobInner N (X j i ω)))
              + frobInner N (X j i ω) ^ 2) ∂P := by simp only [key]
        _ = ∫ ω, (frobInner M (X j i ω) ^ 2
              + 2 * (frobInner M (X j i ω) * frobInner N (X j i ω))) ∂P
            + ∫ ω, frobInner N (X j i ω) ^ 2 ∂P :=
              integral_add ((hf2 i).add ((hfg i).const_mul 2)) (hg2 i)
        _ = (∫ ω, frobInner M (X j i ω) ^ 2 ∂P
              + ∫ ω, 2 * (frobInner M (X j i ω) * frobInner N (X j i ω)) ∂P)
            + ∫ ω, frobInner N (X j i ω) ^ 2 ∂P := by
              rw [integral_add (hf2 i) ((hfg i).const_mul 2)]
        _ = (∫ ω, frobInner M (X j i ω) ^ 2 ∂P
              + 2 * ∫ ω, frobInner M (X j i ω) * frobInner N (X j i ω) ∂P)
            + ∫ ω, frobInner N (X j i ω) ^ 2 ∂P := by
              rw [integral_const_mul]
    have hQ : 1 / (n j : ℝ) * ∑ i : Fin (n j),
          ∫ ω, (frobInner M (X j i ω) + frobInner N (X j i ω)) ^ 2 ∂P
        = (1 / (n j : ℝ) * ∑ i : Fin (n j), ∫ ω, frobInner M (X j i ω) ^ 2 ∂P
            + 2 * (1 / (n j : ℝ) * ∑ i : Fin (n j),
                ∫ ω, frobInner M (X j i ω) * frobInner N (X j i ω) ∂P))
          + 1 / (n j : ℝ) * ∑ i : Fin (n j), ∫ ω, frobInner N (X j i ω) ^ 2 ∂P := by
      rw [Finset.sum_congr rfl (fun i _ => hper i)]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    have hBM : 1 / (n j : ℝ) * ∑ i : Fin (n j), ∫ ω, frobInner M (X j i ω) ^ 2 ∂P
        = B M M := (hDesign j M).trans (hconj2 M).symm
    have hBN : 1 / (n j : ℝ) * ∑ i : Fin (n j), ∫ ω, frobInner N (X j i ω) ^ 2 ∂P
        = B N N := (hDesign j N).trans (hconj2 N).symm
    have hBMN : 1 / (n j : ℝ) * ∑ i : Fin (n j),
          ∫ ω, (frobInner M (X j i ω) + frobInner N (X j i ω)) ^ 2 ∂P
        = B (M + N) (M + N) := by
      change 1 / (n j : ℝ) * ∑ i : Fin (n j),
          ∫ ω, (frobInner M (X j i ω) + frobInner N (X j i ω)) ^ 2 ∂P
        = ∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
            (M + N) a b * Sigma (a, b) (a', b') * (M + N) a' b'
      rw [← (hDesign j (M + N)).trans (hconj2 (M + N)).symm]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hfrob_add]
    have hswap4 : ∀ (g : Fin m1 → Fin m2 → Fin m1 → Fin m2 → ℝ),
        (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2, g a b a' b')
          = ∑ a' : Fin m1, ∑ b' : Fin m2, ∑ a : Fin m1, ∑ b : Fin m2, g a b a' b' := by
      intro g
      calc (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2, g a b a' b')
          = ∑ a : Fin m1, ∑ a' : Fin m1, ∑ b : Fin m2, ∑ b' : Fin m2, g a b a' b' :=
            Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
        _ = ∑ a' : Fin m1, ∑ a : Fin m1, ∑ b : Fin m2, ∑ b' : Fin m2, g a b a' b' :=
            Finset.sum_comm
        _ = ∑ a' : Fin m1, ∑ a : Fin m1, ∑ b' : Fin m2, ∑ b : Fin m2, g a b a' b' :=
            Finset.sum_congr rfl (fun a' _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
        _ = ∑ a' : Fin m1, ∑ b' : Fin m2, ∑ a : Fin m1, ∑ b : Fin m2, g a b a' b' :=
            Finset.sum_congr rfl (fun a' _ => Finset.sum_comm)
    have hquad : B (M + N) (M + N) = (B M M + B M N) + B N M + B N N := by
      have hexp : ∀ (a : Fin m1) (b : Fin m2) (a' : Fin m1) (b' : Fin m2),
          (M + N) a b * Sigma (a, b) (a', b') * (M + N) a' b'
            = ((M a b * Sigma (a, b) (a', b') * M a' b'
                + M a b * Sigma (a, b) (a', b') * N a' b')
                + N a b * Sigma (a, b) (a', b') * M a' b')
              + N a b * Sigma (a, b) (a', b') * N a' b' := by
        intro a b a' b'
        have h1 : (M + N) a b = M a b + N a b := by simp
        have h2 : (M + N) a' b' = M a' b' + N a' b' := by simp
        rw [h1, h2]
        ring
      simp only [B, hexp, Finset.sum_add_distrib]
    have hBsym : B N M = B M N := by
      simp only [B]
      calc (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
              N a b * Sigma (a, b) (a', b') * M a' b')
          = ∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
              N a b * Sigma (a', b') (a, b) * M a' b' :=
            Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
              Finset.sum_congr rfl (fun a' _ => Finset.sum_congr rfl (fun b' _ => by
                rw [hsymm (a, b) (a', b')]))))
        _ = ∑ a' : Fin m1, ∑ b' : Fin m2, ∑ a : Fin m1, ∑ b : Fin m2,
              N a b * Sigma (a', b') (a, b) * M a' b' :=
            hswap4 (fun a b a' b' => N a b * Sigma (a', b') (a, b) * M a' b')
        _ = ∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
              M a b * Sigma (a, b) (a', b') * N a' b' := by
            refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
              Finset.sum_congr rfl (fun a' _ => Finset.sum_congr rfl (fun b' _ => ?_))))
            ring
    have e1 : B (M + N) (M + N)
        = (B M M + 2 * (1 / (n j : ℝ) * ∑ i : Fin (n j),
            ∫ ω, frobInner M (X j i ω) * frobInner N (X j i ω) ∂P)) + B N N := by
      rw [← hBMN, hQ, hBM, hBN]
    linarith [e1, hquad, hBsym]
  have hlin : ∀ (c : Fin T → ℝ) (M : Fin T → Matrix (Fin m1) (Fin m2) ℝ)
      (A : Matrix (Fin m1) (Fin m2) ℝ),
      ∑ j, c j * frobInner (M j) A = frobInner (∑ j, c j • M j) A := by
    intro c M A
    have h1 : ∀ j, c j * frobInner (M j) A
        = ∑ a : Fin m1, ∑ b : Fin m2, c j * (M j a b * A a b) := by
      intro j
      simp only [frobInner]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
    calc ∑ j, c j * frobInner (M j) A
        = ∑ j, ∑ a : Fin m1, ∑ b : Fin m2, c j * (M j a b * A a b) :=
          Finset.sum_congr rfl (fun j _ => h1 j)
      _ = ∑ a : Fin m1, ∑ j, ∑ b : Fin m2, c j * (M j a b * A a b) := Finset.sum_comm
      _ = ∑ a : Fin m1, ∑ b : Fin m2, ∑ j, c j * (M j a b * A a b) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ a : Fin m1, ∑ b : Fin m2, (∑ j, c j * M j a b) * A a b := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = frobInner (∑ j, c j • M j) A := by
          simp only [frobInner]
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
          have hpt : (∑ j, c j • M j) a b = ∑ j, c j * M j a b := by
            rw [hsum_apply]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp
          rw [hpt]
  have hconj1 : ∀ (ω : Ω) (a : Fin m1) (b : Fin m2),
      (∑ j : Fin T, w j • ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω)) a b
        = (∑ a' : Fin m1, ∑ b' : Fin m2,
              Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b')
          + (∑ j : Fin T, w j • DeltaMat P n Y X j ω) a b := by
    intro ω a b
    have hsa : ∀ (k : ℕ) (s : Finset (Fin k)) (g : Fin k → Matrix (Fin m1) (Fin m2) ℝ)
        (p : Fin m1) (q : Fin m2), (∑ i ∈ s, g i) p q = ∑ i ∈ s, g i p q := by
      intro k s g p q
      induction s using Finset.induction with
      | empty => simp
      | insert x s hx ih =>
          rw [Finset.sum_insert hx, Finset.sum_insert hx]
          simp [ih]
    have hMbar : ∀ (p : Fin m1) (q : Fin m2),
        (∑ j : Fin T, w j • M0 j) p q = ∑ j : Fin T, w j * M0 j p q := by
      intro p q
      rw [hsa]
      exact Finset.sum_congr rfl (fun j _ => by simp)
    have hYsamp : ∀ (j : Fin T) (i : Fin (n j)),
        ∫ ω', Y j i ω' * (X j i ω') a b ∂P
          = ∫ ω', frobInner (M0 j) (X j i ω') * (X j i ω') a b ∂P := by
      intro j i
      have hint1 : Integrable (fun ω' => frobInner (M0 j) (X j i ω') * (X j i ω') a b) P := by
        have h := hprod j i (M0 j) (fun p q => if (p, q) = (a, b) then (1 : ℝ) else 0)
        refine h.congr ?_
        filter_upwards with ω'
        rw [hE]
      have hpt : ∀ ω', Y j i ω' * (X j i ω') a b
          = frobInner (M0 j) (X j i ω') * (X j i ω') a b
            + xi j i ω' * (X j i ω') a b := by
        intro ω'
        rw [hModel j i ω']
        ring
      calc ∫ ω', Y j i ω' * (X j i ω') a b ∂P
          = ∫ ω', (frobInner (M0 j) (X j i ω') * (X j i ω') a b
              + xi j i ω' * (X j i ω') a b) ∂P := by simp only [hpt]
        _ = ∫ ω', frobInner (M0 j) (X j i ω') * (X j i ω') a b ∂P
              + ∫ ω', xi j i ω' * (X j i ω') a b ∂P := integral_add hint1 (hXiInt j i a b)
        _ = ∫ ω', frobInner (M0 j) (X j i ω') * (X j i ω') a b ∂P := by
              rw [hXiZero j i a b, add_zero]
    have hbilinE : ∀ (j : Fin T),
        (1 / (n j : ℝ)) * ∑ i : Fin (n j),
            ∫ ω', frobInner (M0 j) (X j i ω') * (X j i ω') a b ∂P
          = ∑ a' : Fin m1, ∑ b' : Fin m2, (M0 j) a' b' * Sigma (a', b') (a, b) := by
      intro j
      have hcongr : (1 / (n j : ℝ)) * ∑ i : Fin (n j),
            ∫ ω', frobInner (M0 j) (X j i ω')
              * frobInner (fun p q => if (p, q) = (a, b) then (1 : ℝ) else 0) (X j i ω') ∂P
          = (1 / (n j : ℝ)) * ∑ i : Fin (n j),
              ∫ ω', frobInner (M0 j) (X j i ω') * (X j i ω') a b ∂P := by
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hE]
      rw [← hcongr, hbilin j (M0 j) (fun p q => if (p, q) = (a, b) then (1 : ℝ) else 0),
        hcross (M0 j) (a, b)]
    have hdesign : (∑ j : Fin T, w j * ((1 / (n j : ℝ)) * ∑ i : Fin (n j),
          ∫ ω', Y j i ω' * (X j i ω') a b ∂P))
        = ∑ a' : Fin m1, ∑ b' : Fin m2,
            Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b' := by
      have hstep : (∑ j : Fin T, w j * ((1 / (n j : ℝ)) * ∑ i : Fin (n j),
            ∫ ω', Y j i ω' * (X j i ω') a b ∂P))
          = ∑ j : Fin T, w j * (∑ a' : Fin m1, ∑ b' : Fin m2,
              (M0 j) a' b' * Sigma (a', b') (a, b)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [show (∑ i : Fin (n j), ∫ ω', Y j i ω' * (X j i ω') a b ∂P)
            = ∑ i : Fin (n j),
                ∫ ω', frobInner (M0 j) (X j i ω') * (X j i ω') a b ∂P from
          Finset.sum_congr rfl (fun i _ => hYsamp j i)]
        rw [hbilinE j]
      rw [hstep]
      calc (∑ j : Fin T, w j * (∑ a' : Fin m1, ∑ b' : Fin m2,
              (M0 j) a' b' * Sigma (a', b') (a, b)))
          = ∑ j : Fin T, ∑ a' : Fin m1, ∑ b' : Fin m2,
              w j * ((M0 j) a' b' * Sigma (a', b') (a, b)) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun a' _ => ?_)
            rw [Finset.mul_sum]
        _ = ∑ a' : Fin m1, ∑ j : Fin T, ∑ b' : Fin m2,
              w j * ((M0 j) a' b' * Sigma (a', b') (a, b)) := Finset.sum_comm
        _ = ∑ a' : Fin m1, ∑ b' : Fin m2, ∑ j : Fin T,
              w j * ((M0 j) a' b' * Sigma (a', b') (a, b)) :=
            Finset.sum_congr rfl (fun a' _ => Finset.sum_comm)
        _ = ∑ a' : Fin m1, ∑ b' : Fin m2,
              Sigma (a', b') (a, b) * (∑ j : Fin T, w j * (M0 j) a' b') := by
            refine Finset.sum_congr rfl (fun a' _ => Finset.sum_congr rfl (fun b' _ => ?_))
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun j _ => by ring)
        _ = ∑ a' : Fin m1, ∑ b' : Fin m2,
              Sigma (a, b) (a', b') * (∑ j : Fin T, w j * (M0 j) a' b') := by
            refine Finset.sum_congr rfl (fun a' _ => Finset.sum_congr rfl (fun b' _ => ?_))
            rw [hsymm (a', b') (a, b)]
        _ = ∑ a' : Fin m1, ∑ b' : Fin m2,
              Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b' := by
            refine Finset.sum_congr rfl (fun a' _ => Finset.sum_congr rfl (fun b' _ => ?_))
            rw [hMbar]
    have hL : (∑ j : Fin T, w j • ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω)) a b
        = ∑ j : Fin T, w j * ((1 / (n j : ℝ)) * ∑ i : Fin (n j), Y j i ω * (X j i ω) a b) := by
      rw [hsa]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hin : (∑ i : Fin (n j), Y j i ω • X j i ω)
          = fun p q => ∑ i : Fin (n j), Y j i ω * (X j i ω) p q := by
        funext p q
        rw [hsa]
        exact Finset.sum_congr rfl (fun i _ => by simp)
      rw [hin]
      simp
    have hE' : (∑ j : Fin T, w j • DeltaMat P n Y X j ω) a b
        = ∑ j : Fin T, w j * ((1 / (n j : ℝ)) * (∑ i : Fin (n j), Y j i ω * (X j i ω) a b
            - ∑ i : Fin (n j), ∫ ω', Y j i ω' * (X j i ω') a b ∂P)) := by
      rw [hsa]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have h1 : (w j • DeltaMat P n Y X j ω) a b = w j * (DeltaMat P n Y X j ω) a b := by simp
      have hD : (DeltaMat P n Y X j ω) a b = (1 / (n j : ℝ)) * ∑ i : Fin (n j),
          (Y j i ω * (X j i ω) a b - ∫ ω', Y j i ω' * (X j i ω') a b ∂P) := rfl
      rw [h1, hD, Finset.sum_sub_distrib]
    rw [hL, hE', ← hdesign, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hconj3 : ∀ (ω : Ω) (A : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner (∑ j : Fin T, w j • ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω)) A
        = (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
              (∑ j : Fin T, w j • M0 j) a b * Sigma (a, b) (a', b') * A a' b')
          + frobInner (∑ j : Fin T, w j • DeltaMat P n Y X j ω) A := by
    intro ω A
    have h1 : ∀ (a : Fin m1) (b : Fin m2),
        (∑ a' : Fin m1, ∑ b' : Fin m2, Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b')
            * A a b
          = ∑ a' : Fin m1, ∑ b' : Fin m2,
              Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b' * A a b := by
      intro a b
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      rw [Finset.sum_mul]
    have h2 : (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
          Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b' * A a b)
        = ∑ p : Fin m1 × Fin m2, ∑ q : Fin m1 × Fin m2,
            Sigma p q * (∑ j : Fin T, w j • M0 j) q.1 q.2 * A p.1 p.2 := by
      rw [show (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
            Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b' * A a b)
          = ∑ a : Fin m1, ∑ b : Fin m2, ∑ q : Fin m1 × Fin m2,
              Sigma (a, b) q * (∑ j : Fin T, w j • M0 j) q.1 q.2 * A a b from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          (hsum_prod (fun q => Sigma (a, b) q * (∑ j : Fin T, w j • M0 j) q.1 q.2 * A a b)).symm))]
      exact (hsum_prod (fun p => ∑ q : Fin m1 × Fin m2,
        Sigma p q * (∑ j : Fin T, w j • M0 j) q.1 q.2 * A p.1 p.2)).symm
    have h3 : (∑ p : Fin m1 × Fin m2, ∑ q : Fin m1 × Fin m2,
          Sigma p q * (∑ j : Fin T, w j • M0 j) q.1 q.2 * A p.1 p.2)
        = ∑ p : Fin m1 × Fin m2, ∑ q : Fin m1 × Fin m2,
            (∑ j : Fin T, w j • M0 j) p.1 p.2 * Sigma p q * A q.1 q.2 := by
      rw [show (∑ p : Fin m1 × Fin m2, ∑ q : Fin m1 × Fin m2,
            Sigma p q * (∑ j : Fin T, w j • M0 j) q.1 q.2 * A p.1 p.2)
          = ∑ q : Fin m1 × Fin m2, ∑ p : Fin m1 × Fin m2,
            Sigma p q * (∑ j : Fin T, w j • M0 j) q.1 q.2 * A p.1 p.2 from Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_))
      rw [hsymm p q]
      ring
    have h4 : (∑ p : Fin m1 × Fin m2, ∑ q : Fin m1 × Fin m2,
          (∑ j : Fin T, w j • M0 j) p.1 p.2 * Sigma p q * A q.1 q.2)
        = ∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
            (∑ j : Fin T, w j • M0 j) a b * Sigma (a, b) (a', b') * A a' b' := by
      rw [show (∑ p : Fin m1 × Fin m2, ∑ q : Fin m1 × Fin m2,
            (∑ j : Fin T, w j • M0 j) p.1 p.2 * Sigma p q * A q.1 q.2)
          = ∑ p : Fin m1 × Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
            (∑ j : Fin T, w j • M0 j) p.1 p.2 * Sigma p (a', b') * A a' b' from
        Finset.sum_congr rfl (fun p _ =>
          hsum_prod (fun q => (∑ j : Fin T, w j • M0 j) p.1 p.2 * Sigma p q * A q.1 q.2))]
      exact hsum_prod (fun p => ∑ a' : Fin m1, ∑ b' : Fin m2,
        (∑ j : Fin T, w j • M0 j) p.1 p.2 * Sigma p (a', b') * A a' b')
    have hkey : (∑ a : Fin m1, ∑ b : Fin m2,
          (∑ a' : Fin m1, ∑ b' : Fin m2,
              Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b') * A a b)
        = ∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
            (∑ j : Fin T, w j • M0 j) a b * Sigma (a, b) (a', b') * A a' b' := by
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))]
      exact h2.trans (h3.trans h4)
    have hLHS : frobInner
          (∑ j : Fin T, w j • ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω)) A
        = ∑ a : Fin m1, ∑ b : Fin m2,
            ((∑ a' : Fin m1, ∑ b' : Fin m2,
                Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b')
              + (∑ j : Fin T, w j • DeltaMat P n Y X j ω) a b) * A a b := by
      simp only [frobInner]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [hconj1 ω a b]
    have hsplit : (∑ a : Fin m1, ∑ b : Fin m2,
            ((∑ a' : Fin m1, ∑ b' : Fin m2,
                Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b')
              + (∑ j : Fin T, w j • DeltaMat P n Y X j ω) a b) * A a b)
        = (∑ a : Fin m1, ∑ b : Fin m2,
              (∑ a' : Fin m1, ∑ b' : Fin m2,
                Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b') * A a b)
          + frobInner (∑ j : Fin T, w j • DeltaMat P n Y X j ω) A := by
      simp only [frobInner]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring
    calc frobInner
          (∑ j : Fin T, w j • ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω)) A
        = ∑ a : Fin m1, ∑ b : Fin m2,
            ((∑ a' : Fin m1, ∑ b' : Fin m2,
                Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b')
              + (∑ j : Fin T, w j • DeltaMat P n Y X j ω) a b) * A a b := hLHS
      _ = (∑ a : Fin m1, ∑ b : Fin m2,
              (∑ a' : Fin m1, ∑ b' : Fin m2,
                Sigma (a, b) (a', b') * (∑ j : Fin T, w j • M0 j) a' b') * A a b)
            + frobInner (∑ j : Fin T, w j • DeltaMat P n Y X j ω) A := hsplit
      _ = (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
              (∑ j : Fin T, w j • M0 j) a b * Sigma (a, b) (a', b') * A a' b')
            + frobInner (∑ j : Fin T, w j • DeltaMat P n Y X j ω) A := by rw [hkey]
  have hconj4 : ∀ (ω : Ω) (A : Matrix (Fin m1) (Fin m2) ℝ) (lam : ℝ),
      localObj Sigma P n Y X w lam A ω
        = secondMomentForm Sigma A
          - 2 * ((∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
                    (∑ j : Fin T, w j • M0 j) a b * Sigma (a, b) (a', b') * A a' b')
                  + frobInner (∑ j : Fin T, w j • DeltaMat P n Y X j ω) A)
          + lam * Statlib.HighDim.Vocabulary.nuclearNorm A := by
    intro ω A lam
    have hlinW : (∑ j : Fin T,
          w j * frobInner ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω) A)
        = frobInner (∑ j : Fin T,
            w j • ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω)) A :=
      hlin w (fun j => (1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω) A
    have hA : (∑ j : Fin T, w j * (secondMomentForm Sigma A
          - 2 * frobInner ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω) A))
        = secondMomentForm Sigma A
          - 2 * frobInner (∑ j : Fin T,
              w j • ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω)) A := by
      have e1 : (∑ j : Fin T, w j * (secondMomentForm Sigma A
            - 2 * frobInner ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω) A))
          = ∑ j : Fin T, (w j * secondMomentForm Sigma A
              - w j * (2 * frobInner ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω) A)) :=
        Finset.sum_congr rfl (fun j _ => by ring)
      have e2 : (∑ j : Fin T, (w j * secondMomentForm Sigma A
              - w j * (2 * frobInner ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω) A)))
          = ((∑ j : Fin T, w j) * secondMomentForm Sigma A
              - 2 * ∑ j : Fin T,
                  w j * frobInner ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω) A) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        rw [show (∑ j : Fin T,
              w j * (2 * frobInner ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω) A))
            = ∑ j : Fin T, 2 * (w j
                * frobInner ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω) A) from
          Finset.sum_congr rfl (fun j _ => by ring)]
        rw [← Finset.mul_sum]
      have e3 : ((∑ j : Fin T, w j) * secondMomentForm Sigma A
              - 2 * ∑ j : Fin T,
                  w j * frobInner ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω) A)
          = secondMomentForm Sigma A
            - 2 * frobInner (∑ j : Fin T,
                w j • ((1 / (n j : ℝ)) • ∑ i : Fin (n j), Y j i ω • X j i ω)) A := by
        rw [hw_sum, hlinW]
        ring
      exact e1.trans (e2.trans e3)
    simp only [localObj]
    rw [hA, hconj3 ω A]
  refine ⟨hconj1, hconj3, hconj2, hconj4⟩
  /- @proof-region region.target-node.session.9a6de9e5751a9da1 end -/

end Statlib.Imported

