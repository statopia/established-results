import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2447966418_633b2e4d : ∀ (m n : ℕ) (hm : 16 ≤ m)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAmeas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => A ω i j)
    (hAint : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => A ω i j) μ)
    (hAmean : ∀ (i : Fin m) (j : Fin n), ∫ ω, A ω i j ∂μ = 0)
    (hAcov : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      ∫ ω, A ω i j * A ω k l ∂μ = if (i, j) = (k, l) then 1 / (m : ℝ) else 0)
    (hAprod : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      Integrable (fun ω => A ω i j * A ω k l) μ),
    sSup {y : ℝ | ∃ v w : Fin (m + n) → ℝ,
      (∑ a : Fin (m + n), (v a) ^ 2 = 1 ∧ ∑ b : Fin (m + n), (w b) ^ 2 = 1) ∧
      y = Real.sqrt (∫ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
        (v a : ℂ) *
          ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
              (Matrix.map (A ω) Complex.ofReal)
              (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
              (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
            finSumFinEquiv.symm finSumFinEquiv.symm) a b *
          (w b : ℂ)‖ ^ 2 ∂μ)} ≤
      2 / Real.sqrt (m : ℝ) := by
  /- @proof-region region.target-node.session.925f2020be34c9d2 begin -/
  intro m n hm Ω _ μ _ A hAmeas hAint hAmean hAcov hAprod
  refine Real.sSup_le ?_ ?_
  · rintro y ⟨v, w, ⟨hv, hw⟩, rfl⟩
    let D : Ω → Matrix (Fin (m + n)) (Fin (m + n)) ℂ := fun ω =>
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
        (Matrix.map (A ω) Complex.ofReal)
        (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
        (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    let bb : Fin m → Fin n → ℝ := fun i j =>
      v (finSumFinEquiv (Sum.inl i)) * w (finSumFinEquiv (Sum.inr j)) +
        w (finSumFinEquiv (Sum.inl i)) * v (finSumFinEquiv (Sum.inr j))
    let T : Ω → ℝ := fun ω => ∑ p : Fin m × Fin n, A ω p.1 p.2 * bb p.1 p.2
    change Real.sqrt (∫ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
        (v a : ℂ) * D ω a b * (w b : ℂ)‖ ^ 2 ∂μ) ≤ 2 / Real.sqrt (m : ℝ)
    have hreidx : ∀ {M : Type 0} [AddCommMonoid M] (f : Fin (m + n) → M),
        (∑ x : Fin m ⊕ Fin n, f (finSumFinEquiv x)) = ∑ a : Fin (m + n), f a := by
      intro M _ f
      refine Finset.sum_bij (fun x (_ : x ∈ Finset.univ) => finSumFinEquiv x) ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_univ _
      · intro x₁ _ x₂ _ h
        exact finSumFinEquiv.injective h
      · intro b _
        exact ⟨finSumFinEquiv.symm b, Finset.mem_univ _, finSumFinEquiv.apply_symm_apply b⟩
      · intro x _
        rfl
    have hsplit : ∀ {M : Type 0} [AddCommMonoid M] (g : Fin m ⊕ Fin n → M),
        (∑ x : Fin m ⊕ Fin n, g x) = (∑ i : Fin m, g (Sum.inl i)) + (∑ j : Fin n, g (Sum.inr j)) := by
      intro M _ g
      exact Fintype.sum_sum_type g
    have hnorm : ∀ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n), (v a : ℂ) * D ω a b * (w b : ℂ)‖ ^ 2 = (T ω) ^ 2 := by
      intro ω
      let B : Matrix (Fin m) (Fin n) ℂ := Matrix.map (A ω) Complex.ofReal
      let F : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
        Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) B (Matrix.transpose B)
          (0 : Matrix (Fin n) (Fin n) ℂ)
      let vv : Fin m ⊕ Fin n → ℂ := fun x => (v (finSumFinEquiv x) : ℂ)
      let wv : Fin m ⊕ Fin n → ℂ := fun y => (w (finSumFinEquiv y) : ℂ)
      have hBval : ∀ (i : Fin m) (j : Fin n), B i j = ((A ω i j : ℝ) : ℂ) := fun i j => rfl
      have hF11 : ∀ (i k : Fin m), F (Sum.inl i) (Sum.inl k) = 0 := fun i k => rfl
      have hF22 : ∀ (j l : Fin n), F (Sum.inr j) (Sum.inr l) = 0 := fun j l => rfl
      have hF12 : ∀ (i : Fin m) (j : Fin n), F (Sum.inl i) (Sum.inr j) = B i j := fun i j => rfl
      have hF21 : ∀ (j : Fin n) (i : Fin m), F (Sum.inr j) (Sum.inl i) = B i j := fun j i => rfl
      have hD : ∀ x y : Fin m ⊕ Fin n, D ω (finSumFinEquiv x) (finSumFinEquiv y) = F x y := by
        intro x y
        have hDv : D ω = (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
            (Matrix.map (A ω) Complex.ofReal)
            (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
            (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
        have hFv : F = (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
            (Matrix.map (A ω) Complex.ofReal)
            (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
            (0 : Matrix (Fin n) (Fin n) ℂ)) := rfl
        simp only [hDv, hFv, Matrix.submatrix_apply, Equiv.symm_apply_apply]
      have hdbl : ∀ (G : Fin (m + n) → Fin (m + n) → ℂ),
          (∑ a : Fin (m + n), ∑ b : Fin (m + n), G a b)
            = ∑ x : Fin m ⊕ Fin n, ∑ y : Fin m ⊕ Fin n,
                G (finSumFinEquiv x) (finSumFinEquiv y) := by
        intro G
        rw [← hreidx (M := ℂ) (fun a => ∑ b : Fin (m + n), G a b)]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        exact (hreidx (M := ℂ) (fun b => G (finSumFinEquiv x) b)).symm
      have h4 : ∀ (G : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℂ),
          (∑ x : Fin m ⊕ Fin n, ∑ y : Fin m ⊕ Fin n, G x y)
            = ((∑ i : Fin m, ∑ k : Fin m, G (Sum.inl i) (Sum.inl k))
                + (∑ i : Fin m, ∑ l : Fin n, G (Sum.inl i) (Sum.inr l)))
              + ((∑ j : Fin n, ∑ k : Fin m, G (Sum.inr j) (Sum.inl k))
                + (∑ j : Fin n, ∑ l : Fin n, G (Sum.inr j) (Sum.inr l))) := by
        intro G
        rw [hsplit (M := ℂ) (fun x => ∑ y : Fin m ⊕ Fin n, G x y)]
        congr 1
        · rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact hsplit (M := ℂ) (fun y => G (Sum.inl i) y)
        · rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          exact hsplit (M := ℂ) (fun y => G (Sum.inr j) y)
      have h2 : (∑ x : Fin m ⊕ Fin n, ∑ y : Fin m ⊕ Fin n,
            (v (finSumFinEquiv x) : ℂ) * D ω (finSumFinEquiv x) (finSumFinEquiv y) *
              (w (finSumFinEquiv y) : ℂ))
          = ∑ x : Fin m ⊕ Fin n, ∑ y : Fin m ⊕ Fin n, vv x * F x y * wv y := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        simp only [hD x y, vv, wv]
      have hz1 : (∑ i : Fin m, ∑ k : Fin m,
          vv (Sum.inl i) * F (Sum.inl i) (Sum.inl k) * wv (Sum.inl k)) = 0 := by
        simp [hF11]
      have hz2 : (∑ j : Fin n, ∑ l : Fin n,
          vv (Sum.inr j) * F (Sum.inr j) (Sum.inr l) * wv (Sum.inr l)) = 0 := by
        simp [hF22]
      have hb12 : (∑ i : Fin m, ∑ l : Fin n,
            vv (Sum.inl i) * F (Sum.inl i) (Sum.inr l) * wv (Sum.inr l))
          = ∑ i : Fin m, ∑ j : Fin n, vv (Sum.inl i) * B i j * wv (Sum.inr j) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
        simp only [hF12 i l]
      have hb21 : (∑ j : Fin n, ∑ k : Fin m,
            vv (Sum.inr j) * F (Sum.inr j) (Sum.inl k) * wv (Sum.inl k))
          = ∑ i : Fin m, ∑ j : Fin n, vv (Sum.inr j) * B i j * wv (Sum.inl i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
        simp only [hF21 j k]
      have hcomb : ((∑ i : Fin m, ∑ j : Fin n, vv (Sum.inl i) * B i j * wv (Sum.inr j))
            + (∑ i : Fin m, ∑ j : Fin n, vv (Sum.inr j) * B i j * wv (Sum.inl i)))
          = ∑ i : Fin m, ∑ j : Fin n,
              (vv (Sum.inl i) * B i j * wv (Sum.inr j) + vv (Sum.inr j) * B i j * wv (Sum.inl i)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact Finset.sum_add_distrib.symm
      have hterm : ∀ (i : Fin m) (j : Fin n),
          (vv (Sum.inl i) * B i j * wv (Sum.inr j) + vv (Sum.inr j) * B i j * wv (Sum.inl i))
            = ((A ω i j * bb i j : ℝ) : ℂ) := by
        intro i j
        have e : vv (Sum.inl i) * B i j * wv (Sum.inr j) + vv (Sum.inr j) * B i j * wv (Sum.inl i)
            = (((v (finSumFinEquiv (Sum.inl i)) * A ω i j * w (finSumFinEquiv (Sum.inr j))
                + v (finSumFinEquiv (Sum.inr j)) * A ω i j *
                  w (finSumFinEquiv (Sum.inl i))) : ℝ) : ℂ) := by
          simp only [vv, wv, hBval i j, ← Complex.ofReal_mul, ← Complex.ofReal_add]
        rw [e]
        congr 1
        simp only [bb]
        ring
      have hstep : (∑ i : Fin m, ∑ j : Fin n,
            (vv (Sum.inl i) * B i j * wv (Sum.inr j) + vv (Sum.inr j) * B i j * wv (Sum.inl i)))
          = ∑ i : Fin m, ∑ j : Fin n, ((A ω i j * bb i j : ℝ) : ℂ) := by
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))
      have hcast : (∑ i : Fin m, ∑ j : Fin n, ((A ω i j * bb i j : ℝ) : ℂ))
          = ((∑ i : Fin m, ∑ j : Fin n, A ω i j * bb i j : ℝ) : ℂ) := by
        symm
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Complex.ofReal_sum]
      have hS : (∑ a : Fin (m + n), ∑ b : Fin (m + n), (v a : ℂ) * D ω a b * (w b : ℂ))
          = ((∑ p : Fin m × Fin n, A ω p.1 p.2 * bb p.1 p.2 : ℝ) : ℂ) := by
        rw [hdbl (fun a b => (v a : ℂ) * D ω a b * (w b : ℂ))]
        rw [h2]
        rw [h4 (fun x y => vv x * F x y * wv y)]
        rw [hz1, hz2, hb12, hb21]
        simp only [zero_add, add_zero]
        rw [hcomb, hstep, hcast]
        rw [Fintype.sum_prod_type]
      rw [hS, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      have hTv : T ω = ∑ p : Fin m × Fin n, A ω p.1 p.2 * bb p.1 p.2 := rfl
      rw [hTv]
      ring
    have hInt : ∫ ω, (T ω) ^ 2 ∂μ = (1 / (m : ℝ)) * ∑ p : Fin m × Fin n, (bb p.1 p.2) ^ 2 := by
      let Fr : Fin m × Fin n → Ω → ℝ := fun p ω => A ω p.1 p.2 * bb p.1 p.2
      have hsq : ∀ ω, (T ω) ^ 2 = ∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n, Fr p ω * Fr q ω := by
        intro ω
        have hT : T ω = ∑ p : Fin m × Fin n, Fr p ω := rfl
        rw [hT, pow_two, Finset.sum_mul_sum]
      have hint : ∀ p q : Fin m × Fin n, Integrable (fun ω => Fr p ω * Fr q ω) μ := by
        intro p q
        have h : (fun ω => Fr p ω * Fr q ω)
            = (fun ω => (bb p.1 p.2 * bb q.1 q.2) * (A ω p.1 p.2 * A ω q.1 q.2)) := by
          funext ω
          simp only [Fr]
          ring
        rw [h]
        exact (hAprod p.1 p.2 q.1 q.2).const_mul (bb p.1 p.2 * bb q.1 q.2)
      have hval : ∀ p q : Fin m × Fin n, ∫ ω, Fr p ω * Fr q ω ∂μ
          = (bb p.1 p.2 * bb q.1 q.2) *
              (if (p.1, p.2) = (q.1, q.2) then 1 / (m : ℝ) else 0) := by
        intro p q
        have h : (fun ω => Fr p ω * Fr q ω)
            = (fun ω => (A ω p.1 p.2 * A ω q.1 q.2) * (bb p.1 p.2 * bb q.1 q.2)) := by
          funext ω
          simp only [Fr]
          ring
        rw [h, MeasureTheory.integral_mul_const, hAcov p.1 p.2 q.1 q.2, mul_comm]
      have hcol : ∀ p : Fin m × Fin n,
          (∑ q : Fin m × Fin n,
              (bb p.1 p.2 * bb q.1 q.2) *
                (if (p.1, p.2) = (q.1, q.2) then 1 / (m : ℝ) else 0))
            = (bb p.1 p.2 * bb p.1 p.2) * (1 / (m : ℝ)) := by
        intro p
        have h1 : (∑ q : Fin m × Fin n,
              (bb p.1 p.2 * bb q.1 q.2) *
                (if (p.1, p.2) = (q.1, q.2) then 1 / (m : ℝ) else 0))
            = (bb p.1 p.2 * bb p.1 p.2) *
                (if (p.1, p.2) = (p.1, p.2) then 1 / (m : ℝ) else 0) := by
          refine Finset.sum_eq_single p ?_ ?_
          · intro q _ hq
            rw [if_neg (fun hh => hq hh.symm)]
            ring
          · intro hp
            exact absurd (Finset.mem_univ p) hp
        rw [h1, if_pos rfl]
      have hstep1 : ∫ ω, ∑ p : Fin m × Fin n, (∑ q : Fin m × Fin n, Fr p ω * Fr q ω) ∂μ
          = ∑ p : Fin m × Fin n, ∫ ω, (∑ q : Fin m × Fin n, Fr p ω * Fr q ω) ∂μ := by
        exact MeasureTheory.integral_finset_sum Finset.univ
          (f := fun p ω => ∑ q : Fin m × Fin n, Fr p ω * Fr q ω)
          (fun p _ => MeasureTheory.integrable_finset_sum Finset.univ
            (f := fun q ω => Fr p ω * Fr q ω) (fun q _ => hint p q))
      have hstep2 : (∑ p : Fin m × Fin n,
            ∫ ω, (∑ q : Fin m × Fin n, Fr p ω * Fr q ω) ∂μ)
          = ∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n, ∫ ω, Fr p ω * Fr q ω ∂μ := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        exact MeasureTheory.integral_finset_sum Finset.univ
          (f := fun q ω => Fr p ω * Fr q ω) (fun q _ => hint p q)
      have hstep3 : (∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n, ∫ ω, Fr p ω * Fr q ω ∂μ)
          = ∑ p : Fin m × Fin n, (bb p.1 p.2 * bb p.1 p.2) * (1 / (m : ℝ)) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        have h2 : (∑ q : Fin m × Fin n, ∫ ω, Fr p ω * Fr q ω ∂μ)
            = ∑ q : Fin m × Fin n,
                (bb p.1 p.2 * bb q.1 q.2) *
                  (if (p.1, p.2) = (q.1, q.2) then 1 / (m : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          exact hval p q
        rw [h2, hcol p]
      have hfin : (∑ p : Fin m × Fin n, (bb p.1 p.2 * bb p.1 p.2) * (1 / (m : ℝ)))
          = (1 / (m : ℝ)) * ∑ p : Fin m × Fin n, (bb p.1 p.2) ^ 2 := by
        rw [← Finset.sum_mul]
        have hsq2 : (∑ p : Fin m × Fin n, bb p.1 p.2 * bb p.1 p.2)
            = ∑ p : Fin m × Fin n, (bb p.1 p.2) ^ 2 := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [pow_two]
        rw [hsq2]
        ring
      simp only [hsq]
      rw [hstep1, hstep2, hstep3, hfin]
    have hbb : ∑ p : Fin m × Fin n, (bb p.1 p.2) ^ 2 ≤ 2 := by
      have hpt : ∀ p : Fin m × Fin n,
          (bb p.1 p.2) ^ 2 ≤
            2 * ((v (finSumFinEquiv (Sum.inl p.1))) ^ 2 * (w (finSumFinEquiv (Sum.inr p.2))) ^ 2)
              + 2 * ((w (finSumFinEquiv (Sum.inl p.1))) ^ 2 * (v (finSumFinEquiv (Sum.inr p.2))) ^ 2) := by
        intro p
        change (v (finSumFinEquiv (Sum.inl p.1)) * w (finSumFinEquiv (Sum.inr p.2))
            + w (finSumFinEquiv (Sum.inl p.1)) * v (finSumFinEquiv (Sum.inr p.2))) ^ 2 ≤
          2 * ((v (finSumFinEquiv (Sum.inl p.1))) ^ 2 * (w (finSumFinEquiv (Sum.inr p.2))) ^ 2)
            + 2 * ((w (finSumFinEquiv (Sum.inl p.1))) ^ 2 * (v (finSumFinEquiv (Sum.inr p.2))) ^ 2)
        nlinarith [sq_nonneg (v (finSumFinEquiv (Sum.inl p.1)) * w (finSumFinEquiv (Sum.inr p.2))
            - w (finSumFinEquiv (Sum.inl p.1)) * v (finSumFinEquiv (Sum.inr p.2)))]
      calc ∑ p : Fin m × Fin n, (bb p.1 p.2) ^ 2
          ≤ ∑ p : Fin m × Fin n,
              (2 * ((v (finSumFinEquiv (Sum.inl p.1))) ^ 2 * (w (finSumFinEquiv (Sum.inr p.2))) ^ 2)
                + 2 * ((w (finSumFinEquiv (Sum.inl p.1))) ^ 2 * (v (finSumFinEquiv (Sum.inr p.2))) ^ 2)) :=
            Finset.sum_le_sum (fun p _ => hpt p)
        _ = 2 * ((∑ i : Fin m, (v (finSumFinEquiv (Sum.inl i))) ^ 2)
                * (∑ j : Fin n, (w (finSumFinEquiv (Sum.inr j))) ^ 2))
              + 2 * ((∑ i : Fin m, (w (finSumFinEquiv (Sum.inl i))) ^ 2)
                * (∑ j : Fin n, (v (finSumFinEquiv (Sum.inr j))) ^ 2)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              Fintype.sum_prod_type, Fintype.sum_prod_type]
            dsimp only
            rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
        _ ≤ 2 := by
            set Sv1 : ℝ := ∑ i : Fin m, (v (finSumFinEquiv (Sum.inl i))) ^ 2 with hSv1
            set Sv2 : ℝ := ∑ j : Fin n, (v (finSumFinEquiv (Sum.inr j))) ^ 2 with hSv2
            set Sw1 : ℝ := ∑ i : Fin m, (w (finSumFinEquiv (Sum.inl i))) ^ 2 with hSw1
            set Sw2 : ℝ := ∑ j : Fin n, (w (finSumFinEquiv (Sum.inr j))) ^ 2 with hSw2
            have hv1 : 0 ≤ Sv1 := by
              rw [hSv1]
              exact Finset.sum_nonneg (fun i _ => sq_nonneg (v (finSumFinEquiv (Sum.inl i))))
            have hv2 : 0 ≤ Sv2 := by
              rw [hSv2]
              exact Finset.sum_nonneg (fun j _ => sq_nonneg (v (finSumFinEquiv (Sum.inr j))))
            have hw1 : 0 ≤ Sw1 := by
              rw [hSw1]
              exact Finset.sum_nonneg (fun i _ => sq_nonneg (w (finSumFinEquiv (Sum.inl i))))
            have hw2 : 0 ≤ Sw2 := by
              rw [hSw2]
              exact Finset.sum_nonneg (fun j _ => sq_nonneg (w (finSumFinEquiv (Sum.inr j))))
            have hSv : Sv1 + Sv2 = 1 := by
              rw [hSv1, hSv2, ← hsplit (M := ℝ) (fun x => (v (finSumFinEquiv x)) ^ 2),
                hreidx (M := ℝ) (fun a => (v a) ^ 2)]
              exact hv
            have hSw : Sw1 + Sw2 = 1 := by
              rw [hSw1, hSw2, ← hsplit (M := ℝ) (fun x => (w (finSumFinEquiv x)) ^ 2),
                hreidx (M := ℝ) (fun a => (w a) ^ 2)]
              exact hw
            have e1 : Sv2 = 1 - Sv1 := by linarith
            have e2 : Sw2 = 1 - Sw1 := by linarith
            have hb1 : 0 ≤ Sv1 * Sw1 := mul_nonneg hv1 hw1
            have hb2 : 0 ≤ (1 - Sv1) * (1 - Sw1) := mul_nonneg (by linarith) (by linarith)
            rw [e1, e2]
            nlinarith [hb1, hb2]
    have hm1 : (0 : ℝ) < (m : ℝ) := by
      have h : (0 : ℕ) < m := by omega
      exact_mod_cast h
    have hle : ∫ ω, (T ω) ^ 2 ∂μ ≤ 4 / (m : ℝ) := by
      rw [hInt]
      have h1 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
      have h2 : (1 / (m : ℝ)) * (∑ p : Fin m × Fin n, (bb p.1 p.2) ^ 2) ≤ (1 / (m : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hbb h1
      have h3 : (1 / (m : ℝ)) * 2 ≤ 4 / (m : ℝ) := by
        have key : (4 : ℝ) / (m : ℝ) - (1 / (m : ℝ)) * 2 = 2 / (m : ℝ) := by
          have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hm1
          field_simp
          ring
        have hnn : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
        linarith
      linarith
    simp only [hnorm]
    calc Real.sqrt (∫ ω, (T ω) ^ 2 ∂μ) ≤ Real.sqrt (4 / (m : ℝ)) := Real.sqrt_le_sqrt hle
      _ = 2 / Real.sqrt (m : ℝ) := by
        have hsq : (2 / Real.sqrt (m : ℝ)) ^ 2 = 4 / (m : ℝ) := by
          rw [div_pow, Real.sq_sqrt (le_of_lt hm1)]
          norm_num
        rw [← hsq, Real.sqrt_sq (by positivity)]
  · positivity
  /- @proof-region region.target-node.session.925f2020be34c9d2 end -/

end Statlib.Imported

