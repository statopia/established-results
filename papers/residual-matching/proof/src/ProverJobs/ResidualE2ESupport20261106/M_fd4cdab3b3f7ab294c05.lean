import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_ca0a7f0c413f5098a553

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3644274559_77b175cc : ∀ (m n : ℕ),
    ∃ W : Fin m × Fin n → Matrix (Fin (m + n)) (Fin (m + n)) ℂ,
      (∀ p : Fin m × Fin n, (W p).IsHermitian) ∧
      (∀ p : Fin m × Fin n, ‖W p‖ = 1) ∧
      (∀ (p : Fin m × Fin n) (a b : Fin (m + n)), (W p) a b = 0 ∨ (W p) a b = 1) ∧
      (∀ A : Matrix (Fin m) (Fin n) ℝ,
        (∑ p : Fin m × Fin n, ((A p.1 p.2 : ℝ) : ℂ) • W p).IsHermitian ∧
        ‖∑ p : Fin m × Fin n, ((A p.1 p.2 : ℝ) : ℂ) • W p‖ = ‖A‖) := by
  /- @proof-region region.target-node.session.915e5ddec9e650c9 begin -/
  intro m n
  let dil : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun B => Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) B (Matrix.transpose B)
        (0 : Matrix (Fin n) (Fin n) ℂ))
  have hfb11 : ∀ (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ)
      (C : Matrix (Fin n) (Fin m) ℂ) (D : Matrix (Fin n) (Fin n) ℂ) (i j : Fin m),
      Matrix.fromBlocks A B C D (Sum.inl i) (Sum.inl j) = A i j := by
    intro A B C D i j
    rfl
  have hfb12 : ∀ (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ)
      (C : Matrix (Fin n) (Fin m) ℂ) (D : Matrix (Fin n) (Fin n) ℂ) (i : Fin m) (j : Fin n),
      Matrix.fromBlocks A B C D (Sum.inl i) (Sum.inr j) = B i j := by
    intro A B C D i j
    rfl
  have hfb21 : ∀ (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ)
      (C : Matrix (Fin n) (Fin m) ℂ) (D : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (j : Fin m),
      Matrix.fromBlocks A B C D (Sum.inr i) (Sum.inl j) = C i j := by
    intro A B C D i j
    rfl
  have hfb22 : ∀ (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ)
      (C : Matrix (Fin n) (Fin m) ℂ) (D : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n),
      Matrix.fromBlocks A B C D (Sum.inr i) (Sum.inr j) = D i j := by
    intro A B C D i j
    rfl
  have hsub : ∀ (M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) (a b : Fin (m + n)),
      (Matrix.reindex finSumFinEquiv finSumFinEquiv M) a b
        = M (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) := by
    intro M a b
    rw [Matrix.reindex_apply]
    rfl
  have hsingle_diag : ∀ (i : Fin m) (j : Fin n), Matrix.single i j (1 : ℂ) i j = 1 := by
    intro i j
    simp
  have hdil_def : ∀ B : Matrix (Fin m) (Fin n) ℂ,
      dil B = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) B (Matrix.transpose B)
          (0 : Matrix (Fin n) (Fin n) ℂ)) := fun B => rfl
  have hsingle01 : ∀ (i : Fin m) (j : Fin n) (a : Fin m) (b : Fin n),
      Matrix.single i j (1 : ℂ) a b = 0 ∨ Matrix.single i j (1 : ℂ) a b = 1 := by
    intro i j a b
    by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (hsingle_diag _ _)
    · by_cases h2 : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h2
        exact Or.inr (hsingle_diag _ _)
      · exact Or.inl (by simp [Matrix.single, h2])
  have hsingle_star : ∀ p : Fin m × Fin n, ∀ i j,
      Matrix.single p.1 p.2 (1 : ℂ) i j = star (Matrix.single p.1 p.2 (1 : ℂ) i j) := by
    intro p i j
    rcases hsingle01 p.1 p.2 i j with h | h
    · rw [h]; simp
    · rw [h]; simp
  have hreindex_herm : ∀ M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ,
      M.IsHermitian → (Matrix.reindex finSumFinEquiv finSumFinEquiv M).IsHermitian := by
    intro M hM
    have h : (Matrix.reindex finSumFinEquiv finSumFinEquiv M).conjTranspose
        = Matrix.reindex finSumFinEquiv finSumFinEquiv M := by
      rw [Matrix.conjTranspose_reindex, hM.eq]
    simpa only [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using h
  have hdil_herm : ∀ B : Matrix (Fin m) (Fin n) ℂ,
      (∀ i j, B i j = star (B i j)) → (dil B).IsHermitian := by
    intro B hB
    have h0m : (0 : Matrix (Fin m) (Fin m) ℂ).IsHermitian := by
      simp [Matrix.IsHermitian]
    have h0n : (0 : Matrix (Fin n) (Fin n) ℂ).IsHermitian := by
      simp [Matrix.IsHermitian]
    have hBC : B.conjTranspose = Matrix.transpose B := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
      exact (hB j i).symm
    rw [hdil_def]
    exact hreindex_herm _ (Matrix.IsHermitian.fromBlocks h0m hBC h0n)
  let W : Fin m × Fin n → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun p => dil (Matrix.single p.1 p.2 (1 : ℂ))
  have hmvapply : ∀ {ι κ : Type} [Fintype κ] (M : Matrix ι κ ℂ) (y : κ → ℂ) (a : ι),
      M.mulVec y a = ∑ b, M a b * y b := by
    intros
    rfl
  have hsumE : ∀ (f : Fin (m + n) → ℝ),
      (∑ b : Fin (m + n), f b) = ∑ c : Fin m ⊕ Fin n, f (finSumFinEquiv c) := by
    intro f
    exact (Equiv.sum_comp finSumFinEquiv f).symm
  have hsumS : ∀ (f : Fin m ⊕ Fin n → ℝ),
      (∑ c, f c) = (∑ i : Fin m, f (Sum.inl i)) + ∑ j : Fin n, f (Sum.inr j) := by
    intro f
    exact Fintype.sum_sum_type f
  have hequiv_ofLpm : ∀ (f : Fin m → ℂ),
      ((EuclideanSpace.equiv (Fin m) ℂ).symm f).ofLp = f := by
    intro f
    rfl
  have hequiv_ofLpn : ∀ (f : Fin n → ℂ),
      ((EuclideanSpace.equiv (Fin n) ℂ).symm f).ofLp = f := by
    intro f
    rfl
  have hreindex_mulVec : ∀ (M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)
      (y : Fin (m + n) → ℂ) (a : Fin m ⊕ Fin n),
      ((Matrix.reindex finSumFinEquiv finSumFinEquiv M).mulVec y) (finSumFinEquiv a)
        = (M.mulVec (fun c => y (finSumFinEquiv c))) a := by
    intro M y a
    have hL := hmvapply (Matrix.reindex finSumFinEquiv finSumFinEquiv M) y (finSumFinEquiv a)
    have hR := hmvapply M (fun c => y (finSumFinEquiv c)) a
    rw [hL, hR]
    rw [← Equiv.sum_comp finSumFinEquiv.symm (fun c => M a c * y (finSumFinEquiv c))]
    apply Finset.sum_congr rfl
    intro b _
    simp only [hsub, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  have hsplit : ∀ (x : EuclideanSpace ℂ (Fin (m + n))),
      ‖x‖ ^ 2 = ‖(EuclideanSpace.equiv (Fin m) ℂ).symm
            (fun i => x.ofLp (finSumFinEquiv (Sum.inl i)))‖ ^ 2
        + ‖(EuclideanSpace.equiv (Fin n) ℂ).symm
            (fun j => x.ofLp (finSumFinEquiv (Sum.inr j)))‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq, hsumE (fun b => ‖x.ofLp b‖ ^ 2), hsumS]
    congr 1
    · rw [EuclideanSpace.norm_sq_eq]
      simp
    · rw [EuclideanSpace.norm_sq_eq]
      simp
  have htoLpEq : ∀ (k : ℕ) (v : Fin k → ℂ),
      (EuclideanSpace.equiv (Fin k) ℂ).symm v = WithLp.toLp 2 v := by
    intro k v
    rfl
  have hblk : ∀ (B : Matrix (Fin m) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin (m + n)))
      (z₁ : Fin m → ℂ) (z₂ : Fin n → ℂ),
      x.ofLp = (fun a => Sum.elim z₁ z₂ (finSumFinEquiv.symm a)) →
      ‖WithLp.toLp 2 ((dil B).mulVec x.ofLp)‖ ^ 2
        = ‖(EuclideanSpace.equiv (Fin m) ℂ).symm (B.mulVec z₂)‖ ^ 2
          + ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((Matrix.transpose B).mulVec z₁)‖ ^ 2 := by
    intro B x z₁ z₂ hx
    rw [EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_toLp]
    rw [hsumE (fun a => ‖(dil B).mulVec x.ofLp a‖ ^ 2), hsumS]
    congr 1
    · rw [EuclideanSpace.norm_sq_eq]
      simp only [hequiv_ofLpm]
      apply Finset.sum_congr rfl
      intro i _
      have hzz : (fun c => x.ofLp (finSumFinEquiv c)) = Sum.elim z₁ z₂ := by
        funext c
        rw [hx]
        simp
      have hinr : (Sum.elim z₁ z₂) ∘ Sum.inr = z₂ := by
        funext j
        rfl
      have h1 : (dil B).mulVec x.ofLp (finSumFinEquiv (Sum.inl i)) = (B.mulVec z₂) i := by
        rw [hdil_def B, hreindex_mulVec, Matrix.fromBlocks_mulVec, hzz, hinr]
        simp [Matrix.zero_mulVec]
      rw [h1]
    · rw [EuclideanSpace.norm_sq_eq]
      simp only [hequiv_ofLpn]
      apply Finset.sum_congr rfl
      intro j _
      have hzz : (fun c => x.ofLp (finSumFinEquiv c)) = Sum.elim z₁ z₂ := by
        funext c
        rw [hx]
        simp
      have hinl : (Sum.elim z₁ z₂) ∘ Sum.inl = z₁ := by
        funext i
        rfl
      have h2 : (dil B).mulVec x.ofLp (finSumFinEquiv (Sum.inr j))
          = ((Matrix.transpose B).mulVec z₁) j := by
        rw [hdil_def B, hreindex_mulVec, Matrix.fromBlocks_mulVec, hzz, hinl]
        simp [Matrix.zero_mulVec]
      rw [h2]
  have hdil_norm : ∀ B : Matrix (Fin m) (Fin n) ℂ, (∀ i j, B i j = star (B i j)) →
      ‖dil B‖ = ‖B‖ := by
    intro B hB
    have hBt : ‖Matrix.transpose B‖ = ‖B‖ := by
      have hEq : Matrix.transpose B = B.conjTranspose := by
        ext i j
        simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply]
        exact hB j i
      rw [hEq, Matrix.l2_opNorm_conjTranspose]
    refine le_antisymm ?_ ?_
    · rw [Matrix.l2_opNorm_def]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) ?_
      intro x
      change ‖(Matrix.toEuclideanLin (dil B)) x‖ ≤ ‖B‖ * ‖x‖
      rw [Matrix.toEuclideanLin_apply]
      set z₁ : Fin m → ℂ := fun i => x.ofLp (finSumFinEquiv (Sum.inl i)) with hz₁
      set z₂ : Fin n → ℂ := fun j => x.ofLp (finSumFinEquiv (Sum.inr j)) with hz₂
      have hx : x.ofLp = (fun a => Sum.elim z₁ z₂ (finSumFinEquiv.symm a)) := by
        funext a
        rcases h : finSumFinEquiv.symm a with i | j
        · have ha : a = finSumFinEquiv (Sum.inl i) := by
            rw [← Equiv.apply_symm_apply finSumFinEquiv a, h]
          rw [ha]
          simp [hz₁]
        · have ha : a = finSumFinEquiv (Sum.inr j) := by
            rw [← Equiv.apply_symm_apply finSumFinEquiv a, h]
          rw [ha]
          simp [hz₂]
      have hnb := hblk B x z₁ z₂ hx
      have h1 : ‖(EuclideanSpace.equiv (Fin m) ℂ).symm (B.mulVec z₂)‖
          ≤ ‖B‖ * ‖(EuclideanSpace.equiv (Fin n) ℂ).symm z₂‖ := by
        have h := Matrix.l2_opNorm_mulVec B ((EuclideanSpace.equiv (Fin n) ℂ).symm z₂)
        rw [hequiv_ofLpn z₂] at h
        exact h
      have h2 : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((Matrix.transpose B).mulVec z₁)‖
          ≤ ‖B‖ * ‖(EuclideanSpace.equiv (Fin m) ℂ).symm z₁‖ := by
        have h := Matrix.l2_opNorm_mulVec (Matrix.transpose B)
          ((EuclideanSpace.equiv (Fin m) ℂ).symm z₁)
        rw [hequiv_ofLpm z₁] at h
        rw [hBt] at h
        exact h
      have hxs : ‖x‖ ^ 2 = ‖(EuclideanSpace.equiv (Fin m) ℂ).symm z₁‖ ^ 2
          + ‖(EuclideanSpace.equiv (Fin n) ℂ).symm z₂‖ ^ 2 := by
        have h := hsplit x
        rw [← hz₁, ← hz₂] at h
        exact h
      have h1'' : ‖(EuclideanSpace.equiv (Fin m) ℂ).symm (B.mulVec z₂)‖ ^ 2
          ≤ ‖B‖ ^ 2 * ‖(EuclideanSpace.equiv (Fin n) ℂ).symm z₂‖ ^ 2 := by
        have h0 := norm_nonneg ((EuclideanSpace.equiv (Fin m) ℂ).symm (B.mulVec z₂))
        have h0' := mul_nonneg (norm_nonneg B)
          (norm_nonneg ((EuclideanSpace.equiv (Fin n) ℂ).symm z₂))
        nlinarith [h1, h0, h0']
      have h2'' : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((Matrix.transpose B).mulVec z₁)‖ ^ 2
          ≤ ‖B‖ ^ 2 * ‖(EuclideanSpace.equiv (Fin m) ℂ).symm z₁‖ ^ 2 := by
        have h0 := norm_nonneg ((EuclideanSpace.equiv (Fin n) ℂ).symm ((Matrix.transpose B).mulVec z₁))
        have h0' := mul_nonneg (norm_nonneg B)
          (norm_nonneg ((EuclideanSpace.equiv (Fin m) ℂ).symm z₁))
        nlinarith [h2, h0, h0']
      have hexp : (‖B‖ * ‖x‖) ^ 2 = ‖B‖ ^ 2 * (‖(EuclideanSpace.equiv (Fin m) ℂ).symm z₁‖ ^ 2
          + ‖(EuclideanSpace.equiv (Fin n) ℂ).symm z₂‖ ^ 2) := by
        have h1 : (‖B‖ * ‖x‖) ^ 2 = ‖B‖ ^ 2 * ‖x‖ ^ 2 := by ring
        rw [h1, hxs]
      have hsq : ‖WithLp.toLp 2 ((dil B).mulVec x.ofLp)‖ ^ 2 ≤ (‖B‖ * ‖x‖) ^ 2 := by
        rw [hnb, hexp]
        nlinarith [h1'', h2'']
      have hnorm0 : (0 : ℝ) ≤ ‖WithLp.toLp 2 ((dil B).mulVec x.ofLp)‖ := norm_nonneg _
      have hc : (0 : ℝ) ≤ ‖B‖ * ‖x‖ := mul_nonneg (norm_nonneg B) (norm_nonneg x)
      nlinarith [hsq, hnorm0, hc]
    · rw [Matrix.l2_opNorm_def]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (dil B)) ?_
      intro y
      change ‖(Matrix.toEuclideanLin B) y‖ ≤ ‖dil B‖ * ‖y‖
      rw [Matrix.toEuclideanLin_apply]
      let f : Fin (m + n) → ℂ :=
        fun a => Sum.elim (fun _ => (0 : ℂ)) y.ofLp (finSumFinEquiv.symm a)
      let xbig : EuclideanSpace ℂ (Fin (m + n)) :=
        (EuclideanSpace.equiv (Fin (m + n)) ℂ).symm f
      have hx : xbig.ofLp = f := rfl
      have hnb := hblk B xbig (fun _ => (0 : ℂ)) y.ofLp hx
      have hstep := Matrix.l2_opNorm_mulVec (dil B) xbig
      rw [← htoLpEq] at hnb
      have hxs : ‖xbig‖ ^ 2 = ‖y‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [hx]
        rw [hsumE (fun a => ‖f a‖ ^ 2), hsumS]
        have h0f : (∑ i : Fin m, ‖f (finSumFinEquiv (Sum.inl i))‖ ^ 2) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          have hfi : f (finSumFinEquiv (Sum.inl i)) = 0 := by
            simp [f]
          rw [hfi, norm_zero]
          norm_num
        have h1f : (∑ j : Fin n, ‖f (finSumFinEquiv (Sum.inr j))‖ ^ 2) = ‖y‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          apply Finset.sum_congr rfl
          intro j _
          have hfj : f (finSumFinEquiv (Sum.inr j)) = y.ofLp j := by
            simp [f]
          rw [hfj]
        rw [h0f, h1f, zero_add]
      have hsq1 : ‖(EuclideanSpace.equiv (Fin (m + n)) ℂ).symm
            ((dil B).mulVec xbig.ofLp)‖ ^ 2 ≤ (‖dil B‖ * ‖xbig‖) ^ 2 := by
        have h0 := norm_nonneg ((EuclideanSpace.equiv (Fin (m + n)) ℂ).symm
          ((dil B).mulVec xbig.ofLp))
        have h0' := mul_nonneg (norm_nonneg (dil B)) (norm_nonneg xbig)
        nlinarith [hstep, h0, h0']
      have hlow : ‖(EuclideanSpace.equiv (Fin m) ℂ).symm (B.mulVec y.ofLp)‖ ^ 2
          ≤ ‖(EuclideanSpace.equiv (Fin (m + n)) ℂ).symm ((dil B).mulVec xbig.ofLp)‖ ^ 2 := by
        rw [hnb]
        have h0 := sq_nonneg ‖(EuclideanSpace.equiv (Fin n) ℂ).symm
          ((Matrix.transpose B).mulVec (fun _ => (0 : ℂ)))‖
        linarith
      have hxeq : ‖xbig‖ = ‖y‖ := by
        nlinarith [hxs, norm_nonneg xbig, norm_nonneg y]
      have hsqle : ‖(EuclideanSpace.equiv (Fin m) ℂ).symm (B.mulVec y.ofLp)‖ ^ 2
          ≤ (‖dil B‖ * ‖y‖) ^ 2 := by
        rw [hxeq] at hsq1
        linarith
      rw [← htoLpEq]
      have h0 : (0 : ℝ) ≤ ‖(EuclideanSpace.equiv (Fin m) ℂ).symm (B.mulVec y.ofLp)‖ :=
        norm_nonneg _
      have hc : (0 : ℝ) ≤ ‖dil B‖ * ‖y‖ :=
        mul_nonneg (norm_nonneg (dil B)) (norm_nonneg y)
      nlinarith [hsqle, h0, hc]
  have hsum_single : ∀ {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
      (f : ι → M) (j : ι), (∀ b, b ≠ j → f b = 0) → (∑ b, f b) = f j := by
    intro ι M _ _ _ f j hf
    exact Finset.sum_eq_single j (fun b _ hb => hf b hb)
      (fun hj => absurd (Finset.mem_univ j) hj)
  have hsingle_off : ∀ (i : Fin m) (j : Fin n) (a : Fin m) (b : Fin n),
      ¬ (a = i ∧ b = j) → Matrix.single i j (1 : ℂ) a b = 0 := by
    intro i j a b h
    by_cases h2 : i = a ∧ j = b
    · exact absurd ⟨h2.1.symm, h2.2.symm⟩ h
    · simp [Matrix.single, h2]
  have hcoord : ∀ (j : Fin n) (y : Fin n → ℂ), ‖y j‖ ^ 2 ≤ ∑ b, ‖y b‖ ^ 2 := by
    intro j y
    have h0 : ∀ b ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ ‖y b‖ ^ 2 := by
      intro b _
      positivity
    exact Finset.single_le_sum h0 (Finset.mem_univ j)
  have hmulVec_single : ∀ (i : Fin m) (j : Fin n) (y : Fin n → ℂ),
      (Matrix.single i j (1 : ℂ)).mulVec y = (fun a => if a = i then y j else 0) := by
    intro i j y
    funext a
    rw [hmvapply]
    by_cases h : a = i
    · rw [h, if_pos rfl]
      have hf : ∀ b, b ≠ j → (Matrix.single i j (1 : ℂ)) i b * y b = 0 := by
        intro b hb
        rw [hsingle_off i j i b (fun hc => hb hc.2), zero_mul]
      rw [hsum_single (fun b => (Matrix.single i j (1 : ℂ)) i b * y b) j hf, hsingle_diag,
        one_mul]
    · rw [if_neg h]
      have hf : ∀ b, b ≠ j → (Matrix.single i j (1 : ℂ)) a b * y b = 0 := by
        intro b hb
        rw [hsingle_off i j a b (fun hc => h hc.1), zero_mul]
      rw [hsum_single (fun b => (Matrix.single i j (1 : ℂ)) a b * y b) j hf]
      rw [hsingle_off i j a j (fun hc => h hc.1), zero_mul]
  have hnorm_if : ∀ (i : Fin m) (c : ℂ),
      ‖(EuclideanSpace.equiv (Fin m) ℂ).symm (fun a => if a = i then c else 0)‖ ^ 2
        = ‖c‖ ^ 2 := by
    intro i c
    rw [EuclideanSpace.norm_sq_eq, hequiv_ofLpm]
    have hsum : (∑ a : Fin m, ‖(if a = i then c else (0 : ℂ))‖ ^ 2)
        = ‖(if i = i then c else (0 : ℂ))‖ ^ 2 :=
      hsum_single (fun a => ‖(if a = i then c else (0 : ℂ))‖ ^ 2) i (by
        intro b hb
        show ‖(if b = i then c else (0 : ℂ))‖ ^ 2 = 0
        rw [if_neg hb, norm_zero]
        norm_num)
    rw [hsum, if_pos rfl]
  have hnorm_eq : ∀ (i : Fin m) (j : Fin n) (y : Fin n → ℂ),
      ‖(EuclideanSpace.equiv (Fin m) ℂ).symm ((Matrix.single i j (1 : ℂ)).mulVec y)‖ ^ 2
        = ‖y j‖ ^ 2 := by
    intro i j y
    rw [hmulVec_single]
    exact hnorm_if i (y j)
  have hnorm_eq' : ∀ (i : Fin m) (j : Fin n) (y : Fin n → ℂ),
      ‖(EuclideanSpace.equiv (Fin m) ℂ).symm ((Matrix.single i j (1 : ℂ)).mulVec y)‖
        = ‖y j‖ := by
    intro i j y
    have h := hnorm_eq i j y
    have h0 : (0 : ℝ) ≤ ‖(EuclideanSpace.equiv (Fin m) ℂ).symm
        ((Matrix.single i j (1 : ℂ)).mulVec y)‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖y j‖ := norm_nonneg _
    nlinarith [h, h0, h1]
  have hsingle_norm : ∀ (i : Fin m) (j : Fin n), ‖Matrix.single i j (1 : ℂ)‖ = 1 := by
    intro i j
    have hsingle_e : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by
      have h1 : ‖EuclideanSpace.single j (1 : ℂ)‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        have hsum : (∑ a : Fin n, ‖(EuclideanSpace.single j (1 : ℂ)).ofLp a‖ ^ 2)
            = ‖(EuclideanSpace.single j (1 : ℂ)).ofLp j‖ ^ 2 :=
          hsum_single (fun a => ‖(EuclideanSpace.single j (1 : ℂ)).ofLp a‖ ^ 2) j (by
            intro b hb
            show ‖(EuclideanSpace.single j (1 : ℂ)).ofLp b‖ ^ 2 = 0
            rw [EuclideanSpace.single_apply, if_neg hb, norm_zero]
            norm_num)
        rw [hsum, EuclideanSpace.single_apply, if_pos rfl]
        simp
      have h0 : (0 : ℝ) ≤ ‖EuclideanSpace.single j (1 : ℂ)‖ := norm_nonneg _
      nlinarith [h1, h0]
    refine le_antisymm ?_ ?_
    · rw [Matrix.l2_opNorm_def]
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro x
      change ‖(Matrix.toEuclideanLin (Matrix.single i j (1 : ℂ))) x‖ ≤ 1 * ‖x‖
      rw [Matrix.toEuclideanLin_apply]
      have h1 : ‖WithLp.toLp 2 ((Matrix.single i j (1 : ℂ)).mulVec x.ofLp)‖ ^ 2
          = ‖x.ofLp j‖ ^ 2 := by
        rw [← htoLpEq]
        rw [hnorm_eq i j x.ofLp]
      have h2 : ‖x.ofLp j‖ ^ 2 ≤ ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        exact hcoord j x.ofLp
      have h0 : (0 : ℝ) ≤ ‖WithLp.toLp 2 ((Matrix.single i j (1 : ℂ)).mulVec x.ofLp)‖ :=
        norm_nonneg _
      have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
      nlinarith [h1, h2, h0, hx0]
    · have hwit := Matrix.l2_opNorm_mulVec (Matrix.single i j (1 : ℂ))
        (EuclideanSpace.single j (1 : ℂ))
      rw [hnorm_eq' i j] at hwit
      rw [hsingle_e] at hwit
      rw [EuclideanSpace.single_apply] at hwit
      simpa using hwit
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro p
    exact hdil_herm _ (hsingle_star p)
  · intro p
    exact (hdil_norm (Matrix.single p.1 p.2 (1 : ℂ)) (hsingle_star p)).trans
      (hsingle_norm p.1 p.2)
  · intro p a b
    show dil (Matrix.single p.1 p.2 (1 : ℂ)) a b = 0
      ∨ dil (Matrix.single p.1 p.2 (1 : ℂ)) a b = 1
    rw [hdil_def, hsub]
    rcases h1 : finSumFinEquiv.symm a with i | i <;> rcases h2 : finSumFinEquiv.symm b with j | j
    · rw [hfb11]
      exact Or.inl (by simp)
    · rw [hfb12]
      exact hsingle01 p.1 p.2 i j
    · rw [hfb21, Matrix.transpose_apply]
      exact hsingle01 p.1 p.2 j i
    · rw [hfb22]
      exact Or.inl (by simp)
  · intro A
    have hstar_real : ∀ i j, ((A i j : ℝ) : ℂ) = star (((A i j : ℝ) : ℂ)) := by
      intro i j
      simp
    have hdil_sub : ∀ (M : Matrix (Fin m) (Fin n) ℂ) (a b : Fin (m + n)),
        dil M a b = (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M (Matrix.transpose M)
          (0 : Matrix (Fin n) (Fin n) ℂ)) (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) := by
      intro M a b
      rw [hdil_def, hsub]
    have hsumW : (∑ p : Fin m × Fin n, ((A p.1 p.2 : ℝ) : ℂ) • W p)
        = dil (fun i j => ((A i j : ℝ) : ℂ)) := by
      ext a b
      show (∑ p : Fin m × Fin n, (fun (x y : Fin (m + n)) =>
          ((A p.1 p.2 : ℝ) : ℂ) * W p x y)) a b
        = dil (fun i j => ((A i j : ℝ) : ℂ)) a b
      rw [Finset.sum_apply, Finset.sum_apply]
      have hWval : ∀ p : Fin m × Fin n, W p = dil (Matrix.single p.1 p.2 (1 : ℂ)) := fun p => rfl
      have hLW : ∀ p : Fin m × Fin n, ((A p.1 p.2 : ℝ) : ℂ) * (W p a b)
          = ((A p.1 p.2 : ℝ) : ℂ) * (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
              (Matrix.single p.1 p.2 (1 : ℂ)) (Matrix.transpose (Matrix.single p.1 p.2 (1 : ℂ)))
              (0 : Matrix (Fin n) (Fin n) ℂ)) (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) := by
        intro p
        rw [hWval, hdil_sub]
      rw [Finset.sum_congr rfl (fun p _ => hLW p), hdil_sub]
      rcases h1 : finSumFinEquiv.symm a with i | i <;> rcases h2 : finSumFinEquiv.symm b with j | j
      · rw [hfb11]
        simp
      · rw [hfb12]
        have hterm : ∀ p : Fin m × Fin n,
            ((A p.1 p.2 : ℝ) : ℂ) * (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
              (Matrix.single p.1 p.2 (1 : ℂ)) (Matrix.transpose (Matrix.single p.1 p.2 (1 : ℂ)))
              (0 : Matrix (Fin n) (Fin n) ℂ)) (Sum.inl i) (Sum.inr j)
            = ((A p.1 p.2 : ℝ) : ℂ) * ((Matrix.single p.1 p.2 (1 : ℂ)) i j) := by
          intro p
          rw [hfb12]
        rw [Finset.sum_congr rfl (fun p _ => hterm p)]
        have hzero : ∀ (q : Fin m × Fin n), q ≠ (i, j) →
            ((A q.1 q.2 : ℝ) : ℂ) * (Matrix.single q.1 q.2 (1 : ℂ)) i j = 0 := by
          intro q hq
          have hoff : ¬ ((i : Fin m) = q.1 ∧ (j : Fin n) = q.2) := by
            rintro ⟨rfl, rfl⟩
            exact hq rfl
          rw [hsingle_off q.1 q.2 i j hoff, mul_zero]
        rw [hsum_single (fun q => ((A q.1 q.2 : ℝ) : ℂ) * (Matrix.single q.1 q.2 (1 : ℂ)) i j)
          (i, j) hzero]
        show ((A i j : ℝ) : ℂ) * (Matrix.single i j (1 : ℂ)) i j = ((A i j : ℝ) : ℂ)
        rw [hsingle_diag, mul_one]
      · rw [hfb21, Matrix.transpose_apply]
        have hterm : ∀ p : Fin m × Fin n,
            ((A p.1 p.2 : ℝ) : ℂ) * (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
              (Matrix.single p.1 p.2 (1 : ℂ)) (Matrix.transpose (Matrix.single p.1 p.2 (1 : ℂ)))
              (0 : Matrix (Fin n) (Fin n) ℂ)) (Sum.inr i) (Sum.inl j)
            = ((A p.1 p.2 : ℝ) : ℂ) * ((Matrix.single p.1 p.2 (1 : ℂ)) j i) := by
          intro p
          rw [hfb21, Matrix.transpose_apply]
        rw [Finset.sum_congr rfl (fun p _ => hterm p)]
        have hzero : ∀ (q : Fin m × Fin n), q ≠ (j, i) →
            ((A q.1 q.2 : ℝ) : ℂ) * (Matrix.single q.1 q.2 (1 : ℂ)) j i = 0 := by
          intro q hq
          have hoff : ¬ ((j : Fin m) = q.1 ∧ (i : Fin n) = q.2) := by
            rintro ⟨rfl, rfl⟩
            exact hq rfl
          rw [hsingle_off q.1 q.2 j i hoff, mul_zero]
        rw [hsum_single (fun q => ((A q.1 q.2 : ℝ) : ℂ) * (Matrix.single q.1 q.2 (1 : ℂ)) j i)
          (j, i) hzero]
        show ((A j i : ℝ) : ℂ) * (Matrix.single j i (1 : ℂ)) j i = ((A j i : ℝ) : ℂ)
        rw [hsingle_diag, mul_one]
      · rw [hfb22]
        simp
    constructor
    · rw [hsumW]
      exact hdil_herm _ hstar_real
    · rw [hsumW]
      exact (hdil_norm (fun i j => ((A i j : ℝ) : ℂ)) hstar_real).trans
        (statopia_math_node_1595882321_18775fcf m n A)
  /- @proof-region region.target-node.session.915e5ddec9e650c9 end -/

end Statlib.Imported

