import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.HighDim.CovarianceMatrix.SampleCovariance
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_360940608_79944c4e : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {Ωm : Type*} [MeasurableSpace Ωm] (P : Measure Ωm) [IsProbabilityMeasure P]
    (Om : Fin m → Fin n → Ωm → ℝ),
    (∀ ω : Ωm,
      Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)))
            (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p))).transpose
            (0 : Matrix (Fin n) (Fin n) ℝ)) =
        ∑ ij : Fin m × Fin n,
          (((Om ij.1 ij.2 ω - p) / Real.sqrt ((m : ℝ) * p)) •
            Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (matrixUnit ij.1 ij.2) (matrixUnit ij.1 ij.2).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ)))) ∧
    (∀ (i : Fin m) (j : Fin n),
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (matrixUnit i j) (matrixUnit i j).transpose
            (0 : Matrix (Fin n) (Fin n) ℝ))).transpose =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (matrixUnit i j) (matrixUnit i j).transpose
            (0 : Matrix (Fin n) (Fin n) ℝ))) ∧
    (∀ (i : Fin m) (j : Fin n),
      specNorm (Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (matrixUnit i j) (matrixUnit i j).transpose
            (0 : Matrix (Fin n) (Fin n) ℝ))) = 1) ∧
    (∀ (i : Fin m) (j : Fin n) (ω : Ωm),
      specNorm (((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) •
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (matrixUnit i j) (matrixUnit i j).transpose
              (0 : Matrix (Fin n) (Fin n) ℝ))) =
        |(Om i j ω - p) / Real.sqrt ((m : ℝ) * p)|) := by
  /- @proof-region region.target-node.session.881823fe2d44143b begin -/
  intro m n hm hn hnm p hp0 hp1 Ωm _ P _ Om
  have delta : ∀ {N : ℕ} (b : Fin N) (g : Fin N → ℝ),
      (∑ j : Fin N, g j * (if b = j then (1 : ℝ) else 0)) = g b := by
    intro N b g
    rw [← Finset.insert_erase (Finset.mem_univ b), Finset.sum_insert (by simp)]
    rw [if_pos rfl, mul_one]
    have hzero :
        (∑ x ∈ Finset.univ.erase b, g x * (if b = x then (1 : ℝ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
      rw [if_neg (fun h : b = x => hxb h.symm), mul_zero]
    rw [hzero, add_zero]
  have entry : ∀ (c : Fin m → Fin n → ℝ) (a : Fin m) (b : Fin n),
      (∑ ij : Fin m × Fin n, c ij.1 ij.2 * matrixUnit ij.1 ij.2 a b) = c a b := by
    intro c a b
    simp only [matrixUnit]
    rw [Fintype.sum_prod_type]
    have inner : ∀ i : Fin m,
        (∑ j : Fin n, c i j * (if a = i ∧ b = j then (1 : ℝ) else 0))
          = (if a = i then (1 : ℝ) else 0) * c i b := by
      intro i
      by_cases hai : a = i
      · have h1 : (∑ j : Fin n, c i j * (if b = j then (1 : ℝ) else 0)) = c i b :=
          delta b (fun j => c i j)
        have h2 : (∑ j : Fin n, c i j * (if a = i ∧ b = j then (1 : ℝ) else 0))
            = ∑ j : Fin n, c i j * (if b = j then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hai]
          simp
        rw [h2, h1, if_pos hai, one_mul]
      · have h0 : (∑ j : Fin n, c i j * (if a = i ∧ b = j then (1 : ℝ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          rw [if_neg (fun hh => hai hh.1), mul_zero]
        rw [h0, if_neg hai, zero_mul]
    calc (∑ i, ∑ j : Fin n, c i j * (if a = i ∧ b = j then (1 : ℝ) else 0))
        = ∑ i, ((if a = i then (1 : ℝ) else 0) * c i b) :=
          Finset.sum_congr rfl (fun i _ => inner i)
      _ = ∑ i, c i b * (if a = i then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = c a b := delta a (fun i => c i b)
  have step1_gen : ∀ (c : Fin m → Fin n → ℝ),
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Matrix.of c) (Matrix.of c).transpose
          (0 : Matrix (Fin n) (Fin n) ℝ))
      = ∑ ij : Fin m × Fin n, c ij.1 ij.2 •
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (matrixUnit ij.1 ij.2)
              (matrixUnit ij.1 ij.2).transpose (0 : Matrix (Fin n) (Fin n) ℝ)) := by
    intro c
    ext x y
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm x with i | j
    · rcases finSumFinEquiv.symm y with k | l
      · simp [Matrix.fromBlocks, Matrix.of_apply]
      · simpa [Matrix.fromBlocks, Matrix.of_apply] using (entry c i l).symm
    · rcases finSumFinEquiv.symm y with k | l
      · simpa [Matrix.fromBlocks, Matrix.of_apply] using (entry c k j).symm
      · simp [Matrix.fromBlocks, Matrix.of_apply]

  have step2_gen : ∀ (M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ), M.transpose = M →
      (Matrix.reindex finSumFinEquiv finSumFinEquiv M).transpose
        = Matrix.reindex finSumFinEquiv finSumFinEquiv M := by
    intro M hM
    have hkey : (Matrix.reindex finSumFinEquiv finSumFinEquiv M).transpose
        = Matrix.reindex finSumFinEquiv finSumFinEquiv M.transpose := by
      ext x y
      simp only [Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hkey, hM]
  have specEq : ∀ A : Matrix (Fin (m + n)) (Fin (m + n)) ℝ, specNorm A = ‖A‖ :=
    fun A => (Matrix.l2_opNorm_def A).symm
  have step3_gen : ∀ (i : Fin m) (j : Fin n),
      ‖Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (matrixUnit i j)
          (matrixUnit i j).transpose (0 : Matrix (Fin n) (Fin n) ℝ))‖ = 1 := by
    intro i j
    set B : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
      Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (matrixUnit i j)
        (matrixUnit i j).transpose (0 : Matrix (Fin n) (Fin n) ℝ) with hB
    set D : Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
      Matrix.reindex finSumFinEquiv finSumFinEquiv B with hD
    set blk : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
      Matrix.fromBlocks (matrixUnit i i) (0 : Matrix (Fin m) (Fin n) ℝ)
        (0 : Matrix (Fin n) (Fin m) ℝ) (matrixUnit j j) with hblk
    set v : Fin (m + n) → ℝ :=
      fun x => blk (finSumFinEquiv.symm x) (finSumFinEquiv.symm x) with hv
    have hinj : ∀ u w : Fin m ⊕ Fin n, (finSumFinEquiv u = finSumFinEquiv w) ↔ u = w := by
      intro u w
      exact ⟨fun hh => finSumFinEquiv.injective hh, fun hh => by rw [hh]⟩
    have hmii : ∀ (a a' : Fin m), a ≠ a' → matrixUnit i i a a' = 0 := by
      intro a a' h
      simp only [matrixUnit]
      exact if_neg (fun hh => h (hh.1.trans hh.2.symm))
    have hmjj : ∀ (b b' : Fin n), b ≠ b' → matrixUnit j j b b' = 0 := by
      intro b b' h
      simp only [matrixUnit]
      exact if_neg (fun hh => h (hh.1.trans hh.2.symm))
    have hblk11 : ∀ (a a' : Fin m), blk (Sum.inl a) (Sum.inl a') = matrixUnit i i a a' := by
      intro a a'
      rw [hblk]
      simp [Matrix.fromBlocks]
    have hblk12 : ∀ (a : Fin m) (b : Fin n), blk (Sum.inl a) (Sum.inr b) = 0 := by
      intro a b
      rw [hblk]
      simp [Matrix.fromBlocks]
    have hblk21 : ∀ (b : Fin n) (a : Fin m), blk (Sum.inr b) (Sum.inl a) = 0 := by
      intro b a
      rw [hblk]
      simp [Matrix.fromBlocks]
    have hblk22 : ∀ (b b' : Fin n), blk (Sum.inr b) (Sum.inr b') = matrixUnit j j b b' := by
      intro b b'
      rw [hblk]
      simp [Matrix.fromBlocks]
    have hEE : (matrixUnit i j : Matrix (Fin m) (Fin n) ℝ) * (matrixUnit i j).transpose
        = matrixUnit i i := by
      ext a a'
      simp only [Matrix.mul_apply, matrixUnit, Matrix.transpose_apply]
      by_cases ha : a = i
      · by_cases ha' : a' = i
        · have hstep : (∑ b : Fin n,
              (if a = i ∧ b = j then (1 : ℝ) else 0) * (if a' = i ∧ b = j then (1 : ℝ) else 0))
              = ∑ b : Fin n, (if b = j then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [ha, ha']
            by_cases hbj : b = j <;> simp [hbj]
          rw [hstep]
          have hsum : (∑ b : Fin n, (if b = j then (1 : ℝ) else 0)) = 1 := by
            simpa using delta j (fun _ => (1 : ℝ))
          rw [hsum, if_pos (show a = i ∧ a' = i from ⟨ha, ha'⟩)]
        · have hstep : (∑ b : Fin n,
              (if a = i ∧ b = j then (1 : ℝ) else 0) *
                (if a' = i ∧ b = j then (1 : ℝ) else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro b _
            rw [if_neg (fun h : a' = i ∧ b = j => ha' h.1), mul_zero]
          rw [hstep, if_neg (fun h : a = i ∧ a' = i => ha' h.2)]
      · have hstep : (∑ b : Fin n,
            (if a = i ∧ b = j then (1 : ℝ) else 0) *
              (if a' = i ∧ b = j then (1 : ℝ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro b _
          rw [if_neg (fun h : a = i ∧ b = j => ha h.1), zero_mul]
        rw [hstep, if_neg (fun h : a = i ∧ a' = i => ha h.1)]
    have hE'E : (matrixUnit i j).transpose * (matrixUnit i j) = matrixUnit j j := by
      ext b b'
      simp only [Matrix.mul_apply, matrixUnit, Matrix.transpose_apply]
      by_cases hb : b = j
      · by_cases hb' : b' = j
        · have hstep : (∑ a : Fin m,
              (if a = i ∧ b = j then (1 : ℝ) else 0) * (if a = i ∧ b' = j then (1 : ℝ) else 0))
              = ∑ a : Fin m, (if a = i then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hb, hb']
            by_cases hai : a = i <;> simp [hai]
          rw [hstep]
          have hsum : (∑ a : Fin m, (if a = i then (1 : ℝ) else 0)) = 1 := by
            simpa using delta i (fun _ => (1 : ℝ))
          rw [hsum, if_pos (show b = j ∧ b' = j from ⟨hb, hb'⟩)]
        · have hstep : (∑ a : Fin m,
              (if a = i ∧ b = j then (1 : ℝ) else 0) *
                (if a = i ∧ b' = j then (1 : ℝ) else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro a _
            rw [if_neg (fun h : a = i ∧ b' = j => hb' h.2), mul_zero]
          rw [hstep, if_neg (fun h : b = j ∧ b' = j => hb' h.2)]
      · have hstep : (∑ a : Fin m,
            (if a = i ∧ b = j then (1 : ℝ) else 0) *
              (if a = i ∧ b' = j then (1 : ℝ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro a _
          rw [if_neg (fun h : a = i ∧ b = j => hb h.2), zero_mul]
        rw [hstep, if_neg (fun h : b = j ∧ b' = j => hb h.1)]
    have hBB : B * B = blk := by
      rw [hB, hblk]
      have h := Matrix.fromBlocks_multiply (A := (0 : Matrix (Fin m) (Fin m) ℝ))
        (B := matrixUnit i j) (C := (matrixUnit i j).transpose)
        (D := (0 : Matrix (Fin n) (Fin n) ℝ))
        (A' := (0 : Matrix (Fin m) (Fin m) ℝ)) (B' := matrixUnit i j)
        (C' := (matrixUnit i j).transpose) (D' := (0 : Matrix (Fin n) (Fin n) ℝ))
      rw [h]
      simp [hEE, hE'E]
    have hDmul : D * D = Matrix.reindex finSumFinEquiv finSumFinEquiv (B * B) := by
      rw [hD]
      have h := Matrix.reindexLinearEquiv_mul ℝ ℝ finSumFinEquiv finSumFinEquiv finSumFinEquiv B B
      simpa only [Matrix.reindexLinearEquiv_apply] using h
    have hdiag : Matrix.reindex finSumFinEquiv finSumFinEquiv (B * B) = Matrix.diagonal v := by
      rw [hBB]
      ext x y
      obtain ⟨x', rfl⟩ := finSumFinEquiv.surjective x
      obtain ⟨y', rfl⟩ := finSumFinEquiv.surjective y
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.diagonal, Matrix.of_apply, hv]
      rcases x' with a | b
      · rcases y' with a' | b'
        · rw [hblk11 a a', hblk11 a a]
          by_cases h : a = a'
          · rw [if_pos (show finSumFinEquiv (Sum.inl a) = finSumFinEquiv (Sum.inl a')
              from by rw [h])]
            rw [h]
          · have hne : ¬ ((finSumFinEquiv (Sum.inl a : Fin m ⊕ Fin n)) =
                (finSumFinEquiv (Sum.inl a' : Fin m ⊕ Fin n))) := by
              intro hh
              have h1 : (Sum.inl a : Fin m ⊕ Fin n) = Sum.inl a' := (hinj _ _).mp hh
              cases h1
              exact h rfl
            rw [if_neg hne]
            exact hmii a a' h
        · rw [hblk12 a b']
          have hne : ¬ ((finSumFinEquiv (Sum.inl a : Fin m ⊕ Fin n)) =
                (finSumFinEquiv (Sum.inr b' : Fin m ⊕ Fin n))) := by
            intro hh
            have h1 : (Sum.inl a : Fin m ⊕ Fin n) = Sum.inr b' := (hinj _ _).mp hh
            cases h1
          rw [if_neg hne]
      · rcases y' with a' | b'
        · rw [hblk21 b a']
          have hne : ¬ ((finSumFinEquiv (Sum.inr b : Fin m ⊕ Fin n)) =
                (finSumFinEquiv (Sum.inl a' : Fin m ⊕ Fin n))) := by
            intro hh
            have h1 : (Sum.inr b : Fin m ⊕ Fin n) = Sum.inl a' := (hinj _ _).mp hh
            cases h1
          rw [if_neg hne]
        · rw [hblk22 b b', hblk22 b b]
          by_cases h : b = b'
          · rw [if_pos (show finSumFinEquiv (Sum.inr b) = finSumFinEquiv (Sum.inr b')
              from by rw [h])]
            rw [h]
          · have hne : ¬ ((finSumFinEquiv (Sum.inr b : Fin m ⊕ Fin n)) =
                (finSumFinEquiv (Sum.inr b' : Fin m ⊕ Fin n))) := by
              intro hh
              have h1 : (Sum.inr b : Fin m ⊕ Fin n) = Sum.inr b' := (hinj _ _).mp hh
              cases h1
              exact h rfl
            rw [if_neg hne]
            exact hmjj b b' h
    have hvn : ‖v‖ = 1 := by
      haveI : Nonempty (Fin (m + n)) := ⟨⟨0, by omega⟩⟩
      have hval : ∀ x : Fin (m + n), v x = 0 ∨ v x = 1 := by
        intro x
        obtain ⟨x', rfl⟩ := finSumFinEquiv.surjective x
        rw [hv]
        simp only [Equiv.symm_apply_apply]
        rcases x' with a | b
        · rw [hblk11 a a]
          by_cases hai : a = i
          · right
            simp [matrixUnit, hai]
          · left
            simp only [matrixUnit]
            exact if_neg (fun hh => hai hh.1)
        · rw [hblk22 b b]
          by_cases hbj : b = j
          · right
            simp [matrixUnit, hbj]
          · left
            simp only [matrixUnit]
            exact if_neg (fun hh => hbj hh.1)
      have hone : v (finSumFinEquiv (Sum.inl i)) = 1 := by
        rw [hv]
        simp only [Equiv.symm_apply_apply]
        rw [hblk11 i i]
        simp [matrixUnit]
      rw [Statlib.HighDim.CovarianceMatrix.pi_real_norm_eq_sup_abs v]
      refine le_antisymm ?_ ?_
      · refine (Finset.sup'_le_iff
          ⟨finSumFinEquiv (Sum.inl i), Finset.mem_univ _⟩ (fun k => |v k|)).mpr ?_
        intro x _
        rcases hval x with h0 | h1
        · rw [h0]; simp
        · rw [h1]; simp
      · refine Finset.le_sup'_of_le (fun k => |v k|)
          (Finset.mem_univ (finSumFinEquiv (Sum.inl i))) ?_
        show 1 ≤ |v (finSumFinEquiv (Sum.inl i))|
        rw [hone]
        simp

    have hDtr : D.transpose = D := by
      rw [hD]
      refine step2_gen B ?_
      rw [hB]
      exact Matrix.IsSymm.fromBlocks (by simp [Matrix.IsSymm]) rfl (by simp [Matrix.IsSymm])
    have hct : D.conjTranspose = D.transpose := by
      ext a b
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    have hprod : ‖D‖ * ‖D‖ = 1 := by
      have h1 : ‖D.conjTranspose * D‖ = ‖D‖ * ‖D‖ := Matrix.l2_opNorm_conjTranspose_mul_self D
      rw [← h1, hct, hDtr, hDmul, hdiag, Matrix.l2_opNorm_diagonal]
      exact hvn
    have hnn : 0 ≤ ‖D‖ := norm_nonneg D
    have hfac : (‖D‖ - 1) * (‖D‖ + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with hc | hc
    · linarith
    · linarith

  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω
    exact step1_gen (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p))
  · intro i j
    refine step2_gen _ ?_
    exact Matrix.IsSymm.fromBlocks (by simp [Matrix.IsSymm]) rfl (by simp [Matrix.IsSymm])
  · intro i j
    rw [specEq]
    exact step3_gen i j
  · intro i j ω
    rw [specEq, norm_smul, Real.norm_eq_abs, step3_gen i j, mul_one]
  /- @proof-region region.target-node.session.881823fe2d44143b end -/

end

end Statlib.Imported

