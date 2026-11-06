import Statlib.HighDim.SpectralPerturbation.Eigenvalues
import Statlib.HighDim.Vocabulary.Spectral
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_0834391f8cf87d4d75a2

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
theorem statopia_math_node_3763049950_70a2cee1 : ∀ (m n : ℕ) (A A' : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) (x : ℝ)
    (h : ∀ (r : Fin m) (j : Fin n), j ≠ i → A' r j = A r j),
    |((Finset.univ.filter (fun j : Fin n => svals A j ≤ x)).card : ℝ)
        - ((Finset.univ.filter (fun j : Fin n => svals A' j ≤ x)).card : ℝ)| ≤ 2 := by
  /- @proof-region region.target-node.session.8c34a5e16fae9f0b begin -/
  intro m n A A' i x h
  have hsv_nonneg : ∀ (M : Matrix (Fin m) (Fin n) ℝ) (j : Fin n), 0 ≤ svals M j :=
    fun M j => Real.sqrt_nonneg _
  by_cases hx : x < 0
  · have hfalseA : ∀ j : Fin n, ¬ (svals A j ≤ x) :=
      fun j hj => absurd hj (not_le.mpr (lt_of_lt_of_le hx (hsv_nonneg A j)))
    have hfalseA' : ∀ j : Fin n, ¬ (svals A' j ≤ x) :=
      fun j hj => absurd hj (not_le.mpr (lt_of_lt_of_le hx (hsv_nonneg A' j)))
    have h1 : (Finset.univ.filter (fun j : Fin n => svals A j ≤ x)).card = 0 := by
      rw [Finset.card_eq_zero]
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hj => absurd hj (hfalseA j), fun hj => absurd hj (by simp)⟩
    have h2 : (Finset.univ.filter (fun j : Fin n => svals A' j ≤ x)).card = 0 := by
      rw [Finset.card_eq_zero]
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hj => absurd hj (hfalseA' j), fun hj => absurd hj (by simp)⟩
    rw [h1, h2]
    simp
  · push_neg at hx
    have hsqrt_iff : ∀ {a : ℝ}, (Real.sqrt a ≤ x ↔ a ≤ x ^ 2) := by
      intro a
      rw [Real.sqrt_le_iff]
      exact ⟨fun ha => ha.2, fun ha => ⟨hx, ha⟩⟩
    have hsv_eq : ∀ (M : Matrix (Fin m) (Fin n) ℝ) (j : Fin n),
        (svals M j ≤ x) ↔
          (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues₀
            (Fin.cast (Fintype.card_fin n).symm j) ≤ x ^ 2 := by
      intro M j
      simpa [svals] using
        hsqrt_iff (a := (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues₀
          (Fin.cast (Fintype.card_fin n).symm j))
    have hsub : ∀ {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p],
        (Finset.univ.filter p).card = Fintype.card {y // p y} := by
      intro α _ p _
      rw [← Finset.card_subtype p (Finset.univ : Finset α)]
      have h : (Finset.subtype p (Finset.univ : Finset α)) = (Finset.univ : Finset {y // p y}) := by
        ext y
        simp
      rw [h, Finset.card_univ]
    have hfin : ∀ {N : ℕ} (f : Fin (Fintype.card (Fin N)) → ℝ) (c : ℝ),
        (Finset.univ.filter (fun j : Fin N => f (Fin.cast (Fintype.card_fin N).symm j) ≤ c)).card
          = (Finset.univ.filter (fun k : Fin (Fintype.card (Fin N)) => f k ≤ c)).card := by
      intro N f c
      refine Finset.card_bij
        (fun j _ => (⟨j.val, by rw [Fintype.card_fin]; exact j.isLt⟩ :
          Fin (Fintype.card (Fin N)))) ?_ ?_ ?_
      · intro j hj
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      · intro j _ j' _ hjj
        have h2 : j.val = j'.val := by simpa using hjj
        exact Fin.ext h2
      · intro k hk
        refine ⟨⟨k.val, ?_⟩, ?_, ?_⟩
        · exact lt_of_lt_of_eq k.isLt (Fintype.card_fin N)
        · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hk
        · rfl
    have hcard : ∀ (M : Matrix (Fin m) (Fin n) ℝ),
        (Finset.univ.filter (fun j : Fin n => svals M j ≤ x)).card
          = Fintype.card {k : Fin (Fintype.card (Fin n)) //
              (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues₀ k ≤ x ^ 2} := by
      intro M
      have h1 : (Finset.univ.filter (fun j : Fin n => svals M j ≤ x))
          = (Finset.univ.filter (fun j : Fin n =>
              (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues₀
                (Fin.cast (Fintype.card_fin n).symm j) ≤ x ^ 2)) := by
        apply Finset.filter_congr
        intro j _
        exact hsv_eq M j
      rw [h1,
        hfin (fun k => (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues₀ k) (x ^ 2)]
      exact hsub _
    have hbr2 : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (y : ℝ),
        Fintype.card {i : Fin n // Statlib.HighDim.Vocabulary.sortedEigenvalues B hB i ≤ y}
          = Fintype.card {i : Fin n // hB.eigenvalues i ≤ y} :=
      fun B hB y => Statlib.HighDim.SpectralPerturbation.card_sorted_le_eq_card_eigen_le B hB y
    have hbr : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (y : ℝ),
        Fintype.card {k : Fin (Fintype.card (Fin n)) // hB.eigenvalues₀ k ≤ y}
          = Fintype.card {i : Fin n // hB.eigenvalues i ≤ y} := by
      intro B hB y
      have heq : Fintype.card (Fin (Fintype.card (Fin n))) = Fintype.card (Fin n) := by
        rw [Fintype.card_fin, Fintype.card_fin]
      have hEig : ∀ i : Fin n,
          hB.eigenvalues i = hB.eigenvalues₀ ((Fintype.equivOfCardEq heq).symm i) :=
        fun i => rfl
      exact (Fintype.card_congr (Equiv.subtypeEquiv ((Fintype.equivOfCardEq heq).symm)
        (fun i => by rw [hEig i]))).symm
    have hspec := fun (B C : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (hC : C.IsHermitian)
        (y : ℝ) (hrank : (C - B).rank ≤ 2) =>
      statopia_math_node_98982382_efcf3d6b n B C hB hC y hrank
    have hrank : (A'.conjTranspose * A' - A.conjTranspose * A).rank ≤ 2 := by
      let u : Fin m → ℝ := fun r => A' r i - A r i
      let M : Matrix (Fin m) (Fin n) ℝ :=
        Matrix.vecMulVec u (fun j => if j = i then (1 : ℝ) else 0)
      have hM : A' = A + M := by
        ext r j
        rw [Matrix.add_apply]
        have hMval : M r j = u r * (if j = i then (1 : ℝ) else 0) := rfl
        rw [hMval]
        by_cases hj : j = i
        · rw [hj, if_pos rfl, mul_one]
          show A' r i = A r i + (A' r i - A r i)
          ring
        · rw [if_neg hj, mul_zero, add_zero]
          exact h r j hj
      have hdiff : A'.conjTranspose * A' - A.conjTranspose * A
          = A'.conjTranspose * M + M.conjTranspose * A := by
        simp only [hM, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
        abel
      have hMT : M.conjTranspose
          = Matrix.vecMulVec (fun j => if j = i then (1 : ℝ) else 0) u := by
        ext a b
        simp [M, Matrix.conjTranspose_apply, Matrix.vecMulVec, mul_comm]
      have h1 : (A'.conjTranspose * M).rank ≤ 1 :=
        le_trans (Matrix.rank_mul_le_right _ _)
          (Matrix.rank_vecMulVec_le u (fun j => if j = i then (1 : ℝ) else 0))
      have h2 : (M.conjTranspose * A).rank ≤ 1 := by
        have hr : (Matrix.vecMulVec (fun j => if j = i then (1 : ℝ) else 0) u).rank ≤ 1 :=
          Matrix.rank_vecMulVec_le _ _
        have hm : (Matrix.vecMulVec (fun j => if j = i then (1 : ℝ) else 0) u * A).rank
            ≤ (Matrix.vecMulVec (fun j => if j = i then (1 : ℝ) else 0) u).rank :=
          Matrix.rank_mul_le_left _ _
        rw [hMT]
        exact le_trans hm hr
      let w : Fin n → ℝ := fun r => ∑ k : Fin m, A' k r * u k
      let v : Fin n → ℝ := fun j => ∑ k : Fin m, A k j * u k
      have hAM : A'.conjTranspose * M
          = Matrix.vecMulVec w (fun j => if j = i then (1 : ℝ) else 0) := by
        ext r j
        have hl : (A'.conjTranspose * M) r j
            = ∑ k, (A' k r * u k) * (if j = i then (1 : ℝ) else 0) := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [show M k j = u k * (if j = i then (1 : ℝ) else 0) from rfl,
            Matrix.conjTranspose_apply, star_trivial]
          ring
        have hr : Matrix.vecMulVec w (fun j => if j = i then (1 : ℝ) else 0) r j
            = (∑ k, A' k r * u k) * (if j = i then (1 : ℝ) else 0) := by
          rw [show Matrix.vecMulVec w (fun j => if j = i then (1 : ℝ) else 0) r j
              = w r * (if j = i then (1 : ℝ) else 0) from rfl]
        rw [hl, hr, Finset.sum_mul]
      have hMA : M.conjTranspose * A
          = Matrix.vecMulVec (fun j => if j = i then (1 : ℝ) else 0) v := by
        ext r j
        have hl : (M.conjTranspose * A) r j
            = ∑ k, (u k * (if r = i then (1 : ℝ) else 0)) * A k j := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [show M.conjTranspose r k = star (M k r) from rfl,
            show M k r = u k * (if r = i then (1 : ℝ) else 0) from rfl, star_trivial]
        have hr : Matrix.vecMulVec (fun j => if j = i then (1 : ℝ) else 0) v r j
            = (if r = i then (1 : ℝ) else 0) * (∑ k, A k j * u k) := by
          rw [show Matrix.vecMulVec (fun j => if j = i then (1 : ℝ) else 0) v r j
              = (if r = i then (1 : ℝ) else 0) * v j from rfl]
        rw [hl, hr, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      let P : Matrix (Fin n) (Fin 2) ℝ := Matrix.of (fun (r : Fin n) (k : Fin 2) =>
        if k = 0 then w r else (if r = i then (1 : ℝ) else 0))
      let Q : Matrix (Fin 2) (Fin n) ℝ := Matrix.of (fun (k : Fin 2) (j : Fin n) =>
        if k = 0 then (if j = i then (1 : ℝ) else 0) else v j)
      have hPQ : Matrix.vecMulVec w (fun j => if j = i then (1 : ℝ) else 0)
            + Matrix.vecMulVec (fun j => if j = i then (1 : ℝ) else 0) v = P * Q := by
        ext r j
        rw [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
        simp [Matrix.vecMulVec, P, Q]
      rw [hdiff, hAM, hMA, hPQ]
      calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left _ _
        _ ≤ 2 := Matrix.rank_le_width _
    rw [hcard A, hcard A', hbr (A.conjTranspose * A), hbr (A'.conjTranspose * A')]
    exact hspec (A.conjTranspose * A) (A'.conjTranspose * A')
      (Matrix.isHermitian_conjTranspose_mul_self A)
      (Matrix.isHermitian_conjTranspose_mul_self A') (x ^ 2) hrank
  /- @proof-region region.target-node.session.8c34a5e16fae9f0b end -/

end Statlib.Imported

