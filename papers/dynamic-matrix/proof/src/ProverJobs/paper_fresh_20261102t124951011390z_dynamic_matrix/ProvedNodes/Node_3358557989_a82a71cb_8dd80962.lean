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
theorem statopia_math_node_3358557989_a82a71cb : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (s : Statlib.HighDim.Vocabulary.SVD A),
    Fintype.card { k : Fin (min m n) //
        0 < s.sigma (Fin.castLE (Nat.min_le_left m n) k)
          (Fin.castLE (Nat.min_le_right m n) k) } = A.rank := by
  /- @proof-region region.target-node.session.09d548985122abe8 begin -/
  intro m n A s
  obtain ⟨U, V, sigma, hU, hV, hdiag, hnonneg, hfac⟩ := s
  show Fintype.card { k : Fin (min m n) // 0 < sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) } = A.rank
  let P : Matrix (Fin m) (Fin (min m n)) ℝ := fun i k => if i = Fin.castLE (Nat.min_le_left m n) k then (1 : ℝ) else 0
  let Q : Matrix (Fin n) (Fin (min m n)) ℝ := fun j k => if j = Fin.castLE (Nat.min_le_right m n) k then (1 : ℝ) else 0
  let D : Matrix (Fin (min m n)) (Fin (min m n)) ℝ := Matrix.diagonal (fun k => sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k))
  have hP : P.transpose * P = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply]
    have htr : ∀ j : Fin m, P.transpose k j = P j k := fun j => rfl
    simp only [htr]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl]
      rw [Finset.sum_eq_single (Fin.castLE (Nat.min_le_left m n) k)]
      · simp [P]
      · intro b _ hb
        simp [P, hb]
      · intro hb
        exact absurd (Finset.mem_univ _) hb
    · rw [if_neg hkl]
      apply Finset.sum_eq_zero
      intro b _
      by_cases hb : b = Fin.castLE (Nat.min_le_left m n) k
      · subst hb
        have hne : ¬ (Fin.castLE (Nat.min_le_left m n) k = Fin.castLE (Nat.min_le_left m n) l) := by
          intro h
          exact hkl (Fin.ext (by simpa using congrArg Fin.val h))
        simp [P, hne]
      · simp [P, hb]
  have hQ : Q.transpose * Q = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply]
    have htr : ∀ j : Fin n, Q.transpose k j = Q j k := fun j => rfl
    simp only [htr]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl]
      rw [Finset.sum_eq_single (Fin.castLE (Nat.min_le_right m n) k)]
      · simp [Q]
      · intro b _ hb
        simp [Q, hb]
      · intro hb
        exact absurd (Finset.mem_univ _) hb
    · rw [if_neg hkl]
      apply Finset.sum_eq_zero
      intro b _
      by_cases hb : b = Fin.castLE (Nat.min_le_right m n) k
      · subst hb
        have hne : ¬ (Fin.castLE (Nat.min_le_right m n) k = Fin.castLE (Nat.min_le_right m n) l) := by
          intro h
          exact hkl (Fin.ext (by simpa using congrArg Fin.val h))
        simp [Q, hne]
      · simp [Q, hb]
  have hsigD : sigma = P * D * Q.transpose := by
    have hDdef : ∀ k l : Fin (min m n), D k l = if k = l then sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) else 0 := fun k l => rfl
    ext i j
    have hinner : ∀ k : Fin (min m n), (D * Q.transpose) k j =
        sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) * Q j k := by
      intro k
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single k]
      · rw [hDdef k k, if_pos rfl]
        rfl
      · intro l _ hl
        rw [hDdef k l, if_neg hl.symm]
        simp
      · intro hh
        exact absurd (Finset.mem_univ k) hh
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    have hstep : (∑ k : Fin (min m n), P i k * (D * Q.transpose) k j) =
        ∑ k : Fin (min m n), P i k * (sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) * Q j k) :=
      Finset.sum_congr rfl (fun k _ => by rw [hinner k])
    rw [hstep]
    by_cases hij : (i : ℕ) = (j : ℕ)
    · have hlt : (i : ℕ) < min m n := lt_min_iff.mpr ⟨i.isLt, hij.symm ▸ j.isLt⟩
      rw [Finset.sum_eq_single (⟨(i : ℕ), hlt⟩ : Fin (min m n))]
      · have ha : (Fin.castLE (Nat.min_le_left m n) ⟨(i : ℕ), hlt⟩ : Fin m) = i := Fin.ext rfl
        have hb : (Fin.castLE (Nat.min_le_right m n) ⟨(i : ℕ), hlt⟩ : Fin n) = j := Fin.ext hij
        have hP1 : P i ⟨(i : ℕ), hlt⟩ = 1 := by
          show (if i = Fin.castLE (Nat.min_le_left m n) ⟨(i : ℕ), hlt⟩ then (1 : ℝ) else 0) = 1
          rw [if_pos ha.symm]
        have hQ1 : Q j ⟨(i : ℕ), hlt⟩ = 1 := by
          show (if j = Fin.castLE (Nat.min_le_right m n) ⟨(i : ℕ), hlt⟩ then (1 : ℝ) else 0) = 1
          rw [if_pos hb.symm]
        have hw : sigma (Fin.castLE (Nat.min_le_left m n) ⟨(i : ℕ), hlt⟩) (Fin.castLE (Nat.min_le_right m n) ⟨(i : ℕ), hlt⟩) = sigma i j := by rw [ha, hb]
        rw [hP1, hQ1, hw]
        ring
      · intro k _ hk
        have hik : ¬ (i = Fin.castLE (Nat.min_le_left m n) k) := by
          intro h
          apply hk
          have h2 : (i : ℕ) = (k : ℕ) := by
            have h3 : (i : ℕ) = ((Fin.castLE (Nat.min_le_left m n) k : Fin m) : ℕ) := congrArg Fin.val h
            simpa using h3
          exact Fin.ext h2.symm
        simp [P, hik]
      · intro hh
        exact absurd (Finset.mem_univ _) hh
    · rw [hdiag i j hij]
      have hz : (∑ k : Fin (min m n), P i k * (sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) * Q j k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk : i = Fin.castLE (Nat.min_le_left m n) k
        · have hk2 : ¬ (j = Fin.castLE (Nat.min_le_right m n) k) := by
            intro h
            apply hij
            rw [hk, h]
            rfl
          simp [P, Q, hk, hk2]
        · simp [P, hk]
      rw [hz]
  have hsigA : sigma = U.transpose * A * V := by
    calc sigma = U.transpose * U * sigma * (V.transpose * V) := by
          rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
      _ = U.transpose * (U * sigma * V.transpose) * V := by
          simp only [Matrix.mul_assoc]
      _ = U.transpose * A * V := by rw [← hfac]
  have hAle : A.rank ≤ D.rank := by
    have h1 : A.rank ≤ sigma.rank := by
      rw [hfac]
      calc (U * sigma * V.transpose).rank = (U * (sigma * V.transpose)).rank := by rw [Matrix.mul_assoc]
        _ ≤ (sigma * V.transpose).rank := Matrix.rank_mul_le_right _ _
        _ ≤ sigma.rank := Matrix.rank_mul_le_left _ _
    have h2 : sigma.rank ≤ D.rank := by
      rw [hsigD]
      calc (P * D * Q.transpose).rank = (P * (D * Q.transpose)).rank := by rw [Matrix.mul_assoc]
        _ ≤ (D * Q.transpose).rank := Matrix.rank_mul_le_right _ _
        _ ≤ D.rank := Matrix.rank_mul_le_left _ _
    exact le_trans h1 h2
  have hDle : D.rank ≤ A.rank := by
    have hσA : sigma.rank ≤ A.rank := by
      rw [hsigA]
      calc (U.transpose * A * V).rank = (U.transpose * (A * V)).rank := by rw [Matrix.mul_assoc]
        _ ≤ (A * V).rank := Matrix.rank_mul_le_right _ _
        _ ≤ A.rank := Matrix.rank_mul_le_left _ _
    have hDσ : D.rank ≤ sigma.rank := by
      have hDform : D = P.transpose * sigma * Q := by
        rw [hsigD]
        calc D = (P.transpose * P) * D * (Q.transpose * Q) := by
              rw [hP, hQ, Matrix.one_mul, Matrix.mul_one]
          _ = P.transpose * (P * D * Q.transpose) * Q := by simp only [Matrix.mul_assoc]
      calc D.rank = (P.transpose * sigma * Q).rank := by rw [hDform]
        _ = (P.transpose * (sigma * Q)).rank := by rw [Matrix.mul_assoc]
        _ ≤ (sigma * Q).rank := Matrix.rank_mul_le_right _ _
        _ ≤ sigma.rank := Matrix.rank_mul_le_left _ _
    exact le_trans hDσ hσA
  have hDrank : D.rank = Fintype.card { k : Fin (min m n) // sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) ≠ 0 } := by
    show (Matrix.diagonal (fun k : Fin (min m n) => sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k))).rank = _
    rw [Matrix.rank_diagonal]
  have hcardeq : Fintype.card { k : Fin (min m n) // 0 < sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) } = Fintype.card { k : Fin (min m n) // sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) ≠ 0 } := by
    refine le_antisymm ?_ ?_
    · refine Fintype.card_le_of_injective (fun x : { k : Fin (min m n) // 0 < sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) } => (⟨x.1, ne_of_gt x.2⟩ : { k : Fin (min m n) // sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) ≠ 0 })) ?_
      intro a b h
      exact Subtype.ext (by simpa using congrArg (fun y : { k : Fin (min m n) // sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) ≠ 0 } => (y : Fin (min m n))) h)
    · refine Fintype.card_le_of_injective (fun x : { k : Fin (min m n) // sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) ≠ 0 } => (⟨x.1, ?_⟩ : { k : Fin (min m n) // 0 < sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) })) ?_
      · rcases lt_or_eq_of_le (hnonneg _ _) with h' | h'
        · exact h'
        · exact absurd h'.symm x.2
      · intro a b h
        exact Subtype.ext (by simpa using congrArg (fun y : { k : Fin (min m n) // 0 < sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k) } => (y : Fin (min m n))) h)
  have hAD : A.rank = D.rank := le_antisymm hAle hDle
  rw [hcardeq, ← hDrank, hAD]
  /- @proof-region region.target-node.session.09d548985122abe8 end -/

end Statlib.Imported

