import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
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
theorem statopia_math_node_3825179525_37ca31cf : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (s : Statlib.HighDim.Vocabulary.SVD A)
    (t : Statlib.HighDim.Vocabulary.SVD
      ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU s *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s)) * A *
        (1 - Statlib.HighDim.MatrixAnalysis.svdPosV s *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s)))),
    Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
        Statlib.HighDim.MatrixAnalysis.svdPosU s = 1 ∧
    Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s) *
        Statlib.HighDim.MatrixAnalysis.svdPosV s = 1 ∧
    Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
        (Statlib.HighDim.MatrixAnalysis.svdPosU t *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV t)) = 0 ∧
    (Statlib.HighDim.MatrixAnalysis.svdPosU t *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV t)) *
        Statlib.HighDim.MatrixAnalysis.svdPosV s = 0 := by
  /- @proof-region region.target-node.session.b1c0eea73a4b0c7d begin -/
  intro m n A s t
  have hsvdU : Statlib.HighDim.MatrixAnalysis.svdPosU s =
      s.U.submatrix id (fun k => Fin.castLE (min_le_left m n) k.val) := by
    simp only [Statlib.HighDim.MatrixAnalysis.svdPosU]
  have hsvdV : Statlib.HighDim.MatrixAnalysis.svdPosV s =
      s.V.submatrix id (fun k => Fin.castLE (min_le_right m n) k.val) := by
    simp only [Statlib.HighDim.MatrixAnalysis.svdPosV]
  have hUU : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
      Statlib.HighDim.MatrixAnalysis.svdPosU s = 1 := by
    rw [hsvdU]
    have hkey : ∀ x y : Fin m, (∑ k : Fin m, s.U k x * s.U k y) = (if x = y then (1 : ℝ) else 0) := by
      intro x y
      have h1 : (∑ k : Fin m, s.U k x * s.U k y) = (s.U.transpose * s.U) x y := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [Matrix.transpose_apply]
      rw [h1, s.hU_orth, Matrix.one_apply]
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    rw [hkey]
    by_cases hab : a = b
    · rw [hab]; simp
    · have hne : ¬ (Fin.castLE (min_le_left m n) a.val = Fin.castLE (min_le_left m n) b.val) := by
        intro h
        apply hab
        have hv : a.val.val = b.val.val := by
          have hh := congrArg Fin.val h
          simpa using hh
        exact Subtype.ext (Fin.ext hv)
      rw [if_neg hne, if_neg hab]
  have hVV : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s) *
      Statlib.HighDim.MatrixAnalysis.svdPosV s = 1 := by
    rw [hsvdV]
    have hkeyV : ∀ x y : Fin n, (∑ k : Fin n, s.V k x * s.V k y) = (if x = y then (1 : ℝ) else 0) := by
      intro x y
      have h1 : (∑ k : Fin n, s.V k x * s.V k y) = (s.V.transpose * s.V) x y := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [Matrix.transpose_apply]
      rw [h1, s.hV_orth, Matrix.one_apply]
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    rw [hkeyV]
    by_cases hab : a = b
    · rw [hab]; simp
    · have hne : ¬ (Fin.castLE (min_le_right m n) a.val = Fin.castLE (min_le_right m n) b.val) := by
        intro h
        apply hab
        have hv : a.val.val = b.val.val := by
          have hh := congrArg Fin.val h
          simpa using hh
        exact Subtype.ext (Fin.ext hv)
      rw [if_neg hne, if_neg hab]
  refine ⟨hUU, hVV, ?_, ?_⟩
  · have hUann : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
        (1 - Statlib.HighDim.MatrixAnalysis.svdPosU s *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s)) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul, sub_self]
    have hUB : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
        ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU s *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s)) * A *
          (1 - Statlib.HighDim.MatrixAnalysis.svdPosV s *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s))) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUann, Matrix.zero_mul, Matrix.zero_mul]
    have hUBt : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
        (t.U * t.sigma * Matrix.transpose t.V) = 0 := by
      rw [← t.h_eq]
      exact hUB
    have hassoc : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
        (t.U * t.sigma * Matrix.transpose t.V) =
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) * t.sigma *
          Matrix.transpose t.V := by
      simp only [Matrix.mul_assoc]
    have hkey3 : (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) * t.sigma *
        Matrix.transpose t.V = 0 := by
      rw [← hassoc, hUBt]
    have hXV : (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) * t.sigma
        = ((Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) * t.sigma *
            Matrix.transpose t.V) * t.V := by
      rw [Matrix.mul_assoc ((Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) * t.sigma)
            (Matrix.transpose t.V) t.V, t.hV_orth, Matrix.mul_one]
    have hMsig : (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) * t.sigma = 0 := by
      rw [hXV, hkey3, Matrix.zero_mul]
    have hsvdUt : Statlib.HighDim.MatrixAnalysis.svdPosU t =
        t.U.submatrix id (fun k => Fin.castLE (min_le_left m n) k.val) := by
      simp only [Statlib.HighDim.MatrixAnalysis.svdPosU]
    have hUtU' : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
        Statlib.HighDim.MatrixAnalysis.svdPosU t = 0 := by
      rw [hsvdUt]
      ext a b
      rw [Matrix.mul_apply, Matrix.zero_apply]
      simp only [Matrix.submatrix_apply, id]
      rw [← Matrix.mul_apply]
      have hMsig_entry : ((Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) * t.sigma)
          a (Fin.castLE (min_le_right m n) b.val) = 0 := by
        rw [hMsig, Matrix.zero_apply]
      have hk0j0 : ((Fin.castLE (min_le_left m n) b.val : Fin m) : ℕ) =
          ((Fin.castLE (min_le_right m n) b.val : Fin n) : ℕ) := rfl
      have hcol_apply : ((Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) * t.sigma)
            a (Fin.castLE (min_le_right m n) b.val)
          = ∑ k : Fin m, (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) a k *
              t.sigma k (Fin.castLE (min_le_right m n) b.val) := Matrix.mul_apply
      have hcol : ((Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) * t.sigma)
            a (Fin.castLE (min_le_right m n) b.val) =
          (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) a
            (Fin.castLE (min_le_left m n) b.val) *
          t.sigma (Fin.castLE (min_le_left m n) b.val) (Fin.castLE (min_le_right m n) b.val) := by
        rw [hcol_apply]
        exact Finset.sum_eq_single (Fin.castLE (min_le_left m n) b.val)
          (fun k _ hk => by
            rw [t.hsigma_diag k (Fin.castLE (min_le_right m n) b.val) (by
              intro h
              apply hk
              apply Fin.ext
              exact h.trans hk0j0.symm), mul_zero])
          (fun hmem => absurd (Finset.mem_univ _) hmem)
      have hprod : (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * t.U) a
            (Fin.castLE (min_le_left m n) b.val) *
          t.sigma (Fin.castLE (min_le_left m n) b.val) (Fin.castLE (min_le_right m n) b.val) = 0 := by
        rw [← hcol, hMsig_entry]
      have hpos : 0 < t.sigma (Fin.castLE (min_le_left m n) b.val) (Fin.castLE (min_le_right m n) b.val) :=
        b.property
      exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hpos)
    calc Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
          (Statlib.HighDim.MatrixAnalysis.svdPosU t *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV t))
        = (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
            Statlib.HighDim.MatrixAnalysis.svdPosU t) *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV t) := by rw [← Matrix.mul_assoc]
        _ = 0 := by rw [hUtU', Matrix.zero_mul]
  · have hVann : (1 - Statlib.HighDim.MatrixAnalysis.svdPosV s *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s)) *
        Statlib.HighDim.MatrixAnalysis.svdPosV s = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hVV, Matrix.mul_one, sub_self]
    have hBV : ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU s *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s)) * A *
        (1 - Statlib.HighDim.MatrixAnalysis.svdPosV s *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s))) *
        Statlib.HighDim.MatrixAnalysis.svdPosV s = 0 := by
      rw [Matrix.mul_assoc ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU s *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s)) * A)
          (1 - Statlib.HighDim.MatrixAnalysis.svdPosV s *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s))
          (Statlib.HighDim.MatrixAnalysis.svdPosV s), hVann, Matrix.mul_zero]
    have hBVt : (t.U * t.sigma * Matrix.transpose t.V) *
        Statlib.HighDim.MatrixAnalysis.svdPosV s = 0 := by
      rw [← t.h_eq]
      exact hBV
    have hUZ : t.U * (t.sigma * (Matrix.transpose t.V *
        Statlib.HighDim.MatrixAnalysis.svdPosV s)) = 0 := by
      have e : (t.U * t.sigma * Matrix.transpose t.V) *
          Statlib.HighDim.MatrixAnalysis.svdPosV s =
          t.U * (t.sigma * (Matrix.transpose t.V *
            Statlib.HighDim.MatrixAnalysis.svdPosV s)) := by
        simp only [Matrix.mul_assoc]
      rw [← e, hBVt]
    have hid : Matrix.transpose t.U * (t.U * (t.sigma * (Matrix.transpose t.V *
        Statlib.HighDim.MatrixAnalysis.svdPosV s))) =
        t.sigma * (Matrix.transpose t.V * Statlib.HighDim.MatrixAnalysis.svdPosV s) := by
      rw [← Matrix.mul_assoc (Matrix.transpose t.U) t.U
          (t.sigma * (Matrix.transpose t.V * Statlib.HighDim.MatrixAnalysis.svdPosV s)),
          t.hU_orth, Matrix.one_mul]
    have hSigV : t.sigma * (Matrix.transpose t.V *
        Statlib.HighDim.MatrixAnalysis.svdPosV s) = 0 := by
      rw [← hid, hUZ, Matrix.mul_zero]
    have hsvdVt : Statlib.HighDim.MatrixAnalysis.svdPosV t =
        t.V.submatrix id (fun k => Fin.castLE (min_le_right m n) k.val) := by
      simp only [Statlib.HighDim.MatrixAnalysis.svdPosV]
    have hV'V : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV t) *
        Statlib.HighDim.MatrixAnalysis.svdPosV s = 0 := by
      ext b jj
      rw [Matrix.zero_apply]
      have h1 : (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV t) *
            Statlib.HighDim.MatrixAnalysis.svdPosV s) b jj =
          (Matrix.transpose t.V * Statlib.HighDim.MatrixAnalysis.svdPosV s)
            (Fin.castLE (min_le_right m n) b.val) jj := by
        rw [hsvdVt]
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id]
      rw [h1]
      have hSigV_entry : (t.sigma * (Matrix.transpose t.V *
          Statlib.HighDim.MatrixAnalysis.svdPosV s))
          (Fin.castLE (min_le_left m n) b.val) jj = 0 := by
        rw [hSigV, Matrix.zero_apply]
      have hk0j0 : ((Fin.castLE (min_le_left m n) b.val : Fin m) : ℕ) =
          ((Fin.castLE (min_le_right m n) b.val : Fin n) : ℕ) := rfl
      have hcolV_apply : (t.sigma * (Matrix.transpose t.V *
            Statlib.HighDim.MatrixAnalysis.svdPosV s))
            (Fin.castLE (min_le_left m n) b.val) jj
          = ∑ k : Fin n, t.sigma (Fin.castLE (min_le_left m n) b.val) k *
              (Matrix.transpose t.V * Statlib.HighDim.MatrixAnalysis.svdPosV s) k jj :=
        Matrix.mul_apply
      have hcolV : (t.sigma * (Matrix.transpose t.V *
            Statlib.HighDim.MatrixAnalysis.svdPosV s))
            (Fin.castLE (min_le_left m n) b.val) jj =
          t.sigma (Fin.castLE (min_le_left m n) b.val) (Fin.castLE (min_le_right m n) b.val) *
          (Matrix.transpose t.V * Statlib.HighDim.MatrixAnalysis.svdPosV s)
            (Fin.castLE (min_le_right m n) b.val) jj := by
        rw [hcolV_apply]
        exact Finset.sum_eq_single (Fin.castLE (min_le_right m n) b.val)
          (fun k _ hk => by
            rw [t.hsigma_diag (Fin.castLE (min_le_left m n) b.val) k (by
              intro h
              apply hk
              apply Fin.ext
              exact h.symm.trans hk0j0), zero_mul])
          (fun hmem => absurd (Finset.mem_univ _) hmem)
      have hprodV : t.sigma (Fin.castLE (min_le_left m n) b.val)
            (Fin.castLE (min_le_right m n) b.val) *
          (Matrix.transpose t.V * Statlib.HighDim.MatrixAnalysis.svdPosV s)
            (Fin.castLE (min_le_right m n) b.val) jj = 0 := by
        rw [← hcolV, hSigV_entry]
      have hposV : 0 < t.sigma (Fin.castLE (min_le_left m n) b.val)
          (Fin.castLE (min_le_right m n) b.val) := b.property
      exact (mul_eq_zero.mp hprodV).resolve_left (ne_of_gt hposV)
    calc (Statlib.HighDim.MatrixAnalysis.svdPosU t *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV t)) *
          Statlib.HighDim.MatrixAnalysis.svdPosV s
        = Statlib.HighDim.MatrixAnalysis.svdPosU t *
            (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV t) *
              Statlib.HighDim.MatrixAnalysis.svdPosV s) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hV'V, Matrix.mul_zero]
  /- @proof-region region.target-node.session.b1c0eea73a4b0c7d end -/

end Statlib.Imported

