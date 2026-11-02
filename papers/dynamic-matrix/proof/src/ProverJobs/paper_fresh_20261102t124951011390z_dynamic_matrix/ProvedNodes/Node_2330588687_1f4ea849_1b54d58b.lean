import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
import Statlib.HighDim.MatrixAnalysis.SVDFoundation
import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_3825179525_37ca31cf_d4c05cca

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix

open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_2330588687_1f4ea849 : ∀ (m n : ℕ)
    (A B : Matrix (Fin m) (Fin n) ℝ)
    (s : Statlib.HighDim.Vocabulary.SVD A)
    (t : Statlib.HighDim.Vocabulary.SVD
      (((1 : Matrix (Fin m) (Fin m) ℝ) -
          Statlib.HighDim.MatrixAnalysis.svdPosU s *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s)) * B *
        ((1 : Matrix (Fin n) (Fin n) ℝ) -
          Statlib.HighDim.MatrixAnalysis.svdPosV s *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s)))),
    Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
        (Statlib.HighDim.MatrixAnalysis.svdPosU t *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV t)) = 0 ∧
    (Statlib.HighDim.MatrixAnalysis.svdPosU t *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV t)) *
        Statlib.HighDim.MatrixAnalysis.svdPosV s = 0 := by
  /- @proof-region region.target-node.session.4f4499ff6bb0a0c3 begin -/
  intro m n A B s t
  have hUorth : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
      Statlib.HighDim.MatrixAnalysis.svdPosU s = 1 :=
    (statopia_math_node_3825179525_37ca31cf m n A s
      (Classical.choice (Statlib.HighDim.MatrixAnalysis.svd_exists _))).1
  have hVorth : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s) *
      Statlib.HighDim.MatrixAnalysis.svdPosV s = 1 :=
    (statopia_math_node_3825179525_37ca31cf m n A s
      (Classical.choice (Statlib.HighDim.MatrixAnalysis.svd_exists _))).2.1
  have hEntryU : ∀ (i : Fin m)
      (k : {k : Fin (min m n) // 0 < t.sigma (Fin.castLE (min_le_left m n) k) (Fin.castLE (min_le_right m n) k)}),
      Statlib.HighDim.MatrixAnalysis.svdPosU t i k = t.U i (Fin.castLE (min_le_left m n) k.1) := by
    intro i k
    simp [Statlib.HighDim.MatrixAnalysis.svdPosU]
  have hEntryV : ∀ (j : Fin n)
      (k : {k : Fin (min m n) // 0 < t.sigma (Fin.castLE (min_le_left m n) k) (Fin.castLE (min_le_right m n) k)}),
      Statlib.HighDim.MatrixAnalysis.svdPosV t j k = t.V j (Fin.castLE (min_le_right m n) k.1) := by
    intro j k
    simp [Statlib.HighDim.MatrixAnalysis.svdPosV]
  obtain ⟨Ut, Vt, sigt, hUt, hVt, hoff, hnn, hdec⟩ := t
  have hUU : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
      ((1 : Matrix (Fin m) (Fin m) ℝ) - Statlib.HighDim.MatrixAnalysis.svdPosU s *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hUorth, Matrix.one_mul, sub_self]
  have hUC : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
      (((1 : Matrix (Fin m) (Fin m) ℝ) - Statlib.HighDim.MatrixAnalysis.svdPosU s *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s)) * B *
        ((1 : Matrix (Fin n) (Fin n) ℝ) - Statlib.HighDim.MatrixAnalysis.svdPosV s *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s))) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.zero_mul, Matrix.zero_mul]
  have hVV : ((1 : Matrix (Fin n) (Fin n) ℝ) - Statlib.HighDim.MatrixAnalysis.svdPosV s *
      Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s)) *
      Statlib.HighDim.MatrixAnalysis.svdPosV s = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hVorth, Matrix.mul_one, sub_self]
  have hCV : (((1 : Matrix (Fin m) (Fin m) ℝ) - Statlib.HighDim.MatrixAnalysis.svdPosU s *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s)) * B *
      ((1 : Matrix (Fin n) (Fin n) ℝ) - Statlib.HighDim.MatrixAnalysis.svdPosV s *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s))) *
      Statlib.HighDim.MatrixAnalysis.svdPosV s = 0 := by
    rw [Matrix.mul_assoc, hVV, Matrix.mul_zero]
  have hW : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
      (Ut * sigt * Matrix.transpose Vt) = 0 := by
    rw [← hdec]
    simpa using hUC
  have hCV' : (Ut * sigt * Matrix.transpose Vt) * Statlib.HighDim.MatrixAnalysis.svdPosV s = 0 := by
    rw [show Ut * sigt * Matrix.transpose Vt =
      ((1 : Matrix (Fin m) (Fin m) ℝ) - Statlib.HighDim.MatrixAnalysis.svdPosU s *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s)) * B *
        ((1 : Matrix (Fin n) (Fin n) ℝ) - Statlib.HighDim.MatrixAnalysis.svdPosV s *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s)) from hdec.symm]
    exact hCV
  have hVtVt : (Ut * sigt * Matrix.transpose Vt) * Vt = Ut * sigt := by
    rw [Matrix.mul_assoc, hVt, Matrix.mul_one]
  have hWσ : (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * Ut) * sigt = 0 := by
    have h2 : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
        ((Ut * sigt * Matrix.transpose Vt) * Vt) = 0 := by
      rw [← Matrix.mul_assoc, hW, Matrix.zero_mul]
    rw [hVtVt] at h2
    rw [Matrix.mul_assoc]
    exact h2
  have hUmul : Matrix.transpose Ut *
        ((Ut * sigt * Matrix.transpose Vt) * Statlib.HighDim.MatrixAnalysis.svdPosV s)
      = sigt * (Matrix.transpose Vt * Statlib.HighDim.MatrixAnalysis.svdPosV s) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, hUt, Matrix.one_mul]
  have hσV : sigt * (Matrix.transpose Vt * Statlib.HighDim.MatrixAnalysis.svdPosV s) = 0 := by
    have h2 : Matrix.transpose Ut *
        ((Ut * sigt * Matrix.transpose Vt) * Statlib.HighDim.MatrixAnalysis.svdPosV s) = 0 := by
      rw [hCV', Matrix.mul_zero]
    rwa [hUmul] at h2
  have hU' : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
      Statlib.HighDim.MatrixAnalysis.svdPosU
        { U := Ut, V := Vt, sigma := sigt, hU_orth := hUt, hV_orth := hVt, hsigma_diag := hoff,
          hsigma_nonneg := hnn, h_eq := hdec } = 0 := by
    ext i k
    have h0 : ((Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * Ut) * sigt) i
        (Fin.castLE (min_le_right m n) k.1) = 0 := by
      rw [hWσ]
      simp
    rw [Matrix.mul_apply] at h0
    have hsingle : ∑ x : Fin m,
          (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * Ut) i x *
            sigt x (Fin.castLE (min_le_right m n) k.1)
        = (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * Ut) i
            (Fin.castLE (min_le_left m n) k.1) *
          sigt (Fin.castLE (min_le_left m n) k.1) (Fin.castLE (min_le_right m n) k.1) := by
      refine Finset.sum_eq_single (Fin.castLE (min_le_left m n) k.1) ?_ ?_
      · intro b _ hb
        have hne : (b : ℕ) ≠ ((Fin.castLE (min_le_right m n) k.1 : Fin n) : ℕ) := by
          intro h
          exact hb (Fin.ext (by simpa using h))
        rw [hoff b (Fin.castLE (min_le_right m n) k.1) hne, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hsingle] at h0
    have hpos : sigt (Fin.castLE (min_le_left m n) k.1) (Fin.castLE (min_le_right m n) k.1) ≠ 0 :=
      ne_of_gt k.2
    have hz : (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) * Ut) i
        (Fin.castLE (min_le_left m n) k.1) = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h hpos
    simpa [Statlib.HighDim.MatrixAnalysis.svdPosU, Matrix.mul_apply] using hz
  have hV' : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV
        { U := Ut, V := Vt, sigma := sigt, hU_orth := hUt, hV_orth := hVt, hsigma_diag := hoff,
          hsigma_nonneg := hnn, h_eq := hdec }) *
      Statlib.HighDim.MatrixAnalysis.svdPosV s = 0 := by
    ext k j
    have h0 : (sigt * (Matrix.transpose Vt * Statlib.HighDim.MatrixAnalysis.svdPosV s))
        (Fin.castLE (min_le_left m n) k.1) j = 0 := by
      rw [hσV]
      simp
    rw [Matrix.mul_apply] at h0
    have hsingle : ∑ x : Fin n, sigt (Fin.castLE (min_le_left m n) k.1) x *
          (Matrix.transpose Vt * Statlib.HighDim.MatrixAnalysis.svdPosV s) x j
        = sigt (Fin.castLE (min_le_left m n) k.1) (Fin.castLE (min_le_right m n) k.1) *
          (Matrix.transpose Vt * Statlib.HighDim.MatrixAnalysis.svdPosV s)
            (Fin.castLE (min_le_right m n) k.1) j := by
      refine Finset.sum_eq_single (Fin.castLE (min_le_right m n) k.1) ?_ ?_
      · intro b _ hb
        have hne : ((Fin.castLE (min_le_left m n) k.1 : Fin m) : ℕ) ≠ (b : ℕ) := by
          intro h
          exact hb (Fin.ext (by simpa using h.symm))
        rw [hoff (Fin.castLE (min_le_left m n) k.1) b hne, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hsingle] at h0
    have hpos : sigt (Fin.castLE (min_le_left m n) k.1) (Fin.castLE (min_le_right m n) k.1) ≠ 0 :=
      ne_of_gt k.2
    have hz : (Matrix.transpose Vt * Statlib.HighDim.MatrixAnalysis.svdPosV s)
        (Fin.castLE (min_le_right m n) k.1) j = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hpos
      · exact h
    simpa [Statlib.HighDim.MatrixAnalysis.svdPosV, Matrix.mul_apply] using hz
  constructor
  · rw [← Matrix.mul_assoc, hU', Matrix.zero_mul]
  · rw [Matrix.mul_assoc, hV', Matrix.mul_zero]
  /- @proof-region region.target-node.session.4f4499ff6bb0a0c3 end -/

end Statlib.Imported

