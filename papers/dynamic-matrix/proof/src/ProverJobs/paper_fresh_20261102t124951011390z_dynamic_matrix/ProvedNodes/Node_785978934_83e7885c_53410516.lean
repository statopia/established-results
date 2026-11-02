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
theorem statopia_math_node_785978934_83e7885c : ∀ (m1 m2 : ℕ)
    (M : Matrix (Fin m1) (Fin m2) ℝ)
    (svd : Statlib.HighDim.Vocabulary.SVD M),
    Matrix.rank (Statlib.HighDim.MatrixAnalysis.svdPosU svd) ≤ Matrix.rank M ∧
      Matrix.rank (Statlib.HighDim.MatrixAnalysis.svdPosV svd) ≤ Matrix.rank M := by
  /- @proof-region region.target-node.session.cd16a2a489b5de73 begin -/
  intro m1 m2 M svd
  obtain ⟨u, v, sg, hu, hv, hoff, hnonneg, hdecomp⟩ := svd
  let Idx := {k : Fin (min m1 m2) // 0 < sg (Fin.castLE (min_le_left m1 m2) k) (Fin.castLE (min_le_right m1 m2) k)}
  have hUform : ∀ (i : Fin m1)
      (k : {k : Fin (min m1 m2) // 0 < sg (Fin.castLE (min_le_left m1 m2) k) (Fin.castLE (min_le_right m1 m2) k)}),
      Statlib.HighDim.MatrixAnalysis.svdPosU ⟨u, v, sg, hu, hv, hoff, hnonneg, hdecomp⟩ i k
        = u i (Fin.castLE (min_le_left m1 m2) k.1) := by
    intro i k
    simp only [Statlib.HighDim.MatrixAnalysis.svdPosU, Matrix.submatrix_apply, id_eq]
  have hMv : M * v = u * sg := by
    rw [hdecomp, Matrix.mul_assoc, hv, Matrix.mul_one]
  have hdiagU : ∀ (i : Fin m1) (k : Idx),
      (u * sg) i (Fin.castLE (min_le_right m1 m2) k.1)
        = u i (Fin.castLE (min_le_left m1 m2) k.1)
            * sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1) := by
    intro i k
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single (Fin.castLE (min_le_left m1 m2) k.1)
    · intro b _ hb
      have hne : (b : ℕ) ≠ ((Fin.castLE (min_le_right m1 m2) k.1 : Fin m2) : ℕ) := by
        intro h
        exact hb (Fin.ext (by rw [h]; rfl))
      rw [hoff b (Fin.castLE (min_le_right m1 m2) k.1) hne, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  let D1' : Matrix (Fin m2) Idx ℝ := fun x k => if x = Fin.castLE (min_le_right m1 m2) k.1 then (sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1))⁻¹ else 0
  have hD1' : ∀ (i : Fin m1) (k : Idx),
      ((u * sg) * D1') i k = u i (Fin.castLE (min_le_left m1 m2) k.1) := by
    intro i k
    rw [Matrix.mul_apply]
    have hsum : (∑ x : Fin m2, (u * sg) i x * D1' x k)
        = (u * sg) i (Fin.castLE (min_le_right m1 m2) k.1)
            * D1' (Fin.castLE (min_le_right m1 m2) k.1) k := by
      apply Finset.sum_eq_single (Fin.castLE (min_le_right m1 m2) k.1)
      · intro b _ hb
        have hb0 : D1' b k = 0 := by
          show (if b = Fin.castLE (min_le_right m1 m2) k.1 then (sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1))⁻¹ else 0) = 0
          rw [if_neg hb]
        rw [hb0, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hsum]
    have hval : D1' (Fin.castLE (min_le_right m1 m2) k.1) k
        = (sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1))⁻¹ := by
      show (if (Fin.castLE (min_le_right m1 m2) k.1 = Fin.castLE (min_le_right m1 m2) k.1) then (sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1))⁻¹ else 0) = (sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1))⁻¹
      rw [if_pos rfl]
    rw [hval, hdiagU i k, mul_assoc, mul_inv_cancel₀ (ne_of_gt k.2), mul_one]
  have hU : Matrix.rank (Statlib.HighDim.MatrixAnalysis.svdPosU ⟨u, v, sg, hu, hv, hoff, hnonneg, hdecomp⟩) ≤ Matrix.rank M := by
    have hfactor : Statlib.HighDim.MatrixAnalysis.svdPosU ⟨u, v, sg, hu, hv, hoff, hnonneg, hdecomp⟩ = (u * sg) * D1' := by
      ext i k
      rw [hUform i k]
      exact (hD1' i k).symm
    rw [hfactor]
    calc Matrix.rank ((u * sg) * D1') ≤ Matrix.rank (u * sg) := Matrix.rank_mul_le_left (u * sg) D1'
      _ = Matrix.rank (M * v) := by rw [hMv]
      _ ≤ Matrix.rank M := Matrix.rank_mul_le_left M v
  refine ⟨hU, ?_⟩
  have hVform : ∀ (j : Fin m2)
      (k : {k : Fin (min m1 m2) // 0 < sg (Fin.castLE (min_le_left m1 m2) k) (Fin.castLE (min_le_right m1 m2) k)}),
      Statlib.HighDim.MatrixAnalysis.svdPosV ⟨u, v, sg, hu, hv, hoff, hnonneg, hdecomp⟩ j k
        = v j (Fin.castLE (min_le_right m1 m2) k.1) := by
    intro j k
    simp only [Statlib.HighDim.MatrixAnalysis.svdPosV, Matrix.submatrix_apply, id_eq]
  have hMt : M.transpose = v * sg.transpose * u.transpose := by
    rw [hdecomp]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc]
  have hMu : M.transpose * u = v * sg.transpose := by
    rw [hMt, Matrix.mul_assoc, hu, Matrix.mul_one]
  have hdiagV : ∀ (j : Fin m2) (k : Idx),
      (v * sg.transpose) j (Fin.castLE (min_le_left m1 m2) k.1)
        = v j (Fin.castLE (min_le_right m1 m2) k.1)
            * sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1) := by
    intro j k
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single (Fin.castLE (min_le_right m1 m2) k.1)
    · intro b _ hb
      have hne : ((Fin.castLE (min_le_left m1 m2) k.1 : Fin m1) : ℕ) ≠ (b : ℕ) := by
        intro h
        exact hb (Fin.ext (by rw [← h]; rfl))
      rw [Matrix.transpose_apply, hoff (Fin.castLE (min_le_left m1 m2) k.1) b hne, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  let D2' : Matrix (Fin m1) Idx ℝ := fun x k => if x = Fin.castLE (min_le_left m1 m2) k.1 then (sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1))⁻¹ else 0
  have hD2' : ∀ (j : Fin m2) (k : Idx),
      ((v * sg.transpose) * D2') j k = v j (Fin.castLE (min_le_right m1 m2) k.1) := by
    intro j k
    rw [Matrix.mul_apply]
    have hsum : (∑ x : Fin m1, (v * sg.transpose) j x * D2' x k)
        = (v * sg.transpose) j (Fin.castLE (min_le_left m1 m2) k.1)
            * D2' (Fin.castLE (min_le_left m1 m2) k.1) k := by
      apply Finset.sum_eq_single (Fin.castLE (min_le_left m1 m2) k.1)
      · intro b _ hb
        have hb0 : D2' b k = 0 := by
          show (if b = Fin.castLE (min_le_left m1 m2) k.1 then (sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1))⁻¹ else 0) = 0
          rw [if_neg hb]
        rw [hb0, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hsum]
    have hval : D2' (Fin.castLE (min_le_left m1 m2) k.1) k
        = (sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1))⁻¹ := by
      show (if (Fin.castLE (min_le_left m1 m2) k.1 = Fin.castLE (min_le_left m1 m2) k.1) then (sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1))⁻¹ else 0) = (sg (Fin.castLE (min_le_left m1 m2) k.1) (Fin.castLE (min_le_right m1 m2) k.1))⁻¹
      rw [if_pos rfl]
    rw [hval, hdiagV j k, mul_assoc, mul_inv_cancel₀ (ne_of_gt k.2), mul_one]
  have hfactor : Statlib.HighDim.MatrixAnalysis.svdPosV ⟨u, v, sg, hu, hv, hoff, hnonneg, hdecomp⟩ = (v * sg.transpose) * D2' := by
    ext j k
    rw [hVform j k]
    exact (hD2' j k).symm
  rw [hfactor]
  calc Matrix.rank ((v * sg.transpose) * D2') ≤ Matrix.rank (v * sg.transpose) := Matrix.rank_mul_le_left (v * sg.transpose) D2'
    _ = Matrix.rank (M.transpose * u) := by rw [hMu]
    _ ≤ Matrix.rank M.transpose := Matrix.rank_mul_le_left M.transpose u
    _ = Matrix.rank M := Matrix.rank_transpose M
  /- @proof-region region.target-node.session.cd16a2a489b5de73 end -/

end Statlib.Imported

