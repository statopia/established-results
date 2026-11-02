import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_4126393493_5c53b8e0_9730c626

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix
open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_1610908339_c7892be1 : ∀ (m1 m2 : ℕ) (X : Matrix (Fin m1) (Fin m2) ℝ)
    (svd : Statlib.HighDim.Vocabulary.SVD X),
    Statlib.HighDim.MatrixAnalysis.opNorm
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose) ≤ 1 ∧
      (∑ i : Fin m1, ∑ j : Fin m2,
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
            (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose) i j * X i j)
        = Statlib.HighDim.Vocabulary.nuclearNorm X := by
  /- @proof-region region.target-node.session.e376cfe1bab6b020 begin -/
  intro m1 m2 X svd
  classical
  let T := {k : Fin (min m1 m2) // 0 < svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) k) (Fin.castLE (Nat.min_le_right m1 m2) k)}
  have hφ1inj : Function.Injective (fun k : Fin (min m1 m2) => Fin.castLE (Nat.min_le_left m1 m2) k) :=
    fun x y h => Fin.ext (by simpa using congrArg Fin.val h)
  have hφ2inj : Function.Injective (fun k : Fin (min m1 m2) => Fin.castLE (Nat.min_le_right m1 m2) k) :=
    fun x y h => Fin.ext (by simpa using congrArg Fin.val h)
  have hUU : ∀ x y : Fin m1, (∑ i : Fin m1, svd.U i x * svd.U i y) = if x = y then 1 else 0 := by
    intro x y
    have hs := congrFun (congrFun svd.hU_orth x) y
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hs
  have hVV : ∀ x y : Fin m2, (∑ i : Fin m2, svd.V i x * svd.V i y) = if x = y then 1 else 0 := by
    intro x y
    have hs := congrFun (congrFun svd.hV_orth x) y
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hs
  have hU' : (Statlib.HighDim.MatrixAnalysis.svdPosU svd).transpose *
      Statlib.HighDim.MatrixAnalysis.svdPosU svd = (1 : Matrix T T ℝ) := by
    have hW : Statlib.HighDim.MatrixAnalysis.svdPosU svd =
        svd.U.submatrix id (fun k : T => Fin.castLE (Nat.min_le_left m1 m2) k.1) := rfl
    have hstep : ∀ a b : T,
        ((svd.U.submatrix id (fun k : T => Fin.castLE (Nat.min_le_left m1 m2) k.1)).transpose *
          svd.U.submatrix id (fun k : T => Fin.castLE (Nat.min_le_left m1 m2) k.1)) a b
        = ∑ i : Fin m1, svd.U i (Fin.castLE (Nat.min_le_left m1 m2) a.1) *
            svd.U i (Fin.castLE (Nat.min_le_left m1 m2) b.1) := fun a b => rfl
    rw [hW]
    ext a b
    rw [hstep, hUU]
    by_cases hab : a = b
    · simp [Matrix.one_apply, hab]
    · have hne : Fin.castLE (Nat.min_le_left m1 m2) a.1 ≠ Fin.castLE (Nat.min_le_left m1 m2) b.1 :=
        fun h => hab (Subtype.ext (hφ1inj h))
      simp [Matrix.one_apply, hab, hne]
  have hV' : (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose *
      Statlib.HighDim.MatrixAnalysis.svdPosV svd = (1 : Matrix T T ℝ) := by
    have hW : Statlib.HighDim.MatrixAnalysis.svdPosV svd =
        svd.V.submatrix id (fun k : T => Fin.castLE (Nat.min_le_right m1 m2) k.1) := rfl
    have hstep : ∀ a b : T,
        ((svd.V.submatrix id (fun k : T => Fin.castLE (Nat.min_le_right m1 m2) k.1)).transpose *
          svd.V.submatrix id (fun k : T => Fin.castLE (Nat.min_le_right m1 m2) k.1)) a b
        = ∑ i : Fin m2, svd.V i (Fin.castLE (Nat.min_le_right m1 m2) a.1) *
            svd.V i (Fin.castLE (Nat.min_le_right m1 m2) b.1) := fun a b => rfl
    rw [hW]
    ext a b
    rw [hstep, hVV]
    by_cases hab : a = b
    · simp [Matrix.one_apply, hab]
    · have hne : Fin.castLE (Nat.min_le_right m1 m2) a.1 ≠ Fin.castLE (Nat.min_le_right m1 m2) b.1 :=
        fun h => hab (Subtype.ext (hφ2inj h))
      simp [Matrix.one_apply, hab, hne]
  constructor
  · rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    have hidemU : (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose).transpose *
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose)
        = Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
        Matrix.mul_assoc (Statlib.HighDim.MatrixAnalysis.svdPosV svd), hU', Matrix.mul_one]
    have hidemV : (Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose).transpose *
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose)
        = Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
        Matrix.mul_assoc (Statlib.HighDim.MatrixAnalysis.svdPosV svd), hV', Matrix.mul_one]
    have hP2 := Matrix.l2_opNorm_conjTranspose_mul_self
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hidemU] at hP2
    have hVV := Matrix.l2_opNorm_conjTranspose_mul_self
      (Statlib.HighDim.MatrixAnalysis.svdPosV svd *
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hidemV] at hVV
    have ht : ‖Statlib.HighDim.MatrixAnalysis.svdPosV svd *
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose‖ ≤ 1 := by
      nlinarith [hVV, sq_nonneg (‖Statlib.HighDim.MatrixAnalysis.svdPosV svd *
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose‖ - 1)]
    by_contra hcon
    push_neg at hcon
    nlinarith [hP2, ht, hcon]
  · exact statopia_math_node_4126393493_5c53b8e0 m1 m2 X svd
  /- @proof-region region.target-node.session.e376cfe1bab6b020 end -/

end Statlib.Imported

