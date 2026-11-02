import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.MatrixRecovery.MatrixRipRecoveryBound
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
theorem statopia_math_node_3180815852_334b7fa8 : ∀ (m1 m2 : ℕ)
    (A B : Matrix (Fin m1) (Fin m2) ℝ),
    frobInner A B ≤
        Statlib.HighDim.MatrixAnalysis.opNorm A *
          Statlib.HighDim.Vocabulary.nuclearNorm B ∧
      |frobInner A B| ≤
        Statlib.HighDim.MatrixAnalysis.opNorm A *
          Statlib.HighDim.Vocabulary.nuclearNorm B := by
  /- @proof-region region.target-node.session.b72793acc94a352c begin -/
  intro m1 m2 A B
  have hentry : ∀ (Y : Matrix (Fin m1) (Fin m2) ℝ) (i : Fin m1) (j : Fin m2),
      |Y i j| ≤ Statlib.HighDim.MatrixAnalysis.opNorm Y := by
    intro Y i j
    have hid : ((Matrix.toEuclideanLin Y) (EuclideanSpace.single j (1 : ℝ))) i = Y i j := by
      rw [Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single, Matrix.mulVec_single]
      simp
    have h1 : |((Matrix.toEuclideanLin Y) (EuclideanSpace.single j (1 : ℝ))) i| ≤
        ‖(Matrix.toEuclideanLin Y) (EuclideanSpace.single j (1 : ℝ))‖ := by
      rw [← Real.norm_eq_abs]
      simpa using PiLp.norm_apply_le
        (x := (Matrix.toEuclideanLin Y) (EuclideanSpace.single j (1 : ℝ))) i
    have h2 : ‖(Matrix.toEuclideanLin Y) (EuclideanSpace.single j (1 : ℝ))‖ ≤
        Statlib.HighDim.MatrixAnalysis.opNorm Y := by
      have h := Statlib.HighDim.MatrixAnalysis.opNorm_vec_le Y (EuclideanSpace.single j (1 : ℝ))
      rwa [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_one, mul_one] at h
    rw [← hid]
    exact le_trans h1 h2
  have htrace : ∀ (N X : Matrix (Fin m1) (Fin m2) ℝ),
      Statlib.HighDim.MatrixAnalysis.traceInner N X = ∑ i, ∑ j, N i j * X i j := by
    intro N X
    simp only [Statlib.HighDim.MatrixAnalysis.traceInner, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
  have hbdd : ∀ (N : Matrix (Fin m1) (Fin m2) ℝ),
      BddAbove (Set.range (fun Y : {M : Matrix (Fin m1) (Fin m2) ℝ //
        Statlib.HighDim.MatrixAnalysis.opNorm M ≤ 1} =>
          Statlib.HighDim.MatrixAnalysis.traceInner N (Y : Matrix (Fin m1) (Fin m2) ℝ))) := by
    intro N
    refine ⟨∑ i : Fin m1, ∑ j : Fin m2, |N i j|, ?_⟩
    rintro _ ⟨Y, rfl⟩
    simp only [htrace]
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    calc N i j * (Y : Matrix (Fin m1) (Fin m2) ℝ) i j
        ≤ |N i j * (Y : Matrix (Fin m1) (Fin m2) ℝ) i j| := le_abs_self _
      _ = |N i j| * |(Y : Matrix (Fin m1) (Fin m2) ℝ) i j| := abs_mul _ _
      _ ≤ |N i j| * 1 := by
          have hY : |(Y : Matrix (Fin m1) (Fin m2) ℝ) i j| ≤ 1 :=
            le_trans (hentry (Y : Matrix (Fin m1) (Fin m2) ℝ) i j) Y.2
          nlinarith [abs_nonneg (N i j), hY]
      _ = |N i j| := mul_one _
  have key : ∀ (N X : Matrix (Fin m1) (Fin m2) ℝ),
      Statlib.HighDim.MatrixAnalysis.opNorm X ≤ 1 →
      Statlib.HighDim.MatrixAnalysis.traceInner N X ≤ Statlib.HighDim.Vocabulary.nuclearNorm N := by
    intro N X hX
    rw [Statlib.HighDim.MatrixAnalysis.nuclearNorm_eq_iSup_opNorm_le_one N]
    exact le_ciSup (hbdd N) ⟨X, hX⟩
  have hsc : ∀ (t : ℝ) (M : Matrix (Fin m1) (Fin m2) ℝ),
      Statlib.HighDim.MatrixAnalysis.opNorm (t • M) ≤
        |t| * Statlib.HighDim.MatrixAnalysis.opNorm M := by
    intro t M
    have h1 : Matrix.toEuclideanLin (t • M) = t • Matrix.toEuclideanLin M := map_smul _ _ _
    have h2 : LinearMap.toContinuousLinearMap (t • Matrix.toEuclideanLin M)
        = t • LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) := by
      ext v
      simp
    simp only [Statlib.HighDim.MatrixAnalysis.opNorm, h1, h2]
    have h := ContinuousLinearMap.opNorm_smul_le t
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M))
    rwa [Real.norm_eq_abs] at h
  have hTI : ∀ (N M : Matrix (Fin m1) (Fin m2) ℝ) (t : ℝ),
      Statlib.HighDim.MatrixAnalysis.traceInner N (t • M) = t * frobInner M N := by
    intro N M t
    rw [htrace, frobInner]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have hstep : ∀ (M N : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner M N ≤ Statlib.HighDim.MatrixAnalysis.opNorm M *
        Statlib.HighDim.Vocabulary.nuclearNorm N := by
    intro M N
    by_cases hM : Statlib.HighDim.MatrixAnalysis.opNorm M = 0
    · have hM0 : M = 0 := by
        ext i j
        have h := hentry M i j
        rw [hM] at h
        have h0 : |M i j| = 0 := le_antisymm h (abs_nonneg (M i j))
        simpa using abs_eq_zero.mp h0
      subst hM0
      have hz : frobInner (0 : Matrix (Fin m1) (Fin m2) ℝ) N = 0 := by simp [frobInner]
      rw [hz]
      exact mul_nonneg (Statlib.HighDim.MatrixAnalysis.opNorm_nonneg 0)
        (Statlib.HighDim.MatrixAnalysis.nuclearNorm_nonneg N).1
    · have hpos : 0 < Statlib.HighDim.MatrixAnalysis.opNorm M :=
        lt_of_le_of_ne (Statlib.HighDim.MatrixAnalysis.opNorm_nonneg M) (Ne.symm hM)
      have h1 : Statlib.HighDim.MatrixAnalysis.opNorm
          ((Statlib.HighDim.MatrixAnalysis.opNorm M)⁻¹ • M) ≤ 1 := by
        have h := hsc (Statlib.HighDim.MatrixAnalysis.opNorm M)⁻¹ M
        rwa [abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)] at h
      have hk := key N ((Statlib.HighDim.MatrixAnalysis.opNorm M)⁻¹ • M) h1
      rw [hTI N M (Statlib.HighDim.MatrixAnalysis.opNorm M)⁻¹] at hk
      have hfac : Statlib.HighDim.MatrixAnalysis.opNorm M *
          (Statlib.HighDim.MatrixAnalysis.opNorm M)⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt hpos)
      calc frobInner M N
          = (Statlib.HighDim.MatrixAnalysis.opNorm M *
              (Statlib.HighDim.MatrixAnalysis.opNorm M)⁻¹) * frobInner M N := by
            rw [hfac, one_mul]
        _ = Statlib.HighDim.MatrixAnalysis.opNorm M *
              ((Statlib.HighDim.MatrixAnalysis.opNorm M)⁻¹ * frobInner M N) := by rw [mul_assoc]
        _ ≤ Statlib.HighDim.MatrixAnalysis.opNorm M * Statlib.HighDim.Vocabulary.nuclearNorm N :=
            mul_le_mul_of_nonneg_left hk (le_of_lt hpos)
  constructor
  · exact hstep A B
  · have hneg : -frobInner A B ≤ Statlib.HighDim.MatrixAnalysis.opNorm A *
        Statlib.HighDim.Vocabulary.nuclearNorm B := by
      have h := hstep A (-B)
      rw [Statlib.HighDim.MatrixRecovery.nuclearNorm_neg B] at h
      have hfr : frobInner A (-B) = -frobInner A B := by
        simp [frobInner]
      rw [hfr] at h
      exact h
    exact abs_le.mpr ⟨by linarith, hstep A B⟩
  /- @proof-region region.target-node.session.b72793acc94a352c end -/

end Statlib.Imported

