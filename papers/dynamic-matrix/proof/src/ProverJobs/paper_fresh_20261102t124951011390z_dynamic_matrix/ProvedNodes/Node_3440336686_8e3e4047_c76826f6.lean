import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SVDFoundation
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_1610908339_c7892be1_cf709dfa
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_3180815852_334b7fa8_7204a7ff

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix
open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_3440336686_8e3e4047 : ∀ (m1 m2 : ℕ)
    (A B G X : Matrix (Fin m1) (Fin m2) ℝ),
    (0 ≤ Statlib.HighDim.Vocabulary.nuclearNorm X) ∧
    (Statlib.HighDim.MatrixAnalysis.opNorm G ≤ 1 →
      frobInner G X ≤ Statlib.HighDim.Vocabulary.nuclearNorm X) ∧
    (Statlib.HighDim.Vocabulary.nuclearNorm X
      = ⨆ (H : {M : Matrix (Fin m1) (Fin m2) ℝ //
            Statlib.HighDim.MatrixAnalysis.opNorm M ≤ 1}), frobInner H.1 X) ∧
    (frobInner A B ≤
      Statlib.HighDim.MatrixAnalysis.opNorm A * Statlib.HighDim.Vocabulary.nuclearNorm B) ∧
    (|frobInner A B| ≤
      Statlib.HighDim.MatrixAnalysis.opNorm A * Statlib.HighDim.Vocabulary.nuclearNorm B) ∧
    (∀ (svd : Statlib.HighDim.Vocabulary.SVD X),
      (Statlib.HighDim.MatrixAnalysis.opNorm
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
            (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose) ≤ 1) ∧
        (frobInner
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
              (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose) X
          = Statlib.HighDim.Vocabulary.nuclearNorm X)) ∧
    (∃ Gx : Matrix (Fin m1) (Fin m2) ℝ,
      (Statlib.HighDim.MatrixAnalysis.opNorm Gx ≤ 1) ∧
        (frobInner Gx X = Statlib.HighDim.Vocabulary.nuclearNorm X) ∧
        (∀ Y : Matrix (Fin m1) (Fin m2) ℝ,
          frobInner Gx Y ≤ Statlib.HighDim.Vocabulary.nuclearNorm Y)) := by
  /- @proof-region region.target-node.session.f6ded45b480ff6cd begin -/
  intro m1 m2 A B G X
  have hbridge : ∀ (Y Z : Matrix (Fin m1) (Fin m2) ℝ),
      Statlib.HighDim.MatrixAnalysis.traceInner Y Z = frobInner Z Y := by
    intro Y Z
    unfold Statlib.HighDim.MatrixAnalysis.traceInner frobInner
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hentryGen : ∀ (M : Matrix (Fin m1) (Fin m2) ℝ) (i : Fin m1) (j : Fin m2),
      |M i j| ≤ Statlib.HighDim.MatrixAnalysis.opNorm M := by
    intro M i j
    have hEv := Statlib.HighDim.MatrixAnalysis.opNorm_vec_le M (EuclideanSpace.single j 1)
    rw [Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single] at hEv
    have hmv : M.mulVec (Pi.single j (1 : ℝ)) = M.col j := by
      rw [Matrix.mulVec_single]
      simp
    rw [hmv, EuclideanSpace.norm_single, norm_one, mul_one] at hEv
    have hcoord := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin m1 => ℝ)
      (WithLp.toLp 2 (M.col j)) i
    have hval : ‖(M.col j) i‖ = |M i j| := by
      change ‖M i j‖ = |M i j|
      exact Real.norm_eq_abs _
    rw [WithLp.ofLp_toLp, hval] at hcoord
    exact hcoord.trans hEv
  have hbdd : ∀ (M : Matrix (Fin m1) (Fin m2) ℝ),
      BddAbove (Set.range fun H : {N : Matrix (Fin m1) (Fin m2) ℝ //
        Statlib.HighDim.MatrixAnalysis.opNorm N ≤ 1} => frobInner H.1 M) := by
    intro M
    refine ⟨∑ i : Fin m1, ∑ j : Fin m2, |M i j|, ?_⟩
    rintro b ⟨H, rfl⟩
    have hterm : ∀ (i : Fin m1) (j : Fin m2), H.1 i j * M i j ≤ |M i j| := by
      intro i j
      have h4 : |H.1 i j| ≤ 1 := (hentryGen H.1 i j).trans H.2
      calc H.1 i j * M i j ≤ |H.1 i j * M i j| := le_abs_self _
        _ = |H.1 i j| * |M i j| := abs_mul _ _
        _ ≤ 1 * |M i j| := by gcongr
        _ = |M i j| := one_mul _
    calc frobInner H.1 M
        = ∑ i : Fin m1, ∑ j : Fin m2, H.1 i j * M i j := rfl
      _ ≤ ∑ i : Fin m1, ∑ j : Fin m2, |M i j| :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hsup : ∀ (M : Matrix (Fin m1) (Fin m2) ℝ),
      Statlib.HighDim.Vocabulary.nuclearNorm M
      = ⨆ (H : {N : Matrix (Fin m1) (Fin m2) ℝ //
            Statlib.HighDim.MatrixAnalysis.opNorm N ≤ 1}), frobInner H.1 M := by
    intro M
    rw [Statlib.HighDim.MatrixAnalysis.nuclearNorm_eq_iSup_opNorm_le_one M]
    exact congrArg iSup (funext fun H => hbridge M H.1)
  have hle : ∀ (M G' : Matrix (Fin m1) (Fin m2) ℝ),
      Statlib.HighDim.MatrixAnalysis.opNorm G' ≤ 1 →
      frobInner G' M ≤ Statlib.HighDim.Vocabulary.nuclearNorm M := by
    intro M G' hG'
    rw [hsup M]
    exact le_ciSup (hbdd M) ⟨G', hG'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Statlib.HighDim.MatrixAnalysis.nuclearNorm_nonneg X).1
  · exact hle X G
  · exact hsup X
  · exact (statopia_math_node_3180815852_334b7fa8 m1 m2 A B).1
  · exact (statopia_math_node_3180815852_334b7fa8 m1 m2 A B).2
  · intro svd
    exact ⟨(statopia_math_node_1610908339_c7892be1 m1 m2 X svd).1,
      by simpa only [frobInner] using (statopia_math_node_1610908339_c7892be1 m1 m2 X svd).2⟩
  · obtain ⟨svd⟩ := Statlib.HighDim.MatrixAnalysis.svd_exists X
    have hchild := statopia_math_node_1610908339_c7892be1 m1 m2 X svd
    refine ⟨Statlib.HighDim.MatrixAnalysis.svdPosU svd *
      (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose, hchild.1, ?_, ?_⟩
    · simpa only [frobInner] using hchild.2
    · intro Y
      exact hle Y _ hchild.1
  /- @proof-region region.target-node.session.f6ded45b480ff6cd end -/

end Statlib.Imported

