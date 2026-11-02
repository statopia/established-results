import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_3440336686_8e3e4047_c76826f6

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix

open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_791349827_8cd9ad5e : ∀ (m1 m2 : ℕ)
    (A B G X M : Matrix (Fin m1) (Fin m2) ℝ),
    (0 ≤ Statlib.HighDim.Vocabulary.nuclearNorm X) ∧
    (Statlib.HighDim.MatrixAnalysis.opNorm G ≤ 1 →
      frobInner G X ≤ Statlib.HighDim.Vocabulary.nuclearNorm X) ∧
    (Statlib.HighDim.Vocabulary.nuclearNorm X
      = ⨆ (H : {N : Matrix (Fin m1) (Fin m2) ℝ //
            Statlib.HighDim.MatrixAnalysis.opNorm N ≤ 1}), frobInner H.1 X) ∧
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
          frobInner Gx Y ≤ Statlib.HighDim.Vocabulary.nuclearNorm Y)) ∧
    (∀ (V : Matrix (Fin m1) (Fin m2) ℝ),
      Statlib.HighDim.MatrixAnalysis.opNorm V ≤ 1 →
        frobInner V M = Statlib.HighDim.Vocabulary.nuclearNorm M →
          (frobInner V A ≤ Statlib.HighDim.Vocabulary.nuclearNorm A) ∧
          (Statlib.HighDim.Vocabulary.nuclearNorm A ≥
            Statlib.HighDim.Vocabulary.nuclearNorm M + frobInner V (A - M))) ∧
    (∃ V : Matrix (Fin m1) (Fin m2) ℝ,
      (Statlib.HighDim.MatrixAnalysis.opNorm V ≤ 1) ∧
        (frobInner V M = Statlib.HighDim.Vocabulary.nuclearNorm M) ∧
        (∀ Y : Matrix (Fin m1) (Fin m2) ℝ,
          frobInner V Y ≤ Statlib.HighDim.Vocabulary.nuclearNorm Y)) := by
  /- @proof-region region.target-node.session.44316f970637b5d3 begin -/
  intro m1 m2 A B G X M
  have hdep := statopia_math_node_3440336686_8e3e4047 m1 m2 A B G X
  obtain ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩ := hdep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hd1
  · exact hd2
  · exact hd3
  · exact hd4
  · exact hd5
  · exact hd6
  · exact hd7
  · intro V hV hVM
    have hVA : frobInner V A ≤ Statlib.HighDim.Vocabulary.nuclearNorm A :=
      (statopia_math_node_3440336686_8e3e4047 m1 m2 A A V A).2.1 hV
    have hlin : frobInner V (A - M) = frobInner V A - frobInner V M := by
      simp [frobInner, Finset.sum_sub_distrib, mul_sub]
    refine ⟨hVA, ?_⟩
    rw [hlin, hVM]
    linarith
  · exact (statopia_math_node_3440336686_8e3e4047 m1 m2 M M M M).2.2.2.2.2.2
  /- @proof-region region.target-node.session.44316f970637b5d3 end -/

end Statlib.Imported

