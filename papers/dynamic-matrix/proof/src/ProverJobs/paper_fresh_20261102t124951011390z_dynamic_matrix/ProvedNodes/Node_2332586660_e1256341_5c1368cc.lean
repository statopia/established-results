import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SVDFoundation
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_1491593895_e4edda66_c73fdada
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_2330588687_1f4ea849_1b54d58b
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_2628551730_d82d74eb_c14fc884
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_3825179525_37ca31cf_d4c05cca
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_791349827_8cd9ad5e_a51ab6c3

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix



open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_2332586660_e1256341 : ∀ (m1 m2 : ℕ) (M : Matrix (Fin m1) (Fin m2) ℝ)
    (svd : Statlib.HighDim.Vocabulary.SVD M)
    (H : Matrix (Fin m1) (Fin m2) ℝ)
    (svd_perp : Statlib.HighDim.Vocabulary.SVD
      ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) * H *
        (1 - Statlib.HighDim.MatrixAnalysis.svdPosV svd *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)))),
    let U := Statlib.HighDim.MatrixAnalysis.svdPosU svd
    let V := Statlib.HighDim.MatrixAnalysis.svdPosV svd
    let PU : Matrix (Fin m1) (Fin m1) ℝ := U * U.transpose
    let PV : Matrix (Fin m2) (Fin m2) ℝ := V * V.transpose
    let Hperp : Matrix (Fin m1) (Fin m2) ℝ :=
      ((1 : Matrix (Fin m1) (Fin m1) ℝ) - PU) * H * ((1 : Matrix (Fin m2) (Fin m2) ℝ) - PV)
    let Zperp : Matrix (Fin m1) (Fin m2) ℝ :=
      Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)
    let V0 : Matrix (Fin m1) (Fin m2) ℝ := U * V.transpose + Zperp
    (U.transpose * Zperp = 0 ∧
      Zperp * V = 0 ∧
      Statlib.HighDim.MatrixAnalysis.opNorm Zperp ≤ 1 ∧
      frobInner Zperp H = Statlib.HighDim.Vocabulary.nuclearNorm Hperp) ∧
    (Statlib.HighDim.MatrixAnalysis.opNorm V0 ≤ 1 ∧
      frobInner V0 M = Statlib.HighDim.Vocabulary.nuclearNorm M ∧
      (∀ A : Matrix (Fin m1) (Fin m2) ℝ,
        frobInner V0 A ≤ Statlib.HighDim.Vocabulary.nuclearNorm A)) ∧
    (frobNorm (U * V.transpose) = Real.sqrt (Matrix.rank M : ℝ) ∧
      frobInner V0 H ≥
        -(Real.sqrt (Matrix.rank M : ℝ)) * frobNorm H +
          Statlib.HighDim.Vocabulary.nuclearNorm Hperp) := by
  /- @proof-region region.target-node.session.1806b6b66bcb999a begin -/
  intro m1 m2 M svd H
  dsimp only
  intro svd_perp
  have hpolar := (statopia_math_node_791349827_8cd9ad5e m1 m2 0 0 0 _ 0).2.2.2.2.2.1 svd_perp
  have hAU := statopia_math_node_2330588687_1f4ea849 m1 m2 M H svd svd_perp
  have h1 : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd) *
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) = 0 := hAU.1
  have h2 : (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
      Statlib.HighDim.MatrixAnalysis.svdPosV svd = 0 := hAU.2
  have h4 : frobInner
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) H =
      Statlib.HighDim.Vocabulary.nuclearNorm
        ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) * H *
          (1 - Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))) := by
    have hPTH :
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) * H +
          (1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) * H *
            (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) =
        H - ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) * H *
          (1 - Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))) :=
      ((statopia_math_node_2628551730_d82d74eb m1 m2 M svd H H 0 H).2.2.2.1).symm
    have hsadj : frobInner
        ((Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) -
          (1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) *
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
            (1 - Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))) H =
        frobInner
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))
          (H - ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) * H *
            (1 - Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)))) :=
      (statopia_math_node_2628551730_d82d74eb m1 m2 M svd
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) H 0 H).2.2.2.2.2.2.1
    have hPTZ :
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) -
            (1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) *
              (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
              (1 - Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) =
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) *
              (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) +
            (1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) *
              (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
              (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) :=
      (statopia_math_node_2628551730_d82d74eb m1 m2 M svd
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) H 0 H).2.2.2.1
    have e1 :
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) *
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) = 0 := by
      rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
    have hZV :
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) = 0 := by
      rw [← Matrix.mul_assoc, h2, Matrix.zero_mul]
    have e2 :
        (1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) *
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
            (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) = 0 := by
      rw [Matrix.mul_assoc, hZV, Matrix.mul_zero]
    have hsub : ∀ X A B : Matrix (Fin m1) (Fin m2) ℝ,
        frobInner X (A - B) = frobInner X A - frobInner X B := by
      intro X A B
      simp [frobInner, Finset.sum_sub_distrib, mul_sub]
    have hkey : frobInner
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))
        (H - ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) * H *
          (1 - Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)))) = 0 := by
      rw [← hsadj, hPTZ, e1, e2, add_zero]
      simp [frobInner]
    have hb : frobInner
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))
        (H - ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) * H *
          (1 - Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)))) =
        frobInner
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) H -
          frobInner
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))
            ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) * H *
              (1 - Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))) :=
      hsub _ H _
    linarith [hb, hkey, hpolar.2]
  have hmem :
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) ∈
        Statlib.HighDim.MatrixAnalysis.nuclearNormSubdifferential M := by
    rw [(Statlib.HighDim.MatrixAnalysis.fenchel_dual_nuclear_norm_prox m1 m2 0 1 one_pos).2 M svd]
    exact ⟨_, rfl, h1, h2, hpolar.1⟩
  have horth : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
      (s : Statlib.HighDim.Vocabulary.SVD A),
      (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU s) *
          Statlib.HighDim.MatrixAnalysis.svdPosU s = 1) ∧
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s) *
          Statlib.HighDim.MatrixAnalysis.svdPosV s = 1) := by
    intro m n A s
    have h := statopia_math_node_3825179525_37ca31cf m n A s
      (Classical.choice (Statlib.HighDim.MatrixAnalysis.svd_exists _))
    exact ⟨h.1, h.2.1⟩
  have horthU : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd) *
      Statlib.HighDim.MatrixAnalysis.svdPosU svd = 1 := (horth m1 m2 M svd).1
  have horthV : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) *
      Statlib.HighDim.MatrixAnalysis.svdPosV svd = 1 := (horth m1 m2 M svd).2
  have horthUp : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp) *
      Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp = 1 := (horth m1 m2 _ svd_perp).1
  have horthVp : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp) *
      Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp = 1 := (horth m1 m2 _ svd_perp).2
  have hopV0 : Statlib.HighDim.MatrixAnalysis.opNorm
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) ≤ 1 := by
    have h1t : Matrix.transpose
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
        Statlib.HighDim.MatrixAnalysis.svdPosU svd = 0 := by
      have h := congrArg Matrix.transpose h1
      simpa [Matrix.transpose_mul] using h
    have hXX : Matrix.transpose
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) *
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) =
        Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [Matrix.mul_assoc (Statlib.HighDim.MatrixAnalysis.svdPosV svd)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd))
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))]
      rw [← Matrix.mul_assoc (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd))
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)),
        horthU, Matrix.one_mul]
    have hXZ : Matrix.transpose
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) *
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) = 0 := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [Matrix.mul_assoc (Statlib.HighDim.MatrixAnalysis.svdPosV svd)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd))
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)),
        h1, Matrix.mul_zero]
    have hZX : Matrix.transpose
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) = 0 := by
      rw [← Matrix.mul_assoc (Matrix.transpose
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)))
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)),
        h1t, Matrix.zero_mul]
    have hZZ : Matrix.transpose
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) =
        Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp) := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [Matrix.mul_assoc (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp))
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))]
      rw [← Matrix.mul_assoc (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp))
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)),
        horthUp, Matrix.one_mul]
    have hV0sq : Matrix.transpose
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) *
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) =
        Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) := by
      rw [Matrix.transpose_add]
      simp only [Matrix.add_mul, Matrix.mul_add, hXX, hXZ, hZX, hZZ, add_zero, zero_add]
    have hPsym : Matrix.transpose
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) =
        Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    have hQsym : Matrix.transpose
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) =
        Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp) := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    have hPsq : (Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) *
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) =
        Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) := by
      rw [Matrix.mul_assoc (Statlib.HighDim.MatrixAnalysis.svdPosV svd)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))]
      rw [← Matrix.mul_assoc (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)),
        horthV, Matrix.one_mul]
    have hQsq : (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) =
        Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp) := by
      rw [Matrix.mul_assoc (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))]
      rw [← Matrix.mul_assoc (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)),
        horthVp, Matrix.one_mul]
    have hVptV : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp) *
        Statlib.HighDim.MatrixAnalysis.svdPosV svd = 0 := by
      have h2a : Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp) *
            Statlib.HighDim.MatrixAnalysis.svdPosV svd) = 0 := by
        rw [← Matrix.mul_assoc]
        exact h2
      have hb := congrArg (fun M => Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp) * M) h2a
      simp only [Matrix.mul_zero] at hb
      rw [← Matrix.mul_assoc (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp))
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp) *
          Statlib.HighDim.MatrixAnalysis.svdPosV svd), horthUp, Matrix.one_mul] at hb
      exact hb
    have hVtVp : Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) *
        Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp = 0 := by
      have h := congrArg Matrix.transpose hVptV
      simpa [Matrix.transpose_mul] using h
    have hPQ : (Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) *
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) = 0 := by
      rw [Matrix.mul_assoc (Statlib.HighDim.MatrixAnalysis.svdPosV svd)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))]
      rw [← Matrix.mul_assoc (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)
        (Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)),
        hVtVp, Matrix.zero_mul, Matrix.mul_zero]
    have hQP : (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) *
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) = 0 := by
      have h := congrArg Matrix.transpose hPQ
      simpa [Matrix.transpose_mul] using h
    have hRsq : Matrix.transpose
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) *
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) =
        Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) := by
      rw [Matrix.transpose_add, hPsym, hQsym]
      simp only [Matrix.add_mul, Matrix.mul_add, hPsq, hPQ, hQP, hQsq, add_zero, zero_add]
    have hconj : ∀ A : Matrix (Fin m1) (Fin m2) ℝ,
        Matrix.conjTranspose A = Matrix.transpose A := by
      intro A
      ext i j
      simp
    have hsq1 : Statlib.HighDim.MatrixAnalysis.opNorm
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) *
        Statlib.HighDim.MatrixAnalysis.opNorm
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) =
        Statlib.HighDim.MatrixAnalysis.opNorm
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) := by
      rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))),
        Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))),
        ← Matrix.l2_opNorm_conjTranspose_mul_self
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)))]
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial, hV0sq]
    have hsq2 : Statlib.HighDim.MatrixAnalysis.opNorm
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) *
        Statlib.HighDim.MatrixAnalysis.opNorm
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) =
        Statlib.HighDim.MatrixAnalysis.opNorm
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) := by
      rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))),
        ← Matrix.l2_opNorm_conjTranspose_mul_self
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)))]
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial, hRsq]
    have hd1 : Statlib.HighDim.MatrixAnalysis.opNorm
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) ≤ 1 := by
      have h0 := Statlib.HighDim.MatrixAnalysis.opNorm_nonneg
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)))
      nlinarith [hsq2, h0, sq_nonneg (Statlib.HighDim.MatrixAnalysis.opNorm
        (Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) - 1)]
    have h0 := Statlib.HighDim.MatrixAnalysis.opNorm_nonneg
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)))
    nlinarith [hsq1, hd1, h0, sq_nonneg (Statlib.HighDim.MatrixAnalysis.opNorm
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) - 1)]
  have hbridge : ∀ A B : Matrix (Fin m1) (Fin m2) ℝ,
      Statlib.HighDim.MatrixAnalysis.traceInner A B = frobInner A B := by
    intro A B
    calc Statlib.HighDim.MatrixAnalysis.traceInner A B
        = ∑ i : Fin m2, ∑ k : Fin m1, A k i * B k i := rfl
      _ = ∑ k : Fin m1, ∑ i : Fin m2, A k i * B k i := Finset.sum_comm
      _ = frobInner A B := rfl
  have hfrobV0M : frobInner
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) M =
      Statlib.HighDim.Vocabulary.nuclearNorm M := by
    have hz0 : Statlib.HighDim.Vocabulary.nuclearNorm (0 : Matrix (Fin m1) (Fin m2) ℝ) = 0 :=
      (Statlib.HighDim.MatrixAnalysis.nuclearNorm_nonneg 0).2.mpr rfl
    have hzero : frobInner
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) (0 - M) =
        -frobInner
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) M := by
      simp [frobInner, mul_sub, Finset.sum_sub_distrib]
    have hge : Statlib.HighDim.Vocabulary.nuclearNorm M ≤ frobInner
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) M := by
      have hz := hmem (0 : Matrix (Fin m1) (Fin m2) ℝ)
      have hz' : Statlib.HighDim.Vocabulary.nuclearNorm M + frobInner
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) (0 - M) ≤ 0 := by
        simpa only [hbridge, hz0] using hz
      rw [hzero] at hz'
      linarith
    have hle : frobInner
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) M ≤
        Statlib.HighDim.Vocabulary.nuclearNorm M := by
      have hz := hmem (M + M)
      have hMM : M + M - M = M := by abel
      have hadd := Statlib.HighDim.MatrixAnalysis.nuclearNorm_add_le M M
      have htr : Statlib.HighDim.Vocabulary.nuclearNorm M + Statlib.HighDim.MatrixAnalysis.traceInner
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) (M + M - M) ≤
          Statlib.HighDim.Vocabulary.nuclearNorm M + Statlib.HighDim.Vocabulary.nuclearNorm M :=
        le_trans hz hadd
      have hz' : Statlib.HighDim.Vocabulary.nuclearNorm M + frobInner
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
            (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
              Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) M ≤
          Statlib.HighDim.Vocabulary.nuclearNorm M + Statlib.HighDim.Vocabulary.nuclearNorm M := by
        simpa only [hMM, hbridge] using htr
      linarith
    linarith
  have hfenchel : ∀ A : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
          (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
            Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) A ≤
        Statlib.HighDim.Vocabulary.nuclearNorm A := by
    intro A
    exact (statopia_math_node_791349827_8cd9ad5e m1 m2 0 0
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) A 0).2.1 hopV0
  have hfrobUV : frobNorm (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) = Real.sqrt ((M.rank : ℕ) : ℝ) :=
    statopia_math_node_1491593895_e4edda66 m1 m2 M svd
  have hlast : frobInner
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd) +
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp *
          Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp))) H ≥
      -(Real.sqrt ((M.rank : ℕ) : ℝ)) * frobNorm H +
        Statlib.HighDim.Vocabulary.nuclearNorm
          ((1 - Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosU svd)) * H *
            (1 - Statlib.HighDim.MatrixAnalysis.svdPosV svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))) := by
    have hadd : ∀ A B X : Matrix (Fin m1) (Fin m2) ℝ,
        frobInner (A + B) X = frobInner A X + frobInner B X := by
      intro A B X
      simp [frobInner, add_mul, Finset.sum_add_distrib]
    have hcs : ∀ A B : Matrix (Fin m1) (Fin m2) ℝ, -(frobNorm A * frobNorm B) ≤ frobInner A B := by
      intro A B
      have hconv : ∀ (F : Fin m1 → Fin m2 → ℝ),
          (∑ p : Fin m1 × Fin m2, F p.1 p.2) = ∑ i, ∑ j, F i j := by
        intro F
        rw [← Finset.sum_product']
        simp
      have hsq : (frobInner A B) ^ 2 ≤
          (∑ i : Fin m1, ∑ j : Fin m2, A i j ^ 2) * (∑ i : Fin m1, ∑ j : Fin m2, B i j ^ 2) := by
        have h0 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m1 × Fin m2))
          (fun p : Fin m1 × Fin m2 => A p.1 p.2) (fun p : Fin m1 × Fin m2 => B p.1 p.2)
        rw [hconv (fun i j => A i j * B i j), hconv (fun i j => A i j ^ 2),
          hconv (fun i j => B i j ^ 2)] at h0
        simpa [frobInner] using h0
      have hA : 0 ≤ ∑ i : Fin m1, ∑ j : Fin m2, A i j ^ 2 :=
        Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
      have hB : 0 ≤ ∑ i : Fin m1, ∑ j : Fin m2, B i j ^ 2 :=
        Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
      have hK : 0 ≤ Real.sqrt ((∑ i : Fin m1, ∑ j : Fin m2, A i j ^ 2) *
          (∑ i : Fin m1, ∑ j : Fin m2, B i j ^ 2)) := Real.sqrt_nonneg _
      have habs_sq : |frobInner A B| ^ 2 ≤
          (Real.sqrt ((∑ i : Fin m1, ∑ j : Fin m2, A i j ^ 2) *
            (∑ i : Fin m1, ∑ j : Fin m2, B i j ^ 2))) ^ 2 := by
        rw [sq_abs, Real.sq_sqrt (mul_nonneg hA hB)]
        exact hsq
      have habs : |frobInner A B| ≤
          Real.sqrt ((∑ i : Fin m1, ∑ j : Fin m2, A i j ^ 2) *
            (∑ i : Fin m1, ∑ j : Fin m2, B i j ^ 2)) := by
        rw [← Real.sqrt_sq (abs_nonneg (frobInner A B)), ← Real.sqrt_sq hK]
        exact Real.sqrt_le_sqrt habs_sq
      have hnorm : frobNorm A * frobNorm B =
          Real.sqrt ((∑ i : Fin m1, ∑ j : Fin m2, A i j ^ 2) *
            (∑ i : Fin m1, ∑ j : Fin m2, B i j ^ 2)) := by
        simp only [frobNorm]
        rw [← Real.sqrt_mul hA]
      rw [hnorm]
      exact (abs_le.mp habs).1
    have hsplit := hadd
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd))
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp)) H
    have hb := hcs
      (Statlib.HighDim.MatrixAnalysis.svdPosU svd * Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd)) H
    rw [hfrobUV] at hb
    linarith [hsplit, hb, h4]
  exact ⟨⟨h1, h2, hpolar.1, h4⟩, ⟨hopV0, hfrobV0M, hfenchel⟩, hfrobUV, hlast⟩
  /- @proof-region region.target-node.session.1806b6b66bcb999a end -/

end Statlib.Imported

