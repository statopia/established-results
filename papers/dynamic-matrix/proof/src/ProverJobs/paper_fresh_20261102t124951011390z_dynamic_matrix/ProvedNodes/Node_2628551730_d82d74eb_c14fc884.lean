import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
import Statlib.HighDim.MatrixAnalysis.NuclearNormLeSqrtRank
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.Vocabulary.Norms
import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_785978934_83e7885c_53410516
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_791349827_8cd9ad5e_a51ab6c3

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix

open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_2628551730_d82d74eb : ∀ (m1 m2 : ℕ) (M : Matrix (Fin m1) (Fin m2) ℝ)
    (svd : Statlib.HighDim.Vocabulary.SVD M)
    (A C E H : Matrix (Fin m1) (Fin m2) ℝ),
    let U := Statlib.HighDim.MatrixAnalysis.svdPosU svd
    let V := Statlib.HighDim.MatrixAnalysis.svdPosV svd
    let PU : Matrix (Fin m1) (Fin m1) ℝ := U * U.transpose
    let PV : Matrix (Fin m2) (Fin m2) ℝ := V * V.transpose
    let Pperp : Matrix (Fin m1) (Fin m2) ℝ → Matrix (Fin m1) (Fin m2) ℝ :=
      fun X => ((1 : Matrix (Fin m1) (Fin m1) ℝ) - PU) * X *
        ((1 : Matrix (Fin m2) (Fin m2) ℝ) - PV)
    let PT : Matrix (Fin m1) (Fin m2) ℝ → Matrix (Fin m1) (Fin m2) ℝ := fun X => X - Pperp X
    (frobInner (PT A) (Pperp C) = 0 ∧
      frobInner A C = frobInner (PT A) (PT C) + frobInner (Pperp A) (Pperp C) ∧
      PT A + Pperp A = A ∧
      PT A = PU * A + ((1 : Matrix (Fin m1) (Fin m1) ℝ) - PU) * A * PV ∧
      PT (PT A) = PT A ∧
      Pperp (Pperp A) = Pperp A ∧
      frobInner (PT A) C = frobInner A (PT C) ∧
      frobInner (Pperp A) C = frobInner A (Pperp C) ∧
      frobNorm (PT A) ≤ frobNorm A ∧
      frobNorm (Pperp A) ≤ frobNorm A ∧
      frobNorm (PT E) ≤
        Real.sqrt (2 * (Matrix.rank M : ℝ)) * Statlib.HighDim.MatrixAnalysis.opNorm E ∧
      frobInner E H ≤
        Real.sqrt (2 * (Matrix.rank M : ℝ)) * Statlib.HighDim.MatrixAnalysis.opNorm E *
            frobNorm H +
          Statlib.HighDim.MatrixAnalysis.opNorm E *
            Statlib.HighDim.Vocabulary.nuclearNorm (Pperp H)) := by
  /- @proof-region region.target-node.session.79ea84ee4dd52ac2 begin -/
  intro m1 m2 M svd A C E H U V PU PV Pperp PT
  have hsvdUorth : ∀ {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
      (svd : Statlib.HighDim.Vocabulary.SVD A), svd.U.transpose * svd.U = 1 := by
    intro m n A svd
    obtain ⟨u, v, sg, hu, hv, hoff, hnonneg, hdecomp⟩ := svd
    exact hu
  have hsvdVorth : ∀ {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
      (svd : Statlib.HighDim.Vocabulary.SVD A), svd.V.transpose * svd.V = 1 := by
    intro m n A svd
    obtain ⟨u, v, sg, hu, hv, hoff, hnonneg, hdecomp⟩ := svd
    exact hv
  have hUtU : U.transpose * U = 1 := by
    have hfull : ∀ a b : Fin m1,
        (∑ j, svd.U j a * svd.U j b) = (if a = b then (1 : ℝ) else 0) := by
      intro a b
      have h1 := congrFun (congrFun (hsvdUorth svd) a) b
      rw [Matrix.mul_apply, Matrix.one_apply] at h1
      simpa only [Matrix.transpose_apply] using h1
    ext k k'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    dsimp only [U]
    simp only [Statlib.HighDim.MatrixAnalysis.svdPosU, Matrix.submatrix_apply, id_eq]
    rw [hfull]
    simp [Fin.ext_iff, Subtype.ext_iff]
  have hVtV : V.transpose * V = 1 := by
    have hfull : ∀ a b : Fin m2,
        (∑ j, svd.V j a * svd.V j b) = (if a = b then (1 : ℝ) else 0) := by
      intro a b
      have h1 := congrFun (congrFun (hsvdVorth svd) a) b
      rw [Matrix.mul_apply, Matrix.one_apply] at h1
      simpa only [Matrix.transpose_apply] using h1
    ext k k'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    dsimp only [V]
    simp only [Statlib.HighDim.MatrixAnalysis.svdPosV, Matrix.submatrix_apply, id_eq]
    rw [hfull]
    simp [Fin.ext_iff, Subtype.ext_iff]
  have hPUsym : PU.transpose = PU := by
    show (U * U.transpose).transpose = U * U.transpose
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPVsym : PV.transpose = PV := by
    show (V * V.transpose).transpose = V * V.transpose
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPUsq : PU * PU = PU := by
    show (U * U.transpose) * (U * U.transpose) = U * U.transpose
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.transpose U U.transpose]
    rw [hUtU, Matrix.one_mul]
  have hPVsq : PV * PV = PV := by
    show (V * V.transpose) * (V * V.transpose) = V * V.transpose
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V.transpose V V.transpose]
    rw [hVtV, Matrix.one_mul]
  have hPU1 : PU * (1 - PU) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPUsq, sub_self]
  have hPU2 : (1 - PU) * PU = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPUsq, sub_self]
  have hPUcomp : (1 - PU) * (1 - PU) = 1 - PU := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPUsq]
    abel
  have hPV1 : PV * (1 - PV) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPVsq, sub_self]
  have hPV2 : (1 - PV) * PV = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPVsq, sub_self]
  have hPVcomp : (1 - PV) * (1 - PV) = 1 - PV := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPVsq]
    abel
  have hFrobInnerTrace : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner X Y = (X.transpose * Y).trace := by
    intro X Y
    have h1 : frobInner X Y = ∑ i : Fin m1, ∑ j : Fin m2, X i j * Y i j := rfl
    have h2 : (X.transpose * Y).trace
        = ∑ i : Fin m2, ∑ j : Fin m1, X j i * Y j i := rfl
    rw [h1, h2]
    conv_rhs => rw [Finset.sum_comm]
  have hAdjL : ∀ (B : Matrix (Fin m1) (Fin m1) ℝ) (X Y : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner (B * X) Y = frobInner X (B.transpose * Y) := by
    intro B X Y
    rw [hFrobInnerTrace (B * X) Y, hFrobInnerTrace X (B.transpose * Y)]
    rw [Matrix.transpose_mul]
    rw [Matrix.mul_assoc]
  have hAdjR : ∀ (B : Matrix (Fin m2) (Fin m2) ℝ) (X Y : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner (X * B) Y = frobInner X (Y * B.transpose) := by
    intro B X Y
    rw [hFrobInnerTrace (X * B) Y, hFrobInnerTrace X (Y * B.transpose)]
    rw [Matrix.transpose_mul]
    rw [Matrix.trace_mul_cycle' X.transpose Y B.transpose]
    rw [Matrix.mul_assoc]
  have hInnerAddL : ∀ X1 X2 Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner (X1 + X2) Y = frobInner X1 Y + frobInner X2 Y := by
    intro X1 X2 Y
    simp [frobInner, add_mul, Finset.sum_add_distrib]
  have hInnerAddR : ∀ X Y1 Y2 : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner X (Y1 + Y2) = frobInner X Y1 + frobInner X Y2 := by
    intro X Y1 Y2
    simp [frobInner, mul_add, Finset.sum_add_distrib]
  have hInnerZeroR : ∀ X : Matrix (Fin m1) (Fin m2) ℝ, frobInner X 0 = 0 := by
    intro X
    simp [frobInner]
  have hInnerComm : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ, frobInner X Y = frobInner Y X := by
    intro X Y
    simp [frobInner, mul_comm]
  have hPUcSym : (1 - PU).transpose = 1 - PU := by
    rw [show (1 - PU).transpose
        = (1 : Matrix (Fin m1) (Fin m1) ℝ).transpose - PU.transpose from rfl,
      Matrix.transpose_one, hPUsym]
  have hPVcSym : (1 - PV).transpose = 1 - PV := by
    rw [show (1 - PV).transpose
        = (1 : Matrix (Fin m2) (Fin m2) ℝ).transpose - PV.transpose from rfl,
      Matrix.transpose_one, hPVsym]
  have hAdjPU : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner (PU * X) Y = frobInner X (PU * Y) := by
    intro X Y
    rw [hAdjL PU X Y, hPUsym]
  have hAdjPV : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner (X * PV) Y = frobInner X (Y * PV) := by
    intro X Y
    rw [hAdjR PV X Y, hPVsym]
  have hAdjPUc : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner ((1 - PU) * X) Y = frobInner X ((1 - PU) * Y) := by
    intro X Y
    rw [hAdjL (1 - PU) X Y, hPUcSym]
  have hAdjPVc : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner (X * (1 - PV)) Y = frobInner X (Y * (1 - PV)) := by
    intro X Y
    rw [hAdjR (1 - PV) X Y, hPVcSym]
  have hSumX : ∀ X : Matrix (Fin m1) (Fin m2) ℝ, PT X + Pperp X = X := by
    intro X
    show X - Pperp X + Pperp X = X
    abel
  have hPExp : ∀ X : Matrix (Fin m1) (Fin m2) ℝ,
      PT X = PU * X + (1 - PU) * X * PV := by
    intro X
    show X - (1 - PU) * X * (1 - PV) = PU * X + (1 - PU) * X * PV
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have hOrthAll : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner (PT X) (Pperp Y) = 0 := by
    intro X Y
    rw [hPExp X]
    show frobInner (PU * X + (1 - PU) * X * PV) ((1 - PU) * Y * (1 - PV)) = 0
    rw [hInnerAddL]
    have e1 : frobInner (PU * X) ((1 - PU) * Y * (1 - PV)) = 0 := by
      rw [hAdjPU X ((1 - PU) * Y * (1 - PV))]
      simp only [← Matrix.mul_assoc, hPU1, Matrix.zero_mul, hInnerZeroR]
    have e2 : frobInner ((1 - PU) * X * PV) ((1 - PU) * Y * (1 - PV)) = 0 := by
      rw [hAdjPV ((1 - PU) * X) ((1 - PU) * Y * (1 - PV)),
        hAdjPUc X (((1 - PU) * Y * (1 - PV)) * PV)]
      simp only [Matrix.mul_assoc, hPV2, Matrix.mul_zero, hInnerZeroR]
    rw [e1, e2, add_zero]
  have hOrth : frobInner (PT A) (Pperp C) = 0 := hOrthAll A C
  have hSplitAll : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner X Y = frobInner (PT X) (PT Y) + frobInner (Pperp X) (Pperp Y) := by
    intro X Y
    conv_lhs => rw [← hSumX X, ← hSumX Y]
    rw [hInnerAddL, hInnerAddR (PT X) (PT Y) (Pperp Y),
      hInnerAddR (Pperp X) (PT Y) (Pperp Y)]
    rw [hOrthAll X Y, hInnerComm (Pperp X) (PT Y), hOrthAll Y X]
    abel
  have hSplit : frobInner A C = frobInner (PT A) (PT C) + frobInner (Pperp A) (Pperp C) :=
    hSplitAll A C
  have hPTself : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner (PT X) Y = frobInner X (PT Y) := by
    intro X Y
    have hL : frobInner (PT X) Y
        = frobInner (PU * X) Y + frobInner ((1 - PU) * X * PV) Y := by
      rw [hPExp X, hInnerAddL]
    have hR : frobInner X (PT Y)
        = frobInner X (PU * Y) + frobInner X ((1 - PU) * Y * PV) := by
      rw [hPExp Y, hInnerAddR]
    rw [hL, hR, hAdjPU X Y, hAdjPV ((1 - PU) * X) Y, hAdjPUc X (Y * PV),
      Matrix.mul_assoc (1 - PU) Y PV]
  have hPerpSelf : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner (Pperp X) Y = frobInner X (Pperp Y) := by
    intro X Y
    show frobInner ((1 - PU) * X * (1 - PV)) Y
        = frobInner X ((1 - PU) * Y * (1 - PV))
    rw [hAdjPVc ((1 - PU) * X) Y, hAdjPUc X (Y * (1 - PV)), Matrix.mul_assoc]
  have hPUabsorb : ∀ Y : Matrix (Fin m1) (Fin m2) ℝ, PU * (PU * Y) = PU * Y := by
    intro Y
    rw [← Matrix.mul_assoc, hPUsq]
  have hPUcabsorb : ∀ Y : Matrix (Fin m1) (Fin m2) ℝ,
      (1 - PU) * ((1 - PU) * Y) = (1 - PU) * Y := by
    intro Y
    rw [← Matrix.mul_assoc, hPUcomp]
  have hPUkill1 : ∀ Y : Matrix (Fin m1) (Fin m2) ℝ, PU * ((1 - PU) * Y) = 0 := by
    intro Y
    rw [← Matrix.mul_assoc, hPU1, Matrix.zero_mul]
  have hPUkill2 : ∀ Y : Matrix (Fin m1) (Fin m2) ℝ, (1 - PU) * (PU * Y) = 0 := by
    intro Y
    rw [← Matrix.mul_assoc, hPU2, Matrix.zero_mul]
  have hPTidem : ∀ X : Matrix (Fin m1) (Fin m2) ℝ, PT (PT X) = PT X := by
    intro X
    rw [hPExp (PT X), hPExp X]
    show PU * (PU * X + (1 - PU) * X * PV) + (1 - PU) * (PU * X + (1 - PU) * X * PV) * PV
        = PU * X + (1 - PU) * X * PV
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, hPUabsorb, hPUcabsorb, hPUkill1, hPUkill2, hPVsq, hPVcomp]
  have hPerpIdem : ∀ X : Matrix (Fin m1) (Fin m2) ℝ, Pperp (Pperp X) = Pperp X := by
    intro X
    show (1 - PU) * ((1 - PU) * X * (1 - PV)) * (1 - PV) = (1 - PU) * X * (1 - PV)
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, hPUabsorb, hPUcabsorb, hPUkill1, hPUkill2, hPVsq, hPVcomp]
  have hFrobNormSq : ∀ X : Matrix (Fin m1) (Fin m2) ℝ,
      frobNorm X = Real.sqrt (frobInner X X) := by
    intro X
    simp [frobNorm, frobInner, sq]
  have hInnerSelfNonneg : ∀ X : Matrix (Fin m1) (Fin m2) ℝ, 0 ≤ frobInner X X := by
    intro X
    simp only [frobInner, ← sq]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (X i j)))
  have hFrobNormNonneg : ∀ X : Matrix (Fin m1) (Fin m2) ℝ, 0 ≤ frobNorm X := by
    intro X
    rw [hFrobNormSq X]
    exact Real.sqrt_nonneg _
  have hNormPT : ∀ X : Matrix (Fin m1) (Fin m2) ℝ, frobNorm (PT X) ≤ frobNorm X := by
    intro X
    rw [hFrobNormSq (PT X), hFrobNormSq X]
    apply Real.sqrt_le_sqrt
    rw [hSplitAll X X]
    linarith [hInnerSelfNonneg (Pperp X)]
  have hNormPerp : ∀ X : Matrix (Fin m1) (Fin m2) ℝ, frobNorm (Pperp X) ≤ frobNorm X := by
    intro X
    rw [hFrobNormSq (Pperp X), hFrobNormSq X]
    apply Real.sqrt_le_sqrt
    rw [hSplitAll X X]
    linarith [hInnerSelfNonneg (PT X)]
  have hNorm1 : frobNorm (PT A) ≤ frobNorm A := hNormPT A
  have hNorm2 : frobNorm (Pperp A) ≤ frobNorm A := hNormPerp A
  have hCSone : ∀ (s A' B' : ℝ), s ^ 2 ≤ A' * B' → 0 ≤ A' → 0 ≤ B' →
      s ≤ Real.sqrt A' * Real.sqrt B' := by
    intro s A' B' hsq hA hB
    have h1 : Real.sqrt (s ^ 2) ≤ Real.sqrt (A' * B') := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs] at h1
    have h2 : s ≤ |s| := le_abs_self s
    rw [← Real.sqrt_mul hA B']
    linarith
  have hCS : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ, frobInner X Y ≤ frobNorm X * frobNorm Y := by
    intro X Y
    have hstep1 : ∀ i : Fin m1, (∑ j : Fin m2, X i j * Y i j) ≤
        Real.sqrt (∑ j : Fin m2, X i j ^ 2) * Real.sqrt (∑ j : Fin m2, Y i j ^ 2) := by
      intro i
      refine hCSone _ _ _ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => X i j)
        (fun j => Y i j)) ?_ ?_
      · exact Finset.sum_nonneg (fun j _ => sq_nonneg (X i j))
      · exact Finset.sum_nonneg (fun j _ => sq_nonneg (Y i j))
    have hstep2 : (∑ i : Fin m1, Real.sqrt (∑ j : Fin m2, X i j ^ 2) *
          Real.sqrt (∑ j : Fin m2, Y i j ^ 2)) ≤
        Real.sqrt (∑ i : Fin m1, ∑ j : Fin m2, X i j ^ 2) *
          Real.sqrt (∑ i : Fin m1, ∑ j : Fin m2, Y i j ^ 2) := by
      have hsumX : (∑ i : Fin m1, Real.sqrt (∑ j : Fin m2, X i j ^ 2) ^ 2)
          = ∑ i : Fin m1, ∑ j : Fin m2, X i j ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (X i j)))
      have hsumY : (∑ i : Fin m1, Real.sqrt (∑ j : Fin m2, Y i j ^ 2) ^ 2)
          = ∑ i : Fin m1, ∑ j : Fin m2, Y i j ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (Y i j)))
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : Fin m1 => Real.sqrt (∑ j : Fin m2, X i j ^ 2))
        (fun i : Fin m1 => Real.sqrt (∑ j : Fin m2, Y i j ^ 2))
      rw [hsumX, hsumY] at h
      exact hCSone _ _ _ h
        (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (X i j))))
        (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (Y i j))))
    have h1 : frobInner X Y ≤ ∑ i : Fin m1, Real.sqrt (∑ j : Fin m2, X i j ^ 2) *
        Real.sqrt (∑ j : Fin m2, Y i j ^ 2) := by
      rw [frobInner]
      exact Finset.sum_le_sum (fun i _ => hstep1 i)
    have h2 : frobNorm X = Real.sqrt (∑ i : Fin m1, ∑ j : Fin m2, X i j ^ 2) := rfl
    have h3 : frobNorm Y = Real.sqrt (∑ i : Fin m1, ∑ j : Fin m2, Y i j ^ 2) := rfl
    rw [h2, h3]
    linarith
  have hBlockOrth : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ,
      frobInner (PU * X) ((1 - PU) * Y * PV) = 0 := by
    intro X Y
    rw [hAdjPU X ((1 - PU) * Y * PV)]
    simp only [← Matrix.mul_assoc, hPUkill1, Matrix.zero_mul, hInnerZeroR]
  have hBlockSq : frobNorm (PT E) * frobNorm (PT E)
      = frobNorm (PU * E) * frobNorm (PU * E)
        + frobNorm ((1 - PU) * E * PV) * frobNorm ((1 - PU) * E * PV) := by
    have h1 : frobNorm (PT E) * frobNorm (PT E) = frobInner (PT E) (PT E) := by
      rw [hFrobNormSq (PT E), ← sq]
      exact Real.sq_sqrt (hInnerSelfNonneg (PT E))
    have h2 : frobNorm (PU * E) * frobNorm (PU * E) = frobInner (PU * E) (PU * E) := by
      rw [hFrobNormSq (PU * E), ← sq]
      exact Real.sq_sqrt (hInnerSelfNonneg (PU * E))
    have h3 : frobNorm ((1 - PU) * E * PV) * frobNorm ((1 - PU) * E * PV)
        = frobInner ((1 - PU) * E * PV) ((1 - PU) * E * PV) := by
      rw [hFrobNormSq ((1 - PU) * E * PV), ← sq]
      exact Real.sq_sqrt (hInnerSelfNonneg ((1 - PU) * E * PV))
    rw [h1, h2, h3, hPExp E, hInnerAddL,
      hInnerAddR (PU * E) (PU * E) ((1 - PU) * E * PV),
      hInnerAddR ((1 - PU) * E * PV) (PU * E) ((1 - PU) * E * PV),
      hBlockOrth E E, hInnerComm ((1 - PU) * E * PV) (PU * E), hBlockOrth E E]
    abel
  have hEW1 : frobInner (PU * E) (PU * E) = frobInner E (PU * E) := by
    rw [hAdjPU E (PU * E), hPUabsorb E]
  have hEW2 : frobInner ((1 - PU) * E * PV) ((1 - PU) * E * PV)
      = frobInner E ((1 - PU) * E * PV) := by
    rw [hAdjPV ((1 - PU) * E) ((1 - PU) * E * PV),
      hAdjPUc E (((1 - PU) * E * PV) * PV)]
    simp only [Matrix.mul_assoc, hPVsq, hPUcabsorb]
  have hRankE : Matrix.rank (PU * E) ≤ Matrix.rank M := by
    have h1 : Matrix.rank (PU * E) ≤ Matrix.rank U := by
      have h : PU * E = U * (U.transpose * E) := by
        show (U * U.transpose) * E = U * (U.transpose * E)
        rw [Matrix.mul_assoc]
      rw [h]
      exact Matrix.rank_mul_le_left U (U.transpose * E)
    exact le_trans h1 (statopia_math_node_785978934_83e7885c m1 m2 M svd).1
  have hRankF : Matrix.rank ((1 - PU) * E * PV) ≤ Matrix.rank M := by
    have h1 : Matrix.rank ((1 - PU) * E * PV) ≤ Matrix.rank PV :=
      Matrix.rank_mul_le_right ((1 - PU) * E) PV
    have h2 : Matrix.rank PV ≤ Matrix.rank V := by
      have h : PV = V * V.transpose := rfl
      rw [h]
      exact Matrix.rank_mul_le_left V V.transpose
    exact le_trans h1 (le_trans h2 (statopia_math_node_785978934_83e7885c m1 m2 M svd).2)
  have hBridge : ∀ X : Matrix (Fin m1) (Fin m2) ℝ,
      Statlib.HighDim.MatrixAnalysis.frobeniusNorm X = frobNorm X := by
    intro X
    simp [Statlib.HighDim.MatrixAnalysis.frobeniusNorm, frobNorm,
      Statlib.HighDim.Vocabulary.frobeniusNormSq]
  have hBlockBound : ∀ W : Matrix (Fin m1) (Fin m2) ℝ, Matrix.rank W ≤ Matrix.rank M →
      frobInner W W = frobInner E W →
      frobNorm W ≤ Real.sqrt (Matrix.rank M : ℝ) *
        Statlib.HighDim.MatrixAnalysis.opNorm E := by
    intro W hW hEW
    have hnn : 0 ≤ frobNorm W := hFrobNormNonneg W
    have hsq : frobNorm W * frobNorm W = frobInner W W := by
      rw [hFrobNormSq W, ← sq]
      exact Real.sq_sqrt (hInnerSelfNonneg W)
    have hpair : frobInner E W ≤ Statlib.HighDim.MatrixAnalysis.opNorm E *
        Statlib.HighDim.Vocabulary.nuclearNorm W :=
      (statopia_math_node_791349827_8cd9ad5e m1 m2 E W 0 0 0).2.2.2.1
    have hnucl : Statlib.HighDim.Vocabulary.nuclearNorm W ≤
        Real.sqrt (Matrix.rank W : ℝ) * frobNorm W := by
      have h := Statlib.HighDim.MatrixAnalysis.nuclear_norm_le_sqrt_rank_mul_frobenius W
      rwa [hBridge W] at h
    have hsqr : Real.sqrt (Matrix.rank W : ℝ) ≤ Real.sqrt (Matrix.rank M : ℝ) :=
      Real.sqrt_le_sqrt (Nat.cast_le.mpr hW)
    have hop : 0 ≤ Statlib.HighDim.MatrixAnalysis.opNorm E :=
      Statlib.HighDim.MatrixAnalysis.opNorm_nonneg E
    have hN : Statlib.HighDim.Vocabulary.nuclearNorm W ≤
        Real.sqrt (Matrix.rank M : ℝ) * frobNorm W :=
      le_trans hnucl (mul_le_mul_of_nonneg_right hsqr hnn)
    have hstep : frobNorm W * frobNorm W ≤ Statlib.HighDim.MatrixAnalysis.opNorm E *
        (Real.sqrt (Matrix.rank M : ℝ) * frobNorm W) := by
      rw [hsq, hEW]
      exact le_trans hpair (mul_le_mul_of_nonneg_left hN hop)
    rcases eq_or_lt_of_le hnn with h0 | hpos
    · rw [← h0]
      exact mul_nonneg (Real.sqrt_nonneg _) hop
    · refine le_of_mul_le_mul_right ?_ hpos
      calc frobNorm W * frobNorm W
          ≤ Statlib.HighDim.MatrixAnalysis.opNorm E *
              (Real.sqrt (Matrix.rank M : ℝ) * frobNorm W) := hstep
        _ = (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E) *
              frobNorm W := by ring
  have hItem2 : frobNorm (PT E) ≤
      Real.sqrt (2 * (M.rank : ℝ)) * Statlib.HighDim.MatrixAnalysis.opNorm E := by
    have hrank0 : (0 : ℝ) ≤ (Matrix.rank M : ℝ) := Nat.cast_nonneg (Matrix.rank M)
    have hsqr : Real.sqrt (Matrix.rank M : ℝ) * Real.sqrt (Matrix.rank M : ℝ)
        = (Matrix.rank M : ℝ) := by
      rw [← sq]
      exact Real.sq_sqrt hrank0
    have hb : (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E) *
        (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E)
        = (Matrix.rank M : ℝ) * (Statlib.HighDim.MatrixAnalysis.opNorm E *
            Statlib.HighDim.MatrixAnalysis.opNorm E) := by
      calc (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E) *
            (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E)
          = (Real.sqrt (Matrix.rank M : ℝ) * Real.sqrt (Matrix.rank M : ℝ)) *
              (Statlib.HighDim.MatrixAnalysis.opNorm E *
                Statlib.HighDim.MatrixAnalysis.opNorm E) := by ring
        _ = (Matrix.rank M : ℝ) * (Statlib.HighDim.MatrixAnalysis.opNorm E *
              Statlib.HighDim.MatrixAnalysis.opNorm E) := by rw [hsqr]
    have hbsq : (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E) *
        (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E)
        = (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E ^ 2 := by
      rw [hb, sq]
    have hop : 0 ≤ Statlib.HighDim.MatrixAnalysis.opNorm E :=
      Statlib.HighDim.MatrixAnalysis.opNorm_nonneg E
    have hb1 : frobNorm (PU * E) * frobNorm (PU * E) ≤
        (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E) *
          (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E) :=
      mul_le_mul (hBlockBound (PU * E) hRankE hEW1) (hBlockBound (PU * E) hRankE hEW1)
        (hFrobNormNonneg (PU * E)) (mul_nonneg (Real.sqrt_nonneg _) hop)
    have hb2 : frobNorm ((1 - PU) * E * PV) * frobNorm ((1 - PU) * E * PV) ≤
        (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E) *
          (Real.sqrt (Matrix.rank M : ℝ) * Statlib.HighDim.MatrixAnalysis.opNorm E) :=
      mul_le_mul (hBlockBound ((1 - PU) * E * PV) hRankF hEW2)
        (hBlockBound ((1 - PU) * E * PV) hRankF hEW2)
        (hFrobNormNonneg ((1 - PU) * E * PV)) (mul_nonneg (Real.sqrt_nonneg _) hop)
    have hf : frobNorm (PT E) * frobNorm (PT E) ≤ 2 * ((Matrix.rank M : ℝ) *
        (Statlib.HighDim.MatrixAnalysis.opNorm E *
          Statlib.HighDim.MatrixAnalysis.opNorm E)) := by
      rw [hBlockSq]
      linarith [hb1, hb2, hb]
    have hconv : (2 * (Matrix.rank M : ℝ)) * (Statlib.HighDim.MatrixAnalysis.opNorm E *
        Statlib.HighDim.MatrixAnalysis.opNorm E) = 2 * ((Matrix.rank M : ℝ) *
          (Statlib.HighDim.MatrixAnalysis.opNorm E *
            Statlib.HighDim.MatrixAnalysis.opNorm E)) := by ring
    have hs2 : frobNorm (PT E) ^ 2 ≤ (2 * (Matrix.rank M : ℝ)) *
        (Statlib.HighDim.MatrixAnalysis.opNorm E *
          Statlib.HighDim.MatrixAnalysis.opNorm E) := by
      rw [sq, hconv]
      exact hf
    have hsp : Real.sqrt (Statlib.HighDim.MatrixAnalysis.opNorm E *
        Statlib.HighDim.MatrixAnalysis.opNorm E) = Statlib.HighDim.MatrixAnalysis.opNorm E := by
      rw [← sq]
      exact Real.sqrt_sq hop
    have key := hCSone (frobNorm (PT E)) (2 * (Matrix.rank M : ℝ))
      (Statlib.HighDim.MatrixAnalysis.opNorm E * Statlib.HighDim.MatrixAnalysis.opNorm E) hs2
      (mul_nonneg (by norm_num) hrank0) (mul_nonneg hop hop)
    rw [hsp] at key
    exact key
  have hItem3 : frobInner E H ≤
      Real.sqrt (2 * (M.rank : ℝ)) * Statlib.HighDim.MatrixAnalysis.opNorm E * frobNorm H +
        Statlib.HighDim.MatrixAnalysis.opNorm E *
          Statlib.HighDim.Vocabulary.nuclearNorm (Pperp H) := by
    have hperp : frobInner (Pperp E) (Pperp H) = frobInner E (Pperp H) := by
      rw [hPerpSelf E (Pperp H), hPerpIdem H]
    have hpair := (statopia_math_node_791349827_8cd9ad5e m1 m2 E (Pperp H) 0 0 0).2.2.2.1
    have hle1 : frobInner (PT E) (PT H) ≤
        Real.sqrt (2 * (M.rank : ℝ)) * Statlib.HighDim.MatrixAnalysis.opNorm E * frobNorm H := by
      have hmul : frobNorm (PT E) * frobNorm (PT H) ≤
          (Real.sqrt (2 * (M.rank : ℝ)) * Statlib.HighDim.MatrixAnalysis.opNorm E) * frobNorm H := by
        exact mul_le_mul hItem2 (hNormPT H) (hFrobNormNonneg (PT H))
          (mul_nonneg (Real.sqrt_nonneg _) (Statlib.HighDim.MatrixAnalysis.opNorm_nonneg E))
      linarith [hCS (PT E) (PT H)]
    have hle2 : frobInner E (Pperp H) ≤
        Statlib.HighDim.MatrixAnalysis.opNorm E *
          Statlib.HighDim.Vocabulary.nuclearNorm (Pperp H) := hpair
    rw [hSplitAll E H, hperp]
    linarith
  exact ⟨hOrth, hSplit, hSumX A, hPExp A, hPTidem A, hPerpIdem A, hPTself A C, hPerpSelf A C,
    hNorm1, hNorm2, hItem2, hItem3⟩
  /- @proof-region region.target-node.session.79ea84ee4dd52ac2 end -/

end Statlib.Imported

