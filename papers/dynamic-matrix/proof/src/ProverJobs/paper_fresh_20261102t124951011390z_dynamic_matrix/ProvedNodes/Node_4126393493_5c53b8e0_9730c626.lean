import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SVDFoundation
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
theorem statopia_math_node_4126393493_5c53b8e0 : ∀ (m1 m2 : ℕ)
    (X : Matrix (Fin m1) (Fin m2) ℝ) (svd : Statlib.HighDim.Vocabulary.SVD X),
    (∑ i : Fin m1, ∑ j : Fin m2,
        (Statlib.HighDim.MatrixAnalysis.svdPosU svd *
            (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose) i j * X i j) =
      Statlib.HighDim.Vocabulary.nuclearNorm X := by
  /- @proof-region region.target-node.session.b53b3dced115d049 begin -/
  intro m1 m2 X svd
  classical
  let T := {k : Fin (min m1 m2) // 0 < svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) k) (Fin.castLE (Nat.min_le_right m1 m2) k)}
  have hsing : ∀ k : Fin (min m1 m2),
      svd.singularValue k = svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) k) (Fin.castLE (Nat.min_le_right m1 m2) k) :=
    fun k => rfl
  have hUU : ∀ x y : Fin m1, ∑ i, svd.U i x * svd.U i y = if x = y then 1 else 0 := by
    intro x y
    have h := congr_fun (congr_fun svd.hU_orth x) y
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    exact h
  have hVV : ∀ x y : Fin m2, ∑ j, svd.V j x * svd.V j y = if x = y then 1 else 0 := by
    intro x y
    have h := congr_fun (congr_fun svd.hV_orth x) y
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    exact h
  have hL : (∑ i : Fin m1, ∑ j : Fin m2, (Statlib.HighDim.MatrixAnalysis.svdPosU svd * (Statlib.HighDim.MatrixAnalysis.svdPosV svd).transpose) i j * X i j)
      = ∑ k : T, svd.singularValue k.1 := by
    let SU := Statlib.HighDim.MatrixAnalysis.svdPosU svd
    let SV := Statlib.HighDim.MatrixAnalysis.svdPosV svd
    have hUp : ∀ (i : Fin m1) (k : T), SU i k = svd.U i (Fin.castLE (Nat.min_le_left m1 m2) k.1) := fun i k => rfl
    have hVp : ∀ (j : Fin m2) (k : T), SV j k = svd.V j (Fin.castLE (Nat.min_le_right m1 m2) k.1) := fun j k => rfl
    have trace_eq : ∀ (A : Matrix (Fin m1) (Fin m2) ℝ), (A.transpose * X).trace = ∑ j : Fin m2, ∑ i : Fin m1, A i j * X i j := by
      intro A
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    have htrace0 : (∑ i : Fin m1, ∑ j : Fin m2, (SU * SV.transpose) i j * X i j) = ((SU * SV.transpose).transpose * X).trace := by
      rw [trace_eq (SU * SV.transpose)]
      exact Finset.sum_comm
    have hWX : ((SU * SV.transpose).transpose * X) = SV * (SU.transpose * svd.U) * svd.sigma * svd.V.transpose := by
      have key : ((SU * SV.transpose).transpose * X) = ((SU * SV.transpose).transpose * (svd.U * svd.sigma * svd.V.transpose)) := by
        rw [← svd.h_eq]
      rw [key, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    have hM1 : ∀ (k : T) (a : Fin m1), (SU.transpose * svd.U) k a = if Fin.castLE (Nat.min_le_left m1 m2) k.1 = a then 1 else 0 := by
      intro k a
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply, hUp]
      exact hUU (Fin.castLE (Nat.min_le_left m1 m2) k.1) a
    have hM2 : ∀ (b : Fin m2) (k : T), (svd.V.transpose * SV) b k = if b = Fin.castLE (Nat.min_le_right m1 m2) k.1 then 1 else 0 := by
      intro b k
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply, hVp]
      exact hVV b (Fin.castLE (Nat.min_le_right m1 m2) k.1)
    have hMsig : ∀ (k : T) (b : Fin m2), ((SU.transpose * svd.U) * svd.sigma) k b = svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) k.1) b := by
      intro k b
      rw [Matrix.mul_apply]
      simp only [hM1]
      rw [Finset.sum_eq_single (Fin.castLE (Nat.min_le_left m1 m2) k.1)]
      · simp
      · intro a _ ha; rw [if_neg (Ne.symm ha), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hcalc2 : (SV * (SU.transpose * svd.U) * svd.sigma * svd.V.transpose).trace = ((SU.transpose * svd.U) * svd.sigma * (svd.V.transpose * SV)).trace := by
      calc
        (SV * (SU.transpose * svd.U) * svd.sigma * svd.V.transpose).trace = (svd.V.transpose * (SV * (SU.transpose * svd.U) * svd.sigma)).trace := Matrix.trace_mul_comm _ _
        _ = ((svd.V.transpose * SV) * ((SU.transpose * svd.U) * svd.sigma)).trace := by simp only [Matrix.mul_assoc]
        _ = (((SU.transpose * svd.U) * svd.sigma) * (svd.V.transpose * SV)).trace := Matrix.trace_mul_comm _ _
    have hcalc3 : ((SU.transpose * svd.U) * svd.sigma * (svd.V.transpose * SV)).trace = ∑ k : T, svd.singularValue k.1 := by
      simp only [Matrix.trace, Matrix.diag]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Matrix.mul_apply]
      have hstep : ∀ b : Fin m2, ((SU.transpose * svd.U) * svd.sigma) k b * (svd.V.transpose * SV) b k = svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) k.1) b * (if b = Fin.castLE (Nat.min_le_right m1 m2) k.1 then 1 else 0) := by
        intro b
        simp only [hMsig, hM2]
      rw [Finset.sum_congr rfl (fun b _ => hstep b)]
      rw [hsing k.1]
      rw [Finset.sum_eq_single (Fin.castLE (Nat.min_le_right m1 m2) k.1)]
      · simp
      · intro b _ hb; rw [if_neg hb, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hcalc1 : ((SU * SV.transpose).transpose * X).trace = (SV * (SU.transpose * svd.U) * svd.sigma * svd.V.transpose).trace := by rw [hWX]
    exact htrace0.trans (hcalc1.trans (hcalc2.trans hcalc3))
  have hN : Statlib.HighDim.Vocabulary.nuclearNorm X = ∑ k : T, svd.singularValue k.1 := by
    obtain ⟨π, hπ⟩ := Statlib.HighDim.MatrixAnalysis.svd_singular_values_unique X (Classical.choice (Statlib.HighDim.MatrixAnalysis.svd_exists X)) svd
    have hπ' : ∀ i : Fin (min m1 m2), (Classical.choice (Statlib.HighDim.MatrixAnalysis.svd_exists X)).singularValue i = svd.singularValue (π i) := by
      intro i
      show (Classical.choice (Statlib.HighDim.MatrixAnalysis.svd_exists X)).sigma (Fin.castLE (Nat.min_le_left m1 m2) i) (Fin.castLE (Nat.min_le_right m1 m2) i) = svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) (π i)) (Fin.castLE (Nat.min_le_right m1 m2) (π i))
      exact hπ i
    have hST : (∑ i : Fin (min m1 m2), svd.singularValue i) = ∑ k : T, svd.singularValue k.1 := by
      have hzero : ∀ i : Fin (min m1 m2), ¬ (0 < svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) i) (Fin.castLE (Nat.min_le_right m1 m2) i)) → svd.singularValue i = 0 := by
        intro i hi
        have hnn : 0 ≤ svd.singularValue i := by
          rw [hsing i]
          exact svd.hsigma_nonneg _ _
        have hle : svd.singularValue i ≤ 0 := by
          rw [hsing i]
          exact not_lt.mp hi
        exact le_antisymm hle hnn
      have h1 : (∑ i : Fin (min m1 m2), svd.singularValue i)
          = ((Finset.univ : Finset (Fin (min m1 m2))).filter (fun i => 0 < svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) i) (Fin.castLE (Nat.min_le_right m1 m2) i))).sum (fun i => svd.singularValue i) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases h : 0 < svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) i) (Fin.castLE (Nat.min_le_right m1 m2) i)
        · simp [h]
        · rw [if_neg h]
          exact hzero i h
      have h2 : (((Finset.univ : Finset (Fin (min m1 m2))).filter (fun i => 0 < svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) i) (Fin.castLE (Nat.min_le_right m1 m2) i))).sum (fun i => svd.singularValue i))
          = ∑ k : T, svd.singularValue k.1 := by
        have hmap : (Finset.univ : Finset (Fin (min m1 m2))).filter (fun i => 0 < svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) i) (Fin.castLE (Nat.min_le_right m1 m2) i))
            = (Finset.univ : Finset T).map (Function.Embedding.subtype (fun i => 0 < svd.sigma (Fin.castLE (Nat.min_le_left m1 m2) i) (Fin.castLE (Nat.min_le_right m1 m2) i))) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coe_subtype]
          constructor
          · intro hi
            exact ⟨⟨i, hi⟩, rfl⟩
          · rintro ⟨a, ha⟩
            rw [← ha]
            exact a.2
        rw [hmap, Finset.sum_map]
        rfl
      exact h1.trans h2
    have hN2 : (∑ i : Fin (min m1 m2), (Classical.choice (Statlib.HighDim.MatrixAnalysis.svd_exists X)).singularValue i) = ∑ i : Fin (min m1 m2), svd.singularValue (π i) :=
      Finset.sum_congr rfl (fun i _ => hπ' i)
    have hN3 : (∑ i : Fin (min m1 m2), svd.singularValue (π i)) = ∑ i : Fin (min m1 m2), svd.singularValue i :=
      Equiv.sum_comp π (fun i => svd.singularValue i)
    exact (Statlib.HighDim.MatrixAnalysis.nuclearNorm_eq_svd_singularValue_sum X).trans (hN2.trans (hN3.trans hST))
  exact hL.trans hN.symm
  /- @proof-region region.target-node.session.b53b3dced115d049 end -/

end Statlib.Imported

