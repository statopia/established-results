import Lean
import ProverJobs.ResidualE2ESupport20261106.M_1707633e48d0b626a450

namespace PaperProofTasks.ResidualE2ESupport20261106

open scoped Matrix.Norms.L2Operator

namespace ResidualSparseRepair20261106.GaussianCalculus

noncomputable def matrixEntryCLM (m n : ℕ) (i : Fin m) (j : Fin n) :
    Matrix (Fin m) (Fin n) ℂ →L[ℝ] ℂ :=
  ({toFun := fun A => A i j
    map_add' := by intros; rfl
    map_smul' := by intros; rfl} : Matrix (Fin m) (Fin n) ℂ →ₗ[ℝ] ℂ).toContinuousLinearMap

@[simp] theorem matrixEntryCLM_apply (m n : ℕ) (i : Fin m) (j : Fin n)
    (A : Matrix (Fin m) (Fin n) ℂ) : matrixEntryCLM m n i j A = A i j := rfl

theorem weighted_gram_resolvent_entry_derivative {m n : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im)
    (t : ℝ) (i : Fin m) (j : Fin n) :
    HasDerivAt
      (fun s : ℝ => ((A + s • E) * (gramPencil (A + s • E) z)⁻¹) i j)
      ((E * (gramPencil (A + t • E) z)⁻¹) i j -
        ((A + t • E) * ((gramPencil (A + t • E) z)⁻¹ *
          (((m : ℝ)⁻¹) • (E.conjTranspose * (A + t • E) +
            (A + t • E).conjTranspose * E)) *
          (gramPencil (A + t • E) z)⁻¹)) i j) t := by
  let Q := (gramPencil (A + t • E) z)⁻¹
  let H := (((m : ℝ)⁻¹) • (E.conjTranspose * (A + t • E) +
            (A + t • E).conjTranspose * E))
  have hdQ := gram_resolvent_directional_derivative A E z hz t
  have hdQentry (k : Fin n) : HasDerivAt
      (fun s : ℝ => ((gramPencil (A + s • E) z)⁻¹) k j)
      (-(Q * H * Q) k j) t := by
    have hh := (matrixEntryCLM n n k j).hasFDerivAt.comp_hasDerivAt t hdQ
    simpa only [matrixEntryCLM_apply, Matrix.neg_apply] using hh
  have hdAentry (k : Fin n) : HasDerivAt
      (fun s : ℝ => (A + s • E) i k) (E i k) t := by
    simpa only [Matrix.add_apply, Matrix.smul_apply, zero_add, one_smul] using
      ((hasDerivAt_const t (A i k)).add ((hasDerivAt_id t).smul_const (E i k)))
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun k _ => (hdAentry k).mul (hdQentry k))
  convert hd using 1
  · funext s
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply]
  · dsimp [Q, H]
    simp only [Matrix.mul_apply, Finset.sum_add_distrib, mul_neg,
      Finset.sum_neg_distrib, sub_eq_add_neg, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul]

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.weighted_gram_resolvent_entry_derivative

