import Lean
import Mathlib

namespace PaperProofTasks.ResidualE2ESupport20261106

open scoped Matrix.Norms.L2Operator

namespace ResidualSparseRepair20261106.GaussianCalculus

theorem matrix_inverse_hasDerivAt {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hA : HasDerivAt A B t) (hu : IsUnit (A t)) :
    HasDerivAt (fun s => (A s)⁻¹) (-((A t)⁻¹ * B * (A t)⁻¹)) t := by
  obtain ⟨u, hu⟩ := hu
  have hInv : (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) = (A t)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hInv, hu] at hi
  have hd := hi.comp_hasDerivAt t hA
  simpa only [Matrix.nonsing_inv_eq_ringInverse, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] using hd

theorem quadratic_pencil_inverse_derivative {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hu : IsUnit (A + t • B + t ^ 2 • C)) :
    HasDerivAt (fun s : ℝ => (A + s • B + s ^ 2 • C)⁻¹)
      (-((A + t • B + t ^ 2 • C)⁻¹ * (B + (2 * t) • C) *
        (A + t • B + t ^ 2 • C)⁻¹)) t := by
  apply matrix_inverse_hasDerivAt _ _ _ ?_ hu
  have h1 := (hasDerivAt_const t A).add ((hasDerivAt_id t).smul_const B)
  have h2 := ((hasDerivAt_id t).pow 2).smul_const C
  simpa using h1.add h2

theorem hermitian_resolvent_isUnit {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) : IsUnit (A - z • 1) := by
  have hs : z ∉ spectrum ℂ A := by
    rw [hA.spectrum_eq_image_range]
    rintro ⟨x, hx, he⟩
    have hi := congrArg Complex.im he
    change (0 : ℝ) = z.im at hi
    linarith
  have hu : IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A) := by
    simpa only [spectrum, resolventSet, Set.mem_compl_iff, Set.mem_setOf_eq,
      not_not, Algebra.algebraMap_eq_smul_one] using hs
  simpa only [neg_sub] using hu.neg

noncomputable def gramPencil {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((m : ℝ)⁻¹) • (A.conjTranspose * A) - z • 1

theorem gram_pencil_isUnit {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im) :
    IsUnit (gramPencil A z) := by
  apply hermitian_resolvent_isUnit _ _ z hz
  change (((m : ℝ)⁻¹) • (A.conjTranspose * A)).conjTranspose = _
  simp

theorem gram_resolvent_directional_derivative {m n : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (gramPencil (A + s • E) z)⁻¹)
      (-((gramPencil (A + t • E) z)⁻¹ *
        (((m : ℝ)⁻¹) • (E.conjTranspose * (A + t • E) +
          (A + t • E).conjTranspose * E)) *
        (gramPencil (A + t • E) z)⁻¹)) t := by
  let A0 := gramPencil A z
  let B0 := ((m : ℝ)⁻¹) • (E.conjTranspose * A + A.conjTranspose * E)
  let C0 := ((m : ℝ)⁻¹) • (E.conjTranspose * E)
  have heq : ∀ s : ℝ, gramPencil (A + s • E) z = A0 + s • B0 + s ^ 2 • C0 := by
    intro s
    dsimp [gramPencil, A0, B0, C0]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      star_trivial, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul]
    module
  have hB : ((m : ℝ)⁻¹) • (E.conjTranspose * (A + t • E) +
      (A + t • E).conjTranspose * E) = B0 + (2 * t) • C0 := by
    dsimp [B0, C0]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      star_trivial, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul]
    module
  have hu : IsUnit (A0 + t • B0 + t ^ 2 • C0) := by
    rw [← heq]
    exact gram_pencil_isUnit _ z hz
  have hd := quadratic_pencil_inverse_derivative A0 B0 C0 t hu
  simp_rw [heq, hB]
  exact hd

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.matrix_inverse_hasDerivAt
#print axioms ResidualSparseRepair20261106.GaussianCalculus.quadratic_pencil_inverse_derivative

#print axioms ResidualSparseRepair20261106.GaussianCalculus.gram_resolvent_directional_derivative

