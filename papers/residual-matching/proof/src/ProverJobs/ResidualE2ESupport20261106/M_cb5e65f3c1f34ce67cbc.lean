import Lean
import Mathlib
import ProverJobs.ResidualE2ESupport20261106.M_1707633e48d0b626a450

namespace PaperProofTasks.ResidualE2ESupport20261106

open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianResolventBounds

set_option maxHeartbeats 2000000 in
theorem hermitian_resolvent_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    ‖(A - z • 1)⁻¹‖ ≤ z.im⁻¹ := by
  classical
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) hA.eigenvectorUnitary
  let d : Fin n → ℂ := fun i => (hA.eigenvalues i : ℂ) - z
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal d
  let E : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => (d i)⁻¹)
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    have hh := congrArg Complex.im hi
    simp only [d, Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at hh
    linarith
  have hDE : D * E = 1 := by
    change Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹) = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j; simp [hd]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  have hAD : A - z • 1 = φ D := by
    have hspec : A = φ (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) := by
      simpa [φ, Function.comp_def] using hA.spectral_theorem
    rw [hspec]
    have hdg : D = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) - z • 1 := by
      ext i j
      by_cases h : i = j
      · subst j; simp [D, d, Matrix.diagonal_apply, Matrix.one_apply]
      · simp [D, d, Matrix.diagonal_apply, Matrix.one_apply, h]
    rw [hdg, map_sub, map_smul, map_one]
  have hInv : (A - z • 1)⁻¹ = φ E := by
    apply Matrix.inv_eq_right_inv
    rw [hAD, ← map_mul, hDE, map_one]
  have hnorm : ‖φ E‖ = ‖E‖ := by
    change ‖(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * E *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)‖ = ‖E‖
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hA.eigenvectorUnitary.prop),
      CStarRing.norm_coe_unitary_mul]
  rw [hInv, hnorm]
  change ‖Matrix.diagonal (fun i => (d i)⁻¹)‖ ≤ _
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hz.le)).2
  intro i
  rw [norm_inv]
  apply (inv_le_inv₀ (norm_pos_iff.mpr (hd i)) hz).2
  have hh : |(d i).im| ≤ ‖d i‖ := Complex.abs_im_le_norm _
  simpa [d, abs_of_pos hz] using hh

theorem matrix_entry_le_l2_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin m) (j : Fin n) : ‖A i j‖ ≤ ‖A‖ := by
  let x : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j (1 : ℂ)
  let v : EuclideanSpace ℂ (Fin m) :=
    (EuclideanSpace.equiv (Fin m) ℂ).symm (A.mulVec x.ofLp)
  have hx : ‖x‖ = 1 := by simp [x]
  have hv : v i = A i j := by simp [v, x]
  calc ‖A i j‖ = ‖v i‖ := congrArg norm hv.symm
    _ ≤ ‖v‖ := PiLp.norm_apply_le v i
    _ ≤ ‖A‖ := by simpa [v, hx] using Matrix.l2_opNorm_mulVec A x

#print axioms hermitian_resolvent_norm
#print axioms matrix_entry_le_l2_norm
end ResidualSparseRepair20261106.GaussianResolventBounds

