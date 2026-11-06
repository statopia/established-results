import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_c71c8d8206a5694d986e

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1439674200_188c062d : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (w : ℂ)
    (hw : ∀ i : Fin n, w - ((Statlib.Imported.svals A i : ℝ) : ℂ) ^ 2 ≠ 0),
    ((w • (1 : Matrix (Fin n) (Fin n) ℂ) -
        (A.map Complex.ofReal).transpose * (A.map Complex.ofReal))⁻¹).trace
      = ∑ i : Fin n, (w - ((Statlib.Imported.svals A i : ℝ) : ℂ) ^ 2)⁻¹ := by
  /- @proof-region region.target-node.session.31f8822f0fe1e569 begin -/
  intro m n A w hw
  set B : Matrix (Fin m) (Fin n) ℂ := A.map Complex.ofReal with hB
  have hBT : B.transpose = B.conjTranspose := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply, hB, Matrix.map_apply]
    simp
  have hH : (B.transpose * B).IsHermitian := by
    rw [hBT]
    exact Matrix.isHermitian_conjTranspose_mul_self B
  have hmult : (Finset.univ.val.map (fun i : Fin n => hH.eigenvalues i))
      = (Finset.univ.val.map (fun i : Fin n => (Statlib.Imported.svals A i) ^ 2)) :=
    statopia_math_node_3875775941_f40cd015 m n A hH
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUstar : U * star U = 1 := by
    have h := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [hU] using h
  have hstarU : star U * U = 1 := by
    have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [hU] using h
  have hspec : B.transpose * B
      = U * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * star U := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [hU] using h
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => w - ((hH.eigenvalues i : ℝ) : ℂ)) with hDdef
  have hD : D = w • (1 : Matrix (Fin n) (Fin n) ℂ)
      - Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    simp [hDdef, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]
  have hQ : w • (1 : Matrix (Fin n) (Fin n) ℂ) - B.transpose * B = U * D * star U := by
    rw [hspec, hD, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, hUstar]
  set E : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => (w - ((hH.eigenvalues i : ℝ) : ℂ))⁻¹) with hEdef
  have hDne : ∀ i, w - ((hH.eigenvalues i : ℝ) : ℂ) ≠ 0 := by
    intro i
    have hmem : hH.eigenvalues i ∈
        Finset.univ.val.map (fun j : Fin n => (Statlib.Imported.svals A j) ^ 2) := by
      rw [← hmult]
      exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [Multiset.mem_map] at hmem
    obtain ⟨j, _, hj⟩ := hmem
    rw [← hj]
    push_cast
    exact hw j
  have hDmul : D * E = 1 := by
    rw [hDdef, hEdef, Matrix.diagonal_mul_diagonal,
      show (fun i => (w - ((hH.eigenvalues i : ℝ) : ℂ)) * (w - ((hH.eigenvalues i : ℝ) : ℂ))⁻¹)
          = (fun _ => 1) from funext (fun i => Complex.mul_inv_cancel (hDne i)),
      Matrix.diagonal_one]
  have hDinv : D⁻¹ = E := Matrix.inv_eq_right_inv hDmul
  have hUinv : U⁻¹ = star U := Matrix.inv_eq_right_inv hUstar
  have hstarUinv : (star U)⁻¹ = U := Matrix.inv_eq_right_inv hstarU
  have hQinv : (w • (1 : Matrix (Fin n) (Fin n) ℂ) - B.transpose * B)⁻¹
      = U * D⁻¹ * star U := by
    rw [hQ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hstarUinv, hUinv, mul_assoc]
  have htrace : (w • (1 : Matrix (Fin n) (Fin n) ℂ) - B.transpose * B)⁻¹.trace
      = ∑ i, (w - ((hH.eigenvalues i : ℝ) : ℂ))⁻¹ := by
    rw [hQinv, hDinv, Matrix.trace_mul_comm (U * E) (star U), ← mul_assoc, hstarU, one_mul,
      hEdef, Matrix.trace_diagonal]
  rw [htrace]
  rw [show (∑ i : Fin n, (w - ((Statlib.Imported.svals A i : ℝ) : ℂ) ^ 2)⁻¹)
      = ∑ i : Fin n, (w - (((Statlib.Imported.svals A i) ^ 2 : ℝ) : ℂ))⁻¹ from
    Finset.sum_congr rfl (fun i _ => by push_cast; rfl)]
  have hmap := congrArg (Multiset.map (fun x : ℝ => (w - (x : ℂ))⁻¹)) hmult
  simp only [Multiset.map_map, Function.comp] at hmap
  have h2 := congrArg Multiset.sum hmap
  simpa [Finset.sum] using h2
  /- @proof-region region.target-node.session.31f8822f0fe1e569 end -/

end Statlib.Imported

