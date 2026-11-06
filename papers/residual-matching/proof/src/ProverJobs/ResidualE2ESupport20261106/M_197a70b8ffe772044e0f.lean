import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
theorem statopia_math_node_3272233362_d4716ab0 : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (g : ι → ℝ)
    (hdiag : ∀ i j : ι, A i j = if i = j then ((g i : ℝ) : ℂ) else 0),
    Set.range hA.eigenvalues = Set.range g := by
  /- @proof-region region.target-node.session.93d3387f4895024e begin -/
  intro ι _ _ A hA g hdiag
  have hAeq : A = Matrix.diagonal (fun q => ((g q : ℝ) : ℂ)) := by
    ext a b
    rw [hdiag a b, Matrix.diagonal_apply]
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    have hbne : hA.eigenvectorBasis j ≠ 0 := hA.eigenvectorBasis.orthonormal.ne_zero j
    have hxne : (hA.eigenvectorBasis j).ofLp ≠ 0 := by
      intro h
      refine hbne (WithLp.ofLp_injective 2 ?_)
      simpa using h
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hxne
    rw [Pi.zero_apply] at ht
    have heq : A.mulVec (hA.eigenvectorBasis j).ofLp
        = ((hA.eigenvalues j : ℝ) : ℂ) • (hA.eigenvectorBasis j).ofLp :=
      Matrix.IsHermitian.mulVec_eigenvectorBasis hA j
    have hmulvec : ∀ y : ι → ℂ,
        (Matrix.diagonal (fun q => ((g q : ℝ) : ℂ))).mulVec y = A.mulVec y := by
      intro y
      rw [hAeq]
    have hdiagmul : (Matrix.diagonal (fun q => ((g q : ℝ) : ℂ))).mulVec (hA.eigenvectorBasis j).ofLp
        = A.mulVec (hA.eigenvectorBasis j).ofLp := hmulvec _
    have hcoord1 : (Matrix.diagonal (fun q => ((g q : ℝ) : ℂ))).mulVec (hA.eigenvectorBasis j).ofLp t
        = ((g t : ℝ) : ℂ) * ((hA.eigenvectorBasis j).ofLp t) :=
      Matrix.mulVec_diagonal _ _ t
    have hcoord2 : (((hA.eigenvalues j : ℝ) : ℂ) • (hA.eigenvectorBasis j).ofLp) t
        = ((hA.eigenvalues j : ℝ) : ℂ) * ((hA.eigenvectorBasis j).ofLp t) := by
      rw [Pi.smul_apply, smul_eq_mul]
    have hEq : ((g t : ℝ) : ℂ) * ((hA.eigenvectorBasis j).ofLp t)
        = ((hA.eigenvalues j : ℝ) : ℂ) * ((hA.eigenvectorBasis j).ofLp t) := by
      rw [← hcoord1, hdiagmul, heq, hcoord2]
    have key : ((g t : ℝ) : ℂ) = ((hA.eigenvalues j : ℝ) : ℂ) := by
      rcases mul_eq_mul_right_iff.mp hEq with h | h
      · exact h
      · exact absurd h ht
    exact ⟨t, Complex.ofReal_injective key⟩
  · rintro ⟨i, rfl⟩
    rw [← Set.mem_range]
    rw [← Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hA]
    simp only [spectrum, Set.mem_setOf_eq]
    intro h
    have hdet : (algebraMap ℝ (Matrix ι ι ℂ) (g i) - A).det = 0 := by
      have hmat : algebraMap ℝ (Matrix ι ι ℂ) (g i) - A
          = Matrix.diagonal (fun q => ((g i : ℝ) : ℂ) - ((g q : ℝ) : ℂ)) := by
        rw [hAeq, Algebra.algebraMap_eq_smul_one]
        ext a b
        by_cases hab : a = b <;>
          simp [hab, Matrix.diagonal_apply, Matrix.one_apply]
      rw [hmat, Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    have hunit : IsUnit (algebraMap ℝ (Matrix ι ι ℂ) (g i) - A).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 h
    rw [hdet] at hunit
    exact (isUnit_iff_ne_zero.mp hunit) rfl
  /- @proof-region region.target-node.session.93d3387f4895024e end -/

end Statlib.Imported

