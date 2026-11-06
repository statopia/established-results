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
theorem statopia_math_node_2281494419_677a8c9a : ∀ (N : ℕ) [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.IsHermitian) (v : Fin N → ℂ),
    ((∑ i : Fin N, ∑ j : Fin N, star (v i) * v j * A i j).re =
        ∑ j : Fin N,
          hA.eigenvalues j * ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 v)‖ ^ 2) ∧
      (∑ j : Fin N, ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 v)‖ ^ 2 =
        ∑ i : Fin N, ‖v i‖ ^ 2) := by
  /- @proof-region region.target-node.session.e9f9209bae084aeb begin -/
  intro N _ A hA v
  set b := hA.eigenvectorBasis with hb
  set V : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 v with hV
  have hbridge : inner ℂ V ((Matrix.toEuclideanLin A) V) = (∑ i, ∑ j, star (v i) * v j * A i j) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply]
    show (∑ i, (∑ j, A i j * v j) * star (v i)) = (∑ i, ∑ j, star (v i) * v j * A i j)
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hAeig : ∀ j, (Matrix.toEuclideanLin A) (b j) = (hA.eigenvalues j : ℂ) • b j := by
    intro j
    apply WithLp.ofLp_injective 2
    rw [Matrix.ofLp_toEuclideanLin_apply, Matrix.IsHermitian.mulVec_eigenvectorBasis hA j]
    rfl
  have hTV : (Matrix.toEuclideanLin A) V = ∑ j, (inner ℂ (b j) V * (hA.eigenvalues j : ℂ)) • b j := by
    conv_lhs => rw [← OrthonormalBasis.sum_repr' b V]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, hAeig j, smul_smul]
  have hconj : ∀ j, inner ℂ V (b j) = (starRingEnd ℂ) (inner ℂ (b j) V) := by
    intro j
    rw [inner_conj_symm]
  have hterm : ∀ j, inner ℂ V ((inner ℂ (b j) V * (hA.eigenvalues j : ℂ)) • b j)
      = (hA.eigenvalues j : ℂ) * (↑(‖inner ℂ (b j) V‖ ^ 2) : ℂ) := by
    intro j
    rw [inner_smul_right, hconj j]
    have hz : (↑(‖inner ℂ (b j) V‖ ^ 2) : ℂ)
        = inner ℂ (b j) V * (starRingEnd ℂ) (inner ℂ (b j) V) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      ring
    rw [hz]
    ring
  have hinner : inner ℂ V ((Matrix.toEuclideanLin A) V)
      = ∑ j, (hA.eigenvalues j : ℂ) * (↑(‖inner ℂ (b j) V‖ ^ 2) : ℂ) := by
    rw [hTV, inner_sum]
    exact Finset.sum_congr rfl (fun j _ => hterm j)
  have hofreal : (∑ j, (hA.eigenvalues j : ℂ) * (↑(‖inner ℂ (b j) V‖ ^ 2) : ℂ))
      = (↑(∑ j, hA.eigenvalues j * ‖inner ℂ (b j) V‖ ^ 2) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun j _ => by push_cast; ring)
  have hval : inner ℂ V ((Matrix.toEuclideanLin A) V)
      = (↑(∑ j, hA.eigenvalues j * ‖inner ℂ (b j) V‖ ^ 2) : ℂ) := by
    rw [hinner, hofreal]
  have hparse : (∑ j, ‖inner ℂ (b j) V‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
    rw [OrthonormalBasis.sum_sq_norm_inner_right b V, EuclideanSpace.norm_sq_eq]
  constructor
  · rw [← hbridge, hval, Complex.ofReal_re]
  · exact hparse
  /- @proof-region region.target-node.session.e9f9209bae084aeb end -/

end Statlib.Imported

