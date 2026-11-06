import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_b4a4feb8a3fe12f0dd7e

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
theorem statopia_math_node_760072556_5eef0e48 : ∀ (m n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hg : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => g ω i j) (i : Fin n),
    Measurable fun ω => svals (m := m) (n := n) (g ω) i := by
  /- @proof-region region.target-node.session.7510cb1dbcd1423d begin -/
  intro m n Ω _inst g hg i
  have hHerm : ∀ ω : Ω, (Matrix.conjTranspose (g ω) * g ω).IsHermitian := fun ω =>
    Matrix.isHermitian_conjTranspose_mul_self (g ω)
  have hentry : ∀ a b : Fin n,
      Measurable fun ω => (Matrix.conjTranspose (g ω) * g ω) a b := by
    intro a b
    have hfun : ∀ ω : Ω,
        (Matrix.conjTranspose (g ω) * g ω) a b = ∑ k : Fin m, g ω k a * g ω k b := by
      intro ω
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp only [hfun]
    apply Finset.measurable_sum
    intro k _
    exact (hg k a).mul (hg k b)

  have htrace : Measurable fun ω => (Matrix.conjTranspose (g ω) * g ω).trace := by
    simp only [Matrix.trace]
    apply Finset.measurable_sum
    intro a _
    exact hentry a a
  have hsumEig : Measurable fun ω => ∑ j : Fin n, (hHerm ω).eigenvalues j := by
    have hfun : ∀ ω : Ω, ∑ j : Fin n, (hHerm ω).eigenvalues j
        = (Matrix.conjTranspose (g ω) * g ω).trace := by
      intro ω
      rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues (hHerm ω)]
      simp
    simp only [hfun]
    exact htrace
  have heig : ∀ k : Fin (Fintype.card (Fin n)),
      Measurable fun ω => (hHerm ω).eigenvalues₀ k := fun k =>
    statopia_math_node_1534763445_28183d06 n
      (fun ω => Matrix.conjTranspose (g ω) * g ω) hentry hHerm k
  have hmain : Measurable fun ω =>
      Real.sqrt ((hHerm ω).eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)) :=
    Real.continuous_sqrt.measurable.comp (heig (Fin.cast (Fintype.card_fin n).symm i))
  simpa [svals, hHerm] using hmain
  /- @proof-region region.target-node.session.7510cb1dbcd1423d end -/

end Statlib.Imported

