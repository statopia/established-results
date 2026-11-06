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
theorem statopia_math_node_1091255960_d6b37970 : ∀ (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian),
    Polynomial.Splits M.charpoly := by
  /- @proof-region region.target-node.session.07bf75a6664b6ff6 begin -/
  intro n M hM
  classical
  have hroots : M.charpoly.roots = Multiset.map hM.eigenvalues Finset.univ.val := by
    simpa using Matrix.IsHermitian.roots_charpoly_eq_eigenvalues (𝕜 := ℝ) hM
  have hcard : M.charpoly.roots.card = M.charpoly.natDegree := by
    rw [hroots, Matrix.charpoly_natDegree_eq_dim]
    simp
  have hfac : M.charpoly
      = (M.charpoly.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod :=
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic M)
      hcard).symm
  set S : Submonoid (Polynomial ℝ) :=
    Submonoid.closure ({x : Polynomial ℝ | ∃ a : ℝ, Polynomial.C a = x} ∪
      {x : Polynomial ℝ | ∃ a : ℝ, Polynomial.X + Polynomial.C a = x}) with hS
  have hmem : (M.charpoly.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod ∈ S := by
    refine Multiset.induction_on M.charpoly.roots ?_ ?_
    · simpa using S.one_mem'
    · intro a s ih
      rw [Multiset.map_cons, Multiset.prod_cons]
      refine S.mul_mem' ?_ ih
      rw [hS]
      exact Submonoid.subset_closure (Or.inr ⟨-a, by rw [sub_eq_add_neg, Polynomial.C_neg]⟩)
  rw [hfac]
  rw [hS] at hmem
  exact hmem
  /- @proof-region region.target-node.session.07bf75a6664b6ff6 end -/

end Statlib.Imported

