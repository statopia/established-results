import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_32e90b762751308982c0

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
theorem statopia_math_node_3611940486_e5c47169 : ∀ (m n : ℕ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hH : ((A.map Complex.ofReal).transpose * (A.map Complex.ofReal)).IsHermitian),
    (Finset.univ.val.map (fun i : Fin n => hH.eigenvalues i))
      = Finset.univ.val.map (fun i : Fin n =>
          (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) := by
  /- @proof-region region.target-node.session.df2dd93011276889 begin -/
  intro m n A hH
  have hM : (A.conjTranspose * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hAT : A.transpose = A.conjTranspose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hHmap : (A.map Complex.ofReal).transpose * (A.map Complex.ofReal)
      = (A.conjTranspose * A).map Complex.ofReal := by
    rw [← hAT]
    ext i j
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  have hmapHom : (A.conjTranspose * A).map Complex.ofReal
      = (A.conjTranspose * A).map ⇑(algebraMap ℝ ℂ) := by
    ext i j
    rfl
  have hchar : ((A.map Complex.ofReal).transpose * (A.map Complex.ofReal)).charpoly
      = (A.conjTranspose * A).charpoly.map (algebraMap ℝ ℂ) := by
    rw [hHmap, hmapHom, Matrix.charpoly_map]
  have hHroot := Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hH
  have hHroot' : ((A.map Complex.ofReal).transpose * (A.map Complex.ofReal)).charpoly.roots
      = Multiset.map (Complex.ofReal ∘ hH.eigenvalues) Finset.univ.val := hHroot
  have hchild := statopia_math_node_3243536340_6e6dfa97 n (A.conjTranspose * A) hM
  have hchild' : (Polynomial.map (algebraMap ℝ ℂ) (A.conjTranspose * A).charpoly).roots
      = Multiset.map (Complex.ofReal ∘ hM.eigenvalues) Finset.univ.val := hchild
  have key : Multiset.map (Complex.ofReal ∘ hH.eigenvalues) Finset.univ.val
      = Multiset.map (Complex.ofReal ∘ hM.eigenvalues) Finset.univ.val := by
    rw [← hHroot', hchar]
    exact hchild'
  classical
  set r : ℂ → ℝ := fun z =>
    if h : ∃ y : ℝ, Complex.ofReal y = z then Classical.choose h else 0 with hr
  have hr_apply : ∀ x : ℝ, r (Complex.ofReal x) = x := by
    intro x
    have hex : ∃ y : ℝ, Complex.ofReal y = Complex.ofReal x := ⟨x, rfl⟩
    have h1 : r (Complex.ofReal x) = Classical.choose hex := by
      simp only [hr, dif_pos hex]
    rw [h1]
    exact Complex.ofReal_injective (Classical.choose_spec hex)
  have hfin : Multiset.map hH.eigenvalues Finset.univ.val
      = Multiset.map hM.eigenvalues Finset.univ.val := by
    calc Multiset.map hH.eigenvalues Finset.univ.val
        = (Multiset.map (Complex.ofReal ∘ hH.eigenvalues) Finset.univ.val).map r := by
          simp [Function.comp_def, hr_apply]
      _ = (Multiset.map (Complex.ofReal ∘ hM.eigenvalues) Finset.univ.val).map r := by
          rw [key]
      _ = Multiset.map hM.eigenvalues Finset.univ.val := by
          simp [Function.comp_def, hr_apply]
  simpa using hfin
  /- @proof-region region.target-node.session.df2dd93011276889 end -/

end Statlib.Imported

