import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3275750866_883f8e1a : ∀ (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (d : ℝ) (hd : 0 ≤ d) (hMN : M = d • N) (i : Fin (Fintype.card (Fin n))),
    hM.eigenvalues₀ i = d * hN.eigenvalues₀ i := by
  /- @proof-region region.target-node.session.f20ff0bb004c9bd5 begin -/
  intro n M N hM hN d hd hMN i
  subst hMN
  rcases eq_or_lt_of_le hd with h0 | hpos
  · subst h0
    have hev0 : hM.eigenvalues = 0 :=
      (Matrix.IsHermitian.eigenvalues_eq_zero_iff hM).mpr (zero_smul ℝ N)
    have hroots0 : ((0 : ℝ) • N).charpoly.roots
        = Multiset.map (RCLike.ofReal ∘ hM.eigenvalues) Finset.univ.val :=
      Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hM
    have e1' : (↑(List.ofFn hM.eigenvalues₀) : Multiset ℝ)
        = Multiset.map RCLike.re (((0 : ℝ) • N).charpoly.roots) := by
      rw [← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀ hM]
      exact Multiset.sort_eq _ _
    have hevals : (↑(List.ofFn hM.eigenvalues₀) : Multiset ℝ)
        = Multiset.map (fun _ : Fin n => (0 : ℝ)) Finset.univ.val := by
      rw [e1', hroots0, hev0]
      simp
    have hmem : hM.eigenvalues₀ i ∈ (↑(List.ofFn hM.eigenvalues₀) : Multiset ℝ) :=
      Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [hevals] at hmem
    obtain ⟨b, _, hb⟩ := Multiset.mem_map.mp hmem
    rw [show hM.eigenvalues₀ i = 0 from hb.symm, zero_mul]
  · have hdne : d ≠ 0 := ne_of_gt hpos
    have hpoly : (d • N).charpoly = (N.charpoly).scaleRoots d := by
      apply Polynomial.funext
      intro x
      have hdx : d * (x / d) = x := by field_simp
      rw [← hdx, Matrix.eval_charpoly, Polynomial.scaleRoots_eval_mul]
      have hscalar : Matrix.scalar (Fin n) (d * (x / d)) = d • Matrix.scalar (Fin n) (x / d) := by
        ext a b
        simp [Matrix.scalar, Matrix.diagonal, Matrix.smul_apply]
      have hmat : Matrix.scalar (Fin n) (d * (x / d)) - d • N
          = d • (Matrix.scalar (Fin n) (x / d) - N) := by
        rw [smul_sub, hscalar]
      rw [hmat, Matrix.det_smul, ← Matrix.eval_charpoly, Matrix.charpoly_natDegree_eq_dim]
    have hroots : ((d • N).charpoly).roots = (N.charpoly).roots.map (fun x => d * x) := by
      rw [hpoly]
      exact Polynomial.roots_scaleRoots N.charpoly (isUnit_iff_ne_zero.mpr hdne)
    have hcongr : Multiset.map RCLike.re ((N.charpoly.roots).map (fun x => d * x))
        = (Multiset.map RCLike.re (N.charpoly.roots)).map (fun x => d * x) := by
      rw [Multiset.map_map, Multiset.map_map]
      congr 1
    have e1 : (↑(List.ofFn hM.eigenvalues₀) : Multiset ℝ)
        = Multiset.map RCLike.re (((d • N).charpoly).roots) := by
      rw [← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀ hM]
      exact Multiset.sort_eq _ _
    have e2 : (↑(List.ofFn hN.eigenvalues₀) : Multiset ℝ)
        = Multiset.map RCLike.re (N.charpoly.roots) := by
      rw [← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀ hN]
      exact Multiset.sort_eq _ _
    have hget : ∀ {m : ℕ} (f : Fin m → ℝ),
        List.get (List.ofFn f) = fun i => f ⟨i.1, by simpa using i.2⟩ := by
      intro m f
      funext i
      simp
    have hantiGE : ∀ {m : ℕ} {f : Fin m → ℝ}, Antitone f → (List.ofFn f).SortedGE := by
      intro m f hf
      show Antitone (List.get (List.ofFn f))
      rw [hget]
      intro a b hab
      exact hf (by simpa using hab)
    have hGE₁ : (List.ofFn hM.eigenvalues₀).SortedGE :=
      hantiGE (Matrix.IsHermitian.eigenvalues₀_antitone hM)
    have hGE₂ : (List.ofFn ((fun x => d * x) ∘ hN.eigenvalues₀)).SortedGE :=
      hantiGE (fun a b hab => mul_le_mul_of_nonneg_left
        (Matrix.IsHermitian.eigenvalues₀_antitone hN hab) hd)
    have h1 : List.ofFn ((fun x => d * x) ∘ hN.eigenvalues₀)
        = (List.ofFn hN.eigenvalues₀).map (fun x => d * x) :=
      (List.map_ofFn hN.eigenvalues₀ (fun x => d * x)).symm
    have e3 : (↑(List.ofFn ((fun x => d * x) ∘ hN.eigenvalues₀)) : Multiset ℝ)
        = (Multiset.map RCLike.re (N.charpoly.roots)).map (fun x => d * x) := by
      rw [h1, ← Multiset.map_coe, e2]
    have hperm : (List.ofFn hM.eigenvalues₀).Perm
        (List.ofFn ((fun x => d * x) ∘ hN.eigenvalues₀)) := by
      refine Multiset.coe_eq_coe.mp ?_
      rw [e1, e3, ← hcongr, ← hroots]
    have key : List.ofFn hM.eigenvalues₀ = List.ofFn ((fun x => d * x) ∘ hN.eigenvalues₀) :=
      List.Perm.eq_of_sortedGE hGE₁ hGE₂ hperm
    exact congrFun (List.ofFn_inj.mp key) i
  /- @proof-region region.target-node.session.f20ff0bb004c9bd5 end -/

end Statlib.Imported

end


