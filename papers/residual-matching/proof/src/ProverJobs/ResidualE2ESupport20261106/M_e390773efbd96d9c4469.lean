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
theorem statopia_math_node_1809001392_3907642a : ∀ (m n : ℕ)
    (A : Matrix (Fin m) (Fin n) ℝ),
    (Finset.univ.val.map (fun i : Fin n =>
        (Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀
          (Fin.cast (Fintype.card_fin n).symm i))) ^ 2)) =
      (Finset.univ.val.map (fun i : Fin n =>
        (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)) := by
  /- @proof-region region.target-node.session.11e9e311827cf8ad begin -/
  intro m n A
  have hM : (A.conjTranspose * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hpsd : (A.conjTranspose * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have keyEmb : ∀ {α β : Type} [Fintype α] [Fintype β] (g : α → β), Function.Injective g →
      Fintype.card α = Fintype.card β → ∀ (f : β → ℝ),
      Multiset.map (fun a : α => f (g a)) (Finset.univ.val : Multiset α)
        = Multiset.map f (Finset.univ.val : Multiset β) := by
    intro α β _ _ g hg hcard f
    have h1 : (Finset.univ.map ⟨g, hg⟩ : Finset β) = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa [Finset.card_map] using hcard
    calc Multiset.map (fun a : α => f (g a)) (Finset.univ.val : Multiset α)
        = Multiset.map f (Multiset.map g (Finset.univ.val : Multiset α)) := by
          rw [Multiset.map_map]; rfl
      _ = Multiset.map f ((Finset.univ.map ⟨g, hg⟩ : Finset β).val) := rfl
      _ = Multiset.map f (Finset.univ.val : Multiset β) := by rw [h1]
  have keyE : ∀ {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ),
      Multiset.map (fun a : α => f (e a)) (Finset.univ.val : Multiset α)
        = Multiset.map f (Finset.univ.val : Multiset β) := by
    intro α β _ _ e f
    have h1 : (Finset.univ.map e.toEmbedding : Finset β) = Finset.univ := Finset.map_univ_equiv e
    calc Multiset.map (fun a : α => f (e a)) (Finset.univ.val : Multiset α)
        = Multiset.map f (Multiset.map (⇑e) (Finset.univ.val : Multiset α)) := by
          rw [Multiset.map_map]; rfl
      _ = Multiset.map f ((Finset.univ.map e.toEmbedding : Finset β).val) := rfl
      _ = Multiset.map f (Finset.univ.val : Multiset β) := by rw [h1]
  have hrootR : ∀ {k : Type} [Fintype k] [DecidableEq k] (M : Matrix k k ℝ) (hMr : M.IsHermitian),
      M.charpoly.roots = Multiset.map hMr.eigenvalues (Finset.univ.val : Multiset k) := by
    intro k _ _ M hMr
    simpa using Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hMr
  have hcharInv : ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (M : Matrix β β ℝ) (e : α ≃ β), (M.submatrix ⇑e ⇑e).charpoly = M.charpoly := by
    intro α β _ _ _ _ M e
    exact Matrix.charpoly_reindex e.symm M
  have hgen : ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (M : Matrix β β ℝ) (hMr : M.IsHermitian) (e : α ≃ β),
      Multiset.map (hMr.submatrix ⇑e).eigenvalues (Finset.univ.val : Multiset α)
        = Multiset.map hMr.eigenvalues (Finset.univ.val : Multiset β) := by
    intro α β _ _ _ _ M hMr e
    have ha : (M.submatrix ⇑e ⇑e).charpoly.roots
        = Multiset.map (hMr.submatrix ⇑e).eigenvalues (Finset.univ.val : Multiset α) :=
      hrootR _ (hMr.submatrix ⇑e)
    have hb : M.charpoly.roots = Multiset.map hMr.eigenvalues (Finset.univ.val : Multiset β) :=
      hrootR _ hMr
    rw [← ha, ← hb]
    exact congrArg (fun p => p.roots) (hcharInv M e)
  have hE : Multiset.map hM.eigenvalues₀ (Finset.univ.val : Multiset (Fin (Fintype.card (Fin n))))
      = Multiset.map hM.eigenvalues (Finset.univ.val : Multiset (Fin n)) := by
    exact (keyE (α := Fin n) (β := Fin (Fintype.card (Fin n))) ?_ hM.eigenvalues₀).symm
  have hnn : ∀ j : Fin (Fintype.card (Fin n)), 0 ≤ hM.eigenvalues₀ j := by
    intro j
    have hmem : hM.eigenvalues₀ j ∈
        Multiset.map hM.eigenvalues (Finset.univ.val : Multiset (Fin n)) := by
      rw [← hE]
      exact Multiset.mem_map.mpr ⟨j, by simp, rfl⟩
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hmem
    rw [← hi]
    exact Matrix.PosSemidef.eigenvalues_nonneg hpsd i
  have hsq : (fun i : Fin n => (Real.sqrt (hM.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i))) ^ 2)
      = fun i : Fin n => hM.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) := by
    funext i
    exact Real.sq_sqrt (hnn (Fin.cast (Fintype.card_fin n).symm i))
  have hcast : Multiset.map (fun i : Fin n => hM.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i))
        (Finset.univ.val : Multiset (Fin n))
      = Multiset.map hM.eigenvalues₀ (Finset.univ.val : Multiset (Fin (Fintype.card (Fin n)))) :=
    keyEmb (Fin.cast (Fintype.card_fin n).symm) (Fin.cast_injective (Fintype.card_fin n).symm)
      (by simp) hM.eigenvalues₀
  rw [hsq, hcast, hE]
  /- @proof-region region.target-node.session.11e9e311827cf8ad end -/

end Statlib.Imported

