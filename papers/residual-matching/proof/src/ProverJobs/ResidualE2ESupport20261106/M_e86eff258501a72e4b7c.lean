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
theorem statopia_math_node_645163511_ea48f44b : ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin n) (hk : min m n ≤ k.val),
    svals A k = 0 := by
  /- @proof-region region.target-node.session.fa2e7149acfccfbc begin -/
  intro m n A k hk
  have hG : (A.conjTranspose * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hsv : svals A k = Real.sqrt (hG.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k)) := rfl
  have hm : (A.conjTranspose * A).rank ≤ m :=
    le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_width _)
  have hn : (A.conjTranspose * A).rank ≤ n :=
    le_trans (Matrix.rank_mul_le_right _ _) (Matrix.rank_le_width _)
  have hrank : (A.conjTranspose * A).rank ≤ k.val := le_trans (le_min hm hn) hk
  have hnonneg : ∀ i : Fin n, 0 ≤ hG.eigenvalues i :=
    fun i => Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i
  have hanti : Antitone hG.eigenvalues₀ := by
    intro i j hij
    simp only [Matrix.IsHermitian.eigenvalues₀]
    exact LinearMap.IsSymmetric.eigenvalues_antitone _ _ hij
  have hbr : ∀ i : Fin n, hG.eigenvalues i =
      hG.eigenvalues₀ ((Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin n))) (β := Fin n)
        (by simp)).symm i) := by
    intro i
    simp only [Matrix.IsHermitian.eigenvalues]
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin n))) (β := Fin n) (by simp)
  have hval : ∀ j : Fin (Fintype.card (Fin n)), hG.eigenvalues₀ j = hG.eigenvalues (e j) := by
    intro j
    rw [hbr (e j)]
    show hG.eigenvalues₀ j = hG.eigenvalues₀ (e.symm (e j))
    rw [e.symm_apply_apply]
  have hnonneg₀ : ∀ j : Fin (Fintype.card (Fin n)), 0 ≤ hG.eigenvalues₀ j := by
    intro j
    rw [hval j]
    exact hnonneg (e j)
  have hcard : Fintype.card {j : Fin (Fintype.card (Fin n)) // hG.eigenvalues₀ j ≠ 0}
      = (A.conjTranspose * A).rank := by
    rw [Matrix.IsHermitian.rank_eq_card_non_zero_eigs hG]
    refine Fintype.card_congr ⟨fun x => ⟨e x.1, ?_⟩, fun y => ⟨e.symm y.1, ?_⟩, ?_, ?_⟩
    · rw [← hval x.1]
      exact x.2
    · have h : hG.eigenvalues₀ (e.symm y.1) = hG.eigenvalues y.1 := by
        rw [hval (e.symm y.1), e.apply_symm_apply]
      rw [h]
      exact y.2
    · intro x
      exact Subtype.ext (e.symm_apply_apply x.1)
    · intro y
      exact Subtype.ext (e.apply_symm_apply y.1)
  have hle : hG.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have hbound : k.val + 1 ≤ (A.conjTranspose * A).rank := by
      rw [← hcard]
      let g₀ : Fin (k.val + 1) → Fin (Fintype.card (Fin n)) := fun t => ⟨t.val, by
        have h1 := t.isLt
        have h2 := k.isLt
        simp only [Fintype.card_fin]
        omega⟩
      have hgval : ∀ t : Fin (k.val + 1), (g₀ t).val = t.val := fun t => rfl
      have hgle : ∀ t : Fin (k.val + 1), g₀ t ≤ Fin.cast (Fintype.card_fin n).symm k := by
        intro t
        have h2 : (Fin.cast (Fintype.card_fin n).symm k).val = k.val := by simp
        show t.val ≤ (Fin.cast (Fintype.card_fin n).symm k).val
        rw [h2]
        have := t.isLt
        omega
      have hnonzero : ∀ t : Fin (k.val + 1), hG.eigenvalues₀ (g₀ t) ≠ 0 := by
        intro t hzero
        have h1 := hanti (hgle t)
        linarith
      let F : Fin (k.val + 1) → {j : Fin (Fintype.card (Fin n)) // hG.eigenvalues₀ j ≠ 0} :=
        fun t => ⟨g₀ t, hnonzero t⟩
      have hinj : Function.Injective F := by
        intro a b hab
        have hv : (g₀ a).val = (g₀ b).val := by
          simpa using
            congrArg (fun x : {j : Fin (Fintype.card (Fin n)) // hG.eigenvalues₀ j ≠ 0} => x.1.val) hab
        rw [hgval a, hgval b] at hv
        exact Fin.ext hv
      have hcle := Fintype.card_le_of_injective F hinj
      simpa using hcle
    omega
  have h0 : hG.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k) = 0 :=
    le_antisymm hle (hnonneg₀ _)
  rw [hsv, h0, Real.sqrt_zero]
  /- @proof-region region.target-node.session.fa2e7149acfccfbc end -/

end Statlib.Imported

