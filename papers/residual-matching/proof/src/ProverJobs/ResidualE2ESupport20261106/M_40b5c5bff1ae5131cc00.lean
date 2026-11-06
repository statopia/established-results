import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_84eb2aee11d7bcdc25b2

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
theorem statopia_math_node_3439180840_d82a2d61 : ∀ (p m : ℕ) (hpm : p ≤ m) (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.IsHermitian)
    (hnn : ∀ i : Fin p, 0 ≤ hS.eigenvalues i)
    (hT : Matrix.IsHermitian (fun i j : Fin m =>
      if h : (i : ℕ) < p ∧ (j : ℕ) < p then S ⟨(i : ℕ), h.1⟩ ⟨(j : ℕ), h.2⟩ else 0))
    (k : Fin m) (hk : (k : ℕ) < p),
    hT.eigenvalues₀ ⟨(k : ℕ), by simpa using k.isLt⟩
      = hS.eigenvalues₀ ⟨(k : ℕ), by simpa using hk⟩ := by
  /- @proof-region region.target-node.session.b8e21164113bb27b begin -/
  intro p m hpm S hS hnn hT k hk
  have hantiS : Antitone hS.eigenvalues₀ := LinearMap.IsSymmetric.eigenvalues_antitone _ _
  have hantiT : Antitone hT.eigenvalues₀ := LinearMap.IsSymmetric.eigenvalues_antitone _ _
  let f : Fin p ⊕ Fin (m - p) → Fin m := fun s =>
    match s with
    | Sum.inl i => ⟨(i : ℕ), lt_of_lt_of_le i.isLt hpm⟩
    | Sum.inr j => ⟨p + (j : ℕ), by have := j.isLt; omega⟩
  let g : Fin m → Fin p ⊕ Fin (m - p) := fun i =>
    if h : (i : ℕ) < p then Sum.inl ⟨(i : ℕ), h⟩
    else Sum.inr ⟨(i : ℕ) - p, by have := i.isLt; omega⟩
  have hgf : ∀ s : Fin p ⊕ Fin (m - p), g (f s) = s := by
    rintro (i | j)
    · dsimp only [f, g]
      rw [dif_pos i.isLt]
    · dsimp only [f, g]
      rw [dif_neg (by have := j.isLt; omega)]
      exact congrArg Sum.inr (Fin.ext (by show p + (j : ℕ) - p = (j : ℕ); omega))
  have hfg : ∀ i : Fin m, f (g i) = i := by
    intro i
    by_cases h : (i : ℕ) < p
    · dsimp only [f, g]
      rw [dif_pos h]
    · dsimp only [f, g]
      rw [dif_neg h]
      exact Fin.ext (by show p + ((i : ℕ) - p) = (i : ℕ); omega)
  let e : Fin p ⊕ Fin (m - p) ≃ Fin m :=
    { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg }
  let T : Matrix (Fin m) (Fin m) ℝ :=
    fun i j => if h : (i : ℕ) < p ∧ (j : ℕ) < p then S ⟨(i : ℕ), h.1⟩ ⟨(j : ℕ), h.2⟩ else 0
  have hTmat : T = Matrix.reindex e e (Matrix.fromBlocks S 0 0 0) := by
    ext i j
    show T i j = (Matrix.fromBlocks S 0 0 0) (g i) (g j)
    by_cases hi : (i : ℕ) < p <;> by_cases hj : (j : ℕ) < p <;>
      simp [T, g, hi, hj, Matrix.fromBlocks]
  have hchar : T.charpoly = S.charpoly * Polynomial.X ^ (m - p) := by
    rw [hTmat, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁, Matrix.charpoly_zero]
    simp [Fintype.card_fin]
  set τT : Fin m ≃ Fin (Fintype.card (Fin m)) :=
    (Fintype.equivOfCardEq (by simp : Fintype.card (Fin (Fintype.card (Fin m))) = Fintype.card (Fin m))).symm with hτT
  set τS : Fin p ≃ Fin (Fintype.card (Fin p)) :=
    (Fintype.equivOfCardEq (by simp : Fintype.card (Fin (Fintype.card (Fin p))) = Fintype.card (Fin p))).symm with hτS
  have hevT : ∀ i : Fin m, hT.eigenvalues i = hT.eigenvalues₀ (τT i) := fun i => rfl
  have hevS : ∀ i : Fin p, hS.eigenvalues i = hS.eigenvalues₀ (τS i) := fun i => rfl
  have hnonneg : ∀ j : Fin (Fintype.card (Fin p)), 0 ≤ hS.eigenvalues₀ j := by
    intro j
    have h := hnn (τS.symm j)
    simpa [hevS] using h
  have hmapT : Multiset.map hT.eigenvalues (Finset.univ : Finset (Fin m)).val
      = Multiset.map hT.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card (Fin m)))).val := by
    have hτ : Multiset.map (⇑τT) (Finset.univ : Finset (Fin m)).val
        = (Finset.univ : Finset (Fin (Fintype.card (Fin m)))).val :=
      congrArg Finset.val (Finset.map_univ_equiv τT)
    calc Multiset.map hT.eigenvalues (Finset.univ : Finset (Fin m)).val
        = Multiset.map (hT.eigenvalues₀ ∘ τT) (Finset.univ : Finset (Fin m)).val := by
          rw [show hT.eigenvalues = hT.eigenvalues₀ ∘ τT from funext hevT]
      _ = Multiset.map hT.eigenvalues₀ (Multiset.map τT (Finset.univ : Finset (Fin m)).val) :=
          (Multiset.map_map hT.eigenvalues₀ τT (Finset.univ : Finset (Fin m)).val).symm
      _ = Multiset.map hT.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card (Fin m)))).val := by
          rw [hτ]
  have hmapS : Multiset.map hS.eigenvalues (Finset.univ : Finset (Fin p)).val
      = Multiset.map hS.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card (Fin p)))).val := by
    have hτ : Multiset.map (⇑τS) (Finset.univ : Finset (Fin p)).val
        = (Finset.univ : Finset (Fin (Fintype.card (Fin p)))).val :=
      congrArg Finset.val (Finset.map_univ_equiv τS)
    calc Multiset.map hS.eigenvalues (Finset.univ : Finset (Fin p)).val
        = Multiset.map (hS.eigenvalues₀ ∘ τS) (Finset.univ : Finset (Fin p)).val := by
          rw [show hS.eigenvalues = hS.eigenvalues₀ ∘ τS from funext hevS]
      _ = Multiset.map hS.eigenvalues₀ (Multiset.map τS (Finset.univ : Finset (Fin p)).val) :=
          (Multiset.map_map hS.eigenvalues₀ τS (Finset.univ : Finset (Fin p)).val).symm
      _ = Multiset.map hS.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card (Fin p)))).val := by
          rw [hτ]
  have hmult : Multiset.map hT.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card (Fin m)))).val
      = Multiset.map hS.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card (Fin p)))).val
        + (m - p) • {(0 : ℝ)} := by
    rw [← hmapT, ← hmapS]
    have hX : (Polynomial.X ^ (m - p) : Polynomial ℝ).roots = (m - p) • {(0 : ℝ)} :=
      Polynomial.roots_X_pow _
    have hmon : (S.charpoly * Polynomial.X ^ (m - p) : Polynomial ℝ) ≠ 0 :=
      mul_ne_zero (Matrix.charpoly_monic S).ne_zero (Polynomial.monic_X_pow (m - p)).ne_zero
    calc Multiset.map hT.eigenvalues (Finset.univ : Finset (Fin m)).val
        = Multiset.map (RCLike.ofReal ∘ hT.eigenvalues) (Finset.univ : Finset (Fin m)).val := rfl
      _ = T.charpoly.roots := hT.roots_charpoly_eq_eigenvalues.symm
      _ = (S.charpoly * Polynomial.X ^ (m - p)).roots := by rw [hchar]
      _ = S.charpoly.roots + (Polynomial.X ^ (m - p) : Polynomial ℝ).roots := Polynomial.roots_mul hmon
      _ = Multiset.map (RCLike.ofReal ∘ hS.eigenvalues) (Finset.univ : Finset (Fin p)).val
            + (Polynomial.X ^ (m - p) : Polynomial ℝ).roots := by
          rw [hS.roots_charpoly_eq_eigenvalues]
      _ = Multiset.map (RCLike.ofReal ∘ hS.eigenvalues) (Finset.univ : Finset (Fin p)).val
            + (m - p) • {(0 : ℝ)} := by rw [hX]
      _ = Multiset.map hS.eigenvalues (Finset.univ : Finset (Fin p)).val + (m - p) • {(0 : ℝ)} := rfl
  have hle : Fintype.card (Fin p) ≤ Fintype.card (Fin m) := by simpa using hpm
  have hsub : Fintype.card (Fin m) - Fintype.card (Fin p) = m - p := by
    simp
  have hmult' : Multiset.map hT.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card (Fin m)))).val
      = Multiset.map hS.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card (Fin p)))).val
        + (Fintype.card (Fin m) - Fintype.card (Fin p)) • ({(0 : ℝ)} : Multiset ℝ) := by
    rw [hsub]
    exact hmult
  have hkS : ((k : Fin m) : ℕ) < Fintype.card (Fin p) := by
    simpa only [Fintype.card_fin] using hk
  have hkT : ((k : Fin m) : ℕ) < Fintype.card (Fin m) := lt_of_lt_of_le hkS hle
  have hmain : hT.eigenvalues₀ ⟨(k : ℕ), by simpa using k.isLt⟩
      = hS.eigenvalues₀ ⟨(k : ℕ), by simpa using hk⟩ :=
    statopia_math_node_3729350466_f4b48ace (Fintype.card (Fin p)) (Fintype.card (Fin m))
      hT.eigenvalues₀ hS.eigenvalues₀ hantiT hantiS hnonneg hle hmult'
      ((k : Fin m) : ℕ) hkS hkT
  exact hmain
  /- @proof-region region.target-node.session.b8e21164113bb27b end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3439180840_d82a2d61


