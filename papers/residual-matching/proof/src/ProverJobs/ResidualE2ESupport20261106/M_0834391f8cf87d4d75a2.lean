import Statlib.HighDim.SpectralPerturbation.Eigenvalues
import Statlib.HighDim.Vocabulary.Spectral
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
theorem statopia_math_node_98982382_efcf3d6b : ∀ (n : ℕ) (B C : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (y : ℝ)
    (hrank : (C - B).rank ≤ 2),
    |((Fintype.card {i : Fin n // hB.eigenvalues i ≤ y} : ℝ) -
      (Fintype.card {i : Fin n // hC.eigenvalues i ≤ y} : ℝ))| ≤ 2 := by
  /- @proof-region region.target-node.session.b4f3978f868311e0 begin -/
  intro n B C hB hC y hrank
  have key : ∀ (P Q : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
      (c : ℝ), (Q - P).rank ≤ 2 →
      (Fintype.card {i : Fin n // hP.eigenvalues i ≤ c} : ℝ) ≤
        (Fintype.card {i : Fin n // hQ.eigenvalues i ≤ c} : ℝ) + 2 := by
    intro P Q hP hQ c hrk
    set aP : ℕ := (Fintype.card {i : Fin n // hP.eigenvalues i ≤ c}) with haP
    set aQ : ℕ := (Fintype.card {i : Fin n // hQ.eigenvalues i ≤ c}) with haQ
    set bQ : ℕ := (Fintype.card {i : Fin n // c < hQ.eigenvalues i}) with hbQ
    have hfinV : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
    set S := Statlib.HighDim.Vocabulary.eigenSubspaceLe P hP c with hSdef
    set G := Statlib.HighDim.Vocabulary.eigenSubspaceGt Q hQ c with hGdef
    set K := LinearMap.ker (Matrix.toEuclideanLin (Q - P)) with hKdef
    set D := G ⊓ K with hDdef
    have hS : Module.finrank ℝ ↥S = aP := by
      rw [hSdef, Statlib.HighDim.SpectralPerturbation.finrank_eigenSubspaceLe]
    have hG : Module.finrank ℝ ↥G = bQ := by
      rw [hGdef, Statlib.HighDim.SpectralPerturbation.finrank_eigenSubspaceGt]
    have hK : Module.finrank ℝ ↥K ≥ n - 2 := by
      rw [hKdef]
      have hr : Module.finrank ℝ ↥(LinearMap.range (Matrix.toEuclideanLin (Q - P))) ≤ 2 := by
        rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
          ← Matrix.rank_eq_finrank_range_toLin (Q - P)
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
        exact hrk
      have hker := LinearMap.finrank_range_add_finrank_ker (Matrix.toEuclideanLin (Q - P))
      rw [hfinV] at hker
      omega
    have hbQeq : bQ = n - aQ := by
      rw [hbQ, haQ]
      have hc : Fintype.card {i : Fin n // c < hQ.eigenvalues i} =
          Fintype.card {i : Fin n // ¬ hQ.eigenvalues i ≤ c} :=
        Fintype.card_congr
          { toFun := fun ⟨i, hi⟩ => ⟨i, not_le.mpr hi⟩
            invFun := fun ⟨i, hi⟩ => ⟨i, not_le.mp hi⟩
            left_inv := fun ⟨i, _⟩ => Subtype.ext rfl
            right_inv := fun ⟨i, _⟩ => Subtype.ext rfl }
      rw [hc, Fintype.card_subtype_compl, Fintype.card_fin]
    have hinf : Module.finrank ℝ ↥(G ⊔ K) + Module.finrank ℝ ↥(G ⊓ K) =
        Module.finrank ℝ ↥G + Module.finrank ℝ ↥K :=
      Submodule.finrank_sup_add_finrank_inf_eq G K
    have hGKle : Module.finrank ℝ ↥(G ⊔ K) ≤ n := by
      have h := Submodule.finrank_le (G ⊔ K)
      rwa [hfinV] at h
    have hlower : bQ - 2 ≤ Module.finrank ℝ ↥D := by
      rw [hDdef]
      omega
    have hbot : D ⊓ S = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf] at hx
      obtain ⟨hxD, hxS⟩ := hx
      rw [hDdef, Submodule.mem_inf] at hxD
      obtain ⟨hxG, hxK⟩ := hxD
      rw [hGdef] at hxG
      rw [hKdef] at hxK
      rw [hSdef] at hxS
      by_contra hx0
      have hQgt := Statlib.HighDim.SpectralPerturbation.eigenSubspaceGt_rayleigh_gt Q hQ c hxG hx0
      have heq : inner ℝ ((Matrix.toEuclideanLin Q) x) x =
          inner ℝ ((Matrix.toEuclideanLin P) x) x := by
        have hsub : Matrix.toEuclideanLin (Q - P) =
            Matrix.toEuclideanLin Q - Matrix.toEuclideanLin P :=
          map_sub (Matrix.toEuclideanLin) Q P
        have h0 := LinearMap.mem_ker.mp hxK
        rw [hsub] at h0
        rw [LinearMap.sub_apply] at h0
        have hQP : (Matrix.toEuclideanLin Q) x = (Matrix.toEuclideanLin P) x := sub_eq_zero.mp h0
        rw [hQP]
      have hPle := Statlib.HighDim.SpectralPerturbation.eigenSubspaceLe_rayleigh_le P hP c hxS
      rw [heq] at hQgt
      linarith
    have hsum_le : Module.finrank ℝ ↥D + Module.finrank ℝ ↥S ≤ n := by
      have hb : Module.finrank ℝ ↥(D ⊓ S) = 0 := by rw [hbot, finrank_bot]
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq D S
      rw [hb, add_zero] at hsup
      rw [← hsup]
      have h := Submodule.finrank_le (D ⊔ S)
      rwa [hfinV] at h
    have hupper : Module.finrank ℝ ↥D ≤ n - aP := by
      have h2 : Module.finrank ℝ ↥D + aP ≤ n := by
        rw [← hS]; exact hsum_le
      omega
    have haPn : aP ≤ n := by
      have h := Submodule.finrank_le S
      rw [hS, hfinV] at h
      exact h
    have haQn : aQ ≤ n := by
      have h := Submodule.finrank_le (Statlib.HighDim.Vocabulary.eigenSubspaceLe Q hQ c)
      rw [Statlib.HighDim.SpectralPerturbation.finrank_eigenSubspaceLe, ← haQ, hfinV] at h
      exact h
    have hgoalN : aP ≤ aQ + 2 := by
      have hcomb : bQ - 2 ≤ n - aP := le_trans hlower hupper
      omega
    exact_mod_cast hgoalN
  have hrank2 : (B - C).rank ≤ 2 := by
    have hspan : Submodule.span ℝ (Set.range (B - C).col) =
        Submodule.span ℝ (Set.range (C - B).col) := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have hcol : (B - C).col j = -((C - B).col j) := by
          funext i
          simp only [Matrix.col_apply, Pi.neg_apply, Matrix.sub_apply, neg_sub]
        have hsm : (B - C).col j = (-1 : ℝ) • (C - B).col j := by
          rw [hcol]; simp
        rw [hsm]
        exact Submodule.smul_mem _ (-1 : ℝ) (Submodule.subset_span ⟨j, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have hcol : (B - C).col j = -((C - B).col j) := by
          funext i
          simp only [Matrix.col_apply, Pi.neg_apply, Matrix.sub_apply, neg_sub]
        have hthis : -((C - B).col j) ∈ Submodule.span ℝ (Set.range (B - C).col) := by
          rw [← hcol]
          exact Submodule.subset_span ⟨j, rfl⟩
        have hmem : (-1 : ℝ) • (-((C - B).col j)) ∈ Submodule.span ℝ (Set.range (B - C).col) :=
          Submodule.smul_mem _ (-1 : ℝ) hthis
        simpa using hmem
    rw [Matrix.rank_eq_finrank_span_cols (B - C), hspan,
      ← Matrix.rank_eq_finrank_span_cols (C - B)]
    exact hrank
  have h1 := key B C hB hC y hrank
  have h2 := key C B hC hB y hrank2
  rw [abs_le]
  constructor
  · linarith
  · linarith
  /- @proof-region region.target-node.session.b4f3978f868311e0 end -/

end Statlib.Imported

