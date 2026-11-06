import Statlib.HighDim.SpectralPerturbation.Eigenvalues
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2989538586_f823134e : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian)
    (hpsd : ∀ (x : EuclideanSpace ℝ (Fin n)), 0 ≤ inner ℝ ((Matrix.toEuclideanLin M) x) x)
    (hn : 0 < n),
    hM.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm ⟨0, hn⟩) = ‖M‖ := by
  /- @proof-region region.target-node.session.92530713ca05bfbd begin -/
  intro n M hM hpsd hn
  have hle : hM.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm ⟨0, hn⟩) ≤ ‖M‖ := by
    set i0 : Fin (Fintype.card (Fin n)) := Fin.cast (Fintype.card_fin n).symm ⟨0, hn⟩
    have hT : (Matrix.toEuclideanLin M).IsSymmetric :=
      Matrix.IsHermitian.eigenvalues₀._proof_4 hM
    set v : EuclideanSpace ℝ (Fin n) := hT.eigenvectorBasis finrank_euclideanSpace i0 with hvdef
    have hb : (Matrix.toEuclideanLin M) v = (hT.eigenvalues finrank_euclideanSpace i0) • v :=
      LinearMap.IsSymmetric.apply_eigenvectorBasis hT finrank_euclideanSpace i0
    have hvn : ‖v‖ = 1 := (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.1 i0
    have hvv : inner ℝ v v = 1 := by
      rw [real_inner_self_eq_norm_sq, hvn, one_pow]
    have hkey : inner ℝ ((Matrix.toEuclideanLin M) v) v
        = hT.eigenvalues finrank_euclideanSpace i0 * inner ℝ v v := by
      rw [hb, real_inner_smul_left]
    calc hM.eigenvalues₀ i0 = hT.eigenvalues finrank_euclideanSpace i0 := rfl
      _ = hT.eigenvalues finrank_euclideanSpace i0 * inner ℝ v v := by rw [hvv, mul_one]
      _ = inner ℝ ((Matrix.toEuclideanLin M) v) v := hkey.symm
      _ ≤ ‖M‖ * ‖v‖ ^ 2 :=
        Statlib.HighDim.SpectralPerturbation.inner_self_op_le_l2_opNorm_mul_norm_sq M v
      _ = ‖M‖ := by rw [hvn, one_pow, mul_one]
  have hge : ‖M‖ ≤ hM.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm ⟨0, hn⟩) := by
    set i0 : Fin (Fintype.card (Fin n)) := Fin.cast (Fintype.card_fin n).symm ⟨0, hn⟩ with hi0
    have hT : (Matrix.toEuclideanLin M).IsSymmetric :=
      Matrix.IsHermitian.eigenvalues₀._proof_4 hM
    set b : OrthonormalBasis (Fin (Fintype.card (Fin n))) ℝ (EuclideanSpace ℝ (Fin n)) :=
      hT.eigenvectorBasis finrank_euclideanSpace with hb
    have hi0le : ∀ k : Fin (Fintype.card (Fin n)), i0 ≤ k := by
      intro k
      rw [Fin.le_def]
      have h0 : i0.val = 0 := by simp [hi0]
      omega
    have hanti : ∀ k, hT.eigenvalues finrank_euclideanSpace k
        ≤ hT.eigenvalues finrank_euclideanSpace i0 :=
      fun k => LinearMap.IsSymmetric.eigenvalues_antitone hT finrank_euclideanSpace (hi0le k)
    have hnn : ∀ k, 0 ≤ hT.eigenvalues finrank_euclideanSpace k := by
      intro k
      have hbk : ‖b k‖ = 1 := b.orthonormal.1 k
      have hap : (Matrix.toEuclideanLin M) (b k)
          = hT.eigenvalues finrank_euclideanSpace k • b k :=
        LinearMap.IsSymmetric.apply_eigenvectorBasis hT finrank_euclideanSpace k
      have hin : inner ℝ (hT.eigenvalues finrank_euclideanSpace k • b k) (b k)
          = hT.eigenvalues finrank_euclideanSpace k := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hbk, one_pow, mul_one]
      have hpos := hpsd (b k)
      rwa [hap, hin] at hpos
    have hpoint : ∀ x : EuclideanSpace ℝ (Fin n),
        ‖(Matrix.toEuclideanLin M) x‖ ≤ hT.eigenvalues finrank_euclideanSpace i0 * ‖x‖ := by
      intro x
      have hTx : ∀ k, inner ℝ (b k) ((Matrix.toEuclideanLin M) x)
          = hT.eigenvalues finrank_euclideanSpace k * inner ℝ (b k) x := by
        intro k
        rw [hb]
        rw [(hT ((hT.eigenvectorBasis finrank_euclideanSpace) k) x).symm,
          LinearMap.IsSymmetric.apply_eigenvectorBasis hT finrank_euclideanSpace k]
        simp [real_inner_smul_left]
      have hTxnorm : ‖(Matrix.toEuclideanLin M) x‖ ^ 2
          = ∑ k, (hT.eigenvalues finrank_euclideanSpace k * inner ℝ (b k) x) ^ 2 := by
        rw [← OrthonormalBasis.sum_sq_inner_right b ((Matrix.toEuclideanLin M) x)]
        exact Finset.sum_congr rfl (fun k _ => by rw [hTx k])
      have hxnorm : ‖x‖ ^ 2 = ∑ k, inner ℝ (b k) x ^ 2 :=
        (OrthonormalBasis.sum_sq_inner_right b x).symm
      have hterm : ∀ k, (hT.eigenvalues finrank_euclideanSpace k * inner ℝ (b k) x) ^ 2
          ≤ (hT.eigenvalues finrank_euclideanSpace i0 * inner ℝ (b k) x) ^ 2 := by
        intro k
        have h1 := hanti k
        have h2 := hnn k
        have h3 := hnn i0
        nlinarith [sq_nonneg (inner ℝ (b k) x),
          mul_nonneg (sub_nonneg.mpr h1) (add_nonneg h3 h2)]
      have hfact : ∑ k, (hT.eigenvalues finrank_euclideanSpace i0 * inner ℝ (b k) x) ^ 2
          = hT.eigenvalues finrank_euclideanSpace i0 ^ 2 * ‖x‖ ^ 2 := by
        rw [hxnorm, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      have hsq : ‖(Matrix.toEuclideanLin M) x‖ ^ 2
          ≤ (hT.eigenvalues finrank_euclideanSpace i0 * ‖x‖) ^ 2 := by
        rw [hTxnorm, mul_pow]
        exact le_trans (Finset.sum_le_sum (fun k _ => hterm k)) (le_of_eq hfact)
      have hb0 : (0 : ℝ) ≤ hT.eigenvalues finrank_euclideanSpace i0 * ‖x‖ :=
        mul_nonneg (hnn i0) (norm_nonneg x)
      have hs := sq_le_sq.mp hsq
      rwa [abs_of_nonneg (norm_nonneg ((Matrix.toEuclideanLin M) x)),
        abs_of_nonneg hb0] at hs
    show ‖M‖ ≤ hT.eigenvalues finrank_euclideanSpace i0
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound
    · exact hnn i0
    · intro x
      exact hpoint x
  exact le_antisymm hle hge
  /- @proof-region region.target-node.session.92530713ca05bfbd end -/

end Statlib.Imported

