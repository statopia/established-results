import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3711227582_dba90c3d : ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hB : B.PosSemidef)
    (hBc : (c • (1 : Matrix (Fin n) (Fin n) ℝ) - B).PosSemidef), ‖B‖ ≤ c := by
  /- @proof-region region.target-node.session.ed9280725fa6dcdd begin -/
  classical
  intro n B c hc hB hBc
  set R : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B with hRdef
  have hRR : R * R = B := by
    rw [hRdef]
    exact Matrix.PosSemidef.sqrt_mul_self hB
  have hRnn : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ R := by
    rw [hRdef]
    exact CFC.sqrt_nonneg B
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hRnn
  have hRherm : Matrix.conjTranspose R = R := hRpsd.isHermitian
  have hRt : Matrix.transpose R = R := by
    ext i j
    have h := congrFun (congrFun hRherm j) i
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h ⊢
    rw [← h]
    simp
  have hquad : ∀ v : Fin n → ℝ, (R.mulVec v) ⬝ᵥ (R.mulVec v) = v ⬝ᵥ (B.mulVec v) := by
    intro v
    have hmv : ∀ (N : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n),
        (N.mulVec y) i = ∑ j, N i j * y j := fun N y i => rfl
    have htr : ∀ (N : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n),
        (Matrix.transpose N) i j = N j i := fun N i j => rfl
    have hadj : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ),
        (M.mulVec a) ⬝ᵥ b = a ⬝ᵥ ((Matrix.transpose M).mulVec b) := by
      intro M a b
      have hL : (M.mulVec a) ⬝ᵥ b = ∑ i, ∑ j, (M i j * a j) * b i := by
        simp only [dotProduct]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hmv M a i, Finset.sum_mul]
      have hR : a ⬝ᵥ ((Matrix.transpose M).mulVec b) = ∑ j, a j * ∑ i, M i j * b i := by
        simp only [dotProduct]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hmv (Matrix.transpose M) b j]
        congr 1
      rw [hL, hR, Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring))
    have hBR : B = Matrix.transpose R * R := by
      rw [← hRR, hRt]
    rw [hBR, ← Matrix.mulVec_mulVec]
    exact hadj R v (R.mulVec v)
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖(Matrix.toEuclideanLin R) x‖ ≤ Real.sqrt c * ‖x‖ := by
    intro x
    have hnsq : ‖(Matrix.toEuclideanLin R) x‖ ^ 2
        = (R.mulVec x.ofLp) ⬝ᵥ (R.mulVec x.ofLp) := by
      have h1 : ((Matrix.toEuclideanLin R) x).ofLp = R.mulVec x.ofLp :=
        Matrix.ofLp_toEuclideanLin_apply R x
      rw [EuclideanSpace.norm_sq_eq, h1, dotProduct]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [Real.norm_eq_abs, sq_abs, pow_two])
    have hQ : x.ofLp ⬝ᵥ (B.mulVec x.ofLp) ≤ c * (x.ofLp ⬝ᵥ x.ofLp) := by
      have h := hBc.dotProduct_mulVec_nonneg x.ofLp
      have hexp : (c • (1 : Matrix (Fin n) (Fin n) ℝ) - B).mulVec x.ofLp
          = c • x.ofLp - B.mulVec x.ofLp := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [hexp] at h
      have hstar : (star x.ofLp : Fin n → ℝ) = x.ofLp := by
        funext i
        simp
      rw [hstar] at h
      have hsplit : x.ofLp ⬝ᵥ (c • x.ofLp - B.mulVec x.ofLp)
          = c * (x.ofLp ⬝ᵥ x.ofLp) - x.ofLp ⬝ᵥ (B.mulVec x.ofLp) := by
        simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hsplit] at h
      linarith
    have hle : ‖(Matrix.toEuclideanLin R) x‖ ^ 2 ≤ c * ‖x‖ ^ 2 := by
      rw [hnsq, hquad x.ofLp]
      have hvv : x.ofLp ⬝ᵥ x.ofLp = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, dotProduct]
        exact Finset.sum_congr rfl (fun i _ => by
          rw [Real.norm_eq_abs, sq_abs, pow_two])
      rw [hvv] at hQ
      exact hQ
    calc ‖(Matrix.toEuclideanLin R) x‖
        = Real.sqrt (‖(Matrix.toEuclideanLin R) x‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ Real.sqrt (c * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt c * ‖x‖ := by
          rw [Real.sqrt_mul hc, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
  have hRnorm : ‖R‖ ≤ Real.sqrt c := by
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg c) ?_
    intro x
    have hx : ((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) R) x
        = (Matrix.toEuclideanLin R) x := by
      simp
    rw [hx]
    exact hpoint x
  calc ‖B‖ = ‖R * R‖ := by rw [hRR]
    _ ≤ ‖R‖ * ‖R‖ := Matrix.l2_opNorm_mul R R
    _ ≤ Real.sqrt c * Real.sqrt c :=
        mul_le_mul hRnorm hRnorm (norm_nonneg R) (Real.sqrt_nonneg c)
    _ = c := by
        rw [← pow_two]
        exact Real.sq_sqrt hc
  /- @proof-region region.target-node.session.ed9280725fa6dcdd end -/

end

end Statlib.Imported

