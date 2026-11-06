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
theorem statopia_math_node_1725776225_3ebc1f62 : ∀ {D : ℕ} (g : Fin D → ℝ),
    specNorm (Matrix.vecMulVec g g) ≤ ∑ q : Fin D, (g q) ^ 2 := by
  /- @proof-region region.target-node.session.2b19648aeb61de12 begin -/
  intro D g
  classical
  set S : ℝ := ∑ q : Fin D, (g q) ^ 2 with hSdef
  have hS_nonneg : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun q _ => sq_nonneg (g q))
  have hnorm_sq_abs : ∀ r : ℝ, ‖r‖ ^ 2 = r ^ 2 := by
    intro r
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs r, Real.sq_sqrt (sq_nonneg r)]
  have hmulvec : ∀ (x : Fin D → ℝ) (a : Fin D),
      (Matrix.vecMulVec g g).mulVec x a = g a * ∑ q : Fin D, g q * x q := by
    intro x a
    have h1 : (Matrix.vecMulVec g g).mulVec x a = ∑ q : Fin D, (g a * g q) * x q := rfl
    rw [h1, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  have hspec : specNorm (Matrix.vecMulVec g g)
      = ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (Matrix.vecMulVec g g)‖ := rfl
  rw [hspec]
  refine ContinuousLinearMap.opNorm_le_bound _ hS_nonneg (fun v => ?_)
  have hcoe : (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (Matrix.vecMulVec g g) v
      = WithLp.toLp 2 (fun a : Fin D => g a * ∑ q : Fin D, g q * v.ofLp q) := by
    rw [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply]
    congr 1
    funext a
    exact hmulvec v.ofLp a
  have hnormTv : ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (Matrix.vecMulVec g g) v‖
      = |∑ q : Fin D, g q * v.ofLp q| * Real.sqrt S := by
    rw [hcoe, EuclideanSpace.norm_eq]
    have hpt : ∀ i : Fin D,
        ‖(WithLp.toLp 2 (fun a : Fin D => g a * ∑ q : Fin D, g q * v.ofLp q)).ofLp i‖ ^ 2
          = (g i) ^ 2 * (∑ q : Fin D, g q * v.ofLp q) ^ 2 := by
      intro i
      simp only [hnorm_sq_abs]
      ring
    have hsum : (∑ i : Fin D,
        ‖(WithLp.toLp 2 (fun a : Fin D => g a * ∑ q : Fin D, g q * v.ofLp q)).ofLp i‖ ^ 2)
        = (∑ q : Fin D, g q * v.ofLp q) ^ 2 * S := by
      have h1 : (∑ i : Fin D,
          ‖(WithLp.toLp 2 (fun a : Fin D => g a * ∑ q : Fin D, g q * v.ofLp q)).ofLp i‖ ^ 2)
          = ∑ i : Fin D, (g i) ^ 2 * (∑ q : Fin D, g q * v.ofLp q) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => hpt i)
      rw [h1, hSdef, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum, Real.sqrt_mul (sq_nonneg (∑ q : Fin D, g q * v.ofLp q)), Real.sqrt_sq_eq_abs]
  have hvsum : (∑ i : Fin D, (v.ofLp i) ^ 2) = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl (fun i _ => (hnorm_sq_abs (v.ofLp i)).symm)
  have hd_sq : (∑ q : Fin D, g q * v.ofLp q) ^ 2 ≤ S * ‖v‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin D)) g
      (fun q : Fin D => v.ofLp q)
    rw [hSdef, ← hvsum]
    exact hcs
  have hd_bound : |∑ q : Fin D, g q * v.ofLp q| ≤ Real.sqrt S * ‖v‖ := by
    have h1 : Real.sqrt ((∑ q : Fin D, g q * v.ofLp q) ^ 2) ≤ Real.sqrt (S * ‖v‖ ^ 2) :=
      Real.sqrt_le_sqrt hd_sq
    rw [Real.sqrt_sq_eq_abs] at h1
    have h2 : Real.sqrt (S * ‖v‖ ^ 2) = Real.sqrt S * ‖v‖ := by
      rw [Real.sqrt_mul hS_nonneg, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]
    rwa [h2] at h1
  calc ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (Matrix.vecMulVec g g) v‖
      = |∑ q : Fin D, g q * v.ofLp q| * Real.sqrt S := hnormTv
    _ ≤ (Real.sqrt S * ‖v‖) * Real.sqrt S :=
        mul_le_mul_of_nonneg_right hd_bound (Real.sqrt_nonneg S)
    _ = S * ‖v‖ := by
        rw [show Real.sqrt S * ‖v‖ * Real.sqrt S = Real.sqrt S ^ 2 * ‖v‖ by ring,
          Real.sq_sqrt hS_nonneg]
  /- @proof-region region.target-node.session.2b19648aeb61de12 end -/

end

end Statlib.Imported

