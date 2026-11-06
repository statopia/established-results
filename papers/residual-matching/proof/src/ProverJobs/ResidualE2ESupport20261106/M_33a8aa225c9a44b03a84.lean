import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_a9a8bba09ddbecaccb87

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
set_option autoImplicit false in
theorem statopia_math_node_288165421_707c7f6f : ∀ (m n : ℕ),
    MeasureTheory.Integrable
      (fun g : (Fin m × Fin n) → ℝ =>
        Statlib.HighDim.MatrixAnalysis.opNorm
          (fun (i : Fin m) (j : Fin n) => g (i, j)))
      (MeasureTheory.Measure.pi
        (fun _ : Fin m × Fin n => ProbabilityTheory.gaussianReal 0 1)) := by
  intro m n
  let curry : ((Fin m × Fin n) → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ :=
    { toFun := fun g i j => g (i, j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let L : ((Fin m × Fin n) → ℝ) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap).toLinearMap.comp
      curry
  have hi : MeasureTheory.Integrable (fun g : (Fin m × Fin n) → ℝ => g)
      (MeasureTheory.Measure.pi (fun _ : Fin m × Fin n =>
        ProbabilityTheory.gaussianReal 0 1)) :=
    MeasureTheory.integrable_pi_iff.mpr
      (statopia_math_node_1043732631_ea2639e2 (Fin m × Fin n)).1
  have h := (L.toContinuousLinearMap.integrable_comp hi).norm
  simpa only [L, curry, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_mk,
    Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2, Matrix.l2_opNorm_def] using h
#print axioms statopia_math_node_288165421_707c7f6f
end Statlib.Imported

