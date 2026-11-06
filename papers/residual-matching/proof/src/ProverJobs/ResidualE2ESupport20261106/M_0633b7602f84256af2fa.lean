import Lean
import ProverJobs.ResidualE2ESupport20261106.M_9f6712965bbb2a8f758c

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ResidualLoss20261106.Statlib.Imported
noncomputable section

/-- An actual finite product Gaussian matrix law, independent of any observations. -/
theorem exists_standard_gaussian_matrix_law (m n : ℕ) :
    ∃ μG : Measure (Matrix (Fin m) (Fin n) ℝ),
      IsProbabilityMeasure μG ∧ IsStdGaussianMatrixLaw μG := by
  let γ : Measure ((Fin m × Fin n) → ℝ) :=
    Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1)
  let cur : ((Fin m × Fin n) → ℝ) → Matrix (Fin m) (Fin n) ℝ :=
    fun x i j => x (i,j)
  have hcur : Measurable cur := measurable_pi_iff.mpr (fun i =>
    measurable_pi_iff.mpr (fun j => measurable_pi_apply (i,j)))
  let μG : Measure (Matrix (Fin m) (Fin n) ℝ) := Measure.map cur γ
  haveI : IsProbabilityMeasure μG := Measure.isProbabilityMeasure_map hcur.aemeasurable
  refine ⟨μG, inferInstance, ?_⟩
  have hc : ∀ i j, Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => A i j) :=
    fun i j => (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hcoord : ∀ i j, Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => A i j) μG
      = gaussianReal 0 1 := by
    intro i j
    change Measure.map _ (Measure.map cur γ) = _
    rw [Measure.map_map (hc i j) hcur]
    exact (measurePreserving_eval (fun _ : Fin m × Fin n => gaussianReal 0 1) (i,j)).map_eq
  refine ⟨hcoord, ?_⟩
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun ij : Fin m × Fin n =>
    (hc ij.1 ij.2).aemeasurable)).mpr
  have hflat : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      fun ij : Fin m × Fin n => A ij.1 ij.2) :=
    measurable_pi_iff.mpr (fun ij => hc ij.1 ij.2)
  change Measure.map _ (Measure.map cur γ) = _
  rw [Measure.map_map hflat hcur]
  have hid : (fun A : Matrix (Fin m) (Fin n) ℝ => fun ij : Fin m × Fin n => A ij.1 ij.2) ∘ cur = id := by
    funext x ij
    rfl
  rw [hid, Measure.map_id]
  simp only [hcoord]
  rfl

end
end ResidualLoss20261106.Statlib.Imported
#print axioms ResidualLoss20261106.Statlib.Imported.exists_standard_gaussian_matrix_law

