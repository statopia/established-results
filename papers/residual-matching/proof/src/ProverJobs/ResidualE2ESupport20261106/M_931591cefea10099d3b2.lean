import Lean
import ProverJobs.ResidualE2ESupport20261106.M_b32d93680634886bcf6b
import ProverJobs.ResidualE2ESupport20261106.M_7607257e8c8d3943332a
import ProverJobs.ResidualE2ESupport20261106.M_f36ae02d45ed65920a57

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianCalculus

noncomputable def flatGaussianMeasure (m n : ℕ) : Measure (Fin (m * n) → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

noncomputable def realCoordinateMatrix {m n : ℕ} (ω : Fin (m * n) → ℝ) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => ω (finProdFinEquiv (i, j))
noncomputable def coordinateMatrix {m n : ℕ} (ω : Fin (m * n) → ℝ) :
    Matrix (Fin m) (Fin n) ℂ := (realCoordinateMatrix ω).map Complex.ofReal
noncomputable def coordinateDirection {m n : ℕ} (q : Fin (m * n)) :
    Matrix (Fin m) (Fin n) ℂ :=
  fun i j => if finProdFinEquiv (i, j) = q then 1 else 0

@[simp] theorem coordinateMatrix_apply {m n : ℕ} (ω : Fin (m * n) → ℝ)
    (i : Fin m) (j : Fin n) : coordinateMatrix ω i j = (ω (finProdFinEquiv (i, j)) : ℂ) := rfl

theorem coordinateDirection_eq_single {m n : ℕ} (q : Fin (m * n)) :
    coordinateDirection q = Matrix.single (finProdFinEquiv.symm q).1
      (finProdFinEquiv.symm q).2 (1 : ℂ) := by
  ext i j
  have hh : finProdFinEquiv (i, j) = q ↔
      (finProdFinEquiv.symm q).1 = i ∧ (finProdFinEquiv.symm q).2 = j := by
    constructor
    · intro h
      have hp : (i, j) = finProdFinEquiv.symm q := by
        simpa only [Equiv.symm_apply_apply] using congrArg finProdFinEquiv.symm h
      exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩
    · intro h
      have hp : (i, j) = finProdFinEquiv.symm q := Prod.ext h.1.symm h.2.symm
      rw [hp]
      exact finProdFinEquiv.apply_symm_apply q
  simp only [coordinateDirection, Matrix.single, Matrix.of_apply, hh]

theorem coordinateMatrix_update {m n : ℕ} (ω : Fin (m * n) → ℝ)
    (q : Fin (m * n)) (t : ℝ) :
    coordinateMatrix (Function.update ω q t) =
      coordinateMatrix ω + (t - ω q) • coordinateDirection q := by
  ext i j
  by_cases h : finProdFinEquiv (i, j) = q
  · simp [coordinateMatrix_apply, Function.update_apply, h, coordinateDirection,
      Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, Complex.ofReal_sub]
  · simp [coordinateMatrix_apply, Function.update_apply, h, coordinateDirection,
      Matrix.add_apply, Matrix.smul_apply]

theorem coordinateMatrix_continuous (m n : ℕ) :
    Continuous (coordinateMatrix (m := m) (n := n)) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun ω : Fin (m * n) → ℝ => (ω (finProdFinEquiv (i, j)) : ℂ))
  fun_prop

theorem gramPencil_continuous (m n : ℕ) (z : ℂ) :
    Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => gramPencil A z) := by
  unfold gramPencil
  fun_prop

theorem gramResolvent_continuous (m n : ℕ) (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => (gramPencil A z)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro A
  have hdet : (gramPencil A z).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).1 (gram_pencil_isUnit A z hz))
  have hscalar : ContinuousAt Ring.inverse (gramPencil A z).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hP : ContinuousAt (fun Y : Matrix (Fin m) (Fin n) ℂ => gramPencil Y z) A :=
    (gramPencil_continuous m n z).continuousAt
  have hInv : ContinuousAt (fun Y : Matrix (Fin n) (Fin n) ℂ => Y⁻¹) (gramPencil A z) :=
    continuousAt_matrix_inv (gramPencil A z) hscalar
  exact ContinuousAt.comp (f := fun Y : Matrix (Fin m) (Fin n) ℂ => gramPencil Y z)
    (x := A) hInv hP

theorem weightedGram_continuous (m n : ℕ) (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => A * (gramPencil A z)⁻¹) := by
  have hid : Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => A) := continuous_id
  exact hid.matrix_mul (gramResolvent_continuous m n z hz)

theorem weightedGramEntry_continuous (m n : ℕ) (z : ℂ) (hz : 0 < z.im)
    (i : Fin m) (j : Fin n) :
    Continuous (fun ω : Fin (m * n) → ℝ =>
      (coordinateMatrix ω * (gramPencil (coordinateMatrix ω) z)⁻¹) i j) := by
  exact ((matrixEntryCLM m n i j).continuous.comp
    (weightedGram_continuous m n z hz)).comp (coordinateMatrix_continuous m n)

theorem realCoordinateMatrix_map_gaussian (m n : ℕ) :
    Measure.map (realCoordinateMatrix (m := m) (n := n)) (flatGaussianMeasure m n) =
      _root_.PaperProofTasks.ResidualE2ESupport20261106.stdNormalMatrixMeasure m n := by
  haveI : IsProbabilityMeasure (flatGaussianMeasure m n) := by
    unfold flatGaussianMeasure
    infer_instance
  have hmeas : ∀ i j, Measurable (fun ω : Fin (m * n) → ℝ => realCoordinateMatrix ω i j) :=
    fun i j => measurable_pi_apply _
  have hflat : iIndepFun (fun q : Fin (m * n) => fun ω : Fin (m * n) → ℝ => ω q)
      (flatGaussianMeasure m n) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hindep : iIndepFun (fun q : Fin m × Fin n =>
      fun ω : Fin (m * n) → ℝ => realCoordinateMatrix ω q.1 q.2)
      (flatGaussianMeasure m n) := hflat.precomp finProdFinEquiv.injective
  have hmarg : ∀ i j, Measure.map (fun ω : Fin (m * n) → ℝ => realCoordinateMatrix ω i j)
      (flatGaussianMeasure m n) = gaussianReal 0 1 := by
    intro i j
    exact (measurePreserving_eval (fun _ : Fin (m * n) => gaussianReal 0 1)
      (finProdFinEquiv (i, j))).map_eq
  exact ResidualSparseRepair.gaussian_matrix_map (flatGaussianMeasure m n)
    realCoordinateMatrix hmeas hindep hmarg

#print axioms realCoordinateMatrix_map_gaussian
#print axioms coordinateMatrix_update
#print axioms weightedGramEntry_continuous
end ResidualSparseRepair20261106.GaussianCalculus

