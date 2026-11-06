import Lean
import ProverJobs.ResidualE2ESupport20261106.M_931591cefea10099d3b2
import ProverJobs.ResidualE2ESupport20261106.M_4e373d3c8caafdc47c0b

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianCalculus
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianResolventBounds

noncomputable def weightedCoordinateEntry {m n : ℕ} (ω : Fin (m * n) → ℝ)
    (z : ℂ) (i : Fin m) (j : Fin n) : ℂ :=
  (coordinateMatrix ω * (gramPencil (coordinateMatrix ω) z)⁻¹) i j
noncomputable def weightedCoordinateDerivative {m n : ℕ} (ω : Fin (m * n) → ℝ)
    (q : Fin (m * n)) (z : ℂ) (i : Fin m) (j : Fin n) : ℂ :=
  weightedResolventDerivative (coordinateMatrix ω) (coordinateDirection q) z i j

theorem weightedCoordinateEntry_hasDerivAt {m n : ℕ}
    (ω : Fin (m * n) → ℝ) (q : Fin (m * n))
    (z : ℂ) (hz : 0 < z.im) (i : Fin m) (j : Fin n) (t : ℝ) :
    HasDerivAt (fun s => weightedCoordinateEntry (Function.update ω q s) z i j)
      (weightedCoordinateDerivative (Function.update ω q t) q z i j) t := by
  let E : Matrix (Fin m) (Fin n) ℂ := coordinateDirection q
  let A := coordinateMatrix ω - (ω q) • E
  have heq : ∀ s : ℝ, coordinateMatrix (Function.update ω q s) = A + s • E := by
    intro s
    rw [coordinateMatrix_update]
    dsimp [A, E]
    module
  have hh := weighted_gram_resolvent_entry_derivative A E z hz t i j
  convert hh using 1
  · funext s
    simp only [weightedCoordinateEntry, heq]
  · simp only [weightedCoordinateDerivative, weightedResolventDerivative, heq,
      Matrix.sub_apply]
    rfl

theorem weightedCoordinateEntry_deriv {m n : ℕ}
    (ω : Fin (m * n) → ℝ) (q : Fin (m * n))
    (z : ℂ) (hz : 0 < z.im) (i : Fin m) (j : Fin n) :
    deriv (fun s => weightedCoordinateEntry (Function.update ω q s) z i j) (ω q) =
      weightedCoordinateDerivative ω q z i j := by
  have h := (weightedCoordinateEntry_hasDerivAt ω q z hz i j (ω q)).deriv
  simpa only [Function.update_eq_self] using h

theorem weightedDerivative_continuous {m n : ℕ} (E : Matrix (Fin m) (Fin n) ℂ)
    (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => weightedResolventDerivative A E z) := by
  have hQ : Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => gramResolvent A z) :=
    gramResolvent_continuous m n z hz
  have hH : Continuous (fun A : Matrix (Fin m) (Fin n) ℂ =>
      ((m : ℝ)⁻¹) • (E.conjTranspose * A + A.conjTranspose * E)) := by fun_prop
  have hid : Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => A) := continuous_id
  exact (continuous_const.matrix_mul hQ).sub (hid.matrix_mul ((hQ.matrix_mul hH).matrix_mul hQ))

theorem weightedCoordinateDerivative_continuous {m n : ℕ} (q : Fin (m * n))
    (z : ℂ) (hz : 0 < z.im) (i : Fin m) (j : Fin n) :
    Continuous (fun ω : Fin (m * n) → ℝ => weightedCoordinateDerivative ω q z i j) := by
  exact ((matrixEntryCLM m n i j).continuous.comp
    (weightedDerivative_continuous (coordinateDirection q) z hz)).comp
      (coordinateMatrix_continuous m n)

theorem weightedCoordinateEntry_bound {m n : ℕ} (hm : 1 ≤ m)
    (ω : Fin (m * n) → ℝ) (z : ℂ) (hz : 0 < z.im) (i : Fin m) (j : Fin n) :
    ‖weightedCoordinateEntry ω z i j‖ ≤
      Real.sqrt ((m : ℝ) * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2)) :=
  norm_mul_gram_resolvent_entry_le hm (coordinateMatrix ω) z hz i j

theorem weightedCoordinateDerivative_bound {m n : ℕ} (hm : 1 ≤ m)
    (ω : Fin (m * n) → ℝ) (q : Fin (m * n)) (z : ℂ) (hz : 0 < z.im)
    (i : Fin m) (j : Fin n) :
    ‖weightedCoordinateDerivative ω q z i j‖ ≤
      ‖coordinateDirection q‖ * (3 * z.im⁻¹ + 2 * ‖z‖ * (z.im⁻¹) ^ 2) :=
  norm_weighted_resolvent_derivative_entry_le hm (coordinateMatrix ω) (coordinateDirection q) z hz i j

theorem weightedCoordinateEntry_product_integrable (m n : ℕ) (hm : 1 ≤ m)
    (z : ℂ) (hz : 0 < z.im) (i : Fin m) (j : Fin n) (q : Fin (m * n)) :
    Integrable (fun ω : Fin (m * n) → ℝ => (ω q : ℂ) * weightedCoordinateEntry ω z i j)
      (flatGaussianMeasure m n) := by
  haveI : IsProbabilityMeasure (flatGaussianMeasure m n) := by unfold flatGaussianMeasure; infer_instance
  let C : ℝ := Real.sqrt ((m : ℝ) * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2))
  have hf : Continuous (fun ω : Fin (m * n) → ℝ => weightedCoordinateEntry ω z i j) :=
    weightedGramEntry_continuous m n z hz i j
  have hreal : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hk : Integrable (fun ω : Fin (m * n) → ℝ => ω q) (flatGaussianMeasure m n) := by
    exact integrable_comp_eval (μ := fun _ : Fin (m * n) => gaussianReal 0 1)
      (i := q) (f := fun x : ℝ => x) hreal
  refine (hk.norm.mul_const C).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp (continuous_apply q)).mul hf).aestronglyMeasurable
  · filter_upwards with ω
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (weightedCoordinateEntry_bound hm ω z hz i j) (norm_nonneg _)

theorem weightedCoordinateDerivative_integrable (m n : ℕ) (hm : 1 ≤ m)
    (z : ℂ) (hz : 0 < z.im) (i : Fin m) (j : Fin n) (q : Fin (m * n)) :
    Integrable (fun ω : Fin (m * n) → ℝ => weightedCoordinateDerivative ω q z i j)
      (flatGaussianMeasure m n) := by
  haveI : IsProbabilityMeasure (flatGaussianMeasure m n) := by unfold flatGaussianMeasure; infer_instance
  apply Integrable.of_bound (weightedCoordinateDerivative_continuous q z hz i j).aestronglyMeasurable
    (‖coordinateDirection q‖ * (3 * z.im⁻¹ + 2 * ‖z‖ * (z.im⁻¹) ^ 2))
  exact ae_of_all _ (fun ω => weightedCoordinateDerivative_bound hm ω q z hz i j)

set_option maxHeartbeats 2000000 in
theorem gaussian_weighted_coordinate_ibp (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) (i : Fin m) (j : Fin n) (q : Fin (m * n)) :
    (∫ ω : Fin (m * n) → ℝ, (ω q : ℂ) * weightedCoordinateEntry ω z i j
      ∂(flatGaussianMeasure m n)) =
      ∫ ω : Fin (m * n) → ℝ, weightedCoordinateDerivative ω q z i j
        ∂(flatGaussianMeasure m n) := by
  let μ : Measure (Fin (m * n) → ℝ) := flatGaussianMeasure m n
  haveI : IsProbabilityMeasure μ := by dsimp [μ, flatGaussianMeasure]; infer_instance
  let f : (Fin (m * n) → ℝ) → ℂ := fun ω => weightedCoordinateEntry ω z i j
  let C : ℝ := Real.sqrt ((m : ℝ) * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2))
  have hf : Continuous f := weightedGramEntry_continuous m n z hz i j
  have hb : ∀ ω, ‖f ω‖ ≤ C := fun ω => weightedCoordinateEntry_bound hm ω z hz i j
  have hd : ∀ ω q, Differentiable ℝ (fun t => f (Function.update ω q t)) := by
    intro ω k
    intro t
    exact (weightedCoordinateEntry_hasDerivAt ω k z hz i j t).differentiableAt
  have hi : ∀ k, Integrable (fun ω => (ω k : ℂ) * f ω) μ :=
    fun k => weightedCoordinateEntry_product_integrable m n hm z hz i j k
  have hid : ∀ k, Integrable (fun ω => deriv (fun t => f (Function.update ω k t)) (ω k)) μ := by
    intro k
    have heq : (fun ω => deriv (fun t => f (Function.update ω k t)) (ω k)) =
        (fun ω => weightedCoordinateDerivative ω k z i j) := by
      funext ω; exact weightedCoordinateEntry_deriv ω k z hz i j
    rw [heq]
    exact weightedCoordinateDerivative_integrable m n hm z hz i j k
  have h := standard_product_stein_complex (m * n) (Nat.mul_pos (by omega) (by omega))
    f ⟨C, hb⟩ hd hi hid q
  simpa only [f, weightedCoordinateEntry_deriv (z := z) (hz := hz)] using h

#print axioms weightedCoordinateEntry_hasDerivAt
#print axioms weightedCoordinateDerivative_continuous
#print axioms weightedCoordinateEntry_product_integrable
#print axioms weightedCoordinateDerivative_integrable
#print axioms gaussian_weighted_coordinate_ibp
end ResidualSparseRepair20261106.GaussianCalculus

