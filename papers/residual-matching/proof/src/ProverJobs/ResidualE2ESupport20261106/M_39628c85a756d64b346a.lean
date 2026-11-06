import Lean
import ProverJobs.ResidualE2ESupport20261106.M_caa107eb86ed05199c5d
import ProverJobs.ResidualE2ESupport20261106.M_74f9bd0e38dfa969823e

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianCalculus
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianResolventBounds

noncomputable def flatNormalizedTrace {m n : ℕ}
    (ω : Fin (m * n) → ℝ) (z : ℂ) : ℂ := normalizedGramTrace (coordinateMatrix ω) z

noncomputable def flatNormalizedSquareTrace {m n : ℕ}
    (ω : Fin (m * n) → ℝ) (z : ℂ) : ℂ := normalizedGramSquareTrace (coordinateMatrix ω) z

theorem flat_normalized_trace_memLp (m n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) :
    MemLp (fun ω => flatNormalizedTrace (m := m) (n := n) ω z)
      2 (flatGaussianMeasure m n) := by
  haveI : IsProbabilityMeasure (flatGaussianMeasure m n) := by
    unfold flatGaussianMeasure; infer_instance
  apply MemLp.of_bound
    (((normalized_gram_trace_continuous m n z hz).comp
      (coordinateMatrix_continuous m n)).aestronglyMeasurable) z.im⁻¹
  exact ae_of_all _ (fun ω => normalized_gram_trace_bound hn (coordinateMatrix ω) z hz)

theorem flat_normalized_square_trace_integrable (m n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun ω => flatNormalizedSquareTrace (m := m) (n := n) ω z)
      (flatGaussianMeasure m n) := by
  haveI : IsProbabilityMeasure (flatGaussianMeasure m n) := by
    unfold flatGaussianMeasure; infer_instance
  exact normalized_gram_square_trace_integrable (flatGaussianMeasure m n) hn
    coordinateMatrix (coordinateMatrix_continuous m n) z hz

theorem coordinate_matrix_real {m n : ℕ} (ω : Fin (m * n) → ℝ) :
    (coordinateMatrix ω).conjTranspose = (coordinateMatrix ω).transpose := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, coordinateMatrix_apply]

set_option maxHeartbeats 2000000 in
theorem gaussian_exact_loop_equation (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) :
    1 + (z + (n : ℂ) / m - 1 + (m : ℂ)⁻¹) *
        (∫ ω, flatNormalizedTrace (m := m) (n := n) ω z ∂(flatGaussianMeasure m n)) +
      ((n : ℂ) / m) * z *
        (∫ ω, flatNormalizedTrace (m := m) (n := n) ω z ^ 2 ∂(flatGaussianMeasure m n)) +
      (z / m) *
        (∫ ω, flatNormalizedSquareTrace (m := m) (n := n) ω z ∂(flatGaussianMeasure m n)) = 0 := by
  classical
  let μ := flatGaussianMeasure m n
  haveI : IsProbabilityMeasure μ := by dsimp [μ, flatGaussianMeasure]; infer_instance
  let f := fun ω => flatNormalizedTrace (m := m) (n := n) ω z
  let g := fun ω => flatNormalizedSquareTrace (m := m) (n := n) ω z
  let P := fun (i : Fin m) (j : Fin n) (ω : Fin (m * n) → ℝ) =>
    (ω (finProdFinEquiv (i, j)) : ℂ) * weightedCoordinateEntry ω z i j
  let D := fun (i : Fin m) (j : Fin n) (ω : Fin (m * n) → ℝ) =>
    weightedCoordinateDerivative ω (finProdFinEquiv (i, j)) z i j
  have hP (i : Fin m) (j : Fin n) : Integrable (P i j) μ :=
    weightedCoordinateEntry_product_integrable m n hm z hz i j (finProdFinEquiv (i, j))
  have hD (i : Fin m) (j : Fin n) : Integrable (D i j) μ :=
    weightedCoordinateDerivative_integrable m n hm z hz i j (finProdFinEquiv (i, j))
  have hsum : (∫ ω, ∑ i : Fin m, ∑ j : Fin n, P i j ω ∂μ) =
      ∫ ω, ∑ i : Fin m, ∑ j : Fin n, D i j ω ∂μ := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hP i j)),
      integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hD i j))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finset_sum _ (fun j _ => hP i j),
      integral_finset_sum _ (fun j _ => hD i j)]
    apply Finset.sum_congr rfl
    intro j hj
    exact gaussian_weighted_coordinate_ibp m n hm hn z hz i j (finProdFinEquiv (i, j))
  let F := fun ω =>
    1 + (z + (n : ℂ) / m - 1 + (m : ℂ)⁻¹) * f ω +
      ((n : ℂ) / m) * z * f ω ^ 2 + (z / m) * g ω
  have hpoint (ω : Fin (m * n) → ℝ) :
      (∑ i : Fin m, ∑ j : Fin n, P i j ω) -
        (∑ i : Fin m, ∑ j : Fin n, D i j ω) = (m : ℂ) * n * F ω := by
    simpa only [P, D, weightedCoordinateEntry, weightedCoordinateDerivative,
      coordinateDirection_eq_single, Equiv.symm_apply_apply, coordinateMatrix_apply,
      F, f, g, flatNormalizedTrace, flatNormalizedSquareTrace] using
      normalized_pointwise_loop hm hn (coordinateMatrix ω) (coordinate_matrix_real ω) z hz
  have hzint : (m : ℂ) * n * (∫ ω, F ω ∂μ) = 0 := by
    rw [← integral_const_mul]
    calc
      _ = ∫ ω, (∑ i : Fin m, ∑ j : Fin n, P i j ω) -
          (∑ i : Fin m, ∑ j : Fin n, D i j ω) ∂μ :=
        integral_congr_ae (ae_of_all _ (fun ω => (hpoint ω).symm))
      _ = 0 := by
        rw [integral_sub
          (integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hP i j)))
          (integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hD i j))),
          hsum, sub_self]
  have hmn : (m : ℂ) * n ≠ 0 := mul_ne_zero
    (by exact_mod_cast (show m ≠ 0 by omega)) (by exact_mod_cast (show n ≠ 0 by omega))
  have hzero : (∫ ω, F ω ∂μ) = 0 := (mul_eq_zero.mp hzint).resolve_left hmn
  have hf2 : MemLp f 2 μ := flat_normalized_trace_memLp m n hn z hz
  have hf : Integrable f μ := hf2.integrable (by norm_num)
  have hff : Integrable (fun ω => f ω ^ 2) μ := by
    simpa only [pow_two] using hf2.integrable_mul hf2
  have hg : Integrable g μ := flat_normalized_square_trace_integrable m n hn z hz
  have h1 : Integrable (fun ω => (1 : ℂ) +
      (z + (n : ℂ) / m - 1 + (m : ℂ)⁻¹) * f ω) μ :=
    (integrable_const 1).add (hf.const_mul _)
  have h2 : Integrable (fun ω => 1 +
      (z + (n : ℂ) / m - 1 + (m : ℂ)⁻¹) * f ω +
      ((n : ℂ) / m) * z * f ω ^ 2) μ := h1.add (hff.const_mul _)
  change (∫ ω, 1 + (z + (n : ℂ) / m - 1 + (m : ℂ)⁻¹) * f ω +
    ((n : ℂ) / m) * z * f ω ^ 2 + (z / m) * g ω ∂μ) = 0 at hzero
  rw [integral_add h2 (hg.const_mul _), integral_add h1 (hff.const_mul _),
    integral_add (integrable_const 1) (hf.const_mul _)] at hzero
  simpa only [integral_const_mul, integral_const, probReal_univ, one_smul, f, g, μ] using hzero

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.gaussian_exact_loop_equation

