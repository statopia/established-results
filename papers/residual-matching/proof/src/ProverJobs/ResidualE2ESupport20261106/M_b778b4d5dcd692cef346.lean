import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.StatFoundation.RandomVariable.Gaussian.LipschitzConcentration
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_e59200d45cd1fc0d9d5e
import ProverJobs.ResidualE2ESupport20261106.M_db134e16948d3365d08c
import ProverJobs.ResidualE2ESupport20261106.M_33a8aa225c9a44b03a84
import Statlib.StatFoundation.RandomVariable.Gaussian.LipschitzConcentration

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000

namespace ResidualSparseRepair20261106.GaussianTail

noncomputable def canonicalMeasure (m n : ℕ) : Measure ((Fin m × Fin n) → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

noncomputable def matrixNorm {m n : ℕ} (g : (Fin m × Fin n) → ℝ) : ℝ :=
  Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => g (i,j))

lemma canonicalMeasure_probability (m n : ℕ) : IsProbabilityMeasure (canonicalMeasure m n) := by
  unfold canonicalMeasure
  infer_instance

lemma matrixNorm_measurable (m n : ℕ) : Measurable (@matrixNorm m n) := by
  let X : ((Fin m × Fin n) → ℝ) → EuclideanSpace ℝ (Fin (m*n)) :=
    fun g => WithLp.toLp 2 (fun k => g (finProdFinEquiv.symm k))
  have hX : Measurable X := by fun_prop
  have heq : (fun g => Statlib.HighDim.MatrixAnalysis.opNorm (entryMatrix (X g))) =
      @matrixNorm m n := by
    funext g
    congr 1
    ext i j
    simp [entryMatrix, X, matrixNorm]
  rw [← heq]
  exact (opNorm_entryMatrix_lipschitz m n).continuous.measurable.comp hX

/-- A genuine Gaussian concentration bound centered at the universal sharp upper edge. -/
theorem canonical_upper_tail (m n : ℕ) (hnm : n ≤ m) (t : ℝ) (ht : 0 < t) :
    canonicalMeasure m n {g | t < max (matrixNorm g - 2 * Real.sqrt (m : ℝ)) 0} ≤
      ENNReal.ofReal (2 * Real.exp (-t^2 / 2)) := by
  let μ := canonicalMeasure m n
  haveI : IsProbabilityMeasure μ := canonicalMeasure_probability m n
  let X : ((Fin m × Fin n) → ℝ) → EuclideanSpace ℝ (Fin (m*n)) :=
    fun g => WithLp.toLp 2 (fun k => g (finProdFinEquiv.symm k))
  have hX : Measurable X := by fun_prop
  have hXiid : iIndepFun (fun k g => X g k) μ := by
    have hi : iIndepFun (fun k : Fin m × Fin n => fun g : (Fin m × Fin n) → ℝ => g k) μ := by
      exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    exact iIndepFun.precomp finProdFinEquiv.symm.injective hi
  have hXstd : ∀ k, Measure.map (fun g => X g k) μ = gaussianReal 0 1 := by
    intro k
    exact (measurePreserving_eval (fun _ : Fin m × Fin n => gaussianReal 0 1)
      (finProdFinEquiv.symm k)).map_eq
  let f : EuclideanSpace ℝ (Fin (m*n)) → ℝ :=
    fun x => Statlib.HighDim.MatrixAnalysis.opNorm (entryMatrix x)
  have hfX : ∀ g, f (X g) = matrixNorm g := by
    intro g
    dsimp [f, matrixNorm]
    congr 1
    ext i j
    simp [entryMatrix, X]
  have hint : Integrable (fun g => f (X g)) μ := by
    simpa only [hfX] using Statlib.Imported.statopia_math_node_288165421_707c7f6f m n
  have hc := Statlib.StatFoundation.RandomVariable.Gaussian.gaussian_lipschitz_concentration
    μ X hX hXiid hXstd f 1 (by norm_num) (opNorm_entryMatrix_lipschitz m n) hint ht.le
  simp only [hfX, NNReal.coe_one, one_pow, mul_one] at hc
  have hmean : (∫ g, matrixNorm g ∂μ) ≤ 2 * Real.sqrt (m : ℝ) := by
    have h := Statlib.Imported.statopia_math_node_3041891103_ca9d76ef m n
    have hs : Real.sqrt (n : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hnm)
    change (∫ g, matrixNorm g ∂μ) ≤ _ at h
    linarith
  refine (measure_mono ?_).trans hc
  intro g hg
  simp only [Set.mem_setOf_eq] at hg ⊢
  have hpos : t < matrixNorm g - 2 * Real.sqrt (m : ℝ) := by
    exact (lt_max_iff.mp hg).resolve_right (by linarith)
  exact le_trans (by linarith) (le_abs_self _)

/-- Both positive-edge moments are absolute constants; their integrability is proved. -/
theorem canonical_edge_moments (m n : ℕ) (hnm : n ≤ m) :
    let Y := fun g : (Fin m × Fin n) → ℝ => max (matrixNorm g - 2 * Real.sqrt (m : ℝ)) 0;
    Integrable Y (canonicalMeasure m n) ∧
    Integrable (fun g => Y g ^ 2) (canonicalMeasure m n) ∧
    (∫ g, Y g ∂canonicalMeasure m n) ≤ 5 ∧
    (∫ g, Y g ^ 2 ∂canonicalMeasure m n) ≤ 4 := by
  intro Y
  haveI := canonicalMeasure_probability m n
  have hm : Measurable Y := ((matrixNorm_measurable m n).sub measurable_const).max measurable_const
  have hn : ∀ g, 0 ≤ Y g := fun g => le_max_right _ _
  obtain ⟨hi2, hb2⟩ := second_moment_of_gaussian_tail (canonicalMeasure m n) Y hm hn
    (fun t ht => canonical_upper_tail m n hnm t ht)
  obtain ⟨hi1, hb1⟩ := first_moment_of_second_moment (canonicalMeasure m n) Y hm hn hi2 hb2
  exact ⟨hi1, hi2, hb1, hb2⟩

#print axioms canonical_upper_tail
#print axioms canonical_edge_moments
end ResidualSparseRepair20261106.GaussianTail

