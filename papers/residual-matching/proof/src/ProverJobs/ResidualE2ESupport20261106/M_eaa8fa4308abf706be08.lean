import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.HighDim.Vocabulary.RandomMatrix
import Statlib.StatFoundation.Convergence.AnalysisTools.IntegralConvergence
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_39f70cd7ffce1d817e97
import ProverJobs.ResidualE2ESupport20261106.M_26abeeb2e47af2c3d89e

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
theorem statopia_math_node_1405331481_81976b87 : ∀ (m n r D : ℕ) (p mu0 Cth : ℝ) (b : Fin D → Matrix (Fin m) (Fin n) ℝ)
    (hD : 0 < D) (hm : 3 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hr : 12 * r ≤ n)
    (hp : 0 < p) (hp1 : p ≤ 1) (hmu0 : 0 < mu0 * (r : ℝ)) (hCth : 12 ≤ Cth)
    (hnp : (n : ℝ) * p ≥ Cth ^ 2 * mu0 * (r : ℝ) * Real.log (m : ℝ))
    (hident : ∀ (i : Fin m) (j : Fin n),
      Real.sqrt (∑ q : Fin D, (tangentCoords b i j q) ^ 2) ^ 2
        ≤ 4 * (mu0 * (r : ℝ)) / (n : ℝ))
    (hframe : (∑ i : Fin m, ∑ j : Fin n,
        Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j) :
          Matrix (Fin D) (Fin D) ℝ) = 1)
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Om : Fin m → Fin n → Omega → ℝ)
    (hmeas : ∀ (i : Fin m) (j : Fin n), Measurable (Om i j))
    (hindep : iIndepFun (fun (ij : Fin m × Fin n) => Om ij.1 ij.2) P)
    (h01 : ∀ (i : Fin m) (j : Fin n), ∀ᵐ ω ∂P, Om i j ω = 0 ∨ Om i j ω = 1)
    (hprob : ∀ (i : Fin m) (j : Fin n), P {ω | Om i j ω = 1} = ENNReal.ofReal p)
    (hint : ∀ (i : Fin m) (j : Fin n), Integrable (Om i j) P)
    (hmean : ∀ (i : Fin m) (j : Fin n), ∫ ω, Om i j ω ∂P = p),
    let M : Fin m → Fin n → Omega → Matrix (Fin D) (Fin D) ℝ :=
      fun i j ω => (p⁻¹ * Om i j ω - 1) •
        Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)
    let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
    let X : Fin (m * n) → Omega → Matrix (Fin D) (Fin D) ℝ :=
      fun k ω => M (e.symm k).1 (e.symm k).2 ω
    let sigma2 : ℝ := 4 * (mu0 * (r : ℝ)) / ((n : ℝ) * p)
    (∀ k : Fin (m * n), Measurable (X k)) ∧
    (∀ k : Fin (m * n), ∀ᵐ ω ∂P, (X k ω).IsHermitian) ∧
    iIndepFun X P ∧
    (∀ k : Fin (m * n), Statlib.HighDim.Vocabulary.HasZeroMean (X k) P) ∧
    (∀ k : Fin (m * n), Statlib.HighDim.Vocabulary.HasBoundedSpectralNorm (X k) sigma2 P) ∧
    ‖∑ k : Fin (m * n), ∫ ω, X k ω * X k ω ∂P‖ ≤ sigma2 := by
  /- @proof-region region.target-node.session.332ef22b03b09dfa begin -/
  intro m n r D p mu0 Cth b hD hm hn hnm hr hp hp1 hmu0 hCth hnp hident hframe Omega instOmega P instP Om hmeas hindep h01 hprob hint hmean
  let M : Fin m → Fin n → Omega → Matrix (Fin D) (Fin D) ℝ :=
    fun i j ω => (p⁻¹ * Om i j ω - 1) • Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  let X : Fin (m * n) → Omega → Matrix (Fin D) (Fin D) ℝ := fun k ω => M (e.symm k).1 (e.symm k).2 ω
  let sigma2 : ℝ := 4 * (mu0 * (r : ℝ)) / ((n : ℝ) * p)
  have hbridge : ∀ A : Matrix (Fin D) (Fin D) ℝ, ‖A‖ = specNorm A := by
    intro A
    unfold specNorm
    exact (Statlib.StatFoundation.Convergence.matrix_toEuclideanCLM_norm_eq_l2_opNorm_real A).symm
  show (∀ k : Fin (m * n), Measurable (X k)) ∧
      (∀ k : Fin (m * n), ∀ᵐ ω ∂P, (X k ω).IsHermitian) ∧
      iIndepFun X P ∧
      (∀ k : Fin (m * n), Statlib.HighDim.Vocabulary.HasZeroMean (X k) P) ∧
      (∀ k : Fin (m * n), Statlib.HighDim.Vocabulary.HasBoundedSpectralNorm (X k) sigma2 P) ∧
      ‖∑ k : Fin (m * n), ∫ ω, X k ω * X k ω ∂P‖ ≤ sigma2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    change Measurable (fun ω : Omega => (fun a bb : Fin D => (p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1) * (tangentCoords b (e.symm k).1 (e.symm k).2 a * tangentCoords b (e.symm k).1 (e.symm k).2 bb)))
    have h1 : Measurable (fun ω : Omega => p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1) := by fun_prop
    refine measurable_pi_iff.mpr (fun a => measurable_pi_iff.mpr (fun bb => ?_))
    exact h1.mul_const _
  · intro k
    filter_upwards with ω
    change ((p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1) • (Matrix.vecMulVec (tangentCoords b (e.symm k).1 (e.symm k).2) (tangentCoords b (e.symm k).1 (e.symm k).2) : Matrix (Fin D) (Fin D) ℝ)).IsHermitian
    unfold Matrix.IsHermitian
    ext a bb
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec, Matrix.smul_apply, mul_comm]
  · have hind : iIndepFun (fun k : Fin (m * n) => Om (e.symm k).1 (e.symm k).2) P :=
      hindep.precomp e.symm.injective
    refine hind.comp (g := fun k x => (p⁻¹ * x - 1) • (Matrix.vecMulVec (tangentCoords b (e.symm k).1 (e.symm k).2) (tangentCoords b (e.symm k).1 (e.symm k).2) : Matrix (Fin D) (Fin D) ℝ)) ?_
    intro k
    change Measurable (fun x : ℝ => (fun a bb : Fin D => (p⁻¹ * x - 1) * (tangentCoords b (e.symm k).1 (e.symm k).2 a * tangentCoords b (e.symm k).1 (e.symm k).2 bb)))
    refine measurable_pi_iff.mpr (fun a => measurable_pi_iff.mpr (fun bb => ?_))
    exact (((measurable_id : Measurable (fun x : ℝ => x)).const_mul p⁻¹).sub_const 1).mul_const _
  · intro k
    refine ⟨fun a bb => ?_, fun a bb => ?_⟩
    · have hXt : ∀ ω : Omega, X k ω a bb = (p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1) * (tangentCoords b (e.symm k).1 (e.symm k).2 a * tangentCoords b (e.symm k).1 (e.symm k).2 bb) := fun ω => rfl
      simp only [hXt]
      exact (((hint (e.symm k).1 (e.symm k).2).const_mul p⁻¹).sub (integrable_const (1 : ℝ))).mul_const _
    · have hXt : ∀ ω : Omega, X k ω a bb = (p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1) * (tangentCoords b (e.symm k).1 (e.symm k).2 a * tangentCoords b (e.symm k).1 (e.symm k).2 bb) := fun ω => rfl
      simp only [hXt]
      have hInt2 : ∫ ω, (p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1) ∂P = 0 := by
        have h1 : ∫ ω, p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω ∂P = p⁻¹ * p := by
          rw [integral_const_mul, hmean]
        have h2 : ∫ ω, (1 : ℝ) ∂P = 1 := by simp
        rw [integral_sub ((hint (e.symm k).1 (e.symm k).2).const_mul p⁻¹) (integrable_const (1 : ℝ)), h1, h2]
        rw [inv_mul_cancel₀ (ne_of_gt hp), sub_self]
      calc ∫ ω, (p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1) * (tangentCoords b (e.symm k).1 (e.symm k).2 a * tangentCoords b (e.symm k).1 (e.symm k).2 bb) ∂P
          = (∫ ω, (p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1) ∂P) * (tangentCoords b (e.symm k).1 (e.symm k).2 a * tangentCoords b (e.symm k).1 (e.symm k).2 bb) := by rw [integral_mul_const]
        _ = 0 := by rw [hInt2, zero_mul]
  · intro k
    unfold Statlib.HighDim.Vocabulary.HasBoundedSpectralNorm
    filter_upwards [h01 (e.symm k).1 (e.symm k).2] with ω hω
    have hspec : ‖Matrix.vecMulVec (tangentCoords b (e.symm k).1 (e.symm k).2) (tangentCoords b (e.symm k).1 (e.symm k).2)‖ ≤ ∑ q : Fin D, (tangentCoords b (e.symm k).1 (e.symm k).2 q) ^ 2 := by
      rw [hbridge]
      exact statopia_math_node_1725776225_3ebc1f62 (tangentCoords b (e.symm k).1 (e.symm k).2)
    have hS : ∑ q : Fin D, (tangentCoords b (e.symm k).1 (e.symm k).2 q) ^ 2 ≤ 4 * (mu0 * (r : ℝ)) / (n : ℝ) := by
      rw [← Real.sq_sqrt (Finset.sum_nonneg (fun q _ => sq_nonneg (tangentCoords b (e.symm k).1 (e.symm k).2 q)))]
      exact hident (e.symm k).1 (e.symm k).2
    have hw : |p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1| ≤ p⁻¹ := by
      have hinv : (1 : ℝ) ≤ p⁻¹ := by
        nlinarith [hp, hp1, inv_pos.mpr hp, mul_inv_cancel₀ (ne_of_gt hp)]
      rcases hω with h | h
      · rw [h]
        simpa using hinv
      · rw [h, mul_one, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p⁻¹ - 1)]
        linarith
    have hX : ‖X k ω‖ = |p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1| * ‖Matrix.vecMulVec (tangentCoords b (e.symm k).1 (e.symm k).2) (tangentCoords b (e.symm k).1 (e.symm k).2)‖ := by
      change ‖(p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1) • (Matrix.vecMulVec (tangentCoords b (e.symm k).1 (e.symm k).2) (tangentCoords b (e.symm k).1 (e.symm k).2) : Matrix (Fin D) (Fin D) ℝ)‖ = |p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1| * ‖(Matrix.vecMulVec (tangentCoords b (e.symm k).1 (e.symm k).2) (tangentCoords b (e.symm k).1 (e.symm k).2) : Matrix (Fin D) (Fin D) ℝ)‖
      rw [norm_smul, Real.norm_eq_abs]
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hpne : p ≠ 0 := ne_of_gt hp
    have hcalc : |p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1| * ‖Matrix.vecMulVec (tangentCoords b (e.symm k).1 (e.symm k).2) (tangentCoords b (e.symm k).1 (e.symm k).2)‖ ≤ p⁻¹ * (4 * (mu0 * (r : ℝ)) / (n : ℝ)) :=
      mul_le_mul hw (le_trans hspec hS) (by positivity) (le_of_lt (inv_pos.mpr hp))
    have hsig : sigma2 = 4 * (mu0 * (r : ℝ)) / ((n : ℝ) * p) := rfl
    calc ‖X k ω‖ = |p⁻¹ * Om (e.symm k).1 (e.symm k).2 ω - 1| * ‖Matrix.vecMulVec (tangentCoords b (e.symm k).1 (e.symm k).2) (tangentCoords b (e.symm k).1 (e.symm k).2)‖ := hX
      _ ≤ p⁻¹ * (4 * (mu0 * (r : ℝ)) / (n : ℝ)) := hcalc
      _ = sigma2 := by
          rw [hsig]
          field_simp
  · rw [hbridge]
    exact statopia_math_node_4008937357_c32b14f6 m n r D mu0 p b hn hp hp1 hmu0 hident hframe P Om h01 hprob hint
  /- @proof-region region.target-node.session.332ef22b03b09dfa end -/

end

end Statlib.Imported

