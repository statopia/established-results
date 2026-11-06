import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.HighDim.Concentration.MatrixBernstein
import Statlib.HighDim.Vocabulary.RandomMatrix
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_34d3da1fd86ef23ce9d8
import ProverJobs.ResidualE2ESupport20261106.M_eaa8fa4308abf706be08

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
theorem statopia_math_node_1315657654_81913db9 : ∀ (m n r D : ℕ) (p mu0 Cth : ℝ) (b : Fin D → Matrix (Fin m) (Fin n) ℝ)
    (hD : 0 < D) (hm : 3 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hr : 12 * r ≤ n)
    (hD1 : D ≤ r * (m + n))
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
    1 - ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4) ≤
          P {ω | specNorm (∑ i : Fin m, ∑ j : Fin n,
                (p⁻¹ * Om i j ω - 1) •
                  Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)) ≤
              Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))} := by
  /- @proof-region region.target-node.session.6d63cef9545a16a2 begin -/
  intro m n r D p mu0 Cth b hD hm hn hnm hr hD1 hp hp1 hmu0 hCth hnp hident hframe
  intro Omega _ P _ Om hmeas hindep h01 hprob hint hmean
  have hm_gt_one : (1 : ℝ) < (m : ℝ) := by
    have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hm_gt_one
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr_pos : (0 : ℝ) < (r : ℝ) := by
    by_contra h
    have hr0 : (r : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg r)
    have hzero : mu0 * (r : ℝ) = 0 := by rw [hr0, mul_zero]
    linarith
  have hmu0_pos : 0 < mu0 := by
    by_contra h
    have hle : mu0 ≤ 0 := le_of_not_gt h
    nlinarith
  have hnp_pos : 0 < (n : ℝ) * p := mul_pos hn_pos hp
  have hbase_pos : 0 < mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p) :=
    div_pos (mul_pos (mul_pos hmu0_pos hr_pos) hlogm) hnp_pos
  let θ : ℝ := Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
  let σ2 : ℝ := 4 * (mu0 * (r : ℝ)) / ((n : ℝ) * p)
  have hθ_sq : θ ^ 2 = Cth ^ 2 * (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) := by
    simp only [θ]
    rw [mul_pow, Real.sq_sqrt (le_of_lt hbase_pos)]
  have hθ_sq_le_one : θ ^ 2 ≤ 1 := by
    rw [hθ_sq]
    have hC2 : 0 ≤ Cth ^ 2 := sq_nonneg Cth
    rw [show Cth ^ 2 * (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
          = (Cth ^ 2 * (mu0 * (r : ℝ) * Real.log (m : ℝ))) / ((n : ℝ) * p) by ring]
    rw [div_le_one hnp_pos]
    nlinarith [hnp]
  have hθ_nonneg : 0 ≤ θ := by
    simp only [θ]
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hθ_le_one : θ ≤ 1 := by
    nlinarith [sq_nonneg (θ - 1), hθ_sq_le_one, hθ_nonneg]
  have hσ2_pos : 0 < σ2 := by
    simp only [σ2]
    positivity
  have hspec_eq : ∀ A : Matrix (Fin D) (Fin D) ℝ, specNorm A = ‖A‖ := by
    intro A
    rfl
  let M : Fin m → Fin n → Omega → Matrix (Fin D) (Fin D) ℝ :=
    fun i j ω => (p⁻¹ * Om i j ω - 1) • Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  let X : Fin (m * n) → Omega → Matrix (Fin D) (Fin D) ℝ :=
    fun k ω => M (e.symm k).1 (e.symm k).2 ω
  have hchild := statopia_math_node_1405331481_81976b87 m n r D p mu0 Cth b hD hm hn hnm hr hp hp1 hmu0 hCth hnp hident hframe P Om hmeas hindep h01 hprob hint hmean
  change (∀ k, Measurable (X k)) ∧
    (∀ k, ∀ᵐ ω ∂P, (X k ω).IsHermitian) ∧
    iIndepFun X P ∧
    (∀ k, Statlib.HighDim.Vocabulary.HasZeroMean (X k) P) ∧
    (∀ k, Statlib.HighDim.Vocabulary.HasBoundedSpectralNorm (X k) σ2 P) ∧
    ‖∑ k, ∫ ω, X k ω * X k ω ∂P‖ ≤ σ2 at hchild
  obtain ⟨hX_meas, hX_herm, hX_indep, hX_zero, hX_bound, hX_var⟩ := hchild
  have hbern : P {ω | ‖∑ k : Fin (m * n), X k ω‖ ≥ θ} ≤
      ENNReal.ofReal (2 * (D : ℝ) * Real.exp (-(θ ^ 2 / 2) / (σ2 + σ2 * θ / 3))) := by
    exact Statlib.HighDim.Concentration.matrix_bernstein (n := D) (m := m * n) hD P X hX_meas hX_herm hX_indep hX_zero σ2 hX_bound σ2 hX_var hθ_nonneg
  have h_arith := statopia_math_node_1231859466_c0d9b055 m n r D p mu0 Cth hD1 hm hn hnm hr hp hp1 hmu0 hCth hnp
  change ENNReal.ofReal (2 * (D : ℝ) * Real.exp (-(θ ^ 2 / 2) / (σ2 + σ2 * θ / 3))) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4) at h_arith
  have hbern_le : P {ω | ‖∑ k : Fin (m * n), X k ω‖ ≥ θ} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4) := le_trans hbern h_arith
  have hsum : ∀ ω, (∑ i : Fin m, ∑ j : Fin n, M i j ω) = ∑ k : Fin (m * n), X k ω := by
    intro ω
    calc
      ∑ i : Fin m, ∑ j : Fin n, M i j ω
          = ∑ ij : Fin m × Fin n, M ij.1 ij.2 ω := by
            exact (Fintype.sum_prod_type (fun p : Fin m × Fin n => M p.1 p.2 ω)).symm
      _ = ∑ k : Fin (m * n), M (e.symm k).1 (e.symm k).2 ω := by
            exact (Equiv.sum_comp e.symm (fun ij : Fin m × Fin n => M ij.1 ij.2 ω)).symm
      _ = ∑ k : Fin (m * n), X k ω := by
            simp [X]
  have hT_meas : MeasurableSet {ω | ‖∑ k : Fin (m * n), X k ω‖ ≥ θ} := by
    have hsum_meas : Measurable (fun ω => ∑ k : Fin (m * n), X k ω) := by
      exact Finset.measurable_sum Finset.univ (fun k _ => hX_meas k)
    exact measurableSet_le measurable_const hsum_meas.norm
  have hsubset : {ω | ‖∑ k : Fin (m * n), X k ω‖ ≥ θ}ᶜ ⊆
      {ω | specNorm (∑ i : Fin m, ∑ j : Fin n, M i j ω) ≤ θ} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    simp only [Set.mem_setOf_eq]
    rw [hspec_eq (∑ i : Fin m, ∑ j : Fin n, M i j ω), hsum ω]
    exact le_of_lt hω
  have hcompl : P {ω | ‖∑ k : Fin (m * n), X k ω‖ ≥ θ}ᶜ =
      1 - P {ω | ‖∑ k : Fin (m * n), X k ω‖ ≥ θ} := by
    rw [measure_compl hT_meas (measure_ne_top P _), measure_univ]
  have hcompl_le : 1 - ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4) ≤
      P {ω | ‖∑ k : Fin (m * n), X k ω‖ ≥ θ}ᶜ := by
    rw [hcompl]
    exact tsub_le_tsub_left hbern_le 1
  change 1 - ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4) ≤
    P {ω | specNorm (∑ i : Fin m, ∑ j : Fin n, M i j ω) ≤ θ}
  refine le_trans hcompl_le ?_
  exact measure_mono hsubset

  /- @proof-region region.target-node.session.6d63cef9545a16a2 end -/

end

end Statlib.Imported

