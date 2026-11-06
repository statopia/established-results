import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_345aa4126e25a07275f2
import ProverJobs.ResidualE2ESupport20261106.M_f342010aecdd79426bfc

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
theorem statopia_math_node_4008937357_c32b14f6 : ∀ (m n r D : ℕ) (mu0 p : ℝ) (b : Fin D → Matrix (Fin m) (Fin n) ℝ)
    (hn : 1 ≤ n) (hp : 0 < p) (hp1 : p ≤ 1) (hmu0 : 0 < mu0 * (r : ℝ))
    (hident : ∀ (i : Fin m) (j : Fin n),
      Real.sqrt (∑ q : Fin D, (tangentCoords b i j q) ^ 2) ^ 2
        ≤ 4 * (mu0 * (r : ℝ)) / (n : ℝ))
    (hframe : (∑ i : Fin m, ∑ j : Fin n,
        Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j) :
          Matrix (Fin D) (Fin D) ℝ) = 1)
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Om : Fin m → Fin n → Omega → ℝ)
    (h01 : ∀ (i : Fin m) (j : Fin n), ∀ᵐ ω ∂P, Om i j ω = 0 ∨ Om i j ω = 1)
    (hprob : ∀ (i : Fin m) (j : Fin n), P {ω | Om i j ω = 1} = ENNReal.ofReal p)
    (hint : ∀ (i : Fin m) (j : Fin n), Integrable (Om i j) P),
    let M : Fin m → Fin n → Omega → Matrix (Fin D) (Fin D) ℝ :=
      fun i j ω => (p⁻¹ * Om i j ω - 1) •
        Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)
    let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
    ‖∑ k : Fin (m * n),
        ∫ ω, M (e.symm k).1 (e.symm k).2 ω * M (e.symm k).1 (e.symm k).2 ω ∂P‖
      ≤ 4 * (mu0 * (r : ℝ)) / ((n : ℝ) * p) := by
  /- @proof-region region.target-node.session.e1f8d4f4f4b8f280 begin -/
  intro m n r D mu0 p b hn hp hp1 hmu0 hident hframe Omega _ P _ Om h01 hprob hInt
  classical
  dsimp only
  set M : Fin m → Fin n → Omega → Matrix (Fin D) (Fin D) ℝ :=
    fun i j omega =>
      (p⁻¹ * Om i j omega - 1) •
        Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j) with hM
  set S : ℝ := 4 * (mu0 * (r : ℝ)) / (n : ℝ) with hS
  set B : Matrix (Fin D) (Fin D) ℝ :=
    ∑ i : Fin m, ∑ j : Fin n, (∑ q : Fin D, (tangentCoords b i j q) ^ 2) •
      Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j) with hB
  change specNorm (∑ k : Fin (m * n),
      ∫ omega, M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 omega *
        M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 omega ∂P)
      ≤ 4 * (mu0 * (r : ℝ)) / ((n : ℝ) * p)
  have hspec_eq : ∀ A : Matrix (Fin D) (Fin D) ℝ, specNorm A = ‖A‖ := by
    intro A
    show ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖ = ‖A‖
    exact (Matrix.l2_opNorm_def A).symm
  have hCmul : ∀ (i : Fin m) (j : Fin n),
      Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j) *
        Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)
        = (∑ q : Fin D, (tangentCoords b i j q) ^ 2) •
            Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j) := by
    intro i j
    ext a bb
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply]
    calc ∑ x : Fin D,
          (tangentCoords b i j a * tangentCoords b i j x) *
            (tangentCoords b i j x * tangentCoords b i j bb)
        = ∑ x : Fin D, (tangentCoords b i j a * tangentCoords b i j bb) *
            (tangentCoords b i j x) ^ 2 :=
          Finset.sum_congr rfl (fun x _ => by ring)
      _ = (tangentCoords b i j a * tangentCoords b i j bb) *
            ∑ x : Fin D, (tangentCoords b i j x) ^ 2 := by rw [Finset.mul_sum]
      _ = (∑ x : Fin D, (tangentCoords b i j x) ^ 2) *
            (tangentCoords b i j a * tangentCoords b i j bb) := by ring
  have hterm : ∀ (i : Fin m) (j : Fin n),
      ∫ omega, M i j omega * M i j omega ∂P
        = ((1 - p) / p) • ((∑ q : Fin D, (tangentCoords b i j q) ^ 2) •
            Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)) := by
    intro i j
    have hpt : ∀ omega, M i j omega * M i j omega
        = ((p⁻¹ * Om i j omega - 1) ^ 2) •
            ((∑ q : Fin D, (tangentCoords b i j q) ^ 2) •
              Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)) := by
      intro omega
      simp only [hM]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hCmul i j, sq]
    calc ∫ omega, M i j omega * M i j omega ∂P
        = ∫ omega, ((p⁻¹ * Om i j omega - 1) ^ 2) •
            ((∑ q : Fin D, (tangentCoords b i j q) ^ 2) •
              Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)) ∂P := by
          simp only [hpt]
      _ = (∫ omega, (p⁻¹ * Om i j omega - 1) ^ 2 ∂P) •
            ((∑ q : Fin D, (tangentCoords b i j q) ^ 2) •
              Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)) :=
          integral_smul_const _ _
      _ = ((1 - p) / p) •
            ((∑ q : Fin D, (tangentCoords b i j q) ^ 2) •
              Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)) := by
          rw [statopia_math_node_334888657_5530b0ba P (Om i j) p hp hp1 (hInt i j)
            (h01 i j) (hprob i j)]
  have hsum : (∑ k : Fin (m * n),
      ∫ omega, M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 omega *
        M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 omega ∂P)
      = ((1 - p) / p) • B := by
    have hreindex : (∑ k : Fin (m * n),
        ∫ omega, M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 omega *
          M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 omega ∂P)
        = ∑ pq : Fin m × Fin n,
            ∫ omega, M pq.1 pq.2 omega * M pq.1 pq.2 omega ∂P := by
      rw [(Equiv.sum_comp finProdFinEquiv (fun k : Fin (m * n) =>
        ∫ omega, M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 omega *
          M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 omega ∂P)).symm]
      simp only [Equiv.symm_apply_apply]
    have hpair : (∑ pq : Fin m × Fin n,
        ∫ omega, M pq.1 pq.2 omega * M pq.1 pq.2 omega ∂P)
        = ∑ i : Fin m, ∑ j : Fin n,
            ∫ omega, M i j omega * M i j omega ∂P :=
      Fintype.sum_prod_type (fun pq : Fin m × Fin n =>
        ∫ omega, M pq.1 pq.2 omega * M pq.1 pq.2 omega ∂P)
    rw [hreindex, hpair]
    simp only [hterm]
    rw [hB]
    simp only [Finset.smul_sum]
  have hcoef : 0 ≤ (1 - p) / p := div_nonneg (by linarith) (le_of_lt hp)
  have hsmul : specNorm (((1 - p) / p) • B) = ((1 - p) / p) * specNorm B := by
    show ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (((1 - p) / p) • B)‖
      = ((1 - p) / p) * ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) B‖
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
  have hSnnB : 0 ≤ S := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [hS]
    exact div_nonneg (by nlinarith [hmu0]) (le_of_lt hnpos)
  have harith : ((1 - p) / p) * S ≤ 4 * (mu0 * (r : ℝ)) / ((n : ℝ) * p) := by
    rw [← div_div, ← hS, div_eq_mul_inv, div_eq_mul_inv]
    have hprod : 0 ≤ S * p⁻¹ := mul_nonneg hSnnB (le_of_lt (inv_pos.mpr hp))
    calc ((1 - p) * p⁻¹) * S = (1 - p) * (S * p⁻¹) := by ring
      _ ≤ 1 * (S * p⁻¹) := mul_le_mul_of_nonneg_right (by linarith) hprod
      _ = S * p⁻¹ := by ring
  have hCpsd : ∀ (i : Fin m) (j : Fin n),
      (Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)).PosSemidef := by
    intro i j
    simpa using Matrix.posSemidef_vecMulVec_self_star (tangentCoords b i j)
  have hsnn : ∀ (i : Fin m) (j : Fin n), 0 ≤ (∑ q : Fin D, (tangentCoords b i j q) ^ 2) := by
    intro i j
    positivity
  have hBpsd : B.PosSemidef := by
    rw [hB]
    exact Matrix.posSemidef_sum Finset.univ (fun i _ =>
      Matrix.posSemidef_sum Finset.univ (fun j _ =>
        Matrix.PosSemidef.smul (hCpsd i j) (hsnn i j)))
  have hSle : ∀ (i : Fin m) (j : Fin n), (∑ q : Fin D, (tangentCoords b i j q) ^ 2) ≤ S := by
    intro i j
    have h := hident i j
    rw [Real.sq_sqrt (hsnn i j)] at h
    rwa [hS]
  have hSB : (S • (1 : Matrix (Fin D) (Fin D) ℝ) - B).PosSemidef := by
    have hsplit : S • (1 : Matrix (Fin D) (Fin D) ℝ) - B
        = ∑ i : Fin m, ∑ j : Fin n,
            (S - (∑ q : Fin D, (tangentCoords b i j q) ^ 2)) •
              Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j) := by
      rw [hB, ← hframe]
      simp only [Finset.smul_sum, Finset.sum_sub_distrib, sub_smul]
    rw [hsplit]
    exact Matrix.posSemidef_sum Finset.univ (fun i _ =>
      Matrix.posSemidef_sum Finset.univ (fun j _ =>
        Matrix.PosSemidef.smul (hCpsd i j) (by linarith [hSle i j])))
  have hnormB : specNorm B ≤ S := by
    rw [hspec_eq B]
    exact statopia_math_node_3711227582_dba90c3d D B S hSnnB hBpsd hSB
  rw [hsum, hsmul]
  calc ((1 - p) / p) * specNorm B ≤ ((1 - p) / p) * S :=
        mul_le_mul_of_nonneg_left hnormB hcoef
    _ ≤ 4 * (mu0 * (r : ℝ)) / ((n : ℝ) * p) := harith
  /- @proof-region region.target-node.session.e1f8d4f4f4b8f280 end -/

end

end Statlib.Imported

