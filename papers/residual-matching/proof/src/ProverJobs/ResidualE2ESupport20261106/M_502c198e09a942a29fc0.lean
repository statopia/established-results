import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_1826cf4a199ca47d64c5
import ProverJobs.ResidualE2ESupport20261106.M_a3db840897049c635923

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3749303560_8ce7b7f3 : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CD : ℝ) (hCD : max (Kt * (D0 + 12)) (D0 + 20) ≤ CD),
    ∃ M1 : ℕ,
      ∀ (m : ℕ) (hm : 2 ≤ m) (hM1 : M1 ≤ m)
        (hrho_lo : rhoMinus ≤ (1 : ℝ) / (m : ℝ))
        (hrho_hi : (1 : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (XT Mask : Ω → Matrix (Fin m) (Fin 1) ℝ)
        (hXT_meas : ∀ (i : Fin m) (j : Fin 1), Measurable fun ω => XT ω i j)
        (hXT_int : ∀ (i : Fin m) (j : Fin 1), Integrable (fun ω => XT ω i j) μ)
        (hXT_sq_int : ∀ (i : Fin m) (j : Fin 1), Integrable (fun ω => (XT ω i j) ^ 2) μ)
        (hXT_indep : iIndepFun (fun (ij : Fin m × Fin 1) (ω : Ω) => XT ω ij.1 ij.2) μ)
        (hXT_mean : ∀ (i : Fin m) (j : Fin 1), ∫ ω, XT ω i j ∂μ = 0)
        (hXT_var : ∀ (i : Fin m) (j : Fin 1), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1)
        (hMask_meas : ∀ (i : Fin m) (j : Fin 1), Measurable fun ω => Mask ω i j)
        (hMask_val : ∀ (i : Fin m) (j : Fin 1) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
        (hMask_law : ∀ (i : Fin m) (j : Fin 1),
          μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
        (hMask_indep : iIndepFun (fun (ij : Fin m × Fin 1) (ω : Ω) => Mask ω ij.1 ij.2) μ)
        (hIndep : IndepFun (fun ω (ij : Fin m × Fin 1) => XT ω ij.1 ij.2)
          (fun ω (ij : Fin m × Fin 1) => Mask ω ij.1 ij.2) μ)
        (hXT_bound : let L : ℝ := CD * Real.log ((m : ℝ) * ((1 : ℕ) : ℝ)) +
            10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4;
          ∀ (ω : Ω) (i : Fin m) (j : Fin 1), |XT ω i j| ≤ 3 * L),
        μ {ω | svals (maskedScaled p (XT ω) (Mask ω)) (⟨1 - 1, by omega⟩ : Fin 1) <
              1 - Real.sqrt ((1 : ℝ) / (m : ℝ)) - 1 * deltaM m} ≤
          ENNReal.ofReal (Real.rpow ((1 : ℕ) : ℝ) (-(D0 + 4)) / 2) := by
  /- @proof-region region.target-node.session.f617f069cfd33282 begin -/
  intro D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le Kt hKt alpha0 halpha0 CD hCD
  obtain ⟨M1, hlow⟩ := statopia_math_node_3786680764_db220746 D0 hD0 rhoMinus hrhoMinus_pos
    hrhoMinus_le Kt hKt alpha0 halpha0 CD hCD
  refine ⟨M1, ?_⟩
  intro m hm hM1m hrho_lo hrho_hi p hp0 hp1 hsparse Ω _inst μ _inst2 XT Mask
    hXT_meas hXT_int hXT_sq_int hXT_indep hXT_mean hXT_var hMask_meas hMask_val hMask_law
    hMask_indep hIndep hXT_bound
  have hprobe : ∀ (B : Matrix (Fin 1) (Fin 1) ℝ) (hB : B.IsHermitian)
      (k : Fin (Fintype.card (Fin 1))), hB.eigenvalues₀ k = B 0 0 := by
    intro B hB k
    have h0 : ∀ j : Fin 1, hB.eigenvalues j = B 0 0 := by
      intro j
      have hdet := Matrix.IsHermitian.det_eq_prod_eigenvalues hB
      rw [Matrix.det_fin_one, Fin.prod_univ_one] at hdet
      rw [Subsingleton.elim j 0]
      simpa using hdet.symm
    unfold Matrix.IsHermitian.eigenvalues₀
    have hev : Module.End.HasEigenvalue (Matrix.toEuclideanLin B) (hB.eigenvalues₀ k) :=
      LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ k
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hsmul : Matrix.toEuclideanLin B v = (hB.eigenvalues₀ k) • v := hv.apply_eq_smul
    have hne : v ≠ 0 := hv.2
    have hv0 : v 0 ≠ 0 := by
      intro h
      apply hne
      first
        | exact WithLp.ofLp_injective (by
            funext i
            rw [Subsingleton.elim i (0 : Fin 1)]
            simpa using h)
        | (ext i
           rw [Subsingleton.elim i (0 : Fin 1)]
           simpa using h)
    have hc : (Matrix.toEuclideanLin B v) 0 = hB.eigenvalues₀ k * v 0 := by
      rw [hsmul]
      simp
    have hcoord : (Matrix.toEuclideanLin B v) 0 = (B.mulVec v) 0 := by
      simp
    have hcoord2 : (B.mulVec v) 0 = B 0 0 * v 0 := by
      have hdp : (fun j => B 0 j) ⬝ᵥ v.ofLp = ∑ j : Fin 1, B 0 j * v.ofLp j := rfl
      simp only [Matrix.mulVec, hdp]
      simp
    have hfinal : hB.eigenvalues₀ k * v 0 = B 0 0 * v 0 := by
      rw [← hc, hcoord, hcoord2]
    exact mul_right_cancel₀ hv0 hfinal
  have hsv : ∀ (A : Matrix (Fin m) (Fin 1) ℝ) (i : Fin 1),
      svals A i = Real.sqrt (∑ k : Fin m, (A k 0) ^ 2) := by
    intro A i
    have h1 : svals A i = Real.sqrt ((Matrix.conjTranspose A * A) 0 0) := by
      unfold svals
      exact congrArg Real.sqrt
        (hprobe (Matrix.conjTranspose A * A) (Matrix.isHermitian_conjTranspose_mul_self A)
          (Fin.cast (Fintype.card_fin 1).symm i))
    have h2 : (Matrix.conjTranspose A * A) 0 0 = ∑ k : Fin m, (A k 0) ^ 2 := by
      simp [Matrix.mul_apply, sq]
    rw [h1, h2]
  have hset : {ω | svals (maskedScaled p (XT ω) (Mask ω)) (⟨1 - 1, by omega⟩ : Fin 1) <
        1 - Real.sqrt ((1 : ℝ) / (m : ℝ)) - 1 * deltaM m} =
      {ω | Real.sqrt (∑ i : Fin m, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2) <
        1 - Real.sqrt ((1 : ℝ) / (m : ℝ)) - 1 * deltaM m} := by
    ext ω
    simp only [Set.mem_setOf_eq,
      hsv (maskedScaled p (XT ω) (Mask ω)) (⟨1 - 1, by omega⟩ : Fin 1)]
  rw [hset]
  exact hlow m hm hM1m hrho_lo hrho_hi p hp0 hp1 hsparse μ XT Mask hXT_meas hXT_int
    hXT_sq_int hXT_indep hXT_mean hXT_var hMask_meas hMask_val hMask_law hMask_indep hIndep
    hXT_bound
  /- @proof-region region.target-node.session.f617f069cfd33282 end -/

end Statlib.Imported

