import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
theorem statopia_math_node_1012928599_c6ceb04b : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp0 : 0 < p)
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hXi_sq_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_var : ∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
    Integrable (fun ω => ∑ i : Fin n, (svals (maskedScaled p (Xi ω) (Mask ω)) i) ^ 2) μ
      ∧ ∫ ω, ∑ i : Fin n, (svals (maskedScaled p (Xi ω) (Mask ω)) i) ^ 2 ∂μ = (n : ℝ) := by
  /- @proof-region region.target-node.session.fe58b04de35abf31 begin -/
  intro Ω _ μ _ m n hm p hp0 Xi Mask hXi_meas hXi_sq_int hXi_var hMask_meas hMask_val hMask_law
    hIndep
  classical
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmp : (0 : ℝ) < (m : ℝ) * p := mul_pos hm0 hp0
  have hR2 : Real.sqrt ((m : ℝ) * p) ^ 2 = (m : ℝ) * p := Real.sq_sqrt hmp.le
  have hidp : ∀ (i : Fin m) (j : Fin n),
      IndepFun (fun ω => Xi ω i j * Xi ω i j) (fun ω => Mask ω i j) μ := by
    intro i j
    rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    have hM : Measurable fun (F : Fin m × Fin n → ℝ) => F (i, j) := measurable_pi_apply (i, j)
    have hX : Measurable fun (F : Fin m × Fin n → ℝ) => F (i, j) * F (i, j) := hM.mul hM
    have hInd := ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.mp hIndep
      {F : Fin m × Fin n → ℝ | F (i, j) * F (i, j) ∈ s}
      {F : Fin m × Fin n → ℝ | F (i, j) ∈ t} (hX hs) (hM ht)
    simpa using hInd
  have hMint : ∀ (i : Fin m) (j : Fin n), ∫ ω, Mask ω i j ∂μ = p := by
    intro i j
    have hs : MeasurableSet ((fun ω : Ω => Mask ω i j) ⁻¹' ({1} : Set ℝ)) :=
      (hMask_meas i j) (measurableSet_singleton (1 : ℝ))
    have hlaw : μ ((fun ω : Ω => Mask ω i j) ⁻¹' ({1} : Set ℝ)) = ENNReal.ofReal p :=
      hMask_law i j
    have hfun : (fun ω => Mask ω i j)
        = Set.indicator ((fun ω : Ω => Mask ω i j) ⁻¹' ({1} : Set ℝ)) (fun _ => (1 : ℝ)) := by
      funext ω
      rcases hMask_val i j ω with h | h
      · simp [h]
      · simp [h]
    rw [hfun, integral_indicator hs, setIntegral_const, smul_eq_mul, mul_one]
    show (μ ((fun ω : Ω => Mask ω i j) ⁻¹' ({1} : Set ℝ))).toReal = p
    rw [hlaw, ENNReal.toReal_ofReal hp0.le]
  have hvar : ∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j * Xi ω i j ∂μ = 1 := by
    intro i j
    rw [← hXi_var i j]
    simp only [sq]
  have hMix : ∀ (i : Fin m) (j : Fin n),
      ∫ ω, Mask ω i j * (Xi ω i j * Xi ω i j) ∂μ = p := by
    intro i j
    have h1 : ∫ ω, Mask ω i j * (Xi ω i j * Xi ω i j) ∂μ
        = ∫ ω, (Xi ω i j * Xi ω i j) * Mask ω i j ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
    rw [h1, IndepFun.integral_fun_mul_eq_mul_integral (hidp i j)
      (((hXi_meas i j).mul (hXi_meas i j)).aestronglyMeasurable)
      ((hMask_meas i j).aestronglyMeasurable), hvar i j, hMint i j, one_mul]
  have hAsq : ∀ (i : Fin m) (j : Fin n) (ω : Ω),
      (maskedScaled p (Xi ω) (Mask ω) i j) ^ 2
        = Mask ω i j * (Xi ω i j) ^ 2 / ((m : ℝ) * p) := by
    intro i j ω
    rcases hMask_val i j ω with h | h
    · simp [maskedScaled, h]
    · simp only [maskedScaled, h, one_mul, div_pow, hR2]
  have hEntry : ∀ (i : Fin m) (j : Fin n),
      ∫ ω, (maskedScaled p (Xi ω) (Mask ω) i j) ^ 2 ∂μ = ((m : ℝ))⁻¹ := by
    intro i j
    rw [show (fun ω => (maskedScaled p (Xi ω) (Mask ω) i j) ^ 2)
        = fun ω => Mask ω i j * (Xi ω i j) ^ 2 / ((m : ℝ) * p) from funext (hAsq i j)]
    rw [show (fun ω => Mask ω i j * (Xi ω i j) ^ 2 / ((m : ℝ) * p))
        = fun ω => Mask ω i j * (Xi ω i j * Xi ω i j) / ((m : ℝ) * p) from by
      funext ω
      rw [sq]]
    rw [integral_div, hMix i j]
    field_simp
  have hAint : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω => (maskedScaled p (Xi ω) (Mask ω) i j) ^ 2) μ := by
    intro i j
    have hfm : Measurable fun ω => (maskedScaled p (Xi ω) (Mask ω) i j) ^ 2 := by
      have h1 : Measurable fun ω => Mask ω i j * Xi ω i j / Real.sqrt ((m : ℝ) * p) :=
        ((hMask_meas i j).mul (hXi_meas i j)).div_const _
      simpa [maskedScaled, sq] using h1.mul h1
    refine Integrable.mono' (g := fun ω => ((m : ℝ) * p)⁻¹ * (Xi ω i j) ^ 2)
      ((hXi_sq_int i j).const_mul _) hfm.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [hAsq i j ω]
    rcases hMask_val i j ω with h | h
    · rw [h, zero_mul, zero_div, Real.norm_eq_abs, abs_zero]
      exact mul_nonneg (le_of_lt (inv_pos.mpr hmp)) (sq_nonneg _)
    · have hnn : 0 ≤ (Xi ω i j) ^ 2 / ((m : ℝ) * p) := div_nonneg (sq_nonneg _) hmp.le
      rw [h, one_mul, Real.norm_eq_abs, abs_of_nonneg hnn, div_eq_mul_inv, mul_comm]
  have hTraceId : ∀ (A : Matrix (Fin m) (Fin n) ℝ),
      (∑ i : Fin n, (svals A i) ^ 2) = ∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2 := by
    intro A
    let E : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (by simp)
    have hev : ∀ i : Fin n, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i
        = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ (E.symm i) :=
      fun i => rfl
    have hnn : ∀ k : Fin (Fintype.card (Fin n)),
        0 ≤ (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ k := by
      intro k
      have hk : (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ k
          = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues (E k) := by
        have h1 : (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ (E.symm (E k))
            = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ k := by
          rw [Equiv.symm_apply_apply]
        exact h1.symm.trans (hev (E k)).symm
      rw [hk]
      exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg A _
    have hsq : ∀ i : Fin n,
        (svals A i) ^ 2 = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀
          (Fin.cast (Fintype.card_fin n).symm i) := by
      intro i
      rw [svals, Real.sq_sqrt (hnn _)]
    have hcast : ∑ i : Fin n, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀
          (Fin.cast (Fintype.card_fin n).symm i)
        = ∑ k : Fin (Fintype.card (Fin n)),
            (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ k :=
      Equiv.sum_comp (finCongr (Fintype.card_fin n).symm) _
    have hevsum : ∑ k : Fin (Fintype.card (Fin n)),
          (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ k
        = ∑ i : Fin n, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i := by
      simp only [Matrix.IsHermitian.eigenvalues]
      exact (Equiv.sum_comp _ _).symm
    have hsum : ∑ i : Fin n, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i
        = (A.conjTranspose * A).trace := by
      rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues
        (Matrix.isHermitian_conjTranspose_mul_self A)]
      simp
    have htr : (A.conjTranspose * A).trace
        = ∑ i : Fin n, (A.conjTranspose * A) i i := rfl
    have hdiag : ∀ i : Fin n, (A.conjTranspose * A) i i = ∑ j : Fin m, (A j i) ^ 2 := by
      intro i
      simp [Matrix.mul_apply, sq]
    calc ∑ i : Fin n, (svals A i) ^ 2
        = ∑ i : Fin n, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀
            (Fin.cast (Fintype.card_fin n).symm i) :=
          Finset.sum_congr rfl (fun i _ => hsq i)
      _ = ∑ k : Fin (Fintype.card (Fin n)),
            (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ k := hcast
      _ = ∑ i : Fin n, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i := hevsum
      _ = (A.conjTranspose * A).trace := hsum
      _ = ∑ i : Fin n, (A.conjTranspose * A) i i := htr
      _ = ∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2 := by
          rw [Finset.sum_congr rfl (fun i _ => hdiag i), Finset.sum_comm]
  have hInt :
      Integrable (fun ω => ∑ i : Fin n, (svals (maskedScaled p (Xi ω) (Mask ω)) i) ^ 2) μ := by
    have hdbl : Integrable (fun ω => ∑ i : Fin m, ∑ j : Fin n,
        (maskedScaled p (Xi ω) (Mask ω) i j) ^ 2) μ :=
      integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hAint i j))
    refine hdbl.congr ?_
    filter_upwards with ω
    exact (hTraceId (maskedScaled p (Xi ω) (Mask ω))).symm
  have hMom :
      ∫ ω, ∑ i : Fin n, (svals (maskedScaled p (Xi ω) (Mask ω)) i) ^ 2 ∂μ = (n : ℝ) := by
    have hpt : (fun ω => ∑ i : Fin n, (svals (maskedScaled p (Xi ω) (Mask ω)) i) ^ 2)
        = fun ω => ∑ i : Fin m, ∑ j : Fin n, (maskedScaled p (Xi ω) (Mask ω) i j) ^ 2 :=
      funext fun ω => hTraceId _
    rw [hpt]
    calc ∫ ω, ∑ i : Fin m, ∑ j : Fin n, (maskedScaled p (Xi ω) (Mask ω) i j) ^ 2 ∂μ
        = ∑ i : Fin m, ∫ ω, ∑ j : Fin n,
            (maskedScaled p (Xi ω) (Mask ω) i j) ^ 2 ∂μ :=
          integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hAint i j))
      _ = ∑ i : Fin m, ∑ j : Fin n, ((m : ℝ))⁻¹ := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [integral_finset_sum _ (fun j _ => hAint i j)]
          simp only [hEntry]
      _ = (n : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [mul_comm ((n : ℝ)) (((m : ℝ))⁻¹), ← mul_assoc,
            mul_inv_cancel₀ (ne_of_gt hm0), one_mul]
  exact ⟨hInt, hMom⟩

  /- @proof-region region.target-node.session.fe58b04de35abf31 end -/

end Statlib.Imported

