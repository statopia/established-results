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
theorem statopia_math_node_499696627_ce536ec6 : ∀ (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (XT Mask : Ω → Matrix (Fin m) (Fin 1) ℝ)
    (hXT_meas : ∀ (i : Fin m) (j : Fin 1), Measurable fun ω => XT ω i j)
    (hXT_sq_int : ∀ (i : Fin m) (j : Fin 1), Integrable (fun ω => (XT ω i j) ^ 2) μ)
    (hXT_indep : iIndepFun (fun (ij : Fin m × Fin 1) (ω : Ω) => XT ω ij.1 ij.2) μ)
    (hXT_var : ∀ (i : Fin m) (j : Fin 1), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1)
    (hMask_meas : ∀ (i : Fin m) (j : Fin 1), Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ (i : Fin m) (j : Fin 1) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ (i : Fin m) (j : Fin 1), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin 1) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin 1) => XT ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin 1) => Mask ω ij.1 ij.2) μ)
    (i j : Fin m) (hij : i ≠ j),
    (∫ ω, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 *
        (maskedScaled p (XT ω) (Mask ω) j 0) ^ 2 ∂μ)
      = (1 / (m : ℝ)) * (1 / (m : ℝ)) := by
  /- @proof-region region.target-node.session.2ebd26699abce99e begin -/
  intro m hm p hp0 hp1 Ω instΩ μ instμ XT Mask hXT_meas hXT_sq_int hXT_indep hXT_var hMask_meas hMask_val hMask_law hMask_indep hIndep i j hij
  letI := instΩ
  letI := instμ
  have hij' : (i, (0 : Fin 1)) ≠ (j, (0 : Fin 1)) := by
    intro h
    exact hij (congrArg Prod.fst h)
  have hXTpair : (fun ω => XT ω i 0) ⟂ᵢ[μ] (fun ω => XT ω j 0) := hXT_indep.indepFun hij'
  have hMaskpair : (fun ω => Mask ω i 0) ⟂ᵢ[μ] (fun ω => Mask ω j 0) := hMask_indep.indepFun hij'
  have hsqm : Measurable (fun x : ℝ => x ^ 2) := by measurability
  have hXT_int : ∫ ω, (XT ω i 0) ^ 2 * (XT ω j 0) ^ 2 ∂μ = 1 := by
    have key : ∫ ω, (XT ω i 0) ^ 2 * (XT ω j 0) ^ 2 ∂μ
        = (∫ ω, (XT ω i 0) ^ 2 ∂μ) * (∫ ω, (XT ω j 0) ^ 2 ∂μ) :=
      hXTpair.integral_fun_comp_mul_comp (hXT_meas i 0).aemeasurable (hXT_meas j 0).aemeasurable
        hsqm.aestronglyMeasurable hsqm.aestronglyMeasurable
    rw [key, hXT_var i 0, hXT_var j 0]
    ring
  have hMask_i_set : MeasurableSet {ω | Mask ω i 0 = 1} := by
    exact (hMask_meas i 0) (measurableSet_singleton (1 : ℝ))
  have hMask_j_set : MeasurableSet {ω | Mask ω j 0 = 1} := by
    exact (hMask_meas j 0) (measurableSet_singleton (1 : ℝ))
  have hMaskint_i : ∫ ω, Mask ω i 0 ∂μ = p := by
    have hind : (fun ω => Mask ω i 0) = ({ω | Mask ω i 0 = 1}.indicator (fun _ => (1 : ℝ))) := by
      funext ω
      rcases hMask_val i 0 ω with h | h
      · have hnot : ω ∉ {ω | Mask ω i 0 = 1} := by simp [h]
        rw [Set.indicator_of_notMem hnot]
        simp [h]
      · have hmem : ω ∈ {ω | Mask ω i 0 = 1} := by simp [h]
        rw [Set.indicator_of_mem hmem]
        simp [h]
    rw [hind, integral_indicator_const (1 : ℝ) hMask_i_set, smul_eq_mul, mul_one]
    change (μ {ω | Mask ω i 0 = 1}).toReal = p
    rw [hMask_law i 0, ENNReal.toReal_ofReal (le_of_lt hp0)]
  have hMaskint_j : ∫ ω, Mask ω j 0 ∂μ = p := by
    have hind : (fun ω => Mask ω j 0) = ({ω | Mask ω j 0 = 1}.indicator (fun _ => (1 : ℝ))) := by
      funext ω
      rcases hMask_val j 0 ω with h | h
      · have hnot : ω ∉ {ω | Mask ω j 0 = 1} := by simp [h]
        rw [Set.indicator_of_notMem hnot]
        simp [h]
      · have hmem : ω ∈ {ω | Mask ω j 0 = 1} := by simp [h]
        rw [Set.indicator_of_mem hmem]
        simp [h]
    rw [hind, integral_indicator_const (1 : ℝ) hMask_j_set, smul_eq_mul, mul_one]
    change (μ {ω | Mask ω j 0 = 1}).toReal = p
    rw [hMask_law j 0, ENNReal.toReal_ofReal (le_of_lt hp0)]
  have hMaskpair_int : ∫ ω, Mask ω i 0 * Mask ω j 0 ∂μ = p * p := by
    have key : ∫ ω, Mask ω i 0 * Mask ω j 0 ∂μ
        = (∫ ω, Mask ω i 0 ∂μ) * (∫ ω, Mask ω j 0 ∂μ) :=
      hMaskpair.integral_fun_mul_eq_mul_integral (hMask_meas i 0).aestronglyMeasurable
        (hMask_meas j 0).aestronglyMeasurable
    rw [key, hMaskint_i, hMaskint_j]
  have hXm : Measurable (fun (ω : Ω) (ij : Fin m × Fin 1) => XT ω ij.1 ij.2) :=
    measurable_pi_iff.mpr (fun ij => hXT_meas ij.1 ij.2)
  have hMm : Measurable (fun (ω : Ω) (ij : Fin m × Fin 1) => Mask ω ij.1 ij.2) :=
    measurable_pi_iff.mpr (fun ij => hMask_meas ij.1 ij.2)
  have hfm : Measurable (fun x : Fin m × Fin 1 → ℝ => x (i, 0) ^ 2 * x (j, 0) ^ 2) := by
    measurability
  have hgm : Measurable (fun y : Fin m × Fin 1 → ℝ => y (i, 0) * y (j, 0)) := by
    measurability
  have hmixed : ∫ ω, ((XT ω i 0) ^ 2 * (XT ω j 0) ^ 2) * (Mask ω i 0 * Mask ω j 0) ∂μ
      = (∫ ω, (XT ω i 0) ^ 2 * (XT ω j 0) ^ 2 ∂μ) * (∫ ω, Mask ω i 0 * Mask ω j 0 ∂μ) :=
    hIndep.integral_fun_comp_mul_comp hXm.aemeasurable hMm.aemeasurable
      hfm.aestronglyMeasurable hgm.aestronglyMeasurable
  have hmixed' : ∫ ω, ((XT ω i 0) ^ 2 * (XT ω j 0) ^ 2) * (Mask ω i 0 * Mask ω j 0) ∂μ
      = 1 * (p * p) := by
    rw [hmixed, hXT_int, hMaskpair_int]
  have hpoint : ∀ ω, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 * (maskedScaled p (XT ω) (Mask ω) j 0) ^ 2
      = (((XT ω i 0) ^ 2 * (XT ω j 0) ^ 2) * (Mask ω i 0 * Mask ω j 0)) * ((Real.sqrt ((m : ℝ) * p)) ^ 4)⁻¹ := by
    intro ω
    unfold maskedScaled
    have ha : (Mask ω i 0) ^ 2 = Mask ω i 0 := by rcases hMask_val i 0 ω with h | h <;> rw [h] <;> norm_num
    have hb : (Mask ω j 0) ^ 2 = Mask ω j 0 := by rcases hMask_val j 0 ω with h | h <;> rw [h] <;> norm_num
    have hAi : (Mask ω i 0 * XT ω i 0 / Real.sqrt ((m : ℝ) * p)) ^ 2
        = Mask ω i 0 * (XT ω i 0) ^ 2 / (Real.sqrt ((m : ℝ) * p)) ^ 2 := by
      rw [div_pow, mul_pow, ha]
    have hAj : (Mask ω j 0 * XT ω j 0 / Real.sqrt ((m : ℝ) * p)) ^ 2
        = Mask ω j 0 * (XT ω j 0) ^ 2 / (Real.sqrt ((m : ℝ) * p)) ^ 2 := by
      rw [div_pow, mul_pow, hb]
    rw [hAi, hAj]
    rw [div_mul_div_comm]
    have hc4 : (Real.sqrt ((m : ℝ) * p)) ^ 4
        = (Real.sqrt ((m : ℝ) * p)) ^ 2 * (Real.sqrt ((m : ℝ) * p)) ^ 2 := by ring
    rw [hc4]
    ring
  have hmain : ∫ ω, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 * (maskedScaled p (XT ω) (Mask ω) j 0) ^ 2 ∂μ
      = (1 * (p * p)) * ((Real.sqrt ((m : ℝ) * p)) ^ 4)⁻¹ := by
    have key : (∫ ω, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 * (maskedScaled p (XT ω) (Mask ω) j 0) ^ 2 ∂μ)
        = ∫ ω, (((XT ω i 0) ^ 2 * (XT ω j 0) ^ 2) * (Mask ω i 0 * Mask ω j 0)) * ((Real.sqrt ((m : ℝ) * p)) ^ 4)⁻¹ ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    rw [key, integral_mul_const, hmixed']
  rw [hmain]
  have hsq : (Real.sqrt ((m : ℝ) * p)) ^ 2 = (m : ℝ) * p :=
    Real.sq_sqrt (mul_nonneg (by exact_mod_cast Nat.zero_le m) (le_of_lt hp0))
  have h4 : ((Real.sqrt ((m : ℝ) * p)) ^ 4)⁻¹ = (((m : ℝ) * p) ^ 2)⁻¹ := by
    have h44 : (Real.sqrt ((m : ℝ) * p)) ^ 4 = ((Real.sqrt ((m : ℝ) * p)) ^ 2) ^ 2 := by ring
    rw [h44, hsq]
  rw [h4]
  have hm0 : (m : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hmp : (m : ℝ) * p ≠ 0 := mul_ne_zero hm0 hpne
  have hmp2 : ((m : ℝ) * p) ^ 2 ≠ 0 := pow_ne_zero 2 hmp
  field_simp
  /- @proof-region region.target-node.session.2ebd26699abce99e end -/

end Statlib.Imported

