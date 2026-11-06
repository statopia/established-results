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
theorem statopia_math_node_2013117215_3eebf068 : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hXi_int3 : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => |Xi ω i j| ^ 3) μ)
    (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ)
    (h : Fin m × Fin n),
    Integrable (fun ω => |maskedScaled p (Xi ω) (Mask ω) h.1 h.2| ^ 3) μ ∧
      (∫ ω, |maskedScaled p (Xi ω) (Mask ω) h.1 h.2| ^ 3 ∂μ
        = p * (∫ ω, |Xi ω h.1 h.2| ^ 3 ∂μ) * ((Real.sqrt ((m : ℝ) * p))⁻¹) ^ 3) := by
  /- @proof-region region.target-node.session.8d89bdac88999cd0 begin -/
  intro m n hm hn p hp hp1 Ω hΩ μ hμ Xi Mask hXi_meas hXi_int3 hXi_indep hMask_meas hMask_val hMask_law hMask_indep hIndep h
  classical
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmp : 0 < (m:ℝ) * p := mul_pos (lt_of_lt_of_le zero_lt_one hmR) hp
  have hc : 0 < Real.sqrt ((m:ℝ) * p) := Real.sqrt_pos.mpr hmp
  have hmeas_set : MeasurableSet {ω | Mask ω h.1 h.2 = 1} := by
    have hh := (hMask_meas h.1 h.2) (measurableSet_singleton (1:ℝ))
    rw [show (fun ω => Mask ω h.1 h.2) ⁻¹' ({1} : Set ℝ) = {ω | Mask ω h.1 h.2 = 1} from by
      ext ω; simp] at hh
    exact hh
  have hXint : Integrable (fun ω => |Xi ω h.1 h.2| ^ 3) μ := hXi_int3 h.1 h.2
  have hpt : ∀ ω, |maskedScaled p (Xi ω) (Mask ω) h.1 h.2| ^ 3
      = (Mask ω h.1 h.2 * |Xi ω h.1 h.2| ^ 3) * ((Real.sqrt ((m:ℝ)*p))⁻¹)^3 := by
    intro ω
    simp only [maskedScaled]
    rcases hMask_val h.1 h.2 ω with hM | hM
    · rw [hM]; simp
    · rw [hM]; simp only [one_mul]
      rw [abs_div, abs_of_pos hc, div_eq_mul_inv, mul_pow]
  constructor
  · have hg_int : Integrable (fun ω => Mask ω h.1 h.2 * |Xi ω h.1 h.2| ^ 3) μ := by
      have hgeq : (fun ω => Mask ω h.1 h.2 * |Xi ω h.1 h.2| ^ 3)
          = ({ω | Mask ω h.1 h.2 = 1}).indicator (fun ω => |Xi ω h.1 h.2| ^ 3) := by
        funext ω; rcases hMask_val h.1 h.2 ω with hM | hM <;> simp [hM]
      rw [hgeq]
      exact hXint.indicator hmeas_set
    have hfeq : (fun ω => |maskedScaled p (Xi ω) (Mask ω) h.1 h.2| ^ 3)
        = fun ω => (Mask ω h.1 h.2 * |Xi ω h.1 h.2| ^ 3) * ((Real.sqrt ((m:ℝ)*p))⁻¹)^3 := funext hpt
    rw [hfeq]
    exact hg_int.mul_const _
  · have hInd0 : IndepFun (fun ω => |Xi ω h.1 h.2| ^ 3) (fun ω => Mask ω h.1 h.2) μ :=
      hIndep.comp
        (φ := fun (v : Fin m × Fin n → ℝ) => |v h| ^ 3)
        (ψ := fun (v : Fin m × Fin n → ℝ) => v h)
        (by
          have hb : Measurable (fun (v : Fin m × Fin n → ℝ) => v h) := measurable_pi_apply h
          exact hb.abs.pow_const 3)
        (measurable_pi_apply h)
    have hAEM_X : AEStronglyMeasurable (fun ω => |Xi ω h.1 h.2| ^ 3) μ := hXint.aestronglyMeasurable
    have hAEM_M : AEStronglyMeasurable (fun ω => Mask ω h.1 h.2) μ := (hMask_meas h.1 h.2).aestronglyMeasurable
    have key := ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral hInd0 hAEM_X hAEM_M
    have key' : ∫ x, |Xi x h.1 h.2| ^ 3 * Mask x h.1 h.2 ∂μ
        = (∫ x, |Xi x h.1 h.2| ^ 3 ∂μ) * (∫ x, Mask x h.1 h.2 ∂μ) := key
    have hgmul : ∫ x, Mask x h.1 h.2 * |Xi x h.1 h.2| ^ 3 ∂μ
        = (∫ x, Mask x h.1 h.2 ∂μ) * (∫ x, |Xi x h.1 h.2| ^ 3 ∂μ) := by
      have hL : ∫ x, Mask x h.1 h.2 * |Xi x h.1 h.2| ^ 3 ∂μ
          = ∫ x, |Xi x h.1 h.2| ^ 3 * Mask x h.1 h.2 ∂μ := by
        rw [show (fun x => Mask x h.1 h.2 * |Xi x h.1 h.2| ^ 3)
            = (fun x => |Xi x h.1 h.2| ^ 3 * Mask x h.1 h.2) from funext (fun x => mul_comm _ _)]
      rw [hL, key']
      ring
    have hM_int : ∫ x, Mask x h.1 h.2 ∂μ = p := by
      have hMeq : (fun ω => Mask ω h.1 h.2) = ({ω | Mask ω h.1 h.2 = 1}).indicator (fun _ => (1:ℝ)) := by
        funext ω; rcases hMask_val h.1 h.2 ω with hM | hM <;> simp [hM]
      rw [hMeq, MeasureTheory.integral_indicator hmeas_set, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
      have hp' : (μ {ω | Mask ω h.1 h.2 = 1}).toReal = p := by
        rw [hMask_law h.1 h.2, ENNReal.toReal_ofReal (le_of_lt hp)]
      simpa [Measure.real] using hp'
    calc ∫ ω, |maskedScaled p (Xi ω) (Mask ω) h.1 h.2| ^ 3 ∂μ
        = ∫ ω, (Mask ω h.1 h.2 * |Xi ω h.1 h.2| ^ 3) * ((Real.sqrt ((m:ℝ)*p))⁻¹)^3 ∂μ := by
          rw [funext hpt]
      _ = (∫ ω, Mask ω h.1 h.2 * |Xi ω h.1 h.2| ^ 3 ∂μ) * ((Real.sqrt ((m:ℝ)*p))⁻¹)^3 := by
          rw [MeasureTheory.integral_mul_const]
      _ = ((∫ ω, Mask ω h.1 h.2 ∂μ) * (∫ ω, |Xi ω h.1 h.2| ^ 3 ∂μ)) * ((Real.sqrt ((m:ℝ)*p))⁻¹)^3 := by
          rw [hgmul]
      _ = p * (∫ ω, |Xi ω h.1 h.2| ^ 3 ∂μ) * ((Real.sqrt ((m:ℝ)*p))⁻¹)^3 := by
          rw [hM_int]
  /- @proof-region region.target-node.session.8d89bdac88999cd0 end -/

end Statlib.Imported

