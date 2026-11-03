import Lean
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Vocabulary
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Base

namespace PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_318020560_e6aa841c : ∀ (c : ℝ) (hc : 0 < c)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z)
    (hInt_pos : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ)
    (hInt_neg : ∀ t : ℝ, Integrable (fun ω => Real.exp (-t * Z ω)) μ)
    (hMGF_pos : ∀ t : ℝ, ∫ ω, Real.exp (t * Z ω) ∂μ ≤ Real.exp (c * t ^ 2 / 2))
    (hMGF_neg : ∀ t : ℝ, ∫ ω, Real.exp (-t * Z ω) ∂μ ≤ Real.exp (c * t ^ 2 / 2))
    (m : ℕ) (hm : 1 ≤ m),
    ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * m)) ∂μ ≤
      ENNReal.ofReal
        ((Real.sqrt (2 * c * Real.exp 1) * Real.sqrt (2 * (m : ℝ))) ^ (2 * m)) := by
  /- @proof-region region.target-node.session.a31af78d8d49a889 begin -/
  intro c hc Ω _ μ _ Z hZ hint_pos hint_neg hbound_pos hbound_neg m hm
  set t : ℝ := Real.sqrt (2 * (m : ℝ) / c) with ht_def
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have harg_pos : 0 < 2 * (m : ℝ) / c := by
    apply div_pos
    · linarith
    · exact hc
  have ht_pos : 0 < t := by
    rw [ht_def]; exact Real.sqrt_pos.mpr harg_pos
  have ht_sq : t ^ 2 = 2 * (m : ℝ) / c := by
    rw [ht_def]; exact Real.sq_sqrt harg_pos.le
  have hpoint : ∀ ω : Ω, (t * |Z ω|) ^ (2 * m) / ((2 * m).factorial : ℝ)
      ≤ Real.exp (t * Z ω) + Real.exp (-t * Z ω) := by
    intro ω
    by_cases hz : 0 ≤ Z ω
    · rw [abs_of_nonneg hz]
      have h1 := Real.pow_div_factorial_le_exp (t * Z ω) (mul_nonneg ht_pos.le hz) (2 * m)
      have h2 : (0:ℝ) ≤ Real.exp (-t * Z ω) := (Real.exp_pos _).le
      linarith [h1, h2]
    · push_neg at hz
      rw [abs_of_neg hz]
      have hneg : (0:ℝ) ≤ -t * Z ω := by
        have h1 : t * Z ω < 0 := mul_neg_of_pos_of_neg ht_pos hz
        rw [neg_mul]; exact neg_nonneg.mpr h1.le
      have h1 := Real.pow_div_factorial_le_exp (-t * Z ω) hneg (2 * m)
      have heq : t * -Z ω = -t * Z ω := by ring
      rw [heq]
      have h2 : (0:ℝ) ≤ Real.exp (t * Z ω) := (Real.exp_pos _).le
      linarith [h1, h2]
  have hA : Measurable (fun ω : Ω => ENNReal.ofReal (Real.exp (t * Z ω))) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul hZ)).ennreal_ofReal
  have hfact_nn : (0:ℝ) ≤ t ^ (2 * m) / ((2 * m).factorial : ℝ) :=
    div_nonneg (pow_nonneg ht_pos.le _) (by exact_mod_cast (Nat.factorial_pos (2 * m)).le)
  have hfactor : ∀ ω : Ω, ENNReal.ofReal ((t * |Z ω|) ^ (2 * m) / ((2 * m).factorial : ℝ))
      = ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ)) * ENNReal.ofReal (|Z ω| ^ (2 * m)) := by
    intro ω
    rw [← ENNReal.ofReal_mul hfact_nn]
    congr 1
    rw [mul_pow, div_mul_eq_mul_div]
  have step1 : ∫⁻ ω, ENNReal.ofReal ((t * |Z ω|) ^ (2 * m) / ((2 * m).factorial : ℝ)) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (t * Z ω)) + ENNReal.ofReal (Real.exp (-t * Z ω))) ∂μ := by
    apply MeasureTheory.lintegral_mono
    intro ω
    change ENNReal.ofReal ((t * |Z ω|) ^ (2 * m) / ((2 * m).factorial : ℝ))
      ≤ ENNReal.ofReal (Real.exp (t * Z ω)) + ENNReal.ofReal (Real.exp (-t * Z ω))
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (hpoint ω)
  have step2 : ∫⁻ ω, (ENNReal.ofReal (Real.exp (t * Z ω)) + ENNReal.ofReal (Real.exp (-t * Z ω))) ∂μ
      ≤ ENNReal.ofReal (2 * Real.exp (c * t ^ 2 / 2)) := by
    rw [MeasureTheory.lintegral_add_left hA]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint_pos t) (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint_neg t) (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
    have b1 : ENNReal.ofReal (∫ ω, Real.exp (t * Z ω) ∂μ) ≤ ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)) :=
      ENNReal.ofReal_le_ofReal (hbound_pos t)
    have b2 : ENNReal.ofReal (∫ ω, Real.exp (-t * Z ω) ∂μ) ≤ ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)) :=
      ENNReal.ofReal_le_ofReal (hbound_neg t)
    calc ENNReal.ofReal (∫ ω, Real.exp (t * Z ω) ∂μ) + ENNReal.ofReal (∫ ω, Real.exp (-t * Z ω) ∂μ)
        ≤ ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)) + ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)) := add_le_add b1 b2
      _ = ENNReal.ofReal (2 * Real.exp (c * t ^ 2 / 2)) := by
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
  have main_le : ∫⁻ ω, ENNReal.ofReal ((t * |Z ω|) ^ (2 * m) / ((2 * m).factorial : ℝ)) ∂μ
      ≤ ENNReal.ofReal (2 * Real.exp (c * t ^ 2 / 2)) := le_trans step1 step2
  have pull : ∫⁻ ω, ENNReal.ofReal ((t * |Z ω|) ^ (2 * m) / ((2 * m).factorial : ℝ)) ∂μ
      = ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ)) * ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * m)) ∂μ := by
    simp_rw [hfactor]
    rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ))) (fun ω => ENNReal.ofReal (|Z ω| ^ (2 * m))) ENNReal.ofReal_ne_top]
  have ha_pos : 0 < t ^ (2 * m) / ((2 * m).factorial : ℝ) :=
    div_pos (pow_pos ht_pos _) (by exact_mod_cast (Nat.factorial_pos (2 * m)))
  have hX_le : ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * m)) ∂μ
      ≤ (ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ)))⁻¹ * ENNReal.ofReal (2 * Real.exp (c * t ^ 2 / 2)) := by
    have hmain : ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ)) * (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * m)) ∂μ)
        ≤ ENNReal.ofReal (2 * Real.exp (c * t ^ 2 / 2)) := by
      rw [← pull]; exact main_le
    have ha_ne0 : ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr ha_pos).ne'
    have ha_netop : ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * m)) ∂μ
        = (ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ)))⁻¹ * (ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ)) * ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * m)) ∂μ) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel ha_ne0 ha_netop, one_mul]
      _ ≤ (ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ)))⁻¹ * ENNReal.ofReal (2 * Real.exp (c * t ^ 2 / 2)) := by
          exact mul_le_mul_left' hmain _
  have hfinal : (ENNReal.ofReal (t ^ (2 * m) / ((2 * m).factorial : ℝ)))⁻¹ * ENNReal.ofReal (2 * Real.exp (c * t ^ 2 / 2))
      ≤ ENNReal.ofReal ((Real.sqrt (2 * c * Real.exp 1) * Real.sqrt (2 * (m : ℝ))) ^ (2 * m)) := by
    have hcne : c ≠ 0 := ne_of_gt hc
    have hMpos : (0:ℝ) < 2 * (m:ℝ) := by
      have h1 : (1:ℝ) ≤ (m:ℝ) := hmR
      linarith
    have hMne : (2*(m:ℝ)) ≠ 0 := ne_of_gt hMpos
    have hct : c * t ^ 2 / 2 = (m:ℝ) := by
      rw [ht_sq]; field_simp
    have hexp : Real.exp (c * t ^ 2 / 2) = Real.exp 1 ^ m := by
      rw [hct, ← mul_one (m:ℝ), Real.exp_nat_mul]
    have hpow : t ^ (2*m) = (2*(m:ℝ)/c)^m := by
      rw [pow_mul, ht_sq]
    have hAinv : (t^(2*m))⁻¹ = (c/(2*(m:ℝ)))^m := by
      rw [hpow, ← inv_pow, inv_div]
    have hAinv2 : (t^(2*m) / ((2*m).factorial : ℝ))⁻¹ = ((2*m).factorial : ℝ) * (t^(2*m))⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    have heq : (t^(2*m) / ((2*m).factorial : ℝ))⁻¹ * (2 * Real.exp (c * t^2 / 2))
        = 2 * ((2*m).factorial : ℝ) * (c/(2*(m:ℝ)))^m * Real.exp 1^m := by
      rw [hAinv2, hAinv, hexp]; ring
    rw [← ENNReal.ofReal_inv_of_pos ha_pos, ← ENNReal.ofReal_mul (inv_nonneg.mpr ha_pos.le)]
    apply ENNReal.ofReal_le_ofReal
    rw [heq]
    have hfact_le : ((2*m).factorial : ℝ) ≤ (2*(m:ℝ))^(2*m) := by
      have h := Nat.factorial_le_pow (2*m)
      have h' : ((2*m).factorial : ℝ) ≤ ((2*m : ℕ) : ℝ)^(2*m) := by exact_mod_cast h
      calc ((2*m).factorial : ℝ) ≤ ((2*m : ℕ) : ℝ)^(2*m) := h'
        _ = (2*(m:ℝ))^(2*m) := by push_cast; ring
    have h2le : (2:ℝ) ≤ 2^m := by
      have h := Bound.pow_le_pow_right_of_le_one_or_one_le (a := (2:ℝ)) (n := 1) (m := m) (Or.inl ⟨by norm_num, hm⟩)
      simpa using h
    have hK : (Real.sqrt (2*c*Real.exp 1))^(2*m) = (2*c*Real.exp 1)^m := by
      rw [pow_mul, Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hc.le) (Real.exp_pos 1).le)]
    have hsqrtm : (Real.sqrt (2*(m:ℝ)))^(2*m) = (2*(m:ℝ))^m := by
      rw [pow_mul, Real.sq_sqrt (mul_nonneg (by norm_num) (Nat.cast_nonneg m))]
    have hXnn : (0:ℝ) ≤ (c/(2*(m:ℝ)))^m * (Real.exp 1)^m :=
      mul_nonneg (pow_nonneg (div_nonneg hc.le hMpos.le) m) (pow_nonneg (Real.exp_pos 1).le m)
    have hYnn : (0:ℝ) ≤ (2*(m:ℝ))^m * c^m * (Real.exp 1)^m :=
      mul_nonneg (mul_nonneg (pow_nonneg hMpos.le m) (pow_nonneg hc.le m)) (pow_nonneg (Real.exp_pos 1).le m)
    rw [mul_pow, hK, hsqrtm]
    calc 2 * ((2*m).factorial : ℝ) * (c/(2*(m:ℝ)))^m * Real.exp 1^m
        ≤ 2 * (2*(m:ℝ))^(2*m) * (c/(2*(m:ℝ)))^m * Real.exp 1^m := by
            nlinarith [hfact_le, hXnn]
      _ = 2 * (2*(m:ℝ))^m * c^m * Real.exp 1^m := by
            have hMMc : (2*(m:ℝ))^m * (c/(2*(m:ℝ)))^m = c^m := by
              rw [← mul_pow]
              congr 1
              field_simp
            have hM2 : (2*(m:ℝ))^(2*m) = (2*(m:ℝ))^m * (2*(m:ℝ))^m := by
              rw [Nat.two_mul, pow_add]
            have h1 : (2*(m:ℝ))^(2*m) * (c/(2*(m:ℝ)))^m = (2*(m:ℝ))^m * c^m := by
              rw [hM2, mul_assoc, hMMc]
            calc 2 * (2*(m:ℝ))^(2*m) * (c/(2*(m:ℝ)))^m * Real.exp 1^m
                = 2 * ((2*(m:ℝ))^(2*m) * (c/(2*(m:ℝ)))^m) * Real.exp 1^m := by ring
              _ = 2 * ((2*(m:ℝ))^m * c^m) * Real.exp 1^m := by rw [h1]
              _ = 2 * (2*(m:ℝ))^m * c^m * Real.exp 1^m := by ring
      _ ≤ 2^m * (2*(m:ℝ))^m * c^m * Real.exp 1^m := by
            nlinarith [h2le, hYnn]
      _ = (2*c*Real.exp 1)^m * (2*(m:ℝ))^m := by
            rw [mul_pow, mul_pow]; ring
  exact le_trans hX_le hfinal
  /- @proof-region region.target-node.session.a31af78d8d49a889 end -/

end Statlib.Imported

