import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_a8791fa1d3e4fe57b534

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
theorem statopia_math_node_2318467292_e95fa886 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (Kt L : ℝ)
    (hKt : 0 < Kt) (hX_meas : Measurable X)
    (hX_int : Integrable X μ)
    (hX_sq_int : Integrable (fun ω => (X ω) ^ 2) μ)
    (hX_mean : ∫ ω, X ω ∂μ = 0)
    (hX_var : ∫ ω, (X ω) ^ 2 ∂μ = 1)
    (hX_tail : ∀ t : ℝ, 0 < t →
      μ {ω | t < |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (hL : (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 ≤ L),
    (|∫ ω, X ω * (if |X ω| ≤ L then (1 : ℝ) else 0) ∂μ| ≤ 1) ∧
      ((1 / 2 : ℝ) ≤ Real.sqrt
        (∫ ω, (X ω * (if |X ω| ≤ L then (1 : ℝ) else 0) -
            ∫ ω, X ω * (if |X ω| ≤ L then (1 : ℝ) else 0) ∂μ) ^ 2 ∂μ)) := by
  /- @proof-region region.target-node.session.7fa47db8629aa405 begin -/
  intro Ω hΩ μ hμ X Kt L hKt hX_meas hX_int hX_sq_int hX_mean hX_var hX_tail hL
  letI : MeasurableSpace Ω := hΩ
  letI : IsProbabilityMeasure μ := hμ
  classical
  have hS_meas : MeasurableSet {ω : Ω | |X ω| ≤ L} :=
    measurableSet_le hX_meas.abs measurable_const
  set Y : Ω → ℝ := fun ω => X ω * (if |X ω| ≤ L then (1 : ℝ) else 0) with hY_def
  set Z : Ω → ℝ := fun ω => X ω * (if |X ω| ≤ L then (0 : ℝ) else 1) with hZ_def
  set W : Ω → ℝ := fun ω => (X ω) ^ 2 * (if |X ω| ≤ L then (0 : ℝ) else 1) with hW_def
  have hY_meas : Measurable Y := by
    rw [hY_def]
    exact hX_meas.mul
      (Measurable.ite (p := {ω : Ω | |X ω| ≤ L}) hS_meas measurable_const measurable_const)
  have hZ_meas : Measurable Z := by
    rw [hZ_def]
    exact hX_meas.mul
      (Measurable.ite (p := {ω : Ω | |X ω| ≤ L}) hS_meas measurable_const measurable_const)
  have hW_meas : Measurable W := by
    rw [hW_def]
    have hXs : Measurable (fun ω : Ω => (X ω) ^ 2) := by
      simpa [sq] using hX_meas.mul hX_meas
    exact hXs.mul
      (Measurable.ite (p := {ω : Ω | |X ω| ≤ L}) hS_meas measurable_const measurable_const)
  have hY2_meas : Measurable (fun ω : Ω => (Y ω) ^ 2) := by
    simpa [sq] using hY_meas.mul hY_meas
  have hZ2_meas : Measurable (fun ω : Ω => (Z ω) ^ 2) := by
    simpa [sq] using hZ_meas.mul hZ_meas
  have hXY : ∀ ω, X ω = Y ω + Z ω := by
    intro ω
    rw [hY_def, hZ_def]
    by_cases h : |X ω| ≤ L <;> simp [h] <;> ring
  have hX2 : ∀ ω, (X ω) ^ 2 = (Y ω) ^ 2 + W ω := by
    intro ω
    rw [hY_def, hW_def]
    by_cases h : |X ω| ≤ L <;> simp [h] <;> ring
  have hWZ : ∀ ω, W ω = (Z ω) ^ 2 := by
    intro ω
    rw [hW_def, hZ_def]
    by_cases h : |X ω| ≤ L <;> simp [h] <;> ring
  have hYabs : ∀ ω, |Y ω| ≤ |X ω| := by
    intro ω
    rw [hY_def]
    by_cases h : |X ω| ≤ L <;> simp [h]
  have hZabs : ∀ ω, |Z ω| ≤ |X ω| := by
    intro ω
    rw [hZ_def]
    by_cases h : |X ω| ≤ L <;> simp [h]
  have hX_abs_int : Integrable (fun ω => |X ω|) μ := by
    simpa [Real.norm_eq_abs] using hX_int.abs
  have hY_int : Integrable Y μ := by
    refine Integrable.mono hX_abs_int hY_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    simpa [Real.norm_eq_abs] using hYabs ω
  have hZ_int : Integrable Z μ := by
    refine Integrable.mono hX_abs_int hZ_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    simpa [Real.norm_eq_abs] using hZabs ω
  have hY2_int : Integrable (fun ω => (Y ω) ^ 2) μ := by
    refine Integrable.mono hX_sq_int hY2_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    have hb : (Y ω) ^ 2 ≤ (X ω) ^ 2 := by
      have h1 := hYabs ω
      nlinarith [h1, abs_nonneg (Y ω), abs_nonneg (X ω), sq_abs (Y ω), sq_abs (X ω)]
    have hL : ‖(Y ω) ^ 2‖ = (Y ω) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y ω))]
    have hR : ‖(X ω) ^ 2‖ = (X ω) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω))]
    linarith [hb, hL, hR]
  have hZ2_int : Integrable (fun ω => (Z ω) ^ 2) μ := by
    refine Integrable.mono hX_sq_int hZ2_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    have hb : (Z ω) ^ 2 ≤ (X ω) ^ 2 := by
      have hZp : Z ω = X ω * (if |X ω| ≤ L then (0 : ℝ) else 1) := by simp [hZ_def]
      rw [hZp]
      by_cases h : |X ω| ≤ L
      · rw [if_pos h]
        nlinarith [sq_nonneg (X ω)]
      · rw [if_neg h]
        nlinarith [sq_nonneg (X ω)]
    have hL : ‖(Z ω) ^ 2‖ = (Z ω) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Z ω))]
    have hR : ‖(X ω) ^ 2‖ = (X ω) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω))]
    linarith [hb, hL, hR]
  have hW_int : Integrable W μ := by
    refine Integrable.mono hX_sq_int hW_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    have hnn : 0 ≤ W ω := by
      have hWp : W ω = (X ω) ^ 2 * (if |X ω| ≤ L then (0 : ℝ) else 1) := by simp [hW_def]
      rw [hWp]
      by_cases h : |X ω| ≤ L
      · rw [if_pos h]
        simp
      · rw [if_neg h]
        positivity
    have hb : W ω ≤ (X ω) ^ 2 := by
      have hWp : W ω = (X ω) ^ 2 * (if |X ω| ≤ L then (0 : ℝ) else 1) := by simp [hW_def]
      rw [hWp]
      by_cases h : |X ω| ≤ L
      · rw [if_pos h]
        nlinarith [sq_nonneg (X ω)]
      · rw [if_neg h]
        nlinarith [sq_nonneg (X ω)]
    have hL : ‖W ω‖ = W ω := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hR : ‖(X ω) ^ 2‖ = (X ω) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω))]
    linarith [hb, hL, hR]
  have hX_split : ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂μ + ∫ ω, Z ω ∂μ := by
    rw [← integral_add hY_int hZ_int]
    apply integral_congr_ae
    filter_upwards with ω
    exact hXY ω
  have hX2_split : ∫ ω, (X ω) ^ 2 ∂μ = ∫ ω, (Y ω) ^ 2 ∂μ + ∫ ω, W ω ∂μ := by
    rw [← integral_add hY2_int hW_int]
    apply integral_congr_ae
    filter_upwards with ω
    exact hX2 ω
  have hY_eq : ∫ ω, Y ω ∂μ = -(∫ ω, Z ω ∂μ) := by linarith [hX_split, hX_mean]
  have hY2_eq : ∫ ω, (Y ω) ^ 2 ∂μ = 1 - ∫ ω, W ω ∂μ := by
    linarith [hX2_split, hX_var]
  have hW_nonneg : 0 ≤ ∫ ω, W ω ∂μ := by
    have hnn : ∀ ω, 0 ≤ W ω := by
      intro ω
      have hWp : W ω = (X ω) ^ 2 * (if |X ω| ≤ L then (0 : ℝ) else 1) := by simp [hW_def]
      rw [hWp]
      by_cases h : |X ω| ≤ L
      · rw [if_pos h]
        simp
      · rw [if_neg h]
        positivity
    exact integral_nonneg hnn

  have key : ∀ (u : Ω → ℝ), Integrable u μ → Integrable (fun ω => (u ω) ^ 2) μ →
      ∫ ω, (u ω - ∫ ω, u ω ∂μ) ^ 2 ∂μ = (∫ ω, (u ω) ^ 2 ∂μ) - (∫ ω, u ω ∂μ) ^ 2 := by
    intro u hu hu2
    have h1 : ∫ ω, (u ω - ∫ ω, u ω ∂μ) ^ 2 ∂μ
        = ∫ ω, ((u ω) ^ 2 - 2 * (∫ ω, u ω ∂μ) * u ω + (∫ ω, u ω ∂μ) * (∫ ω, u ω ∂μ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      ring
    have hA : Integrable (fun ω => (u ω) ^ 2 - 2 * (∫ ω, u ω ∂μ) * u ω) μ :=
      hu2.sub (hu.const_mul (2 * (∫ ω, u ω ∂μ)))
    have hB : Integrable (fun _ : Ω => (∫ ω, u ω ∂μ) * (∫ ω, u ω ∂μ)) μ := integrable_const _
    rw [h1, integral_add hA hB, integral_sub hu2 (hu.const_mul (2 * (∫ ω, u ω ∂μ))),
      integral_const_mul]
    have hc : ∫ ω, (∫ ω, u ω ∂μ) * (∫ ω, u ω ∂μ) ∂μ
        = (∫ ω, u ω ∂μ) * (∫ ω, u ω ∂μ) := by
      simp [integral_const]
    rw [hc]
    ring
  have hvar : ∫ ω, (Y ω - ∫ ω, Y ω ∂μ) ^ 2 ∂μ
      = (∫ ω, (Y ω) ^ 2 ∂μ) - (∫ ω, Y ω ∂μ) ^ 2 := key Y hY_int hY2_int
  have hZW : ∫ ω, (Z ω) ^ 2 ∂μ = ∫ ω, W ω ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    exact (hWZ ω).symm
  have hcsZ : (∫ ω, Z ω ∂μ) ^ 2 ≤ ∫ ω, (Z ω) ^ 2 ∂μ := by
    have hz := key Z hZ_int hZ2_int
    have h0 : 0 ≤ ∫ ω, (Z ω - ∫ ω, Z ω ∂μ) ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg (Z ω - ∫ ω, Z ω ∂μ))
    linarith
  have hLpos : (0 : ℝ) < L := by
    have h1 : (0 : ℝ) < (Kt + 1) ^ 4 := by positivity
    nlinarith [hL, h1]
  have htail_bound : ∫ ω, (X ω) ^ 2 * (if |X ω| ≤ L then (0 : ℝ) else 1) ∂μ
      ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) :=
    (statopia_math_node_895243969_77380b6a μ X Kt L hKt hLpos hX_meas hX_int hX_mean
      hX_sq_int hX_var hX_tail hY_int hW_int).2
  have hnum : (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) ≤ 1 / 4 := by
    have hKt1 : (0 : ℝ) < (Kt + 1) ^ 4 := by positivity
    have hKtL : Kt ≤ L := by
      have h2 : Kt ≤ (Kt + 1) ^ 4 := by
        nlinarith [hKt, sq_nonneg Kt, sq_nonneg (Kt + 1)]
      linarith [hL, hKt1, h2]
    set x : ℝ := L / Kt with hx_def
    have hxpos : 0 < x := by
      rw [hx_def]
      exact div_pos hLpos hKt
    have hxKt : x * Kt = L := by
      rw [hx_def]
      exact div_mul_cancel₀ L (ne_of_gt hKt)
    have hx1 : 1 ≤ x := by
      rw [hx_def, one_le_div hKt]
      exact hKtL
    have hexp3 : x ^ 3 * Real.exp (-x) ≤ 6 := by
      have hp := Real.pow_div_factorial_le_exp x (le_of_lt hxpos) 3
      have h3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
      rw [h3] at hp
      have hEpos : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hp (le_of_lt hEpos)
      have hone : Real.exp x * Real.exp (-x) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [hone] at hmul
      nlinarith [hmul]
    have h240 : 240 * Kt ^ 3 ≤ L := by
      have h2 : 240 * Kt ^ 3 ≤ 240 * (Kt + 1) ^ 4 := by
        nlinarith [hKt, sq_nonneg Kt, sq_nonneg (Kt + 1)]
      have h3 : 240 * (Kt + 1) ^ 4 ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 := by linarith [hKt1]
      linarith [hL, h2, h3]
    have hpoly : 2 * L ^ 2 + 4 * Kt * (L + Kt) ≤ 10 * L ^ 2 := by
      nlinarith [hKtL, hLpos]
    have hEL3 : Real.exp (-x) * L ^ 3 ≤ 6 * Kt ^ 3 := by
      have hx3 : x ^ 3 * Kt ^ 3 = L ^ 3 := by
        rw [← mul_pow, hxKt]
      have hle := mul_le_mul_of_nonneg_left hexp3 (show (0 : ℝ) ≤ Kt ^ 3 by positivity)
      rw [← hx3]
      calc Real.exp (-x) * (x ^ 3 * Kt ^ 3)
          = Kt ^ 3 * (x ^ 3 * Real.exp (-x)) := by ring
        _ ≤ Kt ^ 3 * 6 := hle
        _ = 6 * Kt ^ 3 := by ring
    have key : (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-x) * L ≤ 60 * Kt ^ 3 := by
      have hEL : (0 : ℝ) ≤ Real.exp (-x) * L := by positivity
      have h1 : (2 * L ^ 2 + 4 * Kt * (L + Kt)) * (Real.exp (-x) * L)
          ≤ 10 * L ^ 2 * (Real.exp (-x) * L) :=
        mul_le_mul_of_nonneg_right hpoly hEL
      have h2 : 10 * L ^ 2 * (Real.exp (-x) * L) ≤ 10 * (Real.exp (-x) * L ^ 3) := by
        have hEq : 10 * L ^ 2 * (Real.exp (-x) * L) = 10 * (Real.exp (-x) * L ^ 3) := by ring
        exact le_of_eq hEq
      have h3 : 10 * (Real.exp (-x) * L ^ 3) ≤ 10 * (6 * Kt ^ 3) :=
        mul_le_mul_of_nonneg_left hEL3 (by norm_num : (0 : ℝ) ≤ 10)
      rw [mul_assoc]
      calc (2 * L ^ 2 + 4 * Kt * (L + Kt)) * (Real.exp (-x) * L)
          ≤ 10 * L ^ 2 * (Real.exp (-x) * L) := h1
        _ ≤ 10 * (Real.exp (-x) * L ^ 3) := h2
        _ ≤ 10 * (6 * Kt ^ 3) := h3
        _ = 60 * Kt ^ 3 := by ring
    have h4 : 60 * Kt ^ 3 ≤ (1 / 4) * L := by linarith [h240]
    have h5 : (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-x) * L ≤ (1 / 4) * L :=
      le_trans key h4
    have hstep : (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) ≤ 1 / 4 := by
      by_contra hcon
      push_neg at hcon
      have hlt := mul_lt_mul_of_pos_right hcon hLpos
      have hxE : Real.exp (-x) = Real.exp (-L / Kt) := by
        have harg : -x = -L / Kt := by
          rw [hx_def]
          ring
        rw [harg]
      rw [← hxE] at hlt
      linarith [h5, hlt]
    exact hstep
  have hWle : ∫ ω, W ω ∂μ ≤ 1 / 4 := by
    have h1 : ∫ ω, W ω ∂μ ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) := by
      simpa only [hW_def] using htail_bound
    linarith [h1, hnum]
  have hcs1 : (∫ ω, Y ω ∂μ) ^ 2 ≤ ∫ ω, W ω ∂μ := by
    have hsq : (-(∫ ω, Z ω ∂μ)) ^ 2 = (∫ ω, Z ω ∂μ) ^ 2 := by ring
    rw [hY_eq, hsq, ← hZW]
    exact hcsZ
  have hInt1 : |∫ ω, Y ω ∂μ| ≤ 1 := by
    have hsq1 : (∫ ω, Y ω ∂μ) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      have h4 : (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
      linarith [hcs1, hWle]
    calc |∫ ω, Y ω ∂μ| = Real.sqrt ((∫ ω, Y ω ∂μ) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt ((1 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq1
      _ = 1 / 2 := by rw [Real.sqrt_sq_eq_abs]; norm_num
      _ ≤ 1 := by norm_num
  have hInt2 : (1 / 2 : ℝ) ≤ Real.sqrt (∫ ω, (Y ω - ∫ ω, Y ω ∂μ) ^ 2 ∂μ) := by
    have hge : (1 / 2 : ℝ) ≤ ∫ ω, (Y ω - ∫ ω, Y ω ∂μ) ^ 2 ∂μ := by
      linarith [hvar, hY2_eq, hcs1, hWle]
    have hsq2 : (1 / 2 : ℝ) ^ 2 ≤ ∫ ω, (Y ω - ∫ ω, Y ω ∂μ) ^ 2 ∂μ := by linarith
    calc (1 / 2 : ℝ) = Real.sqrt ((1 / 2 : ℝ) ^ 2) := by rw [Real.sqrt_sq_eq_abs]; norm_num
      _ ≤ Real.sqrt (∫ ω, (Y ω - ∫ ω, Y ω ∂μ) ^ 2 ∂μ) := Real.sqrt_le_sqrt hsq2
  exact ⟨hInt1, hInt2⟩



  /- @proof-region region.target-node.session.7fa47db8629aa405 end -/

end Statlib.Imported

