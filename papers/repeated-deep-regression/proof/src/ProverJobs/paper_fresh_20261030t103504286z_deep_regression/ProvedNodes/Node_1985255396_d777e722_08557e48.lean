import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Lean
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Vocabulary
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Base

namespace PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1985255396_d777e722 : ∀ {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha) [IsProbabilityMeasure mu]
    (lambda_val M : ℝ) (hlambda : 0 < lambda_val) (hM : 0 ≤ M)
    (H : alpha → ℝ) (hH_meas : AEMeasurable H mu)
    (hH_bound : ∀ᵐ omega ∂mu, 0 ≤ H omega ∧ H omega ≤ M)
    (hTail : ∀ s : ℝ, 0 < s →
      mu {omega | H omega > s} ≤ ENNReal.ofReal (Real.exp (-(lambda_val * s)))),
    Integrable H mu ∧ ∫ omega, H omega ∂mu ≤ 6 / lambda_val := by
  /- @proof-region region.target-node.session.11726312d6481376 begin -/
  intro α _ mu _ lam M hlam hM H hH_meas hH_bound hTail
  have hH_nn : ∀ᵐ ω ∂mu, 0 ≤ H ω := hH_bound.mono fun ω h => h.1
  have hInt : Integrable H mu := by
    refine MeasureTheory.Integrable.of_bound hH_meas.aestronglyMeasurable M ?_
    filter_upwards [hH_bound] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  refine ⟨hInt, ?_⟩
  have hlayer : ∫⁻ ω, ENNReal.ofReal (H ω) ∂mu
      = ∫⁻ t in Set.Ioi (0:ℝ), mu {ω : α | t < H ω} :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt (f := H) mu hH_nn hH_meas
  have htail_le : ∫⁻ t in Set.Ioi (0:ℝ), mu {ω : α | t < H ω}
      ≤ ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(lam * t))) := by
    refine MeasureTheory.lintegral_mono (fun t => ?_)
    by_cases ht : 0 < t
    · exact hTail t ht
    · push_neg at ht
      have hexp : (1:ℝ) ≤ Real.exp (-(lam * t)) := by
        have h1 : lam * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.le ht
        have h2 : (0:ℝ) ≤ -(lam * t) := by linarith
        calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp (-(lam * t)) := Real.exp_le_exp.mpr h2
      calc mu {ω : α | t < H ω} ≤ mu Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
        _ = 1 := MeasureTheory.measure_univ
        _ = ENNReal.ofReal (1:ℝ) := (ENNReal.ofReal_one).symm
        _ ≤ ENNReal.ofReal (Real.exp (-(lam * t))) := ENNReal.ofReal_le_ofReal hexp
  have hexp_int : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(lam * t)))
      = ENNReal.ofReal (∫ t in Set.Ioi (0:ℝ), Real.exp (-(lam * t))) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (by simpa [IntegrableOn, neg_mul] using exp_neg_integrableOn_Ioi (0:ℝ) hlam)
      (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)).symm
  have hval : ∫ t in Set.Ioi (0:ℝ), Real.exp (-(lam * t)) = 1 / lam := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1:ℝ)) (r := lam) one_pos hlam
    simpa [Real.Gamma_one, Real.rpow_one, Real.rpow_zero] using h
  have hmain : ∫⁻ ω, ENNReal.ofReal (H ω) ∂mu ≤ ENNReal.ofReal (6 / lam) := by
    rw [hlayer]
    calc ∫⁻ t in Set.Ioi (0:ℝ), mu {ω : α | t < H ω}
        ≤ ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(lam * t))) := htail_le
      _ = ENNReal.ofReal (∫ t in Set.Ioi (0:ℝ), Real.exp (-(lam * t))) := hexp_int
      _ = ENNReal.ofReal (1 / lam) := by rw [hval]
      _ ≤ ENNReal.ofReal (6 / lam) := by
          apply ENNReal.ofReal_le_ofReal
          have h6 : (1:ℝ) ≤ 6 := by norm_num
          have hpos : (0:ℝ) ≤ lam⁻¹ := by positivity
          have hle := mul_le_mul_of_nonneg_right h6 hpos
          simpa [div_eq_mul_inv] using hle
  calc ∫ ω, H ω ∂mu
      = (∫⁻ ω, ENNReal.ofReal (H ω) ∂mu).toReal :=
        Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
          hH_nn hInt
    _ ≤ (ENNReal.ofReal (6 / lam)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = 6 / lam := ENNReal.toReal_ofReal (by positivity)
  /- @proof-region region.target-node.session.11726312d6481376 end -/

end Statlib.Imported
end

