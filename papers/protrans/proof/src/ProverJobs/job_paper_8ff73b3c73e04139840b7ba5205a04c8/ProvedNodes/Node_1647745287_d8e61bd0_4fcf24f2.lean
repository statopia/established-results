import Lean
import ProverJobs.job_paper_8ff73b3c73e04139840b7ba5205a04c8.Vocabulary
import ProverJobs.job_paper_8ff73b3c73e04139840b7ba5205a04c8.Base
import ProverJobs.job_paper_8ff73b3c73e04139840b7ba5205a04c8.ExternalNodes.Node_8d0d0baf9ab4437481f0

namespace PaperProofTasks.job_paper_8ff73b3c73e04139840b7ba5205a04c8

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open _root_.PaperProofTasks.job_paper_8ff73b3c73e04139840b7ba5205a04c8.Statlib.Imported
universe u

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_1647745287_d8e61bd0 : ∀ (b : ℝ) (hb : 0 < b)
    (hBern : ∀ (N' : ℕ), 1 ≤ N' → ∀ (V' : ℝ), 0 < V' →
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
        (U' : Fin N' → Ω' → ℝ),
        (∀ l, Measurable (U' l)) → iIndepFun U' μ' → (∀ l, Integrable (U' l) μ') →
        (∀ l, ∫ ω, U' l ω ∂μ' = 0) →
        (∀ (r : ℕ), 2 ≤ r → ∀ l,
          ∫⁻ ω, ENNReal.ofReal (|U' l ω| ^ r) ∂μ'
            ≤ ENNReal.ofReal ((r.factorial : ℝ) * V' ^ r)) →
        ∀ t : ℝ, 0 < t →
          μ'.real {ω | t < |(N' : ℝ)⁻¹ * ∑ l, U' l ω|} ≤
            2 * Real.exp (-(b * (N' : ℝ) * min (t ^ 2 / V' ^ 2) (t / V'))))
    (V : ℝ) (hV : 0 < V) (delta : ℝ) (hdelta : 0 < delta)
    (C : ℝ) (hC : 0 < C) (hC_sq : C ^ 2 = V ^ 2 * delta / b)
    (N0 : ℝ) (hN0 : 0 < N0) (hN0_ge : delta / b ≤ N0)
    (p : ℕ) (hp : 2 ≤ p) (N : ℕ) (hN : 1 ≤ N)
    (hN_log : N0 * Real.log (p : ℝ) ≤ (N : ℝ))
    (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Fin N → Ω → ℝ)
    (hU_meas : ∀ l, Measurable (U l))
    (hU_indep : iIndepFun U μ)
    (hU_int : ∀ l, Integrable (U l) μ)
    (hU_center : ∀ l, ∫ ω, U l ω ∂μ = 0)
    (hU_moment : ∀ (r : ℕ), 2 ≤ r → ∀ l,
      ∫⁻ ω, ENNReal.ofReal (|U l ω| ^ r) ∂μ
        ≤ ENNReal.ofReal ((r.factorial : ℝ) * V ^ r)),
    μ {ω | C * Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) < |(N : ℝ)⁻¹ * ∑ l, U l ω|}
      ≤ ENNReal.ofReal (2 * Real.rpow (p : ℝ) (-delta)) := by
  /- @proof-region region.target-node.session.ec5b51b013dc9bcc begin -/
  intro b hb hBern V hV delta hdelta C hC hCeq N0 hN0 hN0ge p hp N hN hNlog Ω hΩ μ hμ U
    hU_meas hU_indep hU_int hU_center hU_moment
  set t : ℝ := C * Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) with ht_def
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hq : 0 < Real.log (p : ℝ) / (N : ℝ) := div_pos hlogp hNpos
  have ht : 0 < t := by
    rw [ht_def]
    exact mul_pos hC (Real.sqrt_pos.2 hq)
  have hbne : b ≠ 0 := ne_of_gt hb
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hVne : V ≠ 0 := ne_of_gt hV
  have hN0ne : N0 ≠ 0 := ne_of_gt hN0
  have hbern := hBern N hN V hV Ω μ U hU_meas hU_indep hU_int hU_center hU_moment t ht
  have ht_sq : t ^ 2 = C ^ 2 * (Real.log (p : ℝ) / (N : ℝ)) := by
    rw [ht_def, mul_pow, Real.sq_sqrt (le_of_lt hq)]
  have hsq : t ^ 2 / V ^ 2 = (delta / b) * (Real.log (p : ℝ) / (N : ℝ)) := by
    rw [ht_sq, hCeq]
    field_simp [hbne, hNne, hVne]
  have hratio : Real.log (p : ℝ) / (N : ℝ) ≤ 1 / N0 := by
    have h2 : Real.log (p : ℝ) ≤ (N : ℝ) / N0 := by
      rw [le_div_iff₀ hN0]
      linarith [hNlog]
    have h3 : (N : ℝ) / N0 = (1 / N0) * (N : ℝ) := by
      field_simp
    rw [div_le_iff₀ hNpos, ← h3]
    exact h2
  have hdb : (0 : ℝ) ≤ delta / b := le_of_lt (div_pos hdelta hb)
  have h2' : (delta / b) * (1 / N0) ≤ 1 := by
    have h3 : (delta / b) * (1 / N0) ≤ N0 * (1 / N0) :=
      mul_le_mul_of_nonneg_right hN0ge (by positivity)
    have h4 : N0 * (1 / N0) = 1 := mul_one_div_cancel hN0ne
    linarith
  have hsq1 : t ^ 2 / V ^ 2 ≤ 1 := by
    refine le_trans ?_ h2'
    rw [hsq]
    exact mul_le_mul_of_nonneg_left hratio hdb
  have htV_pos : 0 < t / V := div_pos ht hV
  have htV_le : t / V ≤ 1 := by
    have h : (t / V) ^ 2 ≤ 1 := by
      rw [div_pow]
      exact hsq1
    nlinarith [htV_pos]
  have hmin : min (t ^ 2 / V ^ 2) (t / V) = t ^ 2 / V ^ 2 := by
    have h : t ^ 2 / V ^ 2 ≤ t / V := by
      have hsq2 : t ^ 2 / V ^ 2 = (t / V) ^ 2 := by rw [div_pow]
      nlinarith [htV_pos, htV_le]
    exact min_eq_left h
  have hexp_arg : b * (N : ℝ) * (t ^ 2 / V ^ 2) = delta * Real.log (p : ℝ) := by
    rw [hsq]
    field_simp [hbne, hNne]
  have hrpow_eq : Real.rpow (p : ℝ) (-delta) =
      Real.exp (-(delta * Real.log (p : ℝ))) := by
    have h := Real.rpow_def_of_pos hp0 (-delta)
    rw [show Real.rpow (p : ℝ) (-delta) = (p : ℝ) ^ (-delta) from rfl, h]
    congr 1
    ring
  have hexp : 2 * Real.exp (-(b * (N : ℝ) * min (t ^ 2 / V ^ 2) (t / V))) =
      2 * Real.rpow (p : ℝ) (-delta) := by
    rw [hmin, hexp_arg, hrpow_eq]
  have hbern' : μ.real {ω | t < |(N : ℝ)⁻¹ * ∑ l : Fin N, U l ω|} ≤
      2 * Real.rpow (p : ℝ) (-delta) := hbern.trans (le_of_eq hexp)
  have hμne : μ {ω | t < |(N : ℝ)⁻¹ * ∑ l : Fin N, U l ω|} ≠ ⊤ := measure_ne_top μ _
  have hreal : (μ {ω | t < |(N : ℝ)⁻¹ * ∑ l : Fin N, U l ω|}).toReal ≤
      2 * Real.rpow (p : ℝ) (-delta) := hbern'
  have hRpos : 0 < 2 * Real.rpow (p : ℝ) (-delta) := by
    rw [hrpow_eq]
    have hpos := Real.exp_pos (-(delta * Real.log (p : ℝ)))
    linarith
  refine (ENNReal.le_ofReal_iff_toReal_le (b := 2 * Real.rpow (p : ℝ) (-delta))
    hμne (le_of_lt hRpos)).mpr hreal
  /- @proof-region region.target-node.session.ec5b51b013dc9bcc end -/

end Statlib.Imported

