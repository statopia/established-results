import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3748965445_c602f3c6 : ∀ (U : Type*) [MeasurableSpace U]
    (P : Measure U) [IsProbabilityMeasure P]
    (rho : ℕ → U → ℝ≥0∞) (s : U → ℝ) (sn : ℕ → U → ℝ) (E : U → ℝ)
    (hrho_meas : ∀ n : ℕ, Measurable (rho n))
    (hfn_meas : ∀ n : ℕ,
      AEMeasurable (fun u : U => Real.exp (-(sn n u))) (P.withDensity (rho n)))
    (hf_meas : ∀ n : ℕ,
      AEMeasurable (fun u : U => Real.exp (-(s u))) (P.withDensity (rho n)))
    (hE_nonneg : ∀ u : U, 0 ≤ E u)
    (hE_meas : ∀ n : ℕ, AEMeasurable E (P.withDensity (rho n)))
    (hE_int : ∀ n : ℕ, Integrable E (P.withDensity (rho n)))
    (hmaj : ∀ n : ℕ, ∀ᵐ u ∂(P.withDensity (rho n)),
      Real.exp (-(sn n u)) ≤ E u ∧ Real.exp (-(s u)) ≤ E u)
    (hmaj_int : ∀ n : ℕ, Integrable
      (fun u : U => (sn n u - s u) ^ 2 * E u) (P.withDensity (rho n)))
    (hlim : Tendsto
      (fun n : ℕ => ∫ u : U, (sn n u - s u) ^ 2 * E u ∂(P.withDensity (rho n)))
      Filter.atTop (𝓝 0)),
    Tendsto (fun n : ℕ => ∫ u : U,
      (Real.sqrt (Real.exp (-(sn n u))) - Real.sqrt (Real.exp (-(s u)))) ^ 2
      ∂(P.withDensity (rho n))) Filter.atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.9e655c49e835e26c begin -/
  classical
  intro U instU P instP rho s sn E hrho_meas hfn_meas hf_meas hE_nonneg hE_meas hE_int hmaj hmaj_int
    hlim
  have hstep : ∀ x y c : ℝ, Real.exp (-x) ≤ c → Real.exp (-y) ≤ c → 0 ≤ c →
      (Real.exp (-x / 2) - Real.exp (-y / 2)) ^ 2 ≤ (x - y) ^ 2 * c := by
    intro x y c hx hy hc
    rcases le_total x y with hxy | hyx
    · have h1 : 1 - Real.exp (-((y - x) / 2)) ≤ (y - x) / 2 := by
        have h := Real.add_one_le_exp (-((y - x) / 2))
        linarith
      have hfac : Real.exp (-y / 2) = Real.exp (-x / 2) * Real.exp (-((y - x) / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hbd : Real.exp (-x / 2) - Real.exp (-y / 2)
          ≤ Real.exp (-x / 2) * ((y - x) / 2) := by
        rw [hfac]
        nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos (-x / 2)))]
      have hnn : 0 ≤ Real.exp (-x / 2) - Real.exp (-y / 2) := by
        linarith [Real.exp_le_exp.2 (by linarith : -y / 2 ≤ -x / 2)]
      have hsq : (Real.exp (-x / 2) - Real.exp (-y / 2)) ^ 2
          ≤ (Real.exp (-x / 2) * ((y - x) / 2)) ^ 2 := by
        have h2 := mul_le_mul hbd hbd hnn (le_trans hnn hbd)
        simpa [pow_two] using h2
      have hp2 : (Real.exp (-x / 2)) ^ 2 = Real.exp (-x) := by
        rw [pow_two, ← Real.exp_add, show -x / 2 + -x / 2 = -x by ring]
      have ht2 : ((y - x) / 2) ^ 2 ≤ (x - y) ^ 2 := by
        nlinarith [sq_nonneg (x - y)]
      have hprod : (Real.exp (-x / 2) * ((y - x) / 2)) ^ 2 ≤ (x - y) ^ 2 * c := by
        rw [mul_pow, hp2]
        calc Real.exp (-x) * ((y - x) / 2) ^ 2 ≤ c * (x - y) ^ 2 :=
              mul_le_mul hx ht2 (sq_nonneg _) hc
          _ = (x - y) ^ 2 * c := by ring
      linarith
    · have h1 : 1 - Real.exp (-((x - y) / 2)) ≤ (x - y) / 2 := by
        have h := Real.add_one_le_exp (-((x - y) / 2))
        linarith
      have hfac : Real.exp (-x / 2) = Real.exp (-y / 2) * Real.exp (-((x - y) / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hbd : Real.exp (-y / 2) - Real.exp (-x / 2)
          ≤ Real.exp (-y / 2) * ((x - y) / 2) := by
        rw [hfac]
        nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos (-y / 2)))]
      have hnn : 0 ≤ Real.exp (-y / 2) - Real.exp (-x / 2) := by
        linarith [Real.exp_le_exp.2 (by linarith : -x / 2 ≤ -y / 2)]
      have hsq : (Real.exp (-y / 2) - Real.exp (-x / 2)) ^ 2
          ≤ (Real.exp (-y / 2) * ((x - y) / 2)) ^ 2 := by
        have h2 := mul_le_mul hbd hbd hnn (le_trans hnn hbd)
        simpa [pow_two] using h2
      have hp2 : (Real.exp (-y / 2)) ^ 2 = Real.exp (-y) := by
        rw [pow_two, ← Real.exp_add, show -y / 2 + -y / 2 = -y by ring]
      have ht2 : ((x - y) / 2) ^ 2 ≤ (x - y) ^ 2 := by
        nlinarith [sq_nonneg (x - y)]
      have hprod : (Real.exp (-y / 2) * ((x - y) / 2)) ^ 2 ≤ (x - y) ^ 2 * c := by
        rw [mul_pow, hp2]
        calc Real.exp (-y) * ((x - y) / 2) ^ 2 ≤ c * (x - y) ^ 2 :=
              mul_le_mul hy ht2 (sq_nonneg _) hc
          _ = (x - y) ^ 2 * c := by ring
      have hsym : (Real.exp (-x / 2) - Real.exp (-y / 2)) ^ 2
          = (Real.exp (-y / 2) - Real.exp (-x / 2)) ^ 2 := by ring
      rw [hsym]
      linarith
  have hdom : ∀ n : ℕ, ∀ᵐ u ∂(P.withDensity (rho n)),
      (Real.sqrt (Real.exp (-(sn n u))) - Real.sqrt (Real.exp (-(s u)))) ^ 2
        ≤ (sn n u - s u) ^ 2 * E u := by
    intro n
    filter_upwards [hmaj n] with u hu
    have hs1 : Real.sqrt (Real.exp (-(sn n u))) = Real.exp (-(sn n u) / 2) := by
      have hsq : Real.exp (-(sn n u)) = (Real.exp (-(sn n u) / 2)) ^ 2 := by
        rw [pow_two, ← Real.exp_add,
          show -(sn n u) / 2 + -(sn n u) / 2 = -(sn n u) by ring]
      rw [hsq, Real.sqrt_sq (le_of_lt (Real.exp_pos (-(sn n u) / 2)))]
    have hs2 : Real.sqrt (Real.exp (-(s u))) = Real.exp (-(s u) / 2) := by
      have hsq : Real.exp (-(s u)) = (Real.exp (-(s u) / 2)) ^ 2 := by
        rw [pow_two, ← Real.exp_add, show -(s u) / 2 + -(s u) / 2 = -(s u) by ring]
      rw [hsq, Real.sqrt_sq (le_of_lt (Real.exp_pos (-(s u) / 2)))]
    rw [hs1, hs2]
    exact hstep (sn n u) (s u) (E u) hu.1 hu.2 (hE_nonneg u)
  have hmono : ∀ n : ℕ, (∫ u : U,
      (Real.sqrt (Real.exp (-(sn n u))) - Real.sqrt (Real.exp (-(s u)))) ^ 2
        ∂(P.withDensity (rho n)))
      ≤ ∫ u : U, (sn n u - s u) ^ 2 * E u ∂(P.withDensity (rho n)) := by
    intro n
    by_cases hint : Integrable (fun u : U =>
        (Real.sqrt (Real.exp (-(sn n u))) - Real.sqrt (Real.exp (-(s u)))) ^ 2)
        (P.withDensity (rho n))
    · exact integral_mono_ae hint (hmaj_int n) (hdom n)
    · rw [MeasureTheory.integral_undef hint]
      exact integral_nonneg (fun u : U => mul_nonneg (sq_nonneg _) (hE_nonneg u))
  have hnn : ∀ n : ℕ, 0 ≤ (∫ u : U,
      (Real.sqrt (Real.exp (-(sn n u))) - Real.sqrt (Real.exp (-(s u)))) ^ 2
        ∂(P.withDensity (rho n))) := by
    intro n
    exact integral_nonneg (fun u => sq_nonneg _)
  refine squeeze_zero_norm (fun n => ?_) hlim
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn n)]
  exact hmono n

  /- @proof-region region.target-node.session.9e655c49e835e26c end -/

end Statlib.Imported
end

