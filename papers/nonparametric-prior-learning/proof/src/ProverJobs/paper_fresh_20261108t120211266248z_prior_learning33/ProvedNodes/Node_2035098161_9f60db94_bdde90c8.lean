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
theorem statopia_math_node_2035098161_9f60db94 : ∀ (U : Type*) [MeasurableSpace U]
    (P : Measure U) [IsProbabilityMeasure P]
    (Pn : ℕ → Measure U) (rho : ℕ → U → ℝ≥0∞)
    (hrho_meas : ∀ n : ℕ, Measurable (rho n))
    (hrho_dens : ∀ n : ℕ, Pn n = P.withDensity (rho n))
    (Bbar : ℝ) (hBbar : 0 ≤ Bbar)
    (hrho_bound : ∀ n : ℕ, ∫⁻ u : U, (rho n u) ^ 2 ∂P ≤ ENNReal.ofReal Bbar)
    (F : ℕ → U → ℝ)
    (hF_int : ∀ n : ℕ, Integrable (F n) P)
    (hF_sqrt_int : ∀ n : ℕ, Integrable (fun u : U => Real.sqrt (F n u)) P)
    (hF_nonneg : ∀ (n : ℕ) (u : U), 0 ≤ F n u)
    (hF_tendsto : Filter.Tendsto (fun n : ℕ => ∫ u : U, F n u ∂P) Filter.atTop (nhds 0)),
    Filter.Tendsto (fun n : ℕ => ∫ u : U, Real.sqrt (F n u) ∂Pn n) Filter.atTop (nhds 0) := by
  /- @proof-region region.target-node.session.ce7d4ef8fa14bb90 begin -/
  intro U _ P _ Pn rho hrho_meas hrho_dens Bbar hBbar hrho_bound F hF_int hF_sqrt_int hF_nonneg hF_tendsto
  have hlt : ∀ n : ℕ, ∀ᵐ u : U ∂P, rho n u < ⊤ := by
    intro n
    have hfin : ∫⁻ u : U, rho n u * rho n u ∂P ≠ ⊤ := by
      have h := lt_of_le_of_lt (hrho_bound n) ENNReal.ofReal_lt_top
      simpa [pow_two] using h.ne
    have hsq : ∀ᵐ u : U ∂P, rho n u * rho n u < ⊤ :=
      MeasureTheory.ae_lt_top ((hrho_meas n).mul (hrho_meas n)) hfin
    filter_upwards [hsq] with u hu
    have hp : rho n u ≠ ⊤ := by
      intro h
      exact hu.ne (by rw [h]; simp)
    exact not_le.mp (fun htop => hp (le_antisymm le_top htop))
  have hf_meas : ∀ n : ℕ, Measurable (fun u : U => (rho n u).toReal) :=
    fun n => (hrho_meas n).ennreal_toReal
  have hrewrite : ∀ n : ℕ, ∫ u : U, Real.sqrt (F n u) ∂Pn n
      = ∫ u : U, (rho n u).toReal * Real.sqrt (F n u) ∂P := by
    intro n
    rw [hrho_dens n, integral_withDensity_eq_integral_toReal_smul (hrho_meas n) (hlt n)]
    simp only [smul_eq_mul]
  have hInt_sq : ∀ n : ℕ, Integrable (fun u : U => (rho n u).toReal ^ 2) P := by
    intro n
    refine ⟨?_, ?_⟩
    · have h : AEStronglyMeasurable (fun u : U => (rho n u).toReal * (rho n u).toReal) P :=
        ((hf_meas n).aestronglyMeasurable (μ := P)).mul
          ((hf_meas n).aestronglyMeasurable (μ := P))
      simpa [pow_two] using h
    · refine (hasFiniteIntegral_iff_ofReal (f := fun u : U => (rho n u).toReal ^ 2)
        (Filter.Eventually.of_forall (fun u => sq_nonneg ((rho n u).toReal)))).mpr ?_
      have hcongr : ∫⁻ u : U, ENNReal.ofReal ((rho n u).toReal ^ 2) ∂P
          = ∫⁻ u : U, rho n u * rho n u ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hlt n] with u hu
        rw [pow_two, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hu.ne]
      rw [hcongr]
      simpa [pow_two] using lt_of_le_of_lt (hrho_bound n) ENNReal.ofReal_lt_top
  have hInt_g_sq : ∀ n : ℕ, Integrable (fun u : U => Real.sqrt (F n u) ^ 2) P := by
    intro n
    refine ⟨?_, ?_⟩
    · have h : AEStronglyMeasurable (fun u : U => Real.sqrt (F n u) * Real.sqrt (F n u)) P :=
        ((hF_sqrt_int n).aestronglyMeasurable (μ := P)).mul
          ((hF_sqrt_int n).aestronglyMeasurable (μ := P))
      simpa [pow_two] using h
    · refine (hasFiniteIntegral_iff_ofReal (f := fun u : U => Real.sqrt (F n u) ^ 2)
        (Filter.Eventually.of_forall (fun u => sq_nonneg (Real.sqrt (F n u))))).mpr ?_
      have hcongr : ∫⁻ u : U, ENNReal.ofReal (Real.sqrt (F n u) ^ 2) ∂P
          = ∫⁻ u : U, ENNReal.ofReal (F n u) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards with u
        rw [Real.sq_sqrt (hF_nonneg n u)]
      rw [hcongr]
      exact (hasFiniteIntegral_iff_ofReal (f := F n)
        (Filter.Eventually.of_forall (fun u => hF_nonneg n u))).mp (hF_int n).hasFiniteIntegral
  have hmem_f : ∀ n : ℕ, MemLp (fun u : U => (rho n u).toReal) (ENNReal.ofReal (2 : ℝ)) P := by
    intro n
    have h : MemLp (fun u : U => (rho n u).toReal) (2 : ℝ≥0∞) P :=
      (memLp_two_iff_integrable_sq (f := fun u : U => (rho n u).toReal)
        (hf_meas n).aestronglyMeasurable).mpr (hInt_sq n)
    simpa using h
  have hmem_g : ∀ n : ℕ, MemLp (fun u : U => Real.sqrt (F n u)) (ENNReal.ofReal (2 : ℝ)) P := by
    intro n
    have h : MemLp (fun u : U => Real.sqrt (F n u)) (2 : ℝ≥0∞) P :=
      (memLp_two_iff_integrable_sq (f := fun u : U => Real.sqrt (F n u))
        (hF_sqrt_int n).aestronglyMeasurable).mpr (hInt_g_sq n)
    simpa using h
  have hHolder : ∀ n : ℕ, ∫ u : U, (rho n u).toReal * Real.sqrt (F n u) ∂P
      ≤ (∫ u : U, (rho n u).toReal ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)
        * (∫ u : U, (Real.sqrt (F n u)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
    intro n
    exact integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall (fun u => ENNReal.toReal_nonneg))
      (Filter.Eventually.of_forall (fun u => Real.sqrt_nonneg (F n u)))
      (hmem_f n) (hmem_g n)
  have hr2 : ∀ n : ℕ, ∫ u : U, (rho n u).toReal ^ 2 ∂P ≤ Bbar := by
    intro n
    have hcongr : ∫⁻ u : U, ENNReal.ofReal ((rho n u).toReal ^ 2) ∂P
        = ∫⁻ u : U, rho n u * rho n u ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hlt n] with u hu
      rw [pow_two, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hu.ne]
    refine (ENNReal.ofReal_le_ofReal_iff hBbar).mp ?_
    rw [ofReal_integral_eq_lintegral_ofReal (hInt_sq n)
      (Filter.Eventually.of_forall (fun u => sq_nonneg ((rho n u).toReal))), hcongr]
    simpa [pow_two] using hrho_bound n
  have hsqrt_sq : ∀ n : ℕ, ∫ u : U, (Real.sqrt (F n u)) ^ 2 ∂P = ∫ u : U, F n u ∂P := by
    intro n
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro u
    exact Real.sq_sqrt (hF_nonneg n u)
  have hbound : ∀ n : ℕ, ∫ u : U, Real.sqrt (F n u) ∂Pn n
      ≤ Real.sqrt Bbar * Real.sqrt (∫ u : U, F n u ∂P) := by
    intro n
    rw [hrewrite n]
    have hA : ∫ u : U, (rho n u).toReal ^ (2 : ℝ) ∂P = ∫ u : U, (rho n u).toReal ^ 2 ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro u
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
      dsimp only
      exact Real.rpow_natCast ((rho n u).toReal) 2
    have hB : ∫ u : U, (Real.sqrt (F n u)) ^ (2 : ℝ) ∂P
        = ∫ u : U, (Real.sqrt (F n u)) ^ 2 ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro u
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
      dsimp only
      exact Real.rpow_natCast (Real.sqrt (F n u)) 2
    calc ∫ u : U, (rho n u).toReal * Real.sqrt (F n u) ∂P
        ≤ (∫ u : U, (rho n u).toReal ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)
            * (∫ u : U, (Real.sqrt (F n u)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := hHolder n
      _ = Real.sqrt (∫ u : U, (rho n u).toReal ^ 2 ∂P)
            * Real.sqrt (∫ u : U, (Real.sqrt (F n u)) ^ 2 ∂P) := by
          rw [hA, hB, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      _ = Real.sqrt (∫ u : U, (rho n u).toReal ^ 2 ∂P)
            * Real.sqrt (∫ u : U, F n u ∂P) := by rw [hsqrt_sq n]
      _ ≤ Real.sqrt Bbar * Real.sqrt (∫ u : U, F n u ∂P) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hr2 n)) (Real.sqrt_nonneg _)
  refine squeeze_zero (fun n => integral_nonneg (fun u => Real.sqrt_nonneg (F n u))) hbound ?_
  have h2 : Filter.Tendsto (fun n : ℕ => Real.sqrt (∫ u : U, F n u ∂P)) Filter.atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hF_tendsto
    simpa using h
  have h3 : Filter.Tendsto (fun n : ℕ => Real.sqrt Bbar * Real.sqrt (∫ u : U, F n u ∂P))
      Filter.atTop (nhds 0) := by
    simpa [mul_comm] using h2.const_mul (Real.sqrt Bbar)
  exact h3
  /- @proof-region region.target-node.session.ce7d4ef8fa14bb90 end -/

end Statlib.Imported
end

