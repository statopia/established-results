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
theorem statopia_math_node_3685606887_454ff366 : ∀ (U : Type*) [MeasurableSpace U] (P : Measure U) [IsProbabilityMeasure P]
    (rho : ℕ → U → ℝ≥0∞) (s2 : ℕ → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (rho n))
    (hmom2 : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.rpow (rho n u) (2 : ℝ) ∂P) = ENNReal.ofReal (Real.exp (s2 n)))
    (hmom1 : ∀ n : ℕ,
      (∫⁻ u : U, ENNReal.rpow (rho n u) (1 : ℝ) ∂P) = 1)
    (hexp : Filter.Tendsto (fun n : ℕ => Real.exp (s2 n) - 1) Filter.atTop (𝓝 0)),
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P)
      Filter.atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.f47080ecd03d5bf0 begin -/
  intro U _ P _ rho s2 hmeas hmom2 hmom1 hexp
  have hfin : ∀ n : ℕ, ∀ᵐ u : U ∂P, rho n u < ⊤ := by
    intro n
    have h1 : (∫⁻ u : U, rho n u ∂P) = 1 := by
      simpa using hmom1 n
    exact MeasureTheory.ae_lt_top (hmeas n) (by rw [h1]; exact ENNReal.one_ne_top)
  have hkey : ∀ n : ℕ, (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P)
      = ENNReal.ofReal (Real.exp (s2 n) - 1) := by
    intro n
    have hB : (fun u : U => ENNReal.ofReal (2 * (rho n u).toReal)) =ᵐ[P] (fun u => 2 * rho n u) := by
      filter_upwards [hfin n] with u hu
      have hr : ENNReal.ofReal ((rho n u).toReal) = rho n u := ENNReal.ofReal_toReal hu.ne
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), hr]
      norm_num
    have hC : (fun u : U => ENNReal.ofReal ((rho n u).toReal ^ 2))
        =ᵐ[P] (fun u => ENNReal.rpow (rho n u) (2 : ℝ)) := by
      filter_upwards [hfin n] with u hu
      have hr : ENNReal.ofReal ((rho n u).toReal) = rho n u := ENNReal.ofReal_toReal hu.ne
      rw [show ENNReal.rpow (rho n u) (2 : ℝ)
          = ENNReal.rpow (ENNReal.ofReal ((rho n u).toReal)) (2 : ℝ) from
        congrArg (fun z => ENNReal.rpow z (2 : ℝ)) hr.symm]
      rw [ENNReal.ofReal_pow (show (0:ℝ) ≤ (rho n u).toReal from ENNReal.toReal_nonneg)]
      exact (ENNReal.rpow_natCast (ENNReal.ofReal ((rho n u).toReal)) 2).symm
    have hpt : ∀ᵐ u : U ∂P,
        ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) + ENNReal.ofReal (2 * (rho n u).toReal)
          = ENNReal.ofReal ((rho n u).toReal ^ 2) + 1 := by
      filter_upwards [hfin n] with u hu
      have h1n : (0:ℝ) ≤ ((rho n u).toReal - 1) ^ 2 := sq_nonneg _
      have hn : (0:ℝ) ≤ (rho n u).toReal := ENNReal.toReal_nonneg
      have h2n : (0:ℝ) ≤ 2 * (rho n u).toReal := by linarith
      have h3n : (0:ℝ) ≤ (rho n u).toReal ^ 2 := sq_nonneg _
      have e1 : ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) + ENNReal.ofReal (2 * (rho n u).toReal)
          = ENNReal.ofReal (((rho n u).toReal - 1) ^ 2 + 2 * (rho n u).toReal) :=
        (ENNReal.ofReal_add h1n h2n).symm
      have e2 : ENNReal.ofReal ((rho n u).toReal ^ 2) + 1
          = ENNReal.ofReal ((rho n u).toReal ^ 2 + 1) := by
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_add h3n zero_le_one).symm
      rw [e1, e2]
      congr 1
      ring
    have hX2 : (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P) + 2
        = ENNReal.ofReal (Real.exp (s2 n)) + 1 := by
      have h1 : (∫⁻ u : U, rho n u ∂P) = 1 := by
        simpa using hmom1 n
      have hAB : (fun u : U => ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) + ENNReal.ofReal (2 * (rho n u).toReal))
          =ᵐ[P] (fun u => ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) + 2 * rho n u) := by
        filter_upwards [hB] with u hu
        rw [hu]
      have hL : (∫⁻ u : U, (ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) + ENNReal.ofReal (2 * (rho n u).toReal)) ∂P)
          = (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P) + 2 := by
        rw [MeasureTheory.lintegral_congr_ae hAB,
          MeasureTheory.lintegral_add_right (fun u : U => ENNReal.ofReal (((rho n u).toReal - 1) ^ 2))]
        · have h2r : (∫⁻ u : U, 2 * rho n u ∂P) = 2 := by
            rw [MeasureTheory.lintegral_const_mul'']
            · rw [h1]
              norm_num
            · exact (hmeas n).aemeasurable
          rw [h2r]
        · exact measurable_const.mul (hmeas n)
      have hCD : (fun u : U => ENNReal.ofReal ((rho n u).toReal ^ 2) + 1)
          =ᵐ[P] (fun u => ENNReal.rpow (rho n u) (2 : ℝ) + 1) := by
        filter_upwards [hC] with u hu
        rw [hu]
      have hR : (∫⁻ u : U, (ENNReal.ofReal ((rho n u).toReal ^ 2) + 1) ∂P)
          = ENNReal.ofReal (Real.exp (s2 n)) + 1 := by
        rw [MeasureTheory.lintegral_congr_ae hCD,
          MeasureTheory.lintegral_add_right (fun u : U => ENNReal.rpow (rho n u) (2 : ℝ))]
        · rw [hmom2 n]
          have hone : (∫⁻ _u : U, (1 : ℝ≥0∞) ∂P) = 1 := by simp
          rw [hone]
        · exact measurable_const
      have hI1 : (∫⁻ u : U, (ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) + ENNReal.ofReal (2 * (rho n u).toReal)) ∂P)
          = (∫⁻ u : U, (ENNReal.ofReal ((rho n u).toReal ^ 2) + 1) ∂P) :=
        MeasureTheory.lintegral_congr_ae hpt
      rw [← hL, hI1, hR]
    have hXtop : (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P) ≠ ⊤ := by
      have hBtop : ENNReal.ofReal (Real.exp (s2 n)) + 1 ≠ ⊤ := by
        simp
      intro htop
      exact hBtop (by rw [← hX2, htop]; simp)
    have hreal : (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P).toReal + 2
        = Real.exp (s2 n) + 1 := by
      have h := congrArg ENNReal.toReal hX2
      rw [ENNReal.toReal_add hXtop (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
        ENNReal.toReal_add (ENNReal.ofReal_ne_top) (by norm_num : (1 : ℝ≥0∞) ≠ ⊤),
        ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos (s2 n)))] at h
      simpa using h
    have hXval : (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P).toReal
        = Real.exp (s2 n) - 1 := by
      linarith
    rw [← ENNReal.ofReal_toReal hXtop, hXval]
  have hlim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (s2 n) - 1)) Filter.atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun b hb => absurd hb (not_lt.mpr (zero_le b)), ?_⟩
    intro b hb
    by_cases hbtop : b = ⊤
    · subst hbtop
      exact Filter.Eventually.of_forall fun n => ENNReal.ofReal_lt_top
    · have hbpos : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hbtop
      have hb_eq : ENNReal.ofReal b.toReal = b := ENNReal.ofReal_toReal hbtop
      filter_upwards [(tendsto_order.1 hexp).2 b.toReal hbpos] with n hn
      rw [← hb_eq, ENNReal.ofReal_lt_ofReal_iff hbpos]
      exact hn
  exact hlim.congr' (Filter.Eventually.of_forall fun n => (hkey n).symm)
  /- @proof-region region.target-node.session.f47080ecd03d5bf0 end -/

end Statlib.Imported
end

