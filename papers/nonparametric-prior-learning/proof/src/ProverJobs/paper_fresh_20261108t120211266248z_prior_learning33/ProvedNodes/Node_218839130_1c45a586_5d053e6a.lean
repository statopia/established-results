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
theorem statopia_math_node_218839130_1c45a586 : ∀ (U : Type*) [MeasurableSpace U] (P : Measure U) [IsProbabilityMeasure P]
    (rho : U → ℝ≥0∞) (g : U → ℝ)
    (hrho : Measurable rho) (hg : AEMeasurable g P)
    (hg_int : Integrable g (P.withDensity rho))
    (hg_pos : ∀ u : U, 0 < g u),
    ∀ᵐ u ∂P, rho u < ⊤ := by
  /- @proof-region region.target-node.session.228b6df5909c6563 begin -/
  intro U _ P _ rho g hrho hg hg_int hg_pos
  have hae : AEMeasurable (fun u => ENNReal.ofReal (g u)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable' hg
  have hint : ∫⁻ u, rho u * ENNReal.ofReal (g u) ∂P < ⊤ := by
    have h := hg_int.lintegral_lt_top
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hrho.aemeasurable hae] at h
    simpa using h
  set A : Set U := {u | rho u = ⊤} with hA
  have hA_meas : MeasurableSet A := by
    rw [hA]
    exact hrho (measurableSet_singleton ⊤)
  have hineq : ∫⁻ u in A, (⊤ : ℝ≥0∞) ∂P ≤ ∫⁻ u, rho u * ENNReal.ofReal (g u) ∂P := by
    rw [← MeasureTheory.lintegral_indicator hA_meas]
    apply MeasureTheory.lintegral_mono
    intro u
    by_cases hu : u ∈ A
    · have htop : rho u = ⊤ := hu
      have hne : ENNReal.ofReal (g u) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (hg_pos u))
      have hprod : rho u * ENNReal.ofReal (g u) = ⊤ := by
        rw [htop, ENNReal.top_mul hne]
      rw [Set.indicator_of_mem hu]
      exact le_of_eq hprod.symm
    · simp [hu]
  have htopint : ∫⁻ u in A, (⊤ : ℝ≥0∞) ∂P = ⊤ * P A :=
    MeasureTheory.setLIntegral_const A ⊤
  have hPA : P A = 0 := by
    have h2 : ⊤ * P A < ⊤ := by
      rw [← htopint]
      exact lt_of_le_of_lt hineq hint
    by_contra hne
    rw [ENNReal.top_mul hne] at h2
    exact absurd h2 (lt_irrefl ⊤)
  rw [MeasureTheory.ae_iff]
  have hset : {u : U | ¬ rho u < ⊤} = A := by
    rw [hA]
    ext u
    simp [lt_top_iff_ne_top]
  rw [hset, hPA]
  /- @proof-region region.target-node.session.228b6df5909c6563 end -/

end Statlib.Imported
end

