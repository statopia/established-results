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
theorem statopia_math_node_971375954_c360ad8c : ∀ (U : Type*) [MeasurableSpace U] (P : Measure U) [IsProbabilityMeasure P]
    (rho W : U → ℝ≥0∞)
    (hrho : Measurable rho)
    (hW : AEMeasurable W P)
    (hrho_sq : ∫⁻ u : U, rho u ^ 2 ∂P < ⊤)
    (hW_sq : ∫⁻ u : U, W u ^ 2 ∂P < ⊤),
    ∫⁻ u : U, W u ∂(P.withDensity rho) < ⊤ := by
  /- @proof-region region.target-node.session.54ff5406313e25f0 begin -/
  intro U _ P _ rho W hrho hW hrho_sq hW_sq
  have hwith : ∫⁻ u : U, W u ∂(P.withDensity rho) = ∫⁻ u : U, rho u * W u ∂P :=
    lintegral_withDensity_eq_lintegral_mul₀ (μ := P) (f := rho) (g := W)
      hrho.aemeasurable hW
  rw [hwith]
  have hpt : ∀ u : U, rho u * W u ≤ rho u ^ 2 + W u ^ 2 := by
    intro u
    rcases le_total (rho u) (W u) with h | h
    · have h1 : rho u * W u ≤ W u ^ 2 := by
        calc rho u * W u ≤ W u * W u := by gcongr
          _ = W u ^ 2 := (pow_two (W u)).symm
      refine le_trans h1 ?_
      simpa using add_le_add_right (zero_le (rho u ^ 2)) (W u ^ 2)
    · have h1 : rho u * W u ≤ rho u ^ 2 := by
        calc rho u * W u ≤ rho u * rho u := by gcongr
          _ = rho u ^ 2 := (pow_two (rho u)).symm
      refine le_trans h1 ?_
      simpa using add_le_add_left (zero_le (W u ^ 2)) (rho u ^ 2)
  have hadd : ∫⁻ u : U, (rho u ^ 2 + W u ^ 2) ∂P
      = (∫⁻ u : U, rho u ^ 2 ∂P) + ∫⁻ u : U, W u ^ 2 ∂P :=
    lintegral_add_left (μ := P) (f := fun u : U => rho u ^ 2) (g := fun u : U => W u ^ 2)
      (hrho.pow_const 2)
  calc ∫⁻ u : U, rho u * W u ∂P
      ≤ ∫⁻ u : U, (rho u ^ 2 + W u ^ 2) ∂P := lintegral_mono hpt
    _ = (∫⁻ u : U, rho u ^ 2 ∂P) + ∫⁻ u : U, W u ^ 2 ∂P := hadd
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hrho_sq, hW_sq⟩
  /- @proof-region region.target-node.session.54ff5406313e25f0 end -/

end Statlib.Imported
end

