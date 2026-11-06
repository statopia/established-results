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
theorem statopia_math_node_3931290992_decd810a : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ι : Type} [Fintype ι] (f : ι → α → β → ℝ)
    (hf : ∀ i : ι, MeasureTheory.Integrable (Function.uncurry (f i)) (μ.prod ν)),
    ∀ᵐ y ∂ν, ∀ i : ι, MeasureTheory.Integrable (fun x : α => f i x y) μ := by
  /- @proof-region region.target-node.session.891af374d0d2dbe2 begin -/
  intro α β _ _ μ ν _ _ ι _ f hf
  classical
  have key : ∀ i : ι, ∀ᵐ y ∂ν, Integrable (fun x : α => f i x y) μ := by
    intro i
    have hslice_meas : ∀ᵐ y ∂ν, AEStronglyMeasurable (fun x : α => f i x y) μ := by
      have h := MeasureTheory.AEStronglyMeasurable.prodMk_right (μ := μ) (ν := ν)
        (f := Function.uncurry (f i)) (hf i).aestronglyMeasurable
      simpa [Function.uncurry] using h
    have hG : Integrable (Function.uncurry (f i)) (μ.prod ν) := hf i
    set F : α × β → ENNReal := fun p => (‖f i p.1 p.2‖₊ : ENNReal) with hF
    have hmeas_prod : AEMeasurable F (μ.prod ν) := by
      have h1 : AEMeasurable (Function.uncurry (f i)) (μ.prod ν) :=
        hG.aestronglyMeasurable.aemeasurable
      have h2 : AEMeasurable (fun p : α × β => ‖Function.uncurry (f i) p‖₊) (μ.prod ν) :=
        h1.nnnorm
      exact h2.coe_nnreal_ennreal
    have hsymm : ∫⁻ p : α × β, F p ∂(μ.prod ν) = ∫⁻ y : β, ∫⁻ x : α, F (x, y) ∂μ ∂ν :=
      MeasureTheory.lintegral_prod_symm F hmeas_prod
    have hfin_prod : ∫⁻ y : β, ∫⁻ x : α, F (x, y) ∂μ ∂ν ≠ ⊤ := by
      rw [← hsymm]
      have hlt : ∫⁻ (p : α × β), F p ∂(μ.prod ν) < ⊤ := by
        simpa [hF, MeasureTheory.HasFiniteIntegral, enorm_eq_nnnorm, Function.uncurry] using
          hG.hasFiniteIntegral
      exact hlt.ne
    have hg_meas : AEMeasurable (fun y : β => ∫⁻ x : α, F (x, y) ∂μ) ν :=
      AEMeasurable.lintegral_prod_left (μ := μ) (ν := ν) (f := fun x y => F (x, y)) hmeas_prod
    have hfin_ae : ∀ᵐ y ∂ν, ∫⁻ x : α, (‖f i x y‖₊ : ENNReal) ∂μ ≠ ⊤ := by
      have h0 : ν {y : β | (∫⁻ x : α, F (x, y) ∂μ) = ⊤} = 0 :=
        MeasureTheory.measure_eq_top_of_lintegral_ne_top hg_meas hfin_prod
      have h0' : ν {y : β | (∫⁻ x : α, (‖f i x y‖₊ : ENNReal) ∂μ) = ⊤} = 0 := by
        simpa [hF] using h0
      exact MeasureTheory.ae_iff.mpr (by simpa using h0')
    filter_upwards [hslice_meas, hfin_ae] with y hsm hfi
    refine ⟨hsm, ?_⟩
    simpa [MeasureTheory.HasFiniteIntegral, enorm_eq_nnnorm] using (lt_of_le_of_ne le_top hfi)
  have hall : ∀ᵐ y ∂ν, ∀ i : ι, Integrable (fun x : α => f i x y) μ := by
    have hfs : ∀ s : Finset ι, ∀ᵐ y ∂ν, ∀ i ∈ s, Integrable (fun x : α => f i x y) μ := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact Filter.Eventually.of_forall (by simp)
      | insert a s ha ih =>
          filter_upwards [key a, ih] with y hy1 hy2 i hi
          rcases Finset.mem_insert.mp hi with rfl | hmem
          · exact hy1
          · exact hy2 i hmem
    simpa using hfs Finset.univ
  exact hall
  /- @proof-region region.target-node.session.891af374d0d2dbe2 end -/

end Statlib.Imported

