import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_147939998_02815ef8 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ℕ) (hp : 0 < p)
    (mu : Fin p → ℝ) (F : Fin p → Ω → ℝ) (hmeas : ∀ j : Fin p, Measurable (F j))
    (h3 : ∀ j : Fin p, Integrable (fun ω => |F j ω - mu j| ^ 3) P),
    Integrable (fun ω => (⨆ j : Fin p, |F j ω - mu j|) ^ 3) P := by
  /- @proof-region region.target-node.session.b3338f9161a584fc begin -/
  intro Ω _ P p hp mu F hmeas h3
  haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩


  have hS_meas : Measurable (fun ω => ⨆ j : Fin p, |F j ω - mu j|) :=
    Measurable.iSup fun j => continuous_abs.measurable.comp ((hmeas j).sub measurable_const)
  have hdom : ∀ ω, (⨆ j : Fin p, |F j ω - mu j|) ^ 3 ≤ ∑ j : Fin p, |F j ω - mu j| ^ 3 := by
    intro ω
    obtain ⟨j₀, hj₀⟩ := exists_eq_ciSup_of_finite (f := fun j : Fin p => |F j ω - mu j|)
    have hsingle : |F j₀ ω - mu j₀| ^ 3 ≤ ∑ j : Fin p, |F j ω - mu j| ^ 3 := by
      have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin p)))
        (f := fun j : Fin p => |F j ω - mu j| ^ 3)
        (fun j _ => pow_nonneg (abs_nonneg (F j ω - mu j)) 3) (Finset.mem_univ j₀)
      simpa using h
    rw [hj₀.symm]
    exact hsingle
  have hsum_int : Integrable (fun ω => ∑ j : Fin p, |F j ω - mu j| ^ 3) P :=
    integrable_finset_sum Finset.univ (fun j _ => h3 j)
  refine Integrable.mono' hsum_int
    ((continuous_id.pow 3).measurable.comp hS_meas).aestronglyMeasurable ?_
  filter_upwards with ω
  have hSnn : 0 ≤ ⨆ j : Fin p, |F j ω - mu j| :=
    Real.iSup_nonneg fun j => abs_nonneg (F j ω - mu j)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hSnn 3)]
  exact hdom ω

  /- @proof-region region.target-node.session.b3338f9161a584fc end -/

end

end Statlib.Imported

