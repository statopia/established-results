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
theorem statopia_math_node_327730843_5f5f707b : ∀ (x : ℕ → ℝ≥0∞)
    (hx : ∀ n : ℕ, x n ≠ ⊤)
    (h : Tendsto (fun n : ℕ => (x n) ^ (1 / 2 : ℝ)) Filter.atTop (𝓝 0)),
    Tendsto (fun n : ℕ => (x n).toReal) Filter.atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.22c260885af01f07 begin -/
  intro x hx h
  rw [tendsto_order]
  constructor
  · intro b hb
    exact eventually_atTop.2 ⟨0, fun n _ => lt_of_lt_of_le hb ENNReal.toReal_nonneg⟩
  · intro b hb
    have hsqrtpos : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
    have hbpos : (0 : ℝ≥0∞) < ENNReal.ofReal (Real.sqrt b) := ENNReal.ofReal_pos.mpr hsqrtpos
    have hev : ∀ᶠ n : ℕ in atTop, (x n) ^ (1 / 2 : ℝ) < ENNReal.ofReal (Real.sqrt b) :=
      (tendsto_order.1 h).2 _ hbpos
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hp : (x n) ^ (1 / 2 : ℝ) < ENNReal.ofReal (Real.sqrt b) := hN n hn
    have hpu : ENNReal.ofReal ((x n).toReal) ^ (1 / 2 : ℝ) = ENNReal.ofReal ((x n).toReal ^ (1 / 2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (x := (x n).toReal) (p := 1 / 2) ENNReal.toReal_nonneg (by norm_num)
    have hxn : ENNReal.ofReal ((x n).toReal) = x n := ENNReal.ofReal_toReal (hx n)
    have hn' : ENNReal.ofReal ((x n).toReal ^ (1 / 2 : ℝ)) < ENNReal.ofReal (Real.sqrt b) := by
      rw [← hpu, hxn]
      exact hp
    have h2 : (x n).toReal ^ (1 / 2 : ℝ) < Real.sqrt b :=
      (ENNReal.ofReal_lt_ofReal_iff hsqrtpos).1 hn'
    have h3 : Real.sqrt ((x n).toReal) < Real.sqrt b := by
      rw [Real.sqrt_eq_rpow ((x n).toReal)]
      exact h2
    exact (Real.sqrt_lt_sqrt_iff ENNReal.toReal_nonneg).1 h3
  /- @proof-region region.target-node.session.22c260885af01f07 end -/

end Statlib.Imported
end

