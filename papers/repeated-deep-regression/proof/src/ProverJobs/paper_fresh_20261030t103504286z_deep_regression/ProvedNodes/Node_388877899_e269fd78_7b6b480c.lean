import Statlib.StatFoundation.Vocabulary.EmpiricalProcess
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
theorem statopia_math_node_388877899_e269fd78 : ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
    Measure.pi
        (fun _ : ι =>
          (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ))) =
      (Fintype.card (ι → Bool) : ℝ≥0∞)⁻¹ •
        ∑ ε : ι → Bool,
          Measure.dirac (fun i => Statlib.StatFoundation.Vocabulary.rademacherSign (ε i)) := by
  /- @proof-region region.target-node.session.6bcfdde631c05172 begin -/
  intro ι _ _
  classical
  set c : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ)) with hc
  have hcprob : c Set.univ = 1 := by
    rw [hc, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply, Measure.dirac_apply,
      Set.indicator_of_mem (Set.mem_univ (1 : ℝ)), Set.indicator_of_mem (Set.mem_univ (-1 : ℝ))]
    simp only [Pi.one_apply, smul_eq_mul]
    rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  haveI hfin : IsFiniteMeasure c := ⟨by rw [hcprob]; exact ENNReal.one_lt_top⟩
  apply Measure.pi_eq
  intro s _
  have hR : ∏ i : ι, c (s i)
      = (∏ _ : ι, (2 : ℝ≥0∞)⁻¹) *
          ∏ i : ι, ((if (1 : ℝ) ∈ s i then (1 : ℝ≥0∞) else 0) + (if (-1 : ℝ) ∈ s i then (1 : ℝ≥0∞) else 0)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [hc, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply, Measure.dirac_apply]
    simp only [Set.indicator_apply, Pi.one_apply, smul_eq_mul]
  have hf : ∀ i : ι, (∑ b : Bool, (if Statlib.StatFoundation.Vocabulary.rademacherSign b ∈ s i then (1 : ℝ≥0∞) else 0))
      = ((if (1 : ℝ) ∈ s i then (1 : ℝ≥0∞) else 0) + (if (-1 : ℝ) ∈ s i then (1 : ℝ≥0∞) else 0)) := by
    intro i
    rw [Fintype.sum_bool]
    simp [Statlib.StatFoundation.Vocabulary.rademacherSign]
  have hsum : (∑ ε : ι → Bool, (if ∀ i, Statlib.StatFoundation.Vocabulary.rademacherSign (ε i) ∈ s i then (1 : ℝ≥0∞) else 0))
      = ∏ i : ι, ((if (1 : ℝ) ∈ s i then (1 : ℝ≥0∞) else 0) + (if (-1 : ℝ) ∈ s i then (1 : ℝ≥0∞) else 0)) := by
    have hpiFinset : Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)) = Finset.univ := by
      ext x; simp [Fintype.mem_piFinset]
    have hstep1 : (∑ ε : ι → Bool, (if ∀ i, Statlib.StatFoundation.Vocabulary.rademacherSign (ε i) ∈ s i then (1 : ℝ≥0∞) else 0))
        = ∑ ε : ι → Bool, ∏ i : ι, (if Statlib.StatFoundation.Vocabulary.rademacherSign (ε i) ∈ s i then (1 : ℝ≥0∞) else 0) := by
      apply Finset.sum_congr rfl
      intro ε _
      exact (Fintype.prod_boole (p := fun i => Statlib.StatFoundation.Vocabulary.rademacherSign (ε i) ∈ s i)).symm
    have hstep2 : (∑ ε : ι → Bool, ∏ i : ι, (if Statlib.StatFoundation.Vocabulary.rademacherSign (ε i) ∈ s i then (1 : ℝ≥0∞) else 0))
        = ∏ i : ι, ∑ b : Bool, (if Statlib.StatFoundation.Vocabulary.rademacherSign b ∈ s i then (1 : ℝ≥0∞) else 0) := by
      rw [Finset.prod_univ_sum (t := fun _ : ι => (Finset.univ : Finset Bool))
        (f := fun i b => (if Statlib.StatFoundation.Vocabulary.rademacherSign b ∈ s i then (1 : ℝ≥0∞) else 0))]
      rw [hpiFinset]
    rw [hstep1, hstep2]
    exact Finset.prod_congr rfl (fun i _ => hf i)
  have hL : ((Fintype.card (ι → Bool) : ℝ≥0∞)⁻¹ •
        ∑ ε : ι → Bool, Measure.dirac (fun i => Statlib.StatFoundation.Vocabulary.rademacherSign (ε i))) (Set.univ.pi s)
      = (Fintype.card (ι → Bool) : ℝ≥0∞)⁻¹ *
          ∑ ε : ι → Bool, (if ∀ i, Statlib.StatFoundation.Vocabulary.rademacherSign (ε i) ∈ s i then (1 : ℝ≥0∞) else 0) := by
    simp only [Measure.smul_apply, Measure.finset_sum_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro ε _
    simp only [Measure.dirac_apply, Set.indicator_apply, Pi.one_apply, Set.mem_univ_pi]
  have hcard : (Fintype.card (ι → Bool) : ℝ≥0∞)⁻¹ = ∏ _ : ι, (2 : ℝ≥0∞)⁻¹ := by
    rw [Fintype.card_fun, Fintype.card_bool, Finset.prod_const, Finset.card_univ]
    rw [Nat.cast_pow, ← ENNReal.inv_pow]
    simp
  rw [hL, hsum, hcard]
  exact hR.symm
  /- @proof-region region.target-node.session.6bcfdde631c05172 end -/

end Statlib.Imported
end

