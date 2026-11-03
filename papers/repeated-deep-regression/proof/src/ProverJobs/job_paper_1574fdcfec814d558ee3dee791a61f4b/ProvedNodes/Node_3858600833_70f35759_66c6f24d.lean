import Lean
import ProverJobs.job_paper_1574fdcfec814d558ee3dee791a61f4b.Vocabulary
import ProverJobs.job_paper_1574fdcfec814d558ee3dee791a61f4b.Base

namespace PaperProofTasks.job_paper_1574fdcfec814d558ee3dee791a61f4b

open _root_.PaperProofTasks.job_paper_1574fdcfec814d558ee3dee791a61f4b.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

set_option autoImplicit false in
theorem statopia_math_node_3858600833_70f35759 : ∀ (Ω' : Type*) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (e : Ω' → ℝ) (B3 : ℝ) (hB3 : 0 < B3)
    (hint : Integrable (fun ω : Ω' => Real.exp (|e ω| / B3)) P)
    (hbound : ∫ ω : Ω', Real.exp (|e ω| / B3) ∂P ≤ 1),
    e =ᵐ[P] 0 := by
  /- @proof-region region.target-node.session.ef6fb279ffe1958d begin -/
  intro Ω' _ P _ e B3 hB3 hint hbound
  have hge : ∀ ω : Ω', (1 : ℝ) ≤ Real.exp (|e ω| / B3) := by
    intro ω
    have h : (0 : ℝ) ≤ |e ω| / B3 := div_nonneg (abs_nonneg _) hB3.le
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (|e ω| / B3) := Real.exp_le_exp.mpr h
  have hIntOne : Integrable (fun _ : Ω' => (1 : ℝ)) P := integrable_const 1
  have hIntG : Integrable (fun ω : Ω' => Real.exp (|e ω| / B3) - 1) P := hint.sub hIntOne
  have hone : ∫ _ : Ω', (1 : ℝ) ∂P = 1 := by simp
  have hmono : (1 : ℝ) ≤ ∫ ω : Ω', Real.exp (|e ω| / B3) ∂P := by
    have h := integral_mono hIntOne hint hge
    rwa [hone] at h
  have hEq : ∫ ω : Ω', Real.exp (|e ω| / B3) ∂P = 1 := le_antisymm hbound hmono
  have hzero : ∫ ω : Ω', (Real.exp (|e ω| / B3) - 1) ∂P = 0 := by
    rw [integral_sub hint hIntOne, hEq, hone]
    ring
  have hnonneg : 0 ≤ (fun ω : Ω' => Real.exp (|e ω| / B3) - 1) := by
    intro ω
    show (0 : ℝ) ≤ Real.exp (|e ω| / B3) - 1
    linarith [hge ω]
  have hae : (fun ω : Ω' => Real.exp (|e ω| / B3) - 1) =ᵐ[P] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg hnonneg hIntG).mp hzero
  filter_upwards [hae] with ω hω
  have hω' : Real.exp (|e ω| / B3) - 1 = 0 := hω
  have h1 : Real.exp (|e ω| / B3) = 1 := by linarith
  have h2 : |e ω| / B3 = 0 := by
    apply Real.exp_injective
    rw [h1, Real.exp_zero]
  have h3 : |e ω| = 0 := by
    rcases div_eq_zero_iff.mp h2 with h | h
    · exact h
    · exact absurd h hB3.ne'
  exact abs_eq_zero.mp h3
  /- @proof-region region.target-node.session.ef6fb279ffe1958d end -/

end Statlib.Imported

