import Lean
import ProverJobs.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.Vocabulary
import ProverJobs.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.Base

namespace PaperProofTasks.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1

open MeasureTheory ProbabilityTheory
open _root_.PaperProofTasks.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_1918606011_426b194d : ∀ (p : ℕ) (hp : 2 ≤ p) (c beta : ℝ) (hc : 0 < c)
    (hbeta : 1 + c + (Real.log 40) / (Real.log 2) ≤ beta),
    2 * (p : ℝ) * Real.exp (-(beta * Real.log (p : ℝ))) ≤
      Real.rpow (p : ℝ) (-c) / 20 := by
  /- @proof-region region.target-node.session.497559c9723fb675 begin -/
  intro p hp c beta hc hbeta
  set L := Real.log (p : ℝ) with hLdef
  have hq2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hq : (0 : ℝ) < (p : ℝ) := by linarith
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by norm_num) hq2
  have hLpos : 0 ≤ L := hL2.le.trans hL
  have ha : 0 < Real.log 40 / Real.log 2 := div_pos (Real.log_pos (by norm_num)) hL2
  have hexp1 : 2 * (p : ℝ) * Real.exp (-(beta * L)) = 2 * Real.exp ((1 - beta) * L) := by
    have hqexp : (p : ℝ) = Real.exp L := by
      rw [hLdef, Real.exp_log hq]
    rw [hqexp, mul_assoc, ← Real.exp_add, show L + -(beta * L) = (1 - beta) * L by ring]
  have hstep2 : 2 * Real.exp ((1 - beta) * L)
      ≤ 2 * Real.exp (-(c + Real.log 40 / Real.log 2) * L) := by
    have hb : 1 - beta ≤ -(c + Real.log 40 / Real.log 2) := by linarith
    have hmul : (1 - beta) * L ≤ -(c + Real.log 40 / Real.log 2) * L :=
      mul_le_mul_of_nonneg_right hb hLpos
    have hmono : Real.exp ((1 - beta) * L)
        ≤ Real.exp (-(c + Real.log 40 / Real.log 2) * L) := Real.exp_le_exp.mpr hmul
    linarith
  have hsplit : Real.exp (-(c + Real.log 40 / Real.log 2) * L)
      = Real.exp (-(c * L)) * Real.exp (-((Real.log 40 / Real.log 2) * L)) := by
    rw [← Real.exp_add,
      show -(c + Real.log 40 / Real.log 2) * L = -(c * L) + -((Real.log 40 / Real.log 2) * L)
        by ring]
  have hExpSmall : Real.exp (-((Real.log 40 / Real.log 2) * L)) ≤ 1 / 40 := by
    have hident : (Real.log 40 / Real.log 2) * Real.log 2 = Real.log 40 :=
      div_mul_cancel₀ (Real.log 40) (ne_of_gt hL2)
    have hmul : (Real.log 40 / Real.log 2) * Real.log 2 ≤ (Real.log 40 / Real.log 2) * L :=
      mul_le_mul_of_nonneg_left hL ha.le
    have hkey : Real.log 40 ≤ (Real.log 40 / Real.log 2) * L := by linarith
    calc Real.exp (-((Real.log 40 / Real.log 2) * L)) ≤ Real.exp (-(Real.log 40)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 40 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 40)]
          norm_num
  have hfinal : 2 * Real.exp (-(c + Real.log 40 / Real.log 2) * L) ≤ Real.exp (-(c * L)) / 20 := by
    rw [hsplit]
    have hpos : (0 : ℝ) ≤ 2 * Real.exp (-(c * L)) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hExpSmall hpos
    calc 2 * (Real.exp (-(c * L)) * Real.exp (-((Real.log 40 / Real.log 2) * L)))
        = 2 * Real.exp (-(c * L)) * Real.exp (-((Real.log 40 / Real.log 2) * L)) := by ring
      _ ≤ 2 * Real.exp (-(c * L)) * (1 / 40) := hmul
      _ = Real.exp (-(c * L)) / 20 := by ring
  have hrpow : Real.rpow (p : ℝ) (-c) = Real.exp (-(c * L)) := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hq,
      show Real.log (p : ℝ) * (-c) = -(c * L) by rw [hLdef]; ring]
  calc 2 * (p : ℝ) * Real.exp (-(beta * L))
      = 2 * Real.exp ((1 - beta) * L) := hexp1
    _ ≤ 2 * Real.exp (-(c + Real.log 40 / Real.log 2) * L) := hstep2
    _ ≤ Real.exp (-(c * L)) / 20 := hfinal
    _ = Real.rpow (p : ℝ) (-c) / 20 := by rw [hrpow]
  /- @proof-region region.target-node.session.497559c9723fb675 end -/

end Statlib.Imported

