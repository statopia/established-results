import Statlib.StatFoundation.EmpiricalProcess.RademacherSecondMoment
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
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
theorem statopia_math_node_3511190190_0d8a3dbd : ∀ (m : ℕ) (hm : 1 ≤ m),
    ∫ (g : Fin m → ℝ), Real.sqrt (∑ i : Fin m, (g i) ^ 2)
        ∂(MeasureTheory.Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)) ≤
      Real.sqrt (m : ℝ) := by
  /- @proof-region region.target-node.session.bd028a4c44356e5c begin -/
  intro m hm
  have hsecond : ∫ x : ℝ, x ^ 2 ∂(gaussianReal (0 : ℝ) 1) = 1 := by
    have hmemLp : MemLp (fun x : ℝ => x) 2 (gaussianReal (0 : ℝ) 1) := by
      simpa using
        Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal 1 2 (by simp)
    have hvar : variance (fun x : ℝ => x) (gaussianReal (0 : ℝ) 1) = 1 := by
      simpa using ProbabilityTheory.variance_fun_id_gaussianReal (μ := 0) (v := 1)
    have hEx : ∫ x : ℝ, x ∂(gaussianReal (0 : ℝ) 1) = 0 := by
      simpa using ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)
    rw [ProbabilityTheory.variance_eq_sub hmemLp,
      show ((fun x : ℝ => x) ^ 2) = fun x : ℝ => x ^ 2 from rfl] at hvar
    simpa [hEx] using hvar
  have hmarg : ∀ i : Fin m,
      ∫ g : Fin m → ℝ, (g i) ^ 2
        ∂(Measure.pi (fun _ : Fin m => gaussianReal (0 : ℝ) 1)) = 1 := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin m => (gaussianReal (0 : ℝ) 1)) i
    have hstep :
        ∫ g : Fin m → ℝ, (g i) ^ 2
            ∂(Measure.pi (fun _ : Fin m => gaussianReal (0 : ℝ) 1))
          = ∫ x : ℝ, x ^ 2
              ∂(Measure.map (Function.eval i)
                (Measure.pi (fun _ : Fin m => gaussianReal (0 : ℝ) 1))) :=
      (MeasureTheory.integral_map_of_stronglyMeasurable hmp.measurable
        (φ := Function.eval i)
        (f := fun x : ℝ => x ^ 2) (by fun_prop)).symm
    rw [hstep, hmp.map_eq, hsecond]
  have hcoord_int : ∀ i : Fin m,
      Integrable (fun g : Fin m → ℝ => (g i) ^ 2)
        (Measure.pi (fun _ : Fin m => gaussianReal (0 : ℝ) 1)) := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin m => (gaussianReal (0 : ℝ) 1)) i
    have hmemLp : MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal (0 : ℝ) 1) :=
      Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal 2 2 (by simp)
    have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal (0 : ℝ) 1) :=
      hmemLp.integrable (by norm_num)
    exact hmp.integrable_comp_of_integrable hint
  have hF_int : Integrable (fun g : Fin m → ℝ => ∑ i : Fin m, (g i) ^ 2)
      (Measure.pi (fun _ : Fin m => gaussianReal (0 : ℝ) 1)) :=
    MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => hcoord_int i)
  have hF_eq : ∫ g : Fin m → ℝ, (∑ i : Fin m, (g i) ^ 2)
      ∂(Measure.pi (fun _ : Fin m => gaussianReal (0 : ℝ) 1)) = (m : ℝ) := by
    rw [MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hcoord_int i)]
    simp [hmarg]
  have hF_nonneg : ∀ᵐ g ∂(Measure.pi (fun _ : Fin m => gaussianReal (0 : ℝ) 1)),
      0 ≤ ∑ i : Fin m, (g i) ^ 2 :=
    Filter.Eventually.of_forall (fun g => Finset.sum_nonneg (fun i _ => sq_nonneg (g i)))
  have hsqrt_int : Integrable (fun g : Fin m → ℝ => Real.sqrt (∑ i : Fin m, (g i) ^ 2))
      (Measure.pi (fun _ : Fin m => gaussianReal (0 : ℝ) 1)) := by
    refine Integrable.mono (hF_int.add (integrable_const (1 : ℝ))) ?_ ?_
    · have hcont : Continuous
          (fun g : Fin m → ℝ => Real.sqrt (∑ i : Fin m, (g i) ^ 2)) := by
        fun_prop
      exact hcont.aestronglyMeasurable
    · filter_upwards with g
      have h1 : 0 ≤ ∑ i : Fin m, (g i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (g i))
      have hle : ∑ i : Fin m, (g i) ^ 2 ≤ (∑ i : Fin m, (g i) ^ 2 + 1) ^ 2 := by
        nlinarith
      have hb : Real.sqrt (∑ i : Fin m, (g i) ^ 2) ≤ ∑ i : Fin m, (g i) ^ 2 + 1 := by
        calc Real.sqrt (∑ i : Fin m, (g i) ^ 2)
            ≤ Real.sqrt ((∑ i : Fin m, (g i) ^ 2 + 1) ^ 2) := Real.sqrt_le_sqrt hle
          _ = ∑ i : Fin m, (g i) ^ 2 + 1 := Real.sqrt_sq (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs,
        abs_of_nonneg (by
          show (0 : ℝ) ≤ ∑ i : Fin m, (g i) ^ 2 + 1
          linarith)]
      exact hb
  have hmain := Statlib.StatFoundation.EmpiricalProcess.sqrt_integral_le
    (Measure.pi (fun _ : Fin m => gaussianReal (0 : ℝ) 1))
    (fun g : Fin m → ℝ => ∑ i : Fin m, (g i) ^ 2) hF_nonneg hF_int hsqrt_int
  rw [hF_eq] at hmain
  exact hmain
  /- @proof-region region.target-node.session.bd028a4c44356e5c end -/

end Statlib.Imported

