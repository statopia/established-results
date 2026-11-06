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
theorem statopia_math_node_647033768_7a6b2259 : ∀ (ι : Type*) [Fintype ι] (c : ι → ℝ),
    MeasureTheory.Measure.map (fun ω : ι → ℝ => ∑ p : ι, c p * ω p)
        (MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) =
      ProbabilityTheory.gaussianReal 0
        ⟨∑ p : ι, (c p) ^ 2, Finset.sum_nonneg fun p _ => sq_nonneg (c p)⟩ := by
  /- @proof-region region.target-node.session.441f9140935d0504 begin -/
  intro ι _ c
  classical
  generalize hv : (⟨∑ p : ι, (c p) ^ 2, Finset.sum_nonneg fun p _ => sq_nonneg (c p)⟩ : NNReal) = v
  apply MeasureTheory.Measure.ext_of_charFun
  funext t
  rw [ProbabilityTheory.charFun_gaussianReal]
  have hreal : ∀ a b : ℝ, inner ℝ a b = a * b := fun a b => mul_comm b a
  have hHmeas : AEMeasurable (fun ω : ι → ℝ => ∑ p : ι, c p * ω p)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    have hcoord : ∀ p : ι, Measurable (fun ω : ι → ℝ => ω p) :=
      fun p => (measurable_pi_iff (g := fun x : ι → ℝ => x)).mp measurable_id p
    have hgen : ∀ s : Finset ι, Measurable (fun ω : ι → ℝ => ∑ p ∈ s, c p * ω p) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (measurable_const : Measurable fun _ : ι → ℝ => (0 : ℝ))
      | insert a s ha ih =>
          have hstep : (fun ω : ι → ℝ => ∑ p ∈ insert a s, c p * ω p)
              = fun ω : ι → ℝ => c a * ω a + ∑ p ∈ s, c p * ω p := by
            funext ω
            rw [Finset.sum_insert ha]
          rw [hstep]
          exact (measurable_const.mul (hcoord a)).add ih
    exact (hgen Finset.univ).aemeasurable
  have hTLmeas : AEMeasurable (WithLp.toLp 2 : (ι → ℝ) → PiLp 2 (fun _ : ι => ℝ))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    (WithLp.measurable_toLp 2 (ι → ℝ)).aemeasurable
  have hL1 : charFun (Measure.map (fun ω : ι → ℝ => ∑ p : ι, c p * ω p)
        (Measure.pi (fun _ : ι => gaussianReal 0 1))) t
      = ∫ ω, Complex.exp (↑(inner ℝ (∑ p : ι, c p * ω p) t) * Complex.I)
          ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    rw [MeasureTheory.charFun_apply,
      MeasureTheory.integral_map hHmeas (Continuous.aestronglyMeasurable (by fun_prop))]
  have hI2 : ∫ ω, Complex.exp (↑(inner ℝ (WithLp.toLp 2 ω : PiLp 2 (fun _ : ι => ℝ))
        (WithLp.toLp 2 (fun i : ι => t * c i))) * Complex.I)
        ∂(Measure.pi (fun _ : ι => gaussianReal 0 1))
      = charFun (Measure.map (WithLp.toLp 2 : (ι → ℝ) → PiLp 2 (fun _ : ι => ℝ))
        (Measure.pi (fun _ : ι => gaussianReal 0 1)))
        (WithLp.toLp 2 (fun i : ι => t * c i)) := by
    rw [MeasureTheory.charFun_apply,
      MeasureTheory.integral_map hTLmeas (Continuous.aestronglyMeasurable (by fun_prop))]
  have hint : ∫ ω, Complex.exp (↑(inner ℝ (∑ p : ι, c p * ω p) t) * Complex.I)
        ∂(Measure.pi (fun _ : ι => gaussianReal 0 1))
      = ∫ ω, Complex.exp (↑(inner ℝ (WithLp.toLp 2 ω : PiLp 2 (fun _ : ι => ℝ))
          (WithLp.toLp 2 (fun i : ι => t * c i))) * Complex.I)
          ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    have hinner : inner ℝ (WithLp.toLp 2 ω : PiLp 2 (fun _ : ι => ℝ))
        (WithLp.toLp 2 (fun i : ι => t * c i)) = inner ℝ (∑ p : ι, c p * ω p) t := by
      rw [PiLp.inner_apply]
      simp only [hreal]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hinner]
  have hR2 : charFun (Measure.map (WithLp.toLp 2 : (ι → ℝ) → PiLp 2 (fun _ : ι => ℝ))
        (Measure.pi (fun _ : ι => gaussianReal 0 1)))
        (WithLp.toLp 2 (fun i : ι => t * c i))
      = ∏ i : ι, charFun (gaussianReal 0 1) (t * c i) := by
    rw [MeasureTheory.charFun_pi]
  rw [hL1, hint, hI2, hR2]
  simp only [ProbabilityTheory.charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  have hterm : ∀ x : ι, (↑(t * c x) * ↑(0:ℝ) * Complex.I - ↑↑(1:NNReal) * ↑(t * c x) ^ 2 / 2)
      = Complex.ofReal (-(t * c x) ^ 2 / 2) := by
    intro x
    push_cast
    ring
  have hpush : (∑ x : ι, Complex.ofReal (-(t * c x) ^ 2 / 2))
      = Complex.ofReal (∑ x : ι, (-(t * c x) ^ 2 / 2)) := by
    push_cast
    rfl
  have hSv : (v : ℝ) = ∑ p : ι, (c p) ^ 2 := by
    rw [← hv]
  have hreal_sum : ∑ x : ι, (-(t * c x) ^ 2 / 2) = -(t ^ 2) * (v : ℝ) / 2 := by
    have hpt : ∀ x : ι, (-(t * c x) ^ 2 / 2) = (-(t ^ 2) * (c x) ^ 2) / 2 := by
      intro x
      ring
    simp only [hpt]
    rw [← Finset.sum_div, ← Finset.mul_sum, ← hSv]
  have hsum : ∑ x : ι, (↑(t * c x) * ↑(0:ℝ) * Complex.I - ↑↑(1:NNReal) * ↑(t * c x) ^ 2 / 2)
      = Complex.ofReal (-(t ^ 2) * (v : ℝ) / 2) := by
    simp only [hterm]
    rw [hpush, hreal_sum]
  rw [hsum]
  rw [← hv]
  push_cast
  try ring
  /- @proof-region region.target-node.session.441f9140935d0504 end -/

end Statlib.Imported

