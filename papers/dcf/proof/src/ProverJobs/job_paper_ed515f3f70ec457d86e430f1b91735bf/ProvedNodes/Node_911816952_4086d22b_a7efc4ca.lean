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
theorem statopia_math_node_911816952_4086d22b : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m p : ℕ) (d : ℝ) (muY : Fin p → ℝ)
    (Y G : Fin m → Ω → Fin p → ℝ)
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hGmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, G i ω j ∂P = muY j)
    (hYint : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => Y i ω j) P)
    (hGint : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => G i ω j) P)
    (v t : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ht0 : 0 < t) (ht1 : t < 1)
    (i : Fin m) (j : Fin p) (Ψ : Ω × Ω → ℝ)
    (hΨm : Measurable Ψ)
    (hΨb : ∃ C : ℝ, ∀ x : Ω × Ω, |Ψ x| ≤ C)
    (hΨind : IndepFun Ψ (fun x : Ω × Ω => (Y i x.1, (G i x.1, G i x.2)))
      (P.prod P)),
    ∫ x, Ψ x *
      ((Real.sqrt (m : ℝ))⁻¹ * d *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))) ∂(P.prod P) = 0 := by
  /- @proof-region region.target-node.session.3c491c528d4652c0 begin -/
  intro Ω _ P _ m p d muY Y G hYm hGm hYmean hGmean hYint hGint v t hv0 hv1 ht0 ht1 i j Ψ hΨm hΨb hΨind
  set A : Ω × Ω → ℝ := fun x => Y i x.1 j - muY j with hA
  set Ab : Ω × Ω → ℝ := fun x => G i x.1 j - muY j with hAb
  set B : Ω × Ω → ℝ := fun x => G i x.2 j - muY j with hB
  set Z : Ω × Ω → ℝ := fun x =>
    (Real.sqrt (m : ℝ))⁻¹ * d *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A x + Real.sqrt (1 - v) * Ab x) -
        (2 * Real.sqrt (1 - t))⁻¹ * B x) with hZ
  change ∫ x : Ω × Ω, Ψ x * Z x ∂(P.prod P) = 0
  have hAint : Integrable A (P.prod P) :=
    ((hYint i j).comp_fst P).sub (integrable_const (muY j))
  have hAbint : Integrable Ab (P.prod P) :=
    ((hGint i j).comp_fst P).sub (integrable_const (muY j))
  have hBint : Integrable B (P.prod P) :=
    ((hGint i j).comp_snd P).sub (integrable_const (muY j))
  have hfst0 : ∀ f : Ω → ℝ, Integrable f P → ∫ ω, f ω ∂P = 0 →
      ∫ x : Ω × Ω, f x.1 ∂(P.prod P) = 0 := by
    intro f hfint hf0
    have hmap : Measure.map (Prod.fst : Ω × Ω → Ω) (P.prod P) = P :=
      (MeasureTheory.measurePreserving_fst (μ := P) (ν := P)).map_eq
    have haesm : AEStronglyMeasurable f (Measure.map (Prod.fst : Ω × Ω → Ω) (P.prod P)) := by
      rw [hmap]
      exact hfint.aestronglyMeasurable
    have h := MeasureTheory.integral_map (φ := (Prod.fst : Ω × Ω → Ω)) (μ := P.prod P) (f := f)
      measurable_fst.aemeasurable haesm
    rw [hmap, hf0] at h
    exact h.symm
  have hYA0 : ∫ ω : Ω, (Y i ω j - muY j) ∂P = 0 := by
    rw [MeasureTheory.integral_sub (hYint i j) (integrable_const (muY j)), hYmean i j]
    simp
  have hGA0 : ∫ ω : Ω, (G i ω j - muY j) ∂P = 0 := by
    rw [MeasureTheory.integral_sub (hGint i j) (integrable_const (muY j)), hGmean i j]
    simp
  have hzeroA : ∫ x : Ω × Ω, A x ∂(P.prod P) = 0 :=
    hfst0 (fun ω => Y i ω j - muY j) ((hYint i j).sub (integrable_const (muY j))) hYA0
  have hzeroAb : ∫ x : Ω × Ω, Ab x ∂(P.prod P) = 0 :=
    hfst0 (fun ω => G i ω j - muY j) ((hGint i j).sub (integrable_const (muY j))) hGA0
  have hzeroB : ∫ x : Ω × Ω, B x ∂(P.prod P) = 0 := by
    rw [MeasureTheory.integral_prod B hBint]
    simp [hB, hGA0]
  have hcoefA : ∫ x : Ω × Ω, Real.sqrt v * A x ∂(P.prod P) = 0 := by
    rw [MeasureTheory.integral_const_mul, hzeroA, mul_zero]
  have hcoefAb : ∫ x : Ω × Ω, Real.sqrt (1 - v) * Ab x ∂(P.prod P) = 0 := by
    rw [MeasureTheory.integral_const_mul, hzeroAb, mul_zero]
  have hsum0 : ∫ x : Ω × Ω, (Real.sqrt v * A x + Real.sqrt (1 - v) * Ab x) ∂(P.prod P) = 0 := by
    rw [MeasureTheory.integral_add (hAint.const_mul (Real.sqrt v))
      (hAbint.const_mul (Real.sqrt (1 - v))), hcoefA, hcoefAb, add_zero]
  have hpart1 : ∫ x : Ω × Ω,
      (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A x + Real.sqrt (1 - v) * Ab x) ∂(P.prod P) = 0 := by
    rw [MeasureTheory.integral_const_mul, hsum0, mul_zero]
  have hpart2 : ∫ x : Ω × Ω, (2 * Real.sqrt (1 - t))⁻¹ * B x ∂(P.prod P) = 0 := by
    rw [MeasureTheory.integral_const_mul, hzeroB, mul_zero]
  have hfF : Integrable (fun x : Ω × Ω =>
      (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A x + Real.sqrt (1 - v) * Ab x)) (P.prod P) :=
    ((hAint.const_mul (Real.sqrt v)).add (hAbint.const_mul (Real.sqrt (1 - v)))).const_mul
      ((2 * Real.sqrt t)⁻¹)
  have hgF : Integrable (fun x : Ω × Ω => (2 * Real.sqrt (1 - t))⁻¹ * B x) (P.prod P) :=
    hBint.const_mul ((2 * Real.sqrt (1 - t))⁻¹)
  have hF0 : ∫ x : Ω × Ω,
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A x + Real.sqrt (1 - v) * Ab x) -
        (2 * Real.sqrt (1 - t))⁻¹ * B x) ∂(P.prod P) = 0 := by
    have hsub : ∫ x : Ω × Ω,
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A x + Real.sqrt (1 - v) * Ab x) -
          (2 * Real.sqrt (1 - t))⁻¹ * B x) ∂(P.prod P)
        = ∫ x : Ω × Ω,
            (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A x + Real.sqrt (1 - v) * Ab x) ∂(P.prod P)
          - ∫ x : Ω × Ω, (2 * Real.sqrt (1 - t))⁻¹ * B x ∂(P.prod P) :=
      MeasureTheory.integral_sub hfF hgF
    rw [hsub, hpart1, hpart2, sub_zero]
  have hZint : Integrable Z (P.prod P) := by
    rw [hZ]
    exact (hfF.sub hgF).const_mul ((Real.sqrt (m : ℝ))⁻¹ * d)
  have hZzero : ∫ x : Ω × Ω, Z x ∂(P.prod P) = 0 := by
    rw [hZ, MeasureTheory.integral_const_mul, hF0, mul_zero]
  set Blk : Ω × Ω → (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) :=
    fun x => (Y i x.1, (G i x.1, G i x.2)) with hBlk
  set g : (Fin p → ℝ) × ((Fin p → ℝ) × (Fin p → ℝ)) → ℝ := fun y =>
    (Real.sqrt (m : ℝ))⁻¹ * d *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (y.1 j - muY j) + Real.sqrt (1 - v) * (y.2.1 j - muY j)) -
        (2 * Real.sqrt (1 - t))⁻¹ * (y.2.2 j - muY j)) with hg
  have hZg : Z = fun x => g (Blk x) := by
    funext x
    simp only [hZ, hg, hBlk, hA, hAb, hB]
  have hgm : Measurable g := by
    rw [hg]
    fun_prop
  have hZaesm : AEStronglyMeasurable Z (P.prod P) := hZint.aestronglyMeasurable
  have hind : IndepFun Ψ Z (P.prod P) := by
    rw [hZg]
    exact hΨind.comp measurable_id hgm
  have hfac : ∫ x : Ω × Ω, Ψ x * Z x ∂(P.prod P)
      = (∫ x : Ω × Ω, Ψ x ∂(P.prod P)) * ∫ x : Ω × Ω, Z x ∂(P.prod P) :=
    ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hind hΨm.aestronglyMeasurable hZaesm
  rw [hfac, hZzero, mul_zero]
  /- @proof-region region.target-node.session.3c491c528d4652c0 end -/

end

end Statlib.Imported

