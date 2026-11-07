import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_287517620_f22d7735_a6b10e08

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
theorem statopia_math_node_2651146195_a70c9c7a : ∀ (p : ℕ) (hp : 0 < p)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : (Fin p → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (W U : Ω → (Fin p → ℝ)) (V : Ω → Fin p → ℝ) (Q : Fin p → Fin p → Fin p → Ω → ℝ)
    (hU : ∀ k : Fin p, Measurable (fun x : Ω => U x k))
    (hV : ∀ j : Fin p, Measurable (fun x : Ω => V x j))
    (hQnn : ∀ (j k l : Fin p) (x : Ω), 0 ≤ Q j k l x)
    (hQmeas : ∀ (j k l : Fin p), AEStronglyMeasurable (fun x : Ω => Q j k l x) μ)
    (hQmaj : ∀ (x : Ω) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ j k l : Fin p,
      |(iteratedFDeriv ℝ 3 f (W x + s • U x))
          (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))| ≤ Q j k l x)
    (hInt1 : ∀ j : Fin p, Integrable (fun x : Ω =>
      (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j) μ)
    (hInt2 : ∀ j : Fin p, Integrable (fun x : Ω =>
      (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x j) μ)
    (hInt3 : ∀ j k : Fin p, Integrable (fun x : Ω =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
        (Pi.single k (1 : ℝ)) * U x k * V x j) μ)
    (hInt4 : Integrable (fun x : Ω =>
      ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
        Q j k l x * |U x k| * |U x l| * |V x j|) μ)
    (hE0 : ∀ j : Fin p,
      (∫ x, (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x j ∂μ) = 0)
    (hE1 : ∀ j k : Fin p,
      (∫ x, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
        (Pi.single k (1 : ℝ)) * U x k * V x j ∂μ) = 0),
    |∫ x, ∑ j : Fin p, (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j ∂μ|
      ≤ (1 / 2) * ∫ x, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          Q j k l x * |U x k| * |U x l| * |V x j| ∂μ := by
  /- @proof-region region.target-node.session.e7b5749f3527610d begin -/
  intro p hp Ω _ μ _ f hf W U V Q hU hV hQnn hQmeas hQmaj hInt1 hInt2 hInt3 hInt4 hE0 hE1
  have hMint : ∀ j : Fin p, Integrable (fun x : Ω => ∑ k : Fin p, ∑ l : Fin p,
      Q j k l x * |U x k| * |U x l| * |V x j|) μ := by
    intro j
    have hbase : ∀ k l : Fin p, AEStronglyMeasurable (fun x : Ω =>
        Q j k l x * |U x k| * |U x l| * |V x j|) μ := by
      intro k l
      exact (((hQmeas j k l).mul (hU k).abs.aestronglyMeasurable).mul
        (hU l).abs.aestronglyMeasurable).mul (hV j).abs.aestronglyMeasurable
    have hmeasS : AEStronglyMeasurable (fun x : Ω => (∑ k : Fin p, ∑ l : Fin p,
        fun y : Ω => Q j k l y * |U y k| * |U y l| * |V y j|) x) μ :=
      Finset.aestronglyMeasurable_sum (s := (Finset.univ : Finset (Fin p)))
        (f := fun k : Fin p => ∑ l : Fin p, fun y : Ω =>
          Q j k l y * |U y k| * |U y l| * |V y j|)
        (fun k _ => Finset.aestronglyMeasurable_sum (s := (Finset.univ : Finset (Fin p)))
          (f := fun l : Fin p => fun y : Ω => Q j k l y * |U y k| * |U y l| * |V y j|)
          (fun l _ => hbase k l))
    have hmeas : AEStronglyMeasurable (fun x : Ω => ∑ k : Fin p, ∑ l : Fin p,
        Q j k l x * |U x k| * |U x l| * |V x j|) μ := by
      simpa only [Finset.sum_apply] using hmeasS
    refine Integrable.mono' hInt4 hmeas ?_
    filter_upwards with x

    have hMnn : (0 : ℝ) ≤ ∑ k : Fin p, ∑ l : Fin p,
        Q j k l x * |U x k| * |U x l| * |V x j| := by
      apply Finset.sum_nonneg
      intro k _
      apply Finset.sum_nonneg
      intro l _
      exact mul_nonneg (mul_nonneg (mul_nonneg (hQnn j k l x) (abs_nonneg _))
        (abs_nonneg _)) (abs_nonneg _)
    have hle : (∑ k : Fin p, ∑ l : Fin p, Q j k l x * |U x k| * |U x l| * |V x j|)
        ≤ ∑ j' : Fin p, ∑ k : Fin p, ∑ l : Fin p,
            Q j' k l x * |U x k| * |U x l| * |V x j'| := by
      refine Finset.single_le_sum (f := fun j' : Fin p => ∑ k : Fin p, ∑ l : Fin p,
          Q j' k l x * |U x k| * |U x l| * |V x j'|) ?_ (Finset.mem_univ j)
      intro j' _
      apply Finset.sum_nonneg
      intro k _
      apply Finset.sum_nonneg
      intro l _
      exact mul_nonneg (mul_nonneg (mul_nonneg (hQnn j' k l x) (abs_nonneg _))
        (abs_nonneg _)) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hMnn]
    exact hle
  have hkey : ∀ j : Fin p,
      |∫ x, (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j ∂μ|
        ≤ (1 / 2) * ∫ x, ∑ k : Fin p, ∑ l : Fin p,
            Q j k l x * |U x k| * |U x l| * |V x j| ∂μ := by
    intro j
    have hcongr : (∫ x, (∑ k : Fin p, ∑ l : Fin p,
          Q j k l x * |U x k| * |U x l|) * |V x j| ∂μ)
        = ∫ x, ∑ k : Fin p, ∑ l : Fin p,
            Q j k l x * |U x k| * |U x l| * |V x j| ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only [Finset.sum_mul]
    have hmaj : ∀ (x : Ω) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ k l : Fin p,
        |(iteratedFDeriv ℝ 3 f (W x + s • U x))
            (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))| ≤ Q j k l x := by
      intro x s hs k l
      exact hQmaj x s hs j k l
    have hmain := statopia_math_node_287517620_f22d7735 p hp Ω μ f hf j W U
      (fun x => V x j) (fun k l x => Q j k l x) hU (hV j)
      (fun k l x => hQnn j k l x) hmaj (hInt1 j) (hInt2 j) (fun k => hInt3 j k)
      (hMint j) (hE0 j) (fun k => hE1 j k)
    rw [hcongr] at hmain
    exact hmain
  have hIntsum : (∫ x, ∑ j : Fin p,
        (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j ∂μ)
      = ∑ j : Fin p, ∫ x,
          (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j ∂μ :=
    integral_finset_sum Finset.univ (fun j _ => hInt1 j)
  have hMsum : (∫ x, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
        Q j k l x * |U x k| * |U x l| * |V x j| ∂μ)
      = ∑ j : Fin p, ∫ x, (∑ k : Fin p, ∑ l : Fin p,
          Q j k l x * |U x k| * |U x l| * |V x j|) ∂μ :=
    integral_finset_sum Finset.univ (fun j _ => hMint j)
  calc |∫ x, ∑ j : Fin p, (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j ∂μ|
      = |∑ j : Fin p, ∫ x,
          (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j ∂μ| := by
        rw [hIntsum]
    _ ≤ ∑ j : Fin p, |∫ x,
          (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j ∂μ| :=
        Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j : Fin p =>
          ∫ x, (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x j ∂μ)
    _ ≤ ∑ j : Fin p, (1 / 2) * ∫ x, (∑ k : Fin p, ∑ l : Fin p,
          Q j k l x * |U x k| * |U x l| * |V x j|) ∂μ :=
        Finset.sum_le_sum (fun j _ => hkey j)
    _ = (1 / 2) * ∑ j : Fin p, ∫ x, (∑ k : Fin p, ∑ l : Fin p,
          Q j k l x * |U x k| * |U x l| * |V x j|) ∂μ := by
        rw [Finset.mul_sum]
    _ = (1 / 2) * ∫ x, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          Q j k l x * |U x k| * |U x l| * |V x j| ∂μ := by
        rw [hMsum]
  /- @proof-region region.target-node.session.e7b5749f3527610d end -/

end

end Statlib.Imported

