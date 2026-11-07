import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1895226305_c21e48bd_908442dc
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1967109576_c7239acb_4f2497e8
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3923401065_5b4914e1_f95c2434
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_4261448272_13a285fe_bd8a0429

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
theorem statopia_math_node_4044352104_35d188c9 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (phi0 : ℝ → ℝ)
    (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
    (hXm : ∀ i : Fin n, Measurable (X i)) (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i)) (hGm : ∀ i : Fin m, Measurable (G i))
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (y : Fin p → ℝ),
    (let phi : ℝ := min phi1 phi2
     let beta : ℝ := phi * Real.log (p : ℝ)
     let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (n : ℝ))⁻¹ *
         (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
             Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
           Real.sqrt (1 - t) * (F i x.2 j - muX j))
     let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
             Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
           Real.sqrt (1 - t) * (G i x.2 j - muY j))
     let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
       (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
     let Zdotstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (n : ℝ))⁻¹ *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) +
             Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
           (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
     let kappa : (Fin p → ℝ) → ℝ := fun w =>
       phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
     Integrable (fun q : ℝ × (Ω × Ω) =>
         ∑ j : Fin p, ∑ i : Fin n,
           (fderiv ℝ kappa (Z q.1 q.2)) (Pi.single j (1 : ℝ)) * Zdotstar q.1 q.2 i j)
       ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P))) := by
  /- @proof-region region.target-node.session.79c7c790efc92f96 begin -/
  intro Ω _ P _ n m p delta muX muY X Y F G phi0
    hphi0_cont hphi0_left hphi0_right hphi0_range
    hn hm hp hlogp hXm hYm hFm hGm hX3 hF3
    phi1 phi2 hphi1 hphi2 v hv0 hv1 y
  let phi : ℝ := min phi1 phi2
  let beta : ℝ := phi * Real.log (p : ℝ)
  let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
          Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
        Real.sqrt (1 - t) * (F i x.2 j - muX j))
  let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
          Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
        Real.sqrt (1 - t) * (G i x.2 j - muY j))
  let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
    (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
  let Zdotstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) +
          Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
        (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
  let kappa : (Fin p → ℝ) → ℝ := fun w =>
    phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
  have hmin1 : (1:ℝ) ≤ phi := le_min hphi1 hphi2
  have hpne1 : p ≠ 1 := by
    rintro rfl
    exact absurd hlogp (by simp)
  have hp2 : 2 ≤ p := by omega
  obtain ⟨Cκ, hCκpos, hCκ⟩ :=
    statopia_math_node_1967109576_c7239acb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  have hkap : ContDiff ℝ 3 kappa := by
    obtain ⟨h1, -⟩ := statopia_math_node_2194576110_d2ad0cef p hp2 phi hmin1 phi0
      hphi0_cont hphi0_left hphi0_right hphi0_range y
    simpa [kappa, beta] using h1
  show Integrable
    (fun q : ℝ × (Ω × Ω) =>
      ∑ j : Fin p, ∑ i : Fin n,
        (fderiv ℝ kappa (Z q.1 q.2)) (Pi.single j (1 : ℝ)) * Zdotstar q.1 q.2 i j)
    ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P))
  set W : ℝ → ℝ := fun t => (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹ with hW
  set Hf : Ω × Ω → ℝ := fun x =>
    ∑ j : Fin p, ∑ i : Fin n,
      (|X i x.1 j - muX j| + |F i x.1 j - muX j| + |F i x.2 j - muX j|) with hHf
  have hIntW : Integrable W (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [hW]
    exact statopia_math_node_4261448272_13a285fe
  have hIntH : Integrable Hf (P.prod P) := by
    have hob : Integrable (fun _ : Ω => (1 : ℝ)) P :=
      MeasureTheory.Integrable.of_bound measurable_const.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun _ => by simp))
    have habs_le : ∀ c : ℝ, |c| ≤ 1 + |c| ^ 3 := by
      intro c
      nlinarith [sq_nonneg (|c| - 1), sq_nonneg |c|, abs_nonneg c,
        mul_nonneg (abs_nonneg c) (sq_nonneg (|c| - 1))]
    have hXabs : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j|) P := by
      intro i j
      refine MeasureTheory.Integrable.mono' (hob.add (hX3 i j)) ?_ ?_
      · have hm : Measurable (fun ω : Ω => X i ω j - muX j) :=
          ((measurable_pi_apply j).comp (hXm i)).sub measurable_const
        exact (continuous_abs.measurable.comp hm).aestronglyMeasurable
      · filter_upwards with ω
        simpa only [Real.norm_eq_abs, abs_abs] using habs_le (X i ω j - muX j)
    have hFabs : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j|) P := by
      intro i j
      refine MeasureTheory.Integrable.mono' (hob.add (hF3 i j)) ?_ ?_
      · have hm : Measurable (fun ω : Ω => F i ω j - muX j) :=
          ((measurable_pi_apply j).comp (hFm i)).sub measurable_const
        exact (continuous_abs.measurable.comp hm).aestronglyMeasurable
      · filter_upwards with ω
        simpa only [Real.norm_eq_abs, abs_abs] using habs_le (F i ω j - muX j)
    rw [hHf]
    refine MeasureTheory.integrable_finset_sum (Finset.univ : Finset (Fin p)) ?_
    intro j _
    refine MeasureTheory.integrable_finset_sum (Finset.univ : Finset (Fin n)) ?_
    intro i _
    exact (MeasureTheory.Integrable.add
        (MeasureTheory.Integrable.comp_fst (hXabs i j) P)
        (MeasureTheory.Integrable.comp_fst (hFabs i j) P)).add
      (MeasureTheory.Integrable.comp_snd (hFabs i j) P)
  have hIntg : Integrable
      (fun q : ℝ × (Ω × Ω) => Cκ * phi * (Real.sqrt (n : ℝ))⁻¹ * (W q.1 * Hf q.2))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P)) :=
    (MeasureTheory.Integrable.mul_prod hIntW hIntH).const_mul
      (Cκ * phi * (Real.sqrt (n : ℝ))⁻¹)
  have hmeas : AEStronglyMeasurable
      (fun q : ℝ × (Ω × Ω) =>
        ∑ j : Fin p, ∑ i : Fin n,
          (fderiv ℝ kappa (Z q.1 q.2)) (Pi.single j (1 : ℝ)) * Zdotstar q.1 q.2 i j)
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P)) :=
    statopia_math_node_1895226305_c21e48bd Ω P n m p delta muX muY X Y F G phi0
      hphi0_cont hphi0_left hphi0_right hphi0_range hn hm hp hlogp
      hXm hYm hFm hGm hX3 hF3 phi1 phi2 hphi1 hphi2 v hv0 hv1 y hkap
  have hCκ' : ∀ (w : Fin p → ℝ) (j : Fin p),
      |(fderiv ℝ kappa w) (Pi.single j (1 : ℝ))| ≤ Cκ * phi := by
    intro w j
    simpa [kappa, beta] using hCκ p hp2 phi hmin1 y w j
  have hbound : ∀ᵐ q ∂((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P)),
      ‖(∑ j : Fin p, ∑ i : Fin n,
          (fderiv ℝ kappa (Z q.1 q.2)) (Pi.single j (1 : ℝ)) * Zdotstar q.1 q.2 i j)‖
        ≤ Cκ * phi * (Real.sqrt (n : ℝ))⁻¹ * (W q.1 * Hf q.2) := by
    rw [hW, hHf]
    exact statopia_math_node_3923401065_5b4914e1 Ω P n m p delta muX muY X Y F G phi0
      hphi0_cont hphi0_left hphi0_right hphi0_range hn hm hp hlogp
      hXm hYm hFm hGm hX3 hF3 phi1 phi2 hphi1 hphi2 v hv0 hv1 y Cκ hCκ'
  exact MeasureTheory.Integrable.mono' hIntg hmeas hbound
  /- @proof-region region.target-node.session.79c7c790efc92f96 end -/

end

end Statlib.Imported

