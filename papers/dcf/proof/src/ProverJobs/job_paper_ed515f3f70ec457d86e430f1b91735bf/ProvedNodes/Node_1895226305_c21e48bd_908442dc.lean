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
theorem statopia_math_node_1895226305_c21e48bd : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
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
     ContDiff ℝ 3 kappa →
       AEStronglyMeasurable
         (fun q : ℝ × (Ω × Ω) =>
           ∑ j : Fin p, ∑ i : Fin n,
             (fderiv ℝ kappa (Z q.1 q.2)) (Pi.single j (1 : ℝ)) *
               Zdotstar q.1 q.2 i j)
         ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P))) := by
  /- @proof-region region.target-node.session.7e9255a1b9805182 begin -/
  intro Ω _ P _ n m p delta muX muY X Y F G phi0 hphi0_cont hphi0_left hphi0_right
    hphi0_range hn hm hp hlogp hXm hYm hFm hGm hX3 hF3 phi1 phi2 hphi1 hphi2 v hv0 hv1 y
  intro phi beta Zstar Zstarstar Z Zdotstar kappa hkap
  have hsqrt : Measurable (Real.sqrt : ℝ → ℝ) := Real.continuous_sqrt.measurable
  have hXc : ∀ (i : Fin n) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => X i q.2.1 j) := by
    intro i j
    exact ((measurable_pi_apply j).comp (hXm i)).comp (measurable_fst.comp measurable_snd)
  have hFc : ∀ (i : Fin n) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => F i q.2.1 j) := by
    intro i j
    exact ((measurable_pi_apply j).comp (hFm i)).comp (measurable_fst.comp measurable_snd)
  have hFc2 : ∀ (i : Fin n) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => F i q.2.2 j) := by
    intro i j
    exact ((measurable_pi_apply j).comp (hFm i)).comp (measurable_snd.comp measurable_snd)
  have hYc : ∀ (i : Fin m) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => Y i q.2.1 j) := by
    intro i j
    exact ((measurable_pi_apply j).comp (hYm i)).comp (measurable_fst.comp measurable_snd)
  have hGc : ∀ (i : Fin m) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => G i q.2.1 j) := by
    intro i j
    exact ((measurable_pi_apply j).comp (hGm i)).comp (measurable_fst.comp measurable_snd)
  have hGc2 : ∀ (i : Fin m) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => G i q.2.2 j) := by
    intro i j
    exact ((measurable_pi_apply j).comp (hGm i)).comp (measurable_snd.comp measurable_snd)
  have ht1 : Measurable (fun q : ℝ × (Ω × Ω) => Real.sqrt q.1) := hsqrt.comp measurable_fst
  have ht2 : Measurable (fun q : ℝ × (Ω × Ω) => Real.sqrt (1 - q.1)) :=
    hsqrt.comp (measurable_const.sub measurable_fst)
  have hZstar : ∀ (i : Fin n) (j : Fin p),
      Measurable (fun q : ℝ × (Ω × Ω) => Zstar q.1 q.2 i j) := by
    intro i j
    dsimp only [Zstar]
    have hX0 : Measurable (fun q : ℝ × (Ω × Ω) => X i q.2.1 j - muX j) :=
      (hXc i j).sub measurable_const
    have hF0 : Measurable (fun q : ℝ × (Ω × Ω) => F i q.2.1 j - muX j) :=
      (hFc i j).sub measurable_const
    have hF1 : Measurable (fun q : ℝ × (Ω × Ω) => F i q.2.2 j - muX j) :=
      (hFc2 i j).sub measurable_const
    have hXv : Measurable (fun q : ℝ × (Ω × Ω) => Real.sqrt v * (X i q.2.1 j - muX j)) :=
      measurable_const.mul hX0
    have hFv : Measurable
        (fun q : ℝ × (Ω × Ω) => Real.sqrt (1 - v) * (F i q.2.1 j - muX j)) :=
      measurable_const.mul hF0
    have hinner : Measurable (fun q : ℝ × (Ω × Ω) =>
        Real.sqrt v * (X i q.2.1 j - muX j) +
          Real.sqrt (1 - v) * (F i q.2.1 j - muX j)) := hXv.add hFv
    have hfirst : Measurable (fun q : ℝ × (Ω × Ω) =>
        Real.sqrt q.1 * (Real.sqrt v * (X i q.2.1 j - muX j) +
          Real.sqrt (1 - v) * (F i q.2.1 j - muX j))) := ht1.mul hinner
    have hsecond : Measurable
        (fun q : ℝ × (Ω × Ω) => Real.sqrt (1 - q.1) * (F i q.2.2 j - muX j)) :=
      ht2.mul hF1
    exact measurable_const.mul (hfirst.add hsecond)
  have hZstarstar : ∀ (i : Fin m) (j : Fin p),
      Measurable (fun q : ℝ × (Ω × Ω) => Zstarstar q.1 q.2 i j) := by
    intro i j
    dsimp only [Zstarstar]
    have hY0 : Measurable (fun q : ℝ × (Ω × Ω) => Y i q.2.1 j - muY j) :=
      (hYc i j).sub measurable_const
    have hG0 : Measurable (fun q : ℝ × (Ω × Ω) => G i q.2.1 j - muY j) :=
      (hGc i j).sub measurable_const
    have hG1 : Measurable (fun q : ℝ × (Ω × Ω) => G i q.2.2 j - muY j) :=
      (hGc2 i j).sub measurable_const
    have hYv : Measurable (fun q : ℝ × (Ω × Ω) => Real.sqrt v * (Y i q.2.1 j - muY j)) :=
      measurable_const.mul hY0
    have hGv : Measurable
        (fun q : ℝ × (Ω × Ω) => Real.sqrt (1 - v) * (G i q.2.1 j - muY j)) :=
      measurable_const.mul hG0
    have hinner : Measurable (fun q : ℝ × (Ω × Ω) =>
        Real.sqrt v * (Y i q.2.1 j - muY j) +
          Real.sqrt (1 - v) * (G i q.2.1 j - muY j)) := hYv.add hGv
    have hfirst : Measurable (fun q : ℝ × (Ω × Ω) =>
        Real.sqrt q.1 * (Real.sqrt v * (Y i q.2.1 j - muY j) +
          Real.sqrt (1 - v) * (G i q.2.1 j - muY j))) := ht1.mul hinner
    have hsecond : Measurable
        (fun q : ℝ × (Ω × Ω) => Real.sqrt (1 - q.1) * (G i q.2.2 j - muY j)) :=
      ht2.mul hG1
    exact measurable_const.mul (hfirst.add hsecond)
  have hZdot : ∀ (i : Fin n) (j : Fin p),
      Measurable (fun q : ℝ × (Ω × Ω) => Zdotstar q.1 q.2 i j) := by
    intro i j
    dsimp only [Zdotstar]
    have hX0 : Measurable (fun q : ℝ × (Ω × Ω) => X i q.2.1 j - muX j) :=
      (hXc i j).sub measurable_const
    have hF0 : Measurable (fun q : ℝ × (Ω × Ω) => F i q.2.1 j - muX j) :=
      (hFc i j).sub measurable_const
    have hF1 : Measurable (fun q : ℝ × (Ω × Ω) => F i q.2.2 j - muX j) :=
      (hFc2 i j).sub measurable_const
    have hXv : Measurable (fun q : ℝ × (Ω × Ω) => Real.sqrt v * (X i q.2.1 j - muX j)) :=
      measurable_const.mul hX0
    have hFv : Measurable
        (fun q : ℝ × (Ω × Ω) => Real.sqrt (1 - v) * (F i q.2.1 j - muX j)) :=
      measurable_const.mul hF0
    have hinner : Measurable (fun q : ℝ × (Ω × Ω) =>
        Real.sqrt v * (X i q.2.1 j - muX j) +
          Real.sqrt (1 - v) * (F i q.2.1 j - muX j)) := hXv.add hFv
    have h2t : Measurable (fun q : ℝ × (Ω × Ω) => (2 * Real.sqrt q.1)⁻¹) :=
      (measurable_const.mul ht1).inv
    have h2t' : Measurable (fun q : ℝ × (Ω × Ω) => (2 * Real.sqrt (1 - q.1))⁻¹) :=
      (measurable_const.mul ht2).inv
    have hA : Measurable (fun q : ℝ × (Ω × Ω) =>
        (2 * Real.sqrt q.1)⁻¹ * (Real.sqrt v * (X i q.2.1 j - muX j) +
          Real.sqrt (1 - v) * (F i q.2.1 j - muX j))) := h2t.mul hinner
    have hB : Measurable (fun q : ℝ × (Ω × Ω) =>
        (2 * Real.sqrt (1 - q.1))⁻¹ * (F i q.2.2 j - muX j)) := h2t'.mul hF1
    exact measurable_const.mul (hA.sub hB)
  have hZ : Measurable (fun q : ℝ × (Ω × Ω) => Z q.1 q.2) := by
    rw [measurable_pi_iff]
    intro j
    dsimp only [Z]
    have h1 : Measurable (fun q : ℝ × (Ω × Ω) => ∑ i : Fin n, Zstar q.1 q.2 i j) := by
      apply Finset.measurable_sum
      intro i _
      exact hZstar i j
    have h2 : Measurable (fun q : ℝ × (Ω × Ω) => ∑ i : Fin m, Zstarstar q.1 q.2 i j) := by
      apply Finset.measurable_sum
      intro i _
      exact hZstarstar i j
    exact h1.add h2
  have hfd : ∀ j : Fin p, Measurable (fun q : ℝ × (Ω × Ω) =>
      (fderiv ℝ kappa (Z q.1 q.2)) (Pi.single j (1 : ℝ))) := by
    intro j
    have hpair : Continuous (fun w : Fin p → ℝ => (w, (Pi.single j (1 : ℝ) : Fin p → ℝ))) := by
      continuity
    have hcont : Continuous (fun w : Fin p → ℝ => (fderiv ℝ kappa w) (Pi.single j (1 : ℝ))) :=
      (ContDiff.continuous_fderiv_apply (f := kappa) hkap (by norm_num)).comp hpair
    exact hcont.measurable.comp hZ
  have hterm : ∀ (j : Fin p) (i : Fin n), Measurable (fun q : ℝ × (Ω × Ω) =>
      (fderiv ℝ kappa (Z q.1 q.2)) (Pi.single j (1 : ℝ)) * Zdotstar q.1 q.2 i j) := by
    intro j i
    exact (hfd j).mul (hZdot i j)
  have hsum : Measurable (fun q : ℝ × (Ω × Ω) =>
      ∑ j : Fin p, ∑ i : Fin n,
        (fderiv ℝ kappa (Z q.1 q.2)) (Pi.single j (1 : ℝ)) * Zdotstar q.1 q.2 i j) := by
    apply Finset.measurable_sum
    intro j _
    apply Finset.measurable_sum
    intro i _
    exact hterm j i
  exact hsum.aestronglyMeasurable
  /- @proof-region region.target-node.session.7e9255a1b9805182 end -/

end

end Statlib.Imported

