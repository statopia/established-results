import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2948575112_cf5ddfcb_f79bf72f
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_478009398_9cbe8093_66d7da48

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
theorem statopia_math_node_351002483_30a1f705 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ) (phi0 : ℝ → ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hFL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => F i ω j) 2 P)
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hFmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, F i ω j ∂P = muX j)
    (hphi0_smooth : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1),
    ∀ (phi1 phi2 : ℝ), 1 ≤ phi1 → 1 ≤ phi2 →
    ∀ (v : ℝ), 0 ≤ v → v ≤ 1 → ∀ (y : Fin p → ℝ),
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
       ∀ (t : ℝ), 0 < t → t < 1 → ∀ (i : Fin n) (j : Fin p),
         Integrable (fun x : Ω × Ω =>
           (fderiv ℝ kappa (fun k : Fin p => Z t x k - Zstar t x i k)) (Pi.single j (1 : ℝ)) *
             Zdotstar t x i j) (P.prod P) ∧
         (∫ x : Ω × Ω,
           (fderiv ℝ kappa (fun k : Fin p => Z t x k - Zstar t x i k)) (Pi.single j (1 : ℝ)) *
             Zdotstar t x i j ∂(P.prod P)) = 0) := by
  /- @proof-region region.target-node.session.8298b47e63d88240 begin -/
  intro Ω hMS P hProb n m p delta muX muY X Y F G phi0
    hn hm hp hlogp hXm hYm hFm hGm hindep
    hXL2 hFL2 hX3 hF3 hXmean hFmean hphi0_smooth hphi0_left hphi0_right hphi0_range
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
  show ∀ (t : ℝ), 0 < t → t < 1 → ∀ (i : Fin n) (j : Fin p),
      Integrable (fun x : Ω × Ω =>
        (fderiv ℝ kappa (fun k : Fin p => Z t x k - Zstar t x i k)) (Pi.single j (1 : ℝ)) *
          Zdotstar t x i j) (P.prod P) ∧
      (∫ x : Ω × Ω,
        (fderiv ℝ kappa (fun k : Fin p => Z t x k - Zstar t x i k)) (Pi.single j (1 : ℝ)) *
          Zdotstar t x i j ∂(P.prod P)) = 0
  intro t ht0 ht1 i j
  have hphi1phi : (1 : ℝ) ≤ phi := le_min hphi1 hphi2
  have hbetanonneg : (0 : ℝ) ≤ beta := mul_nonneg (le_trans zero_le_one hphi1phi) hlogp.le
  obtain ⟨M0, hM0nn, hM0bd, hM0cont⟩ :=
    statopia_math_node_478009398_9cbe8093 p hp phi0 hphi0_smooth hphi0_left hphi0_right phi beta
      hphi1phi hbetanonneg y
  have hbdd : ∃ C : ℝ, ∀ x : Ω × Ω,
      ‖(fderiv ℝ kappa (fun k : Fin p => Z t x k - Zstar t x i k)) (Pi.single j (1 : ℝ))‖ ≤ C := by
    refine ⟨M0 * ‖(Pi.single j (1 : ℝ) : Fin p → ℝ)‖, fun x => ?_⟩
    calc ‖(fderiv ℝ kappa (fun k : Fin p => Z t x k - Zstar t x i k)) (Pi.single j (1 : ℝ))‖
        ≤ ‖fderiv ℝ kappa (fun k : Fin p => Z t x k - Zstar t x i k)‖ *
            ‖(Pi.single j (1 : ℝ) : Fin p → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M0 * ‖(Pi.single j (1 : ℝ) : Fin p → ℝ)‖ :=
        mul_le_mul_of_nonneg_right (hM0bd (fun k : Fin p => Z t x k - Zstar t x i k)) (norm_nonneg _)
  have hZs : ∀ (l : Fin n) (k : Fin p), Measurable fun x : Ω × Ω => Zstar t x l k := by
    intro l k
    have h1k : Measurable fun x : Ω × Ω => X l x.1 k :=
      ((measurable_pi_apply k).comp (hXm l)).comp measurable_fst
    have h2k : Measurable fun x : Ω × Ω => F l x.1 k :=
      ((measurable_pi_apply k).comp (hFm l)).comp measurable_fst
    have h3k : Measurable fun x : Ω × Ω => F l x.2 k :=
      ((measurable_pi_apply k).comp (hFm l)).comp measurable_snd
    have g1 : Measurable fun x : Ω × Ω => Real.sqrt v * (X l x.1 k - muX k) :=
      measurable_const.mul (h1k.sub measurable_const)
    have g2 : Measurable fun x : Ω × Ω => Real.sqrt (1 - v) * (F l x.1 k - muX k) :=
      measurable_const.mul (h2k.sub measurable_const)
    have g3 : Measurable fun x : Ω × Ω => Real.sqrt t *
        (Real.sqrt v * (X l x.1 k - muX k) +
          Real.sqrt (1 - v) * (F l x.1 k - muX k)) :=
      measurable_const.mul (g1.add g2)
    have g4 : Measurable fun x : Ω × Ω => Real.sqrt (1 - t) * (F l x.2 k - muX k) :=
      measurable_const.mul (h3k.sub measurable_const)
    exact measurable_const.mul (g3.add g4)
  have hZss : ∀ (l : Fin m) (k : Fin p), Measurable fun x : Ω × Ω => Zstarstar t x l k := by
    intro l k
    have h1k : Measurable fun x : Ω × Ω => Y l x.1 k :=
      ((measurable_pi_apply k).comp (hYm l)).comp measurable_fst
    have h2k : Measurable fun x : Ω × Ω => G l x.1 k :=
      ((measurable_pi_apply k).comp (hGm l)).comp measurable_fst
    have h3k : Measurable fun x : Ω × Ω => G l x.2 k :=
      ((measurable_pi_apply k).comp (hGm l)).comp measurable_snd
    have g1 : Measurable fun x : Ω × Ω => Real.sqrt v * (Y l x.1 k - muY k) :=
      measurable_const.mul (h1k.sub measurable_const)
    have g2 : Measurable fun x : Ω × Ω => Real.sqrt (1 - v) * (G l x.1 k - muY k) :=
      measurable_const.mul (h2k.sub measurable_const)
    have g3 : Measurable fun x : Ω × Ω => Real.sqrt t *
        (Real.sqrt v * (Y l x.1 k - muY k) +
          Real.sqrt (1 - v) * (G l x.1 k - muY k)) :=
      measurable_const.mul (g1.add g2)
    have g4 : Measurable fun x : Ω × Ω => Real.sqrt (1 - t) * (G l x.2 k - muY k) :=
      measurable_const.mul (h3k.sub measurable_const)
    exact measurable_const.mul (g3.add g4)
  have hZk : ∀ k : Fin p, Measurable fun x : Ω × Ω => Z t x k := by
    intro k
    have hA : Measurable fun x : Ω × Ω => ∑ l : Fin n, Zstar t x l k :=
      Finset.measurable_sum Finset.univ (fun l _ => hZs l k)
    have hB : Measurable fun x : Ω × Ω => ∑ l : Fin m, Zstarstar t x l k :=
      Finset.measurable_sum Finset.univ (fun l _ => hZss l k)
    exact hA.add hB
  have hcurve : Measurable fun x : Ω × Ω => (fun k : Fin p => Z t x k - Zstar t x i k) := by
    rw [measurable_pi_iff]
    intro k
    exact (hZk k).sub (hZs i k)
  have hcontA : Continuous fun w : Fin p → ℝ => (fderiv ℝ kappa w) (Pi.single j (1 : ℝ)) :=
    hM0cont.clm_apply continuous_const
  have hmeasF : AEStronglyMeasurable
      (fun x : Ω × Ω => (fderiv ℝ kappa (fun k : Fin p => Z t x k - Zstar t x i k)) (Pi.single j (1 : ℝ)))
      (P.prod P) :=
    (hcontA.measurable.comp hcurve).aestronglyMeasurable
  have hmeasZ : AEStronglyMeasurable (fun x : Ω × Ω => Zdotstar t x i j) (P.prod P) := by
    have h1 : Measurable fun x : Ω × Ω => X i x.1 j :=
      ((measurable_pi_apply j).comp (hXm i)).comp measurable_fst
    have h2 : Measurable fun x : Ω × Ω => F i x.1 j :=
      ((measurable_pi_apply j).comp (hFm i)).comp measurable_fst
    have h3 : Measurable fun x : Ω × Ω => F i x.2 j :=
      ((measurable_pi_apply j).comp (hFm i)).comp measurable_snd
    have e1 : Measurable fun x : Ω × Ω => Real.sqrt v * (X i x.1 j - muX j) :=
      measurable_const.mul (h1.sub measurable_const)
    have e2 : Measurable fun x : Ω × Ω => Real.sqrt (1 - v) * (F i x.1 j - muX j) :=
      measurable_const.mul (h2.sub measurable_const)
    have e3 : Measurable fun x : Ω × Ω =>
        (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) +
          Real.sqrt (1 - v) * (F i x.1 j - muX j)) :=
      measurable_const.mul (e1.add e2)
    have e4 : Measurable fun x : Ω × Ω => (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j) :=
      measurable_const.mul (h3.sub measurable_const)
    exact (measurable_const.mul (e3.sub e4)).aestronglyMeasurable
  have hXi : Integrable (fun x : Ω × Ω => X i x.1 j) (P.prod P) :=
    memLp_one_iff_integrable.mp (((hXL2 i j).mono_exponent (by norm_num)).comp_fst P)
  have hF1 : Integrable (fun x : Ω × Ω => F i x.1 j) (P.prod P) :=
    memLp_one_iff_integrable.mp (((hFL2 i j).mono_exponent (by norm_num)).comp_fst P)
  have hF2 : Integrable (fun x : Ω × Ω => F i x.2 j) (P.prod P) :=
    memLp_one_iff_integrable.mp (((hFL2 i j).mono_exponent (by norm_num)).comp_snd P)
  have hsubI1 : Integrable (fun x : Ω × Ω => X i x.1 j - muX j) (P.prod P) :=
    hXi.sub (integrable_const (muX j))
  have hsubI2 : Integrable (fun x : Ω × Ω => F i x.1 j - muX j) (P.prod P) :=
    hF1.sub (integrable_const (muX j))
  have hsubI3 : Integrable (fun x : Ω × Ω => F i x.2 j - muX j) (P.prod P) :=
    hF2.sub (integrable_const (muX j))
  have hp1 : Integrable (fun x : Ω × Ω => Real.sqrt v * (X i x.1 j - muX j)) (P.prod P) :=
    hsubI1.const_mul (Real.sqrt v)
  have hp2 : Integrable (fun x : Ω × Ω => Real.sqrt (1 - v) * (F i x.1 j - muX j)) (P.prod P) :=
    hsubI2.const_mul (Real.sqrt (1 - v))
  have hp3 : Integrable (fun x : Ω × Ω => (2 * Real.sqrt t)⁻¹ *
      (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)))
      (P.prod P) :=
    (hp1.add hp2).const_mul (2 * Real.sqrt t)⁻¹
  have hp4 : Integrable (fun x : Ω × Ω => (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
      (P.prod P) :=
    hsubI3.const_mul (2 * Real.sqrt (1 - t))⁻¹
  have hAi : Integrable (fun x : Ω × Ω => Real.sqrt v * (X i x.1 j - muX j) +
      Real.sqrt (1 - v) * (F i x.1 j - muX j)) (P.prod P) :=
    hp1.add hp2
  have hZint : Integrable (fun x : Ω × Ω => Zdotstar t x i j) (P.prod P) := by
    have hBi : Integrable (fun x : Ω × Ω =>
        (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) +
          Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
        (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)) (P.prod P) :=
      hp3.sub hp4
    exact hBi.const_mul (Real.sqrt (n : ℝ))⁻¹
  have hconst : ∀ c : ℝ, (∫ x : Ω × Ω, c ∂(P.prod P)) = c := by
    intro c
    rw [MeasureTheory.integral_const]
    simp
  have hslice1 : ∀ f : Ω → ℝ, AEMeasurable f P →
      (∫ x : Ω × Ω, f x.1 ∂(P.prod P)) = ∫ z, f z ∂P := by
    intro f hf
    have hfst : Measure.map Prod.fst (P.prod P) = P := by
      rw [Measure.map_fst_prod]
      simp
    have hf' : AEStronglyMeasurable f (Measure.map Prod.fst (P.prod P)) := by
      rw [hfst]
      exact hf.aestronglyMeasurable
    have key := MeasureTheory.integral_map measurable_fst.aemeasurable hf'
    rw [hfst] at key
    exact key.symm
  have hslice2 : ∀ f : Ω → ℝ, AEMeasurable f P →
      (∫ x : Ω × Ω, f x.2 ∂(P.prod P)) = ∫ z, f z ∂P := by
    intro f hf
    have hsnd : Measure.map Prod.snd (P.prod P) = P := by
      rw [Measure.map_snd_prod]
      simp
    have hf' : AEStronglyMeasurable f (Measure.map Prod.snd (P.prod P)) := by
      rw [hsnd]
      exact hf.aestronglyMeasurable
    have key := MeasureTheory.integral_map measurable_snd.aemeasurable hf'
    rw [hsnd] at key
    exact key.symm
  have hZzero : (∫ x : Ω × Ω, Zdotstar t x i j ∂(P.prod P)) = 0 := by
    have e1 : AEMeasurable (fun z : Ω => X i z j) P :=
      ((measurable_pi_apply j).comp (hXm i)).aemeasurable
    have e2 : AEMeasurable (fun z : Ω => F i z j) P :=
      ((measurable_pi_apply j).comp (hFm i)).aemeasurable
    have h1 : (∫ x : Ω × Ω, X i x.1 j ∂(P.prod P)) = muX j := by
      rw [hslice1 (fun z => X i z j) e1]
      exact hXmean i j
    have h2 : (∫ x : Ω × Ω, F i x.1 j ∂(P.prod P)) = muX j := by
      rw [hslice1 (fun z => F i z j) e2]
      exact hFmean i j
    have h3 : (∫ x : Ω × Ω, F i x.2 j ∂(P.prod P)) = muX j := by
      rw [hslice2 (fun z => F i z j) e2]
      exact hFmean i j
    have hsub1 : (∫ x : Ω × Ω, X i x.1 j - muX j ∂(P.prod P)) = 0 := by
      simp only [integral_sub hXi (integrable_const (muX j))]
      rw [h1, hconst (muX j)]
      ring
    have hsub2 : (∫ x : Ω × Ω, F i x.1 j - muX j ∂(P.prod P)) = 0 := by
      simp only [integral_sub hF1 (integrable_const (muX j))]
      rw [h2, hconst (muX j)]
      ring
    have hsub3 : (∫ x : Ω × Ω, F i x.2 j - muX j ∂(P.prod P)) = 0 := by
      simp only [integral_sub hF2 (integrable_const (muX j))]
      rw [h3, hconst (muX j)]
      ring
    have hA0 : (∫ x : Ω × Ω, Real.sqrt v * (X i x.1 j - muX j) +
        Real.sqrt (1 - v) * (F i x.1 j - muX j) ∂(P.prod P)) = 0 := by
      simp only [integral_add hp1 hp2, integral_const_mul]
      rw [hsub1, hsub2]
      ring
    dsimp only [Zdotstar]
    simp only [integral_const_mul]
    simp only [integral_sub hp3 hp4, integral_const_mul]
    rw [hA0, hsub3]
    ring
  have hIndep : (fun x : Ω × Ω =>
        (fderiv ℝ kappa (fun k : Fin p => Z t x k - Zstar t x i k)) (Pi.single j (1 : ℝ)))
      ⟂ᵢ[P.prod P] (fun x : Ω × Ω => Zdotstar t x i j) := by
    exact statopia_math_node_2948575112_cf5ddfcb Ω P n m p delta muX muY X Y F G kappa j
      hXm hYm hFm hGm hindep hcontA v hv0 hv1 t ht0 ht1 i
  obtain ⟨C, hC⟩ := hbdd
  constructor
  · exact hZint.bdd_mul hmeasF (Filter.Eventually.of_forall hC)
  · rw [ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hIndep hmeasF hmeasZ, hZzero,
      mul_zero]
  /- @proof-region region.target-node.session.8298b47e63d88240 end -/

end

end Statlib.Imported

