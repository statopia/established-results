import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1967109576_c7239acb_4f2497e8
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604

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
theorem statopia_math_node_3276301073_1a4e82d2 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hp2 : 2 ≤ p)
    (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (y : Fin p → ℝ) (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (hXm : ∀ i : Fin n, Measurable (X i)) (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i)) (hGm : ∀ i : Fin m, Measurable (G i))
    (hX1 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => X i ω j - muX j) P)
    (hY1 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => Y i ω j - muY j) P)
    (hF1 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => F i ω j - muX j) P)
    (hG1 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => G i ω j - muY j) P),
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
     let Zdot : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) +
             Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
           (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
     let kappa : (Fin p → ℝ) → ℝ := fun w =>
       phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
     Integrable
         (Function.uncurry (fun (t : ℝ) (x : Ω × Ω) =>
           ∑ j : Fin p, ∑ i : Fin m,
             (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j))
         ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P)) ∧
     (∫ x, (∫ t in (0 : ℝ)..1, ∑ j : Fin p, ∑ i : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j) ∂(P.prod P)
       = ∫ t in (0 : ℝ)..1, ∫ x, (∑ j : Fin p, ∑ i : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j) ∂(P.prod P))) := by
  /- @proof-region region.target-node.session.91c58c2af23239e0 begin -/
  intro Ω _inst P _hP n m p hn hm hp hp2 delta muX muY X Y F G v hv0 hv1
    phi1 phi2 hphi1 hphi2 y phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
    hXm hYm hFm hGm hX1 hY1 hF1 hG1
  dsimp only
  obtain ⟨Cκ, hCκnonneg, hCκ⟩ :=
    statopia_math_node_1967109576_c7239acb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  have hk :=
    statopia_math_node_2194576110_d2ad0cef p hp2 (min phi1 phi2) (le_min hphi1 hphi2)
      phi0 hphi0_cont hphi0_left hphi0_right hphi0_range y
  dsimp only at hk
  obtain ⟨hk_cont, -⟩ := hk
  let KAP : (Fin p → ℝ) → ℝ := fun w =>
    phi0 (min phi1 phi2 * (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
      Real.log (∑ j : Fin p, Real.exp (((min phi1 phi2) * Real.log (p : ℝ)) * (w j - y j)))))
  have hgrad : ∀ (w : Fin p → ℝ) (j : Fin p),
      |(fderiv ℝ KAP w) (Pi.single j (1 : ℝ))| ≤ Cκ * phi2 := by
    intro w j
    have h0 := hCκ p hp2 (min phi1 phi2) (le_min hphi1 hphi2) y w j
    dsimp only at h0
    calc |(fderiv ℝ KAP w) (Pi.single j (1 : ℝ))| ≤ Cκ * min phi1 phi2 := h0
      _ ≤ Cκ * phi2 := mul_le_mul_of_nonneg_left (min_le_right phi1 phi2) hCκnonneg
  have hderiv_cont : ∀ j : Fin p,
      Continuous (fun z : Fin p → ℝ => (fderiv ℝ KAP z) (Pi.single j (1 : ℝ))) := by
    intro j
    exact (hk_cont.continuous_fderiv (by norm_num)).clm_apply continuous_const
  let ZC : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
    (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
            Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - t) * (F i x.2 j - muX j))) +
      (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
            Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - t) * (G i x.2 j - muY j)))
  let ZD : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) +
          Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
        (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
  have hZT : Measurable (fun q : ℝ × (Ω × Ω) => Real.sqrt q.1) :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hZT1 : Measurable (fun q : ℝ × (Ω × Ω) => Real.sqrt (1 - q.1)) :=
    Real.continuous_sqrt.measurable.comp (measurable_const.sub measurable_fst)
  have h2T : Measurable (fun q : ℝ × (Ω × Ω) => (2 * Real.sqrt q.1)⁻¹) :=
    (measurable_const.mul hZT).inv
  have h2T1 : Measurable (fun q : ℝ × (Ω × Ω) => (2 * Real.sqrt (1 - q.1))⁻¹) :=
    (measurable_const.mul hZT1).inv
  have hXc : ∀ (i : Fin n) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => X i q.2.1 j) :=
    fun i j => (measurable_pi_apply j).comp ((hXm i).comp measurable_snd.fst)
  have hFc : ∀ (i : Fin n) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => F i q.2.1 j) :=
    fun i j => (measurable_pi_apply j).comp ((hFm i).comp measurable_snd.fst)
  have hFc' : ∀ (i : Fin n) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => F i q.2.2 j) :=
    fun i j => (measurable_pi_apply j).comp ((hFm i).comp measurable_snd.snd)
  have hYc : ∀ (i : Fin m) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => Y i q.2.1 j) :=
    fun i j => (measurable_pi_apply j).comp ((hYm i).comp measurable_snd.fst)
  have hGc : ∀ (i : Fin m) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => G i q.2.1 j) :=
    fun i j => (measurable_pi_apply j).comp ((hGm i).comp measurable_snd.fst)
  have hGc' : ∀ (i : Fin m) (j : Fin p), Measurable (fun q : ℝ × (Ω × Ω) => G i q.2.2 j) :=
    fun i j => (measurable_pi_apply j).comp ((hGm i).comp measurable_snd.snd)
  have hZC : Measurable (fun q : ℝ × (Ω × Ω) => ZC q.1 q.2) := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    have hinnerX : ∀ i : Fin n, Measurable (fun q : ℝ × (Ω × Ω) =>
        Real.sqrt v * (X i q.2.1 j - muX j) + Real.sqrt (1 - v) * (F i q.2.1 j - muX j)) :=
      fun i => (measurable_const.mul ((hXc i j).sub measurable_const)).add
        (measurable_const.mul ((hFc i j).sub measurable_const))
    have htermX : ∀ i : Fin n, Measurable (fun q : ℝ × (Ω × Ω) =>
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt q.1 * (Real.sqrt v * (X i q.2.1 j - muX j) +
              Real.sqrt (1 - v) * (F i q.2.1 j - muX j)) +
            Real.sqrt (1 - q.1) * (F i q.2.2 j - muX j))) :=
      fun i => (measurable_const : Measurable (fun _ : ℝ × (Ω × Ω) => (Real.sqrt (n : ℝ))⁻¹)).mul
        ((hZT.mul (hinnerX i)).add (hZT1.mul ((hFc' i j).sub measurable_const)))
    have hinnerY : ∀ i : Fin m, Measurable (fun q : ℝ × (Ω × Ω) =>
        Real.sqrt v * (Y i q.2.1 j - muY j) + Real.sqrt (1 - v) * (G i q.2.1 j - muY j)) :=
      fun i => (measurable_const.mul ((hYc i j).sub measurable_const)).add
        (measurable_const.mul ((hGc i j).sub measurable_const))
    have htermY : ∀ i : Fin m, Measurable (fun q : ℝ × (Ω × Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt q.1 * (Real.sqrt v * (Y i q.2.1 j - muY j) +
              Real.sqrt (1 - v) * (G i q.2.1 j - muY j)) +
            Real.sqrt (1 - q.1) * (G i q.2.2 j - muY j))) :=
      fun i =>
        (measurable_const : Measurable (fun _ : ℝ × (Ω × Ω) => (Real.sqrt (m : ℝ))⁻¹ * delta n m)).mul
          ((hZT.mul (hinnerY i)).add (hZT1.mul ((hGc' i j).sub measurable_const)))
    exact (Finset.measurable_sum Finset.univ (fun i _ => htermX i)).add
      (Finset.measurable_sum Finset.univ (fun i _ => htermY i))
  have hZD : ∀ (i : Fin m) (j : Fin p),
      Measurable (fun q : ℝ × (Ω × Ω) => ZD q.1 q.2 i j) := by
    intro i j
    have hinnerY : Measurable (fun q : ℝ × (Ω × Ω) =>
        Real.sqrt v * (Y i q.2.1 j - muY j) + Real.sqrt (1 - v) * (G i q.2.1 j - muY j)) :=
      (measurable_const.mul ((hYc i j).sub measurable_const)).add
        (measurable_const.mul ((hGc i j).sub measurable_const))
    exact (measurable_const : Measurable (fun _ : ℝ × (Ω × Ω) => (Real.sqrt (m : ℝ))⁻¹ * delta n m)).mul
      ((h2T.mul hinnerY).sub (h2T1.mul ((hGc' i j).sub measurable_const)))
  have hIK : Measurable (fun q : ℝ × (Ω × Ω) =>
      ∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ KAP (ZC q.1 q.2)) (Pi.single j (1 : ℝ)) * ZD q.1 q.2 i j) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
    exact ((hderiv_cont j).measurable.comp hZC).mul (hZD i j)

  let TW : ℝ → ℝ := fun t => |t ^ (-(1/2) : ℝ)| + |(1 - t) ^ (-(1/2) : ℝ)|
  let W : Ω × Ω → ℝ := fun x =>
    ∑ j : Fin p, ∑ i : Fin m,
      (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|)
  let Kc : ℝ := Cκ * phi2 * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|
  have hWterm : ∀ (i : Fin m) (j : Fin p), Integrable
      (fun x : Ω × Ω => |Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|)
      (P.prod P) := by
    intro i j
    have h1 : Integrable (fun x : Ω × Ω => Y i x.1 j - muY j) (P.prod P) :=
      (hY1 i j).comp_fst P
    have h2 : Integrable (fun x : Ω × Ω => G i x.1 j - muY j) (P.prod P) :=
      (hG1 i j).comp_fst P
    have h3 : Integrable (fun x : Ω × Ω => G i x.2 j - muY j) (P.prod P) :=
      (hG1 i j).comp_snd P
    exact (h1.abs.add h2.abs).add h3.abs
  have hinner : ∀ (j : Fin p) (S : Finset (Fin m)), Integrable
      (fun x : Ω × Ω => Finset.sum S (fun i =>
        (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|)))
      (P.prod P) := by
    intro j S
    induction S using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        have hEq : (fun x : Ω × Ω => Finset.sum (insert a s) (fun i =>
              (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|)))
            = (fun x : Ω × Ω =>
              (|Y a x.1 j - muY j| + |G a x.1 j - muY j| + |G a x.2 j - muY j|)
                + Finset.sum s (fun i =>
                  (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|))) := by
          funext x
          rw [Finset.sum_insert ha]
        rw [hEq]
        exact (hWterm a j).add ih
  have houter : ∀ (S : Finset (Fin p)), Integrable
      (fun x : Ω × Ω => Finset.sum S (fun j => Finset.sum Finset.univ (fun i =>
        (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|))))
      (P.prod P) := by
    intro S
    induction S using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        have hEq : (fun x : Ω × Ω => Finset.sum (insert a s) (fun j =>
              Finset.sum Finset.univ (fun i =>
                (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|))))
            = (fun x : Ω × Ω =>
              Finset.sum Finset.univ (fun i =>
                  (|Y i x.1 a - muY a| + |G i x.1 a - muY a| + |G i x.2 a - muY a|))
                + Finset.sum s (fun j => Finset.sum Finset.univ (fun i =>
                  (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|)))) := by
          funext x
          rw [Finset.sum_insert ha]
        rw [hEq]
        exact (hinner a Finset.univ).add ih
  have hW_int : Integrable W (P.prod P) := houter Finset.univ

  have hTW_int : Integrable TW (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    have hset : Set.uIoc (0 : ℝ) 1 = Set.Ioc 0 1 := by simp [Set.uIoc]
    have hr0 : IntervalIntegrable (fun t : ℝ => t ^ (-(1/2) : ℝ)) volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1/2)) (by norm_num)
    have hr20 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(1/2) : ℝ)) volume (0 : ℝ) 1 := by
      have hc := (IntervalIntegrable.comp_sub_left (f := fun x : ℝ => x ^ (-(1/2) : ℝ)) hr0
        (c := (1 : ℝ))).symm
      simpa using hc
    have hr : Integrable (fun t : ℝ => t ^ (-(1/2) : ℝ))
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      rw [hset]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hr0
    have hr2 : Integrable (fun t : ℝ => (1 - t) ^ (-(1/2) : ℝ))
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      rw [hset]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hr20
    exact hr.abs.add hr2.abs

  have hdom : ∀ q : ℝ × (Ω × Ω), ‖(fun q : ℝ × (Ω × Ω) =>
      ∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ KAP (ZC q.1 q.2)) (Pi.single j (1 : ℝ)) * ZD q.1 q.2 i j) q‖
      ≤ Kc * (TW q.1 * W q.2) := by
    rintro ⟨t, x⟩
    rw [Real.norm_eq_abs]
    let V : Fin m → Fin p → ℝ := fun i j =>
      |Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|
    have hVeq : ∀ (i : Fin m) (j : Fin p), V i j =
        |Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j| := fun i j => rfl
    have hCph : (0:ℝ) ≤ Cκ * phi2 := mul_nonneg hCκnonneg (by linarith)
    have hTWnn : (0:ℝ) ≤ TW t := by
      have h1 := abs_nonneg (t ^ (-(1/2) : ℝ))
      have h2 := abs_nonneg ((1 - t) ^ (-(1/2) : ℝ))
      show (0:ℝ) ≤ |t ^ (-(1/2) : ℝ)| + |(1 - t) ^ (-(1/2) : ℝ)|
      linarith
    have hVnn : ∀ (i : Fin m) (j : Fin p), (0:ℝ) ≤ V i j := by
      intro i j
      have h1 := abs_nonneg (Y i x.1 j - muY j)
      have h2 := abs_nonneg (G i x.1 j - muY j)
      have h3 := abs_nonneg (G i x.2 j - muY j)
      show (0:ℝ) ≤ |Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|
      linarith
    have hle1 : ∀ s : ℝ, |(2 * Real.sqrt s)⁻¹| ≤ |s ^ (-(1/2) : ℝ)| := by
      intro s
      have hsq : s ^ (-(1/2) : ℝ) = Real.sqrt (s⁻¹) := by
        rw [Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow]
      rw [hsq, abs_of_nonneg (Real.sqrt_nonneg (s⁻¹))]
      by_cases hs : Real.sqrt s = 0
      · rw [hs, mul_zero, inv_zero, abs_zero]
        exact Real.sqrt_nonneg (s⁻¹)
      · have hpos : 0 < Real.sqrt s := lt_of_le_of_ne (Real.sqrt_nonneg s) (Ne.symm hs)
        rw [Real.sqrt_inv, abs_of_pos (inv_pos.mpr (by linarith : (0:ℝ) < 2 * Real.sqrt s))]
        rw [mul_inv]
        have hx : (0:ℝ) ≤ (Real.sqrt s)⁻¹ := le_of_lt (inv_pos.mpr hpos)
        calc (2:ℝ)⁻¹ * (Real.sqrt s)⁻¹ ≤ 1 * (Real.sqrt s)⁻¹ :=
              mul_le_mul_of_nonneg_right (by norm_num) hx
          _ = (Real.sqrt s)⁻¹ := one_mul _
    have hkey : ∀ (i : Fin m) (j : Fin p), |ZD t x i j| ≤
        |(Real.sqrt (m : ℝ))⁻¹ * delta n m| *
          ((|(2 * Real.sqrt t)⁻¹| + |(2 * Real.sqrt (1 - t))⁻¹|) * V i j) := by
      intro i j
      have hsv0 : (0:ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg v
      have hsv1 : (0:ℝ) ≤ Real.sqrt (1 - v) := Real.sqrt_nonneg (1 - v)
      have hsvle : Real.sqrt v ≤ 1 := Real.sqrt_le_one.mpr hv1
      have hsv1le : Real.sqrt (1 - v) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
      have hA : (0:ℝ) ≤ |Y i x.1 j - muY j| := abs_nonneg _
      have hB : (0:ℝ) ≤ |G i x.1 j - muY j| := abs_nonneg _
      have hC : (0:ℝ) ≤ |G i x.2 j - muY j| := abs_nonneg _
      have hinner : |Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)|
          ≤ |Y i x.1 j - muY j| + |G i x.1 j - muY j| := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hsv1]
        nlinarith [mul_le_mul_of_nonneg_right hsvle hA, mul_le_mul_of_nonneg_right hsv1le hB]
      have h1 : |(2 * Real.sqrt t)⁻¹ *
              (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
            - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)|
          ≤ |(2 * Real.sqrt t)⁻¹| * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
            + |(2 * Real.sqrt (1 - t))⁻¹| * |G i x.2 j - muY j| := by
        have habs : |(2 * Real.sqrt t)⁻¹ *
              (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
            - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)|
            ≤ |(2 * Real.sqrt t)⁻¹ *
              (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))|
              + |(2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)| := abs_sub _ _
        rw [abs_mul, abs_mul] at habs
        refine le_trans habs ?_
        exact add_le_add (mul_le_mul_of_nonneg_left hinner (abs_nonneg _)) le_rfl

      have h2 : |(2 * Real.sqrt t)⁻¹| * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
              + |(2 * Real.sqrt (1 - t))⁻¹| * |G i x.2 j - muY j|
          ≤ (|(2 * Real.sqrt t)⁻¹| + |(2 * Real.sqrt (1 - t))⁻¹|) *
            (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|) := by
        have hp1 : |(2 * Real.sqrt t)⁻¹| * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
            ≤ |(2 * Real.sqrt t)⁻¹| *
              (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        have hp2 : |(2 * Real.sqrt (1 - t))⁻¹| * |G i x.2 j - muY j|
            ≤ |(2 * Real.sqrt (1 - t))⁻¹| *
              (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        nlinarith [hp1, hp2]
      have hK : ZD t x i j = ((Real.sqrt (m : ℝ))⁻¹ * delta n m) *
          ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
            - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)) := rfl
      rw [hK, hVeq i j, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact le_trans h1 h2
    have hBD : ∀ (i : Fin m) (j : Fin p), |ZD t x i j| ≤
        |(Real.sqrt (m : ℝ))⁻¹ * delta n m| * (TW t * V i j) := by
      intro i j
      have hcoef : (|(2 * Real.sqrt t)⁻¹| + |(2 * Real.sqrt (1 - t))⁻¹|) ≤ TW t :=
        add_le_add (hle1 t) (hle1 (1 - t))
      calc |ZD t x i j| ≤ |(Real.sqrt (m : ℝ))⁻¹ * delta n m| *
            ((|(2 * Real.sqrt t)⁻¹| + |(2 * Real.sqrt (1 - t))⁻¹|) * V i j) := hkey i j
        _ ≤ |(Real.sqrt (m : ℝ))⁻¹ * delta n m| * (TW t * V i j) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [hVeq i j]
            exact mul_le_mul hcoef le_rfl (hVnn i j) hTWnn
    have hstep1 : |∑ j : Fin p, ∑ i : Fin m,
          (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ)) * ZD t x i j|
        ≤ ∑ j : Fin p, ∑ i : Fin m, (Cκ * phi2) * |ZD t x i j| := by
      refine le_trans (Finset.abs_sum_le_sum_abs
        (fun j : Fin p => ∑ i : Fin m,
          (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ)) * ZD t x i j) Finset.univ) ?_
      refine le_trans (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs
        (fun i : Fin m =>
          (fderiv ℝ KAP (ZC t x)) (Pi.single j (1 : ℝ)) * ZD t x i j) Finset.univ)) ?_
      refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => ?_))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hgrad (ZC t x) j) (abs_nonneg _)
    have hstep2 : ∑ j : Fin p, ∑ i : Fin m, (Cκ * phi2) * |ZD t x i j|
        ≤ ∑ j : Fin p, ∑ i : Fin m, (Cκ * phi2) *
          (|(Real.sqrt (m : ℝ))⁻¹ * delta n m| * (TW t * V i j)) := by
      refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => ?_))
      exact mul_le_mul_of_nonneg_left (hBD i j) hCph
    have hstep3 : ∑ j : Fin p, ∑ i : Fin m, (Cκ * phi2) *
          (|(Real.sqrt (m : ℝ))⁻¹ * delta n m| * (TW t * V i j)) = Kc * (TW t * W x) := by
      have hrow : ∀ j : Fin p, (∑ i : Fin m, (Cκ * phi2) *
            (|(Real.sqrt (m : ℝ))⁻¹ * delta n m| * (TW t * V i j)))
          = (Cκ * phi2 * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| * TW t) *
              (∑ i : Fin m, V i j) := by
        intro j
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [Finset.sum_congr rfl (fun j _ => hrow j)]
      rw [← Finset.mul_sum]
      have hWdef : (∑ j : Fin p, ∑ i : Fin m, V i j) = W x := rfl
      rw [hWdef]
      show (Cκ * phi2 * |(Real.sqrt (m : ℝ))⁻¹ * delta n m| * TW t) * W x
        = (Cκ * phi2 * |(Real.sqrt (m : ℝ))⁻¹ * delta n m|) * (TW t * W x)
      ring

    exact hstep1.trans (hstep2.trans (le_of_eq hstep3))

  have hprod_int : Integrable (fun q : ℝ × (Ω × Ω) => TW q.1 * W q.2)
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P)) :=
    hTW_int.mul_prod hW_int
  have hbound_int : Integrable (fun q : ℝ × (Ω × Ω) => Kc * (TW q.1 * W q.2))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P)) :=
    hprod_int.const_mul Kc
  have hInt : Integrable (fun q : ℝ × (Ω × Ω) =>
      ∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ KAP (ZC q.1 q.2)) (Pi.single j (1 : ℝ)) * ZD q.1 q.2 i j)
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P)) :=
    Integrable.mono' hbound_int hIK.aestronglyMeasurable (Filter.Eventually.of_forall hdom)
  exact ⟨hInt, (MeasureTheory.intervalIntegral_integral_swap hInt).symm⟩





  /- @proof-region region.target-node.session.91c58c2af23239e0 end -/

end

end Statlib.Imported

