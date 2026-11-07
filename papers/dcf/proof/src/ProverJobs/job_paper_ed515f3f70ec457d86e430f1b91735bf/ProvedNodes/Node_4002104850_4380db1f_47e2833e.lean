import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
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
theorem statopia_math_node_4002104850_4380db1f : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (phi1 phi2 : ℝ) (v : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
    (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hX : ∀ i : Fin n, Measurable (X i)) (hY : ∀ i : Fin m, Measurable (Y i))
    (hF : ∀ i : Fin n, Measurable (F i)) (hG : ∀ i : Fin m, Measurable (G i))
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (y : Fin p → ℝ),
    let kappa : (Fin p → ℝ) → ℝ := fun w =>
      phi0 (min phi1 phi2 * (((min phi1 phi2) * Real.log (p : ℝ))⁻¹ *
        Real.log (∑ j : Fin p, Real.exp (((min phi1 phi2) * Real.log (p : ℝ)) * (w j - y j)))))
    let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
          Real.sqrt (1 - t) * (F i x.2 j - muX j))
    let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
          Real.sqrt (1 - t) * (G i x.2 j - muY j))
    let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
      (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
    let Zdotstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ *
            (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
    let Zdotstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        ((2 * Real.sqrt t)⁻¹ *
            (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
    let Zdot : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
      (∑ i : Fin n, Zdotstar t x i j) + (∑ i : Fin m, Zdotstarstar t x i j)
    (∀ (x : Ω × Ω) (j : Fin p),
        Z 1 x j = Real.sqrt v *
            combVec n m (delta n m) muX muY (fun i : Fin n => X i x.1) (fun i : Fin m => Y i x.1) j +
          Real.sqrt (1 - v) *
            combVec n m (delta n m) muX muY (fun i : Fin n => F i x.1) (fun i : Fin m => G i x.1) j) ∧
      (∀ (x : Ω × Ω) (j : Fin p),
        Z 0 x j =
          combVec n m (delta n m) muX muY (fun i : Fin n => F i x.2) (fun i : Fin m => G i x.2) j) ∧
      (∀ (x : Ω × Ω) (j : Fin p), ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => Z s x j) (Zdot t x j) t) ∧
      (∀ (x : Ω × Ω) (j : Fin p),
        IntervalIntegrable (fun t : ℝ => Zdot t x j) volume (0 : ℝ) 1) ∧
      (∀ (x : Ω × Ω), ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => kappa (Z s x))
          (∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x j) t) ∧
      (∀ (x : Ω × Ω),
        IntervalIntegrable
          (fun t : ℝ => ∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x j)
          volume (0 : ℝ) 1) ∧
      (∀ᵐ x ∂(P.prod P),
        kappa (Z 1 x) - kappa (Z 0 x) =
          ∫ t in (0 : ℝ)..1,
            ∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x j) ∧
      (∀ᵐ x ∂(P.prod P),
        kappa (Z 1 x) - kappa (Z 0 x) =
          (∫ t in (0 : ℝ)..1,
              ∑ j : Fin p, ∑ i : Fin n,
                (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j) +
            (∫ t in (0 : ℝ)..1,
              ∑ j : Fin p, ∑ i : Fin m,
                (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstarstar t x i j)) := by
  /- @proof-region region.target-node.session.5e4a3ba6eea2ad32 begin -/
  intro Ω instΩ P instP n m p delta muX muY X Y F G phi1 phi2 v hn hm hp hlogp
    hphi1 hphi2 hv0 hv1 hX hY hF hG phi0 hphi0_cont hphi0_left hphi0_right hphi0_range y
  haveI := instΩ
  haveI := instP
  let phi : ℝ := min phi1 phi2
  let beta : ℝ := phi * Real.log (p : ℝ)
  let kappa : (Fin p → ℝ) → ℝ :=
    fun w => phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
  let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
        Real.sqrt (1 - t) * (F i x.2 j - muX j))
  let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
        Real.sqrt (1 - t) * (G i x.2 j - muY j))
  let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
    (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
  let ZdotStar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ((2 * Real.sqrt t)⁻¹ *
          (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
        (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
  let ZdotStarStar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      ((2 * Real.sqrt t)⁻¹ *
          (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)) -
        (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
  let Zdot : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
    (∑ i : Fin n, ZdotStar t x i j) + (∑ i : Fin m, ZdotStarStar t x i j)
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hsqn : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := by
    simpa [pow_two] using Real.sq_sqrt hnpos.le
  have hsqm : Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = (m:ℝ) := by
    simpa [pow_two] using Real.sq_sqrt hmpos.le
  have hcN : (Real.sqrt (n:ℝ))⁻¹ * (n:ℝ) = Real.sqrt (n:ℝ) := by
    calc (Real.sqrt (n:ℝ))⁻¹ * (n:ℝ)
        = (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) := by rw [hsqn]
      _ = ((Real.sqrt (n:ℝ))⁻¹ * Real.sqrt (n:ℝ)) * Real.sqrt (n:ℝ) := by rw [mul_assoc]
      _ = Real.sqrt (n:ℝ) := by
          rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr hnpos).ne', one_mul]
  have hcM : (Real.sqrt (m:ℝ))⁻¹ * (m:ℝ) = Real.sqrt (m:ℝ) := by
    calc (Real.sqrt (m:ℝ))⁻¹ * (m:ℝ)
        = (Real.sqrt (m:ℝ))⁻¹ * (Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ)) := by rw [hsqm]
      _ = ((Real.sqrt (m:ℝ))⁻¹ * Real.sqrt (m:ℝ)) * Real.sqrt (m:ℝ) := by rw [mul_assoc]
      _ = Real.sqrt (m:ℝ) := by
          rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr hmpos).ne', one_mul]
  have hdevN : ∀ (f : Fin n → ℝ) (c : ℝ),
      (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, (f i - c))
        = (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, f i) - Real.sqrt (n:ℝ) * c := by
    intro f c
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_sub, ← mul_assoc, hcN]
  have hdevM2 : ∀ (f : Fin m → ℝ) (c : ℝ),
      ((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, (f i - c))
        = ((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, f i)
          - (delta n m * Real.sqrt (m:ℝ)) * c := by
    intro f c
    calc ((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, (f i - c))
        = ((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, f i)
            - ((Real.sqrt (m:ℝ))⁻¹ * (m:ℝ)) * (delta n m * c) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_sub]
          ring
      _ = ((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, f i)
            - (delta n m * Real.sqrt (m:ℝ)) * c := by
          rw [hcM]
          ring
  have hsumDeriv : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ → ℝ) (g' : ι → ℝ) (x : ℝ),
      (∀ i, HasDerivAt (g i) (g' i) x) → HasDerivAt (fun s => ∑ i, g i s) (∑ i, g' i) x := by
    intro ι _ g g' x h
    classical
    have key : ∀ s : Finset ι, HasDerivAt (fun y => ∑ i ∈ s, g i y) (∑ i ∈ s, g' i) x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hasDerivAt_const x (0 : ℝ)
      | insert a s ha ih =>
          have h1 : HasDerivAt (fun y => g a y + ∑ i ∈ s, g i y) (g' a + ∑ i ∈ s, g' i) x :=
            (h a).add ih
          simpa [Finset.sum_insert ha] using h1
    simpa using key Finset.univ
  have hterm : ∀ (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → ∀ (A B c : ℝ),
      HasDerivAt (fun s : ℝ => c * (Real.sqrt s * A + Real.sqrt (1 - s) * B))
        (c * ((2 * Real.sqrt t)⁻¹ * A - (2 * Real.sqrt (1 - t))⁻¹ * B)) t := by
    intro t ht A B c
    have ht1 : t ≠ 0 := ne_of_gt ht.1
    have ht2 : (1 - t) ≠ 0 := ne_of_gt (by linarith [ht.2])
    have h1 : HasDerivAt (fun s : ℝ => Real.sqrt s) ((2 * Real.sqrt t)⁻¹) t := by
      simpa [one_div] using Real.hasDerivAt_sqrt (x := t) ht1
    have h2 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have h3 : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s)) (-(2 * Real.sqrt (1 - t))⁻¹) t := by
      have hc := ((Real.hasDerivAt_sqrt (x := 1 - t) ht2).hasFDerivAt).comp_hasDerivAt t h2
      simpa [Function.comp, one_div, smul_eq_mul, neg_one_mul] using hc
    have h4 : HasDerivAt (fun s : ℝ => Real.sqrt s * A) ((2 * Real.sqrt t)⁻¹ * A) t :=
      h1.mul_const A
    have h5 : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s) * B)
        ((-(2 * Real.sqrt (1 - t))⁻¹) * B) t := h3.mul_const B
    have h6 : HasDerivAt (fun s : ℝ => Real.sqrt s * A + Real.sqrt (1 - s) * B)
        ((2 * Real.sqrt t)⁻¹ * A + (-(2 * Real.sqrt (1 - t))⁻¹) * B) t := h4.add h5
    have h7 := h6.const_mul c
    convert h7 using 1
    ring
  have hZderiv : ∀ (x : Ω × Ω) (j : Fin p) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 →
      HasDerivAt (fun s : ℝ => Z s x j) (Zdot t x j) t := by
    intro x j t ht
    have hN : HasDerivAt (fun s : ℝ => ∑ i : Fin n, Zstar s x i j)
        (∑ i : Fin n, ZdotStar t x i j) t :=
      hsumDeriv (ι := Fin n) (g := fun (i : Fin n) (s : ℝ) => Zstar s x i j)
        (g' := fun i => ZdotStar t x i j) t
        (fun i => hterm t ht
          (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
          (F i x.2 j - muX j) (Real.sqrt (n : ℝ))⁻¹)
    have hM : HasDerivAt (fun s : ℝ => ∑ i : Fin m, Zstarstar s x i j)
        (∑ i : Fin m, ZdotStarStar t x i j) t :=
      hsumDeriv (ι := Fin m) (g := fun (i : Fin m) (s : ℝ) => Zstarstar s x i j)
        (g' := fun i => ZdotStarStar t x i j) t
        (fun i => hterm t ht
          (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
          (G i x.2 j - muY j) ((Real.sqrt (m : ℝ))⁻¹ * delta n m))
    exact hN.add hM
  have hp2 : 2 ≤ p := by
    have h1 : (1:ℝ) < (p:ℝ) := by
      have h2 := Real.exp_lt_exp.mpr hlogp
      rwa [Real.exp_zero, Real.exp_log (by exact_mod_cast hp)] at h2
    have h3 : 1 < p := by exact_mod_cast h1
    omega
  have hphi : (1:ℝ) ≤ phi := le_min hphi1 hphi2
  have hκC3 : ContDiff ℝ 3 kappa :=
    (statopia_math_node_2194576110_d2ad0cef p hp2 phi hphi phi0 hphi0_cont
      hphi0_left hphi0_right hphi0_range y).1
  have hZs : ∀ (x : Ω × Ω) (i : Fin n) (j : Fin p), Continuous fun t : ℝ => Zstar t x i j := by
    intro x i j
    have h1 : Continuous fun t : ℝ => Real.sqrt t := Real.continuous_sqrt
    have h2 : Continuous fun t : ℝ => Real.sqrt (1 - t) :=
      Real.continuous_sqrt.comp (continuous_const.sub continuous_id)
    have h3 : Continuous fun t : ℝ =>
        Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
          + Real.sqrt (1 - t) * (F i x.2 j - muX j) :=
      (h1.mul continuous_const).add (h2.mul continuous_const)
    exact continuous_const.mul h3
  have hZss : ∀ (x : Ω × Ω) (i : Fin m) (j : Fin p), Continuous fun t : ℝ => Zstarstar t x i j := by
    intro x i j
    have h1 : Continuous fun t : ℝ => Real.sqrt t := Real.continuous_sqrt
    have h2 : Continuous fun t : ℝ => Real.sqrt (1 - t) :=
      Real.continuous_sqrt.comp (continuous_const.sub continuous_id)
    have h3 : Continuous fun t : ℝ =>
        Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
          + Real.sqrt (1 - t) * (G i x.2 j - muY j) :=
      (h1.mul continuous_const).add (h2.mul continuous_const)
    exact continuous_const.mul h3
  have hZcont : ∀ x : Ω × Ω, Continuous fun t : ℝ => Z t x := by
    intro x
    refine continuous_pi ?_
    intro j
    have h1 : Continuous fun t : ℝ => ∑ i : Fin n, Zstar t x i j :=
      continuous_finset_sum _ (fun i _ => hZs x i j)
    have h2 : Continuous fun t : ℝ => ∑ i : Fin m, Zstarstar t x i j :=
      continuous_finset_sum _ (fun i _ => hZss x i j)
    exact h1.add h2
  have hfdcont : ∀ (x : Ω × Ω) (j : Fin p),
      Continuous fun t : ℝ => (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) := by
    intro x j
    have hc : Continuous fun q : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ kappa q.1) q.2 :=
      hκC3.continuous_fderiv_apply (by norm_num)
    have hp : Continuous fun t : ℝ => (Z t x, (Pi.single j (1:ℝ) : Fin p → ℝ)) :=
      (hZcont x).prodMk continuous_const
    exact hc.comp hp
  have hZint : ∀ (x : Ω × Ω) (j : Fin p),
      IntervalIntegrable (fun t : ℝ => Zdot t x j) volume (0:ℝ) 1 := by
    intro x j
    have hpow : IntervalIntegrable (fun t : ℝ => t ^ (-(1/2) : ℝ)) volume (0:ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1) (r := -(1/2)) (by norm_num)
    have hsing1 : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹) volume (0:ℝ) 1 := by
      have h := hpow.const_mul ((2:ℝ)⁻¹)
      refine h.congr_ae ?_
      have hμ : Set.uIoc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 := by
        rw [Set.uIoc]
        simp
      rw [hμ]
      filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Ioc (0:ℝ) 1) measurableSet_Ioc]
        with t ht
      have ht0 : (0:ℝ) < t := ht.1
      rw [Real.sqrt_eq_rpow, mul_inv, ← Real.rpow_neg ht0.le (1/2)]
    have hsing2 : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt (1 - t))⁻¹) volume (0:ℝ) 1 := by
      simpa using (IntervalIntegrable.comp_sub_left (f := fun u : ℝ => (2 * Real.sqrt u)⁻¹)
        (c := (1:ℝ)) (hf := hsing1.symm))
    have hterm2 : ∀ (A B : ℝ),
        IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹ * A - (2 * Real.sqrt (1 - t))⁻¹ * B)
          volume (0:ℝ) 1 := by
      intro A B
      simpa [sub_eq_add_neg] using (hsing1.mul_const A).add ((hsing2.mul_const B).neg)
    have hstep : ∀ i : Fin n, IntervalIntegrable (fun t : ℝ => ZdotStar t x i j) volume (0:ℝ) 1 := by
      intro i
      exact (hterm2 (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
        (F i x.2 j - muX j)).const_mul ((Real.sqrt (n:ℝ))⁻¹)
    have hstep2 : ∀ i : Fin m, IntervalIntegrable (fun t : ℝ => ZdotStarStar t x i j) volume (0:ℝ) 1 := by
      intro i
      exact (hterm2 (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
        (G i x.2 j - muY j)).const_mul ((Real.sqrt (m:ℝ))⁻¹ * delta n m)
    have hsumI : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ → ℝ),
        (∀ i, IntervalIntegrable (g i) volume (0:ℝ) 1) →
        IntervalIntegrable (fun t => ∑ i, g i t) volume (0:ℝ) 1 := by
      intro ι _ g hg
      classical
      have key : ∀ s : Finset ι, IntervalIntegrable (fun t => ∑ i ∈ s, g i t) volume (0:ℝ) 1 := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using hpow.const_mul (0:ℝ)
        | insert a s ha ih =>
            have h1 : IntervalIntegrable (fun t => g a t + ∑ i ∈ s, g i t) volume (0:ℝ) 1 :=
              (hg a).add ih
            simpa [Finset.sum_insert ha] using h1
      simpa using key Finset.univ
    have hN := hsumI (fun (i : Fin n) (t : ℝ) => ZdotStar t x i j) hstep
    have hM := hsumI (fun (i : Fin m) (t : ℝ) => ZdotStarStar t x i j) hstep2
    exact hN.add hM
  have hsumInt : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ → ℝ),
      (∀ i, IntervalIntegrable (g i) volume (0:ℝ) 1) →
      IntervalIntegrable (fun t => ∑ i, g i t) volume (0:ℝ) 1 := by
    intro ι _ g hg
    classical
    have key : ∀ s : Finset ι, IntervalIntegrable (fun t => ∑ i ∈ s, g i t) volume (0:ℝ) 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa using (continuous_const : Continuous fun _ : ℝ => (0:ℝ)).intervalIntegrable (0:ℝ) 1
      | insert a s ha ih =>
          have h1 : IntervalIntegrable (fun t => g a t + ∑ i ∈ s, g i t) volume (0:ℝ) 1 :=
            (hg a).add ih
          simpa [Finset.sum_insert ha] using h1
    simpa using key Finset.univ
  have hsingT : ∀ (A B : ℝ),
      IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹ * A - (2 * Real.sqrt (1 - t))⁻¹ * B)
        volume (0:ℝ) 1 := by
    have hpow : IntervalIntegrable (fun t : ℝ => t ^ (-(1/2) : ℝ)) volume (0:ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1) (r := -(1/2)) (by norm_num)
    have hsing1 : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹) volume (0:ℝ) 1 := by
      have h := hpow.const_mul ((2:ℝ)⁻¹)
      refine h.congr_ae ?_
      have hμ : Set.uIoc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 := by
        rw [Set.uIoc]
        simp
      rw [hμ]
      filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Ioc (0:ℝ) 1) measurableSet_Ioc]
        with t ht
      have ht0 : (0:ℝ) < t := ht.1
      rw [Real.sqrt_eq_rpow, mul_inv, ← Real.rpow_neg ht0.le (1/2)]
    have hsing2 : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt (1 - t))⁻¹) volume (0:ℝ) 1 := by
      simpa using (IntervalIntegrable.comp_sub_left (f := fun u : ℝ => (2 * Real.sqrt u)⁻¹)
        (c := (1:ℝ)) (hf := hsing1.symm))
    intro A B
    simpa [sub_eq_add_neg] using (hsing1.mul_const A).add ((hsing2.mul_const B).neg)
  have hchain : ∀ (x : Ω × Ω), ∀ t ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => kappa (Z s x))
        (∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j) t := by
    intro x t ht
    have hκd : DifferentiableAt ℝ kappa (Z t x) :=
      (hκC3.differentiable (by norm_num)).differentiableAt
    have hfd : HasFDerivAt kappa (fderiv ℝ kappa (Z t x)) (Z t x) := hκd.hasFDerivAt
    have hZa : HasDerivAt (fun s : ℝ => Z s x) (Zdot t x) t :=
      hasDerivAt_pi.mpr (fun j => hZderiv x j t ht)
    have hcomp := hfd.comp_hasDerivAt t hZa
    have hdecomp : (∑ j : Fin p, (Zdot t x j) • (Pi.single j (1:ℝ) : Fin p → ℝ)) = Zdot t x := by
      funext i
      simp
      have hterm : ∀ j : Fin p,
          Zdot t x j * (Pi.single j (1:ℝ) : Fin p → ℝ) i = (if j = i then Zdot t x j else 0) := by
        intro j
        by_cases h : i = j
        · subst h
          rw [Pi.single_eq_same, mul_one]
          simp
        · rw [if_neg (fun hji : j = i => h hji.symm), Pi.single_eq_of_ne h, mul_zero]
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      simp
    have hval : (fderiv ℝ kappa (Z t x)) (Zdot t x)
        = ∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j := by
      calc (fderiv ℝ kappa (Z t x)) (Zdot t x)
          = (fderiv ℝ kappa (Z t x))
              (∑ j : Fin p, (Zdot t x j) • (Pi.single j (1:ℝ) : Fin p → ℝ)) := by
              rw [hdecomp]
        _ = ∑ j : Fin p,
              (fderiv ℝ kappa (Z t x)) ((Zdot t x j) • (Pi.single j (1:ℝ) : Fin p → ℝ)) :=
              map_sum _ _ _
        _ = ∑ j : Fin p,
              (Zdot t x j) • ((fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [map_smul]
        _ = ∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [smul_eq_mul, mul_comm]
    rw [hval] at hcomp
    exact hcomp
  have hcompInt : ∀ (x : Ω × Ω),
      IntervalIntegrable
        (fun t : ℝ => ∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j)
        volume (0:ℝ) 1 := by
    intro x
    have hstep : ∀ j : Fin p,
        IntervalIntegrable
          (fun t : ℝ => (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j)
          volume (0:ℝ) 1 := by
      intro j
      have hc : ContinuousOn (fun t : ℝ => (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)))
          (Set.uIcc (0:ℝ) 1) := (hfdcont x j).continuousOn
      exact IntervalIntegrable.continuousOn_mul (hZint x j) hc
    exact hsumInt (fun (j : Fin p) (t : ℝ) =>
      (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j) hstep
  have hFTC : ∀ x : Ω × Ω, kappa (Z 1 x) - kappa (Z 0 x)
      = ∫ t in (0:ℝ)..1,
          ∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j := by
    intro x
    have hcont : ContinuousOn (fun t : ℝ => kappa (Z t x)) (Set.Icc (0:ℝ) 1) :=
      ((hκC3.differentiable (by norm_num)).continuous.comp (hZcont x)).continuousOn
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := (0:ℝ)) (b := 1) (f := fun t : ℝ => kappa (Z t x))
      (f' := fun t : ℝ => ∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j)
      (by norm_num) hcont (fun t ht => hchain x t ht) (hcompInt x)
    exact h.symm


  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x j
    have hLX : (∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ *
        (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)))
        = Real.sqrt v * ((Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, X i x.1 j) - Real.sqrt (n:ℝ) * muX j)
          + Real.sqrt (1 - v) *
              ((Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, F i x.1 j) - Real.sqrt (n:ℝ) * muX j) := by
      calc (∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ *
            (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)))
          = (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n,
              (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))) := by
            rw [← Finset.mul_sum]
        _ = (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt v * (∑ i : Fin n, (X i x.1 j - muX j))
              + Real.sqrt (1 - v) * (∑ i : Fin n, (F i x.1 j - muX j))) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = Real.sqrt v * ((Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, (X i x.1 j - muX j)))
              + Real.sqrt (1 - v) * ((Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, (F i x.1 j - muX j))) := by
            ring
        _ = Real.sqrt v * ((Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, X i x.1 j) - Real.sqrt (n:ℝ) * muX j)
              + Real.sqrt (1 - v) *
                  ((Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, F i x.1 j) - Real.sqrt (n:ℝ) * muX j) := by
            rw [hdevN (fun i => X i x.1 j) (muX j), hdevN (fun i => F i x.1 j) (muX j)]
    have hLY : (∑ i : Fin m, ((Real.sqrt (m:ℝ))⁻¹ * delta n m) *
        (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)))
        = Real.sqrt v * (((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, Y i x.1 j)
              - (delta n m * Real.sqrt (m:ℝ)) * muY j)
          + Real.sqrt (1 - v) * (((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, G i x.1 j)
              - (delta n m * Real.sqrt (m:ℝ)) * muY j) := by
      calc (∑ i : Fin m, ((Real.sqrt (m:ℝ))⁻¹ * delta n m) *
            (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)))
          = ((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m,
              (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))) := by
            rw [← Finset.mul_sum]
        _ = ((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (Real.sqrt v * (∑ i : Fin m, (Y i x.1 j - muY j))
              + Real.sqrt (1 - v) * (∑ i : Fin m, (G i x.1 j - muY j))) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = Real.sqrt v * (((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, (Y i x.1 j - muY j)))
              + Real.sqrt (1 - v) *
                  (((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, (G i x.1 j - muY j))) := by
            ring
        _ = Real.sqrt v * (((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, Y i x.1 j)
              - (delta n m * Real.sqrt (m:ℝ)) * muY j)
              + Real.sqrt (1 - v) * (((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, G i x.1 j)
              - (delta n m * Real.sqrt (m:ℝ)) * muY j) := by
            rw [hdevM2 (fun i => Y i x.1 j) (muY j), hdevM2 (fun i => G i x.1 j) (muY j)]
    change Z 1 x j =
      Real.sqrt v * combVec n m (delta n m) muX muY (fun i : Fin n => X i x.1) (fun i : Fin m => Y i x.1) j
      + Real.sqrt (1 - v) * combVec n m (delta n m) muX muY (fun i : Fin n => F i x.1) (fun i : Fin m => G i x.1) j
    dsimp only [Z, Zstar, Zstarstar, combVec, normSum]
    simp only [Real.sqrt_one, Real.sqrt_zero, sub_self, one_mul, zero_mul, add_zero]
    rw [hLX, hLY]
    ring
  · intro x j
    have hF : (∑ i : Fin n, (Real.sqrt (n:ℝ))⁻¹ * (F i x.2 j - muX j))
        = (Real.sqrt (n:ℝ))⁻¹ * (∑ i : Fin n, F i x.2 j) - Real.sqrt (n:ℝ) * muX j := by
      rw [← Finset.mul_sum, hdevN (fun i => F i x.2 j) (muX j)]
    have hG : (∑ i : Fin m, ((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (G i x.2 j - muY j))
        = ((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (∑ i : Fin m, G i x.2 j)
          - (delta n m * Real.sqrt (m:ℝ)) * muY j := by
      rw [← Finset.mul_sum, hdevM2 (fun i => G i x.2 j) (muY j)]
    change Z 0 x j = combVec n m (delta n m) muX muY (fun i : Fin n => F i x.2) (fun i : Fin m => G i x.2) j
    dsimp only [Z, Zstar, Zstarstar, combVec, normSum]
    simp only [Real.sqrt_zero, Real.sqrt_one, sub_zero, zero_mul, one_mul, zero_add, add_zero]
    rw [hF, hG]
    ring
  · exact hZderiv
  · intro x j
    have hpow : IntervalIntegrable (fun t : ℝ => t ^ (-(1/2) : ℝ)) volume (0:ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1) (r := -(1/2)) (by norm_num)
    have hsing1 : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹) volume (0:ℝ) 1 := by
      have h := hpow.const_mul ((2:ℝ)⁻¹)
      refine h.congr_ae ?_
      have hμ : Set.uIoc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 := by
        rw [Set.uIoc]
        simp
      rw [hμ]
      filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Ioc (0:ℝ) 1) measurableSet_Ioc]
        with t ht
      have ht0 : (0:ℝ) < t := ht.1
      rw [Real.sqrt_eq_rpow, mul_inv, ← Real.rpow_neg ht0.le (1/2)]
    have hsing2 : IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt (1 - t))⁻¹) volume (0:ℝ) 1 := by
      simpa using (IntervalIntegrable.comp_sub_left (f := fun u : ℝ => (2 * Real.sqrt u)⁻¹)
        (c := (1:ℝ)) (hf := hsing1.symm))
    have hterm2 : ∀ (A B : ℝ),
        IntervalIntegrable (fun t : ℝ => (2 * Real.sqrt t)⁻¹ * A - (2 * Real.sqrt (1 - t))⁻¹ * B)
          volume (0:ℝ) 1 := by
      intro A B
      simpa [sub_eq_add_neg] using (hsing1.mul_const A).add ((hsing2.mul_const B).neg)
    have hstep : ∀ i : Fin n, IntervalIntegrable (fun t : ℝ => ZdotStar t x i j) volume (0:ℝ) 1 := by
      intro i
      exact (hterm2 (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
        (F i x.2 j - muX j)).const_mul ((Real.sqrt (n:ℝ))⁻¹)
    have hstep2 : ∀ i : Fin m, IntervalIntegrable (fun t : ℝ => ZdotStarStar t x i j) volume (0:ℝ) 1 := by
      intro i
      exact (hterm2 (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
        (G i x.2 j - muY j)).const_mul ((Real.sqrt (m:ℝ))⁻¹ * delta n m)
    have hsumI : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ → ℝ),
        (∀ i, IntervalIntegrable (g i) volume (0:ℝ) 1) →
        IntervalIntegrable (fun t => ∑ i, g i t) volume (0:ℝ) 1 := by
      intro ι _ g hg
      classical
      have key : ∀ s : Finset ι, IntervalIntegrable (fun t => ∑ i ∈ s, g i t) volume (0:ℝ) 1 := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using hpow.const_mul (0:ℝ)
        | insert a s ha ih =>
            have h1 : IntervalIntegrable (fun t => g a t + ∑ i ∈ s, g i t) volume (0:ℝ) 1 :=
              (hg a).add ih
            simpa [Finset.sum_insert ha] using h1
      simpa using key Finset.univ
    have hN := hsumI (fun (i : Fin n) (t : ℝ) => ZdotStar t x i j) hstep
    have hM := hsumI (fun (i : Fin m) (t : ℝ) => ZdotStarStar t x i j) hstep2
    exact hN.add hM
  · intro x t ht
    have hp2 : 2 ≤ p := by
      have h1 : (1:ℝ) < (p:ℝ) := by
        have h2 := Real.exp_lt_exp.mpr hlogp
        rwa [Real.exp_zero, Real.exp_log (by exact_mod_cast hp)] at h2
      have h3 : 1 < p := by exact_mod_cast h1
      omega
    have hphi : (1:ℝ) ≤ min phi1 phi2 := le_min hphi1 hphi2
    have hκC3 : ContDiff ℝ 3 kappa :=
      (statopia_math_node_2194576110_d2ad0cef p hp2 (min phi1 phi2) hphi phi0 hphi0_cont
        hphi0_left hphi0_right hphi0_range y).1
    have hκd : DifferentiableAt ℝ kappa (Z t x) :=
      (hκC3.differentiable (by norm_num)).differentiableAt
    have hfd : HasFDerivAt kappa (fderiv ℝ kappa (Z t x)) (Z t x) := hκd.hasFDerivAt
    have hZa : HasDerivAt (fun s : ℝ => Z s x) (Zdot t x) t :=
      hasDerivAt_pi.mpr (fun j => hZderiv x j t ht)
    have hcomp := hfd.comp_hasDerivAt t hZa
    have hdecomp : (∑ j : Fin p, (Zdot t x j) • (Pi.single j (1:ℝ) : Fin p → ℝ)) = Zdot t x := by
      funext i
      simp
      have hterm : ∀ j : Fin p,
          Zdot t x j * (Pi.single j (1:ℝ) : Fin p → ℝ) i = (if j = i then Zdot t x j else 0) := by
        intro j
        by_cases h : i = j
        · subst h
          rw [Pi.single_eq_same, mul_one]
          simp
        · rw [if_neg (fun hji : j = i => h hji.symm), Pi.single_eq_of_ne h, mul_zero]
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      simp
    have hval : (fderiv ℝ kappa (Z t x)) (Zdot t x)
        = ∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j := by
      calc (fderiv ℝ kappa (Z t x)) (Zdot t x)
          = (fderiv ℝ kappa (Z t x))
              (∑ j : Fin p, (Zdot t x j) • (Pi.single j (1:ℝ) : Fin p → ℝ)) := by
              rw [hdecomp]
        _ = ∑ j : Fin p,
              (fderiv ℝ kappa (Z t x)) ((Zdot t x j) • (Pi.single j (1:ℝ) : Fin p → ℝ)) :=
              map_sum _ _ _
        _ = ∑ j : Fin p,
              (Zdot t x j) • ((fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [map_smul]
        _ = ∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [smul_eq_mul, mul_comm]
    rw [hval] at hcomp
    exact hcomp
  · intro x
    have hsum : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ → ℝ),
        (∀ i, IntervalIntegrable (g i) volume (0:ℝ) 1) →
        IntervalIntegrable (fun t => ∑ i, g i t) volume (0:ℝ) 1 := by
      intro ι _ g hg
      classical
      have key : ∀ s : Finset ι, IntervalIntegrable (fun t => ∑ i ∈ s, g i t) volume (0:ℝ) 1 := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simpa using (continuous_const : Continuous fun _ : ℝ => (0:ℝ)).intervalIntegrable (0:ℝ) 1
        | insert a s ha ih =>
            have h1 : IntervalIntegrable (fun t => g a t + ∑ i ∈ s, g i t) volume (0:ℝ) 1 :=
              (hg a).add ih
            simpa [Finset.sum_insert ha] using h1
      simpa using key Finset.univ
    have hstep : ∀ j : Fin p,
        IntervalIntegrable
          (fun t : ℝ => (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j)
          volume (0:ℝ) 1 := by
      intro j
      have hc : ContinuousOn (fun t : ℝ => (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)))
          (Set.uIcc (0:ℝ) 1) := (hfdcont x j).continuousOn
      exact IntervalIntegrable.continuousOn_mul (hZint x j) hc
    exact hsum (fun (j : Fin p) (t : ℝ) =>
      (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j) hstep
  · exact Filter.Eventually.of_forall hFTC
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hFTC x]
    have hAB : (fun t : ℝ => ∑ j : Fin p, (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * Zdot t x j)
        = fun t : ℝ =>
            (∑ j : Fin p, ∑ i : Fin n,
              (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * ZdotStar t x i j)
          + (∑ j : Fin p, ∑ i : Fin m,
              (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * ZdotStarStar t x i j) := by
      funext t
      simp only [Zdot, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    have htermA : ∀ (j : Fin p) (i : Fin n),
        IntervalIntegrable
          (fun t : ℝ => (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * ZdotStar t x i j)
          volume (0:ℝ) 1 := by
      intro j i
      have hc : ContinuousOn
          (fun t : ℝ => (Real.sqrt (n:ℝ))⁻¹ * (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)))
          (Set.uIcc (0:ℝ) 1) := (continuous_const.mul (hfdcont x j)).continuousOn
      have h := (hsingT (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
        (F i x.2 j - muX j)).continuousOn_mul hc
      exact h.congr_ae (Filter.Eventually.of_forall (fun t => by
        simp only [ZdotStar]
        ring))
    have htermB : ∀ (j : Fin p) (i : Fin m),
        IntervalIntegrable
          (fun t : ℝ => (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * ZdotStarStar t x i j)
          volume (0:ℝ) 1 := by
      intro j i
      have hc : ContinuousOn
          (fun t : ℝ =>
            ((Real.sqrt (m:ℝ))⁻¹ * delta n m) * (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)))
          (Set.uIcc (0:ℝ) 1) := (continuous_const.mul (hfdcont x j)).continuousOn
      have h := (hsingT (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
        (G i x.2 j - muY j)).continuousOn_mul hc
      exact h.congr_ae (Filter.Eventually.of_forall (fun t => by
        simp only [ZdotStarStar]
        ring))
    have hA : IntervalIntegrable
        (fun t : ℝ => ∑ j : Fin p, ∑ i : Fin n,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * ZdotStar t x i j)
        volume (0:ℝ) 1 :=
      hsumInt (fun (j : Fin p) (t : ℝ) => ∑ i : Fin n,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * ZdotStar t x i j)
        (fun j => hsumInt (fun (i : Fin n) (t : ℝ) =>
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * ZdotStar t x i j) (fun i => htermA j i))
    have hB : IntervalIntegrable
        (fun t : ℝ => ∑ j : Fin p, ∑ i : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * ZdotStarStar t x i j)
        volume (0:ℝ) 1 :=
      hsumInt (fun (j : Fin p) (t : ℝ) => ∑ i : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * ZdotStarStar t x i j)
        (fun j => hsumInt (fun (i : Fin m) (t : ℝ) =>
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1:ℝ)) * ZdotStarStar t x i j) (fun i => htermB j i))
    rw [hAB, intervalIntegral.integral_add hA hB]

  /- @proof-region region.target-node.session.5e4a3ba6eea2ad32 end -/

end

end Statlib.Imported

