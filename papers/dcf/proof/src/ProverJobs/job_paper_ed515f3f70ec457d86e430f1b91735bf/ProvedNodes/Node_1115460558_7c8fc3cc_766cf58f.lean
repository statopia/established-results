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
theorem statopia_math_node_1115460558_7c8fc3cc : ∀ (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (Ω : Type*) [MeasurableSpace Ω]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (phi1 phi2 : ℝ) (y : Fin p → ℝ) (v : ℝ)
    (hp : 0 < p) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1),
    (let phi : ℝ := min phi1 phi2
     let beta : ℝ := phi * Real.log (p : ℝ)
     let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (n : ℝ))⁻¹ *
         (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
           + Real.sqrt (1 - t) * (F i x.2 j - muX j))
     let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
           + Real.sqrt (1 - t) * (G i x.2 j - muY j))
     let Z : ℝ → Ω × Ω → Fin p → ℝ := fun t x j =>
       (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
     let Zdotstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (n : ℝ))⁻¹ *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
           - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
     let Zdot : ℝ → Ω × Ω → Fin m → Fin p → ℝ := fun t x i j =>
       (Real.sqrt (m : ℝ))⁻¹ * delta n m *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
           - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
     let kappa : (Fin p → ℝ) → ℝ := fun w =>
       phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
     let Istar : Ω × Ω → ℝ := fun x =>
       ∫ t in (0 : ℝ)..1,
         ∑ j : Fin p, ∑ i : Fin n,
           (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j
     let Istarstar : Ω × Ω → ℝ := fun x =>
       ∫ t in (0 : ℝ)..1,
         ∑ j : Fin p, ∑ i : Fin m,
           (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j
     ∀ x : Ω × Ω, kappa (Z 1 x) - kappa (Z 0 x) = Istar x + Istarstar x) := by
  /- @proof-region region.target-node.session.44178e8449f20de0 begin -/
  intro phi0 hphi0_cont Ω hΩ n m p delta muX muY X Y F G phi1 phi2 y v hp hphi1 hphi2 hv0 hv1
  intro phi beta Zstar Zstarstar Z Zdotstar Zdot kappa Istar Istarstar
  intro x
  let fI : ℝ → ℝ := fun t =>
    ∑ j : Fin p, ∑ i : Fin n, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j
  let gI : ℝ → ℝ := fun t =>
    ∑ j : Fin p, ∑ i : Fin m, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j
  have hSpos : ∀ w : Fin p → ℝ, 0 < ∑ j : Fin p, Real.exp (beta * (w j - y j)) := by
    intro w
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨⟨0, hp⟩, Finset.mem_univ _⟩
  have hZderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun s => Z s x)
        (fun j => (∑ i : Fin n, Zdotstar t x i j) + (∑ i : Fin m, Zdot t x i j)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have ht1 : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
    have hsqrt1 : HasDerivAt (fun s : ℝ => Real.sqrt s) ((2 * Real.sqrt t)⁻¹) t := by
      simpa only [one_div] using Real.hasDerivAt_sqrt ht0
    have hsqrt2 : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s)) (-((2 * Real.sqrt (1 - t))⁻¹)) t := by
      have h1 : HasDerivAt (fun s : ℝ => Real.sqrt s) ((2 * Real.sqrt (1 - t))⁻¹) (1 - t) := by
        simpa only [one_div] using Real.hasDerivAt_sqrt ht1
      have h2 : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub 1
      have hcomp : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s))
          (((2 * Real.sqrt (1 - t))⁻¹) * (-1)) t := by
        first
          | exact h1.comp t h2
          | exact h2.comp t h1
          | exact h1.comp h2
          | exact h2.comp h1
      simpa only [mul_neg, mul_one] using hcomp
    have hZs : ∀ (i : Fin n) (j : Fin p),
        HasDerivAt (fun s : ℝ => Zstar s x i j) (Zdotstar t x i j) t := by
      intro i j
      have hA : HasDerivAt
          (fun s : ℝ => Real.sqrt s * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)))
          ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))) t :=
        hsqrt1.mul_const _
      have hB : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s) * (F i x.2 j - muX j))
          (-((2 * Real.sqrt (1 - t))⁻¹) * (F i x.2 j - muX j)) t :=
        hsqrt2.mul_const _
      have hAB := (hA.add hB).const_mul ((Real.sqrt (n : ℝ))⁻¹)
      simpa only [neg_mul] using hAB
    have hZss : ∀ (i : Fin m) (j : Fin p),
        HasDerivAt (fun s : ℝ => Zstarstar s x i j) (Zdot t x i j) t := by
      intro i j
      have hA : HasDerivAt
          (fun s : ℝ => Real.sqrt s * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)))
          ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))) t :=
        hsqrt1.mul_const _
      have hB : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s) * (G i x.2 j - muY j))
          (-((2 * Real.sqrt (1 - t))⁻¹) * (G i x.2 j - muY j)) t :=
        hsqrt2.mul_const _
      have hAB := (hA.add hB).const_mul ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
      simpa only [neg_mul] using hAB
    have hZj : ∀ j : Fin p, HasDerivAt (fun s : ℝ => Z s x j)
        ((∑ i : Fin n, Zdotstar t x i j) + (∑ i : Fin m, Zdot t x i j)) t := by
      intro j
      have hgenn : ∀ s : Finset (Fin n),
          HasDerivAt (fun y : ℝ => ∑ i ∈ s, Zstar y x i j) (∑ i ∈ s, Zdotstar t x i j) t := by
        intro s
        induction s using Finset.induction with
        | empty => simpa using (hasDerivAt_id t).const_mul (0 : ℝ)
        | insert a s ha ih =>
            have hfun : (fun y : ℝ => ∑ i ∈ insert a s, Zstar y x i j)
                = fun y : ℝ => Zstar y x a j + ∑ i ∈ s, Zstar y x i j := by
              funext y
              rw [Finset.sum_insert ha]
            rw [Finset.sum_insert ha, hfun]
            exact (hZs a j).add ih
      have hgenm : ∀ s : Finset (Fin m),
          HasDerivAt (fun y : ℝ => ∑ i ∈ s, Zstarstar y x i j) (∑ i ∈ s, Zdot t x i j) t := by
        intro s
        induction s using Finset.induction with
        | empty => simpa using (hasDerivAt_id t).const_mul (0 : ℝ)
        | insert a s ha ih =>
            have hfun : (fun y : ℝ => ∑ i ∈ insert a s, Zstarstar y x i j)
                = fun y : ℝ => Zstarstar y x a j + ∑ i ∈ s, Zstarstar y x i j := by
              funext y
              rw [Finset.sum_insert ha]
            rw [Finset.sum_insert ha, hfun]
            exact (hZss a j).add ih
      exact (hgenn Finset.univ).add (hgenm Finset.univ)
    exact (hasDerivAtFilter_pi).2 hZj
  have hlogdiff : ∀ w : Fin p → ℝ,
      DifferentiableAt ℝ
        (fun w : Fin p → ℝ => Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))) w := by
    intro w
    have hS : DifferentiableAt ℝ
        (fun w : Fin p → ℝ => ∑ j : Fin p, Real.exp (beta * (w j - y j))) w := by
      fun_prop
    first
      | exact hS.log (ne_of_gt (hSpos w))
      | exact DifferentiableAt.log (ne_of_gt (hSpos w)) hS
      | exact (Real.differentiableAt_log (ne_of_gt (hSpos w))).comp w hS
      | exact (Real.differentiableAt_log (ne_of_gt (hSpos w))).comp hS
  have hinnerdiff : ∀ w : Fin p → ℝ,
      DifferentiableAt ℝ
        (fun w : Fin p → ℝ => phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j))))) w := by
    intro w
    exact ((hlogdiff w).const_mul (beta⁻¹)).const_mul phi
  have hkdiff : ∀ w : Fin p → ℝ, DifferentiableAt ℝ kappa w := by
    intro w
    exact (hphi0_cont.differentiable (by simp)).differentiableAt.comp w (hinnerdiff w)
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun s => kappa (Z s x)) (fI t + gI t) t := by
    have hpi : ∀ (L : (Fin p → ℝ) →L[ℝ] ℝ) (c : Fin p → ℝ),
        L c = ∑ j : Fin p, c j * L (Pi.single j (1 : ℝ)) := by
      intro L c
      have hc : c = ∑ j : Fin p, c j • (Pi.single j (1 : ℝ) : Fin p → ℝ) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hc]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by simp)
    have hstep : ∀ {ι : Type} [Fintype ι] (c : ι → Fin p → ℝ) (L : (Fin p → ℝ) →L[ℝ] ℝ),
        ∑ j : Fin p, (∑ i : ι, c i j) * L (Pi.single j (1 : ℝ))
          = ∑ j : Fin p, ∑ i : ι, L (Pi.single j (1 : ℝ)) * c i j := by
      intro ι _ c L
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    intro t ht
    have hF : HasFDerivAt kappa (fderiv ℝ kappa (Z t x)) (Z t x) := (hkdiff (Z t x)).hasFDerivAt
    have hcomp : HasDerivAt (kappa ∘ fun s => Z s x)
        ((fderiv ℝ kappa (Z t x))
          (fun j => (∑ i : Fin n, Zdotstar t x i j) + (∑ i : Fin m, Zdot t x i j))) t := by
      first
        | exact hF.comp_hasDerivAt t (hZderiv t ht)
        | exact hF.comp_hasDerivAt (hZderiv t ht)
    have key : (fderiv ℝ kappa (Z t x))
        (fun j => (∑ i : Fin n, Zdotstar t x i j) + (∑ i : Fin m, Zdot t x i j)) = fI t + gI t := by
      have h1 := hpi (fderiv ℝ kappa (Z t x))
        (fun j => (∑ i : Fin n, Zdotstar t x i j) + (∑ i : Fin m, Zdot t x i j))
      rw [h1]
      have e1 : ∑ j : Fin p,
            ((∑ i : Fin n, Zdotstar t x i j) + (∑ i : Fin m, Zdot t x i j)) *
              (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ))
          = (∑ j : Fin p, (∑ i : Fin n, Zdotstar t x i j) * (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)))
            + ∑ j : Fin p, (∑ i : Fin m, Zdot t x i j) * (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => add_mul _ _ _)
      rw [e1,
        hstep (ι := Fin n) (fun (i : Fin n) (j : Fin p) => Zdotstar t x i j) (fderiv ℝ kappa (Z t x)),
        hstep (ι := Fin m) (fun (i : Fin m) (j : Fin p) => Zdot t x i j) (fderiv ℝ kappa (Z t x))]
    rw [key] at hcomp
    exact hcomp
  have hcont : ContinuousOn (fun s => kappa (Z s x)) (Set.Icc (0 : ℝ) 1) := by
    have hk : Continuous kappa := by
      rw [continuous_iff_continuousAt]
      exact fun w => (hkdiff w).continuousAt
    have hZj : ∀ j : Fin p, Continuous (fun s : ℝ => Z s x j) := by
      intro j
      show Continuous (fun s : ℝ =>
        (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt s * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
            + Real.sqrt (1 - s) * (F i x.2 j - muX j)))
        + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt s * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
            + Real.sqrt (1 - s) * (G i x.2 j - muY j))))
      fun_prop
    have hZc : Continuous (fun s : ℝ => Z s x) := by
      rw [continuous_iff_continuousAt]
      intro s
      show Filter.Tendsto (fun s : ℝ => Z s x) (nhds s) (nhds (Z s x))
      rw [tendsto_pi_nhds]
      exact fun j => (hZj j).continuousAt
    have h1 : Continuous (fun s => kappa (Z s x)) := hk.comp hZc
    exact fun s hs => (h1.continuousAt).continuousWithinAt
  have hZj' : ∀ j : Fin p, Continuous (fun s : ℝ => Z s x j) := by
    intro j
    show Continuous (fun s : ℝ =>
      (∑ i : Fin n, (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt s * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
          + Real.sqrt (1 - s) * (F i x.2 j - muX j)))
      + (∑ i : Fin m, (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt s * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
          + Real.sqrt (1 - s) * (G i x.2 j - muY j))))
    fun_prop
  have hcurve : Continuous (fun s : ℝ => Z s x) := by
    rw [continuous_iff_continuousAt]
    intro s
    show Filter.Tendsto (fun s : ℝ => Z s x) (nhds s) (nhds (Z s x))
    rw [tendsto_pi_nhds]
    exact fun j => (hZj' j).continuousAt
  have hScd : ContDiff ℝ 3 (fun w : Fin p → ℝ => ∑ j : Fin p, Real.exp (beta * (w j - y j))) := by
    fun_prop
  have hlogcd : ContDiff ℝ 3
      (fun w : Fin p → ℝ => Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))) :=
    hScd.log (fun w => (hSpos w).ne')
  have hinnercd : ContDiff ℝ 3
      (fun w : Fin p → ℝ => phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j))))) :=
    contDiff_const.mul (contDiff_const.mul hlogcd)
  have hkappaC : ContDiff ℝ 3 kappa := hphi0_cont.comp hinnercd
  have hfdcont : Continuous (fun pp : (Fin p → ℝ) × (Fin p → ℝ) => (fderiv ℝ kappa pp.1) pp.2) :=
    (hkappaC.contDiff_fderiv_apply (m := 0) (by decide)).continuous
  have hAcont : ∀ j : Fin p,
      Continuous (fun t : ℝ => (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ))) := by
    intro j
    have h1 : Continuous (fun t : ℝ => Z t x) := hcurve
    have h2 : Continuous (fun _ : ℝ => (Pi.single j (1 : ℝ) : Fin p → ℝ)) := continuous_const
    have hpair : Continuous (fun t : ℝ => (Z t x, (Pi.single j (1 : ℝ) : Fin p → ℝ))) :=
      Continuous.prodMk h1 h2
    exact hfdcont.comp hpair
  have hmod0 : IntervalIntegrable (fun t : ℝ => (Real.sqrt t)⁻¹) volume (0 : ℝ) 1 := by
    have hbase : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    refine IntervalIntegrable.congr ?_ hbase
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    show t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (x := t) (le_of_lt ht0)]
  have hmod1 : IntervalIntegrable (fun t : ℝ => (Real.sqrt (1 - t))⁻¹) volume (0 : ℝ) 1 := by
    have h := hmod0.comp_sub_left (1 : ℝ)
    rw [show (1 : ℝ) - 1 = 0 by norm_num, show (1 : ℝ) - 0 = 1 by norm_num] at h
    rw [intervalIntegrable_iff] at h ⊢
    rwa [Set.uIoc_comm] at h
  have hW : IntervalIntegrable
      (fun t : ℝ => (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) volume (0 : ℝ) 1 :=
    hmod0.add hmod1
  have hhalf : ∀ a : ℝ, (2 * a)⁻¹ = (1 / 2) * a⁻¹ := by
    intro a
    rcases eq_or_ne a 0 with h | ha
    · simp [h]
    · field_simp
  have key : ∀ (B : ℝ → ℝ), Continuous B → ∀ (c d : ℝ),
      IntervalIntegrable
        (fun t : ℝ => B t * (c * (2 * Real.sqrt t)⁻¹ + d * (2 * Real.sqrt (1 - t))⁻¹))
        volume (0 : ℝ) 1 := by
    intro B hB c d
    obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := B) (fun t ht => hB.continuousAt.continuousWithinAt)
    set C : ℝ := max C0 0 with hCdef
    have hCnn : 0 ≤ C := le_max_right _ _
    have hCB : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖B t‖ ≤ C :=
      fun t ht => le_trans (hC0 t ht) (le_max_left _ _)
    have hmeasB : Measurable
        (fun t : ℝ => c * (2 * Real.sqrt t)⁻¹ + d * (2 * Real.sqrt (1 - t))⁻¹) := by
      have h1 : Measurable (fun t : ℝ => (2 * Real.sqrt t)⁻¹) :=
        (continuous_const.mul Real.continuous_sqrt).measurable.inv
      have hS2 : Measurable (fun t : ℝ => Real.sqrt (1 - t)) :=
        Real.continuous_sqrt.measurable.comp (measurable_const.sub measurable_id)
      have h2 : Measurable (fun t : ℝ => (2 * Real.sqrt (1 - t))⁻¹) :=
        (measurable_const.mul hS2).inv
      exact (measurable_const.mul h1).add (measurable_const.mul h2)
    rw [intervalIntegrable_iff]
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => (C * (|c| + |d|)) * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)) ?_ ?_ ?_
    · have hc := hW.const_mul (C * (|c| + |d|))
      rw [intervalIntegrable_iff] at hc
      simpa using hc
    · exact (hB.measurable.mul hmeasB).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hs1 : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht0
      have hinv1 : 0 ≤ (Real.sqrt t)⁻¹ := inv_nonneg.2 (le_of_lt hs1)
      have hinv2 : 0 ≤ (Real.sqrt (1 - t))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      have hWnn : 0 ≤ (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹ := add_nonneg hinv1 hinv2
      have hBt : ‖B t‖ ≤ C := hCB t (Set.mem_Icc.2 ⟨le_of_lt ht0, ht1⟩)
      have hA1 : ‖c * (2 * Real.sqrt t)⁻¹‖ = |c| * ((1 / 2) * (Real.sqrt t)⁻¹) := by
        rw [Real.norm_eq_abs, abs_mul, hhalf,
          abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hinv1)]
      have hA2 : ‖d * (2 * Real.sqrt (1 - t))⁻¹‖ = |d| * ((1 / 2) * (Real.sqrt (1 - t))⁻¹) := by
        rw [Real.norm_eq_abs, abs_mul, hhalf,
          abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hinv2)]
      have hinner : ‖c * (2 * Real.sqrt t)⁻¹ + d * (2 * Real.sqrt (1 - t))⁻¹‖
          ≤ (|c| + |d|) * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) := by
        have h3 := norm_add_le (c * (2 * Real.sqrt t)⁻¹) (d * (2 * Real.sqrt (1 - t))⁻¹)
        rw [hA1, hA2] at h3
        nlinarith [h3, hWnn, abs_nonneg c, abs_nonneg d, hinv1, hinv2]
      rw [norm_mul]
      calc ‖B t‖ * ‖c * (2 * Real.sqrt t)⁻¹ + d * (2 * Real.sqrt (1 - t))⁻¹‖
          ≤ C * ((|c| + |d|) * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)) :=
            mul_le_mul hBt hinner (norm_nonneg _) hCnn
        _ = (C * (|c| + |d|)) * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) := by ring
  have hterm : ∀ (j : Fin p) (i : Fin n),
      IntervalIntegrable
        (fun t : ℝ => (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j)
        volume (0 : ℝ) 1 := by
    intro j i
    have hZ : ∀ t : ℝ, Zdotstar t x i j = (Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
          - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)) := fun t => rfl
    refine IntervalIntegrable.congr (f := fun t : ℝ =>
      (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) *
        (((Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))) * (2 * Real.sqrt t)⁻¹
          + (-((Real.sqrt (n : ℝ))⁻¹ * (F i x.2 j - muX j))) * (2 * Real.sqrt (1 - t))⁻¹)) ?_ ?_
    · intro t ht
      simp only []
      rw [hZ t]
      ring
    · exact key _ (hAcont j) _ _
  have htermB : ∀ (j : Fin p) (i : Fin m),
      IntervalIntegrable
        (fun t : ℝ => (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j)
        volume (0 : ℝ) 1 := by
    intro j i
    have hZ : ∀ t : ℝ, Zdot t x i j = (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
          - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)) := fun t => rfl
    refine IntervalIntegrable.congr (f := fun t : ℝ =>
      (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) *
        ((((Real.sqrt (m : ℝ))⁻¹ * delta n m) * (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))) * (2 * Real.sqrt t)⁻¹
          + (-(((Real.sqrt (m : ℝ))⁻¹ * delta n m) * (G i x.2 j - muY j))) * (2 * Real.sqrt (1 - t))⁻¹)) ?_ ?_
    · intro t ht
      simp only []
      rw [hZ t]
      ring
    · exact key _ (hAcont j) _ _
  have hIA : IntervalIntegrable fI volume (0 : ℝ) 1 := by
    have hstep1 : ∀ j : Fin p, IntervalIntegrable
        (fun t : ℝ => ∑ i : Fin n,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j) volume (0 : ℝ) 1 := by
      intro j
      refine IntervalIntegrable.congr (f := ∑ i : Fin n, fun t : ℝ =>
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j) ?_
        (IntervalIntegrable.sum (s := Finset.univ) (f := fun i : Fin n => fun t : ℝ =>
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j)
          (fun i _ => hterm j i))
      intro t ht
      show (∑ i : Fin n, fun t' : ℝ =>
          (fderiv ℝ kappa (Z t' x)) (Pi.single j (1 : ℝ)) * Zdotstar t' x i j) t
        = ∑ i : Fin n, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j
      simp only [Finset.sum_apply]
    refine IntervalIntegrable.congr (f := ∑ j : Fin p, fun t : ℝ => ∑ i : Fin n,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j) ?_
      (IntervalIntegrable.sum (s := Finset.univ) (f := fun j : Fin p => fun t : ℝ =>
        ∑ i : Fin n, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j)
        (fun j _ => hstep1 j))
    intro t ht
    show (∑ j : Fin p, fun t' : ℝ => ∑ i : Fin n,
        (fderiv ℝ kappa (Z t' x)) (Pi.single j (1 : ℝ)) * Zdotstar t' x i j) t
      = ∑ j : Fin p, ∑ i : Fin n,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j
    simp only [Finset.sum_apply]
  have hIB : IntervalIntegrable gI volume (0 : ℝ) 1 := by
    have hstep1 : ∀ j : Fin p, IntervalIntegrable
        (fun t : ℝ => ∑ i : Fin m,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j) volume (0 : ℝ) 1 := by
      intro j
      refine IntervalIntegrable.congr (f := ∑ i : Fin m, fun t : ℝ =>
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j) ?_
        (IntervalIntegrable.sum (s := Finset.univ) (f := fun i : Fin m => fun t : ℝ =>
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j)
          (fun i _ => htermB j i))
      intro t ht
      show (∑ i : Fin m, fun t' : ℝ =>
          (fderiv ℝ kappa (Z t' x)) (Pi.single j (1 : ℝ)) * Zdot t' x i j) t
        = ∑ i : Fin m, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j
      simp only [Finset.sum_apply]
    refine IntervalIntegrable.congr (f := ∑ j : Fin p, fun t : ℝ => ∑ i : Fin m,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j) ?_
      (IntervalIntegrable.sum (s := Finset.univ) (f := fun j : Fin p => fun t : ℝ =>
        ∑ i : Fin m, (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j)
        (fun j _ => hstep1 j))
    intro t ht
    show (∑ j : Fin p, fun t' : ℝ => ∑ i : Fin m,
        (fderiv ℝ kappa (Z t' x)) (Pi.single j (1 : ℝ)) * Zdot t' x i j) t
      = ∑ j : Fin p, ∑ i : Fin m,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdot t x i j
    simp only [Finset.sum_apply]
  have hint : IntervalIntegrable (fun t => fI t + gI t) volume (0 : ℝ) 1 := hIA.add hIB
  have hFTC : ∫ t in (0 : ℝ)..1, (fI t + gI t) = kappa (Z 1 x) - kappa (Z 0 x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
  have hsplit : ∫ t in (0 : ℝ)..1, (fI t + gI t) =
      (∫ t in (0 : ℝ)..1, fI t) + ∫ t in (0 : ℝ)..1, gI t :=
    intervalIntegral.integral_add hIA hIB
  have e1 : Istar x = ∫ t in (0 : ℝ)..1, fI t := rfl
  have e2 : Istarstar x = ∫ t in (0 : ℝ)..1, gI t := rfl
  rw [e1, e2, ← hsplit, hFTC]
  /- @proof-region region.target-node.session.44178e8449f20de0 end -/

end

end Statlib.Imported

