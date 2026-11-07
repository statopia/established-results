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
theorem statopia_math_node_3923401065_5b4914e1 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
     ∀ (Ckappa : ℝ),
       (∀ (w : Fin p → ℝ) (j : Fin p),
           |(fderiv ℝ kappa w) (Pi.single j (1 : ℝ))| ≤ Ckappa * phi) →
         ∀ᵐ q ∂((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (P.prod P)),
           ‖∑ j : Fin p, ∑ i : Fin n,
               (fderiv ℝ kappa (Z q.1 q.2)) (Pi.single j (1 : ℝ)) *
                 Zdotstar q.1 q.2 i j‖
             ≤ Ckappa * phi * (Real.sqrt (n : ℝ))⁻¹ *
                 (((Real.sqrt q.1)⁻¹ + (Real.sqrt (1 - q.1))⁻¹) *
                   (∑ j : Fin p, ∑ i : Fin n,
                     (|X i q.2.1 j - muX j| + |F i q.2.1 j - muX j| +
                       |F i q.2.2 j - muX j|)))) := by
  /- @proof-region region.target-node.session.3af60b2a5ea02370 begin -/
  intro Ω instΩ P instP n m p delta muX muY X Y F G phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
    hn hm hp hlogp hXm hYm hFm hGm hX3 hF3 phi1 phi2 hphi1 hphi2 v hv0 hv1 y
  intro phi beta Zstar Zstarstar Z Zdotstar kappa Ckappa hkappa
  filter_upwards with q
  obtain ⟨t, x⟩ := q
  let D : Fin n → Fin p → ℝ := fun i j =>
    |X i x.1 j - muX j| + |F i x.1 j - muX j| + |F i x.2 j - muX j|
  have hA : ∀ j : Fin p, |(fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ))| ≤ Ckappa * phi :=
    fun j => hkappa (Z t x) j
  have hK : 0 ≤ Ckappa * phi := by
    have h1 := hA ⟨0, hp⟩
    have h2 : (0 : ℝ) ≤ |(fderiv ℝ kappa (Z t x)) (Pi.single ⟨0, hp⟩ (1 : ℝ))| := abs_nonneg _
    linarith
  have hZd : ∀ (i : Fin n) (j : Fin p), |Zdotstar t x i j| ≤
      (Real.sqrt (n : ℝ))⁻¹ * (((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) * D i j) := by
    intro i j
    change |(Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ *
            (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))|
      ≤ (Real.sqrt (n : ℝ))⁻¹ *
        (((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
          (|X i x.1 j - muX j| + |F i x.1 j - muX j| + |F i x.2 j - muX j|))
    set xa : ℝ := X i x.1 j - muX j with hxa
    set fa : ℝ := F i x.1 j - muX j with hfa
    set fb : ℝ := F i x.2 j - muX j with hfb
    set P : ℝ := Real.sqrt v * xa + Real.sqrt (1 - v) * fa with hP
    set c1 : ℝ := (2 * Real.sqrt t)⁻¹ with hc1
    set c2 : ℝ := (2 * Real.sqrt (1 - t))⁻¹ with hc2
    set u1 : ℝ := (Real.sqrt t)⁻¹ with hu1
    set u2 : ℝ := (Real.sqrt (1 - t))⁻¹ with hu2
    have hsv0 : (0 : ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg v
    have hsv1 : Real.sqrt v ≤ 1 := by
      have h : Real.sqrt v ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hv1
      simpa using h
    have hsf0 : (0 : ℝ) ≤ Real.sqrt (1 - v) := Real.sqrt_nonneg (1 - v)
    have hsf1 : Real.sqrt (1 - v) ≤ 1 := by
      have h : Real.sqrt (1 - v) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      simpa using h
    have hcn : (0 : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg (n : ℝ))
    have hc1nn : 0 ≤ c1 := by rw [hc1]; exact inv_nonneg.mpr (by positivity)
    have hc2nn : 0 ≤ c2 := by rw [hc2]; exact inv_nonneg.mpr (by positivity)
    have hu1nn : 0 ≤ u1 := by rw [hu1]; exact inv_nonneg.mpr (Real.sqrt_nonneg t)
    have hu2nn : 0 ≤ u2 := by rw [hu2]; exact inv_nonneg.mpr (Real.sqrt_nonneg (1 - t))
    have hc1le : c1 ≤ u1 := by
      rw [hc1, hu1]
      rcases eq_or_lt_of_le (Real.sqrt_nonneg t) with h | h
      · rw [← h]; norm_num
      · have h3 : (2 * Real.sqrt t)⁻¹ = (2 : ℝ)⁻¹ * (Real.sqrt t)⁻¹ := by
          rw [mul_inv, mul_comm]
        rw [h3]
        have h6 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
        rw [h6]
        nlinarith [inv_nonneg.mpr (Real.sqrt_nonneg t)]
    have hc2le : c2 ≤ u2 := by
      rw [hc2, hu2]
      rcases eq_or_lt_of_le (Real.sqrt_nonneg (1 - t)) with h | h
      · rw [← h]; norm_num
      · have h3 : (2 * Real.sqrt (1 - t))⁻¹ = (2 : ℝ)⁻¹ * (Real.sqrt (1 - t))⁻¹ := by
          rw [mul_inv, mul_comm]
        rw [h3]
        have h6 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
        rw [h6]
        nlinarith [inv_nonneg.mpr (Real.sqrt_nonneg (1 - t))]
    have hPle : |P| ≤ |xa| + |fa| := by
      rw [hP]
      have h1 : |Real.sqrt v * xa + Real.sqrt (1 - v) * fa| ≤
          Real.sqrt v * |xa| + Real.sqrt (1 - v) * |fa| := by
        have h := abs_add_le (Real.sqrt v * xa) (Real.sqrt (1 - v) * fa)
        rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hsf0] at h
        exact h
      refine h1.trans ?_
      have h2 : Real.sqrt v * |xa| ≤ 1 * |xa| :=
        mul_le_mul_of_nonneg_right hsv1 (abs_nonneg xa)
      have h3 : Real.sqrt (1 - v) * |fa| ≤ 1 * |fa| :=
        mul_le_mul_of_nonneg_right hsf1 (abs_nonneg fa)
      linarith
    have htri : |c1 * P - c2 * fb| ≤ u1 * |P| + u2 * |fb| := by
      have h1 : |c1 * P - c2 * fb| ≤ c1 * |P| + c2 * |fb| := by
        have h := abs_add_le (c1 * P) (-(c2 * fb))
        rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hc1nn, abs_of_nonneg hc2nn] at h
        simpa using h
      nlinarith [h1, hc1le, hc2le, abs_nonneg P, abs_nonneg fb]
    have hmid : u1 * |P| + u2 * |fb| ≤ (u1 + u2) * (|xa| + |fa| + |fb|) := by
      nlinarith [hPle, abs_nonneg xa, abs_nonneg fa, abs_nonneg fb, hu1nn, hu2nn]
    calc |(Real.sqrt (n : ℝ))⁻¹ * (c1 * P - c2 * fb)|
        = (Real.sqrt (n : ℝ))⁻¹ * |c1 * P - c2 * fb| := by
          rw [abs_mul, abs_of_nonneg hcn]
      _ ≤ (Real.sqrt (n : ℝ))⁻¹ * (u1 * |P| + u2 * |fb|) :=
          mul_le_mul_of_nonneg_left htri hcn
      _ ≤ (Real.sqrt (n : ℝ))⁻¹ * ((u1 + u2) * (|xa| + |fa| + |fb|)) :=
          mul_le_mul_of_nonneg_left hmid hcn
  have hterm : ∀ (j : Fin p) (i : Fin n),
      |(fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j| ≤
        (Ckappa * phi) *
          ((Real.sqrt (n : ℝ))⁻¹ * (((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) * D i j)) := by
    intro j i
    have h := mul_le_mul (hA j) (hZd i j) (abs_nonneg (Zdotstar t x i j)) hK
    rwa [← abs_mul] at h
  have hstep1 : ‖∑ j : Fin p, ∑ i : Fin n,
        (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j‖ ≤
      ∑ j : Fin p, ∑ i : Fin n,
        |(fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j| := by
    calc ‖∑ j : Fin p, ∑ i : Fin n,
          (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j‖
        ≤ ∑ j : Fin p, ‖∑ i : Fin n,
            (fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j : Fin p, ∑ i : Fin n,
            ‖(fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j‖ :=
          Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
      _ = ∑ j : Fin p, ∑ i : Fin n,
            |(fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j| := by
          simp only [Real.norm_eq_abs]
  have hstep2 : ∑ j : Fin p, ∑ i : Fin n,
        |(fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j| ≤
      Ckappa * phi * (Real.sqrt (n : ℝ))⁻¹ *
        (((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) * (∑ j : Fin p, ∑ i : Fin n, D i j)) := by
    calc ∑ j : Fin p, ∑ i : Fin n,
          |(fderiv ℝ kappa (Z t x)) (Pi.single j (1 : ℝ)) * Zdotstar t x i j|
        ≤ ∑ j : Fin p, ∑ i : Fin n, (Ckappa * phi) *
            ((Real.sqrt (n : ℝ))⁻¹ *
              (((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) * D i j)) :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hterm j i))
      _ = Ckappa * phi * (Real.sqrt (n : ℝ))⁻¹ *
            (((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
              (∑ j : Fin p, ∑ i : Fin n, D i j)) := by
          simp only [← Finset.mul_sum]
          ring
  exact le_trans hstep1 hstep2
  /- @proof-region region.target-node.session.3af60b2a5ea02370 end -/

end

end Statlib.Imported

