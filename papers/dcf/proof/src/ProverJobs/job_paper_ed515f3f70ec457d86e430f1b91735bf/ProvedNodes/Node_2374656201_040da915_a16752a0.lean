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
theorem statopia_math_node_2374656201_040da915 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muY : Fin p → ℝ)
    (Y G : Fin m → Ω → Fin p → ℝ)
    (t v phi beta C1 C2 C3 : ℝ) (i : Fin m) (j : Fin p)
    (W : Ω × Ω → Fin p → ℝ)
    (Q : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ)
    (hYm : ∀ ii : Fin m, Measurable (Y ii))
    (hGm : ∀ ii : Fin m, Measurable (G ii))
    (hY3 : ∀ (ii : Fin m) (l : Fin p), Integrable (fun ω => |Y ii ω l - muY l| ^ 3) P)
    (hG3 : ∀ (ii : Fin m) (l : Fin p), Integrable (fun ω => |G ii ω l - muY l| ^ 3) P)
    (ht : 0 < t) (ht1 : t < 1) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hp : 0 < p) (hm : 0 < m) (hbeta : 0 < beta) (hC1 : 1 ≤ C1) (hC3 : 1 ≤ C3)
    (hQnn : ∀ (a b c : Fin p) (w : Fin p → ℝ), 0 ≤ Q a b c w)
    (hQsum : ∀ w : Fin p → ℝ,
      ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, Q a b c w ≤ C1 * C2 * phi * beta ^ 2)
    (hQmeas : ∀ a b c : Fin p, Measurable (fun x : Ω × Ω => Q a b c (W x))),
    (let Zs : Ω × Ω → Fin p → ℝ := fun x r =>
        ((Real.sqrt (m : ℝ))⁻¹ * delta n m) *
          (Real.sqrt t * (Real.sqrt v * (Y i x.1 r - muY r)
              + Real.sqrt (1 - v) * (G i x.1 r - muY r))
            + Real.sqrt (1 - t) * (G i x.2 r - muY r))
     let Zd : Ω × Ω → ℝ := fun x =>
        ((Real.sqrt (m : ℝ))⁻¹ * delta n m) *
          ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j)
              + Real.sqrt (1 - v) * (G i x.1 j - muY j))
            - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
     Integrable
       (fun x : Ω × Ω =>
         ∑ k : Fin p, ∑ l : Fin p,
           (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
            else C1 * C2 * phi * beta ^ 2)
           * |Zs x k| * |Zs x l| * |Zd x|)
       (P.prod P)) := by
  /- @proof-region region.target-node.session.36e9fcaedcc0af30 begin -/
  classical
  intro Ω _ P _ n m p delta muY Y G t v phi beta C1 C2 C3 i j W Q
  intro hYm hGm hY3 hG3 ht ht1 hv hv1 hp hm hbeta hC1 hC3 hQnn hQsum hQmeas
  let Zs : Ω × Ω → Fin p → ℝ := fun x r =>
      ((Real.sqrt (m : ℝ))⁻¹ * delta n m) *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 r - muY r)
            + Real.sqrt (1 - v) * (G i x.1 r - muY r))
          + Real.sqrt (1 - t) * (G i x.2 r - muY r))
  let Zd : Ω × Ω → ℝ := fun x =>
      ((Real.sqrt (m : ℝ))⁻¹ * delta n m) *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j)
            + Real.sqrt (1 - v) * (G i x.1 j - muY j))
          - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
  change Integrable (fun x : Ω × Ω =>
      ∑ k : Fin p, ∑ l : Fin p,
        (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
         else C1 * C2 * phi * beta ^ 2)
        * |Zs x k| * |Zs x l| * |Zd x|) (P.prod P)
  let Pp : Fin p → Ω × Ω → ℝ := fun r x =>
      |Y i x.1 r - muY r| + |G i x.1 r - muY r| + |G i x.2 r - muY r|
  let c : ℝ := (Real.sqrt (m : ℝ))⁻¹ * |delta n m|
  let Wt : ℝ := (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹
  let K : ℝ := C3 * (C1 * C2 * phi * beta ^ 2)
  have hKnn : 0 ≤ C1 * C2 * phi * beta ^ 2 := by
    have h := hQsum (fun _ => (0 : ℝ))
    have hnn : 0 ≤ ∑ a : Fin p, ∑ b : Fin p, ∑ c' : Fin p, Q a b c' (fun _ => (0 : ℝ)) := by
      apply Finset.sum_nonneg
      intro a _
      apply Finset.sum_nonneg
      intro b _
      apply Finset.sum_nonneg
      intro c' _
      exact hQnn a b c' _
    linarith
  have hC3nn : (0 : ℝ) ≤ C3 := by linarith
  have hc : (0 : ℝ) ≤ c := by
    show (0 : ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ * |delta n m|
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (abs_nonneg _)
  have hWtnn : (0 : ℝ) ≤ Wt := by
    show (0 : ℝ) ≤ (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹
    exact add_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hKnn' : (0 : ℝ) ≤ K := by
    show (0 : ℝ) ≤ C3 * (C1 * C2 * phi * beta ^ 2)
    exact mul_nonneg hC3nn hKnn
  have hQle : ∀ (a b cc : Fin p) (w : Fin p → ℝ), Q a b cc w ≤ C1 * C2 * phi * beta ^ 2 := by
    intro a b cc w
    have h1 : Q a b cc w ≤ ∑ c' : Fin p, Q a b c' w :=
      Finset.single_le_sum (f := fun c' : Fin p => Q a b c' w)
        (fun c' _ => hQnn a b c' w) (Finset.mem_univ cc)
    have h2 : (∑ c' : Fin p, Q a b c' w) ≤ ∑ b' : Fin p, ∑ c' : Fin p, Q a b' c' w :=
      Finset.single_le_sum (f := fun b' : Fin p => ∑ c' : Fin p, Q a b' c' w)
        (fun b' _ => Finset.sum_nonneg (fun c' _ => hQnn a b' c' w)) (Finset.mem_univ b)
    have h3 : (∑ b' : Fin p, ∑ c' : Fin p, Q a b' c' w)
        ≤ ∑ a' : Fin p, ∑ b' : Fin p, ∑ c' : Fin p, Q a' b' c' w :=
      Finset.single_le_sum (f := fun a' : Fin p => ∑ b' : Fin p, ∑ c' : Fin p, Q a' b' c' w)
        (fun a' _ => Finset.sum_nonneg (fun b' _ => Finset.sum_nonneg (fun c' _ => hQnn a' b' c' w)))
        (Finset.mem_univ a)
    linarith [hQsum w]
  have hq_le : ∀ (x : Ω × Ω) (k l : Fin p),
      (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
       else C1 * C2 * phi * beta ^ 2) ≤ K := by
    intro x k l
    by_cases h : (∀ r : Fin p, |Zs x r| * beta ≤ 1)
    · rw [if_pos h]
      show C3 * Q l k j (W x) ≤ C3 * (C1 * C2 * phi * beta ^ 2)
      exact mul_le_mul_of_nonneg_left (hQle l k j (W x)) hC3nn
    · rw [if_neg h]
      show C1 * C2 * phi * beta ^ 2 ≤ C3 * (C1 * C2 * phi * beta ^ 2)
      calc C1 * C2 * phi * beta ^ 2 = 1 * (C1 * C2 * phi * beta ^ 2) := by ring
        _ ≤ C3 * (C1 * C2 * phi * beta ^ 2) := mul_le_mul_of_nonneg_right (by linarith) hKnn
  have hq_nn : ∀ (x : Ω × Ω) (k l : Fin p),
      (0 : ℝ) ≤ (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
       else C1 * C2 * phi * beta ^ 2) := by
    intro x k l
    by_cases h : (∀ r : Fin p, |Zs x r| * beta ≤ 1)
    · rw [if_pos h]
      exact mul_nonneg hC3nn (hQnn l k j (W x))
    · rw [if_neg h]
      exact hKnn
  have hWtval : Wt = (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹ := rfl
  have hPpval : ∀ (r : Fin p) (x : Ω × Ω),
      Pp r x = |Y i x.1 r - muY r| + |G i x.1 r - muY r| + |G i x.2 r - muY r| := by
    intro r x
    rfl
  have hst0 : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hst_le : Real.sqrt t ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (le_of_lt ht1)
  have hsv0 : (0 : ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hsv_le : Real.sqrt v ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hv1
  have hs1v0 : (0 : ℝ) ≤ Real.sqrt (1 - v) := Real.sqrt_nonneg _
  have hs1v_le : Real.sqrt (1 - v) ≤ 1 := by
    have h : Real.sqrt (1 - v) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    simpa using h
  have hs1t0 : (0 : ℝ) ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
  have hs1t_le : Real.sqrt (1 - t) ≤ 1 := by
    have h : Real.sqrt (1 - t) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    simpa using h
  have keyA : ∀ (y g1 sv s1v : ℝ), 0 ≤ sv → sv ≤ 1 → 0 ≤ s1v → s1v ≤ 1 →
      |sv * y + s1v * g1| ≤ |y| + |g1| := by
    intro y g1 sv s1v hsv0' hsv1' hs1v0' hs1v1'
    calc |sv * y + s1v * g1| ≤ |sv * y| + |s1v * g1| := abs_add_le _ _
      _ = sv * |y| + s1v * |g1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hsv0', abs_of_nonneg hs1v0']
      _ ≤ 1 * |y| + 1 * |g1| := by
          exact add_le_add (mul_le_mul_of_nonneg_right hsv1' (abs_nonneg y))
            (mul_le_mul_of_nonneg_right hs1v1' (abs_nonneg g1))
      _ = |y| + |g1| := by ring
  have keyC : ∀ (y g1 g2 s sv s1v s1t : ℝ), 0 ≤ s → s ≤ 1 → 0 ≤ sv → sv ≤ 1 →
      0 ≤ s1v → s1v ≤ 1 → 0 ≤ s1t → s1t ≤ 1 →
      |s * (sv * y + s1v * g1) + s1t * g2| ≤ |y| + |g1| + |g2| := by
    intro y g1 g2 s sv s1v s1t hs0' hs1' hsv0' hsv1' hs1v0' hs1v1' hs1t0' hs1t1'
    have h1 : |sv * y + s1v * g1| ≤ |y| + |g1| :=
      keyA y g1 sv s1v hsv0' hsv1' hs1v0' hs1v1'
    calc |s * (sv * y + s1v * g1) + s1t * g2| ≤ |s * (sv * y + s1v * g1)| + |s1t * g2| :=
          abs_add_le _ _
      _ = s * |sv * y + s1v * g1| + s1t * |g2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs0', abs_of_nonneg hs1t0']
      _ ≤ 1 * (|y| + |g1|) + 1 * |g2| := by
          exact add_le_add (mul_le_mul hs1' h1 (abs_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_right hs1t1' (abs_nonneg g2))
      _ = |y| + |g1| + |g2| := by ring
  have keyB : ∀ (u1 u2 r1 r2 : ℝ), 0 ≤ u1 → 0 ≤ u2 →
      |u1 * r1 - u2 * r2| ≤ u1 * |r1| + u2 * |r2| := by
    intro u1 u2 r1 r2 hu1' hu2'
    have h1 : |u1 * r1| = u1 * |r1| := by rw [abs_mul, abs_of_nonneg hu1']
    have h2 : |u2 * r2| = u2 * |r2| := by rw [abs_mul, abs_of_nonneg hu2']
    calc |u1 * r1 - u2 * r2| = |u1 * r1 + -(u2 * r2)| := by rw [sub_eq_add_neg]
      _ ≤ |u1 * r1| + |-(u2 * r2)| := abs_add_le _ _
      _ = u1 * |r1| + u2 * |r2| := by rw [abs_neg, h1, h2]
  have hidt : (2 * Real.sqrt t)⁻¹ ≤ (Real.sqrt t)⁻¹ := by
    rw [mul_inv]
    calc 2⁻¹ * (Real.sqrt t)⁻¹ ≤ 1 * (Real.sqrt t)⁻¹ :=
          mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hst0)
      _ = (Real.sqrt t)⁻¹ := by ring
  have hidt1 : (2 * Real.sqrt (1 - t))⁻¹ ≤ (Real.sqrt (1 - t))⁻¹ := by
    rw [mul_inv]
    calc 2⁻¹ * (Real.sqrt (1 - t))⁻¹ ≤ 1 * (Real.sqrt (1 - t))⁻¹ :=
          mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hs1t0)
      _ = (Real.sqrt (1 - t))⁻¹ := by ring
  have hcfac : |((Real.sqrt (m : ℝ))⁻¹ * delta n m)| = c := by
    show |((Real.sqrt (m : ℝ))⁻¹ * delta n m)| = (Real.sqrt (m : ℝ))⁻¹ * |delta n m|
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hZs : ∀ (x : Ω × Ω) (r : Fin p), |Zs x r| ≤ c * Pp r x := by
    intro x r
    have hmain := keyC (Y i x.1 r - muY r) (G i x.1 r - muY r) (G i x.2 r - muY r)
      (Real.sqrt t) (Real.sqrt v) (Real.sqrt (1 - v)) (Real.sqrt (1 - t))
      hst0 hst_le hsv0 hsv_le hs1v0 hs1v_le hs1t0 hs1t_le
    have hstep : |((Real.sqrt (m : ℝ))⁻¹ * delta n m) *
        (Real.sqrt t * (Real.sqrt v * (Y i x.1 r - muY r)
            + Real.sqrt (1 - v) * (G i x.1 r - muY r))
          + Real.sqrt (1 - t) * (G i x.2 r - muY r))|
        ≤ c * (|Y i x.1 r - muY r| + |G i x.1 r - muY r| + |G i x.2 r - muY r|) := by
      rw [abs_mul, hcfac]
      exact mul_le_mul_of_nonneg_left hmain hc
    exact hstep
  have hZd : ∀ (x : Ω × Ω), |Zd x| ≤ c * Wt * Pp j x := by
    intro x
    have hy : |Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j)|
        ≤ |Y i x.1 j - muY j| + |G i x.1 j - muY j| :=
      keyA _ _ _ _ hsv0 hsv_le hs1v0 hs1v_le
    have hA0 : (0 : ℝ) ≤ (2 * Real.sqrt t)⁻¹ := inv_nonneg.mpr (by positivity)
    have hA1 : (0 : ℝ) ≤ (2 * Real.sqrt (1 - t))⁻¹ := inv_nonneg.mpr (by positivity)
    have hin : |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j)
          + Real.sqrt (1 - v) * (G i x.1 j - muY j))
        - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)|
        ≤ (Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
          + (Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j| := by
      refine le_trans (keyB _ _ _ _ hA0 hA1) ?_
      have h2 : (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (Y i x.1 j - muY j)
            + Real.sqrt (1 - v) * (G i x.1 j - muY j)|
          ≤ (Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|) := by
        calc (2 * Real.sqrt t)⁻¹ * |Real.sqrt v * (Y i x.1 j - muY j)
              + Real.sqrt (1 - v) * (G i x.1 j - muY j)|
            ≤ (Real.sqrt t)⁻¹ * |Real.sqrt v * (Y i x.1 j - muY j)
              + Real.sqrt (1 - v) * (G i x.1 j - muY j)| :=
              mul_le_mul_of_nonneg_right hidt (abs_nonneg _)
          _ ≤ (Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|) :=
              mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hst0)
      have h3 : (2 * Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|
          ≤ (Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j| :=
        mul_le_mul_of_nonneg_right hidt1 (abs_nonneg _)
      exact add_le_add h2 h3
    have hW : (Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
        + (Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|
        ≤ Wt * (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|) := by
      rw [hWtval]
      have hu1 : (0 : ℝ) ≤ (Real.sqrt t)⁻¹ := inv_nonneg.mpr hst0
      have hu2 : (0 : ℝ) ≤ (Real.sqrt (1 - t))⁻¹ := inv_nonneg.mpr hs1t0
      have hq0 : (0 : ℝ) ≤ |G i x.2 j - muY j| := abs_nonneg _
      have hp0 : (0 : ℝ) ≤ |Y i x.1 j - muY j| + |G i x.1 j - muY j| := by positivity
      nlinarith [hu1, hu2, hq0, hp0, mul_nonneg hu1 hq0, mul_nonneg hu2 hp0]
    have hstep : |((Real.sqrt (m : ℝ))⁻¹ * delta n m) *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j)
            + Real.sqrt (1 - v) * (G i x.1 j - muY j))
          - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))|
        ≤ c * Wt * (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|) := by
      rw [abs_mul, hcfac]
      have hgoal : c * |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j)
            + Real.sqrt (1 - v) * (G i x.1 j - muY j))
          - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)|
          ≤ c * ((Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
            + (Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|) :=
        mul_le_mul_of_nonneg_left hin hc
      calc c * |(2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j)
            + Real.sqrt (1 - v) * (G i x.1 j - muY j))
          - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)|
          ≤ c * ((Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
            + (Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|) := hgoal
        _ ≤ c * Wt * (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|) := by
            have h1 := mul_le_mul_of_nonneg_left hW hc
            calc c * ((Real.sqrt t)⁻¹ * (|Y i x.1 j - muY j| + |G i x.1 j - muY j|)
                + (Real.sqrt (1 - t))⁻¹ * |G i x.2 j - muY j|)
                ≤ c * (Wt * (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|)) := h1
              _ = c * Wt * (|Y i x.1 j - muY j| + |G i x.1 j - muY j| + |G i x.2 j - muY j|) := by
                  ring
    exact hstep
  let S : Ω × Ω → ℝ := fun x => ∑ r : Fin p, Pp r x ^ 3
  let Kmaj : ℝ := (p : ℝ) * (p : ℝ) * (K * c ^ 3 * Wt * 3)
  have hSval : ∀ x : Ω × Ω, S x = ∑ r : Fin p, Pp r x ^ 3 := fun x => rfl
  have hKmajval : Kmaj = (p : ℝ) * (p : ℝ) * (K * c ^ 3 * Wt * 3) := rfl
  have hPp_nn : ∀ (r : Fin p) (x : Ω × Ω), 0 ≤ Pp r x := by
    intro r x
    show (0 : ℝ) ≤ |Y i x.1 r - muY r| + |G i x.1 r - muY r| + |G i x.2 r - muY r|
    positivity
  have hS_nn : ∀ x : Ω × Ω, 0 ≤ S x := by
    intro x
    rw [hSval]
    exact Finset.sum_nonneg (fun r _ => pow_nonneg (hPp_nn r x) 3)
  have hPp_le_S : ∀ (r : Fin p) (x : Ω × Ω), Pp r x ^ 3 ≤ S x := by
    intro r x
    rw [hSval]
    exact Finset.single_le_sum (f := fun r' : Fin p => Pp r' x ^ 3)
      (fun r' _ => pow_nonneg (hPp_nn r' x) 3) (Finset.mem_univ r)
  have hYoung : ∀ a b cc : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ cc →
      a * b * cc ≤ a ^ 3 + b ^ 3 + cc ^ 3 := by
    intro a b cc ha hb hcc
    have hpos : 0 ≤ a + b + cc := by linarith
    have hsq : 0 ≤ (a - b) ^ 2 + (b - cc) ^ 2 + (cc - a) ^ 2 := by positivity
    have hkey : 2 * (a ^ 3 + b ^ 3 + cc ^ 3) - 6 * (a * b * cc)
        = (a + b + cc) * ((a - b) ^ 2 + (b - cc) ^ 2 + (cc - a) ^ 2) := by ring
    have hprod : 0 ≤ (a + b + cc) * ((a - b) ^ 2 + (b - cc) ^ 2 + (cc - a) ^ 2) :=
      mul_nonneg hpos hsq
    have h2 : 0 ≤ 2 * (a ^ 3 + b ^ 3 + cc ^ 3) - 6 * (a * b * cc) := by
      rw [hkey]
      exact hprod
    have habc : 0 ≤ a * b * cc := mul_nonneg (mul_nonneg ha hb) hcc
    linarith [h2, habc]
  have hterm : ∀ (x : Ω × Ω) (k l : Fin p),
      (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
       else C1 * C2 * phi * beta ^ 2) * |Zs x k| * |Zs x l| * |Zd x|
      ≤ K * c ^ 3 * Wt * (3 * S x) := by
    intro x k l
    have hq0 := hq_nn x k l
    have hqK := hq_le x k l
    have hsk := hZs x k
    have hsl := hZs x l
    have hd := hZd x
    have hPk := hPp_nn k x
    have hPl := hPp_nn l x
    have hPj := hPp_nn j x
    have hnn1 : 0 ≤ K * (c * Pp k x) := mul_nonneg hKnn' (mul_nonneg hc hPk)
    have hnn2 : 0 ≤ (K * (c * Pp k x)) * (c * Pp l x) :=
      mul_nonneg hnn1 (mul_nonneg hc hPl)
    have hnn3 : 0 ≤ K * c ^ 3 * Wt :=
      mul_nonneg (mul_nonneg hKnn' (pow_nonneg hc 3)) hWtnn
    have s1 : (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
        else C1 * C2 * phi * beta ^ 2) * |Zs x k| ≤ K * (c * Pp k x) :=
      mul_le_mul hqK hsk (abs_nonneg _) hKnn'
    have s2 : ((if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
        else C1 * C2 * phi * beta ^ 2) * |Zs x k|) * |Zs x l|
        ≤ (K * (c * Pp k x)) * (c * Pp l x) :=
      mul_le_mul s1 hsl (abs_nonneg _) hnn1
    have s3 : (((if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
        else C1 * C2 * phi * beta ^ 2) * |Zs x k|) * |Zs x l|) * |Zd x|
        ≤ ((K * (c * Pp k x)) * (c * Pp l x)) * (c * Wt * Pp j x) :=
      mul_le_mul s2 hd (abs_nonneg _) hnn2
    have s4 : ((K * (c * Pp k x)) * (c * Pp l x)) * (c * Wt * Pp j x)
        = K * c ^ 3 * Wt * (Pp k x * Pp l x * Pp j x) := by ring
    have s5 : K * c ^ 3 * Wt * (Pp k x * Pp l x * Pp j x) ≤ K * c ^ 3 * Wt * (3 * S x) := by
      have hy := hYoung (Pp k x) (Pp l x) (Pp j x) hPk hPl hPj
      have hsum3 : Pp k x ^ 3 + Pp l x ^ 3 + Pp j x ^ 3 ≤ 3 * S x := by
        have h1 := hPp_le_S k x
        have h2 := hPp_le_S l x
        have h3 := hPp_le_S j x
        linarith
      calc K * c ^ 3 * Wt * (Pp k x * Pp l x * Pp j x)
          ≤ K * c ^ 3 * Wt * (Pp k x ^ 3 + Pp l x ^ 3 + Pp j x ^ 3) :=
            mul_le_mul_of_nonneg_left hy hnn3
        _ ≤ K * c ^ 3 * Wt * (3 * S x) := mul_le_mul_of_nonneg_left hsum3 hnn3
    linarith [s3, s4, s5]
  have hsum_bound : ∀ x : Ω × Ω,
      ∑ k : Fin p, ∑ l : Fin p,
        (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
         else C1 * C2 * phi * beta ^ 2) * |Zs x k| * |Zs x l| * |Zd x|
      ≤ Kmaj * S x := by
    intro x
    have hinner : ∀ k : Fin p, ∑ l : Fin p, (K * c ^ 3 * Wt * (3 * S x))
        = (p : ℝ) * (K * c ^ 3 * Wt * (3 * S x)) := by
      intro k
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ∑ k : Fin p, ∑ l : Fin p,
          (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
           else C1 * C2 * phi * beta ^ 2) * |Zs x k| * |Zs x l| * |Zd x|
        ≤ ∑ k : Fin p, ∑ l : Fin p, (K * c ^ 3 * Wt * (3 * S x)) := by
          apply Finset.sum_le_sum
          intro k _
          apply Finset.sum_le_sum
          intro l _
          exact hterm x k l
      _ = ∑ k : Fin p, (p : ℝ) * (K * c ^ 3 * Wt * (3 * S x)) :=
          Finset.sum_congr rfl (fun k _ => hinner k)
      _ = Kmaj * S x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hKmajval]
          ring
  have hAint : ∀ r : Fin p, Integrable (fun x : Ω × Ω => |Y i x.1 r - muY r| ^ 3) (P.prod P) := by
    intro r
    exact (hY3 i r).comp_fst P
  have hBint : ∀ r : Fin p, Integrable (fun x : Ω × Ω => |G i x.1 r - muY r| ^ 3) (P.prod P) := by
    intro r
    exact (hG3 i r).comp_fst P
  have hCint : ∀ r : Fin p, Integrable (fun x : Ω × Ω => |G i x.2 r - muY r| ^ 3) (P.prod P) := by
    intro r
    exact (hG3 i r).comp_snd P
  have hcube : ∀ a b cc : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ cc →
      (a + b + cc) ^ 3 ≤ 27 * (a ^ 3 + b ^ 3 + cc ^ 3) := by
    intro a b cc ha hb hcc
    have hsq : (a + b + cc) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + cc ^ 2) := by
      have hid : 3 * (a ^ 2 + b ^ 2 + cc ^ 2) - (a + b + cc) ^ 2
          = (a - b) ^ 2 + (b - cc) ^ 2 + (cc - a) ^ 2 := by ring
      have hnn : 0 ≤ (a - b) ^ 2 + (b - cc) ^ 2 + (cc - a) ^ 2 := by positivity
      linarith [hid, hnn]
    have hprod : (a + b + cc) * (a ^ 2 + b ^ 2 + cc ^ 2) ≤ 3 * (a ^ 3 + b ^ 3 + cc ^ 3) := by
      have hid : 3 * (a ^ 3 + b ^ 3 + cc ^ 3) - (a + b + cc) * (a ^ 2 + b ^ 2 + cc ^ 2)
          = (a + b) * (a - b) ^ 2 + (b + cc) * (b - cc) ^ 2 + (cc + a) * (cc - a) ^ 2 := by ring
      have h1 : 0 ≤ (a + b) * (a - b) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have h2 : 0 ≤ (b + cc) * (b - cc) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have h3 : 0 ≤ (cc + a) * (cc - a) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      linarith [hid, h1, h2, h3]
    have hnnS : 0 ≤ a + b + cc := by linarith
    have hnnC : 0 ≤ a ^ 3 + b ^ 3 + cc ^ 3 := by
      have h1 := pow_nonneg ha 3
      have h2 := pow_nonneg hb 3
      have h3 := pow_nonneg hcc 3
      linarith
    calc (a + b + cc) ^ 3 = (a + b + cc) * (a + b + cc) ^ 2 := by ring
      _ ≤ (a + b + cc) * (3 * (a ^ 2 + b ^ 2 + cc ^ 2)) := mul_le_mul_of_nonneg_left hsq hnnS
      _ = 3 * ((a + b + cc) * (a ^ 2 + b ^ 2 + cc ^ 2)) := by ring
      _ ≤ 3 * (3 * (a ^ 3 + b ^ 3 + cc ^ 3)) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ ≤ 27 * (a ^ 3 + b ^ 3 + cc ^ 3) := by linarith [hnnC]
  let T : Ω × Ω → ℝ := fun x => 27 * ∑ r : Fin p,
      (|Y i x.1 r - muY r| ^ 3 + |G i x.1 r - muY r| ^ 3 + |G i x.2 r - muY r| ^ 3)
  have hTval : ∀ x : Ω × Ω, T x = 27 * ∑ r : Fin p,
      (|Y i x.1 r - muY r| ^ 3 + |G i x.1 r - muY r| ^ 3 + |G i x.2 r - muY r| ^ 3) :=
    fun x => rfl
  have hT_int : Integrable T (P.prod P) := by
    have h1 : ∀ r : Fin p, Integrable (fun x : Ω × Ω =>
        |Y i x.1 r - muY r| ^ 3 + |G i x.1 r - muY r| ^ 3 + |G i x.2 r - muY r| ^ 3)
        (P.prod P) :=
      fun r => ((hAint r).add (hBint r)).add (hCint r)
    have h2 : Integrable (fun x : Ω × Ω => ∑ r : Fin p,
        (|Y i x.1 r - muY r| ^ 3 + |G i x.1 r - muY r| ^ 3 + |G i x.2 r - muY r| ^ 3))
        (P.prod P) :=
      integrable_finset_sum Finset.univ (fun r _ => h1 r)
    exact h2.const_mul 27
  have hS_le_T : ∀ x : Ω × Ω, S x ≤ T x := by
    intro x
    rw [hSval, hTval]
    have h1 : ∀ r : Fin p, Pp r x ^ 3 ≤ 27 * (|Y i x.1 r - muY r| ^ 3
        + |G i x.1 r - muY r| ^ 3 + |G i x.2 r - muY r| ^ 3) :=
      fun r => hcube _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    calc ∑ r : Fin p, Pp r x ^ 3
        ≤ ∑ r : Fin p, 27 * (|Y i x.1 r - muY r| ^ 3 + |G i x.1 r - muY r| ^ 3
            + |G i x.2 r - muY r| ^ 3) :=
          Finset.sum_le_sum (fun r _ => h1 r)
      _ = 27 * ∑ r : Fin p, (|Y i x.1 r - muY r| ^ 3 + |G i x.1 r - muY r| ^ 3
            + |G i x.2 r - muY r| ^ 3) := by
          rw [Finset.mul_sum]
  have hKmaj_nn : 0 ≤ Kmaj := by
    rw [hKmajval]
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    exact mul_nonneg (mul_nonneg hp0 hp0)
      (mul_nonneg (mul_nonneg (mul_nonneg hKnn' (pow_nonneg hc 3)) hWtnn) (by norm_num))
  have hmY : ∀ r : Fin p, Measurable (fun x : Ω × Ω => Y i x.1 r) := by
    intro r
    exact ((measurable_pi_iff.mp (hYm i)) r).comp measurable_fst
  have hmG1 : ∀ r : Fin p, Measurable (fun x : Ω × Ω => G i x.1 r) := by
    intro r
    exact ((measurable_pi_iff.mp (hGm i)) r).comp measurable_fst
  have hmG2 : ∀ r : Fin p, Measurable (fun x : Ω × Ω => G i x.2 r) := by
    intro r
    exact ((measurable_pi_iff.mp (hGm i)) r).comp measurable_snd
  have hmZs : ∀ r : Fin p, Measurable (fun x : Ω × Ω => Zs x r) := by
    intro r
    have h1 : Measurable (fun x : Ω × Ω => Y i x.1 r - muY r) := (hmY r).sub measurable_const
    have h2 : Measurable (fun x : Ω × Ω => G i x.1 r - muY r) := (hmG1 r).sub measurable_const
    have h3 : Measurable (fun x : Ω × Ω => G i x.2 r - muY r) := (hmG2 r).sub measurable_const
    have h4 : Measurable (fun x : Ω × Ω => Real.sqrt v * (Y i x.1 r - muY r)
        + Real.sqrt (1 - v) * (G i x.1 r - muY r)) :=
      (measurable_const.mul h1).add (measurable_const.mul h2)
    have h5 : Measurable (fun x : Ω × Ω => Real.sqrt t * (Real.sqrt v * (Y i x.1 r - muY r)
        + Real.sqrt (1 - v) * (G i x.1 r - muY r))
        + Real.sqrt (1 - t) * (G i x.2 r - muY r)) :=
      (measurable_const.mul h4).add (measurable_const.mul h3)
    exact measurable_const.mul h5
  have hmZd : Measurable Zd := by
    have h1 : Measurable (fun x : Ω × Ω => Y i x.1 j - muY j) := (hmY j).sub measurable_const
    have h2 : Measurable (fun x : Ω × Ω => G i x.1 j - muY j) := (hmG1 j).sub measurable_const
    have h3 : Measurable (fun x : Ω × Ω => G i x.2 j - muY j) := (hmG2 j).sub measurable_const
    have h4 : Measurable (fun x : Ω × Ω => Real.sqrt v * (Y i x.1 j - muY j)
        + Real.sqrt (1 - v) * (G i x.1 j - muY j)) :=
      (measurable_const.mul h1).add (measurable_const.mul h2)
    have h5 : Measurable (fun x : Ω × Ω => (2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (Y i x.1 j - muY j)
        + Real.sqrt (1 - v) * (G i x.1 j - muY j))
        - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)) :=
      (measurable_const.mul h4).sub (measurable_const.mul h3)
    exact measurable_const.mul h5
  have hset : ∀ r : Fin p, MeasurableSet {x : Ω × Ω | |Zs x r| * beta ≤ 1} := by
    intro r
    have hmeas : Measurable (fun x : Ω × Ω => |Zs x r| * beta) :=
      (hmZs r).abs.mul measurable_const
    exact measurableSet_le hmeas measurable_const
  have hcond : MeasurableSet {x : Ω × Ω | ∀ r : Fin p, |Zs x r| * beta ≤ 1} := by
    have heq : {x : Ω × Ω | ∀ r : Fin p, |Zs x r| * beta ≤ 1}
        = ⋂ r : Fin p, {x : Ω × Ω | |Zs x r| * beta ≤ 1} := by
      ext x
      simp
    rw [heq]
    exact MeasurableSet.iInter (fun r => hset r)
  have hbr : ∀ (k l : Fin p), Measurable (fun x : Ω × Ω =>
      if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
      else C1 * C2 * phi * beta ^ 2) := by
    intro k l
    exact Measurable.ite hcond (measurable_const.mul (hQmeas l k j)) measurable_const
  have hmterm : ∀ (k l : Fin p), Measurable (fun x : Ω × Ω =>
      (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
       else C1 * C2 * phi * beta ^ 2) * |Zs x k| * |Zs x l| * |Zd x|) := by
    intro k l
    exact (((hbr k l).mul ((hmZs k).abs)).mul ((hmZs l).abs)).mul hmZd.abs
  have hF_meas : AEStronglyMeasurable (fun x : Ω × Ω =>
      ∑ k : Fin p, ∑ l : Fin p,
        (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
         else C1 * C2 * phi * beta ^ 2) * |Zs x k| * |Zs x l| * |Zd x|) (P.prod P) :=
    (Finset.measurable_sum Finset.univ
      (fun k _ => Finset.measurable_sum Finset.univ (fun l _ => hmterm k l))).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(P.prod P),
      ‖∑ k : Fin p, ∑ l : Fin p,
        (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
         else C1 * C2 * phi * beta ^ 2) * |Zs x k| * |Zs x l| * |Zd x|‖ ≤ Kmaj * T x := by
    filter_upwards with x
    have hFnn : 0 ≤ ∑ k : Fin p, ∑ l : Fin p,
        (if (∀ r : Fin p, |Zs x r| * beta ≤ 1) then C3 * Q l k j (W x)
         else C1 * C2 * phi * beta ^ 2) * |Zs x k| * |Zs x l| * |Zd x| := by
      apply Finset.sum_nonneg
      intro k _
      apply Finset.sum_nonneg
      intro l _
      exact mul_nonneg (mul_nonneg (mul_nonneg (hq_nn x k l) (abs_nonneg _)) (abs_nonneg _))
        (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
    exact le_trans (hsum_bound x) (mul_le_mul_of_nonneg_left (hS_le_T x) hKmaj_nn)
  have hmaj_int : Integrable (fun x : Ω × Ω => Kmaj * T x) (P.prod P) := hT_int.const_mul Kmaj
  exact Integrable.mono' hmaj_int hF_meas hbound
  /- @proof-region region.target-node.session.36e9fcaedcc0af30 end -/

end

end Statlib.Imported

