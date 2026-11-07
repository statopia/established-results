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
theorem statopia_math_node_2105095423_f9567069 : ∀ (p : ℕ) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : δ ≠ 0)
    (t : ℝ) (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (v : ℝ) (hv_nonneg : 0 ≤ v) (hv_le_one : v ≤ 1) (μ : Fin p → ℝ)
    (Y G : Ω → Fin p → ℝ)
    (hY_meas : ∀ r : Fin p, Measurable (fun ω : Ω => Y ω r))
    (hG_meas : ∀ r : Fin p, Measurable (fun ω : Ω => G ω r))
    (L L' : ℝ)
    (hL : ∀ r : Fin p,
      Integrable (fun ω : Ω => |Y ω r - μ r| ^ 3) P ∧
      (∫ ω : Ω, |Y ω r - μ r| ^ 3 ∂P) ≤ L ∧
      Integrable (fun ω : Ω => |G ω r - μ r| ^ 3) P ∧
      (∫ ω : Ω, |G ω r - μ r| ^ 3 ∂P) ≤ L'),
    (let A : Ω × Ω → Fin p → ℝ := fun x r => Y x.1 r - μ r
     let Abar : Ω × Ω → Fin p → ℝ := fun x r => G x.1 r - μ r
     let Bb : Ω × Ω → Fin p → ℝ := fun x r => G x.2 r - μ r
     let Pcut : Ω × Ω → Fin p → ℝ := fun x r => |A x r| + |Abar x r| + |Bb x r|
     let U : Ω × Ω → Fin p → ℝ := fun x r =>
       (Real.sqrt (m : ℝ))⁻¹ * δ *
         (Real.sqrt t * (Real.sqrt v * A x r + Real.sqrt (1 - v) * Abar x r)
           + Real.sqrt (1 - t) * Bb x r)
     let V : Ω × Ω → Fin p → ℝ := fun x r =>
       (Real.sqrt (m : ℝ))⁻¹ * δ *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A x r + Real.sqrt (1 - v) * Abar x r)
           - (2 * Real.sqrt (1 - t))⁻¹ * Bb x r)
     ∀ j k l : Fin p,
       Integrable (fun x : Ω × Ω => |U x k * U x l * V x j|) (P.prod P) ∧
       (∫ x : Ω × Ω, |U x k * U x l * V x j| ∂(P.prod P))
         ≤ (1 / 2) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3 * |δ| ^ 3 *
             ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) * (27 * (L + 2 * L'))) := by
  /- @proof-region region.target-node.session.be9b81869b9084f8 begin -/
  intro p Ω _ P _ m hm delta hdelta t ht_pos ht_lt v hv_nonneg hv_le mu Y G hY hG L L' hL
  dsimp only
  intro j k l
  set UU : Ω × Ω → Fin p → ℝ := fun x r =>
    (√(m : ℝ))⁻¹ * delta *
      (√t * (√v * (Y x.1 r - mu r) + √(1 - v) * (G x.1 r - mu r))
        + √(1 - t) * (G x.2 r - mu r)) with hUU
  set VV : Ω × Ω → Fin p → ℝ := fun x r =>
    (√(m : ℝ))⁻¹ * delta *
      ((2 * √t)⁻¹ * (√v * (Y x.1 r - mu r) + √(1 - v) * (G x.1 r - mu r))
        - (2 * √(1 - t))⁻¹ * (G x.2 r - mu r)) with hVV
  obtain ⟨hYk_i, hYk_b, hGk_i, hGk_b⟩ := hL k
  obtain ⟨hYl_i, hYl_b, hGl_i, hGl_b⟩ := hL l
  obtain ⟨hYj_i, hYj_b, hGj_i, hGj_b⟩ := hL j
  have hst0 : (0 : ℝ) ≤ √t := Real.sqrt_nonneg t
  have hstp : (0 : ℝ) < √t := Real.sqrt_pos.mpr ht_pos
  have hst1 : √t ≤ 1 := Real.sqrt_le_one.mpr ht_lt.le
  have hs1t0 : (0 : ℝ) ≤ √(1 - t) := Real.sqrt_nonneg (1 - t)
  have hs1tp : (0 : ℝ) < √(1 - t) := Real.sqrt_pos.mpr (by linarith)
  have hs1t1 : √(1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hsv0 : (0 : ℝ) ≤ √v := Real.sqrt_nonneg v
  have hsv1 : √v ≤ 1 := Real.sqrt_le_one.mpr hv_le
  have hs1v0 : (0 : ℝ) ≤ √(1 - v) := Real.sqrt_nonneg (1 - v)
  have hs1v1 : √(1 - v) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hc0 : (0 : ℝ) ≤ (√(m : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg (m : ℝ))
  have hW0 : (0 : ℝ) ≤ (√t)⁻¹ + (√(1 - t))⁻¹ := by
    have h1 : (0 : ℝ) < (√t)⁻¹ := inv_pos.mpr hstp
    have h2 : (0 : ℝ) < (√(1 - t))⁻¹ := inv_pos.mpr hs1tp
    linarith
  have keyU : ∀ a b c : ℝ,
      |(√(m : ℝ))⁻¹ * delta * (√t * (√v * a + √(1 - v) * b) + √(1 - t) * c)|
        ≤ (√(m : ℝ))⁻¹ * |delta| * (|a| + |b| + |c|) := by
    intro a b c
    have hin : |√v * a + √(1 - v) * b| ≤ |a| + |b| := by
      have h := abs_add_le (√v * a) (√(1 - v) * b)
      rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hs1v0] at h
      have h1 : √v * |a| ≤ |a| := by
        simpa using mul_le_mul_of_nonneg_right hsv1 (abs_nonneg a)
      have h2 : √(1 - v) * |b| ≤ |b| := by
        simpa using mul_le_mul_of_nonneg_right hs1v1 (abs_nonneg b)
      linarith
    have hin2 : |√t * (√v * a + √(1 - v) * b) + √(1 - t) * c| ≤ |a| + |b| + |c| := by
      have h := abs_add_le (√t * (√v * a + √(1 - v) * b)) (√(1 - t) * c)
      rw [abs_mul, abs_mul, abs_of_nonneg hst0, abs_of_nonneg hs1t0] at h
      have h1 : √t * |√v * a + √(1 - v) * b| ≤ |a| + |b| := by
        calc √t * |√v * a + √(1 - v) * b| ≤ 1 * (|a| + |b|) :=
              mul_le_mul hst1 hin (abs_nonneg _) (by norm_num)
          _ = |a| + |b| := one_mul _
      have h2 : √(1 - t) * |c| ≤ |c| := by
        simpa using mul_le_mul_of_nonneg_right hs1t1 (abs_nonneg c)
      linarith
    calc |(√(m : ℝ))⁻¹ * delta * (√t * (√v * a + √(1 - v) * b) + √(1 - t) * c)|
        = (√(m : ℝ))⁻¹ * |delta| * |√t * (√v * a + √(1 - v) * b) + √(1 - t) * c| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc0]
      _ ≤ (√(m : ℝ))⁻¹ * |delta| * (|a| + |b| + |c|) := by
          apply mul_le_mul_of_nonneg_left hin2
          positivity
  have keyV : ∀ a b c : ℝ,
      |(√(m : ℝ))⁻¹ * delta *
          ((2 * √t)⁻¹ * (√v * a + √(1 - v) * b) - (2 * √(1 - t))⁻¹ * c)|
        ≤ (√(m : ℝ))⁻¹ * |delta| *
            ((1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) * (|a| + |b| + |c|)) := by
    intro a b c
    have hinv0 : (0 : ℝ) ≤ (2 * √t)⁻¹ := by positivity
    have hinv1 : (0 : ℝ) ≤ (2 * √(1 - t))⁻¹ := by positivity
    have hX : |√v * a + √(1 - v) * b| ≤ |a| + |b| := by
      have h := abs_add_le (√v * a) (√(1 - v) * b)
      rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hs1v0] at h
      have h1 : √v * |a| ≤ |a| := by
        simpa using mul_le_mul_of_nonneg_right hsv1 (abs_nonneg a)
      have h2 : √(1 - v) * |b| ≤ |b| := by
        simpa using mul_le_mul_of_nonneg_right hs1v1 (abs_nonneg b)
      linarith
    have hstep : |(2 * √t)⁻¹ * (√v * a + √(1 - v) * b) - (2 * √(1 - t))⁻¹ * c|
        ≤ (2 * √t)⁻¹ * (|a| + |b|) + (2 * √(1 - t))⁻¹ * |c| := by
      have h := abs_add_le ((2 * √t)⁻¹ * (√v * a + √(1 - v) * b))
        (-((2 * √(1 - t))⁻¹ * c))
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hinv0, abs_of_nonneg hinv1] at h
      have h1 : (2 * √t)⁻¹ * |√v * a + √(1 - v) * b| ≤ (2 * √t)⁻¹ * (|a| + |b|) :=
        mul_le_mul_of_nonneg_left hX hinv0
      rw [sub_eq_add_neg]
      linarith
    have hstep2 : (2 * √t)⁻¹ * (|a| + |b|) + (2 * √(1 - t))⁻¹ * |c|
        ≤ (1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) * (|a| + |b| + |c|) := by
      have e0 : (2 * √t)⁻¹ = (1 / 2) * (√t)⁻¹ := by
        rw [mul_inv]
        norm_num
      have e1 : (2 * √(1 - t))⁻¹ = (1 / 2) * (√(1 - t))⁻¹ := by
        rw [mul_inv]
        norm_num
      rw [e0, e1]
      have h1 : (0 : ℝ) ≤ (√t)⁻¹ := inv_nonneg.mpr hst0
      have h2 : (0 : ℝ) ≤ (√(1 - t))⁻¹ := inv_nonneg.mpr hs1t0
      have h3 : (0 : ℝ) ≤ |a| + |b| := by positivity
      have h4 : (0 : ℝ) ≤ |c| := abs_nonneg c
      have h5 : (0 : ℝ) ≤ (√t)⁻¹ * |c| := mul_nonneg h1 h4
      have h6 : (0 : ℝ) ≤ (√(1 - t))⁻¹ * (|a| + |b|) := mul_nonneg h2 h3
      nlinarith [h5, h6]
    have hK : (0 : ℝ) ≤ (√(m : ℝ))⁻¹ * |delta| := mul_nonneg hc0 (abs_nonneg delta)
    calc |(√(m : ℝ))⁻¹ * delta *
            ((2 * √t)⁻¹ * (√v * a + √(1 - v) * b) - (2 * √(1 - t))⁻¹ * c)|
        = (√(m : ℝ))⁻¹ * |delta| *
            |(2 * √t)⁻¹ * (√v * a + √(1 - v) * b) - (2 * √(1 - t))⁻¹ * c| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc0]
      _ ≤ (√(m : ℝ))⁻¹ * |delta| *
            ((1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) * (|a| + |b| + |c|)) :=
          mul_le_mul_of_nonneg_left (le_trans hstep hstep2) hK
  let Qk : Ω × Ω → ℝ := fun x => |Y x.1 k - mu k| + |G x.1 k - mu k| + |G x.2 k - mu k|
  let Ql : Ω × Ω → ℝ := fun x => |Y x.1 l - mu l| + |G x.1 l - mu l| + |G x.2 l - mu l|
  let Qj : Ω × Ω → ℝ := fun x => |Y x.1 j - mu j| + |G x.1 j - mu j| + |G x.2 j - mu j|
  have hQk0 : ∀ x : Ω × Ω, (0 : ℝ) ≤ Qk x := by
    intro x
    show (0 : ℝ) ≤ |Y x.1 k - mu k| + |G x.1 k - mu k| + |G x.2 k - mu k|
    positivity
  have hQl0 : ∀ x : Ω × Ω, (0 : ℝ) ≤ Ql x := by
    intro x
    show (0 : ℝ) ≤ |Y x.1 l - mu l| + |G x.1 l - mu l| + |G x.2 l - mu l|
    positivity
  have hQj0 : ∀ x : Ω × Ω, (0 : ℝ) ≤ Qj x := by
    intro x
    show (0 : ℝ) ≤ |Y x.1 j - mu j| + |G x.1 j - mu j| + |G x.2 j - mu j|
    positivity
  have hUbd : ∀ (x : Ω × Ω) (r : Fin p), |UU x r| ≤ (√(m : ℝ))⁻¹ * |delta| *
      (|Y x.1 r - mu r| + |G x.1 r - mu r| + |G x.2 r - mu r|) := by
    intro x r
    rw [hUU]
    exact keyU _ _ _
  have hVbd : ∀ (x : Ω × Ω) (r : Fin p), |VV x r| ≤ (√(m : ℝ))⁻¹ * |delta| *
      ((1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) *
        (|Y x.1 r - mu r| + |G x.1 r - mu r| + |G x.2 r - mu r|)) := by
    intro x r
    rw [hVV]
    exact keyV _ _ _
  have hprod : ∀ x : Ω × Ω,
      |UU x k * UU x l * VV x j| ≤ (1 / 2) * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 *
        ((√t)⁻¹ + (√(1 - t))⁻¹) * (Qk x * Ql x * Qj x) := by
    intro x
    have hK : (0 : ℝ) ≤ (√(m : ℝ))⁻¹ * |delta| := mul_nonneg hc0 (abs_nonneg delta)
    have hk := hUbd x k
    have hl := hUbd x l
    have hj := hVbd x j
    have hmul1 : |UU x k| * |UU x l| ≤
        ((√(m : ℝ))⁻¹ * |delta| * Qk x) * ((√(m : ℝ))⁻¹ * |delta| * Ql x) := by
      refine mul_le_mul hk hl (abs_nonneg _) ?_
      exact mul_nonneg hK (hQk0 x)
    have hmul2 : |UU x k| * |UU x l| * |VV x j| ≤
        (((√(m : ℝ))⁻¹ * |delta| * Qk x) * ((√(m : ℝ))⁻¹ * |delta| * Ql x)) *
          ((√(m : ℝ))⁻¹ * |delta| * ((1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) * Qj x)) := by
      refine mul_le_mul hmul1 hj (abs_nonneg _) ?_
      exact mul_nonneg (mul_nonneg hK (hQk0 x)) (mul_nonneg hK (hQl0 x))
    rw [abs_mul, abs_mul]
    refine le_trans hmul2 (le_of_eq ?_)
    show (((√(m : ℝ))⁻¹ * |delta| * Qk x) * ((√(m : ℝ))⁻¹ * |delta| * Ql x)) *
        ((√(m : ℝ))⁻¹ * |delta| * ((1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) * Qj x)) =
      (1 / 2) * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 *
        ((√t)⁻¹ + (√(1 - t))⁻¹) * (Qk x * Ql x * Qj x)
    rw [← inv_pow]
    ring
  have honeP : (∫ _ : Ω, (1 : ℝ) ∂P) = 1 := by simp
  have hIk1 : (∫ x : Ω × Ω, |Y x.1 k - mu k| ^ 3 ∂(P.prod P))
      = ∫ ω : Ω, |Y ω k - mu k| ^ 3 ∂P := by
    have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
      (f := fun ω : Ω => |Y ω k - mu k| ^ 3) (g := fun _ : Ω => (1 : ℝ))
    simp only [honeP, mul_one] at h
    simpa using h
  have hIk2 : (∫ x : Ω × Ω, |G x.1 k - mu k| ^ 3 ∂(P.prod P))
      = ∫ ω : Ω, |G ω k - mu k| ^ 3 ∂P := by
    have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
      (f := fun ω : Ω => |G ω k - mu k| ^ 3) (g := fun _ : Ω => (1 : ℝ))
    simp only [honeP, mul_one] at h
    simpa using h
  have hIk3 : (∫ x : Ω × Ω, |G x.2 k - mu k| ^ 3 ∂(P.prod P))
      = ∫ ω : Ω, |G ω k - mu k| ^ 3 ∂P := by
    have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
      (f := fun _ : Ω => (1 : ℝ)) (g := fun ω : Ω => |G ω k - mu k| ^ 3)
    simp only [honeP, one_mul] at h
    simpa using h
  have hIY : Integrable (fun x : Ω × Ω => |Y x.1 k - mu k| ^ 3) (P.prod P) :=
    hYk_i.comp_fst P
  have hIG1 : Integrable (fun x : Ω × Ω => |G x.1 k - mu k| ^ 3) (P.prod P) :=
    hGk_i.comp_fst P
  have hIG2 : Integrable (fun x : Ω × Ω => |G x.2 k - mu k| ^ 3) (P.prod P) :=
    hGk_i.comp_snd P
  have hcube3 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      (a + b + c) ^ 3 ≤ 27 * (a ^ 3 + b ^ 3 + c ^ 3) := by
    intro a b c ha hb hc
    have hsq : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      have hexp : (a + b + c) ^ 2 =
          (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a * b + b * c + c * a) := by ring
      rw [hexp]
      have h1 : (0 : ℝ) ≤ (a - b) ^ 2 := sq_nonneg _
      have h2 : (0 : ℝ) ≤ (b - c) ^ 2 := sq_nonneg _
      have h3 : (0 : ℝ) ≤ (c - a) ^ 2 := sq_nonneg _
      have hid : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 =
          2 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a * b + b * c + c * a) := by ring
      linarith
    have h1 : a ^ 2 * b + a * b ^ 2 ≤ a ^ 3 + b ^ 3 := by
      have hh : (0 : ℝ) ≤ (a - b) ^ 2 * (a + b) :=
        mul_nonneg (sq_nonneg (a - b)) (by linarith)
      have he : a ^ 3 + b ^ 3 - (a ^ 2 * b + a * b ^ 2) = (a - b) ^ 2 * (a + b) := by
        ring
      linarith
    have h2 : a ^ 2 * c + a * c ^ 2 ≤ a ^ 3 + c ^ 3 := by
      have hh : (0 : ℝ) ≤ (a - c) ^ 2 * (a + c) :=
        mul_nonneg (sq_nonneg (a - c)) (by linarith)
      have he : a ^ 3 + c ^ 3 - (a ^ 2 * c + a * c ^ 2) = (a - c) ^ 2 * (a + c) := by
        ring
      linarith
    have h3 : b ^ 2 * c + b * c ^ 2 ≤ b ^ 3 + c ^ 3 := by
      have hh : (0 : ℝ) ≤ (b - c) ^ 2 * (b + c) :=
        mul_nonneg (sq_nonneg (b - c)) (by linarith)
      have he : b ^ 3 + c ^ 3 - (b ^ 2 * c + b * c ^ 2) = (b - c) ^ 2 * (b + c) := by
        ring
      linarith
    have hprod : (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 3 * (a ^ 3 + b ^ 3 + c ^ 3) := by
      have hexp : (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) = (a ^ 3 + b ^ 3 + c ^ 3) +
          ((a ^ 2 * b + a * b ^ 2) + (a ^ 2 * c + a * c ^ 2) + (b ^ 2 * c + b * c ^ 2)) := by
        ring
      rw [hexp]
      linarith
    have hsum : (0 : ℝ) ≤ a + b + c := by linarith
    have hstep : (a + b + c) ^ 3 ≤ (a + b + c) * (3 * (a ^ 2 + b ^ 2 + c ^ 2)) := by
      have h : (a + b + c) ^ 3 = (a + b + c) * (a + b + c) ^ 2 := by ring
      rw [h]
      exact mul_le_mul_of_nonneg_left hsq hsum
    refine le_trans hstep ?_
    have hmult : (a + b + c) * (3 * (a ^ 2 + b ^ 2 + c ^ 2)) =
        3 * ((a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2)) := by ring
    rw [hmult]
    have hna : (0 : ℝ) ≤ a ^ 3 := pow_nonneg ha 3
    have hnb : (0 : ℝ) ≤ b ^ 3 := pow_nonneg hb 3
    have hnc : (0 : ℝ) ≤ c ^ 3 := pow_nonneg hc 3
    linarith
  have hQkcube : ∀ x : Ω × Ω, Qk x ^ 3 ≤ 27 * (|Y x.1 k - mu k| ^ 3 +
      |G x.1 k - mu k| ^ 3 + |G x.2 k - mu k| ^ 3) := by
    intro x
    exact hcube3 _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
  show Integrable (fun x : Ω × Ω => |UU x k * UU x l * VV x j|) (P.prod P) ∧
      (∫ x : Ω × Ω, |UU x k * UU x l * VV x j| ∂(P.prod P)) ≤
        (1 / 2 : ℝ) * ((√(m : ℝ))⁻¹) ^ 3 * |delta| ^ 3 *
          ((√t)⁻¹ + (√(1 - t))⁻¹) * (27 * (L + 2 * L'))
  have amgm3 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      3 * (a * b * c) ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
    intro a b c ha hb hc
    have h1 : (0 : ℝ) ≤ (a - b) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (b - c) ^ 2 := sq_nonneg _
    have h3 : (0 : ℝ) ≤ (c - a) ^ 2 := sq_nonneg _
    have hsum : (0 : ℝ) ≤ a + b + c := by linarith
    have hnn : (0 : ℝ) ≤ (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) :=
      mul_nonneg hsum (by linarith)
    have hid : (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) =
        2 * (a ^ 3 + b ^ 3 + c ^ 3) - 6 * (a * b * c) := by ring
    linarith
  have hQcube : ∀ (r : Fin p) (X : Ω × Ω → ℝ),
      (∀ x : Ω × Ω, X x = |Y x.1 r - mu r| + |G x.1 r - mu r| + |G x.2 r - mu r|) →
      Integrable (fun x : Ω × Ω => X x ^ 3) (P.prod P) ∧
        (∫ x : Ω × Ω, X x ^ 3 ∂(P.prod P)) ≤ 27 * (L + 2 * L') := by
    intro r X hXeq
    obtain ⟨iY, bY, iG, bG⟩ := hL r
    have hi1 : Integrable (fun x : Ω × Ω => |Y x.1 r - mu r| ^ 3) (P.prod P) := iY.comp_fst P
    have hi2 : Integrable (fun x : Ω × Ω => |G x.1 r - mu r| ^ 3) (P.prod P) := iG.comp_fst P
    have hi3 : Integrable (fun x : Ω × Ω => |G x.2 r - mu r| ^ 3) (P.prod P) := iG.comp_snd P
    have hSI : Integrable (fun x : Ω × Ω =>
        |Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3 + |G x.2 r - mu r| ^ 3) (P.prod P) :=
      (hi1.add hi2).add hi3
    have m1 : (∫ x : Ω × Ω, |Y x.1 r - mu r| ^ 3 ∂(P.prod P))
        = ∫ ω : Ω, |Y ω r - mu r| ^ 3 ∂P := by
      have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
        (f := fun ω : Ω => |Y ω r - mu r| ^ 3) (g := fun _ : Ω => (1 : ℝ))
      simp only [honeP, mul_one] at h
      simpa using h
    have m2 : (∫ x : Ω × Ω, |G x.1 r - mu r| ^ 3 ∂(P.prod P))
        = ∫ ω : Ω, |G ω r - mu r| ^ 3 ∂P := by
      have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
        (f := fun ω : Ω => |G ω r - mu r| ^ 3) (g := fun _ : Ω => (1 : ℝ))
      simp only [honeP, mul_one] at h
      simpa using h
    have m3 : (∫ x : Ω × Ω, |G x.2 r - mu r| ^ 3 ∂(P.prod P))
        = ∫ ω : Ω, |G ω r - mu r| ^ 3 ∂P := by
      have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
        (f := fun _ : Ω => (1 : ℝ)) (g := fun ω : Ω => |G ω r - mu r| ^ 3)
      simp only [honeP, one_mul] at h
      simpa using h
    have e2s : (∫ x : Ω × Ω,
        (|Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3 + |G x.2 r - mu r| ^ 3) ∂(P.prod P)) =
        (∫ x : Ω × Ω, (|Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3) ∂(P.prod P)) +
          (∫ x : Ω × Ω, |G x.2 r - mu r| ^ 3 ∂(P.prod P)) :=
      MeasureTheory.integral_add (hi1.add hi2) hi3
    have e1s : (∫ x : Ω × Ω, (|Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3) ∂(P.prod P)) =
        (∫ x : Ω × Ω, |Y x.1 r - mu r| ^ 3 ∂(P.prod P)) +
          (∫ x : Ω × Ω, |G x.1 r - mu r| ^ 3 ∂(P.prod P)) :=
      MeasureTheory.integral_add hi1 hi2
    have hSle : (∫ x : Ω × Ω,
        (|Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3 + |G x.2 r - mu r| ^ 3) ∂(P.prod P))
        ≤ L + 2 * L' := by
      rw [e2s, e1s, m1, m2, m3]
      linarith
    have hX0 : ∀ x : Ω × Ω, (0 : ℝ) ≤ X x := by
      intro x
      rw [hXeq x]
      positivity
    have hpt : ∀ x : Ω × Ω, X x ^ 3 ≤ 27 *
        (|Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3 + |G x.2 r - mu r| ^ 3) := by
      intro x
      rw [hXeq x]
      exact hcube3 _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    have hXm : Measurable (fun x : Ω × Ω => X x ^ 3) := by
      have heq : (fun x : Ω × Ω => X x ^ 3) = fun x : Ω × Ω =>
          (|Y x.1 r - mu r| + |G x.1 r - mu r| + |G x.2 r - mu r|) ^ 3 := by
        funext x
        rw [hXeq x]
      rw [heq]
      fun_prop
    have hXint : Integrable (fun x : Ω × Ω => X x ^ 3) (P.prod P) := by
      refine (hSI.const_mul 27).mono' hXm.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hX0 x) 3)]
      exact hpt x
    refine ⟨hXint, ?_⟩
    have hcomp := MeasureTheory.integral_mono hXint (hSI.const_mul 27) hpt
    rw [MeasureTheory.integral_const_mul] at hcomp
    exact le_trans hcomp (by linarith [hSle])
  have hQk3 : Integrable (fun x : Ω × Ω => Qk x ^ 3) (P.prod P) ∧
      (∫ x : Ω × Ω, Qk x ^ 3 ∂(P.prod P)) ≤ 27 * (L + 2 * L') :=
    hQcube k Qk (fun x => rfl)
  have hQl3 : Integrable (fun x : Ω × Ω => Ql x ^ 3) (P.prod P) ∧
      (∫ x : Ω × Ω, Ql x ^ 3 ∂(P.prod P)) ≤ 27 * (L + 2 * L') :=
    hQcube l Ql (fun x => rfl)
  have hQj3 : Integrable (fun x : Ω × Ω => Qj x ^ 3) (P.prod P) ∧
      (∫ x : Ω × Ω, Qj x ^ 3 ∂(P.prod P)) ≤ 27 * (L + 2 * L') :=
    hQcube j Qj (fun x => rfl)
  have hSI3 : Integrable (fun x : Ω × Ω => Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) (P.prod P) :=
    (hQk3.1.add hQl3.1).add hQj3.1
  have hDint : Integrable (fun x : Ω × Ω =>
      (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3)) (P.prod P) :=
    hSI3.const_mul _
  have hK0 : (0 : ℝ) ≤
      1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) := by
    have h1 : (0 : ℝ) ≤ ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ :=
      inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg (m : ℝ)) 3)
    have h2 : (0 : ℝ) ≤ |delta| ^ 3 := pow_nonneg (abs_nonneg delta) 3
    have h3 : (0 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
    exact mul_nonneg (mul_nonneg (mul_nonneg h3 h1) h2) hW0
  have hK3 : (0 : ℝ) ≤
      1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3 :=
    div_nonneg hK0 (by norm_num)
  have hfinpt : ∀ x : Ω × Ω, |UU x k * UU x l * VV x j| ≤
      (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) := by
    intro x
    have h1 := hprod x
    have h2 : 3 * (Qk x * Ql x * Qj x) ≤ Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3 :=
      amgm3 _ _ _ (hQk0 x) (hQl0 x) (hQj0 x)
    have h3 : Qk x * Ql x * Qj x ≤ (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) / 3 := by linarith
    have h4 : (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹)) *
        (Qk x * Ql x * Qj x) ≤
        (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹)) *
          ((Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) / 3) :=
      mul_le_mul_of_nonneg_left h3 hK0
    have h5 : (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹)) *
          ((Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) / 3) =
        (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
          (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) := by ring
    linarith
  have hfinint : Integrable (fun x : Ω × Ω => |UU x k * UU x l * VV x j|) (P.prod P) := by
    have hm : Measurable (fun x : Ω × Ω => |UU x k * UU x l * VV x j|) := by
      simp only [hUU, hVV]
      fun_prop
    refine hDint.mono' hm.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hfinpt x
  refine ⟨hfinint, ?_⟩
  have hmono := MeasureTheory.integral_mono hfinint hDint hfinpt
  have hDval : (∫ x : Ω × Ω,
      (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) ∂(P.prod P)) =
      (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        ((∫ x : Ω × Ω, Qk x ^ 3 ∂(P.prod P)) + (∫ x : Ω × Ω, Ql x ^ 3 ∂(P.prod P)) +
          (∫ x : Ω × Ω, Qj x ^ 3 ∂(P.prod P))) := by
    rw [MeasureTheory.integral_const_mul]
    have e2d : (∫ x : Ω × Ω, (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) ∂(P.prod P)) =
        (∫ x : Ω × Ω, (Qk x ^ 3 + Ql x ^ 3) ∂(P.prod P)) +
          (∫ x : Ω × Ω, Qj x ^ 3 ∂(P.prod P)) :=
      MeasureTheory.integral_add (hQk3.1.add hQl3.1) hQj3.1
    have e1d : (∫ x : Ω × Ω, (Qk x ^ 3 + Ql x ^ 3) ∂(P.prod P)) =
        (∫ x : Ω × Ω, Qk x ^ 3 ∂(P.prod P)) + (∫ x : Ω × Ω, Ql x ^ 3 ∂(P.prod P)) :=
      MeasureTheory.integral_add hQk3.1 hQl3.1
    rw [e2d, e1d]
  rw [hDval] at hmono
  refine le_trans hmono ?_
  have hbound : (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
      ((∫ x : Ω × Ω, Qk x ^ 3 ∂(P.prod P)) + (∫ x : Ω × Ω, Ql x ^ 3 ∂(P.prod P)) +
        (∫ x : Ω × Ω, Qj x ^ 3 ∂(P.prod P))) ≤
      (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        (3 * (27 * (L + 2 * L'))) := by
    refine mul_le_mul_of_nonneg_left ?_ hK3
    linarith [hQk3.2, hQl3.2, hQj3.2]
  refine le_trans hbound ?_
  have hcalc : (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        (3 * (27 * (L + 2 * L'))) =
      (1 / 2 * ((√(m : ℝ))⁻¹) ^ 3 * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹)) *
        (27 * (L + 2 * L')) := by
    rw [← inv_pow]
    ring
  exact le_of_eq hcalc
  /- @proof-region region.target-node.session.be9b81869b9084f8 end -/

end

end Statlib.Imported

