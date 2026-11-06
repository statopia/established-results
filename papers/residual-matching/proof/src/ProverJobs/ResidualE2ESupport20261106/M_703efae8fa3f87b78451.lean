import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_b3c65bd3087beae5f458

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2154310619_f2ebfa07 : ∀ (m n : ℕ) (ν : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν]
    (i : Fin m) (j : Fin n) (L Kt b c : ℝ)
    (hKt : 0 < Kt) (hL : 0 < L)
    (hmean : ∫ x, x i j ∂ν = 0)
    (hvar : ∫ x, (x i j) ^ 2 ∂ν = 1)
    (htail : ∀ t : ℝ, 0 < t →
      ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|} ≤
        ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (hb : b = ∫ x, x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) ∂ν)
    (hc : c = Real.sqrt (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b) ^ 2 ∂ν)),
    |b| ≤ 2 * (L + Kt) * Real.exp (-L / Kt) ∧
      1 - c ^ 2 ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) +
        4 * (L + Kt) ^ 2 * (Real.exp (-L / Kt)) ^ 2 := by
  /- @proof-region region.target-node.session.60c0b19542d12380 begin -/
  intro m n ν _ i j L Kt b c hKt hL hmean hvar htail hb hc
  have hmeas : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hmom := statopia_math_node_943015288_0eb97663 m n ν i j L Kt hKt hL hmeas htail
  have hInt2 : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2) ν := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hvar
    norm_num at hvar
  have hdom : ∀ x : Matrix (Fin m) (Fin n) ℝ, ‖x i j‖ ≤ (x i j) ^ 2 + 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by nlinarith [sq_nonneg (x i j + 1 / 2)], by nlinarith [sq_nonneg (x i j - 1 / 2)]⟩
  have hdomInt : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2 + 1) ν :=
    hInt2.add (integrable_const (1 : ℝ))
  have hset : MeasurableSet {x : Matrix (Fin m) (Fin n) ℝ | |x i j| ≤ L} := by
    measurability
  have hifm : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ => if |x i j| ≤ L then x i j else 0) :=
    Measurable.ite hset hmeas measurable_const
  have hifm2 : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ =>
      if |x i j| ≤ L then (0 : ℝ) else x i j) :=
    Measurable.ite hset measurable_const hmeas
  have hIntX : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => x i j) ν := by
    refine Integrable.mono' hdomInt hmeas.aestronglyMeasurable ?_
    filter_upwards with x
    exact hdom x
  have hIXf : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ =>
      x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) ν := by
    have heq : (fun x : Matrix (Fin m) (Fin n) ℝ =>
        x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
        = fun x => if |x i j| ≤ L then x i j else 0 := by
      funext x
      by_cases hx : (|x i j| ≤ L) <;> simp [hx]
    rw [heq]
    refine Integrable.mono' hdomInt hifm.aestronglyMeasurable ?_
    filter_upwards with x
    have h2 : ‖(if |x i j| ≤ L then x i j else 0)‖ ≤ ‖x i j‖ := by
      by_cases hx : (|x i j| ≤ L) <;> simp [hx]
    calc ‖(if |x i j| ≤ L then x i j else 0)‖ ≤ ‖x i j‖ := h2
      _ ≤ (x i j) ^ 2 + 1 := hdom x
  have hIXψ : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ =>
      x i j * (if |x i j| ≤ L then (0 : ℝ) else 1)) ν := by
    have heq : (fun x : Matrix (Fin m) (Fin n) ℝ =>
        x i j * (if |x i j| ≤ L then (0 : ℝ) else 1))
        = fun x => if |x i j| ≤ L then (0 : ℝ) else x i j := by
      funext x
      by_cases hx : (|x i j| ≤ L) <;> simp [hx]
    rw [heq]
    refine Integrable.mono' hdomInt hifm2.aestronglyMeasurable ?_
    filter_upwards with x
    have h2 : ‖(if |x i j| ≤ L then (0 : ℝ) else x i j)‖ ≤ ‖x i j‖ := by
      by_cases hx : (|x i j| ≤ L) <;> simp [hx]
    calc ‖(if |x i j| ≤ L then (0 : ℝ) else x i j)‖ ≤ ‖x i j‖ := h2
      _ ≤ (x i j) ^ 2 + 1 := hdom x
  have hpt : (fun x : Matrix (Fin m) (Fin n) ℝ => x i j)
      = fun x => x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)
        + x i j * (if |x i j| ≤ L then (0 : ℝ) else 1) := by
    funext x
    by_cases hx : (|x i j| ≤ L) <;> simp [hx]
  have hsplit : (∫ x, x i j ∂ν)
      = (∫ x, x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) ∂ν)
        + (∫ x, x i j * (if |x i j| ≤ L then (0 : ℝ) else 1) ∂ν) := by
    rw [hpt, integral_add hIXf hIXψ]
  have hb' : b = -∫ x, x i j * (if |x i j| ≤ L then (0 : ℝ) else 1) ∂ν := by
    linarith [hb, hmean, hsplit]
  have hab : |b| ≤ 2 * (L + Kt) * Real.exp (-L / Kt) := by
    have h1 : |b| ≤ ∫ x, ‖x i j * (if |x i j| ≤ L then (0 : ℝ) else 1)‖ ∂ν := by
      have h2 : |b| = ‖∫ x, x i j * (if |x i j| ≤ L then (0 : ℝ) else 1) ∂ν‖ := by
        rw [hb']
        simp
      rw [h2]
      exact norm_integral_le_integral_norm _
    have h3 : (fun x : Matrix (Fin m) (Fin n) ℝ =>
        ‖x i j * (if |x i j| ≤ L then (0 : ℝ) else 1)‖)
        = fun x => |x i j| * (if |x i j| ≤ L then (0 : ℝ) else 1) := by
      funext x
      by_cases hx : (|x i j| ≤ L) <;> simp [hx]
    rw [h3] at h1
    exact le_trans h1 hmom.1
  constructor
  · exact hab
  · have hsq : c ^ 2 = ∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b) ^ 2 ∂ν := by
      rw [hc]
      exact Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)
    have hφm : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ =>
        if |x i j| ≤ L then (1 : ℝ) else 0) :=
      Measurable.ite hset measurable_const measurable_const
    have hψm : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ =>
        if |x i j| ≤ L then (0 : ℝ) else 1) :=
      Measurable.ite hset measurable_const measurable_const
    have hGm : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ =>
        x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) := hmeas.mul hφm
    have hG2int : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ =>
        (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
          * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))) ν := by
      refine Integrable.mono' hdomInt (hGm.mul hGm).aestronglyMeasurable ?_
      filter_upwards with x
      have h7 : (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
          * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) ≤ (x i j) ^ 2 := by
        by_cases hx : (|x i j| ≤ L)
        · simp [hx, pow_two]
        · have h0 : (0 : ℝ) ≤ (x i j) ^ 2 := sq_nonneg _
          simpa [hx] using h0
      have h8 : (0 : ℝ) ≤ (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
          * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) := by
        by_cases hx : (|x i j| ≤ L)
        · have h0 : (0 : ℝ) ≤ x i j * x i j := by
            simpa [pow_two] using sq_nonneg (x i j)
          simpa [hx] using h0
        · have h0 : (0 : ℝ) ≤ x i j * x i j := by
            simpa [pow_two] using sq_nonneg (x i j)
          simpa [hx] using h0
      rw [Real.norm_eq_abs, abs_of_nonneg h8]
      linarith
    have h2bG : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ =>
        2 * b * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))) ν := by
      simpa [smul_eq_mul] using hIXf.const_mul (2 * b)
    have hB2 : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ => b ^ 2) ν :=
      integrable_const _
    have hX2I : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ =>
        (x i j) ^ 2 * (if |x i j| ≤ L then (0 : ℝ) else 1)) ν := by
      refine Integrable.mono' hdomInt ?_ ?_
      · have hm := (hmeas.mul hmeas).mul hψm
        simpa [pow_two] using hm.aestronglyMeasurable
      · filter_upwards with x
        have h7 : (x i j) ^ 2 * (if |x i j| ≤ L then (0 : ℝ) else 1) ≤ (x i j) ^ 2 := by
          by_cases hx : (|x i j| ≤ L)
          · have h0 : (0 : ℝ) ≤ (x i j) ^ 2 := sq_nonneg _
            simpa [hx] using h0
          · simp [hx]
        have h8 : (0 : ℝ) ≤ (x i j) ^ 2 * (if |x i j| ≤ L then (0 : ℝ) else 1) := by
          by_cases hx : (|x i j| ≤ L)
          · simp [hx]
          · have h0 : (0 : ℝ) ≤ (x i j) ^ 2 := sq_nonneg _
            simpa [hx] using h0
        rw [Real.norm_eq_abs, abs_of_nonneg h8]
        linarith
    have hpt1 : (fun x : Matrix (Fin m) (Fin n) ℝ =>
        (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b) ^ 2)
        = fun x => (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
            * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
          - (2 * b * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) - b ^ 2) := by
      funext x
      ring
    have hRest : Integrable (fun x : Matrix (Fin m) (Fin n) ℝ =>
        2 * b * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) - b ^ 2) ν :=
      h2bG.sub hB2
    have hexp1 : (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b) ^ 2 ∂ν)
        = (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
            * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) ∂ν) - b ^ 2 := by
      rw [hpt1]
      rw [integral_sub hG2int hRest]
      rw [integral_sub h2bG hB2]
      rw [integral_const_mul]
      rw [← hb]
      have hD : (∫ x, (b ^ 2 : ℝ) ∂ν) = b ^ 2 := by
        rw [integral_const]
        simp
      rw [hD]
      ring
    have hpt2 : (fun x : Matrix (Fin m) (Fin n) ℝ => (x i j) ^ 2)
        = fun x => (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
            * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
          + (x i j) ^ 2 * (if |x i j| ≤ L then (0 : ℝ) else 1) := by
      funext x
      by_cases hx : (|x i j| ≤ L) <;> simp [hx, pow_two]
    have hsum2 : (∫ x, (x i j) ^ 2 ∂ν)
        = (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
            * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) ∂ν)
          + ∫ x, (x i j) ^ 2 * (if |x i j| ≤ L then (0 : ℝ) else 1) ∂ν := by
      rw [hpt2, integral_add hG2int hX2I]
    have hc2 : c ^ 2 = (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0))
        * (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0)) ∂ν) - b ^ 2 := by
      rw [hsq, hexp1]
    have hkey : 1 - c ^ 2
        = (∫ x, (x i j) ^ 2 * (if |x i j| ≤ L then (0 : ℝ) else 1) ∂ν) + b ^ 2 := by
      linarith [hc2, hsum2, hvar]
    have hb2 : b ^ 2 ≤ 4 * (L + Kt) ^ 2 * (Real.exp (-L / Kt)) ^ 2 := by
      obtain ⟨hbl, hbr⟩ := abs_le.1 hab
      have h3 : b ^ 2 ≤ (2 * (L + Kt) * Real.exp (-L / Kt)) ^ 2 := by nlinarith [hbl, hbr]
      calc b ^ 2 ≤ (2 * (L + Kt) * Real.exp (-L / Kt)) ^ 2 := h3
        _ = 4 * (L + Kt) ^ 2 * (Real.exp (-L / Kt)) ^ 2 := by ring
    rw [hkey]
    exact add_le_add hmom.2 hb2
  /- @proof-region region.target-node.session.60c0b19542d12380 end -/

end Statlib.Imported

