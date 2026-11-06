import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_1826cf4a199ca47d64c5
import ProverJobs.ResidualE2ESupport20261106.M_c8e3736b5e5f81c303a0

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
theorem statopia_math_node_3925995709_85201a55 : ∀ (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (L : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (XT Mask : Ω → Matrix (Fin m) (Fin 1) ℝ)
    (hXT_meas : ∀ (i : Fin m) (j : Fin 1), Measurable fun ω => XT ω i j)
    (hXT_int : ∀ (i : Fin m) (j : Fin 1), Integrable (fun ω => XT ω i j) μ)
    (hXT_sq_int : ∀ (i : Fin m) (j : Fin 1), Integrable (fun ω => (XT ω i j) ^ 2) μ)
    (hXT_indep : iIndepFun (fun (ij : Fin m × Fin 1) (ω : Ω) => XT ω ij.1 ij.2) μ)
    (hXT_mean : ∀ (i : Fin m) (j : Fin 1), ∫ ω, XT ω i j ∂μ = 0)
    (hXT_var : ∀ (i : Fin m) (j : Fin 1), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1)
    (hMask_meas : ∀ (i : Fin m) (j : Fin 1), Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ (i : Fin m) (j : Fin 1) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ (i : Fin m) (j : Fin 1), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin 1) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin 1) => XT ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin 1) => Mask ω ij.1 ij.2) μ)
    (hbound : ∀ (ω : Ω) (i : Fin m) (j : Fin 1), |XT ω i j| ≤ 3 * L),
    Integrable (fun ω => ((∑ i : Fin m, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2) - 1) ^ 2) μ ∧
    (∫ ω, (((∑ i : Fin m, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2) - 1) ^ 2) ∂μ)
      ≤ 9 * L ^ 2 / ((m : ℝ) * p) := by
  /- @proof-region region.target-node.session.7d4775886706d9da begin -/
  intro m hm p hp0 hp1 L Ω instΩ μ instμ XT Mask hXT_meas hXT_int hXT_sq_int hXT_indep hXT_mean
    hXT_var hMask_meas hMask_val hMask_law hMask_indep hIndep hbound
  classical
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hmp : (0 : ℝ) < (m : ℝ) * p := mul_pos hmpos hp0
  have hCnn : (0 : ℝ) ≤ 9 * L ^ 2 / ((m : ℝ) * p) := by positivity
  have hmul : (m : ℝ) * (1 / (m : ℝ)) = 1 := by
    rw [mul_one_div, div_self hmne]
  have hmul' : (1 / (m : ℝ)) * (m : ℝ) = 1 := by
    rw [mul_comm, hmul]
  have hcpos : (0 : ℝ) < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.mpr hmp
  have hcsq : Real.sqrt ((m : ℝ) * p) ^ 2 = (m : ℝ) * p := Real.sq_sqrt (le_of_lt hmp)
  have hconst : ∀ c : ℝ, ∫ _ : Ω, c ∂μ = c := by
    intro c
    rw [integral_const]
    simp
  have hsum_one : (∑ i : Fin m, (1 / (m : ℝ))) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hmul]
  have hsum_sq : (∑ _i : Fin m, (1 / (m : ℝ)) ^ 2) = 1 / (m : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two, ← mul_assoc,
      hmul, one_mul]
  have hdep : ∀ (h h' : Fin m × Fin 1),
      Integrable (fun ω => maskedScaled p (XT ω) (Mask ω) h.1 h.2) μ ∧
      (∫ ω, maskedScaled p (XT ω) (Mask ω) h.1 h.2 ∂μ = 0) ∧
      Integrable (fun ω => maskedScaled p (XT ω) (Mask ω) h.1 h.2 *
        maskedScaled p (XT ω) (Mask ω) h'.1 h'.2) μ ∧
      (∫ ω, maskedScaled p (XT ω) (Mask ω) h.1 h.2 *
        maskedScaled p (XT ω) (Mask ω) h'.1 h'.2 ∂μ = if h = h' then 1 / (m : ℝ) else 0) := by
    intro h h'
    exact statopia_math_node_3553486712_c6cf8bba m 1 hm (le_refl 1) p hp0 hp1 μ XT Mask
      hXT_meas hXT_int hXT_sq_int hXT_indep hXT_mean hXT_var hMask_meas hMask_val hMask_law
      hMask_indep hIndep h h'
  have hAint : ∀ i : Fin m, Integrable (fun ω => maskedScaled p (XT ω) (Mask ω) i 0) μ :=
    fun i => (hdep (i, 0) (i, 0)).1
  have hAmean : ∀ i : Fin m, ∫ ω, maskedScaled p (XT ω) (Mask ω) i 0 ∂μ = 0 :=
    fun i => (hdep (i, 0) (i, 0)).2.1
  have hAsq : ∀ i : Fin m, Integrable (fun ω => (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2) μ := by
    intro i
    have h := (hdep (i, 0) (i, 0)).2.2.1
    simpa [pow_two] using h
  have hAsq2 : ∀ i : Fin m, (∫ ω, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 ∂μ) = 1 / (m : ℝ) := by
    intro i
    have h := (hdep (i, 0) (i, 0)).2.2.2
    simpa [pow_two] using h
  have hpt_sq : ∀ (ω : Ω) (i : Fin m),
      (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 ≤ 9 * L ^ 2 / ((m : ℝ) * p) := by
    intro ω i
    have hmask : |Mask ω i 0| ≤ 1 := by
      rcases hMask_val i 0 ω with h | h <;> rw [h] <;> norm_num
    have hxt : |XT ω i 0| ≤ 3 * L := hbound ω i 0
    have h3L : (0 : ℝ) ≤ 3 * L := le_trans (abs_nonneg _) hxt
    have hle : |maskedScaled p (XT ω) (Mask ω) i 0| ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := by
      have hstep : maskedScaled p (XT ω) (Mask ω) i 0
          = Mask ω i 0 * XT ω i 0 / Real.sqrt ((m : ℝ) * p) := rfl
      rw [hstep, abs_div, abs_of_pos hcpos]
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hcpos)
      calc |Mask ω i 0 * XT ω i 0| = |Mask ω i 0| * |XT ω i 0| := abs_mul _ _
        _ ≤ 1 * (3 * L) := mul_le_mul hmask hxt (abs_nonneg _) zero_le_one
        _ = 3 * L := one_mul _
    calc (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2
        = |maskedScaled p (XT ω) (Mask ω) i 0| ^ 2 := by rw [sq_abs]
      _ ≤ (3 * L / Real.sqrt ((m : ℝ) * p)) ^ 2 := by
          rw [pow_two, pow_two]
          exact mul_self_le_mul_self (abs_nonneg _) hle
      _ = 9 * L ^ 2 / ((m : ℝ) * p) := by
          rw [div_pow, hcsq, mul_pow]
          norm_num
  have hA4int : ∀ i : Fin m,
      Integrable (fun ω => (maskedScaled p (XT ω) (Mask ω) i 0) ^ 4) μ := by
    intro i
    refine Integrable.mono' ((hAsq i).const_mul (9 * L ^ 2 / ((m : ℝ) * p))) ?_ ?_
    · have h4 : (fun ω => (maskedScaled p (XT ω) (Mask ω) i 0) ^ 4)
          = fun ω => (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 *
              (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 := by
        funext ω
        ring
      rw [h4]
      exact (hAsq i).aestronglyMeasurable.mul (hAsq i).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h2 : (0 : ℝ) ≤ (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 := sq_nonneg _
      calc (maskedScaled p (XT ω) (Mask ω) i 0) ^ 4
          = (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2
            * (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 := by ring
        _ ≤ (9 * L ^ 2 / ((m : ℝ) * p)) * (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 :=
            mul_le_mul_of_nonneg_right (hpt_sq ω i) h2
  have hA4bound : ∀ i : Fin m,
      (∫ ω, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 4 ∂μ)
        ≤ (9 * L ^ 2 / ((m : ℝ) * p)) * (1 / (m : ℝ)) := by
    intro i
    have h1 : (∫ ω, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 4 ∂μ)
        ≤ (∫ ω, (9 * L ^ 2 / ((m : ℝ) * p)) *
            (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 ∂μ) := by
      refine integral_mono_ae (hA4int i) ((hAsq i).const_mul _) ?_
      filter_upwards with ω
      have h2 : (0 : ℝ) ≤ (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 := sq_nonneg _
      calc (maskedScaled p (XT ω) (Mask ω) i 0) ^ 4
          = (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2
            * (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 := by ring
        _ ≤ (9 * L ^ 2 / ((m : ℝ) * p)) * (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 :=
            mul_le_mul_of_nonneg_right (hpt_sq ω i) h2
    rw [integral_const_mul, hAsq2 i] at h1
    exact h1
  have hAcrossInt : ∀ i j : Fin m, i ≠ j →
      Integrable (fun ω => (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 *
        (maskedScaled p (XT ω) (Mask ω) j 0) ^ 2) μ := by
    intro i j hij
    refine Integrable.mono' ((hAsq j).const_mul (9 * L ^ 2 / ((m : ℝ) * p))) ?_ ?_
    · exact (hAsq i).aestronglyMeasurable.mul (hAsq j).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hpt_sq ω i) (sq_nonneg _)
  have hAcross : ∀ i j : Fin m, i ≠ j →
      (∫ ω, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2 *
        (maskedScaled p (XT ω) (Mask ω) j 0) ^ 2 ∂μ)
        = (1 / (m : ℝ)) * (1 / (m : ℝ)) := by
    intro i j hij
    exact statopia_math_node_499696627_ce536ec6 m hm p hp0 hp1 μ XT Mask hXT_meas hXT_sq_int
      hXT_indep hXT_var hMask_meas hMask_val hMask_law hMask_indep hIndep i j hij
  have core : ∀ (f : Fin m → Ω → ℝ),
      (∀ i, Integrable (f i) μ) →
      (∀ i, (∫ ω, f i ω ∂μ) = 0) →
      (∀ i, Integrable (fun ω => (f i ω) ^ 2) μ) →
      (∀ i, (∫ ω, (f i ω) ^ 2 ∂μ) = 1 / (m : ℝ)) →
      (∀ i, Integrable (fun ω => (f i ω) ^ 4) μ) →
      (∀ i, (∫ ω, (f i ω) ^ 4 ∂μ) ≤ (9 * L ^ 2 / ((m : ℝ) * p)) * (1 / (m : ℝ))) →
      (∀ i j, i ≠ j → Integrable (fun ω => (f i ω) ^ 2 * (f j ω) ^ 2) μ) →
      (∀ i j, i ≠ j → (∫ ω, (f i ω) ^ 2 * (f j ω) ^ 2 ∂μ) = (1 / (m : ℝ)) * (1 / (m : ℝ))) →
      Integrable (fun ω => ((∑ i, (f i ω) ^ 2) - 1) ^ 2) μ ∧
        ((∫ ω, ((∑ i, (f i ω) ^ 2) - 1) ^ 2 ∂μ) ≤ 9 * L ^ 2 / ((m : ℝ) * p)) := by
    intro f hfint hfmean hfsqint hfsq2 hf4int hf4bound hcrossint hcross
    have hsplit : ∀ ω : Ω, (∑ i, (f i ω) ^ 2) - 1 = ∑ i, ((f i ω) ^ 2 - 1 / (m : ℝ)) := by
      intro ω
      rw [Finset.sum_sub_distrib, hsum_one]
    have hYint : ∀ i j : Fin m,
        Integrable (fun ω => ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f j ω) ^ 2 - 1 / (m : ℝ))) μ := by
      intro i j
      by_cases hij : i = j
      · have hfun : (fun ω => ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f j ω) ^ 2 - 1 / (m : ℝ)))
            = fun ω => (f j ω) ^ 4 - (2 * (1 / (m : ℝ))) * (f j ω) ^ 2 + (1 / (m : ℝ)) ^ 2 := by
          funext ω
          simp only [hij]
          ring
        rw [hfun]
        exact ((hf4int j).sub ((hfsqint j).const_mul (2 * (1 / (m : ℝ))))).add
          (integrable_const _)
      · have hfun : (fun ω => ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f j ω) ^ 2 - 1 / (m : ℝ)))
            = fun ω => (f i ω) ^ 2 * (f j ω) ^ 2 - (1 / (m : ℝ)) * (f i ω) ^ 2
                - (1 / (m : ℝ)) * (f j ω) ^ 2 + (1 / (m : ℝ)) * (1 / (m : ℝ)) := by
          funext ω
          ring
        rw [hfun]
        exact (((hcrossint i j hij).sub ((hfsqint i).const_mul (1 / (m : ℝ)))).sub
          ((hfsqint j).const_mul (1 / (m : ℝ)))).add (integrable_const _)
    have hpt : ∀ ω : Ω, ((∑ i, (f i ω) ^ 2) - 1) ^ 2
        = ∑ i, ∑ j, ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f j ω) ^ 2 - 1 / (m : ℝ)) := by
      intro ω
      rw [hsplit ω, pow_two, Finset.sum_mul_sum]
    have hexp : (∫ ω, ((∑ i, (f i ω) ^ 2) - 1) ^ 2 ∂μ)
        = ∑ i, ∑ j, ∫ ω, ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f j ω) ^ 2 - 1 / (m : ℝ)) ∂μ := by
      simp only [hpt]
      rw [integral_finset_sum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_finset_sum]
        exact fun j _ => hYint i j
      · intro i _
        exact integrable_finset_sum _ (fun j _ => hYint i j)
    have hdiag : ∀ i : Fin m,
        (∫ ω, ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f i ω) ^ 2 - 1 / (m : ℝ)) ∂μ)
          = (∫ ω, (f i ω) ^ 4 ∂μ) - (1 / (m : ℝ)) ^ 2 := by
      intro i
      have hfun : (fun ω => ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f i ω) ^ 2 - 1 / (m : ℝ)))
          = fun ω => (f i ω) ^ 4 - (2 * (1 / (m : ℝ))) * (f i ω) ^ 2 + (1 / (m : ℝ)) ^ 2 := by
        funext ω
        ring
      have e1 : (∫ ω, ((f i ω) ^ 4 - (2 * (1 / (m : ℝ))) * (f i ω) ^ 2 + (1 / (m : ℝ)) ^ 2) ∂μ)
          = (∫ ω, ((f i ω) ^ 4 - (2 * (1 / (m : ℝ))) * (f i ω) ^ 2) ∂μ)
            + (∫ ω, (1 / (m : ℝ)) ^ 2 ∂μ) :=
        integral_add ((hf4int i).sub ((hfsqint i).const_mul (2 * (1 / (m : ℝ)))))
          (integrable_const _)
      have e2 : (∫ ω, ((f i ω) ^ 4 - (2 * (1 / (m : ℝ))) * (f i ω) ^ 2) ∂μ)
          = (∫ ω, (f i ω) ^ 4 ∂μ)
            - (∫ ω, (2 * (1 / (m : ℝ))) * (f i ω) ^ 2 ∂μ) :=
        integral_sub (hf4int i) ((hfsqint i).const_mul (2 * (1 / (m : ℝ))))
      have e3 : (∫ ω, (2 * (1 / (m : ℝ))) * (f i ω) ^ 2 ∂μ)
          = (2 * (1 / (m : ℝ))) * (∫ ω, (f i ω) ^ 2 ∂μ) :=
        integral_const_mul (2 * (1 / (m : ℝ))) (fun ω => (f i ω) ^ 2)
      rw [hfun, e1, e2, e3, hfsq2 i, hconst]
      ring
    have hoff : ∀ i j : Fin m, i ≠ j →
        (∫ ω, ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f j ω) ^ 2 - 1 / (m : ℝ)) ∂μ) = 0 := by
      intro i j hij
      have hfun : (fun ω => ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f j ω) ^ 2 - 1 / (m : ℝ)))
          = fun ω => (f i ω) ^ 2 * (f j ω) ^ 2 - (1 / (m : ℝ)) * (f i ω) ^ 2
              - (1 / (m : ℝ)) * (f j ω) ^ 2 + (1 / (m : ℝ)) * (1 / (m : ℝ)) := by
        funext ω
        ring
      have e1 : (∫ ω, ((f i ω) ^ 2 * (f j ω) ^ 2 - (1 / (m : ℝ)) * (f i ω) ^ 2
            - (1 / (m : ℝ)) * (f j ω) ^ 2 + (1 / (m : ℝ)) * (1 / (m : ℝ))) ∂μ)
          = (∫ ω, ((f i ω) ^ 2 * (f j ω) ^ 2 - (1 / (m : ℝ)) * (f i ω) ^ 2
              - (1 / (m : ℝ)) * (f j ω) ^ 2) ∂μ)
            + (∫ ω, (1 / (m : ℝ)) * (1 / (m : ℝ)) ∂μ) :=
        integral_add (((hcrossint i j hij).sub ((hfsqint i).const_mul (1 / (m : ℝ)))).sub
          ((hfsqint j).const_mul (1 / (m : ℝ)))) (integrable_const _)
      have e2 : (∫ ω, ((f i ω) ^ 2 * (f j ω) ^ 2 - (1 / (m : ℝ)) * (f i ω) ^ 2
              - (1 / (m : ℝ)) * (f j ω) ^ 2) ∂μ)
          = (∫ ω, ((f i ω) ^ 2 * (f j ω) ^ 2 - (1 / (m : ℝ)) * (f i ω) ^ 2) ∂μ)
            - (∫ ω, (1 / (m : ℝ)) * (f j ω) ^ 2 ∂μ) :=
        integral_sub ((hcrossint i j hij).sub ((hfsqint i).const_mul (1 / (m : ℝ))))
          ((hfsqint j).const_mul (1 / (m : ℝ)))
      have e3 : (∫ ω, ((f i ω) ^ 2 * (f j ω) ^ 2 - (1 / (m : ℝ)) * (f i ω) ^ 2) ∂μ)
          = (∫ ω, (f i ω) ^ 2 * (f j ω) ^ 2 ∂μ)
            - (∫ ω, (1 / (m : ℝ)) * (f i ω) ^ 2 ∂μ) :=
        integral_sub (hcrossint i j hij) ((hfsqint i).const_mul (1 / (m : ℝ)))
      have e4 : (∫ ω, (1 / (m : ℝ)) * (f i ω) ^ 2 ∂μ) = (1 / (m : ℝ)) * (1 / (m : ℝ)) := by
        rw [integral_const_mul, hfsq2 i]
      have e5 : (∫ ω, (1 / (m : ℝ)) * (f j ω) ^ 2 ∂μ) = (1 / (m : ℝ)) * (1 / (m : ℝ)) := by
        rw [integral_const_mul, hfsq2 j]
      rw [hfun, e1, e2, e3, e4, e5, hcross i j hij, hconst]
      ring
    have hinner : ∀ i : Fin m,
        (∑ j, ∫ ω, ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f j ω) ^ 2 - 1 / (m : ℝ)) ∂μ)
          = (∫ ω, (f i ω) ^ 4 ∂μ) - (1 / (m : ℝ)) ^ 2 := by
      intro i
      refine (Finset.sum_eq_single i ?_ ?_).trans (hdiag i)
      · intro j _ hji
        exact hoff i j (Ne.symm hji)
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have hdouble : (∑ i, ∑ j, ∫ ω, ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f j ω) ^ 2 - 1 / (m : ℝ)) ∂μ)
        = (∑ i, ∫ ω, (f i ω) ^ 4 ∂μ) - 1 / (m : ℝ) := by
      rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_sub_distrib, hsum_sq]
    have hint : Integrable (fun ω => ((∑ i, (f i ω) ^ 2) - 1) ^ 2) μ := by
      rw [show (fun ω => ((∑ i, (f i ω) ^ 2) - 1) ^ 2)
          = fun ω => ∑ i, ∑ j, ((f i ω) ^ 2 - 1 / (m : ℝ)) * ((f j ω) ^ 2 - 1 / (m : ℝ))
          from funext hpt]
      exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hYint i j))
    have hbound_sum : (∑ i, ∫ ω, (f i ω) ^ 4 ∂μ) ≤ 9 * L ^ 2 / ((m : ℝ) * p) := by
      have h1 : (∑ i, ∫ ω, (f i ω) ^ 4 ∂μ)
          ≤ ∑ _i : Fin m, (9 * L ^ 2 / ((m : ℝ) * p)) * (1 / (m : ℝ)) :=
        Finset.sum_le_sum (fun i _ => hf4bound i)
      have h2 : (∑ _i : Fin m, (9 * L ^ 2 / ((m : ℝ) * p)) * (1 / (m : ℝ)))
          = 9 * L ^ 2 / ((m : ℝ) * p) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hrw : (m : ℝ) * ((9 * L ^ 2 / ((m : ℝ) * p)) * (1 / (m : ℝ)))
            = (9 * L ^ 2 / ((m : ℝ) * p)) * ((m : ℝ) * (1 / (m : ℝ))) := by ring
        rw [hrw, hmul, mul_one]
      rw [h2] at h1
      exact h1
    refine ⟨hint, ?_⟩
    rw [hexp, hdouble]
    linarith [hbound_sum, one_div_pos.mpr hmpos]
  exact core (fun i ω => maskedScaled p (XT ω) (Mask ω) i 0) hAint hAmean hAsq hAsq2 hA4int
    hA4bound hAcrossInt hAcross
  /- @proof-region region.target-node.session.7d4775886706d9da end -/

end Statlib.Imported

