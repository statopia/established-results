import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

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
theorem statopia_math_node_2490289310_a8cb3761 : (open MeasureTheory ProbabilityTheory in (open scoped BigOperators ENNReal in (∀ (b : ℝ), 0 < b →
      ∃ C : ℝ, 0 < C ∧
        ∀ (p : ℕ) (hp : 3 ≤ p) (μ_Y : Measure (Fin p → ℝ)) [IsProbabilityMeasure μ_Y],
          ProbabilityTheory.IsGaussian μ_Y →
          (∫ y, y ∂μ_Y = fun _ => (0 : ℝ)) →
          (∀ j : Fin p, b ≤ ∫ y, (y j) ^ 2 ∂μ_Y) →
          ∀ (y : Fin p → ℝ) (a : ℝ), 0 < a →
            (μ_Y {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ y j + a}).toReal -
                (μ_Y {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ y j}).toReal ≤
              C * a * Real.sqrt (Real.log (p : ℝ))))) := by
  /- @proof-region region.target-node.session.f430fc1d375ea3b2 begin -/
  have centeredGaussian_of_IsGaussian (p : ℕ) (μ : Measure (Fin p → ℝ))
    [IsProbabilityMeasure μ] [IsGaussian μ]
    (hmean : (∫ y, y ∂μ) = fun _ => (0 : ℝ)) :
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ id
      (fun i j => ∫ y, y i * y j ∂μ) := by
    classical
    have hint (i : Fin p) : Integrable (fun y : Fin p → ℝ => y i) μ :=
      IsGaussian.integrable_dual μ (ContinuousLinearMap.proj i)
    have hm (i : Fin p) : (∫ y, y i ∂μ) = 0 := by
      rw [← eval_integral hint, hmean]
    have hprod (i j : Fin p) : Integrable (fun y : Fin p → ℝ => y i * y j) μ :=
      (IsGaussian.memLp_dual μ (ContinuousLinearMap.proj i) 2 (by simp)).integrable_mul
        (IsGaussian.memLp_dual μ (ContinuousLinearMap.proj j) 2 (by simp))
    refine ⟨measurable_id, ?_, ?_⟩
    · intro u
      let L : (Fin p → ℝ) →L[ℝ] ℝ := ∑ j : Fin p, u j • ContinuousLinearMap.proj j
      have hmap := IsGaussian.map_eq_gaussianReal (μ := μ) L
      have h := integrable_exp_mul_gaussianReal (μ := ∫ y, L y ∂μ)
        (v := (Var[L; μ]).toNNReal) 1
      rw [← hmap, integrable_map_measure (by fun_prop) (by fun_prop)] at h
      simpa [L, Function.comp_def] using h
    · intro u
      let L : (Fin p → ℝ) →L[ℝ] ℝ := ∑ j : Fin p, u j • ContinuousLinearMap.proj j
      have hL (y : Fin p → ℝ) : L y = ∑ j : Fin p, u j * y j := by simp [L]
      have hmL : (∫ y, L y ∂μ) = 0 := by
        simp_rw [hL]
        rw [integral_finset_sum _ (fun i _ => (hint i).const_mul _)]
        simp [integral_const_mul, hm]
      have hvL : Var[L; μ] = ∑ i : Fin p, ∑ j : Fin p,
          u i * (∫ y, y i * y j ∂μ) * u j := by
        rw [variance_eq_integral (by fun_prop), hmL]
        simp only [sub_zero]
        simp_rw [hL]
        have heq (y : Fin p → ℝ) : (∑ j, u j * y j)^2 =
            ∑ i : Fin p, ∑ j : Fin p, u i * (y i * y j) * u j := by
          simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        simp_rw [heq]
        rw [integral_finset_sum _ (fun i _ =>
          integrable_finset_sum _ (fun j _ => ((hprod i j).const_mul _).mul_const _))]
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finset_sum _ (fun j _ => ((hprod i j).const_mul _).mul_const _)]
        simp only [integral_mul_const, integral_const_mul]
      have hmgf := mgf_gaussianReal (IsGaussian.map_eq_gaussianReal (μ := μ) L) 1
      rw [Real.coe_toNNReal _ (variance_nonneg _ _)] at hmgf
      simp only [mgf, one_mul, hmL, zero_add, one_pow, mul_one, hvL] at hmgf
      simpa only [id_eq, ← hL] using hmgf
  intro b hb
  refine ⟨8 / Real.sqrt b, div_pos (by norm_num) (Real.sqrt_pos.2 hb), ?_⟩
  intro p hp μ hprob hgauss hm hv y a ha
  letI : IsGaussian μ := hgauss
  have hcenter := centeredGaussian_of_IsGaussian p μ hm
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hvar (j : Fin p) : (Real.sqrt b)^2 ≤ ∫ z, z j * z j ∂μ := by
    rw [Real.sq_sqrt hb.le]
    simpa only [pow_two] using hv j
  have h := Statlib.StatFoundation.Convergence.gaussianVector_rectangle_increment_le
    p (by omega) μ (fun i j => ∫ z, z i * z j ∂μ) id hcenter
    (Real.sqrt b) a hs ha.le hvar y
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (show 2 ≤ p by omega)
  have hl : (1/2 : ℝ) ≤ Real.log (p : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < p by positivity)
    have hi : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpR
    norm_num at hi
    linarith
  have hln : 0 ≤ Real.log (p : ℝ) := by linarith
  have hsqr := Real.sq_sqrt hln
  have hsn := Real.sqrt_nonneg (Real.log (p : ℝ))
  have hhalf : (1/2 : ℝ) ≤ Real.sqrt (Real.log (p : ℝ)) := by nlinarith
  have htwo : Real.sqrt 2 ≤ (2 : ℝ) := by
    have hh := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hfac : Real.sqrt (2 * Real.log (p : ℝ)) + 2 ≤
      8 * Real.sqrt (Real.log (p : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [mul_le_mul_of_nonneg_right htwo hsn]
  have hmul := mul_le_mul_of_nonneg_left hfac (show 0 ≤ a / Real.sqrt b by positivity)
  have heq : (a / Real.sqrt b) * (8 * Real.sqrt (Real.log (p : ℝ))) =
      (8 / Real.sqrt b) * a * Real.sqrt (Real.log (p : ℝ)) := by ring
  exact le_trans h (heq ▸ hmul)

  /- @proof-region region.target-node.session.f430fc1d375ea3b2 end -/

end

end Statlib.Imported

