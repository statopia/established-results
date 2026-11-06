import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1728106886_3c04fa7a : ∀ (rho : ℝ) (hrho_pos : 0 < rho) (hrho_le : rho ≤ 1),
    ∫ x in Set.Icc (lambdaMinus rho) (lambdaPlus rho), nuRho rho x = 1 := by
  /- @proof-region region.target-node.session.342f05b30d474708 begin -/
  intro rho hrho_pos hrho_le
  have key : ∀ a b : ℝ, 0 ≤ a → a < b →
      ∫ x in Set.Icc a b, Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - a ^ 2)) / x
        = Real.pi * (b - a) ^ 2 / 4 := by
    intro a b ha hab
    have h1 : ∫ x in Set.Icc a b, Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - a ^ 2)) / x
        = ∫ x in Set.Ioc a b, Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - a ^ 2)) / x :=
      MeasureTheory.integral_Icc_eq_integral_Ioc
    rw [h1, ← intervalIntegral.integral_of_le hab.le]
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0
      rw [intervalIntegral.integral_of_le hab.le]
      have hpt : ∫ x in Set.Ioc 0 b, Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - 0 ^ 2)) / x
          = ∫ x in Set.Ioc 0 b, Real.sqrt (b ^ 2 - x ^ 2) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        obtain ⟨hx0, hxb⟩ := hx
        have hx2 : Real.sqrt (x ^ 2) = x := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hx0]
        show Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - 0 ^ 2)) / x = Real.sqrt (b ^ 2 - x ^ 2)
        rw [show x ^ 2 - 0 ^ 2 = x ^ 2 by ring, mul_comm (b ^ 2 - x ^ 2) (x ^ 2),
          Real.sqrt_mul (sq_nonneg x), hx2]
        field_simp
      rw [hpt, ← intervalIntegral.integral_of_le hab.le]
      have hscale1 : ∫ x in (0:ℝ)..b, Real.sqrt (b ^ 2 - x ^ 2)
          = b * ∫ x in (0:ℝ)..1, Real.sqrt (b ^ 2 - (b * x) ^ 2) := by
        have h := intervalIntegral.mul_integral_comp_mul_add
          (f := fun y : ℝ => Real.sqrt (b ^ 2 - y ^ 2)) (a := (0:ℝ)) (b := (1:ℝ)) (c := b) (d := (0:ℝ))
        simpa using h.symm
      have hcongr2 : ∫ x in (0:ℝ)..1, Real.sqrt (b ^ 2 - (b * x) ^ 2)
          = ∫ x in (0:ℝ)..1, b * Real.sqrt (1 - x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x _
        show Real.sqrt (b ^ 2 - (b * x) ^ 2) = b * Real.sqrt (1 - x ^ 2)
        rw [show b ^ 2 - (b * x) ^ 2 = b ^ 2 * (1 - x ^ 2) by ring]
        rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq_eq_abs, abs_of_pos hab]
      have hpull : ∫ x in (0:ℝ)..1, b * Real.sqrt (1 - x ^ 2)
          = b * ∫ x in (0:ℝ)..1, Real.sqrt (1 - x ^ 2) := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
          intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
        rw [MeasureTheory.integral_const_mul]
      have hquarter : ∫ x in (0:ℝ)..1, Real.sqrt (1 - x ^ 2) = Real.pi / 4 := by
        have hbase : Continuous fun x : ℝ => Real.sqrt (1 - x ^ 2) :=
          Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))
        have hint : ∀ c d : ℝ, IntervalIntegrable (fun x : ℝ => Real.sqrt (1 - x ^ 2)) volume c d :=
          fun c d => (hbase.continuousOn.mono (Set.subset_univ _)).intervalIntegrable
        have hsplit : (∫ x in (-1:ℝ)..0, Real.sqrt (1 - x ^ 2)) +
            (∫ x in (0:ℝ)..1, Real.sqrt (1 - x ^ 2))
            = ∫ x in (-1:ℝ)..1, Real.sqrt (1 - x ^ 2) :=
          intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
        have hsym : ∫ x in (-1:ℝ)..0, Real.sqrt (1 - x ^ 2) = ∫ x in (0:ℝ)..1, Real.sqrt (1 - x ^ 2) := by
          have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1)
            (f := fun x : ℝ => Real.sqrt (1 - x ^ 2))
          simpa using h.symm
        rw [hsym, integral_sqrt_one_sub_sq] at hsplit
        linarith
      rw [hscale1, hcongr2, hpull, hquarter]
      ring
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      set A : ℝ := (a ^ 2 + b ^ 2) / 2 with hA
      set B : ℝ := (b ^ 2 - a ^ 2) / 2 with hB
      have hAB1 : A - B = a ^ 2 := by rw [hA, hB]; ring
      have hAB2 : A + B = b ^ 2 := by rw [hA, hB]; ring
      have hBpos : 0 < B := by
        have h3 : 0 < (b - a) * (b + a) := mul_pos (by linarith) (by linarith)
        rw [hB, show b ^ 2 - a ^ 2 = (b - a) * (b + a) by ring]
        linarith
      have hBA : B < A := by linarith [hAB1, pow_pos hapos 2]
      have hABsq : A ^ 2 - B ^ 2 = (a * b) ^ 2 := by
        have h1 : A ^ 2 - B ^ 2 = (A - B) * (A + B) := by ring
        rw [h1, hAB1, hAB2]; ring
      have hCsq_pos : 0 < A ^ 2 - B ^ 2 := by
        rw [hABsq]
        exact pow_pos (mul_pos hapos (lt_trans hapos hab)) 2
      set C : ℝ := Real.sqrt (A ^ 2 - B ^ 2) with hC
      have hCsq : C ^ 2 = A ^ 2 - B ^ 2 := by
        rw [hC]; exact Real.sq_sqrt hCsq_pos.le
      have hCpos : 0 < C := by rw [hC]; exact Real.sqrt_pos.mpr hCsq_pos
      have hfsqrt_pos : ∀ φ : ℝ, 0 < A + B * Real.cos φ := by
        intro φ
        have hc : B * (-1) ≤ B * Real.cos φ :=
          mul_le_mul_of_nonneg_left (Real.neg_one_le_cos φ) hBpos.le
        linarith
      have hfderiv : ∀ φ ∈ Set.uIcc (0:ℝ) Real.pi,
          HasDerivAt (fun φ : ℝ => Real.sqrt (A + B * Real.cos φ))
            ((B * -Real.sin φ) / (2 * Real.sqrt (A + B * Real.cos φ))) φ := by
        intro φ _
        have hinner : HasDerivAt (fun φ : ℝ => A + B * Real.cos φ) (B * -Real.sin φ) φ := by
          have h3 := (hasDerivAt_const φ A).add ((Real.hasDerivAt_cos φ).const_mul B)
          simpa only [zero_add] using h3
        exact hinner.sqrt (ne_of_gt (hfsqrt_pos φ))
      have hf'cont : ContinuousOn
          (fun φ : ℝ => (B * -Real.sin φ) / (2 * Real.sqrt (A + B * Real.cos φ)))
          (Set.uIcc (0:ℝ) Real.pi) := by
        have hnumc : ContinuousOn (fun φ : ℝ => B * -Real.sin φ) (Set.uIcc (0:ℝ) Real.pi) :=
          (continuous_const.mul (continuous_neg.comp Real.continuous_sin)).continuousOn
        have hdenc : ContinuousOn (fun φ : ℝ => 2 * Real.sqrt (A + B * Real.cos φ))
            (Set.uIcc (0:ℝ) Real.pi) := by
          have hc : Continuous fun φ : ℝ => A + B * Real.cos φ :=
            continuous_const.add (continuous_const.mul Real.continuous_cos)
          exact (continuous_const.mul (Real.continuous_sqrt.comp hc)).continuousOn
        exact hnumc.div hdenc (fun φ _ => by
          have hp := hfsqrt_pos φ
          have hsp : 0 < Real.sqrt (A + B * Real.cos φ) := Real.sqrt_pos.mpr hp
          linarith)
      have hg_cont : ContinuousOn
          (fun x : ℝ => Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - a ^ 2)) / x) (Set.Ioi 0) := by
        have hnum : Continuous fun x : ℝ => Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - a ^ 2)) :=
          Real.continuous_sqrt.comp
            ((continuous_const.sub (continuous_id.pow 2)).mul
              ((continuous_id.pow 2).sub continuous_const))
        exact hnum.continuousOn.div continuousOn_id (fun x hx => ne_of_gt hx)
      have himage : (fun φ : ℝ => Real.sqrt (A + B * Real.cos φ)) '' Set.uIcc (0:ℝ) Real.pi ⊆
          Set.Ioi 0 := by
        rintro x ⟨φ, _, rfl⟩
        exact Real.sqrt_pos.mpr (hfsqrt_pos φ)
      have hmain := intervalIntegral.integral_comp_mul_deriv' hfderiv hf'cont (hg_cont.mono himage)
      have hcos_pi : Real.cos Real.pi = -1 := by
        simp
      have hfb : Real.sqrt (A + B * Real.cos 0) = b := by
        have h1 : A + B * Real.cos 0 = b ^ 2 := by
          have hc : Real.cos (0:ℝ) = 1 := by simp
          rw [hc, ← hAB2]
          ring
        rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt (lt_trans hapos hab))]
      have hfa : Real.sqrt (A + B * Real.cos Real.pi) = a := by
        have h1 : A + B * Real.cos Real.pi = a ^ 2 := by
          rw [hcos_pi]
          have h2 : A + B * (-1) = A - B := by ring
          rw [h2, hAB1]
        rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hapos)]
      have hR : ∫ x in (Real.sqrt (A + B * Real.cos 0))..(Real.sqrt (A + B * Real.cos Real.pi)),
            Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - a ^ 2)) / x
          = -∫ x in a..b, Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - a ^ 2)) / x := by
        rw [hfb, hfa, intervalIntegral.integral_symm]
      have hmain' := hmain
      have hLR : ∫ φ in (0:ℝ)..Real.pi,
            Real.sqrt ((b ^ 2 - Real.sqrt (A + B * Real.cos φ) ^ 2) *
                (Real.sqrt (A + B * Real.cos φ) ^ 2 - a ^ 2)) /
                Real.sqrt (A + B * Real.cos φ) *
              ((B * -Real.sin φ) / (2 * Real.sqrt (A + B * Real.cos φ)))
          = -((B ^ 2 / 2) * ∫ φ in (0:ℝ)..Real.pi,
              Real.sin φ ^ 2 / (A + B * Real.cos φ)) := by
        rw [intervalIntegral.integral_of_le Real.pi_pos.le,
          intervalIntegral.integral_of_le Real.pi_pos.le,
          ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_neg]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro φ hφ
        obtain ⟨hφ1, hφ2⟩ := hφ
        show Real.sqrt ((b ^ 2 - Real.sqrt (A + B * Real.cos φ) ^ 2) *
              (Real.sqrt (A + B * Real.cos φ) ^ 2 - a ^ 2)) /
              Real.sqrt (A + B * Real.cos φ) *
              ((B * -Real.sin φ) / (2 * Real.sqrt (A + B * Real.cos φ)))
            = -((B ^ 2 / 2) * (Real.sin φ ^ 2 / (A + B * Real.cos φ)))
        have hs2 : Real.sqrt (A + B * Real.cos φ) ^ 2 = A + B * Real.cos φ :=
          Real.sq_sqrt (hfsqrt_pos φ).le
        have hs0 : Real.sqrt (A + B * Real.cos φ) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.mpr (hfsqrt_pos φ))
        have hsinnn : 0 ≤ Real.sin φ := by
          apply Real.sin_nonneg_of_mem_Icc
          constructor <;> linarith [Real.pi_pos]
        have hsqrt_eq : Real.sqrt ((b ^ 2 - Real.sqrt (A + B * Real.cos φ) ^ 2) *
            (Real.sqrt (A + B * Real.cos φ) ^ 2 - a ^ 2)) = B * Real.sin φ := by
          have hbs : b ^ 2 - Real.sqrt (A + B * Real.cos φ) ^ 2 = B * (1 - Real.cos φ) := by
            rw [hs2, ← hAB2]; ring
          have hsa : Real.sqrt (A + B * Real.cos φ) ^ 2 - a ^ 2 = B * (1 + Real.cos φ) := by
            rw [hs2, ← hAB1]; ring
          have hprod : (b ^ 2 - Real.sqrt (A + B * Real.cos φ) ^ 2) *
              (Real.sqrt (A + B * Real.cos φ) ^ 2 - a ^ 2) = (B * Real.sin φ) ^ 2 := by
            rw [hbs, hsa, mul_pow,
              show Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 by
                linarith [Real.sin_sq_add_cos_sq φ]]
            ring
          rw [hprod, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hBpos.le hsinnn)]
        rw [hsqrt_eq]
        have hd0 : A + B * Real.cos φ ≠ 0 := ne_of_gt (hfsqrt_pos φ)
        field_simp
        rw [hs2]
      have hstep : (B ^ 2 / 2) * ∫ φ in (0:ℝ)..Real.pi, Real.sin φ ^ 2 / (A + B * Real.cos φ)
          = ∫ x in a..b, Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - a ^ 2)) / x := by
        have h := hmain
        rw [hR] at h
        simp only [Function.comp_apply] at h
        rw [hLR] at h
        exact neg_inj.mp h
      have hCab : C = a * b := by
        rw [hC, hABsq, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (mul_nonneg hapos.le (le_of_lt (lt_trans hapos hab)))]
      have hAC : A - C = (b - a) ^ 2 / 2 := by
        rw [hCab, hA]; ring
      have hJ : ∫ φ in (0:ℝ)..Real.pi, Real.sin φ ^ 2 / (A + B * Real.cos φ)
          = Real.pi * (A - C) / B ^ 2 := by
        let g : ℝ → ℝ := fun φ => (A * Real.cos φ + B) / (A + B * Real.cos φ)
        let F : ℝ → ℝ := fun φ => (A * φ - B * Real.sin φ) / B ^ 2 + (C / B ^ 2) * Real.arcsin (g φ)
        have hgd : ∀ φ : ℝ,
            HasDerivAt g (Real.sin φ * (B ^ 2 - A ^ 2) / (A + B * Real.cos φ) ^ 2) φ := by
          intro φ
          have hnum : HasDerivAt (fun φ : ℝ => A * Real.cos φ + B) (A * -Real.sin φ) φ := by
            have ha : HasDerivAt (fun φ : ℝ => A * Real.cos φ) (A * -Real.sin φ) φ :=
              (Real.hasDerivAt_cos φ).const_mul A
            have hb : HasDerivAt (fun _ : ℝ => B) 0 φ := hasDerivAt_const φ B
            simpa only [add_zero] using ha.add hb
          have hden : HasDerivAt (fun φ : ℝ => A + B * Real.cos φ) (B * -Real.sin φ) φ := by
            have hb := (hasDerivAt_const φ A).add ((Real.hasDerivAt_cos φ).const_mul B)
            simpa only [zero_add] using hb
          have hq := hnum.div hden (ne_of_gt (hfsqrt_pos φ))
          have hsimp : A * -Real.sin φ * (A + B * Real.cos φ) -
              (A * Real.cos φ + B) * (B * -Real.sin φ) = Real.sin φ * (B ^ 2 - A ^ 2) := by ring
          rw [hsimp] at hq
          exact hq
        have hone : ∀ φ : ℝ, 1 - (g φ) ^ 2 = (C * Real.sin φ / (A + B * Real.cos φ)) ^ 2 := by
          intro φ
          show 1 - ((A * Real.cos φ + B) / (A + B * Real.cos φ)) ^ 2
              = (C * Real.sin φ / (A + B * Real.cos φ)) ^ 2
          have hC2 : C ^ 2 = A ^ 2 - B ^ 2 := hCsq
          have hs2 : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
          have hsin2 : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := by linarith
          have hnum : (A + B * Real.cos φ) ^ 2 - (A * Real.cos φ + B) ^ 2
              = (C * Real.sin φ) ^ 2 := by
            rw [show (A + B * Real.cos φ) ^ 2 - (A * Real.cos φ + B) ^ 2
                = (A ^ 2 - B ^ 2) * (1 - Real.cos φ ^ 2) by ring, ← hC2, ← hsin2]
            ring
          have h1 : 1 - ((A * Real.cos φ + B) / (A + B * Real.cos φ)) ^ 2
              = ((A + B * Real.cos φ) ^ 2 - (A * Real.cos φ + B) ^ 2) /
                (A + B * Real.cos φ) ^ 2 := by
            rw [div_pow, sub_div, div_self (ne_of_gt (pow_pos (hfsqrt_pos φ) 2))]
          rw [h1, hnum, div_pow]
        have hsqrtg : ∀ φ ∈ Set.Ioo (0:ℝ) Real.pi,
            Real.sqrt (1 - (g φ) ^ 2) = C * Real.sin φ / (A + B * Real.cos φ) := by
          intro φ hφ
          have hsin : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
          rw [hone φ, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (div_nonneg (mul_nonneg hCpos.le hsin.le) (hfsqrt_pos φ).le)]
        have hF_deriv : ∀ φ ∈ Set.Ioo (0:ℝ) Real.pi,
            HasDerivAt F (Real.sin φ ^ 2 / (A + B * Real.cos φ)) φ := by
          intro φ hφ
          have hsin : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
          have hs2 : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
          have hsin2 : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := by linarith
          have hd0 : A + B * Real.cos φ ≠ 0 := ne_of_gt (hfsqrt_pos φ)
          have hB2 : B ^ 2 ≠ 0 := ne_of_gt (pow_pos hBpos 2)
          have hC0 : C ≠ 0 := ne_of_gt hCpos
          have hs0 : Real.sin φ ≠ 0 := ne_of_gt hsin
          have hne : 1 - (g φ) ^ 2 ≠ 0 := by
            rw [hone φ]
            exact ne_of_gt (pow_pos (div_pos (mul_pos hCpos hsin) (hfsqrt_pos φ)) 2)
          have hg1 : g φ ≠ 1 := fun hh => hne (by rw [hh]; ring)
          have hg2 : g φ ≠ -1 := fun hh => hne (by rw [hh]; ring)
          have harc : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (g φ) ^ 2)) (g φ) :=
            Real.hasDerivAt_arcsin hg2 hg1
          have hcomp := harc.comp φ (hgd φ)
          have hlin : HasDerivAt (fun φ : ℝ => (A * φ - B * Real.sin φ) / B ^ 2)
              ((A - B * Real.cos φ) / B ^ 2) φ := by
            have h1 : HasDerivAt (fun φ : ℝ => A * φ) A φ := by
              have hh := (hasDerivAt_id' φ).const_mul A
              simpa using hh
            have h2 : HasDerivAt (fun φ : ℝ => B * Real.sin φ) (B * Real.cos φ) φ :=
              (Real.hasDerivAt_sin φ).const_mul B
            exact (h1.sub h2).div_const (B ^ 2)
          have htot := hlin.add (hcomp.const_mul (C / B ^ 2))
          rw [hsqrtg φ hφ] at htot
          have hfin : (A - B * Real.cos φ) / B ^ 2 +
              (C / B ^ 2) * ((1 / (C * Real.sin φ / (A + B * Real.cos φ))) *
                (Real.sin φ * (B ^ 2 - A ^ 2) / (A + B * Real.cos φ) ^ 2))
              = Real.sin φ ^ 2 / (A + B * Real.cos φ) := by
            field_simp
            rw [hsin2]
            ring
          rw [hfin] at htot
          exact htot
        have hcont : ContinuousOn F (Set.Icc (0:ℝ) Real.pi) := by
          have hgcont : Continuous g := by
            have hn : Continuous fun φ : ℝ => A * Real.cos φ + B :=
              (continuous_const.mul Real.continuous_cos).add continuous_const
            have hdn : Continuous fun φ : ℝ => A + B * Real.cos φ :=
              continuous_const.add (continuous_const.mul Real.continuous_cos)
            exact hn.div hdn (fun φ => ne_of_gt (hfsqrt_pos φ))
          have h1 : Continuous fun φ : ℝ => (A * φ - B * Real.sin φ) / B ^ 2 := by
            have hx : Continuous fun φ : ℝ => A * φ := continuous_const.mul continuous_id
            have hy : Continuous fun φ : ℝ => B * Real.sin φ :=
              continuous_const.mul Real.continuous_sin
            exact (hx.sub hy).div_const (B ^ 2)
          have h2 : Continuous fun φ : ℝ => (C / B ^ 2) * Real.arcsin (g φ) :=
            continuous_const.mul (Real.continuous_arcsin.comp hgcont)
          exact (h1.add h2).continuousOn
        have hii : IntervalIntegrable (fun φ : ℝ => Real.sin φ ^ 2 / (A + B * Real.cos φ))
            volume (0:ℝ) Real.pi := by
          have hn : ContinuousOn (fun φ : ℝ => Real.sin φ ^ 2) (Set.uIcc (0:ℝ) Real.pi) :=
            (Real.continuous_sin.pow 2).continuousOn
          have hdn : ContinuousOn (fun φ : ℝ => A + B * Real.cos φ)
              (Set.uIcc (0:ℝ) Real.pi) :=
            (continuous_const.add (continuous_const.mul Real.continuous_cos)).continuousOn
          exact (hn.div hdn (fun φ _ => ne_of_gt (hfsqrt_pos φ))).intervalIntegrable
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le hcont hF_deriv hii
        have hABpos : (0:ℝ) < A + B := by
          rw [hAB2]
          exact pow_pos (lt_trans hapos hab) 2
        have hg0 : g 0 = 1 := by
          show (A * Real.cos 0 + B) / (A + B * Real.cos 0) = 1
          have hc : Real.cos (0:ℝ) = 1 := by simp
          rw [hc]
          have h1 : A * (1:ℝ) + B = A + B := by ring
          have h2 : A + B * (1:ℝ) = A + B := by ring
          rw [h1, h2]
          exact div_self (ne_of_gt hABpos)
        have hgpi : g Real.pi = -1 := by
          show (A * Real.cos Real.pi + B) / (A + B * Real.cos Real.pi) = -1
          rw [hcos_pi]
          have h1 : A * (-1:ℝ) + B = -(A - B) := by ring
          have h2 : A + B * (-1:ℝ) = A - B := by ring
          have hne : A - B ≠ 0 := by
            have hpos : (0:ℝ) < A - B := by
              rw [hAB1]
              exact pow_pos hapos 2
            exact ne_of_gt hpos
          rw [h1, h2, neg_div, div_self hne]
        rw [h]
        have hsin0 : Real.sin (0:ℝ) = 0 := by simp
        have hFpi : F Real.pi = A * Real.pi / B ^ 2 - (C / B ^ 2) * (Real.pi / 2) := by
          show (A * Real.pi - B * Real.sin Real.pi) / B ^ 2 +
              (C / B ^ 2) * Real.arcsin (g Real.pi)
              = A * Real.pi / B ^ 2 - (C / B ^ 2) * (Real.pi / 2)
          rw [Real.sin_pi, hgpi, Real.arcsin_neg_one, mul_zero, sub_zero, mul_neg,
            sub_eq_add_neg]
        have hF0 : F 0 = (C / B ^ 2) * (Real.pi / 2) := by
          show (A * 0 - B * Real.sin 0) / B ^ 2 + (C / B ^ 2) * Real.arcsin (g 0)
              = (C / B ^ 2) * (Real.pi / 2)
          rw [hsin0, hg0, Real.arcsin_one]
          simp only [mul_zero, sub_zero, zero_div, zero_add]
        rw [hFpi, hF0]
        have hB2 : B ^ 2 ≠ 0 := ne_of_gt (pow_pos hBpos 2)
        field_simp
        ring
      rw [← hstep, hJ, hAC]
      field_simp
      ring
  have hmin_nonneg : 0 ≤ lambdaMinus rho := by
    simp only [lambdaMinus]
    linarith [Real.sqrt_nonneg rho, Real.sqrt_le_one.mpr hrho_le]
  have hlt : lambdaMinus rho < lambdaPlus rho := by
    have hp : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
    simp only [lambdaMinus, lambdaPlus]
    linarith
  have hcongr : ∫ x in Set.Icc (lambdaMinus rho) (lambdaPlus rho), nuRho rho x
      = ∫ x in Set.Icc (lambdaMinus rho) (lambdaPlus rho),
          Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)) /
            (Real.pi * rho * x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro x hx
    simp only [nuRho, Set.mem_Icc] at hx ⊢
    rw [if_pos hx]
  have hfac : ∫ x in Set.Icc (lambdaMinus rho) (lambdaPlus rho),
        Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)) /
          (Real.pi * rho * x)
      = (1 / (Real.pi * rho)) * ∫ x in Set.Icc (lambdaMinus rho) (lambdaPlus rho),
          Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)) / x := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro x hx
    rcases eq_or_ne x 0 with hx0 | hx0
    · subst hx0
      simp
    · simp only []
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
  rw [hcongr, hfac, key (lambdaMinus rho) (lambdaPlus rho) hmin_nonneg hlt]
  have hdiff : lambdaPlus rho - lambdaMinus rho = 2 * Real.sqrt rho := by
    simp only [lambdaPlus, lambdaMinus]
    ring
  have hsq2 : (2 * Real.sqrt rho) ^ 2 = 4 * rho := by
    have h := Real.sq_sqrt hrho_pos.le
    rw [mul_pow, show (2:ℝ) ^ 2 = 4 by norm_num, h]
  rw [hdiff, hsq2]
  field_simp
  /- @proof-region region.target-node.session.342f05b30d474708 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_1728106886_3c04fa7a


