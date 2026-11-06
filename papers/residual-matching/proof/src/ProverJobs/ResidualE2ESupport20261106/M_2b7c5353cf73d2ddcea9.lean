import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
theorem statopia_math_node_4071678792_608a93f0 : ∀ (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus)
    (h_rhoMinus_le : rhoMinus ≤ 1),
    ∃ cRho tRho : ℝ, 0 < cRho ∧ 0 < tRho ∧
      ∀ rho : ℝ, rhoMinus ≤ rho → rho ≤ 1 →
        ∀ x : ℝ, mpLambdaMinus rho ≤ x → x ≤ mpLambdaPlus rho →
          ∀ t : ℝ, 0 < t → t ≤ tRho →
            (x + t ≤ mpLambdaPlus rho →
              cRho * t ^ ((3 : ℝ) / 2) ≤ ∫ u in x..(x + t), rootedMPDensity rho u) ∧
            (mpLambdaMinus rho ≤ x - t →
              cRho * t ^ ((3 : ℝ) / 2) ≤ ∫ u in (x - t)..x, rootedMPDensity rho u) := by
  /- @proof-region region.target-node.session.507dc21fad6d83e3 begin -/
  intro rhoMinus h_rhoMinus_pos h_rhoMinus_le
  have hsrm_pos : 0 < Real.sqrt rhoMinus := Real.sqrt_pos.2 h_rhoMinus_pos
  refine ⟨Real.sqrt (Real.sqrt rhoMinus) / (8 * Real.pi), min 1 (Real.sqrt rhoMinus / 2),
    ?_, ?_, ?_⟩
  · have h2 : (0 : ℝ) < Real.sqrt (Real.sqrt rhoMinus) := Real.sqrt_pos.2 hsrm_pos
    exact div_pos h2 (by positivity)
  · exact lt_min one_pos (by positivity)
  · intro rho hrho_ge hrho_le x hxlo hxhi t ht htle
    have hrho_pos : 0 < rho := lt_of_lt_of_le h_rhoMinus_pos hrho_ge
    set r : ℝ := Real.sqrt rho with hr_def
    have hr_pos : 0 < r := by rw [hr_def]; exact Real.sqrt_pos.2 hrho_pos
    have hr_le_one : r ≤ 1 := by
      rw [hr_def, ← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hrho_le
    have hsr_le_r : Real.sqrt rhoMinus ≤ r := by
      rw [hr_def]; exact Real.sqrt_le_sqrt hrho_ge
    have hlo_nonneg : 0 ≤ 1 - r := by linarith
    have hhi_pos : 0 < 1 + r := by linarith
    have hhi_le_two : 1 + r ≤ 2 := by linarith
    have ht_one : t ≤ 1 := le_trans htle (min_le_left _ _)
    have ht_sq : t ≤ Real.sqrt rhoMinus / 2 := le_trans htle (min_le_right _ _)
    have ht_quarter : t ≤ ((1 + r) - (1 - r)) / 4 := by
      have h2 : (1 + r) - (1 - r) = 2 * r := by ring
      rw [h2]; nlinarith
    have hxlo' : 1 - r ≤ x := by
      have h : mpLambdaMinus rho = 1 - r := by rw [mpLambdaMinus, hr_def]
      linarith
    have hxhi' : x ≤ 1 + r := by
      have h : mpLambdaPlus rho = 1 + r := by rw [mpLambdaPlus, hr_def]
      linarith
    have hcontG : Continuous (fun u : ℝ => Real.sqrt (((1 + r) - u) * (u - (1 - r)))) :=
      Real.continuous_sqrt.comp
        ((continuous_const.sub continuous_id).mul (continuous_id.sub continuous_const))
    have hIntG : ∀ a b : ℝ, a ≤ b →
        IntervalIntegrable (fun u : ℝ => Real.sqrt (((1 + r) - u) * (u - (1 - r)))) volume a b := by
      intro a b hab
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      exact ContinuousOn.integrableOn_compact isCompact_Icc hcontG.continuousOn
    have hdens : ∀ u : ℝ, 1 - r ≤ u → u ≤ 1 + r →
        (1 / (2 * Real.pi)) * Real.sqrt (((1 + r) - u) * (u - (1 - r))) ≤ rootedMPDensity rho u := by
      intro u h1 h2
      have hpm : mpLambdaPlus rho = 1 + r := by rw [mpLambdaPlus, hr_def]
      have hmm : mpLambdaMinus rho = 1 - r := by rw [mpLambdaMinus, hr_def]
      rw [rootedMPDensity, hpm, hmm,
        if_pos (show 1 - r ≤ u ∧ u ≤ 1 + r from ⟨h1, h2⟩), mul_one]
      rcases eq_or_lt_of_le (le_trans hlo_nonneg h1 : (0 : ℝ) ≤ u) with hzero | hupos
      · have hu0 : u = 0 := hzero.symm
        have hr1 : r = 1 := by rw [hu0] at h1; linarith
        rw [hu0, hr1]
        norm_num
      · have hPS : 0 ≤ ((1 + r) - u) * (u - (1 - r)) :=
          mul_nonneg (by linarith) (by linarith)
        have hprod_eq : ((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)
            = (((1 + r) - u) * (u - (1 - r))) * (((1 + r) + u) * (u + (1 - r))) := by
          rw [show (1 + r) ^ 2 - u ^ 2 = ((1 + r) - u) * ((1 + r) + u) by ring,
            show u ^ 2 - (1 - r) ^ 2 = (u - (1 - r)) * (u + (1 - r)) by ring]
          ring
        have hmain : Real.sqrt (((1 + r) - u) * (u - (1 - r)))
            ≤ Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) / u := by
          have hupper : u ≤ Real.sqrt (((1 + r) + u) * (u + (1 - r))) := by
            have hle : u ^ 2 ≤ ((1 + r) + u) * (u + (1 - r)) := by
              nlinarith [hupos.le, hhi_pos, hlo_nonneg]
            calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq hupos.le).symm
              _ ≤ Real.sqrt (((1 + r) + u) * (u + (1 - r))) := Real.sqrt_le_sqrt hle
          have hkey : Real.sqrt (((1 + r) - u) * (u - (1 - r))) * u
              ≤ Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) := by
            rw [hprod_eq, Real.sqrt_mul hPS]
            exact mul_le_mul_of_nonneg_left hupper (Real.sqrt_nonneg _)
          have hu1 : u * u⁻¹ = (1 : ℝ) := by field_simp
          calc Real.sqrt (((1 + r) - u) * (u - (1 - r)))
              = (Real.sqrt (((1 + r) - u) * (u - (1 - r))) * u) * u⁻¹ := by
                  rw [mul_assoc, hu1, mul_one]
            _ ≤ Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) * u⁻¹ :=
                  mul_le_mul_of_nonneg_right hkey (by positivity)
            _ = Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) / u := by
                  rw [div_eq_mul_inv]
        have hle1 : (1 : ℝ) / (2 * Real.pi) ≤ 1 / (Real.pi * rho) := by
          have hpos : (0 : ℝ) < Real.pi * rho := by positivity
          have h2r : Real.pi * rho ≤ 2 * Real.pi := by
            have h2' : rho ≤ 2 := by linarith [hrho_le]
            calc Real.pi * rho ≤ Real.pi * 2 := mul_le_mul_of_nonneg_left h2' Real.pi_pos.le
              _ = 2 * Real.pi := by ring
          exact one_div_le_one_div_of_le hpos h2r
        have hconv : (1 / Real.pi) * Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) / (rho * u)
            = (1 / (Real.pi * rho))
              * (Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) / u) := by
          set S := Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) with hS
          field_simp
        rw [hconv]
        calc (1 / (2 * Real.pi)) * Real.sqrt (((1 + r) - u) * (u - (1 - r)))
            ≤ (1 / (2 * Real.pi))
              * (Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) / u) :=
              mul_le_mul_of_nonneg_left hmain (by positivity)
          _ ≤ (1 / (Real.pi * rho))
              * (Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) / u) :=
              mul_le_mul_of_nonneg_right hle1 (by positivity)
    have hgeom : ∀ (c a b t' L : ℝ), 0 ≤ a → t' ≤ b → a + b = L → 0 < t' → t' ≤ L / 4 →
        (1 / 2) * Real.sqrt (L / 8) * t' ^ ((3 : ℝ) / 2) ≤
          ∫ u in c..(c + t'), Real.sqrt ((b - (u - c)) * (a + (u - c))) := by
      intro c a b t' L ha htb hsum ht' htL
      have hLnonneg : 0 ≤ L := by linarith
      have hcontf : Continuous (fun u : ℝ => Real.sqrt ((b - (u - c)) * (a + (u - c)))) :=
        Real.continuous_sqrt.comp
          ((continuous_const.sub (continuous_id.sub continuous_const)).mul
            (continuous_const.add (continuous_id.sub continuous_const)))
      have hfnonneg : ∀ u : ℝ, 0 ≤ Real.sqrt ((b - (u - c)) * (a + (u - c))) :=
        fun u => Real.sqrt_nonneg _
      have hIntf : ∀ p q : ℝ, p ≤ q →
          IntervalIntegrable (fun u : ℝ => Real.sqrt ((b - (u - c)) * (a + (u - c)))) volume p q := by
        intro p q hpq
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hpq]
        exact ContinuousOn.integrableOn_compact isCompact_Icc hcontf.continuousOn
      have key : ∀ p q : ℝ, p ≤ q → q - p = t' / 2 →
          (∀ u ∈ Set.Icc p q, Real.sqrt (L * t' / 8) ≤ Real.sqrt ((b - (u - c)) * (a + (u - c)))) →
          (1 / 2) * Real.sqrt (L / 8) * t' ^ ((3 : ℝ) / 2)
            ≤ ∫ u in p..q, Real.sqrt ((b - (u - c)) * (a + (u - c))) := by
        intro p q hpq hlen hpt
        have hmono : ∫ u in p..q, Real.sqrt (L * t' / 8)
            ≤ ∫ u in p..q, Real.sqrt ((b - (u - c)) * (a + (u - c))) :=
          intervalIntegral.integral_mono_on hpq intervalIntegral.intervalIntegrable_const
            (hIntf p q hpq) hpt
        have hval : ∫ u in p..q, Real.sqrt (L * t' / 8) = Real.sqrt (L * t' / 8) * (q - p) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
        have harith : Real.sqrt (L * t' / 8) * (t' / 2)
            = (1 / 2) * Real.sqrt (L / 8) * t' ^ ((3 : ℝ) / 2) := by
          have h1 : Real.sqrt (L * t' / 8) = Real.sqrt (L / 8) * Real.sqrt t' := by
            rw [show L * t' / 8 = L / 8 * t' by ring, Real.sqrt_mul (by linarith : (0 : ℝ) ≤ L / 8)]
          have h2 : t' ^ ((3 : ℝ) / 2) = t' * Real.sqrt t' := by
            rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num]
            rw [Real.rpow_add ht']
            rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
          rw [h1, h2]
          ring
        calc (1 / 2) * Real.sqrt (L / 8) * t' ^ ((3 : ℝ) / 2)
            = Real.sqrt (L * t' / 8) * (q - p) := by rw [hlen]; exact harith.symm
          _ = ∫ u in p..q, Real.sqrt (L * t' / 8) := hval.symm
          _ ≤ ∫ u in p..q, Real.sqrt ((b - (u - c)) * (a + (u - c))) := hmono
      by_cases hcase : a ≤ L / 2
      · have hhalf : (1 / 2) * Real.sqrt (L / 8) * t' ^ ((3 : ℝ) / 2)
            ≤ ∫ u in (c + t' / 2)..(c + t'), Real.sqrt ((b - (u - c)) * (a + (u - c))) := by
          apply key (c + t' / 2) (c + t') (by linarith) (by ring)
          intro u hu
          obtain ⟨hu1, hu2⟩ := hu
          have hY : t' / 2 ≤ a + (u - c) := by linarith
          have hX : L / 4 ≤ b - (u - c) := by linarith
          have hprod : (L / 4) * (t' / 2) ≤ (b - (u - c)) * (a + (u - c)) :=
            mul_le_mul hX hY (by linarith) (by linarith)
          have heq : L * t' / 8 = (L / 4) * (t' / 2) := by ring
          rw [heq]
          exact Real.sqrt_le_sqrt hprod
        have hle : ∫ u in (c + t' / 2)..(c + t'), Real.sqrt ((b - (u - c)) * (a + (u - c)))
            ≤ ∫ u in c..(c + t'), Real.sqrt ((b - (u - c)) * (a + (u - c))) :=
          intervalIntegral.integral_mono_interval (by linarith) (by linarith) (le_refl (c + t'))
            (Filter.Eventually.of_forall hfnonneg) (hIntf c (c + t') (by linarith))
        exact le_trans hhalf hle
      · push_neg at hcase
        have hhalf : (1 / 2) * Real.sqrt (L / 8) * t' ^ ((3 : ℝ) / 2)
            ≤ ∫ u in c..(c + t' / 2), Real.sqrt ((b - (u - c)) * (a + (u - c))) := by
          apply key c (c + t' / 2) (by linarith) (by ring)
          intro u hu
          obtain ⟨hu1, hu2⟩ := hu
          have hY : L / 2 ≤ a + (u - c) := by linarith [hcase, ha, hu1]
          have hX : t' / 2 ≤ b - (u - c) := by linarith [htb, hu2]
          have hL2 : (0 : ℝ) ≤ L / 2 := by linarith [hLnonneg]
          have hbd : (0 : ℝ) ≤ b - (u - c) := by linarith [htb, hu2]
          have hprod1 : (t' / 2) * (L / 2) ≤ (b - (u - c)) * (a + (u - c)) :=
            mul_le_mul hX hY hL2 hbd
          have hprod2 : L * t' / 8 ≤ (t' / 2) * (L / 2) := by
            have h0 : 0 ≤ L * t' := mul_nonneg hLnonneg ht'.le
            have he : (t' / 2) * (L / 2) = L * t' / 4 := by ring
            rw [he]
            linarith [h0]
          exact Real.sqrt_le_sqrt (le_trans hprod2 hprod1)
        have hmid : c ≤ c + t' / 2 := by linarith [ht']
        have htop : c + t' / 2 ≤ c + t' := by linarith [ht']
        have hInt : IntervalIntegrable
            (fun u : ℝ => Real.sqrt ((b - (u - c)) * (a + (u - c)))) volume c (c + t') :=
          hIntf c (c + t') (by linarith [ht'])
        have hle : ∫ u in c..(c + t' / 2), Real.sqrt ((b - (u - c)) * (a + (u - c)))
            ≤ ∫ u in c..(c + t'), Real.sqrt ((b - (u - c)) * (a + (u - c))) :=
          intervalIntegral.integral_mono_interval (le_refl c) hmid htop
            (Filter.Eventually.of_forall hfnonneg) hInt
        exact le_trans hhalf hle
    have hcontP : Continuous (fun u : ℝ =>
        (mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) :=
      (continuous_const.sub (continuous_id.pow 2)).mul
        ((continuous_id.pow 2).sub continuous_const)
    have hsqrt : Measurable (fun u : ℝ =>
        Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2))) :=
      Real.continuous_sqrt.measurable.comp hcontP.measurable
    have hcore : Measurable (fun u : ℝ =>
        (1 / Real.pi) *
          Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u)) :=
      (measurable_const.mul hsqrt).div (measurable_const.mul measurable_id)
    have hpm : mpLambdaPlus rho = 1 + r := by rw [mpLambdaPlus, hr_def]
    have hmm : mpLambdaMinus rho = 1 - r := by rw [mpLambdaMinus, hr_def]
    have hCoreBound : ∀ u : ℝ,
        |(1 / Real.pi) *
          Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u)|
          ≤ 2 / (Real.pi * rho) := by
      intro u
      rw [hpm, hmm]
      rcases eq_or_ne u 0 with hu0 | hu0
      · rw [hu0, mul_zero, div_zero, abs_zero]
        positivity
      · have hP2 : ((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2) ≤ 4 * u ^ 2 := by
          rcases le_total (u ^ 2) ((1 + r) ^ 2) with hc | hc
          · have h1 : u ^ 2 - (1 - r) ^ 2 ≤ u ^ 2 := by linarith [sq_nonneg (1 - r)]
            have h4 : (1 + r) ^ 2 ≤ 4 := by nlinarith [hhi_le_two, hhi_pos]
            have h2 : (1 + r) ^ 2 - u ^ 2 ≤ 4 := by linarith [h4, sq_nonneg u]
            calc ((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)
                ≤ ((1 + r) ^ 2 - u ^ 2) * u ^ 2 := mul_le_mul_of_nonneg_left h1 (by linarith)
              _ ≤ 4 * u ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
          · have hneg : (1 + r) ^ 2 - u ^ 2 ≤ 0 := by linarith
            have hpos : (0 : ℝ) ≤ u ^ 2 - (1 - r) ^ 2 := by
              have hs : (1 - r) ^ 2 ≤ (1 + r) ^ 2 := by
                have h4 : (1 + r) ^ 2 = (1 - r) ^ 2 + 4 * r := by ring
                linarith [hr_pos.le, h4]
              linarith [hc, hs]
            have hle : ((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg hneg hpos
            have h9 : (0 : ℝ) ≤ 4 * u ^ 2 := by positivity
            linarith [hle, h9]
        have hsqrtle : Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) ≤ 2 * |u| := by
          calc Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2))
              ≤ Real.sqrt (4 * u ^ 2) := Real.sqrt_le_sqrt hP2
            _ = 2 * |u| := by
                rw [show (4 : ℝ) * u ^ 2 = 2 ^ 2 * u ^ 2 by norm_num,
                  Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num),
                  Real.sqrt_sq_eq_abs]
        rw [abs_div, abs_mul, abs_mul, abs_of_pos hrho_pos,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
          abs_of_nonneg (Real.sqrt_nonneg _)]
        have hstep : (1 / Real.pi) *
              Real.sqrt (((1 + r) ^ 2 - u ^ 2) * (u ^ 2 - (1 - r) ^ 2)) / (rho * |u|)
            ≤ (1 / Real.pi) * (2 * |u|) / (rho * |u|) := by
          gcongr
        have hval : (1 / Real.pi) * (2 * |u|) / (rho * |u|) = 2 / (Real.pi * rho) := by
          have h1 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
          have h2 : rho * |u| ≠ 0 := ne_of_gt (by positivity)
          field_simp
        linarith [hstep, hval]
    have hIntCore : ∀ a b : ℝ, a ≤ b → IntervalIntegrable (fun u : ℝ =>
        (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u))
        volume a b := by
      intro a b hab
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      have hconst : IntegrableOn (fun _ : ℝ => 2 / (Real.pi * rho)) (Set.Icc a b) volume :=
        ContinuousOn.integrableOn_compact isCompact_Icc continuous_const.continuousOn
      refine MeasureTheory.Integrable.mono hconst hcore.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => ?_)
      have hMpos : (0 : ℝ) ≤ 2 / (Real.pi * rho) := by positivity
      have h1 : ‖(2 : ℝ) / (Real.pi * rho)‖ = 2 / (Real.pi * rho) := by
        rw [Real.norm_eq_abs]
        exact abs_of_pos (by positivity)
      rw [h1]
      rw [Real.norm_eq_abs]
      exact hCoreBound u
    have hs4 : Real.sqrt (r / 4) = Real.sqrt r / 2 := by
      rw [show r / 4 = r * (1 / 4) by ring, Real.sqrt_mul hr_pos.le]
      rw [show Real.sqrt ((1 : ℝ) / 4) = 1 / 2 by
        rw [show ((1 : ℝ) / 4) = (1 / 2) ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)]
      ring
    have hcRho_le : Real.sqrt (Real.sqrt rhoMinus) / (8 * Real.pi)
        ≤ (1 / (2 * Real.pi)) * ((1 / 2) * Real.sqrt (((1 + r) - (1 - r)) / 8)) := by
      rw [show (1 + r) - (1 - r) = 2 * r by ring]
      rw [show 2 * r / 8 = r / 4 by ring]
      rw [hs4]
      have hsr : Real.sqrt (Real.sqrt rhoMinus) ≤ Real.sqrt r :=
        Real.sqrt_le_sqrt hsr_le_r
      have hR : (1 / (2 * Real.pi)) * ((1 / 2) * (Real.sqrt r / 2))
          = Real.sqrt r / (8 * Real.pi) := by
        have hpne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
        field_simp
        norm_num
      rw [hR]
      have hinv : (0 : ℝ) ≤ (8 * Real.pi)⁻¹ := by positivity
      have h := mul_le_mul_of_nonneg_right hsr hinv
      simpa [div_eq_mul_inv] using h
    have htpow : 0 ≤ t ^ ((3 : ℝ) / 2) := Real.rpow_nonneg ht.le _
    have hgen : ∀ p q : ℝ, 1 - r ≤ p → q ≤ 1 + r → q = p + t →
        Real.sqrt (Real.sqrt rhoMinus) / (8 * Real.pi) * t ^ ((3 : ℝ) / 2)
          ≤ ∫ u in p..q, rootedMPDensity rho u := by
      intro p q hp hq hpq
      have hpqle : p ≤ q := by rw [hpq]; linarith
      have hCint : IntervalIntegrable (fun u : ℝ =>
          (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u))
          volume p q := hIntCore p q hpqle
      have hmono : (1 / (2 * Real.pi)) * ∫ u in p..q, Real.sqrt (((1 + r) - u) * (u - (1 - r)))
          ≤ ∫ u in p..q,
              (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u) := by
        have h := intervalIntegral.integral_mono_on hpqle
          ((hIntG p q hpqle).const_mul (1 / (2 * Real.pi))) hCint
          (fun u hu => by
            obtain ⟨hu1, hu2⟩ := hu
            have h1 : 1 - r ≤ u := le_trans hp hu1
            have h2 : u ≤ 1 + r := le_trans hu2 hq
            have hd := hdens u h1 h2
            rw [rootedMPDensity,
              if_pos (show mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho from
                ⟨by linarith [hmm, h1], by linarith [hpm, h2]⟩), mul_one] at hd
            rw [hpm, hmm] at hd ⊢
            exact hd)
        rwa [intervalIntegral.integral_const_mul] at h
      have hEqCore : ∫ u in p..q, rootedMPDensity rho u
          = ∫ u in p..q,
              (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u ∈ Set.Icc p q := by
          rwa [Set.uIcc_of_le hpqle] at hu
        obtain ⟨hu1, hu2⟩ := hu'
        have h1 : 1 - r ≤ u := le_trans hp hu1
        have h2 : u ≤ 1 + r := le_trans hu2 hq
        rw [rootedMPDensity,
          if_pos (show mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho from
            ⟨by linarith [hmm, h1], by linarith [hpm, h2]⟩), mul_one, hpm, hmm]
      have hgeomapp : (1 / 2) * Real.sqrt (((1 + r) - (1 - r)) / 8) * t ^ ((3 : ℝ) / 2)
          ≤ ∫ u in p..q, Real.sqrt (((1 + r) - u) * (u - (1 - r))) := by
        have hg := hgeom p (p - (1 - r)) ((1 + r) - p) t ((1 + r) - (1 - r))
          (by linarith) (by linarith [hpq, hq]) (by ring) ht ht_quarter
        have hEq : ∫ u in p..(p + t),
              Real.sqrt ((((1 + r) - p) - (u - p)) * ((p - (1 - r)) + (u - p)))
            = ∫ u in p..(p + t), Real.sqrt (((1 + r) - u) * (u - (1 - r))) := by
          apply intervalIntegral.integral_congr
          intro u hu
          congr 1
          ring
        rw [hEq] at hg
        rw [hpq]
        exact hg
      calc Real.sqrt (Real.sqrt rhoMinus) / (8 * Real.pi) * t ^ ((3 : ℝ) / 2)
          ≤ ((1 / (2 * Real.pi)) * ((1 / 2) * Real.sqrt (((1 + r) - (1 - r)) / 8)))
              * t ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_right hcRho_le htpow
        _ = (1 / (2 * Real.pi))
              * ((1 / 2) * Real.sqrt (((1 + r) - (1 - r)) / 8) * t ^ ((3 : ℝ) / 2)) :=
            mul_assoc _ _ _
        _ ≤ (1 / (2 * Real.pi))
              * ∫ u in p..q, Real.sqrt (((1 + r) - u) * (u - (1 - r))) :=
            mul_le_mul_of_nonneg_left hgeomapp (by positivity)
        _ ≤ ∫ u in p..q,
              (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u) :=
            hmono
        _ = ∫ u in p..q, rootedMPDensity rho u := hEqCore.symm
    constructor
    · intro hxt
      have hq : x + t ≤ 1 + r := hxt
      exact hgen x (x + t) hxlo' hq rfl
    · intro hxt
      have hxt' : 1 - r ≤ x - t := by linarith [hmm, hxt]
      exact hgen (x - t) x hxt' hxhi' (by ring)
  /- @proof-region region.target-node.session.507dc21fad6d83e3 end -/

end Statlib.Imported

