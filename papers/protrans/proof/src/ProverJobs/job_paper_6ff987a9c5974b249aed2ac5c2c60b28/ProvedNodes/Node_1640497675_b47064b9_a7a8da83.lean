import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Statlib.StatFoundation.Vocabulary.OrliczNorm
import Lean
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Vocabulary
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Base

namespace PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28

open MeasureTheory ProbabilityTheory ENNReal
open scoped ENNReal Matrix
open Statlib.StatFoundation.Vocabulary
open _root_.PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported

open MeasureTheory ProbabilityTheory ENNReal
open scoped ENNReal Matrix
open Statlib.StatFoundation.Vocabulary
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
universe u

set_option autoImplicit false in
theorem statopia_math_node_1640497675_b47064b9 : ∀ (L : ℝ) (hL : 0 < L),
    ∃ V : ℝ, 0 < V ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X Y : Ω → ℝ),
        Measurable X → Measurable Y →
        subgaussianOrliczNorm X μ ≤ ENNReal.ofReal L →
        subgaussianOrliczNorm Y μ ≤ ENNReal.ofReal L →
        Integrable (fun ω => X ω * Y ω) μ ∧
        (∀ (r : ℕ), 1 ≤ r →
          Integrable (fun ω => |X ω * Y ω - ∫ ω', X ω' * Y ω' ∂μ| ^ r) μ) ∧
        (∀ (r : ℕ), 1 ≤ r →
          ∫⁻ ω, ENNReal.ofReal (|X ω * Y ω - ∫ ω', X ω' * Y ω' ∂μ| ^ r) ∂μ
            ≤ ENNReal.ofReal ((Nat.factorial r : ℝ) * V ^ r)) := by
  /- @proof-region region.target-node.session.972db98383460269 begin -/
  intro L hL
  set M : ℝ := L + 1 with hMdef
  have hMp : 0 < M := by rw [hMdef]; linarith

  refine ⟨16 * M ^ 2, by positivity, ?_⟩

  intro Ω _ μ _ X Y hX hY hOrX hOrY
  have orlicz_exp : ∀ (Z : Ω → ℝ), Measurable Z →
      subgaussianOrliczNorm Z μ ≤ ENNReal.ofReal L →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2)) ∂μ ≤ ENNReal.ofReal 2 := by
    intro Z hZ hZor
    have hsinf : sInf {t : ℝ≥0∞ | 0 < t ∧ ∫⁻ ω, ENNReal.ofReal (Real.exp ((|Z ω| / t.toReal) ^ (2:ℝ)) - 1) ∂μ ≤ 1}
        ≤ ENNReal.ofReal L := by
      simpa only [subgaussianOrliczNorm, orliczNorm, psiOrlicz] using hZor
    have hne : {t : ℝ≥0∞ | 0 < t ∧ ∫⁻ ω, ENNReal.ofReal (Real.exp ((|Z ω| / t.toReal) ^ (2:ℝ)) - 1) ∂μ ≤ 1}.Nonempty := by
      refine ⟨⊤, ?_⟩
      simp
    have hbdd : BddBelow {t : ℝ≥0∞ | 0 < t ∧ ∫⁻ ω, ENNReal.ofReal (Real.exp ((|Z ω| / t.toReal) ^ (2:ℝ)) - 1) ∂μ ≤ 1} :=
      ⟨0, fun t _ => zero_le t⟩
    have hLltM : ENNReal.ofReal L < ENNReal.ofReal M := by
      have hLM : L < M := by rw [hMdef]; linarith
      exact (ENNReal.ofReal_lt_ofReal_iff hMp).mpr hLM
    have hMlt : sInf {t : ℝ≥0∞ | 0 < t ∧ ∫⁻ ω, ENNReal.ofReal (Real.exp ((|Z ω| / t.toReal) ^ (2:ℝ)) - 1) ∂μ ≤ 1}
        < ENNReal.ofReal M := lt_of_le_of_lt hsinf hLltM
    obtain ⟨t, htT, htt⟩ := (csInf_lt_iff hbdd hne).mp hMlt
    obtain ⟨htpos, htint⟩ := htT
    have htne : t ≠ ⊤ := ne_top_of_lt (lt_trans htt ENNReal.ofReal_lt_top)
    have htp : 0 < t.toReal := ENNReal.toReal_pos htpos.ne' htne
    have httM : t.toReal ≤ M := by
      have h := ENNReal.toReal_mono (ne_of_lt ENNReal.ofReal_lt_top) (le_of_lt htt)
      rwa [ENNReal.toReal_ofReal hMp.le] at h
    have hmodM : ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2) - 1) ∂μ ≤ 1 := by
      refine le_trans (lintegral_mono (fun ω => ?_)) htint
      apply ENNReal.ofReal_le_ofReal
      have h1 : |Z ω| / M ≤ |Z ω| / t.toReal := by
        rw [le_div_iff₀ htp, div_mul_eq_mul_div, div_le_iff₀ hMp]
        exact mul_le_mul_of_nonneg_left httM (abs_nonneg _)
      have h2 : Z ω ^ 2 / M ^ 2 ≤ (|Z ω| / t.toReal) ^ (2:ℝ) := by
        have hsq : (|Z ω| / M) * (|Z ω| / M) ≤ (|Z ω| / t.toReal) * (|Z ω| / t.toReal) :=
          mul_le_mul h1 h1 (by positivity) (by positivity)
        calc Z ω ^ 2 / M ^ 2 = (|Z ω| / M) ^ 2 := by rw [div_pow, sq_abs]
          _ = (|Z ω| / M) * (|Z ω| / M) := pow_two _
          _ ≤ (|Z ω| / t.toReal) * (|Z ω| / t.toReal) := hsq
          _ = (|Z ω| / t.toReal) ^ 2 := (pow_two _).symm
          _ = (|Z ω| / t.toReal) ^ (2:ℝ) := by rw [Real.rpow_two]
      have h3 := Real.exp_le_exp.mpr h2
      linarith
    have hpt : ∀ ω : Ω, ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2))
        = ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2) - 1) + 1 := by
      intro ω
      have hge : (0:ℝ) ≤ Real.exp (Z ω ^ 2 / M ^ 2) - 1 := by
        have h1 : (1:ℝ) ≤ Real.exp (Z ω ^ 2 / M ^ 2) := by
          have h2 := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Z ω ^ 2 / M ^ 2 by positivity)
          simpa using h2
        linarith
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hge (by norm_num)]
      congr 1
      ring
    have harg : Measurable fun ω : Ω => Z ω ^ 2 / M ^ 2 := by
      have h1 : Measurable fun ω : Ω => Z ω ^ 2 := by
        simpa [pow_two] using hZ.mul hZ
      exact h1.div_const _
    have hmeasSub : Measurable fun ω : Ω => ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2) - 1) :=
      ((Real.continuous_exp.measurable.comp harg).sub measurable_const).ennreal_ofReal
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2)) ∂μ
        = ∫⁻ ω, (ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2) - 1) + 1) ∂μ := by
          apply lintegral_congr
          intro ω
          exact hpt ω
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2) - 1) ∂μ) + ∫⁻ ω, (1:ℝ≥0∞) ∂μ := by
          rw [MeasureTheory.lintegral_add_left hmeasSub]
      _ ≤ ENNReal.ofReal 2 := by
          rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
          have h2 : (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2) - 1) ∂μ) + 1 ≤ 1 + 1 := by
            simpa using add_le_add_right hmodM 1
          refine le_trans h2 ?_
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  have single : ∀ (Z : Ω → ℝ), Measurable Z → ∀ (n : ℕ), 1 ≤ n →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2)) ∂μ ≤ ENNReal.ofReal 2) →
      ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * n)) ∂μ
        ≤ ENNReal.ofReal (2 * (Nat.factorial n : ℝ) * M ^ (2 * n)) := by
    intro Z hZ n hn hExp
    have hpt : ∀ ω : Ω, |Z ω| ^ (2 * n) ≤ (Nat.factorial n : ℝ) * M ^ (2 * n) * Real.exp (Z ω ^ 2 / M ^ 2) := by
      intro ω
      have hs : 0 ≤ Z ω ^ 2 / M ^ 2 := by positivity
      have hfac : (0:ℝ) < (Nat.factorial n : ℝ) := by positivity
      have h1 : (Z ω ^ 2 / M ^ 2) ^ n ≤ (Nat.factorial n : ℝ) * Real.exp (Z ω ^ 2 / M ^ 2) := by
        have h := Real.pow_div_factorial_le_exp (Z ω ^ 2 / M ^ 2) hs n
        rw [div_le_iff₀ hfac] at h
        linarith
      have hbase : Z ω ^ 2 = (Z ω ^ 2 / M ^ 2) * M ^ 2 :=
        (div_mul_cancel₀ _ (pow_ne_zero 2 hMp.ne')).symm
      have e1 : |Z ω| ^ (2 * n) = (Z ω ^ 2) ^ n := by rw [pow_mul, sq_abs]
      have e2 : (Z ω ^ 2) ^ n = ((Z ω ^ 2 / M ^ 2) * M ^ 2) ^ n :=
        congrArg (fun t : ℝ => t ^ n) hbase
      have hMn : (M ^ 2) ^ n = M ^ (2 * n) := by rw [pow_mul]
      have e3 : ((Z ω ^ 2 / M ^ 2) * M ^ 2) ^ n = (Z ω ^ 2 / M ^ 2) ^ n * M ^ (2 * n) := by
        rw [mul_pow, hMn]
      calc |Z ω| ^ (2 * n) = (Z ω ^ 2 / M ^ 2) ^ n * M ^ (2 * n) := by rw [e1, e2, e3]
        _ ≤ ((Nat.factorial n : ℝ) * Real.exp (Z ω ^ 2 / M ^ 2)) * M ^ (2 * n) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (Nat.factorial n : ℝ) * M ^ (2 * n) * Real.exp (Z ω ^ 2 / M ^ 2) := by ring
    have hargS : Measurable fun ω : Ω => Z ω ^ 2 / M ^ 2 := by
      have h1 : Measurable fun ω : Ω => Z ω ^ 2 := by
        simpa [pow_two] using hZ.mul hZ
      exact h1.div_const _
    have hmeasS : Measurable fun ω : Ω => ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2)) :=
      (Real.continuous_exp.measurable.comp hargS).ennreal_ofReal
    calc ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ (2 * n)) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal ((Nat.factorial n : ℝ) * M ^ (2 * n) * Real.exp (Z ω ^ 2 / M ^ 2)) ∂μ :=
          lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hpt ω))
      _ = ENNReal.ofReal ((Nat.factorial n : ℝ) * M ^ (2 * n)) * ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω ^ 2 / M ^ 2)) ∂μ := by
          rw [← MeasureTheory.lintegral_const_mul (ENNReal.ofReal ((Nat.factorial n : ℝ) * M ^ (2 * n))) hmeasS]
          apply lintegral_congr
          intro ω
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((Nat.factorial n : ℝ) * M ^ (2 * n)) * ENNReal.ofReal 2 :=
          mul_le_mul_left' hExp _
      _ = ENNReal.ofReal (2 * (Nat.factorial n : ℝ) * M ^ (2 * n)) := by
          rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ (Nat.factorial n : ℝ) * M ^ (2 * n) by positivity)]
          congr 1
          ring
  have hexpX : ∫⁻ ω, ENNReal.ofReal (Real.exp (X ω ^ 2 / M ^ 2)) ∂μ ≤ ENNReal.ofReal 2 :=
    orlicz_exp X hX hOrX
  have hexpY : ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω ^ 2 / M ^ 2)) ∂μ ≤ ENNReal.ofReal 2 :=
    orlicz_exp Y hY hOrY
  have hmeasXY : Measurable fun ω : Ω => X ω * Y ω := hX.mul hY
  have hprod : ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ω, ENNReal.ofReal (|X ω * Y ω| ^ n) ∂μ
        ≤ ENNReal.ofReal ((Nat.factorial n : ℝ) * (4 * M ^ 2) ^ n) := by
    intro n hn
    have hfunX : (fun ω : Ω => ENNReal.ofReal (|X ω| ^ (2 * n))) = (fun ω : Ω => ENNReal.ofReal ((X ω ^ 2) ^ n)) := by
      funext ω
      rw [pow_mul, sq_abs]
    have hfunY : (fun ω : Ω => ENNReal.ofReal (|Y ω| ^ (2 * n))) = (fun ω : Ω => ENNReal.ofReal ((Y ω ^ 2) ^ n)) := by
      funext ω
      rw [pow_mul, sq_abs]
    have hcontG : Continuous fun t : ℝ => (t ^ 2) ^ n := (continuous_id.pow 2).pow n
    have hXm : Measurable fun ω : Ω => ENNReal.ofReal ((X ω ^ 2) ^ n) :=
      (hcontG.measurable.comp hX).ennreal_ofReal
    have hYm : Measurable fun ω : Ω => ENNReal.ofReal ((Y ω ^ 2) ^ n) :=
      (hcontG.measurable.comp hY).ennreal_ofReal
    have hXb : ∫⁻ ω, ENNReal.ofReal ((X ω ^ 2) ^ n) ∂μ
        ≤ ENNReal.ofReal (2 * (Nat.factorial n : ℝ) * M ^ (2 * n)) := by
      have h := single X hX n hn hexpX
      rwa [hfunX] at h
    have hYb : ∫⁻ ω, ENNReal.ofReal ((Y ω ^ 2) ^ n) ∂μ
        ≤ ENNReal.ofReal (2 * (Nat.factorial n : ℝ) * M ^ (2 * n)) := by
      have h := single Y hY n hn hexpY
      rwa [hfunY] at h
    have hpt : ∀ ω : Ω, ENNReal.ofReal (|X ω * Y ω| ^ n)
        ≤ ENNReal.ofReal ((X ω ^ 2) ^ n) + ENNReal.ofReal ((Y ω ^ 2) ^ n) := by
      intro ω
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hx : |X ω| ^ (2 * n) = (X ω ^ 2) ^ n := by rw [pow_mul, sq_abs]
      have hy : |Y ω| ^ (2 * n) = (Y ω ^ 2) ^ n := by rw [pow_mul, sq_abs]
      have hxy : |X ω * Y ω| ^ n = |X ω| ^ n * |Y ω| ^ n := by rw [abs_mul, mul_pow]
      have hsq1 : (|X ω| ^ n) ^ 2 = |X ω| ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
      have hsq2 : (|Y ω| ^ n) ^ 2 = |Y ω| ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
      rw [hxy, ← hx, ← hy, ← hsq1, ← hsq2]
      have h1 : (0:ℝ) ≤ |X ω| ^ n := by positivity
      have h2 : (0:ℝ) ≤ |Y ω| ^ n := by positivity
      nlinarith [sq_nonneg (|X ω| ^ n - |Y ω| ^ n), h1, h2]
    calc ∫⁻ ω, ENNReal.ofReal (|X ω * Y ω| ^ n) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal ((X ω ^ 2) ^ n) + ENNReal.ofReal ((Y ω ^ 2) ^ n)) ∂μ :=
          lintegral_mono hpt
      _ = (∫⁻ ω, ENNReal.ofReal ((X ω ^ 2) ^ n) ∂μ) + (∫⁻ ω, ENNReal.ofReal ((Y ω ^ 2) ^ n) ∂μ) := by
          rw [MeasureTheory.lintegral_add_left hXm]
      _ ≤ ENNReal.ofReal (2 * (Nat.factorial n : ℝ) * M ^ (2 * n))
            + ENNReal.ofReal (2 * (Nat.factorial n : ℝ) * M ^ (2 * n)) :=
          add_le_add hXb hYb
      _ = ENNReal.ofReal (4 * (Nat.factorial n : ℝ) * M ^ (2 * n)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
      _ ≤ ENNReal.ofReal ((Nat.factorial n : ℝ) * (4 * M ^ 2) ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have h4n : (4:ℝ) ≤ 4 ^ n := by
            have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hn
            simpa using h
          have hMn2 : (4 * M ^ 2) ^ n = 4 ^ n * M ^ (2 * n) := by
            rw [mul_pow, ← pow_mul]
          rw [hMn2]
          have h1 : (4:ℝ) * ((Nat.factorial n : ℝ) * M ^ (2 * n))
              ≤ 4 ^ n * ((Nat.factorial n : ℝ) * M ^ (2 * n)) :=
            mul_le_mul_of_nonneg_right h4n (by positivity)
          calc 4 * (Nat.factorial n : ℝ) * M ^ (2 * n)
              = 4 * ((Nat.factorial n : ℝ) * M ^ (2 * n)) := by ring
            _ ≤ 4 ^ n * ((Nat.factorial n : ℝ) * M ^ (2 * n)) := h1
            _ = (Nat.factorial n : ℝ) * (4 ^ n * M ^ (2 * n)) := by ring
  have hprod1 : ∫⁻ ω, ENNReal.ofReal (|X ω * Y ω|) ∂μ ≠ ⊤ := by
    have h := hprod 1 le_rfl
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne h
  have habsXY : Measurable fun ω : Ω => |X ω * Y ω| := by
    have h1 : Measurable fun ω : Ω => (X ω * Y ω) ^ 2 := by
      simpa [pow_two] using hmeasXY.mul hmeasXY
    have h2 : Measurable fun ω : Ω => Real.sqrt ((X ω * Y ω) ^ 2) :=
      Real.continuous_sqrt.measurable.comp h1
    simpa [Real.sqrt_sq_eq_abs] using h2
  have hIabs : Integrable (fun ω : Ω => |X ω * Y ω|) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable habsXY.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => abs_nonneg _))).mp hprod1
  have hI1 : Integrable (fun ω : Ω => X ω * Y ω) μ := by
    have hnorm : Integrable (fun ω : Ω => ‖X ω * Y ω‖) μ := by
      simpa [Real.norm_eq_abs] using hIabs
    exact (MeasureTheory.integrable_norm_iff hmeasXY.aestronglyMeasurable).mp hnorm
  set c : ℝ := ∫ ω, X ω * Y ω ∂μ with hcdef
  have hc : |c| ≤ 4 * M ^ 2 := by
    have h1 : |c| ≤ ∫ ω, |X ω * Y ω| ∂μ := by
      rw [hcdef]
      exact MeasureTheory.abs_integral_le_integral_abs
    have h2 : ∫ ω, |X ω * Y ω| ∂μ ≤ 4 * M ^ 2 := by
      have hp := hprod 1 le_rfl
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at hp
      rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
        (Filter.Eventually.of_forall (fun ω => abs_nonneg _)) hIabs]
      calc (∫⁻ ω, ENNReal.ofReal (|X ω * Y ω|) ∂μ).toReal ≤ (ENNReal.ofReal (4 * M ^ 2)).toReal :=
            ENNReal.toReal_mono (ne_of_lt ENNReal.ofReal_lt_top) hp
        _ = 4 * M ^ 2 := ENNReal.toReal_ofReal (by positivity)
    linarith
  have hmain : ∀ r : ℕ, 1 ≤ r →
      ∫⁻ ω, ENNReal.ofReal (|X ω * Y ω - c| ^ r) ∂μ
        ≤ ENNReal.ofReal ((Nat.factorial r : ℝ) * (16 * M ^ 2) ^ r) := by
    intro r hr
    have habspow : Measurable fun ω : Ω => |X ω * Y ω| ^ r := by
      have hcont : Continuous fun t : ℝ => |t| ^ r := by
        have h1 : Continuous fun t : ℝ => Real.sqrt (t ^ 2) :=
          Real.continuous_sqrt.comp (continuous_id.pow 2)
        simpa [Real.sqrt_sq_eq_abs] using h1.pow r
      have h2 : Measurable fun ω : Ω => (fun t : ℝ => |t| ^ r) (X ω * Y ω) :=
        hcont.measurable.comp hmeasXY
      simpa using h2
    have hpt : ∀ ω : Ω, ENNReal.ofReal (|X ω * Y ω - c| ^ r)
        ≤ ENNReal.ofReal (2 ^ r) * (ENNReal.ofReal (|X ω * Y ω| ^ r) + ENNReal.ofReal (|c| ^ r)) := by
      intro ω
      have hsub : |X ω * Y ω - c| ≤ |X ω * Y ω| + |c| := by
        have h := abs_add_le (X ω * Y ω) (-c)
        simpa using h
      have hmax : |X ω * Y ω - c| ≤ 2 * max |X ω * Y ω| |c| := by
        nlinarith [hsub, le_max_left (|X ω * Y ω|) |c|, le_max_right (|X ω * Y ω|) |c|]
      have h2 : |X ω * Y ω - c| ^ r ≤ (2 * max |X ω * Y ω| |c|) ^ r :=
        pow_le_pow_left₀ (abs_nonneg _) hmax r
      have h3 : max |X ω * Y ω| |c| ^ r ≤ |X ω * Y ω| ^ r + |c| ^ r := by
        rcases le_total (|X ω * Y ω|) (|c|) with h | h
        · rw [max_eq_right h]
          exact le_add_of_nonneg_left (pow_nonneg (abs_nonneg _) r)
        · rw [max_eq_left h]
          exact le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) r)
      have h4 : |X ω * Y ω - c| ^ r ≤ 2 ^ r * (|X ω * Y ω| ^ r + |c| ^ r) := by
        calc |X ω * Y ω - c| ^ r ≤ (2 * max |X ω * Y ω| |c|) ^ r := h2
          _ = 2 ^ r * max |X ω * Y ω| |c| ^ r := by rw [mul_pow]
          _ ≤ 2 ^ r * (|X ω * Y ω| ^ r + |c| ^ r) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
      calc ENNReal.ofReal (|X ω * Y ω - c| ^ r)
          ≤ ENNReal.ofReal (2 ^ r * (|X ω * Y ω| ^ r + |c| ^ r)) := ENNReal.ofReal_le_ofReal h4
        _ = ENNReal.ofReal (2 ^ r) * ENNReal.ofReal (|X ω * Y ω| ^ r + |c| ^ r) := by
            rw [ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal (2 ^ r) * (ENNReal.ofReal (|X ω * Y ω| ^ r) + ENNReal.ofReal (|c| ^ r)) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    have hsum : Measurable fun ω : Ω => ENNReal.ofReal (|X ω * Y ω| ^ r) + ENNReal.ofReal (|c| ^ r) := by
      have h1 : Measurable fun ω : Ω => ENNReal.ofReal (|X ω * Y ω| ^ r) := habspow.ennreal_ofReal
      have h2 : Measurable fun ω : Ω => ENNReal.ofReal (|c| ^ r) := measurable_const
      simpa using h1.add h2
    calc ∫⁻ ω, ENNReal.ofReal (|X ω * Y ω - c| ^ r) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ r) * (ENNReal.ofReal (|X ω * Y ω| ^ r) + ENNReal.ofReal (|c| ^ r)) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 ^ r) * ∫⁻ ω, (ENNReal.ofReal (|X ω * Y ω| ^ r) + ENNReal.ofReal (|c| ^ r)) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (2 ^ r)) hsum]
      _ = ENNReal.ofReal (2 ^ r) * ((∫⁻ ω, ENNReal.ofReal (|X ω * Y ω| ^ r) ∂μ) + ∫⁻ ω, ENNReal.ofReal (|c| ^ r) ∂μ) := by
          rw [MeasureTheory.lintegral_add_left habspow.ennreal_ofReal]
      _ = ENNReal.ofReal (2 ^ r) * ((∫⁻ ω, ENNReal.ofReal (|X ω * Y ω| ^ r) ∂μ) + ENNReal.ofReal (|c| ^ r)) := by
          rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (2 ^ r) * (ENNReal.ofReal ((Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r) + ENNReal.ofReal ((4 * M ^ 2) ^ r)) := by
          apply mul_le_mul_left'
          exact add_le_add (hprod r hr) (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg c) hc r))
      _ ≤ ENNReal.ofReal ((Nat.factorial r : ℝ) * (16 * M ^ 2) ^ r) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hA : (0:ℝ) ≤ (4 * M ^ 2) ^ r := by positivity
          have hfac1 : (1:ℝ) ≤ (Nat.factorial r : ℝ) := by
            have hnat : (1:ℕ) ≤ Nat.factorial r := by
              have h0 : 0 < Nat.factorial r := Nat.factorial_pos r
              omega
            exact_mod_cast hnat
          have h2r : (2:ℝ) ^ (r + 1) ≤ 4 ^ r := by
            rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
            exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
          have h16 : (16 * M ^ 2) ^ r = 4 ^ r * (4 * M ^ 2) ^ r := by
            rw [show (16:ℝ) * M ^ 2 = 4 * (4 * M ^ 2) by ring, mul_pow]
          rw [h16]
          have h1 : 2 ^ r * ((Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r + (4 * M ^ 2) ^ r)
              ≤ 2 ^ r * (2 * (Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hfac1, hA]
          have h2 : 2 ^ r * (2 * (Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r)
              = 2 ^ (r + 1) * (Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r := by
            rw [pow_succ]
            ring
          have h3 : 2 ^ (r + 1) * (Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r
              ≤ 4 ^ r * (Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r := by
            apply mul_le_mul_of_nonneg_right _ hA
            exact mul_le_mul_of_nonneg_right h2r (by positivity)
          calc 2 ^ r * ((Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r + (4 * M ^ 2) ^ r)
              ≤ 2 ^ r * (2 * (Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r) := h1
            _ = 2 ^ (r + 1) * (Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r := h2
            _ ≤ 4 ^ r * (Nat.factorial r : ℝ) * (4 * M ^ 2) ^ r := h3
            _ = (Nat.factorial r : ℝ) * (4 ^ r * (4 * M ^ 2) ^ r) := by ring
  refine ⟨hI1, ?_, ?_⟩
  · intro r hr
    have hne : ∫⁻ ω, ENNReal.ofReal (|X ω * Y ω - c| ^ r) ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne (hmain r hr)
    have hcont : Continuous fun t : ℝ => |t| ^ r := by
      have h1 : Continuous fun t : ℝ => Real.sqrt (t ^ 2) :=
        Real.continuous_sqrt.comp (continuous_id.pow 2)
      simpa [Real.sqrt_sq_eq_abs] using h1.pow r
    have hmeas2 : Measurable fun ω : Ω => |X ω * Y ω - c| ^ r := by
      have h2 : Measurable fun ω : Ω => (fun t : ℝ => |t| ^ r) (X ω * Y ω - c) :=
        hcont.measurable.comp (hmeasXY.sub measurable_const)
      simpa using h2
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas2.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg _) r))).mp hne
  · intro r hr
    exact hmain r hr
  /- @proof-region region.target-node.session.972db98383460269 end -/

end Statlib.Imported

