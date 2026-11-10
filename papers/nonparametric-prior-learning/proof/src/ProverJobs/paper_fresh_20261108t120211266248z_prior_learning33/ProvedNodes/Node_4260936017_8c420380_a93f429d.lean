import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_218839130_1c45a586_5d053e6a

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_4260936017_8c420380 : ∀ (U : Type*) [MeasurableSpace U] (P : Measure U) [IsProbabilityMeasure P]
    (rho : ℕ → U → ℝ≥0∞) (s : U → ℝ) (sn : ℕ → U → ℝ) (E : U → ℝ)
    (hrho_meas : ∀ n : ℕ, Measurable (rho n))
    (hs_meas : AEMeasurable (fun u : U => Real.exp (-(s u))) P)
    (hsn_meas : ∀ n : ℕ,
      AEMeasurable (fun u : U => Real.exp (-(sn n u))) (P.withDensity (rho n)))
    (hE_nonneg : ∀ u : U, 0 ≤ E u)
    (hE_meas : AEMeasurable E P)
    (hE_int : Integrable E P)
    (hE_meas_n : ∀ n : ℕ, AEMeasurable E (P.withDensity (rho n)))
    (hE_int_n : ∀ n : ℕ, Integrable E (P.withDensity (rho n)))
    (hs_maj : ∀ᵐ u ∂P, Real.exp (-(s u)) ≤ E u)
    (hsn_maj : ∀ n : ℕ, ∀ᵐ u ∂(P.withDensity (rho n)),
      Real.exp (-(sn n u)) ≤ E u ∧ Real.exp (-(s u)) ≤ E u)
    (hsq_lt_top : (∫⁻ u : U, ENNReal.ofReal ((Real.exp (-(s u))) ^ 2) ∂P) < ⊤)
    (hrho_conv : Tendsto
      (fun n : ℕ => ∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P)
      Filter.atTop (𝓝 0))
    (hconv_int : ∀ n : ℕ,
      Integrable (fun u : U => |sn n u - s u| * E u) (P.withDensity (rho n)))
    (hconv : Tendsto
      (fun n : ℕ => ∫ u : U, |sn n u - s u| * E u ∂(P.withDensity (rho n)))
      Filter.atTop (𝓝 0)),
    Tendsto (fun n : ℕ => ∫ u : U, Real.exp (-(sn n u)) ∂(P.withDensity (rho n)))
      Filter.atTop (𝓝 (∫ u : U, Real.exp (-(s u)) ∂P)) := by
  /- @proof-region region.target-node.session.556e2f8ad6fe6392 begin -/
  intro U _ P _ rho s sn E hrho_meas hs_meas hsn_meas hE_nonneg hE_meas hE_int hE_meas_n hE_int_n
    hmaj hmaj_n hsq_lt_top hrho_conv hconv_int hconv
  have hnorm_exp : ∀ t : ℝ, ‖Real.exp (-t)‖ = Real.exp (-t) := by
    intro t
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-t))]
  have hae_f : ∀ n : ℕ, AEMeasurable (fun u : U => Real.exp (-(s u))) (P.withDensity (rho n)) :=
    fun n => hs_meas.mono_ac (withDensity_absolutelyContinuous P (rho n))
  have hf_int : Integrable (fun u : U => Real.exp (-(s u))) P :=
    hE_int.mono' hs_meas.aestronglyMeasurable (by
      filter_upwards [hmaj] with u hu
      rw [hnorm_exp]
      exact hu)
  have hfn_int : ∀ n : ℕ, Integrable (fun u : U => Real.exp (-(sn n u))) (P.withDensity (rho n)) := by
    intro n
    exact (hE_int_n n).mono' (hsn_meas n).aestronglyMeasurable (by
      filter_upwards [hmaj_n n] with u hu
      rw [hnorm_exp]
      exact hu.1)
  have hf_int_n : ∀ n : ℕ, Integrable (fun u : U => Real.exp (-(s u))) (P.withDensity (rho n)) := by
    intro n
    exact (hE_int_n n).mono' (hae_f n).aestronglyMeasurable (by
      filter_upwards [hmaj_n n] with u hu
      rw [hnorm_exp]
      exact hu.2)
  have hlt_top : ∀ n : ℕ, ∀ᵐ u ∂P, rho n u < ⊤ := by
    intro n
    exact statopia_math_node_218839130_1c45a586 (U := U) (P := P) (rho := rho n)
      (g := fun u : U => Real.exp (-(s u))) (hrho := hrho_meas n) (hg := hs_meas)
      (hg_int := hf_int_n n) (hg_pos := fun u => Real.exp_pos _)
  have hcm : ∀ n : ℕ, (∫ u : U, Real.exp (-(s u)) ∂(P.withDensity (rho n)))
      = ∫ u : U, Real.exp (-(s u)) * (rho n u).toReal ∂P := by
    intro n
    rw [integral_withDensity_eq_integral_toReal_smul (μ := P) (f := rho n) (hrho_meas n)
      (hlt_top n)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    simp [smul_eq_mul, mul_comm]
  have hmv : ∀ x y : ℝ,
      |Real.exp (-y) - Real.exp (-x)| ≤ |y - x| * max (Real.exp (-y)) (Real.exp (-x)) := by
    have key : ∀ a b : ℝ, a ≤ b → Real.exp (-a) - Real.exp (-b) ≤ (b - a) * Real.exp (-a) := by
      intro a b hab
      have hfac : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hle : 1 - Real.exp (-(b - a)) ≤ b - a := by
        have h := Real.add_one_le_exp (-(b - a))
        linarith
      calc Real.exp (-a) - Real.exp (-b)
          = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
            rw [hfac]
            ring
        _ ≤ Real.exp (-a) * (b - a) := by
            apply mul_le_mul_of_nonneg_left hle (le_of_lt (Real.exp_pos _))
        _ = (b - a) * Real.exp (-a) := by ring
    intro x y
    rcases le_total x y with hxy | hxy
    · have hyx : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
      rw [max_eq_right hyx, abs_of_nonpos (by linarith : Real.exp (-y) - Real.exp (-x) ≤ 0),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
      linarith [key x y hxy]
    · have hyx : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
      rw [max_eq_left hyx, abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.exp (-y) - Real.exp (-x)),
        abs_of_nonpos (by linarith : y - x ≤ 0)]
      linarith [key y x hxy]
  have hterm1 : Tendsto
      (fun n : ℕ => ∫ u : U, |Real.exp (-(sn n u)) - Real.exp (-(s u))| ∂(P.withDensity (rho n)))
      atTop (𝓝 0) := by
    have hptw : ∀ n : ℕ, ∀ᵐ u ∂(P.withDensity (rho n)),
        |Real.exp (-(sn n u)) - Real.exp (-(s u))| ≤ |sn n u - s u| * E u := by
      intro n
      filter_upwards [hmaj_n n] with u hu
      have h2 : max (Real.exp (-(sn n u))) (Real.exp (-(s u))) ≤ E u := max_le hu.1 hu.2
      calc |Real.exp (-(sn n u)) - Real.exp (-(s u))|
          ≤ |sn n u - s u| * max (Real.exp (-(sn n u))) (Real.exp (-(s u))) := hmv (s u) (sn n u)
        _ ≤ |sn n u - s u| * E u := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have hasm : ∀ n : ℕ, AEStronglyMeasurable
        (fun u : U => |Real.exp (-(sn n u)) - Real.exp (-(s u))|) (P.withDensity (rho n)) := by
      intro n
      have h := ((hsn_meas n).sub (hae_f n)).norm
      simpa only [Real.norm_eq_abs] using h.aestronglyMeasurable
    have hint_abs : ∀ n : ℕ, Integrable
        (fun u : U => |Real.exp (-(sn n u)) - Real.exp (-(s u))|) (P.withDensity (rho n)) := by
      intro n
      refine (hconv_int n).mono' (hasm n) ?_
      filter_upwards [hptw n] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      exact hu
    have hle : ∀ n : ℕ,
        (∫ u : U, |Real.exp (-(sn n u)) - Real.exp (-(s u))| ∂(P.withDensity (rho n)))
          ≤ ∫ u : U, |sn n u - s u| * E u ∂(P.withDensity (rho n)) := by
      intro n
      exact MeasureTheory.integral_mono_ae (hint_abs n) (hconv_int n) (hptw n)
    have hnonneg : ∀ n : ℕ,
        (0:ℝ) ≤ ∫ u : U, |Real.exp (-(sn n u)) - Real.exp (-(s u))| ∂(P.withDensity (rho n)) := by
      intro n
      rw [← Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
        (μ := P.withDensity (rho n))
        (f := fun u : U => |Real.exp (-(sn n u)) - Real.exp (-(s u))|)
        (Filter.Eventually.of_forall fun u => abs_nonneg _) (hint_abs n)]
      exact ENNReal.toReal_nonneg
    exact squeeze_zero hnonneg hle hconv
  have hterm2 : Tendsto
      (fun n : ℕ => ‖∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P‖) atTop (𝓝 0) := by
    have hf_asm : AEStronglyMeasurable (fun u : U => Real.exp (-(s u))) P :=
      hs_meas.aestronglyMeasurable
    have hfsq_int : Integrable (fun u : U => (Real.exp (-(s u))) ^ 2) P := by
      refine ⟨?_, ?_⟩
      · simpa only [pow_two] using hf_asm.mul hf_asm
      · have hnorm : (fun u : U => ‖(Real.exp (-(s u))) ^ 2‖ₑ)
            = fun u : U => ENNReal.ofReal ((Real.exp (-(s u))) ^ 2) := by
          funext u
          rw [Real.enorm_eq_ofReal_abs, abs_sq]
        change (∫⁻ u : U, ‖(Real.exp (-(s u))) ^ 2‖ₑ ∂P) < ⊤
        rw [hnorm]
        exact hsq_lt_top
    have hf_memLp : MemLp (fun u : U => Real.exp (-(s u))) 2 P :=
      (MeasureTheory.memLp_two_iff_integrable_sq hf_asm).mpr hfsq_int
    have hk_asm : ∀ n : ℕ, AEStronglyMeasurable (fun u : U => (rho n u).toReal - 1) P := by
      intro n
      have hm : Measurable (fun u : U => (rho n u).toReal - 1) :=
        ((hrho_meas n).ennreal_toReal).sub measurable_const
      exact hm.aestronglyMeasurable
    have hk_sq_asm : ∀ n : ℕ,
        AEStronglyMeasurable (fun u : U => ((rho n u).toReal - 1) ^ 2) P := by
      intro n
      simpa only [pow_two] using (hk_asm n).mul (hk_asm n)
    have hA_lt : ∀ᶠ n : ℕ in atTop,
        (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P) < ⊤ :=
      hrho_conv.eventually (isOpen_Iio.mem_nhds (by simp))
    have hint_sq : ∀ᶠ n : ℕ in atTop,
        Integrable (fun u : U => ((rho n u).toReal - 1) ^ 2) P := by
      filter_upwards [hA_lt] with n hn
      refine ⟨hk_sq_asm n, ?_⟩
      have hnorm : (fun u : U => ‖((rho n u).toReal - 1) ^ 2‖ₑ)
          = fun u : U => ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) := by
        funext u
        rw [Real.enorm_eq_ofReal_abs, abs_sq]
      change (∫⁻ u : U, ‖((rho n u).toReal - 1) ^ 2‖ₑ ∂P) < ⊤
      rw [hnorm]
      exact hn
    have hsq_eq_body : ∀ n : ℕ, (∫ u : U, (|(rho n u).toReal - 1|) ^ 2 ∂P)
        = ∫ u : U, ((rho n u).toReal - 1) ^ 2 ∂P := by
      intro n
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      exact sq_abs _
    have hholder : ∀ᶠ n : ℕ in atTop,
        ‖∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P‖
          ≤ Real.sqrt (∫ u : U, (Real.exp (-(s u))) ^ 2 ∂P)
            * Real.sqrt (∫ u : U, (|(rho n u).toReal - 1|) ^ 2 ∂P) := by
      filter_upwards [hint_sq] with n hn
      have hk_abs_asm : AEStronglyMeasurable (fun u : U => |(rho n u).toReal - 1|) P := by
        simpa only [Real.norm_eq_abs] using (hk_asm n).norm
      have hk_abs_sq_int : Integrable (fun u : U => (|(rho n u).toReal - 1|) ^ 2) P := by
        simpa only [sq_abs] using hn
      have hk_abs_memLp : MemLp (fun u : U => |(rho n u).toReal - 1|) 2 P :=
        (MeasureTheory.memLp_two_iff_integrable_sq hk_abs_asm).mpr hk_abs_sq_int
      have h2 : ENNReal.ofReal 2 = 2 := by norm_num
      have hf_memLp' : MemLp (fun u : U => Real.exp (-(s u))) (ENNReal.ofReal 2) P := by
        rw [h2]
        exact hf_memLp
      have hk_abs_memLp' : MemLp (fun u : U => |(rho n u).toReal - 1|) (ENNReal.ofReal 2) P := by
        rw [h2]
        exact hk_abs_memLp
      have hholder' := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
        (p := 2) (q := 2) Real.HolderConjugate.two_two
        (f := fun u : U => Real.exp (-(s u)))
        (g := fun u : U => |(rho n u).toReal - 1|)
        (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
        (Filter.Eventually.of_forall fun u => abs_nonneg _)
        hf_memLp' hk_abs_memLp'
      calc ‖∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P‖
          ≤ ∫ u : U, ‖Real.exp (-(s u)) * ((rho n u).toReal - 1)‖ ∂P :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ = ∫ u : U, Real.exp (-(s u)) * |(rho n u).toReal - 1| ∂P := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with u
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ (∫ u : U, (Real.exp (-(s u))) ^ 2 ∂P) ^ (1 / 2)
              * (∫ u : U, (|(rho n u).toReal - 1|) ^ 2 ∂P) ^ (1 / 2) := hholder'
        _ = Real.sqrt (∫ u : U, (Real.exp (-(s u))) ^ 2 ∂P)
              * Real.sqrt (∫ u : U, (|(rho n u).toReal - 1|) ^ 2 ∂P) := by
            simp [Real.sqrt_eq_rpow]
    have hbase_lt : Tendsto (fun n : ℕ =>
        (∫⁻ u : U, ENNReal.ofReal (((rho n u).toReal - 1) ^ 2) ∂P).toReal) atTop (𝓝 0) := by
      have hcont : ContinuousAt (fun x : ℝ≥0∞ => x.toReal) 0 :=
        ENNReal.continuousAt_toReal (by simp)
      simpa using hcont.tendsto.comp hrho_conv
    have hbase : Tendsto (fun n : ℕ => ∫ u : U, ((rho n u).toReal - 1) ^ 2 ∂P) atTop (𝓝 0) := by
      refine Filter.Tendsto.congr' ?_ hbase_lt
      filter_upwards [hint_sq] with n hn
      exact (Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
        (Filter.Eventually.of_forall fun u => sq_nonneg ((rho n u).toReal - 1)) hn).symm
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (∫ u : U, (|(rho n u).toReal - 1|) ^ 2 ∂P))
        atTop (𝓝 0) := by
      refine Filter.Tendsto.congr' ?_ (by
        simpa using (Real.continuous_sqrt.tendsto 0).comp hbase)
      filter_upwards with n
      show Real.sqrt (∫ u : U, ((rho n u).toReal - 1) ^ 2 ∂P)
        = Real.sqrt (∫ u : U, (|(rho n u).toReal - 1|) ^ 2 ∂P)
      simp only [hsq_eq_body n]
    set c : ℝ := Real.sqrt (∫ u : U, (Real.exp (-(s u))) ^ 2 ∂P) with hc
    have hc0 : (0:ℝ) ≤ c := by
      rw [hc]
      exact Real.sqrt_nonneg _
    have hd : Tendsto (fun n : ℕ => c * Real.sqrt (∫ u : U, (|(rho n u).toReal - 1|) ^ 2 ∂P))
        atTop (𝓝 0) := by
      simpa using hsqrt.const_mul c
    have hG : Tendsto (fun n : ℕ =>
        if ‖∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P‖
          ≤ c * Real.sqrt (∫ u : U, (|(rho n u).toReal - 1|) ^ 2 ∂P)
        then ‖∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P‖ else 0) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => ?_) (fun n => ?_) hd
      · split_ifs with h
        · exact norm_nonneg _
        · exact le_refl 0
      · split_ifs with h
        · exact h
        · exact mul_nonneg hc0 (Real.sqrt_nonneg _)
    have hG_eq : (fun n : ℕ =>
        if ‖∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P‖
          ≤ c * Real.sqrt (∫ u : U, (|(rho n u).toReal - 1|) ^ 2 ∂P)
        then ‖∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P‖ else 0)
        =ᶠ[atTop] fun n : ℕ =>
          ‖∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P‖ := by
      filter_upwards [hholder] with n hn
      rw [if_pos (by rw [hc]; exact hn)]
    exact Filter.Tendsto.congr' hG_eq hG
  have hbound : ∀ n : ℕ,
      ‖(∫ u : U, Real.exp (-(sn n u)) ∂(P.withDensity (rho n))) - (∫ u : U, Real.exp (-(s u)) ∂P)‖
        ≤ (∫ u : U, |Real.exp (-(sn n u)) - Real.exp (-(s u))| ∂(P.withDensity (rho n)))
          + ‖∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P‖ := by
    have hint_fk : ∀ n : ℕ, Integrable (fun u : U => Real.exp (-(s u)) * (rho n u).toReal) P := by
      intro n
      have hae_of : AEMeasurable (fun u : U => ENNReal.ofReal (Real.exp (-(s u)))) P :=
        ENNReal.measurable_ofReal.comp_aemeasurable hs_meas
      have hmeas_fk : AEStronglyMeasurable (fun u : U => Real.exp (-(s u)) * (rho n u).toReal) P := by
        have hm : Measurable (fun u : U => (rho n u).toReal) := (hrho_meas n).ennreal_toReal
        exact (hs_meas.mul hm.aemeasurable).aestronglyMeasurable
      have hle_lint : (∫⁻ u : U, ENNReal.ofReal (Real.exp (-(s u)) * (rho n u).toReal) ∂P)
          ≤ ∫⁻ u : U, rho n u * ENNReal.ofReal (Real.exp (-(s u))) ∂P := by
        apply MeasureTheory.lintegral_mono
        intro u
        calc ENNReal.ofReal (Real.exp (-(s u)) * (rho n u).toReal)
            = ENNReal.ofReal (Real.exp (-(s u))) * ENNReal.ofReal ((rho n u).toReal) :=
              ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))
          _ = ENNReal.ofReal ((rho n u).toReal) * ENNReal.ofReal (Real.exp (-(s u))) := by
              rw [mul_comm]
          _ ≤ rho n u * ENNReal.ofReal (Real.exp (-(s u))) := by
              apply mul_le_mul_of_nonneg_right ENNReal.ofReal_toReal_le
              exact zero_le _
      have h1 : (∫⁻ u : U, rho n u * ENNReal.ofReal (Real.exp (-(s u))) ∂P) < ⊤ := by
        have heq : (∫⁻ u : U, rho n u * ENNReal.ofReal (Real.exp (-(s u))) ∂P)
            = ∫⁻ u : U, ENNReal.ofReal (Real.exp (-(s u))) ∂(P.withDensity (rho n)) :=
          (MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ (μ := P) (f := rho n)
            (hrho_meas n).aemeasurable
            (g := fun u : U => ENNReal.ofReal (Real.exp (-(s u)))) hae_of).symm
        rw [heq]
        exact (hf_int_n n).lintegral_lt_top
      exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas_fk
        (Filter.Eventually.of_forall fun u =>
          mul_nonneg (le_of_lt (Real.exp_pos _)) ENNReal.toReal_nonneg)).mp
        (ne_of_lt (lt_of_le_of_lt hle_lint h1))
    intro n
    have hfk : Integrable (fun u : U => Real.exp (-(s u)) * (rho n u).toReal) P := hint_fk n
    have hsub1 : (∫ u : U, (Real.exp (-(sn n u)) - Real.exp (-(s u))) ∂(P.withDensity (rho n)))
        = (∫ u : U, Real.exp (-(sn n u)) ∂(P.withDensity (rho n)))
          - (∫ u : U, Real.exp (-(s u)) ∂(P.withDensity (rho n))) :=
      MeasureTheory.integral_sub (hfn_int n) (hf_int_n n)
    have hsub2 : (∫ u : U, (Real.exp (-(s u)) * (rho n u).toReal - Real.exp (-(s u))) ∂P)
        = (∫ u : U, Real.exp (-(s u)) * (rho n u).toReal ∂P)
          - (∫ u : U, Real.exp (-(s u)) ∂P) :=
      MeasureTheory.integral_sub hfk hf_int
    have hcongr : (∫ u : U, (Real.exp (-(s u)) * (rho n u).toReal - Real.exp (-(s u))) ∂P)
        = ∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      ring
    have hnorm1 : ‖∫ u : U, (Real.exp (-(sn n u)) - Real.exp (-(s u))) ∂(P.withDensity (rho n))‖
        ≤ ∫ u : U, |Real.exp (-(sn n u)) - Real.exp (-(s u))| ∂(P.withDensity (rho n)) := by
      simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
        (fun u : U => Real.exp (-(sn n u)) - Real.exp (-(s u)))
    have hsplit : (∫ u : U, Real.exp (-(sn n u)) ∂(P.withDensity (rho n)))
        - (∫ u : U, Real.exp (-(s u)) ∂P)
        = ((∫ u : U, Real.exp (-(sn n u)) ∂(P.withDensity (rho n)))
            - (∫ u : U, Real.exp (-(s u)) ∂(P.withDensity (rho n))))
          + ((∫ u : U, Real.exp (-(s u)) ∂(P.withDensity (rho n))) - (∫ u : U, Real.exp (-(s u)) ∂P)) := by
      ring
    rw [hsplit, ← hsub1, hcm n, ← hsub2, hcongr]
    exact le_trans (norm_add_le _ _) (add_le_add hnorm1 le_rfl)
  have hdiff : Tendsto
      (fun n : ℕ =>
        (∫ u : U, Real.exp (-(sn n u)) ∂(P.withDensity (rho n))) - (∫ u : U, Real.exp (-(s u)) ∂P))
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun n : ℕ =>
        (∫ u : U, |Real.exp (-(sn n u)) - Real.exp (-(s u))| ∂(P.withDensity (rho n)))
          + ‖∫ u : U, Real.exp (-(s u)) * ((rho n u).toReal - 1) ∂P‖) atTop (𝓝 0) := by
      have h := hterm1.add hterm2
      simpa using h
    have hnorm : Tendsto (fun n : ℕ =>
        ‖(∫ u : U, Real.exp (-(sn n u)) ∂(P.withDensity (rho n))) - (∫ u : U, Real.exp (-(s u)) ∂P)‖)
        atTop (𝓝 0) :=
      squeeze_zero (fun n => norm_nonneg _) hbound hsum
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hfinal := hdiff.add (tendsto_const_nhds (x := ∫ u : U, Real.exp (-(s u)) ∂P))
  simpa using hfinal
  /- @proof-region region.target-node.session.556e2f8ad6fe6392 end -/

end Statlib.Imported
end

