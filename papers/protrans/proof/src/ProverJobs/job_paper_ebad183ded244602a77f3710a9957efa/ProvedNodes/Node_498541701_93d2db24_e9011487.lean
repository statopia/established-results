import Lean
import ProverJobs.job_paper_ebad183ded244602a77f3710a9957efa.Vocabulary
import ProverJobs.job_paper_ebad183ded244602a77f3710a9957efa.Base
import ProverJobs.job_paper_ebad183ded244602a77f3710a9957efa.ProvedNodes.Node_1375259586_446cfff9_56faac71

namespace PaperProofTasks.job_paper_ebad183ded244602a77f3710a9957efa
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_ebad183ded244602a77f3710a9957efa.Statlib.Imported
universe u

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_498541701_93d2db24 : ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : ℝ) (hV : 0 < V) (X : Ω → ℝ)
    (hX_meas : Measurable X) (hX_int : Integrable X μ)
    (hX_mean : ∫ ω, X ω ∂μ = 0)
    (hmoment : ∀ r : ℕ, 2 ≤ r →
      ∫⁻ ω, ENNReal.ofReal (|X ω| ^ r) ∂μ
        ≤ ENNReal.ofReal ((r.factorial : ℝ) * V ^ r)),
    ∀ lam : ℝ, |lam| ≤ 1 / (2 * V) →
      Integrable (fun ω => Real.exp (lam * X ω)) μ ∧
        ∫ ω, Real.exp (lam * X ω) ∂μ ≤ Real.exp (2 * lam ^ 2 * V ^ 2) := by
  /- @proof-region region.target-node.session.51a71b8e9f47d1c4 begin -/
  intro Ω _ μ _ V hV X hX_meas hX_int hX_mean hmoment lam hlam
  have hVne : V ≠ 0 := ne_of_gt hV
  have hq_le : |lam| * V ≤ 1 / 2 := by
    have h1 : (1 / (2 * V)) * V = 1 / 2 := by field_simp
    have h2 := mul_le_mul_of_nonneg_right hlam (le_of_lt hV)
    rwa [h1] at h2
  have hq_nonneg : 0 ≤ |lam| * V := by positivity
  have hq_lt_one : |lam| * V < 1 := by linarith
  have hmom_real : ∀ r : ℕ, 2 ≤ r →
      Integrable (fun ω => |X ω| ^ r) μ ∧ ∫ ω, |X ω| ^ r ∂μ ≤ (r.factorial : ℝ) * V ^ r := by
    intro r hr
    have hnonneg : 0 ≤ᶠ[ae μ] (fun ω => |X ω| ^ r) := Filter.Eventually.of_forall (fun ω => by positivity)
    have hfin : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ r) ∂μ < ⊤ :=
      lt_of_le_of_lt (hmoment r hr) ENNReal.ofReal_lt_top
    have hint : Integrable (fun ω => |X ω| ^ r) μ := by
      refine ⟨?_, (MeasureTheory.hasFiniteIntegral_iff_ofReal hnonneg).2 hfin⟩
      have hm : Measurable fun ω => |X ω| ^ r := by
        have h := hX_meas
        measurability
      exact hm.aestronglyMeasurable
    refine ⟨hint, ?_⟩
    have h1 : ENNReal.ofReal (∫ ω, |X ω| ^ r ∂μ) = ∫⁻ ω, ENNReal.ofReal (|X ω| ^ r) ∂μ :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg
    have h2 : ENNReal.ofReal (∫ ω, |X ω| ^ r ∂μ) ≤ ENNReal.ofReal ((r.factorial : ℝ) * V ^ r) :=
      h1.trans_le (hmoment r hr)
    have h3 : (0 : ℝ) ≤ (r.factorial : ℝ) * V ^ r := by positivity
    have h4 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ ∫ ω, |X ω| ^ r ∂μ),
      ENNReal.toReal_ofReal h3] at h4
  have habs_int : ∀ n : ℕ, Integrable (fun ω => |X ω| ^ n) μ := by
    intro n
    match n with
    | 0 => simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
    | 1 => simpa [Real.norm_eq_abs] using hX_int.norm
    | (k + 2) => exact (hmom_real (k + 2) (by omega)).1
  have hXn_int : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) μ := by
    intro n
    match n with
    | 0 => simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
    | 1 => simpa using hX_int
    | (k + 2) =>
        have haesm : AEStronglyMeasurable (fun ω => X ω ^ (k + 2)) μ := by
          have hm : Measurable fun ω => X ω ^ (k + 2) := by
            have h := hX_meas
            measurability
          exact hm.aestronglyMeasurable
        exact Integrable.mono' (habs_int (k + 2)) haesm
          (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_pow]))
  set c : ℕ → ℝ := fun n => lam ^ n / (n.factorial : ℝ) with hc
  have hG_int : ∀ n : ℕ, Integrable (fun ω => c n * X ω ^ n) μ :=
    fun n => (hXn_int n).const_mul (c n)
  have hGN : ∀ n : ℕ,
      ∫ ω, ‖c n * X ω ^ n‖ ∂μ = |lam| ^ n / (n.factorial : ℝ) * ∫ ω, |X ω| ^ n ∂μ := by
    intro n
    have hfac : |((n.factorial : ℝ))| = (n.factorial : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg n.factorial)
    have hpt : (fun ω => ‖c n * X ω ^ n‖)
        = fun ω => (|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n := by
      funext ω
      simp only [hc, norm_mul, norm_div, norm_pow, Real.norm_eq_abs, hfac]
    rw [hpt, integral_const_mul]
  have hN_bound : ∀ n : ℕ, 2 ≤ n → ∫ ω, ‖c n * X ω ^ n‖ ∂μ ≤ (|lam| * V) ^ n := by
    intro n hn
    have hfacne : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [hGN n]
    calc |lam| ^ n / (n.factorial : ℝ) * ∫ ω, |X ω| ^ n ∂μ
        ≤ |lam| ^ n / (n.factorial : ℝ) * ((n.factorial : ℝ) * V ^ n) :=
          mul_le_mul_of_nonneg_left (hmom_real n hn).2 (by positivity)
      _ = (|lam| * V) ^ n := by
          rw [mul_pow]
          field_simp
  have hgeom : Summable fun k : ℕ => (|lam| * V) ^ k :=
    summable_geometric_of_lt_one hq_nonneg hq_lt_one
  have hgeom2 : Summable fun k : ℕ => (|lam| * V) ^ (k + 2) :=
    (summable_nat_add_iff 2).mpr hgeom
  have hsum2 : Summable fun k : ℕ => ∫ ω, ‖c (k + 2) * X ω ^ (k + 2)‖ ∂μ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg (fun ω => norm_nonneg _))
      (fun k => hN_bound (k + 2) (by omega)) hgeom2
  have hsumN : Summable fun n : ℕ => ∫ ω, ‖c n * X ω ^ n‖ ∂μ :=
    (summable_nat_add_iff 2).mp hsum2
  have hterm := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun n ω => c n * X ω ^ n) hG_int hsumN
  have hexp_series : ∀ y : ℝ, Real.exp y = ∑' n : ℕ, y ^ n / (n.factorial : ℝ) := by
    intro y
    rw [Real.exp_eq_exp_ℝ]
    exact congrFun NormedSpace.exp_eq_tsum_div y
  have hpt : ∀ ω : Ω, ∑' n : ℕ, c n * X ω ^ n = Real.exp (lam * X ω) := by
    intro ω
    rw [hexp_series (lam * X ω)]
    refine tsum_congr (fun n => ?_)
    simp only [hc, div_eq_mul_inv, mul_pow]
    ring
  have hterm' : ∑' n : ℕ, ∫ ω, c n * X ω ^ n ∂μ = ∫ ω, ∑' n : ℕ, c n * X ω ^ n ∂μ := by
    simpa using MeasureTheory.integral_tsum_of_summable_integral_norm
      (F := fun n ω => c n * X ω ^ n) hG_int hsumN
  have hIntEq : ∫ ω, Real.exp (lam * X ω) ∂μ = ∑' n : ℕ, ∫ ω, c n * X ω ^ n ∂μ := by
    rw [hterm']
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => (hpt ω).symm))
  have hHasSum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (F := fun n ω => c n * X ω ^ n) hG_int hsumN
  have hsum_a : Summable fun n : ℕ => ∫ ω, c n * X ω ^ n ∂μ := hHasSum.summable
  have h0c : c 0 = 1 := by simp [hc]
  have h1c : ∫ ω, c 1 * X ω ∂μ = 0 := by
    have hfun : (fun ω => c 1 * X ω) = fun ω => lam * X ω := by
      funext ω
      simp [hc]
    rw [hfun, integral_const_mul, hX_mean, mul_zero]
  have hsplit : ∑' n : ℕ, (∫ ω, c n * X ω ^ n ∂μ)
      = 1 + ∑' k : ℕ, (∫ ω, c (k + 2) * X ω ^ (k + 2) ∂μ) := by
    have h := hsum_a.sum_add_tsum_nat_add 2
    have h2 : (Finset.range 2).sum (fun n => ∫ ω, c n * X ω ^ n ∂μ) = 1 + 0 := by
      simp [Finset.sum_range_succ, h0c, h1c]
    rw [h2] at h
    linarith [h]
  have ha_bound : ∀ n : ℕ, 2 ≤ n → (∫ ω, c n * X ω ^ n ∂μ) ≤ (|lam| * V) ^ n := by
    intro n hn
    calc ∫ ω, c n * X ω ^ n ∂μ ≤ |∫ ω, c n * X ω ^ n ∂μ| := le_abs_self _
      _ = ‖∫ ω, c n * X ω ^ n ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ ω, ‖c n * X ω ^ n‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ (|lam| * V) ^ n := hN_bound n hn
  have hsum_a2 : Summable fun k : ℕ => ∫ ω, c (k + 2) * X ω ^ (k + 2) ∂μ :=
    (summable_nat_add_iff 2).mpr hsum_a
  have htail_le : ∑' k : ℕ, (∫ ω, c (k + 2) * X ω ^ (k + 2) ∂μ)
      ≤ ∑' k : ℕ, (|lam| * V) ^ (k + 2) :=
    hsum_a2.tsum_le_tsum (fun k => ha_bound (k + 2) (by omega)) hgeom2
  have hgeom_val : ∑' k : ℕ, (|lam| * V) ^ (k + 2) ≤ 2 * (|lam| * V) ^ 2 := by
    have hfac2 : (fun k : ℕ => (|lam| * V) ^ (k + 2))
        = fun k => (|lam| * V) ^ 2 * (|lam| * V) ^ k := by
      funext k
      rw [pow_add]
      ring
    have hHas : HasSum (fun k : ℕ => (|lam| * V) ^ 2 * (|lam| * V) ^ k)
        ((|lam| * V) ^ 2 * (1 - |lam| * V)⁻¹) := by
      have hh := hgeom.hasSum.mul_left ((|lam| * V) ^ 2)
      rwa [tsum_geometric_of_lt_one hq_nonneg hq_lt_one] at hh
    rw [hfac2, hHas.tsum_eq]
    have hinv : (1 - |lam| * V)⁻¹ ≤ 2 := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 / 2 by norm_num)
        (show (1 : ℝ) / 2 ≤ 1 - |lam| * V by linarith)
      have h2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
      rw [h2] at h
      simpa [one_div] using h
    calc (|lam| * V) ^ 2 * (1 - |lam| * V)⁻¹ ≤ (|lam| * V) ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * (|lam| * V) ^ 2 := by ring
  have hq2 : (|lam| * V) ^ 2 = lam ^ 2 * V ^ 2 := by
    rw [mul_pow, sq_abs]
  constructor
  · exact statopia_math_node_1375259586_446cfff9 Ω μ V hV X hX_meas hX_int hX_mean hmoment lam hlam
  · rw [hIntEq, hsplit]
    have hstep : 1 + (∑' k : ℕ, (∫ ω, c (k + 2) * X ω ^ (k + 2) ∂μ))
        ≤ 1 + 2 * (|lam| * V) ^ 2 := by
      linarith [htail_le, hgeom_val]
    rw [hq2] at hstep
    refine hstep.trans ?_
    have h3 := Real.add_one_le_exp (2 * lam ^ 2 * V ^ 2)
    linarith
  /- @proof-region region.target-node.session.51a71b8e9f47d1c4 end -/

end Statlib.Imported

