import Lean
import ProverJobs.job_paper_ebad183ded244602a77f3710a9957efa.Vocabulary
import ProverJobs.job_paper_ebad183ded244602a77f3710a9957efa.Base

namespace PaperProofTasks.job_paper_ebad183ded244602a77f3710a9957efa

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_ebad183ded244602a77f3710a9957efa.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_1375259586_446cfff9 : ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : ℝ) (hV : 0 < V) (X : Ω → ℝ)
    (hX_meas : Measurable X) (hX_int : Integrable X μ)
    (hX_mean : ∫ ω, X ω ∂μ = 0)
    (hmoment : ∀ r : ℕ, 2 ≤ r →
      ∫⁻ ω, ENNReal.ofReal (|X ω| ^ r) ∂μ
        ≤ ENNReal.ofReal ((r.factorial : ℝ) * V ^ r))
    (lam : ℝ) (hlam : |lam| ≤ 1 / (2 * V)),
    Integrable (fun ω => Real.exp (lam * X ω)) μ := by
  /- @proof-region region.target-node.session.014a10912a30dcb6 begin -/
  intro Ω _ μ _ V hV X hX_meas hX_int hX_mean hmoment lam hlam
  set q : ℝ := |lam| * V with hq_def
  have hq_nonneg : 0 ≤ q := by
    rw [hq_def]
    positivity
  have hq_le : q ≤ 1 / 2 := by
    rw [hq_def]
    calc |lam| * V ≤ (1 / (2 * V)) * V := mul_le_mul_of_nonneg_right hlam hV.le
      _ = 1 / 2 := by field_simp
  have hq_lt : q < 1 := by linarith
  set A : ℕ → ℝ := fun k => ∫ ω : Ω, |X ω| ^ k ∂μ with hA_def
  have hA0 : A 0 = 1 := by
    show ∫ ω : Ω, |X ω| ^ 0 ∂μ = 1
    simp
  have hA_int : ∀ k : ℕ, Integrable (fun ω : Ω => |X ω| ^ k) μ := by
    intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · simpa using (integrable_const (1 : ℝ))
      · simpa using hX_int.norm
    · have hm := hmoment k hk
      have hmeas : Measurable fun ω : Ω => |X ω| ^ k :=
        (continuous_pow k).measurable.comp hX_meas.abs
      refine ⟨hmeas.aestronglyMeasurable, ?_⟩
      exact (MeasureTheory.hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall (fun ω => by positivity))).mpr
        (lt_of_le_of_lt hm ENNReal.ofReal_lt_top)
  have hA_bound : ∀ k : ℕ, 2 ≤ k → A k ≤ (k.factorial : ℝ) * V ^ k := by
    intro k hk
    have hm := hmoment k hk
    have hnn : 0 ≤ᵐ[μ] fun ω : Ω => |X ω| ^ k := Filter.Eventually.of_forall (fun ω => by positivity)
    have hint := hA_int k
    have hEq : ENNReal.ofReal (A k) = ∫⁻ ω : Ω, ENNReal.ofReal (|X ω| ^ k) ∂μ :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
    have hle : ENNReal.ofReal (A k) ≤ ENNReal.ofReal ((k.factorial : ℝ) * V ^ k) := by
      rw [hEq]
      exact hm
    have hAnonneg : 0 ≤ A k := integral_nonneg (fun ω => by positivity)
    have hR : (0 : ℝ) ≤ (k.factorial : ℝ) * V ^ k := by positivity
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal hAnonneg, ENNReal.toReal_ofReal hR] at h2
  set K : ℝ := max 1 (A 1 / V) with hK_def
  have hK1 : 1 ≤ K := by
    rw [hK_def]
    exact le_max_left _ _
  have hA1_le : A 1 ≤ K * V := by
    have h1 : A 1 / V ≤ K := by
      rw [hK_def]
      exact le_max_right _ _
    have h2 : (A 1 / V) * V ≤ K * V := mul_le_mul_of_nonneg_right h1 hV.le
    have h3 : (A 1 / V) * V = A 1 := by field_simp
    linarith [h2, h3]
  set f : Ω → ℝ := fun ω => Real.exp (lam * X ω) with hf_def
  have hf_meas : Measurable f := by
    have h1 : Measurable fun ω : Ω => lam * X ω := measurable_const.mul hX_meas
    exact Real.measurable_exp.comp h1
  have hf_nn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)
  have hGsum : ∀ ω : Ω, HasSum (fun n : ℕ => (|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n)
      (Real.exp (|lam| * |X ω|)) := by
    intro ω
    have h0 : HasSum (fun n : ℕ => (|lam| * |X ω|) ^ n / (n.factorial : ℝ))
        (NormedSpace.exp (|lam| * |X ω|)) :=
      NormedSpace.expSeries_div_hasSum_exp (|lam| * |X ω|)
    have hcongr : (fun n : ℕ => (|lam| * |X ω|) ^ n / (n.factorial : ℝ))
        = (fun n : ℕ => (|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n) := by
      funext n
      rw [mul_pow, div_eq_mul_inv]
      ring
    rw [hcongr] at h0
    rw [Real.exp_eq_exp_ℝ]
    exact h0
  have hpoint : ∀ ω : Ω, ENNReal.ofReal (f ω) ≤
      ∑' n : ℕ, ENNReal.ofReal ((|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n) := by
    intro ω
    have hle : f ω ≤ ∑' n : ℕ, (|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n := by
      have h1 : lam * X ω ≤ |lam| * |X ω| := by
        calc lam * X ω ≤ |lam * X ω| := le_abs_self _
          _ = |lam| * |X ω| := abs_mul lam (X ω)
      have h2 : Real.exp (lam * X ω) ≤ Real.exp (|lam| * |X ω|) := Real.exp_le_exp.mpr h1
      rw [← (hGsum ω).tsum_eq] at h2
      exact h2
    calc ENNReal.ofReal (f ω)
        ≤ ENNReal.ofReal (∑' n : ℕ, (|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n) :=
            ENNReal.ofReal_le_ofReal hle
      _ = ∑' n : ℕ, ENNReal.ofReal ((|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n) :=
            ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hGsum ω).summable
  have hTs_meas : ∀ n : ℕ, AEMeasurable (fun ω : Ω =>
      ENNReal.ofReal ((|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n)) μ := by
    intro n
    have hpow : Measurable fun ω : Ω => |X ω| ^ n := (continuous_pow n).measurable.comp hX_meas.abs
    have hmul : Measurable fun ω : Ω => (|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n :=
      measurable_const.mul hpow
    exact (ENNReal.measurable_ofReal.comp hmul).aemeasurable
  have hmaj : ∫⁻ ω : Ω, ENNReal.ofReal (f ω) ∂μ ≤
      ∑' n : ℕ, ENNReal.ofReal ((|lam| ^ n / (n.factorial : ℝ)) * A n) := by
    calc ∫⁻ ω : Ω, ENNReal.ofReal (f ω) ∂μ
        ≤ ∫⁻ ω : Ω, ∑' n : ℕ, ENNReal.ofReal ((|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n) ∂μ :=
            lintegral_mono hpoint
      _ = ∑' n : ℕ, ∫⁻ ω : Ω, ENNReal.ofReal ((|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n) ∂μ :=
            MeasureTheory.lintegral_tsum hTs_meas
      _ = ∑' n : ℕ, ENNReal.ofReal ((|lam| ^ n / (n.factorial : ℝ)) * A n) := by
            apply tsum_congr
            intro n
            have hGn : Integrable (fun ω : Ω => (|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n) μ := by
              have h0 := (hA_int n).const_mul (|lam| ^ n / (n.factorial : ℝ))
              simpa only [mul_comm] using h0
            have hGnn : 0 ≤ᵐ[μ] fun ω : Ω => (|lam| ^ n / (n.factorial : ℝ)) * |X ω| ^ n :=
              Filter.Eventually.of_forall (fun ω => by positivity)
            rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGn hGnn]
            congr 1
            rw [MeasureTheory.integral_const_mul]
            -- goal closed by `integral_const_mul` (A n is definitionally the integral)
  have hD : ∀ n : ℕ, ENNReal.ofReal ((|lam| ^ n / (n.factorial : ℝ)) * A n) ≤
      ENNReal.ofReal (K * q ^ n) := by
    intro n
    apply ENNReal.ofReal_le_ofReal
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · have h1 : (|lam| ^ 0 / ((0 : ℕ).factorial : ℝ)) * A 0 = 1 := by simp [hA0]
        rw [h1, pow_zero, mul_one]
        exact hK1
      · have h1 : (|lam| ^ 1 / ((1 : ℕ).factorial : ℝ)) * A 1 = |lam| * A 1 := by simp
        rw [h1, pow_one]
        calc |lam| * A 1 ≤ |lam| * (K * V) := mul_le_mul_of_nonneg_left hA1_le (abs_nonneg lam)
          _ = K * q := by rw [hq_def]; ring
    · have hbound := hA_bound n hn
      have hcoef : 0 ≤ |lam| ^ n / (n.factorial : ℝ) := by positivity
      have h1 : (|lam| ^ n / (n.factorial : ℝ)) * A n
          ≤ (|lam| ^ n / (n.factorial : ℝ)) * ((n.factorial : ℝ) * V ^ n) :=
        mul_le_mul_of_nonneg_left hbound hcoef
      have h2 : (|lam| ^ n / (n.factorial : ℝ)) * ((n.factorial : ℝ) * V ^ n) = q ^ n := by
        rw [hq_def, mul_pow]
        field_simp
      have h3 : q ^ n ≤ K * q ^ n := le_mul_of_one_le_left (pow_nonneg hq_nonneg _) hK1
      linarith [h1, h2, h3]
  have hgeom : Summable fun n : ℕ => q ^ n := summable_geometric_of_lt_one hq_nonneg hq_lt
  have hgeomK : Summable fun n : ℕ => K * q ^ n := hgeom.mul_left K
  have hfin : ∫⁻ ω : Ω, ENNReal.ofReal (f ω) ∂μ < ⊤ := by
    calc ∫⁻ ω : Ω, ENNReal.ofReal (f ω) ∂μ
        ≤ ∑' n : ℕ, ENNReal.ofReal ((|lam| ^ n / (n.factorial : ℝ)) * A n) := hmaj
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (K * q ^ n) := ENNReal.tsum_le_tsum hD
      _ < ⊤ := Summable.tsum_ofReal_lt_top hgeomK
  exact ⟨hf_meas.aestronglyMeasurable, (MeasureTheory.hasFiniteIntegral_iff_ofReal hf_nn).mpr hfin⟩
  /- @proof-region region.target-node.session.014a10912a30dcb6 end -/

end Statlib.Imported

