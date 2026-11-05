import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_3721294497_2acf13ef : ∀ {H : Type*} [TopologicalSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
    (mu nu : ProbabilityMeasure H)
    (h : H → ℝ) (hh_meas : Measurable h)
    (C : ℝ) (hC : ∀ x : H, |h x| ≤ C),
    ∃ Theta : ℕ → H → ℝ,
      (∀ n : ℕ, Continuous (Theta n)) ∧
      (∀ n : ℕ, Bornology.IsBounded (Set.range (Theta n))) ∧
      Filter.Tendsto (fun n : ℕ => ∫ x, Theta n x ∂(nu : Measure H)) Filter.atTop
        (nhds (∫ x, h x ∂(nu : Measure H))) ∧
      Filter.Tendsto (fun n : ℕ => ∫ x, Real.exp (Theta n x) ∂(mu : Measure H)) Filter.atTop
        (nhds (∫ x, Real.exp (h x) ∂(mu : Measure H))) := by
  /- @proof-region region.target-node.session.ec37c215c28d4b9c begin -/
  intro H _ _ _ _ mu nu h hh_meas C hC
  classical
  set B : ℝ := max C 0 with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; exact le_max_right C 0
  have hhB : ∀ x : H, |h x| ≤ B := fun x => by
    rw [hBdef]; exact (hC x).trans (le_max_left C 0)
  set ρ : Measure H := (nu : Measure H) + (mu : Measure H) with hρdef
  haveI hρfin : IsFiniteMeasure ρ := by rw [hρdef]; infer_instance
  have hhm : AEStronglyMeasurable h ρ := hh_meas.aestronglyMeasurable
  have hMemLp : MemLp h 1 ρ := by
    refine MeasureTheory.memLp_of_bounded (a := -B) (b := B) ?_ hhm 1
    filter_upwards with x
    exact ⟨(abs_le.mp (hhB x)).1, (abs_le.mp (hhB x)).2⟩
  have hdense := BoundedContinuousFunction.toLp_denseRange (α := H) (E := ℝ) (μ := ρ)
    (p := 1) (𝕜 := ℝ) (by norm_num)
  have hex : ∀ n : ℕ, ∃ g : BoundedContinuousFunction H ℝ,
      dist (hMemLp.toLp) (BoundedContinuousFunction.toLp 1 ρ ℝ g) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, hy, hdist⟩ :=
      Metric.mem_closure_iff.mp (hdense (hMemLp.toLp)) (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, hdist⟩
  choose g hg using hex
  set Θ : ℕ → H → ℝ := fun n x => max (-B) (min ((g n) x) B) with hΘdef
  have hΘcont : ∀ n : ℕ, Continuous (Θ n) := by
    intro n
    have h1 : Continuous (fun x : H => (g n) x) := (g n).continuous
    have h2 : Continuous (fun x : H => max (-B) (min ((g n) x) B)) :=
      continuous_const.max (h1.min continuous_const)
    rw [hΘdef]
    exact h2
  have hΘbdd : ∀ n : ℕ, Bornology.IsBounded (Set.range (Θ n)) := by
    intro n
    have hsub : Set.range (Θ n) ⊆ Metric.closedBall (0 : ℝ) B := by
      rintro y ⟨x, rfl⟩
      rw [Metric.mem_closedBall]
      rw [hΘdef]
      simp only
      rw [Real.dist_eq, sub_zero]
      refine abs_le.mpr ⟨le_max_left _ _, max_le ?_ (min_le_right _ _)⟩
      linarith
    exact (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : ℝ) B)).subset hsub
  have hclamp : ∀ (m : ℕ) (x : H), |Θ m x - h x| ≤ |(g m) x - h x| := by
    intro m x
    have hx1 : -B ≤ h x := (abs_le.mp (hhB x)).1
    have hx2 : h x ≤ B := (abs_le.mp (hhB x)).2
    show |max (-B) (min ((g m) x) B) - h x| ≤ |(g m) x - h x|
    rcases le_total ((g m) x) B with h1 | h1
    · rcases le_total (-B) ((g m) x) with h2 | h2
      · have hval : max (-B) (min ((g m) x) B) = (g m) x := by
          rw [min_eq_left h1, max_eq_right h2]
        rw [hval]
      · have hval : max (-B) (min ((g m) x) B) = -B := by
          rw [min_eq_left h1, max_eq_left h2]
        rw [hval, abs_of_nonpos (by linarith : -B - h x ≤ 0),
          abs_of_nonpos (by linarith : (g m) x - h x ≤ 0)]
        linarith
    · have hval : max (-B) (min ((g m) x) B) = B := by
        rw [min_eq_right h1, max_eq_right (by linarith : -B ≤ B)]
      rw [hval, abs_of_nonneg (by linarith : 0 ≤ B - h x),
        abs_of_nonneg (by linarith : 0 ≤ (g m) x - h x)]
      linarith
  have hbridge : ∀ (F : H → ℝ), Integrable F ρ →
      ∫ x, ‖F x‖ ∂ρ = (eLpNorm F 1 ρ).toReal := by
    intro F hF
    have h1 : ENNReal.ofReal (∫ x, ‖F x‖ ∂ρ) = ∫⁻ x, ‖F x‖ₑ ∂ρ :=
      MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hF
    have h2 : eLpNorm F 1 ρ = ∫⁻ x, ‖F x‖ₑ ∂ρ := MeasureTheory.eLpNorm_one_eq_lintegral_enorm
    have h3 : 0 ≤ ∫ x, ‖F x‖ ∂ρ := integral_nonneg (fun x => norm_nonneg (F x))
    rw [h2, ← h1, ENNReal.toReal_ofReal h3]
  have hΘabs : ∀ (n : ℕ) (x : H), ‖Θ n x‖ ≤ B := by
    intro n x
    show ‖max (-B) (min ((g n) x) B)‖ ≤ B
    rw [Real.norm_eq_abs]
    refine abs_le.mpr ⟨le_max_left _ _, max_le ?_ (min_le_right _ _)⟩
    linarith
  have hIntNormAny : ∀ (m : Measure H), IsFiniteMeasure m →
      ∀ n : ℕ, Integrable (fun x : H => ‖Θ n x - h x‖) m := by
    intro m hmfin n
    haveI := hmfin
    have hb : ∀ᵐ x ∂m, (fun x : H => ‖Θ n x - h x‖) x ∈ Set.Icc (0 : ℝ) (2 * B) := by
      filter_upwards with x
      refine ⟨norm_nonneg _, ?_⟩
      have h2 : ‖h x‖ ≤ B := by rw [Real.norm_eq_abs]; exact hhB x
      calc ‖Θ n x - h x‖ ≤ ‖Θ n x‖ + ‖h x‖ := norm_sub_le _ _
        _ ≤ B + B := by linarith [hΘabs n x]
        _ = 2 * B := by ring
    have hm : AEStronglyMeasurable (fun x : H => ‖Θ n x - h x‖) m :=
      (((hΘcont n).measurable.aestronglyMeasurable).sub hh_meas.aestronglyMeasurable).norm
    exact MeasureTheory.memLp_one_iff_integrable.mp (MeasureTheory.memLp_of_bounded hb hm 1)
  have hIntNorm : ∀ n : ℕ, Integrable (fun x : H => ‖Θ n x - h x‖) ρ :=
    fun n => hIntNormAny ρ hρfin n
  have hkey : ∀ n : ℕ, ∫ x, ‖Θ n x - h x‖ ∂ρ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have haeh : (↑↑(hMemLp.toLp) : H → ℝ) =ᵐ[ρ] h := MeasureTheory.MemLp.coeFn_toLp hMemLp
    have haeg : (↑↑(BoundedContinuousFunction.toLp 1 ρ ℝ (g n)) : H → ℝ) =ᵐ[ρ] (fun x => (g n) x) :=
      BoundedContinuousFunction.coeFn_toLp 1 ρ ℝ (g n)
    have hsup : ∀ x : H, ‖(g n) x‖ ≤ ‖g n‖ := fun x =>
      BoundedContinuousFunction.norm_coe_le_norm (f := g n) x
    have hmemg : MemLp (fun x : H => h x - (g n) x) 1 ρ := by
      have hb : ∀ᵐ x ∂ρ, (fun x : H => h x - (g n) x) x ∈ Set.Icc (-(‖g n‖ + B)) (‖g n‖ + B) := by
        filter_upwards with x
        have h1 : ‖(g n) x‖ ≤ ‖g n‖ := hsup x
        have h2 : ‖h x‖ ≤ B := by rw [Real.norm_eq_abs]; exact hhB x
        have h3 : ‖h x - (g n) x‖ ≤ ‖g n‖ + B := by
          calc ‖h x - (g n) x‖ ≤ ‖h x‖ + ‖(g n) x‖ := norm_sub_le _ _
            _ ≤ ‖g n‖ + B := by linarith
        rw [Real.norm_eq_abs] at h3
        exact abs_le.mp h3
      have hm : AEStronglyMeasurable (fun x : H => h x - (g n) x) ρ :=
        hhm.sub ((g n).continuous.measurable.aestronglyMeasurable)
      exact MeasureTheory.memLp_of_bounded hb hm 1
    have hIntF : Integrable (fun x : H => h x - (g n) x) ρ :=
      MeasureTheory.memLp_one_iff_integrable.mp hmemg
    have hE : eLpNorm ((↑↑(hMemLp.toLp) : H → ℝ) - ↑↑(BoundedContinuousFunction.toLp 1 ρ ℝ (g n))) 1 ρ
        < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      have h := (edist_lt_ofReal (r := 1 / ((n : ℝ) + 1))).mpr (hg n)
      rwa [MeasureTheory.Lp.edist_def] at h
    have hL : ∫⁻ x, ‖h x - (g n) x‖ₑ ∂ρ < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm] at hE
      have hae : ((↑↑(hMemLp.toLp) : H → ℝ) - ↑↑(BoundedContinuousFunction.toLp 1 ρ ℝ (g n)))
          =ᵐ[ρ] (fun x => h x - (g n) x) := haeh.sub haeg
      have hcongr : (fun x => ‖((↑↑(hMemLp.toLp) : H → ℝ) - ↑↑(BoundedContinuousFunction.toLp 1 ρ ℝ (g n))) x‖ₑ)
          =ᵐ[ρ] (fun x => ‖h x - (g n) x‖ₑ) :=
        hae.mono fun x hx => by
          show ‖((↑↑(hMemLp.toLp) : H → ℝ) - ↑↑(BoundedContinuousFunction.toLp 1 ρ ℝ (g n))) x‖ₑ
            = ‖h x - (g n) x‖ₑ
          rw [show ((↑↑(hMemLp.toLp) : H → ℝ) - ↑↑(BoundedContinuousFunction.toLp 1 ρ ℝ (g n))) x
            = h x - (g n) x from hx]
      rwa [MeasureTheory.lintegral_congr_ae hcongr] at hE
    have hreal : ∫ x, ‖h x - (g n) x‖ ∂ρ < 1 / ((n : ℝ) + 1) := by
      have h1 : (∫⁻ x, ‖h x - (g n) x‖ₑ ∂ρ).toReal < 1 / ((n : ℝ) + 1) :=
        ENNReal.toReal_lt_of_lt_ofReal hL
      rwa [← MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
        ← hbridge (fun x : H => h x - (g n) x) hIntF] at h1
    have hclamp' : ∀ x : H, ‖Θ n x - h x‖ ≤ ‖h x - (g n) x‖ := by
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (h x) ((g n) x)]
      exact hclamp n x
    exact le_of_lt (lt_of_le_of_lt (integral_mono (hIntNorm n) hIntF.norm (fun x => hclamp' x)) hreal)
  have hsplit : ∀ n : ℕ, ∫ x, ‖Θ n x - h x‖ ∂ρ
      = ∫ x, ‖Θ n x - h x‖ ∂(nu : Measure H) + ∫ x, ‖Θ n x - h x‖ ∂(mu : Measure H) := by
    intro n
    rw [hρdef]
    exact MeasureTheory.integral_add_measure (hIntNormAny (nu : Measure H) (by infer_instance) n)
      (hIntNormAny (mu : Measure H) (by infer_instance) n)
  have hIntΘν : ∀ n : ℕ, Integrable (fun x : H => Θ n x) (nu : Measure H) := by
    intro n
    refine MeasureTheory.memLp_one_iff_integrable.mp
      (MeasureTheory.memLp_of_bounded (a := -B) (b := B) ?_ ?_ 1)
    · filter_upwards with x
      have h := hΘabs n x
      rw [Real.norm_eq_abs] at h
      exact abs_le.mp h
    · exact (hΘcont n).measurable.aestronglyMeasurable
  have hInthν : Integrable h (nu : Measure H) := by
    refine MeasureTheory.memLp_one_iff_integrable.mp
      (MeasureTheory.memLp_of_bounded (a := -B) (b := B) ?_ ?_ 1)
    · filter_upwards with x
      exact ⟨(abs_le.mp (hhB x)).1, (abs_le.mp (hhB x)).2⟩
    · exact hh_meas.aestronglyMeasurable
  have hν : Filter.Tendsto (fun n : ℕ => ∫ x, Θ n x ∂(nu : Measure H)) Filter.atTop
      (nhds (∫ x, h x ∂(nu : Measure H))) := by
    have hb : ∀ n : ℕ,
        ‖∫ x, Θ n x ∂(nu : Measure H) - ∫ x, h x ∂(nu : Measure H)‖ ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have hmono : ∫ x, ‖Θ n x - h x‖ ∂(nu : Measure H) ≤ 1 / ((n : ℝ) + 1) := by
        have h1 : ∫ x, ‖Θ n x - h x‖ ∂(nu : Measure H) ≤ ∫ x, ‖Θ n x - h x‖ ∂ρ := by
          rw [hsplit n]
          have h0 : 0 ≤ ∫ x, ‖Θ n x - h x‖ ∂(mu : Measure H) :=
            integral_nonneg (fun x => norm_nonneg _)
          linarith
        exact le_trans h1 (hkey n)
      calc ‖∫ x, Θ n x ∂(nu : Measure H) - ∫ x, h x ∂(nu : Measure H)‖
          = ‖∫ x, (Θ n x - h x) ∂(nu : Measure H)‖ := by
            rw [(MeasureTheory.integral_sub (hIntΘν n) hInthν).symm]
        _ ≤ ∫ x, ‖Θ n x - h x‖ ∂(nu : Measure H) :=
          MeasureTheory.norm_integral_le_integral_norm (fun x : H => Θ n x - h x)
        _ ≤ 1 / ((n : ℝ) + 1) := hmono
    have hlim : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlow : Filter.Tendsto (fun n : ℕ => ∫ x, h x ∂(nu : Measure H) - 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds (∫ x, h x ∂(nu : Measure H))) := by
      simpa using tendsto_const_nhds.sub hlim
    have hup : Filter.Tendsto (fun n : ℕ => ∫ x, h x ∂(nu : Measure H) + 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds (∫ x, h x ∂(nu : Measure H))) := by
      simpa using tendsto_const_nhds.add hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup ?_ ?_
    · intro n
      have h := hb n
      rw [Real.norm_eq_abs] at h
      linarith [(abs_le.mp h).1]
    · intro n
      have h := hb n
      rw [Real.norm_eq_abs] at h
      linarith [(abs_le.mp h).2]
  have hexp_step : ∀ a b : ℝ, b ≤ a → a ≤ B → Real.exp a - Real.exp b ≤ Real.exp B * (a - b) := by
    intro a b hba haB
    have h1 : Real.exp a = Real.exp b * Real.exp (a - b) := by
      rw [← Real.exp_add, show b + (a - b) = a by ring]
    have h3 : 1 - Real.exp (-(a - b)) ≤ a - b := by
      have h := Real.add_one_le_exp (-(a - b))
      linarith
    have hEq : Real.exp (a - b) * (1 - Real.exp (-(a - b))) = Real.exp (a - b) - 1 := by
      have h2 : Real.exp (a - b) * Real.exp (-(a - b)) = 1 := by
        rw [← Real.exp_add, show a - b + -(a - b) = 0 by ring, Real.exp_zero]
      rw [mul_sub, h2, mul_one]
    have h4 : Real.exp (a - b) - 1 ≤ (a - b) * Real.exp (a - b) := by
      rw [← hEq, mul_comm (a - b) (Real.exp (a - b))]
      exact mul_le_mul_of_nonneg_left h3 (Real.exp_pos (a - b)).le
    have h6 : 0 ≤ a - b := by linarith
    have h5 : Real.exp a ≤ Real.exp B := Real.exp_le_exp.mpr haB
    calc Real.exp a - Real.exp b = Real.exp b * (Real.exp (a - b) - 1) := by
          rw [h1]; ring
      _ ≤ Real.exp b * ((a - b) * Real.exp (a - b)) :=
          mul_le_mul_of_nonneg_left h4 (Real.exp_pos b).le
      _ = Real.exp a * (a - b) := by rw [h1]; ring
      _ ≤ Real.exp B * (a - b) := mul_le_mul_of_nonneg_right h5 h6
  have hexp_lip : ∀ a b : ℝ, |a| ≤ B → |b| ≤ B →
      ‖Real.exp a - Real.exp b‖ ≤ Real.exp B * ‖a - b‖ := by
    intro a b ha hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have haB : a ≤ B := (abs_le.mp ha).2
    have hbB : b ≤ B := (abs_le.mp hb).2
    rcases le_total b a with hle | hle
    · have e1 : |Real.exp a - Real.exp b| = Real.exp a - Real.exp b :=
        abs_of_nonneg (by linarith [Real.exp_le_exp.mpr hle])
      have e2 : |a - b| = a - b := abs_of_nonneg (by linarith)
      rw [e1, e2]
      exact hexp_step a b hle haB
    · have e1 : |Real.exp a - Real.exp b| = Real.exp b - Real.exp a := by
        rw [abs_of_nonpos (by linarith [Real.exp_le_exp.mpr hle])]; ring
      have e2 : |a - b| = b - a := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [e1, e2]
      exact hexp_step b a hle hbB
  have hIntExpΘ : ∀ n : ℕ, Integrable (fun x : H => Real.exp (Θ n x)) (mu : Measure H) := by
    intro n
    refine MeasureTheory.memLp_one_iff_integrable.mp
      (MeasureTheory.memLp_of_bounded (a := 0) (b := Real.exp B) ?_ ?_ 1)
    · filter_upwards with x
      have h : |Θ n x| ≤ B := by
        rw [← Real.norm_eq_abs]
        exact hΘabs n x
      exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (abs_le.mp h).2⟩
    · exact (Real.continuous_exp.measurable.comp (hΘcont n).measurable).aestronglyMeasurable
  have hIntExph : Integrable (fun x : H => Real.exp (h x)) (mu : Measure H) := by
    refine MeasureTheory.memLp_one_iff_integrable.mp
      (MeasureTheory.memLp_of_bounded (a := 0) (b := Real.exp B) ?_ ?_ 1)
    · filter_upwards with x
      have h : |h x| ≤ B := by
        rw [← Real.norm_eq_abs]
        exact hhB x
      exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (abs_le.mp h).2⟩
    · exact (Real.continuous_exp.measurable.comp hh_meas).aestronglyMeasurable
  have hIntExpDiff : ∀ n : ℕ,
      Integrable (fun x : H => ‖Real.exp (Θ n x) - Real.exp (h x)‖) (mu : Measure H) := by
    intro n
    refine MeasureTheory.memLp_one_iff_integrable.mp
      (MeasureTheory.memLp_of_bounded (a := 0) (b := Real.exp B * (2 * B)) ?_ ?_ 1)
    · filter_upwards with x
      refine ⟨norm_nonneg _, ?_⟩
      have h2 : ‖h x‖ ≤ B := by rw [Real.norm_eq_abs]; exact hhB x
      have h1 : ‖Θ n x - h x‖ ≤ 2 * B := by
        calc ‖Θ n x - h x‖ ≤ ‖Θ n x‖ + ‖h x‖ := norm_sub_le _ _
          _ ≤ B + B := by linarith [hΘabs n x]
          _ = 2 * B := by ring
      calc ‖Real.exp (Θ n x) - Real.exp (h x)‖
          ≤ Real.exp B * ‖Θ n x - h x‖ := hexp_lip (Θ n x) (h x)
            (by rw [← Real.norm_eq_abs]; exact hΘabs n x)
            (by rw [← Real.norm_eq_abs]; exact hhB x)
        _ ≤ Real.exp B * (2 * B) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos B).le
    · exact (((Real.continuous_exp.measurable.comp (hΘcont n).measurable).sub
        (Real.continuous_exp.measurable.comp hh_meas)).norm).aestronglyMeasurable
  have hIntMul : ∀ n : ℕ,
      Integrable (fun x : H => Real.exp B * ‖Θ n x - h x‖) (mu : Measure H) := by
    intro n
    refine MeasureTheory.memLp_one_iff_integrable.mp
      (MeasureTheory.memLp_of_bounded (a := 0) (b := Real.exp B * (2 * B)) ?_ ?_ 1)
    · filter_upwards with x
      refine ⟨mul_nonneg (Real.exp_pos B).le (norm_nonneg _), ?_⟩
      have h2 : ‖h x‖ ≤ B := by rw [Real.norm_eq_abs]; exact hhB x
      have h1 : ‖Θ n x - h x‖ ≤ 2 * B := by
        calc ‖Θ n x - h x‖ ≤ ‖Θ n x‖ + ‖h x‖ := norm_sub_le _ _
          _ ≤ B + B := by linarith [hΘabs n x]
          _ = 2 * B := by ring
      exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos B).le
    · exact ((((hΘcont n).measurable.sub hh_meas).norm).const_mul (Real.exp B)).aestronglyMeasurable
  have hμ : Filter.Tendsto (fun n : ℕ => ∫ x, Real.exp (Θ n x) ∂(mu : Measure H)) Filter.atTop
      (nhds (∫ x, Real.exp (h x) ∂(mu : Measure H))) := by
    have hb : ∀ n : ℕ,
        ‖∫ x, Real.exp (Θ n x) ∂(mu : Measure H) - ∫ x, Real.exp (h x) ∂(mu : Measure H)‖
          ≤ Real.exp B * (1 / ((n : ℝ) + 1)) := by
      intro n
      have hstep : ∫ x, ‖Real.exp (Θ n x) - Real.exp (h x)‖ ∂(mu : Measure H)
          ≤ Real.exp B * (1 / ((n : ℝ) + 1)) := by
        have h1 : ∫ x, ‖Real.exp (Θ n x) - Real.exp (h x)‖ ∂(mu : Measure H)
            ≤ ∫ x, Real.exp B * ‖Θ n x - h x‖ ∂(mu : Measure H) :=
          integral_mono (hIntExpDiff n) (hIntMul n) (fun x => hexp_lip (Θ n x) (h x)
            (by rw [← Real.norm_eq_abs]; exact hΘabs n x)
            (by rw [← Real.norm_eq_abs]; exact hhB x))
        have h2 : ∫ x, Real.exp B * ‖Θ n x - h x‖ ∂(mu : Measure H)
            = Real.exp B * ∫ x, ‖Θ n x - h x‖ ∂(mu : Measure H) :=
          MeasureTheory.integral_const_mul (Real.exp B) (fun x : H => ‖Θ n x - h x‖)
        have h3 : ∫ x, ‖Θ n x - h x‖ ∂(mu : Measure H) ≤ 1 / ((n : ℝ) + 1) := by
          have h4 : ∫ x, ‖Θ n x - h x‖ ∂(mu : Measure H) ≤ ∫ x, ‖Θ n x - h x‖ ∂ρ := by
            rw [hsplit n]
            have h0 : 0 ≤ ∫ x, ‖Θ n x - h x‖ ∂(nu : Measure H) :=
              integral_nonneg (fun x => norm_nonneg _)
            linarith
          exact le_trans h4 (hkey n)
        calc ∫ x, ‖Real.exp (Θ n x) - Real.exp (h x)‖ ∂(mu : Measure H)
            ≤ ∫ x, Real.exp B * ‖Θ n x - h x‖ ∂(mu : Measure H) := h1
          _ = Real.exp B * ∫ x, ‖Θ n x - h x‖ ∂(mu : Measure H) := h2
          _ ≤ Real.exp B * (1 / ((n : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left h3 (Real.exp_pos B).le
      calc ‖∫ x, Real.exp (Θ n x) ∂(mu : Measure H) - ∫ x, Real.exp (h x) ∂(mu : Measure H)‖
          = ‖∫ x, (Real.exp (Θ n x) - Real.exp (h x)) ∂(mu : Measure H)‖ := by
            rw [(MeasureTheory.integral_sub (hIntExpΘ n) hIntExph).symm]
        _ ≤ ∫ x, ‖Real.exp (Θ n x) - Real.exp (h x)‖ ∂(mu : Measure H) :=
            MeasureTheory.norm_integral_le_integral_norm (fun x : H => Real.exp (Θ n x) - Real.exp (h x))
        _ ≤ Real.exp B * (1 / ((n : ℝ) + 1)) := hstep
    have hlim : Filter.Tendsto (fun n : ℕ => Real.exp B * (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds 0) := by
      have h0 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.exp B)
      simpa using h0
    have hlow : Filter.Tendsto
        (fun n : ℕ => ∫ x, Real.exp (h x) ∂(mu : Measure H) - Real.exp B * (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds (∫ x, Real.exp (h x) ∂(mu : Measure H))) := by
      simpa using tendsto_const_nhds.sub hlim
    have hup : Filter.Tendsto
        (fun n : ℕ => ∫ x, Real.exp (h x) ∂(mu : Measure H) + Real.exp B * (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds (∫ x, Real.exp (h x) ∂(mu : Measure H))) := by
      simpa using tendsto_const_nhds.add hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup ?_ ?_
    · intro n
      have h := hb n
      rw [Real.norm_eq_abs] at h
      linarith [(abs_le.mp h).1]
    · intro n
      have h := hb n
      rw [Real.norm_eq_abs] at h
      linarith [(abs_le.mp h).2]
  exact ⟨Θ, hΘcont, hΘbdd, hν, hμ⟩
  /- @proof-region region.target-node.session.ec37c215c28d4b9c end -/

end
end Statlib.Imported
