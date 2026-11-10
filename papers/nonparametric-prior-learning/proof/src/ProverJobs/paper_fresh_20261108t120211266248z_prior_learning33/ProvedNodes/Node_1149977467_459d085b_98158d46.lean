import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

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
theorem statopia_math_node_1149977467_459d085b : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Ω → ℝ≥0∞) (ρ : Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hF_meas : ∀ n : ℕ, AEMeasurable (F n) μ)
    (hF_sq : ∀ n : ℕ, ∫⁻ ω, (F n ω) ^ (2 : ℕ) ∂μ ≤ C)
    (hC_top : C ≠ ⊤)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => F n ω) atTop (𝓝 (ρ ω))),
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal |(F n ω).toReal - (ρ ω).toReal| ∂μ)
      atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.cd0f6cc069343fac begin -/
  classical
  intro Ω instΩ μ instP F ρ C hF_meas hF_sq hC_top hae
  set f : ℕ → Ω → ℝ := fun n ω => (F n ω).toReal with hf
  set g : Ω → ℝ := fun ω => (ρ ω).toReal with hg
  change Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal |f n ω - g ω| ∂μ) atTop (𝓝 0)
  have hF_aesm : ∀ n : ℕ, AEStronglyMeasurable (F n) μ := fun n => (hF_meas n).aestronglyMeasurable
  have hρ_aesm : AEStronglyMeasurable ρ μ := aestronglyMeasurable_of_tendsto_ae atTop hF_aesm hae
  have hρ_meas : AEMeasurable ρ μ := hρ_aesm.aemeasurable
  have hf_aesm : ∀ n : ℕ, AEStronglyMeasurable (f n) μ :=
    fun n => (hF_meas n).ennreal_toReal.aestronglyMeasurable
  have hρ_int : ∫⁻ ω, ρ ω ∂μ ≠ ⊤ := by
    have hFatou : ∫⁻ ω, ρ ω ∂μ ≤ Filter.liminf (fun n : ℕ => ∫⁻ ω, F n ω ∂μ) atTop := by
      have heq : (∫⁻ ω, ρ ω ∂μ) = ∫⁻ ω, Filter.liminf (fun n : ℕ => F n ω) atTop ∂μ := by
        refine MeasureTheory.lintegral_congr_ae ?_
        filter_upwards [hae] with ω hω
        exact hω.liminf_eq.symm
      rw [heq]
      exact MeasureTheory.lintegral_liminf_le' hF_meas
    have hlim : Filter.liminf (fun n : ℕ => ∫⁻ ω, F n ω ∂μ) atTop ≤ C + 1 := by
      refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall fun n => zero_le _⟩ fun b hb => ?_
      obtain ⟨n, hn⟩ := Filter.Eventually.exists hb
      refine le_trans hn ?_
      have hpt' : ∀ x : ℝ≥0∞, x ≤ (1 : ℝ≥0∞) + x ^ (2 : ℕ) := by
        intro x
        by_cases hx : x = ⊤
        · rw [hx]; exact le_top
        · by_cases h1 : x ≤ 1
          · calc x ≤ 1 := h1
              _ ≤ (1 : ℝ≥0∞) + x ^ (2 : ℕ) := by
                  simpa using add_le_add (le_refl (1 : ℝ≥0∞)) (zero_le (x ^ (2 : ℕ)))
          · have h2 : x ≤ x ^ (2 : ℕ) := by
              have hx1 : (1 : ℝ≥0∞) ≤ x := le_of_lt (not_le.mp h1)
              calc x = x * 1 := (mul_one x).symm
                _ ≤ x * x := by gcongr
                _ = x ^ 2 := (pow_two x).symm
            calc x ≤ x ^ (2 : ℕ) := h2
              _ ≤ (1 : ℝ≥0∞) + x ^ (2 : ℕ) := by
                  simpa using add_le_add (zero_le (1 : ℝ≥0∞)) (le_refl (x ^ (2 : ℕ)))
      have hpt : (fun ω => F n ω) ≤ fun ω => (1 : ℝ≥0∞) + (F n ω) ^ (2 : ℕ) :=
        fun ω => hpt' (F n ω)
      calc ∫⁻ ω, F n ω ∂μ
          ≤ ∫⁻ ω, ((1 : ℝ≥0∞) + (F n ω) ^ (2 : ℕ)) ∂μ := MeasureTheory.lintegral_mono hpt
        _ = 1 + ∫⁻ ω, (F n ω) ^ (2 : ℕ) ∂μ := by
            rw [MeasureTheory.lintegral_add_left
              (show Measurable (fun _ : Ω => (1 : ℝ≥0∞)) from measurable_const)]
            simp
        _ ≤ 1 + C := add_le_add le_rfl (hF_sq n)
        _ = C + 1 := add_comm 1 C
    exact ne_top_of_le_ne_top (by simp [hC_top]) (le_trans hFatou hlim)
  have hg_memLp : MemLp g 1 μ := MeasureTheory.mem_L1_toReal_of_lintegral_ne_top hρ_meas hρ_int
  have hρ_lt : ∀ᵐ ω ∂μ, ρ ω < ⊤ := by
    have hnull : μ {ω | ρ ω = ⊤} = 0 :=
      MeasureTheory.measure_eq_top_of_lintegral_ne_top hρ_meas hρ_int
    have hc : {ω | ρ ω < ⊤}ᶜ = {ω | ρ ω = ⊤} := by
      ext ω
      constructor
      · intro h
        exact top_le_iff.1 (not_lt.1 h)
      · intro h
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at h ⊢
        rw [h]
        simp
    have hmem : {ω | ρ ω < ⊤} ∈ ae μ := by
      rw [MeasureTheory.mem_ae_iff, hc]
      exact hnull
    exact hmem
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hae, hρ_lt] with ω hω hlt
    show Tendsto (fun n : ℕ => (F n ω).toReal) atTop (𝓝 ((ρ ω).toReal))
    have hne : ρ ω ≠ ⊤ := ne_of_lt hlt
    have hfin : ∀ᶠ n : ℕ in atTop, F n ω < ⊤ := hω.eventually (isOpen_Iio.mem_nhds hlt)
    rw [tendsto_order]
    constructor
    · intro b hb
      by_cases hb0 : b < 0
      · exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le hb0 ENNReal.toReal_nonneg
      · push_neg at hb0
        have hpos : 0 < (ρ ω).toReal := lt_of_le_of_lt hb0 hb
        have h1 : ENNReal.ofReal b < ρ ω := by
          have h2 : ENNReal.ofReal b < ENNReal.ofReal ((ρ ω).toReal) :=
            (ENNReal.ofReal_lt_ofReal_iff hpos).2 hb
          rwa [ENNReal.ofReal_toReal hne] at h2
        filter_upwards [hω.eventually (isOpen_Ioi.mem_nhds h1), hfin] with n hn₁ hn₂
        have h3 : (ENNReal.ofReal b).toReal < (F n ω).toReal :=
          (ENNReal.toReal_lt_toReal (ne_of_lt (lt_of_lt_of_le h1 le_top)) (ne_of_lt hn₂)).2 hn₁
        rwa [ENNReal.toReal_ofReal hb0] at h3
    · intro b hb
      have hbpos : 0 < b := lt_of_le_of_lt ENNReal.toReal_nonneg hb
      have h1 : ρ ω < ENNReal.ofReal b := by
        have h2 : ENNReal.ofReal ((ρ ω).toReal) < ENNReal.ofReal b :=
          (ENNReal.ofReal_lt_ofReal_iff hbpos).2 hb
        rwa [ENNReal.ofReal_toReal hne] at h2
      filter_upwards [hω.eventually (isOpen_Iio.mem_nhds h1)] with n hn₁
      by_contra hc
      rw [not_lt] at hc
      exact absurd (ENNReal.ofReal_le_of_le_toReal hc) (not_le.2 hn₁)
  have hUI : UnifIntegrable f 1 μ := by
    intro ε hε
    have hx0 : (0:ℝ) < C.toReal + 1 := by linarith [ENNReal.toReal_nonneg (a := C)]
    refine ⟨(ε / (C.toReal + 1)) ^ 2, pow_pos (div_pos hε hx0) 2, ?_⟩
    intro i s hs hμs
    have hA : eLpNorm (s.indicator (f i)) 1 μ ≤ ∫⁻ x in s, F i x ∂μ := by
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      rw [← MeasureTheory.lintegral_indicator hs (f := fun x => F i x)]
      refine MeasureTheory.lintegral_mono fun x => ?_
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        show ‖(F i x).toReal‖ₑ ≤ F i x
        rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
        exact ENNReal.ofReal_toReal_le
      · simp [Set.indicator, hx]
    have hH := ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
      (μ := μ.restrict s) (p := (2:ℝ)) (q := (2:ℝ)) Real.HolderConjugate.two_two
      (f := F i) (g := fun _ : Ω => (1:ℝ≥0∞))
      ((hF_meas i).mono_measure Measure.restrict_le_self) aemeasurable_const
    have hL : (∫⁻ a, (F i a) * (1:ℝ≥0∞) ^ ((2:ℝ) - 1) ∂(μ.restrict s))
        = ∫⁻ x in s, F i x ∂μ := by
      simp
    have e1 : (∫⁻ a, (F i a) ^ (2:ℝ) ∂(μ.restrict s)) ^ (1/2:ℝ) ≤ C ^ (1/2:ℝ) := by
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      calc ∫⁻ a, (F i a) ^ (2:ℝ) ∂(μ.restrict s)
          = ∫⁻ a in s, (F i a) ^ (2:ℝ) ∂μ := rfl
        _ = ∫⁻ a, s.indicator (fun x => (F i x) ^ (2:ℝ)) a ∂μ := by
            rw [MeasureTheory.lintegral_indicator hs]
        _ ≤ ∫⁻ a, (F i a) ^ (2:ℝ) ∂μ := by
            refine MeasureTheory.lintegral_mono fun a => ?_
            by_cases ha : a ∈ s
            · rw [Set.indicator_of_mem ha]
            · simp [Set.indicator, ha]
        _ = ∫⁻ a, (F i a) ^ (2:ℕ) ∂μ := by simp
        _ ≤ C := hF_sq i
    have e2 : (∫⁻ a, (1:ℝ≥0∞) ^ (2:ℝ) ∂(μ.restrict s)) ^ (1/2:ℝ) ≤ (μ s) ^ (1/2:ℝ) := by
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      calc ∫⁻ a, (1:ℝ≥0∞) ^ (2:ℝ) ∂(μ.restrict s)
          = ∫⁻ a in s, (1:ℝ≥0∞) ∂μ := by simp
        _ = ∫⁻ a, s.indicator (fun _ => (1:ℝ≥0∞)) a ∂μ := by
            rw [MeasureTheory.lintegral_indicator hs]
        _ ≤ μ s := MeasureTheory.lintegral_indicator_one_le s
    have hB : ∫⁻ x in s, F i x ∂μ ≤ C ^ (1/2:ℝ) * (μ s) ^ (1/2:ℝ) := by
      calc ∫⁻ x in s, F i x ∂μ
          = ∫⁻ a, (F i a) * (1:ℝ≥0∞) ^ ((2:ℝ) - 1) ∂(μ.restrict s) := hL.symm
        _ ≤ (∫⁻ a, (F i a) ^ (2:ℝ) ∂(μ.restrict s)) ^ (1/2:ℝ)
              * (∫⁻ a, (1:ℝ≥0∞) ^ (2:ℝ) ∂(μ.restrict s)) ^ (1/2:ℝ) := hH
        _ ≤ C ^ (1/2:ℝ) * (μ s) ^ (1/2:ℝ) := by gcongr
    refine le_trans hA (le_trans hB ?_)
    have hCb : C ^ (1/2:ℝ) ≤ ENNReal.ofReal ((C.toReal + 1) ^ (1/2:ℝ)) := by
      have h1 : C ≤ ENNReal.ofReal (C.toReal + 1) := by
        rw [ENNReal.le_ofReal_iff_toReal_le hC_top (by positivity)]
        linarith
      calc C ^ (1/2:ℝ) ≤ (ENNReal.ofReal (C.toReal + 1)) ^ (1/2:ℝ) :=
            ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = ENNReal.ofReal ((C.toReal + 1) ^ (1/2:ℝ)) :=
            ENNReal.ofReal_rpow_of_nonneg (le_of_lt hx0) (by norm_num)
    have hs1 : (μ s) ^ (1/2:ℝ) ≤ ENNReal.ofReal (((ε / (C.toReal + 1)) ^ 2) ^ (1/2:ℝ)) := by
      calc (μ s) ^ (1/2:ℝ) ≤ (ENNReal.ofReal ((ε / (C.toReal + 1)) ^ 2)) ^ (1/2:ℝ) :=
            ENNReal.rpow_le_rpow hμs (by norm_num)
        _ = ENNReal.ofReal (((ε / (C.toReal + 1)) ^ 2) ^ (1/2:ℝ)) :=
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    have hAB : (C.toReal + 1) ^ (1/2:ℝ) * (((ε / (C.toReal + 1)) ^ 2) ^ (1/2:ℝ)) ≤ ε := by
      have hx1 : (1:ℝ) ≤ C.toReal + 1 := by linarith [ENNReal.toReal_nonneg (a := C)]
      have hB' : (((ε / (C.toReal + 1)) ^ 2) ^ (1/2:ℝ)) = ε / (C.toReal + 1) := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
      have hA' : (C.toReal + 1) ^ (1/2:ℝ) ≤ C.toReal + 1 := by
        rw [← Real.sqrt_eq_rpow]
        nlinarith [Real.sq_sqrt (le_of_lt hx0), Real.sqrt_nonneg (C.toReal + 1)]
      rw [hB']
      calc (C.toReal + 1) ^ (1/2:ℝ) * (ε / (C.toReal + 1))
          ≤ (C.toReal + 1) * (ε / (C.toReal + 1)) := mul_le_mul_of_nonneg_right hA' (by positivity)
        _ = ε := by field_simp
    calc C ^ (1/2:ℝ) * (μ s) ^ (1/2:ℝ)
        ≤ ENNReal.ofReal ((C.toReal + 1) ^ (1/2:ℝ))
            * ENNReal.ofReal (((ε / (C.toReal + 1)) ^ 2) ^ (1/2:ℝ)) := by gcongr
      _ = ENNReal.ofReal ((C.toReal + 1) ^ (1/2:ℝ) * (((ε / (C.toReal + 1)) ^ 2) ^ (1/2:ℝ))) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hAB
  have hLp : Tendsto (fun n : ℕ => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
    MeasureTheory.tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp) hf_aesm hg_memLp hUI hconv
  have hEq : (fun n : ℕ => eLpNorm (f n - g) 1 μ)
      =ᶠ[atTop] (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal |f n ω - g ω| ∂μ) := by
    filter_upwards with n
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
    refine MeasureTheory.lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs]
    simp only [Pi.sub_apply]
  exact hLp.congr' hEq

  /- @proof-region region.target-node.session.cd0f6cc069343fac end -/

end Statlib.Imported
end

