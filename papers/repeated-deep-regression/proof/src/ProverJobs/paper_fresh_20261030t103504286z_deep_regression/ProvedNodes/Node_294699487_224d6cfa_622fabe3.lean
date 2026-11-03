import Lean
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Vocabulary
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Base
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ProvedNodes.Node_1985255396_d777e722_08557e48
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ProvedNodes.Node_346034670_5d73780e_9324d444

namespace PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression


open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_294699487_224d6cfa : ∀ {ΩS Ω : Type*} [MeasurableSpace ΩS] [MeasurableSpace Ω]
    (mu : Measure ΩS) [IsProbabilityMeasure mu]
    (PX : Measure Ω) [IsProbabilityMeasure PX]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (X : Fin n × Fin m → ΩS → Ω)
    (hX_meas : ∀ ij : Fin n × Fin m, Measurable (X ij))
    (hX_map : ∀ ij : Fin n × Fin m, Measure.map (X ij) mu = PX)
    (B1 rstar c38 c39 : ℝ)
    (hB1 : 0 < B1) (hrstar : 0 < rstar) (hc38 : 0 ≤ c38) (hc39 : 0 ≤ c39)
    (fcirc : Ω → ℝ) (hfcirc_meas : Measurable fcirc)
    (hfcirc_bound : ∀ x : Ω, |fcirc x| ≤ B1)
    (F : Set (Ω → ℝ)) (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_bound : ∀ f ∈ F, ∀ x : Ω, |f x| ≤ B1)
    (fhat : ΩS → Ω → ℝ)
    (hFhat_mem : ∀ᵐ ω ∂mu, fhat ω ∈ F)
    (hA_meas : AEMeasurable (fun ω : ΩS => (l2Err PX fcirc (fhat ω)).toReal) mu)
    (hFhat_min : ∀ᵐ ω ∂mu, ∀ f ∈ F,
      (1 / ((n : ℝ) * (m : ℝ))) *
          ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2
        ≤ (1 / ((n : ℝ) * (m : ℝ))) *
          ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2)
    (hTail : ∀ t : ℝ, 0 < t →
      mu {ω : ΩS |
        |(l2Err PX fcirc (fhat ω)).toReal -
            (1 / ((n : ℝ) * (m : ℝ))) *
              ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2| >
          (1 / 2) * (l2Err PX fcirc (fhat ω)).toReal +
            c38 * B1 ^ 2 * rstar +
              c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ))}
        ≤ ENNReal.ofReal (Real.exp (-t))), ∀ f ∈ F,
      ∫ ω : ΩS, (l2Err PX fcirc (fhat ω)).toReal ∂mu ≤
        2 * (l2Err PX fcirc f).toReal + 2 * c38 * B1 ^ 2 * rstar +
          12 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := by
  /- @proof-region region.target-node.session.b1bd38924c059d6e begin -/
  intro ΩS _ Ω _ mu _ PX _ n m hn hm X hX_meas hX_law B1 rstar c38 c39 hB1 hrstar hc38 hc39
    fcirc hfcirc_meas hfcirc_bound F hF_meas hF_bound fhat hfhat_mem hA_meas h_min h_tail f hf
  obtain ⟨hBf_meas, hBf_bd, hBf_int, hBf_eq⟩ :=
      statopia_math_node_346034670_5d73780e mu PX n m hn hm X hX_meas hX_law B1 hB1
      fcirc hfcirc_meas hfcirc_bound f (hF_meas f hf) (hF_bound f hf)
  let A : ΩS → ℝ := fun ω => (l2Err PX fcirc (fhat ω)).toReal
  let Bf : ΩS → ℝ := fun ω =>
    (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2
  let Bfh : ΩS → ℝ := fun ω =>
    (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2
  let K1 : ℝ := c38 * B1 ^ 2 * rstar
  let R : ℝ → ℝ := fun t => c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ))
  let H : ΩS → ℝ := fun ω => max (A ω - 2 * Bf ω - 2 * K1) 0
  have hA_meas' : AEMeasurable A _ := hA_meas
  have hBf_meas' : Measurable Bf := hBf_meas
  have hBf_nonneg : ∀ ω : ΩS, (0 : ℝ) ≤ Bf ω := fun ω => (hBf_bd ω).1
  have hBf_ub : ∀ ω : ΩS, Bf ω ≤ 4 * B1 ^ 2 := fun ω => (hBf_bd ω).2
  have hBf_int' : Integrable Bf mu := hBf_int
  have hBf_eq' : ∫ ω : ΩS, Bf ω ∂mu = (l2Err PX fcirc f).toReal := by
    show (∫ ω : ΩS, (1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2 ∂mu) = (l2Err PX fcirc f).toReal
    have h := hBf_eq
    simp only [empRisk] at h
    exact h
  have hnm : (0 : ℝ) < (n : ℝ) * (m : ℝ) := by
    have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    exact mul_pos h1 h2
  have hK1 : (0 : ℝ) ≤ K1 :=
    mul_nonneg (mul_nonneg hc38 (sq_nonneg B1)) hrstar.le
  have hM : (0 : ℝ) ≤ 4 * B1 ^ 2 := mul_nonneg (by norm_num) (sq_nonneg B1)
  have hR : ∀ t : ℝ, 0 < t → (0 : ℝ) ≤ R t := fun t ht =>
    div_nonneg (mul_nonneg (mul_nonneg hc39 (sq_nonneg B1)) ht.le) hnm.le
  have hAnonneg : ∀ ω : ΩS, (0 : ℝ) ≤ A ω := fun ω => ENNReal.toReal_nonneg
  have hA_bound : ∀ᵐ ω ∂mu, A ω ≤ 4 * B1 ^ 2 := by
    filter_upwards [hfhat_mem] with ω hω
    have hle : l2Err PX fcirc (fhat ω) ≤ ENNReal.ofReal (4 * B1 ^ 2) := by
      show (∫⁻ x, ENNReal.ofReal ((fhat ω x - fcirc x) ^ 2) ∂PX) ≤ ENNReal.ofReal (4 * B1 ^ 2)
      calc (∫⁻ x, ENNReal.ofReal ((fhat ω x - fcirc x) ^ 2) ∂PX)
          ≤ ∫⁻ x, ENNReal.ofReal (4 * B1 ^ 2) ∂PX := by
            refine lintegral_mono fun x => ?_
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : fhat ω x - fcirc x ≤ 2 * B1 := by
              have h1a := (abs_le.1 (hF_bound (fhat ω) hω x)).2
              have h1b := (abs_le.1 (hfcirc_bound x)).1
              linarith
            have h2 : -(2 * B1) ≤ fhat ω x - fcirc x := by
              have h2a := (abs_le.1 (hF_bound (fhat ω) hω x)).1
              have h2b := (abs_le.1 (hfcirc_bound x)).2
              linarith
            have hp : (0 : ℝ) ≤
                (2 * B1 - (fhat ω x - fcirc x)) * (2 * B1 + (fhat ω x - fcirc x)) :=
              mul_nonneg (by linarith) (by linarith)
            nlinarith [hp]
        _ = ENNReal.ofReal (4 * B1 ^ 2) := by
            rw [lintegral_const, measure_univ, mul_one]
    calc A ω = (l2Err PX fcirc (fhat ω)).toReal := rfl
      _ ≤ (ENNReal.ofReal (4 * B1 ^ 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = 4 * B1 ^ 2 := ENNReal.toReal_ofReal (by positivity)
  have hH_meas : AEMeasurable H mu := by
    have hb : AEMeasurable (fun ω : ΩS => 2 * Bf ω) mu := hBf_meas'.aemeasurable.const_mul 2
    have h1 : AEMeasurable (fun ω : ΩS => A ω - 2 * Bf ω - 2 * K1) mu :=
      (hA_meas'.sub hb).sub aemeasurable_const
    have hcont : Continuous fun x : ℝ => max x 0 := continuous_id.max continuous_const
    exact hcont.measurable.comp_aemeasurable' h1
  have hH_nonneg : ∀ ω : ΩS, (0 : ℝ) ≤ H ω := fun ω => le_max_right _ _
  have hH_le_A : ∀ ω : ΩS, H ω ≤ A ω := by
    intro ω
    have hb : (0 : ℝ) ≤ 2 * Bf ω := by linarith [hBf_nonneg ω]
    have hx : A ω - 2 * Bf ω - 2 * K1 ≤ A ω := by linarith
    exact max_le hx (hAnonneg ω)
  have hH_bound : ∀ᵐ ω ∂mu, (0 : ℝ) ≤ H ω ∧ H ω ≤ 4 * B1 ^ 2 := by
    filter_upwards [hA_bound] with ω hω
    exact ⟨hH_nonneg ω, le_trans (hH_le_A ω) hω⟩
  have hkey : ∀ (t : ℝ), 0 < t → ∀ ω : ΩS, H ω > 2 * R t →
      fhat ω ∈ F → Bfh ω ≤ Bf ω →
      |A ω - Bfh ω| > (1 / 2) * A ω + K1 + R t := by
    intro t ht ω hH hmem hmin
    have hs0 : (0 : ℝ) ≤ 2 * R t := by linarith [hR t ht]
    have hxA : A ω - 2 * Bf ω - 2 * K1 > 2 * R t := by
      have hHdef : H ω = max (A ω - 2 * Bf ω - 2 * K1) 0 := rfl
      rw [hHdef] at hH
      by_contra hcon
      push_neg at hcon
      have hle : max (A ω - 2 * Bf ω - 2 * K1) 0 ≤ 2 * R t := max_le hcon hs0
      linarith
    have hA_gt : 2 * Bfh ω + 2 * K1 + 2 * R t < A ω := by linarith
    have hXY : Bfh ω < A ω := by
      by_contra hcon
      push_neg at hcon
      linarith [hA_gt, hcon, hAnonneg ω, hK1, hR t ht]
    have habs : |A ω - Bfh ω| = A ω - Bfh ω := abs_of_pos (by linarith)
    rw [habs]
    linarith
  have hnullP : mu {ω : ΩS | ¬ (fhat ω ∈ F ∧ Bfh ω ≤ Bf ω)} = 0 := by
    have hae : ∀ᵐ ω ∂mu, fhat ω ∈ F ∧ Bfh ω ≤ Bf ω := by
      filter_upwards [hfhat_mem, h_min] with ω h1 h2 using ⟨h1, h2 f hf⟩
    exact MeasureTheory.ae_iff.1 hae
  have htail_bound : ∀ t : ℝ, 0 < t →
      mu {ω : ΩS | H ω > 2 * R t} ≤ ENNReal.ofReal (Real.exp (-t)) := by
    intro t ht
    have hsub : {ω : ΩS | H ω > 2 * R t} ⊆
        {ω : ΩS | |A ω - Bfh ω| > (1 / 2) * A ω + K1 + R t}
          ∪ {ω : ΩS | ¬ (fhat ω ∈ F ∧ Bfh ω ≤ Bf ω)} := by
      intro ω hω
      by_cases hP : fhat ω ∈ F ∧ Bfh ω ≤ Bf ω
      · exact Or.inl (hkey t ht ω hω hP.1 hP.2)
      · exact Or.inr hP
    calc mu {ω : ΩS | H ω > 2 * R t}
        ≤ mu ({ω : ΩS | |A ω - Bfh ω| > (1 / 2) * A ω + K1 + R t}
            ∪ {ω : ΩS | ¬ (fhat ω ∈ F ∧ Bfh ω ≤ Bf ω)}) := measure_mono hsub
      _ ≤ mu {ω : ΩS | |A ω - Bfh ω| > (1 / 2) * A ω + K1 + R t}
            + mu {ω : ΩS | ¬ (fhat ω ∈ F ∧ Bfh ω ≤ Bf ω)} := measure_union_le _ _
      _ = mu {ω : ΩS | |A ω - Bfh ω| > (1 / 2) * A ω + K1 + R t} := by
            rw [hnullP, add_zero]
      _ ≤ ENNReal.ofReal (Real.exp (-t)) := h_tail t ht
  have hHmain : Integrable H mu ∧
      ∫ ω : ΩS, H ω ∂mu ≤ 12 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := by
    rcases eq_or_lt_of_le hc39 with hzero | hpos
    · have hc39z : c39 = 0 := hzero.symm
      have hbnd : ∀ t : ℝ, 0 < t →
          mu {ω : ΩS | H ω > 0} ≤ ENNReal.ofReal (Real.exp (-t)) := by
        intro t ht
        have harg' : R t = 0 := by
          show c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) = 0
          rw [hc39z]
          simp
        have hset : {ω : ΩS | H ω > 0} = {ω : ΩS | H ω > 2 * R t} := by
          rw [harg']
          norm_num
        rw [hset]
        exact htail_bound t ht
      have integ : Integrable H mu := by
        refine (statopia_math_node_1985255396_d777e722 mu 1 (4 * B1 ^ 2) zero_lt_one hM H
          hH_meas hH_bound ?_).1
        intro s hs
        have hsub : {ω : ΩS | H ω > s} ⊆ {ω : ΩS | H ω > 0} := by
          intro ω hω
          exact lt_trans hs hω
        calc mu {ω : ΩS | H ω > s} ≤ mu {ω : ΩS | H ω > 0} := measure_mono hsub
          _ ≤ ENNReal.ofReal (Real.exp (-(1 * s))) := by simpa using hbnd s hs
      have hzero_int : ∫ ω : ΩS, H ω ∂mu ≤ 0 := by
        refine le_of_forall_pos_le_add fun eps heps => ?_
        have hb : ∫ ω : ΩS, H ω ∂mu ≤ 6 / (6 / eps) := by
          refine (statopia_math_node_1985255396_d777e722 mu (6 / eps) (4 * B1 ^ 2)
            (div_pos (by norm_num) heps) hM H hH_meas hH_bound ?_).2
          intro s hs
          have hsub : {ω : ΩS | H ω > s} ⊆ {ω : ΩS | H ω > 0} := by
            intro ω hω
            exact lt_trans hs hω
          calc mu {ω : ΩS | H ω > s} ≤ mu {ω : ΩS | H ω > 0} := measure_mono hsub
            _ ≤ ENNReal.ofReal (Real.exp (-((6 / eps) * s))) :=
                hbnd ((6 / eps) * s) (mul_pos (div_pos (by norm_num) heps) hs)
        have heq : 6 / (6 / eps) = eps := by
          have hne : eps ≠ 0 := ne_of_gt heps
          field_simp
        linarith [hb, heq]
      have hgoal : 12 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) = 0 := by
        rw [hc39z]
        simp
      exact ⟨integ, by rw [hgoal]; exact hzero_int⟩
    · have hB1sq : (0 : ℝ) < B1 ^ 2 := pow_pos hB1 2
      have hc39pos : (0 : ℝ) < c39 := hpos
      have hden : (0 : ℝ) < 2 * c39 * B1 ^ 2 := mul_pos (by linarith) hB1sq
      have hlam : (0 : ℝ) < ((n : ℝ) * (m : ℝ)) / (2 * c39 * B1 ^ 2) := div_pos hnm hden
      have hc39ne : c39 ≠ 0 := ne_of_gt hpos
      have hB1ne : B1 ≠ 0 := ne_of_gt hB1
      have hnmne : (n : ℝ) * (m : ℝ) ≠ 0 := ne_of_gt hnm
      have hdne : 2 * c39 * B1 ^ 2 ≠ 0 := ne_of_gt hden
      have hscaled : ∀ s : ℝ, 0 < s →
          mu {ω : ΩS | H ω > s} ≤
            ENNReal.ofReal (Real.exp (-(((n : ℝ) * (m : ℝ)) / (2 * c39 * B1 ^ 2) * s))) := by
        intro s hs
        have ht : 0 < ((n : ℝ) * (m : ℝ)) / (2 * c39 * B1 ^ 2) * s := mul_pos hlam hs
        have h2 : 2 * R (((n : ℝ) * (m : ℝ)) / (2 * c39 * B1 ^ 2) * s) = s := by
          show 2 * (c39 * B1 ^ 2 * (((n : ℝ) * (m : ℝ)) / (2 * c39 * B1 ^ 2) * s) /
            ((n : ℝ) * (m : ℝ))) = s
          field_simp
        calc mu {ω : ΩS | H ω > s}
            = mu {ω : ΩS | H ω > 2 * R (((n : ℝ) * (m : ℝ)) / (2 * c39 * B1 ^ 2) * s)} := by
                rw [h2]
          _ ≤ ENNReal.ofReal (Real.exp (-(((n : ℝ) * (m : ℝ)) / (2 * c39 * B1 ^ 2) * s))) :=
                htail_bound _ ht
      obtain ⟨hint, hle⟩ :=
        statopia_math_node_1985255396_d777e722 mu (((n : ℝ) * (m : ℝ)) / (2 * c39 * B1 ^ 2))
          (4 * B1 ^ 2) hlam hM H hH_meas hH_bound hscaled
      refine ⟨hint, ?_⟩
      have heq : 6 / (((n : ℝ) * (m : ℝ)) / (2 * c39 * B1 ^ 2)) =
          12 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := by
        field_simp
        ring
      linarith [hle, heq]
  obtain ⟨hH_int, hH_le⟩ := hHmain
  have hA_int : Integrable A mu := by
    refine MeasureTheory.Integrable.of_bound hA_meas'.aestronglyMeasurable (4 * B1 ^ 2) ?_
    filter_upwards [hA_bound] with ω hω
    rw [Real.norm_of_nonneg (hAnonneg ω)]
    exact hω
  have hInt : Integrable (fun ω : ΩS => 2 * Bf ω + 2 * K1 + H ω) mu :=
    ((hBf_int'.const_mul 2).add (integrable_const (2 * K1))).add hH_int
  have hA_le : ∀ᵐ ω ∂mu, A ω ≤ 2 * Bf ω + 2 * K1 + H ω := by
    filter_upwards with ω
    have h1 : A ω - 2 * Bf ω - 2 * K1 ≤ H ω := le_max_left _ _
    linarith
  have hmono : ∫ ω : ΩS, A ω ∂mu ≤ ∫ ω : ΩS, 2 * Bf ω + 2 * K1 + H ω ∂mu :=
    integral_mono_ae hA_int hInt hA_le
  have hI1 : Integrable (fun ω : ΩS => 2 * Bf ω) mu := hBf_int'.const_mul 2
  have hI2 : Integrable (fun _ : ΩS => 2 * K1) mu := integrable_const (2 * K1)
  have hI3 : Integrable (fun ω : ΩS => 2 * Bf ω + 2 * K1) mu := by
    have h := hI1.add hI2
    simpa using h
  have hsplit : ∫ ω : ΩS, (2 * Bf ω + 2 * K1 + H ω) ∂mu
      = 2 * ∫ ω : ΩS, Bf ω ∂mu + 2 * K1 + ∫ ω : ΩS, H ω ∂mu := by
    have e1 : ∫ ω : ΩS, (2 * Bf ω + 2 * K1) + H ω ∂mu
        = ∫ ω : ΩS, 2 * Bf ω + 2 * K1 ∂mu + ∫ ω : ΩS, H ω ∂mu := by
      simpa using integral_add hI3 hH_int
    have e2 : ∫ ω : ΩS, 2 * Bf ω + 2 * K1 ∂mu
        = ∫ ω : ΩS, 2 * Bf ω ∂mu + ∫ ω : ΩS, 2 * K1 ∂mu := by
      simpa using integral_add hI1 hI2
    have e3 : ∫ ω : ΩS, 2 * Bf ω ∂mu = 2 * ∫ ω : ΩS, Bf ω ∂mu :=
      integral_const_mul 2 Bf
    have e4 : ∫ ω : ΩS, 2 * K1 ∂mu = 2 * K1 := by
      rw [integral_const]
      simp [Measure.real]
    linarith [e1, e2, e3, e4]
  calc ∫ ω : ΩS, A ω ∂mu
      ≤ ∫ ω : ΩS, 2 * Bf ω + 2 * K1 + H ω ∂mu := hmono
    _ = 2 * ∫ ω : ΩS, Bf ω ∂mu + 2 * K1 + ∫ ω : ΩS, H ω ∂mu := hsplit
    _ ≤ 2 * (l2Err PX fcirc f).toReal + 2 * c38 * B1 ^ 2 * rstar
          + 12 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := by
        have h2 : 2 * ∫ ω : ΩS, Bf ω ∂mu = 2 * (l2Err PX fcirc f).toReal := by
          rw [hBf_eq']
        have h3 : 2 * K1 = 2 * c38 * B1 ^ 2 * rstar := by
          show 2 * (c38 * B1 ^ 2 * rstar) = 2 * c38 * B1 ^ 2 * rstar
          ring
        linarith [h2, h3, hH_le]
  /- @proof-region region.target-node.session.b1bd38924c059d6e end -/

end Statlib.Imported
end

