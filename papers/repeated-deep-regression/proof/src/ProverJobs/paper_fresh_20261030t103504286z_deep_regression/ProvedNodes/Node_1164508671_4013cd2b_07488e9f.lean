import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Lean
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Vocabulary
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Base

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
theorem statopia_math_node_1164508671_4013cd2b : ∀ {ΩS Ω : Type*} [MeasurableSpace ΩS] [MeasurableSpace Ω]
    (mu : Measure ΩS) [IsProbabilityMeasure mu] (PX : Measure Ω) [IsProbabilityMeasure PX]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (X : Fin n × Fin m → ΩS → Ω) (hX_meas : ∀ ij : Fin n × Fin m, Measurable (X ij))
    (hX_law : ∀ ij : Fin n × Fin m, Measure.map (X ij) mu = PX)
    (B1 rstar c38 c39 : ℝ) (hB1 : 0 < B1) (hrstar : 0 < rstar) (hc38 : 0 < c38)
    (hc39 : 0 < c39)
    (fcirc : Ω → ℝ) (hfcirc_meas : Measurable fcirc) (hfcirc_bound : ∀ x : Ω, |fcirc x| ≤ B1)
    (F : Set (Ω → ℝ)) (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_bound : ∀ f ∈ F, ∀ x : Ω, |f x| ≤ B1)
    (fhat : ΩS → Ω → ℝ) (hmem : ∀ᵐ ω ∂mu, fhat ω ∈ F)
    (hA_meas : AEMeasurable (fun ω : ΩS => (l2Err PX fcirc (fhat ω)).toReal) mu)
    (hmin : ∀ᵐ ω ∂mu, ∀ f ∈ F,
      (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
          (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2
        ≤ (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
          (f (X ij ω) - fcirc (X ij ω)) ^ 2)
    (hdev : ∀ t : ℝ, 0 < t →
      rstar ≤ 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) →
      mu {ω : ΩS |
          |(l2Err PX fcirc (fhat ω)).toReal
              - (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                  (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2|
            > (1 / 2) * (l2Err PX fcirc (fhat ω)).toReal + c38 * B1 ^ 2 * rstar
              + c39 * B1 ^ 2 * (t + 1) / ((n : ℝ) * (m : ℝ))}
        ≤ ENNReal.ofReal (Real.exp (-t))),
    ∀ f ∈ F,
      (∫ ω : ΩS, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
        ≤ 2 * (l2Err PX fcirc f).toReal + max rstar (2 * c38 * B1 ^ 2 * rstar)
          + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := by
  /- @proof-region region.target-node.session.879f8c0e813c5a13 begin -/
  intro ΩS Ω _ _ mu _ PX _ n m hn hm X hX_meas hX_law B1 rstar c38 c39 hB1 hrstar hc38 hc39
    fcirc hfcirc_meas hfcirc_bound F hF_meas hF_bound fhat hmem hA_meas hmin hdev f hf
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := mul_pos hnR hmR
  have hNne : ((n : ℝ) * (m : ℝ)) ≠ 0 := ne_of_gt hNpos
  set A : ΩS → ℝ := fun ω => (l2Err PX fcirc (fhat ω)).toReal with hAdef
  set Bc : ΩS → ℝ := fun ω => (1 / ((n : ℝ) * (m : ℝ))) *
    ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2 with hBcdef
  set Bh : ΩS → ℝ := fun ω => (1 / ((n : ℝ) * (m : ℝ))) *
    ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2 with hBhdef
  set Q : ℝ := (l2Err PX fcirc f).toReal with hQdef
  set a : ℝ := c38 * B1 ^ 2 * rstar with hadef
  set b : ℝ := c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) with hbdef
  set S : ℝ := max rstar (2 * a) + 2 * b with hSdef
  set H : ΩS → ℝ := fun ω => max (A ω - 2 * Bc ω) 0 with hHdef
  have hA_nn : ∀ ω, 0 ≤ A ω := fun ω => ENNReal.toReal_nonneg
  have hff_meas : Measurable f := hF_meas f hf
  have hff_bd : ∀ x : Ω, |f x| ≤ B1 := hF_bound f hf
  have hsq : ∀ (g : Ω → ℝ), (∀ x : Ω, |g x| ≤ B1) → ∀ x : Ω, (g x - fcirc x) ^ 2 ≤ 4 * B1 ^ 2 := by
    intro g hg x
    have h1 : |g x - fcirc x| ≤ 2 * B1 := by
      have hsub : g x - fcirc x = g x + -(fcirc x) := by ring
      calc |g x - fcirc x| = |g x + -(fcirc x)| := by rw [hsub]
        _ ≤ |g x| + |-(fcirc x)| := abs_add_le _ _
        _ = |g x| + |fcirc x| := by rw [abs_neg]
        _ ≤ B1 + B1 := by linarith [hg x, hfcirc_bound x]
        _ = 2 * B1 := by ring
    have h2 : (0 : ℝ) ≤ 2 * B1 := by linarith
    calc (g x - fcirc x) ^ 2 = |g x - fcirc x| ^ 2 := (sq_abs _).symm
      _ = |g x - fcirc x| * |g x - fcirc x| := sq _
      _ ≤ (2 * B1) * (2 * B1) := mul_le_mul h1 h1 (abs_nonneg _) h2
      _ = 4 * B1 ^ 2 := by ring
  have hl2_le : ∀ (g : Ω → ℝ), (∀ x : Ω, |g x| ≤ B1) →
      l2Err PX fcirc g ≤ ENNReal.ofReal (4 * B1 ^ 2) := by
    intro g hg
    simp only [l2Err]
    calc ∫⁻ x, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX
        ≤ ∫⁻ _x, ENNReal.ofReal (4 * B1 ^ 2) ∂PX :=
          lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hsq g hg x))
      _ = ENNReal.ofReal (4 * B1 ^ 2) := by rw [lintegral_const, measure_univ, mul_one]
  have hA_le : ∀ᵐ ω ∂mu, A ω ≤ 4 * B1 ^ 2 := by
    filter_upwards [hmem] with ω hω
    have h := hl2_le (fhat ω) (hF_bound (fhat ω) hω)
    have h4 : (0 : ℝ) ≤ 4 * B1 ^ 2 := by positivity
    calc A ω = (l2Err PX fcirc (fhat ω)).toReal := by simp only [hAdef]
      _ ≤ (ENNReal.ofReal (4 * B1 ^ 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = 4 * B1 ^ 2 := ENNReal.toReal_ofReal h4
  have hcpos : (0 : ℝ) < 1 / ((n : ℝ) * (m : ℝ)) := one_div_pos.mpr hNpos
  have hBc_nn : ∀ ω, 0 ≤ Bc ω := by
    intro ω
    have h2 : (0 : ℝ) ≤ ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2 :=
      Finset.sum_nonneg (fun ij _ => sq_nonneg _)
    simp only [hBcdef]
    exact mul_nonneg (le_of_lt hcpos) h2
  have hcard : ((Fintype.card (Fin n × Fin m) : ℕ) : ℝ) = (n : ℝ) * (m : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
  have hsum_le : ∀ ω, ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2
      ≤ ((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2) := by
    intro ω
    have h2 : ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2
        ≤ ∑ _ij : Fin n × Fin m, (4 * B1 ^ 2) :=
      Finset.sum_le_sum (fun ij _ => hsq f hff_bd (X ij ω))
    have h3 : (∑ _ij : Fin n × Fin m, (4 * B1 ^ 2)) = ((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    linarith [h2, h3]
  have hBc_le : ∀ ω, Bc ω ≤ 4 * B1 ^ 2 := by
    intro ω
    have h1 := hsum_le ω
    have h3 : (1 / ((n : ℝ) * (m : ℝ))) * (((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2)) = 4 * B1 ^ 2 := by
      field_simp
    calc Bc ω = (1 / ((n : ℝ) * (m : ℝ))) *
          ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2 := by simp only [hBcdef]
      _ ≤ (1 / ((n : ℝ) * (m : ℝ))) * (((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hcpos)
      _ = 4 * B1 ^ 2 := h3
  have hterm : ∀ ij : Fin n × Fin m, Measurable fun ω => (f (X ij ω) - fcirc (X ij ω)) ^ 2 := by
    intro ij
    have h1 : Measurable fun ω => f (X ij ω) - fcirc (X ij ω) :=
      (hff_meas.comp (hX_meas ij)).sub (hfcirc_meas.comp (hX_meas ij))
    have h2 : Measurable fun ω =>
        (f (X ij ω) - fcirc (X ij ω)) * (f (X ij ω) - fcirc (X ij ω)) := h1.mul h1
    simpa only [sq] using h2
  have hsum_meas : Measurable fun ω =>
      ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2 := by
    classical
    have hgen : ∀ s : Finset (Fin n × Fin m),
        Measurable fun ω => ∑ ij ∈ s, (f (X ij ω) - fcirc (X ij ω)) ^ 2 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty]
          exact measurable_const
      | insert a s ha ih =>
          have hstep := (hterm a).add ih
          simpa only [Finset.sum_insert ha] using hstep
    exact hgen Finset.univ
  have hBc_meas : Measurable Bc := by
    have h := (measurable_const : Measurable fun _ : ΩS => (1 / ((n : ℝ) * (m : ℝ)))).mul hsum_meas
    simpa only [hBcdef] using h
  have hBc_aesm : AEStronglyMeasurable Bc mu := hBc_meas.aestronglyMeasurable
  have hH_aesm : AEStronglyMeasurable H mu := by
    have h1 : AEMeasurable (fun ω => A ω - 2 * Bc ω) mu :=
      hA_meas.sub (hBc_meas.aemeasurable.const_mul 2)
    have h2 : AEMeasurable (fun ω => max (A ω - 2 * Bc ω) 0) mu := by
      first
      | exact h1.max aemeasurable_const
      | exact AEMeasurable.max h1 aemeasurable_const
      | exact h1.max measurable_const.aemeasurable
    simpa only [hHdef] using h2.aestronglyMeasurable
  have hBc_int : Integrable Bc mu := by
    refine MeasureTheory.Integrable.of_bound hBc_aesm (4 * B1 ^ 2) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hBc_nn ω)]
    exact hBc_le ω
  have hA_aesm : AEStronglyMeasurable A mu := hA_meas.aestronglyMeasurable
  have hA_int : Integrable A mu := by
    refine MeasureTheory.Integrable.of_bound hA_aesm (4 * B1 ^ 2) ?_
    filter_upwards [hA_le] with ω hle
    rw [Real.norm_eq_abs, abs_of_nonneg (hA_nn ω)]
    exact hle
  have hH_nn : ∀ ω, 0 ≤ H ω := by
    intro ω
    simp only [hHdef]
    exact le_max_right _ _
  have hH_leA : ∀ ω, H ω ≤ A ω := by
    intro ω
    simp only [hHdef]
    exact max_le (by linarith [hBc_nn ω]) (hA_nn ω)
  have hH_int : Integrable H mu := by
    refine MeasureTheory.Integrable.of_bound hH_aesm (4 * B1 ^ 2) ?_
    filter_upwards [hA_le] with ω hle
    rw [Real.norm_eq_abs, abs_of_nonneg (hH_nn ω)]
    exact le_trans (hH_leA ω) hle
  have hBc_eq_int : ∫ ω, Bc ω ∂mu = Q := by
    have hF_meas2 : Measurable fun y : Ω => (f y - fcirc y) ^ 2 := by
      have h1 : Measurable fun y : Ω => f y - fcirc y := hff_meas.sub hfcirc_meas
      have h2 : Measurable fun y : Ω => (f y - fcirc y) * (f y - fcirc y) := h1.mul h1
      simpa only [sq] using h2
    have hF_int : Integrable (fun y : Ω => (f y - fcirc y) ^ 2) PX := by
      refine MeasureTheory.Integrable.of_bound hF_meas2.aestronglyMeasurable (4 * B1 ^ 2) ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsq f hff_bd y
    have hF_bridge : ∫ y, (f y - fcirc y) ^ 2 ∂PX = Q := by
      have h0 : 0 ≤ᶠ[ae PX] fun y : Ω => (f y - fcirc y) ^ 2 :=
        Filter.Eventually.of_forall (fun y => sq_nonneg _)
      rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
        h0 hF_int]
      rw [hQdef]
      simp only [l2Err]
    have hsum_int : ∀ ij : Fin n × Fin m,
        Integrable (fun ω => (f (X ij ω) - fcirc (X ij ω)) ^ 2) mu := by
      intro ij
      refine MeasureTheory.Integrable.of_bound (hterm ij).aestronglyMeasurable (4 * B1 ^ 2) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsq f hff_bd (X ij ω)
    have hper : ∀ ij : Fin n × Fin m,
        ∫ ω, (f (X ij ω) - fcirc (X ij ω)) ^ 2 ∂mu = Q := by
      intro ij
      have hmap : ∫ y, (f y - fcirc y) ^ 2 ∂PX
          = ∫ ω, (f (X ij ω) - fcirc (X ij ω)) ^ 2 ∂mu := by
        rw [← hX_law ij]
        exact integral_map (hX_meas ij).aemeasurable
          (by rw [hX_law ij]; exact hF_meas2.aestronglyMeasurable)
      rw [← hmap]
      exact hF_bridge
    have hpull : ∫ ω, (1 / ((n : ℝ) * (m : ℝ))) * (∑ ij : Fin n × Fin m,
          (f (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu
        = (1 / ((n : ℝ) * (m : ℝ))) * ∫ ω, (∑ ij : Fin n × Fin m,
          (f (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu := by
      first
      | rw [integral_const_mul]
      | simp only [← smul_eq_mul, integral_smul]
      | rw [integral_mul_left]
      | rw [integral_smul, smul_eq_mul]
    have hfin : ∫ ω, (∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu
        = ((n : ℝ) * (m : ℝ)) * Q := by
      have h1 : ∫ ω, (∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu
          = ∑ ij : Fin n × Fin m, ∫ ω, (f (X ij ω) - fcirc (X ij ω)) ^ 2 ∂mu := by
        first
        | exact integral_finset_sum Finset.univ (fun ij _ => hsum_int ij)
        | exact integral_finset_sum (fun ij _ => hsum_int ij)
      rw [h1]
      have h2 : ∑ ij : Fin n × Fin m, ∫ ω, (f (X ij ω) - fcirc (X ij ω)) ^ 2 ∂mu
          = ∑ _ij : Fin n × Fin m, Q := Finset.sum_congr rfl (fun ij _ => hper ij)
      rw [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    calc ∫ ω, Bc ω ∂mu
        = ∫ ω, (1 / ((n : ℝ) * (m : ℝ))) * (∑ ij : Fin n × Fin m,
            (f (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu := by simp only [hBcdef]
      _ = (1 / ((n : ℝ) * (m : ℝ))) * ∫ ω, (∑ ij : Fin n × Fin m,
            (f (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu := hpull
      _ = (1 / ((n : ℝ) * (m : ℝ))) * (((n : ℝ) * (m : ℝ)) * Q) := by rw [hfin]
      _ = Q := by field_simp
  have hb_pos : 0 < b := by
    rw [hbdef]
    exact div_pos (mul_pos hc39 (pow_pos hB1 2)) hNpos
  have hKey : ∫ ω, H ω ∂mu ≤ max rstar (2 * a) + 4 * b := by
    have hSpos : 0 < S := by
      rw [hSdef]
      linarith [hrstar, hb_pos, le_max_left rstar (2 * a)]
    have hb2 : (0 : ℝ) < 2 * b := by linarith
    have hw : (0 : ℝ) < 1 / (2 * b) := one_div_pos.mpr hb2
    have hSr : rstar + 2 * b ≤ S := by
      rw [hSdef]
      linarith [le_max_left rstar (2 * a)]
    have hSa : 2 * a + 2 * b ≤ S := by rw [hSdef]; linarith [le_max_right rstar (2 * a)]
    have htail : ∀ t : ℝ, S < t →
        mu {a : ΩS | t < H a} ≤
          ENNReal.ofReal (Real.exp 1 * Real.exp (-(t - 2 * a) / (2 * b))) := by
      intro t ht
      set u : ℝ := (t / 2 - a) / b - 1 with hudef
      have hbu : b * u = t / 2 - a - b := by
        rw [hudef]
        field_simp
      have hu_pos : 0 < u := by
        have hSa2 : 2 * a + 2 * b ≤ S := by rw [hSdef]; linarith [le_max_right rstar (2 * a)]
        have h1 : (0 : ℝ) < (t / 2 - a) - b := by linarith
        have hq : (t / 2 - a) / b - 1 = ((t / 2 - a) - b) / b := by field_simp
        rw [hudef, hq]
        exact div_pos h1 hb_pos
      have hguard : rstar ≤ 2 * c38 * B1 ^ 2 * rstar
          + 2 * c39 * B1 ^ 2 * u / ((n : ℝ) * (m : ℝ)) := by
        have h1 : (2 : ℝ) * c38 * B1 ^ 2 * rstar = 2 * a := by
          rw [hadef]
          ring
        have h2 : (2 : ℝ) * c39 * B1 ^ 2 * u / ((n : ℝ) * (m : ℝ)) = 2 * (b * u) := by
          rw [hbdef]
          ring
        rw [h1, h2, hbu]
        linarith
      have hexp : -u = 1 + (-(t - 2 * a) / (2 * b)) := by
        rw [hudef]
        field_simp
        ring
      have hset : {ω : ΩS | |A ω - Bh ω| > (1 / 2) * A ω + a
            + c39 * B1 ^ 2 * (u + 1) / ((n : ℝ) * (m : ℝ))}
          = {ω : ΩS |
              |(l2Err PX fcirc (fhat ω)).toReal
                  - (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                      (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2|
                > (1 / 2) * (l2Err PX fcirc (fhat ω)).toReal + a
                  + c39 * B1 ^ 2 * (u + 1) / ((n : ℝ) * (m : ℝ))} := by
        ext ω
        simp only [Set.mem_setOf_eq, hAdef, hBhdef]
      have hdev' : mu {ω : ΩS | |A ω - Bh ω| > (1 / 2) * A ω + a
            + c39 * B1 ^ 2 * (u + 1) / ((n : ℝ) * (m : ℝ))}
          ≤ ENNReal.ofReal (Real.exp (-u)) := by
        rw [hset]
        exact hdev u hu_pos hguard
      have hmin' : ∀ᵐ ω ∂mu, Bh ω ≤ Bc ω := by
        filter_upwards [hmin] with ω hω
        simpa only [hBhdef, hBcdef] using hω f hf
      have hnull : mu {ω : ΩS | ¬ (Bh ω ≤ Bc ω)} = 0 := by
        rw [← MeasureTheory.ae_iff]
        exact hmin'
      have hsub : {a : ΩS | t < H a} ⊆
          ({ω : ΩS | |A ω - Bh ω| > (1 / 2) * A ω + a
              + c39 * B1 ^ 2 * (u + 1) / ((n : ℝ) * (m : ℝ))}
            ∪ {ω : ΩS | ¬ (Bh ω ≤ Bc ω)}) := by
        intro ω hω
        by_cases hbc : Bh ω ≤ Bc ω
        · left
          simp only [Set.mem_setOf_eq]
          have hω' : t < H ω := hω
          have hHv : H ω = max (A ω - 2 * Bc ω) 0 := by simp only [hHdef]
          have ht0 : (0 : ℝ) < t := lt_trans hSpos ht
          have hgt : t < A ω - 2 * Bc ω := by
            by_contra hcon
            push_neg at hcon
            have hle : max (A ω - 2 * Bc ω) 0 ≤ t := max_le hcon (le_of_lt ht0)
            rw [hHv] at hω'
            linarith
          have hthr : (1 / 2) * A ω + a + c39 * B1 ^ 2 * (u + 1) / ((n : ℝ) * (m : ℝ))
              = (1 / 2) * A ω + t / 2 := by
            have h1 : (c39 : ℝ) * B1 ^ 2 * (u + 1) / ((n : ℝ) * (m : ℝ)) = b * (u + 1) := by
              rw [hbdef]
              ring
            have h2 : b * (u + 1) = t / 2 - a := by
              rw [mul_add, hbu, mul_one]
              ring
            rw [h1, h2]
            ring
          have hlt : (1 / 2) * A ω + t / 2 < A ω - Bh ω := by linarith
          have habs : A ω - Bh ω ≤ |A ω - Bh ω| := le_abs_self _
          rw [hthr]
          linarith
        · exact Or.inr hbc
      calc mu {a : ΩS | t < H a}
          ≤ mu ({ω : ΩS | |A ω - Bh ω| > (1 / 2) * A ω + a
              + c39 * B1 ^ 2 * (u + 1) / ((n : ℝ) * (m : ℝ))}
            ∪ {ω : ΩS | ¬ (Bh ω ≤ Bc ω)}) := measure_mono hsub
        _ ≤ mu {ω : ΩS | |A ω - Bh ω| > (1 / 2) * A ω + a
              + c39 * B1 ^ 2 * (u + 1) / ((n : ℝ) * (m : ℝ))}
            + mu {ω : ΩS | ¬ (Bh ω ≤ Bc ω)} := measure_union_le _ _
        _ = mu {ω : ΩS | |A ω - Bh ω| > (1 / 2) * A ω + a
              + c39 * B1 ^ 2 * (u + 1) / ((n : ℝ) * (m : ℝ))} := by
            rw [hnull, add_zero]
        _ ≤ ENNReal.ofReal (Real.exp (-u)) := hdev'
        _ = ENNReal.ofReal (Real.exp 1 * Real.exp (-(t - 2 * a) / (2 * b))) := by
            rw [hexp, Real.exp_add]
    have hK_meas : AEMeasurable (fun ω : ΩS => max (H ω - S) 0) mu := by
      have h1 : AEMeasurable (fun ω : ΩS => H ω - S) mu :=
        hH_aesm.aemeasurable.sub aemeasurable_const
      first
      | exact h1.max aemeasurable_const
      | exact AEMeasurable.max h1 aemeasurable_const
      | exact h1.max measurable_const.aemeasurable
    have hK_nn : 0 ≤ᶠ[ae mu] fun ω : ΩS => max (H ω - S) 0 :=
      Filter.Eventually.of_forall (fun ω => le_max_right _ _)
    have hK_int : Integrable (fun ω : ΩS => max (H ω - S) 0) mu := by
      refine MeasureTheory.Integrable.of_bound hK_meas.aestronglyMeasurable (4 * B1 ^ 2) ?_
      filter_upwards [hA_le] with ω hle
      have h1 : max (H ω - S) 0 ≤ A ω := by
        have h2 : max (H ω - S) 0 ≤ H ω := max_le (by linarith) (hH_nn ω)
        linarith [hH_leA ω]
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      linarith
    have hK_lc : ∫⁻ ω, ENNReal.ofReal (max (H ω - S) 0) ∂mu
        = ∫⁻ t in Set.Ioi (0 : ℝ), mu {a : ΩS | t < max (H a - S) 0} :=
      MeasureTheory.lintegral_eq_lintegral_meas_lt mu hK_nn hK_meas
    have hmaj : ∀ t : ℝ, mu {a : ΩS | t < max (H a - S) 0}
        ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * b)) * t)) := by
      intro t
      by_cases ht0 : t ≤ 0
      · have h1 : mu {a : ΩS | t < max (H a - S) 0} ≤ (1 : ℝ≥0∞) := by
          have h2 : mu {a : ΩS | t < max (H a - S) 0} ≤ mu Set.univ :=
            measure_mono (Set.subset_univ _)
          rwa [measure_univ] at h2
        have h3 : (1 : ℝ) ≤ Real.exp (-(1 / (2 * b)) * t) := by
          apply Real.one_le_exp
          first
          | exact mul_nonneg_of_nonpos_of_nonpos (by linarith) ht0
          | nlinarith [hw, ht0]
        have h6 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * b)) * t)) := by
          rw [ENNReal.one_le_ofReal]
          exact h3
        exact le_trans h1 h6
      · push_neg at ht0
        have hset : {a : ΩS | t < max (H a - S) 0} = {a : ΩS | S + t < H a} := by
          ext x
          simp only [Set.mem_setOf_eq]
          constructor
          · intro h
            by_contra hc
            push_neg at hc
            have h1 : max (H x - S) 0 ≤ t := max_le (by linarith) (by linarith)
            linarith
          · intro h
            have h1 : t < H x - S := by linarith
            linarith [le_max_left (H x - S) 0]
        rw [hset]
        refine le_trans (htail (S + t) (by linarith)) ?_
        have h8 : Real.exp 1 * Real.exp (-(S + t - 2 * a) / (2 * b))
            ≤ Real.exp (-(1 / (2 * b)) * t) := by
          have hX : Real.exp 1 * Real.exp (-(S + t - 2 * a) / (2 * b))
              = Real.exp (-(1 / (2 * b)) * t) * Real.exp (1 - (S - 2 * a) / (2 * b)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            field_simp
            ring
          have hd : Real.exp (1 - (S - 2 * a) / (2 * b)) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            have hSa2 : 2 * a + 2 * b ≤ S := by
              rw [hSdef]
              linarith [le_max_right rstar (2 * a)]
            have h10 : 1 ≤ (S - 2 * a) / (2 * b) := (one_le_div hb2).mpr (by linarith)
            linarith
          rw [hX]
          calc Real.exp (-(1 / (2 * b)) * t) * Real.exp (1 - (S - 2 * a) / (2 * b))
              ≤ Real.exp (-(1 / (2 * b)) * t) * 1 :=
                mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
            _ = Real.exp (-(1 / (2 * b)) * t) := by ring
        exact ENNReal.ofReal_le_ofReal h8
    have hKb : ∫⁻ ω, ENNReal.ofReal (max (H ω - S) 0) ∂mu ≤ ENNReal.ofReal (2 * b) := by
      rw [hK_lc]
      have h2 : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(1 / (2 * b)) * t))
          = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 / (2 * b)) * t)) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (exp_neg_integrableOn_Ioi 0 hw)
          (Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le))]
      have h3 : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 / (2 * b)) * t) = 2 * b := by
        rw [integral_exp_mul_Ioi (by linarith : -(1 / (2 * b)) < 0) 0]
        have hbit : -(1 / (2 * b)) * 0 = 0 := by ring
        rw [hbit, Real.exp_zero]
        field_simp
      calc ∫⁻ t in Set.Ioi (0 : ℝ), mu {a : ΩS | t < max (H a - S) 0}
          ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(1 / (2 * b)) * t)) :=
            lintegral_mono (fun t => hmaj t)
        _ = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 / (2 * b)) * t)) := h2
        _ = ENNReal.ofReal (2 * b) := by rw [h3]
    have hKval : ∫ ω, max (H ω - S) 0 ∂mu ≤ 2 * b := by
      have h1 : ∫ ω, max (H ω - S) 0 ∂mu
          = (∫⁻ ω, ENNReal.ofReal (max (H ω - S) 0) ∂mu).toReal :=
        Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
          hK_nn hK_int
      rw [h1]
      calc (∫⁻ ω, ENNReal.ofReal (max (H ω - S) 0) ∂mu).toReal
          ≤ (ENNReal.ofReal (2 * b)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKb
        _ = 2 * b := ENNReal.toReal_ofReal (le_of_lt hb2)
    have hSint : Integrable (fun _ : ΩS => S) mu := by
      refine MeasureTheory.Integrable.of_bound measurable_const.aestronglyMeasurable |S| ?_
      filter_upwards with x
      exact le_of_eq (Real.norm_eq_abs S)
    have hSval : ∫ ω, (fun _ : ΩS => S) ω ∂mu = S := by
      rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
        (Filter.Eventually.of_forall (fun _ => le_of_lt hSpos)) hSint]
      rw [lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal (le_of_lt hSpos)]
    have hHK : ∫ ω, H ω ∂mu ≤ S + ∫ ω, max (H ω - S) 0 ∂mu := by
      have hpt : ∀ ω : ΩS, H ω ≤ (fun _ : ΩS => S) ω + max (H ω - S) 0 := by
        intro ω
        have h := le_max_left (H ω - S) 0
        linarith
      have hsum_int : Integrable (fun ω : ΩS => (fun _ : ΩS => S) ω + max (H ω - S) 0) mu :=
        hSint.add hK_int
      have hmono : ∫ ω, H ω ∂mu
          ≤ ∫ ω, (fun _ : ΩS => S) ω + max (H ω - S) 0 ∂mu := by
        first
        | exact integral_mono hpt hsum_int
        | exact integral_mono hH_int hpt
        | exact integral_mono hsum_int hpt
        | exact integral_mono_ae (Filter.Eventually.of_forall hpt) hsum_int
        | exact integral_mono_ae hH_int (Filter.Eventually.of_forall hpt)
        | exact integral_mono_ae hH_int hsum_int (Filter.Eventually.of_forall hpt)
      have hstep : ∫ ω, (fun _ : ΩS => S) ω + max (H ω - S) 0 ∂mu
          = (∫ ω, (fun _ : ΩS => S) ω ∂mu) + ∫ ω, max (H ω - S) 0 ∂mu :=
        integral_add hSint hK_int
      calc ∫ ω, H ω ∂mu ≤ ∫ ω, (fun _ : ΩS => S) ω + max (H ω - S) 0 ∂mu := hmono
        _ = (∫ ω, (fun _ : ΩS => S) ω ∂mu) + ∫ ω, max (H ω - S) 0 ∂mu := hstep
        _ = S + ∫ ω, max (H ω - S) 0 ∂mu := by rw [hSval]
    calc ∫ ω, H ω ∂mu ≤ S + ∫ ω, max (H ω - S) 0 ∂mu := hHK
      _ ≤ S + 2 * b := add_le_add_right hKval S
      _ = max rstar (2 * a) + 4 * b := by
          rw [hSdef]
          ring

  have hpt_all : ∀ ω, A ω ≤ (Bc + Bc + H) ω := by
    intro ω
    have h1 := le_max_left (A ω - 2 * Bc ω) 0
    have hval : (Bc + Bc + H) ω = Bc ω + Bc ω + H ω := rfl
    have hH : H ω = max (A ω - 2 * Bc ω) 0 := by simp only [hHdef]
    rw [hval, hH]
    linarith
  have hInt_rhs : Integrable (Bc + Bc + H) mu := (hBc_int.add hBc_int).add hH_int
  have hA_split : ∫ ω, A ω ∂mu
      ≤ (∫ ω, Bc ω ∂mu) + (∫ ω, Bc ω ∂mu) + ∫ ω, H ω ∂mu := by
    have hmono : ∫ ω, A ω ∂mu ≤ ∫ ω, (Bc + Bc + H) ω ∂mu := by
      first
      | exact integral_mono hpt_all hInt_rhs
      | exact integral_mono hA_int hpt_all
      | exact integral_mono hInt_rhs hpt_all
      | exact integral_mono_ae (Filter.Eventually.of_forall hpt_all) hInt_rhs
      | exact integral_mono_ae hA_int (Filter.Eventually.of_forall hpt_all)
      | exact integral_mono_ae hA_int hInt_rhs (Filter.Eventually.of_forall hpt_all)
    calc ∫ ω, A ω ∂mu ≤ ∫ ω, (Bc + Bc + H) ω ∂mu := hmono
      _ = (∫ ω, Bc ω ∂mu) + (∫ ω, Bc ω ∂mu) + ∫ ω, H ω ∂mu := by
          have hstep1 : ∫ ω, (Bc ω + Bc ω) + H ω ∂mu
              = (∫ ω, Bc ω + Bc ω ∂mu) + ∫ ω, H ω ∂mu :=
            integral_add (hBc_int.add hBc_int) hH_int
          have hstep2 : ∫ ω, Bc ω + Bc ω ∂mu
              = (∫ ω, Bc ω ∂mu) + ∫ ω, Bc ω ∂mu :=
            integral_add hBc_int hBc_int
          simp only [Pi.add_apply]
          rw [hstep1, hstep2]
  have hmaxeq : max rstar (2 * a) = max rstar (2 * c38 * B1 ^ 2 * rstar) := by
    rw [hadef]
    congr 1
    ring
  calc ∫ ω, A ω ∂mu ≤ (∫ ω, Bc ω ∂mu) + (∫ ω, Bc ω ∂mu) + ∫ ω, H ω ∂mu := hA_split
    _ = 2 * Q + ∫ ω, H ω ∂mu := by rw [hBc_eq_int]; ring
    _ ≤ 2 * Q + (max rstar (2 * a) + 4 * b) := add_le_add_right hKey (2 * Q)
    _ = 2 * Q + max rstar (2 * c38 * B1 ^ 2 * rstar)
          + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := by
        rw [hmaxeq, hbdef]
        ring_nf
  /- @proof-region region.target-node.session.879f8c0e813c5a13 end -/

end Statlib.Imported
end

