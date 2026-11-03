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
theorem statopia_math_node_3070932353_56484c4e : ∀ {ΩS Ω : Type*} [MeasurableSpace ΩS] [MeasurableSpace Ω]
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
              + c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ))}
        ≤ ENNReal.ofReal (Real.exp (-t))),
    ∀ f ∈ F,
      (∫ ω : ΩS, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
        ≤ 2 * (l2Err PX fcirc f).toReal + max rstar (2 * c38 * B1 ^ 2 * rstar)
          + 2 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := by
  /- @proof-region region.target-node.session.87478f9ae749b149 begin -/
  intro ΩS Ω _ _ mu _ PX _ n m hn hm X hX_meas hX_law B1 rstar c38 c39 hB1 hrstar hc38 hc39 fcirc hfcirc_meas hfcirc_bound F hF_meas hF_bound fhat hmem hA_meas hmin hdev f hf
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnm_pos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := mul_pos hnR hmR
  have hnm_ne : ((n : ℝ) * (m : ℝ)) ≠ 0 := ne_of_gt hnm_pos
  set A : ΩS → ℝ := fun ω => (l2Err PX fcirc (fhat ω)).toReal with hA
  set Bc : ΩS → ℝ := fun ω => (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2 with hBc
  set Bhat : ΩS → ℝ := fun ω => (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2 with hBhat
  set S : ℝ := max rstar (2 * c38 * B1 ^ 2 * rstar) with hS
  set b : ℝ := ((n : ℝ) * (m : ℝ)) / (2 * c39 * B1 ^ 2) with hb
  set H : ΩS → ℝ := fun ω => max (A ω - 2 * Bc ω) 0 with hH
  have hcoef_pos : 0 < 1 / ((n : ℝ) * (m : ℝ)) := one_div_pos.mpr hnm_pos
  have hb_pos : 0 < b := by rw [hb]; exact div_pos hnm_pos (by positivity)
  have hA_nonneg : ∀ ω, 0 ≤ A ω := by intro ω; rw [hA]; exact ENNReal.toReal_nonneg
  have hH_nonneg : ∀ ω, 0 ≤ H ω := by intro ω; rw [hH]; exact le_max_right _ _
  have hbc_nonneg : ∀ ω, 0 ≤ Bc ω := by intro ω; rw [hBc]; positivity
  have hA_le : ∀ᵐ ω ∂mu, A ω ≤ 4 * B1 ^ 2 := by
    filter_upwards [hmem] with ω hω
    have hbound : l2Err PX fcirc (fhat ω) ≤ ENNReal.ofReal (4 * B1 ^ 2) := by
      unfold l2Err
      calc ∫⁻ x, ENNReal.ofReal ((fhat ω x - fcirc x) ^ 2) ∂PX
          ≤ ∫⁻ x, ENNReal.ofReal (4 * B1 ^ 2) ∂PX := by
            apply lintegral_mono
            intro x
            apply ENNReal.ofReal_le_ofReal
            have h1 := abs_le.mp (hF_bound (fhat ω) hω x)
            have h2 := abs_le.mp (hfcirc_bound x)
            nlinarith [h1.1, h1.2, h2.1, h2.2]
        _ = ENNReal.ofReal (4 * B1 ^ 2) := by
            rw [lintegral_const, measure_univ, mul_one]
    calc A ω = (l2Err PX fcirc (fhat ω)).toReal := by rw [hA]
      _ ≤ (ENNReal.ofReal (4 * B1 ^ 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      _ = 4 * B1 ^ 2 := by rw [ENNReal.toReal_ofReal (by positivity)]
  have hBc_le : ∀ ω, Bc ω ≤ 4 * B1 ^ 2 := by
    intro ω
    rw [hBc]
    have hterm : ∀ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2 ≤ 4 * B1 ^ 2 := by
      intro ij
      have h1 := abs_le.mp (hF_bound f hf (X ij ω))
      have h2 := abs_le.mp (hfcirc_bound (X ij ω))
      nlinarith [h1.1, h1.2, h2.1, h2.2]
    have hsum : ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2
        ≤ ((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2) := by
      calc ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2
          ≤ ∑ _ij : Fin n × Fin m, (4 * B1 ^ 2) := Finset.sum_le_sum (fun ij _ => hterm ij)
        _ = ((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    calc 1 / ((n : ℝ) * (m : ℝ)) * ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2
        ≤ 1 / ((n : ℝ) * (m : ℝ)) * (((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hcoef_pos)
      _ = 4 * B1 ^ 2 := by rw [← mul_assoc, one_div, inv_mul_cancel₀ hnm_ne, one_mul]
  have h_intBc : ∫ ω, Bc ω ∂mu = (l2Err PX fcirc f).toReal := by
    have hf_meas : Measurable f := hF_meas f hf
    have hL_top : l2Err PX fcirc f ≠ ⊤ := by
      have hbdd : l2Err PX fcirc f ≤ ENNReal.ofReal (4 * B1 ^ 2) := by
        unfold l2Err
        calc ∫⁻ x, ENNReal.ofReal ((f x - fcirc x) ^ 2) ∂PX
            ≤ ∫⁻ x, ENNReal.ofReal (4 * B1 ^ 2) ∂PX := by
              apply lintegral_mono
              intro x
              apply ENNReal.ofReal_le_ofReal
              have h1 := abs_le.mp (hF_bound f hf x)
              have h2 := abs_le.mp (hfcirc_bound x)
              nlinarith [h1.1, h1.2, h2.1, h2.2]
          _ = ENNReal.ofReal (4 * B1 ^ 2) := by rw [lintegral_const, measure_univ, mul_one]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbdd
    have hφmeas : Measurable (fun x : Ω => ENNReal.ofReal ((f x - fcirc x) ^ 2)) := by
      have hsq : Measurable (fun x : Ω => (f x - fcirc x) ^ 2) := by
        have h1 : Measurable (fun x : Ω => f x - fcirc x) := hf_meas.sub hfcirc_meas
        simpa [pow_two] using h1.mul h1
      exact ENNReal.measurable_ofReal.comp hsq
    have hcard : (↑(n * m) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) * (m : ℝ)) := by
      rw [ENNReal.ofReal_mul (le_of_lt hnR), ENNReal.ofReal_natCast n, ENNReal.ofReal_natCast m, Nat.cast_mul]
    have hij : ∀ ij : Fin n × Fin m, ∫⁻ ω, ENNReal.ofReal ((f (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu = l2Err PX fcirc f := by
      intro ij
      have hmap := MeasureTheory.lintegral_map (μ := mu) (f := fun x : Ω => ENNReal.ofReal ((f x - fcirc x) ^ 2)) (g := X ij) hφmeas (hX_meas ij)
      rw [hX_law ij] at hmap
      exact hmap.symm
    have hgmeas : ∀ ij ∈ (Finset.univ : Finset (Fin n × Fin m)), Measurable (fun ω : ΩS => ENNReal.ofReal ((f (X ij ω) - fcirc (X ij ω)) ^ 2)) := by
      intro ij _
      exact hφmeas.comp (hX_meas ij)
    have hstep : ∫⁻ ω, (∑ ij : Fin n × Fin m, ENNReal.ofReal ((f (X ij ω) - fcirc (X ij ω)) ^ 2)) ∂mu
        = ENNReal.ofReal ((n : ℝ) * (m : ℝ)) * l2Err PX fcirc f := by
      rw [MeasureTheory.lintegral_finset_sum (Finset.univ) hgmeas]
      simp only [hij]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, hcard]
    have hBc_lintegral : ∫⁻ ω, ENNReal.ofReal (Bc ω) ∂mu = l2Err PX fcirc f := by
      have hBc_eq : ∀ ω : ΩS, ENNReal.ofReal (Bc ω)
          = ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m, ENNReal.ofReal ((f (X ij ω) - fcirc (X ij ω)) ^ 2) := by
        intro ω
        rw [hBc, ENNReal.ofReal_mul (le_of_lt hcoef_pos), ENNReal.ofReal_sum_of_nonneg (fun ij _ => sq_nonneg _)]
      have hGmeas : Measurable (fun ω : ΩS => ∑ ij : Fin n × Fin m, ENNReal.ofReal ((f (X ij ω) - fcirc (X ij ω)) ^ 2)) :=
        Finset.measurable_sum _ (fun ij _ => hφmeas.comp (hX_meas ij))
      have hconst : ∫⁻ ω, ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) * (∑ ij : Fin n × Fin m, ENNReal.ofReal ((f (X ij ω) - fcirc (X ij ω)) ^ 2)) ∂mu
          = ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) * ∫⁻ ω, (∑ ij : Fin n × Fin m, ENNReal.ofReal ((f (X ij ω) - fcirc (X ij ω)) ^ 2)) ∂mu := by
        rw [MeasureTheory.lintegral_const_mul]
        exact hGmeas
      simp only [hBc_eq]
      rw [hconst, hstep, ← mul_assoc]
      have hc1 : ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) * ENNReal.ofReal ((n : ℝ) * (m : ℝ)) = 1 := by
        rw [← ENNReal.ofReal_mul (le_of_lt hcoef_pos), show 1 / ((n : ℝ) * (m : ℝ)) * ((n : ℝ) * (m : ℝ)) = 1 from by rw [one_div, inv_mul_cancel₀ hnm_ne], ENNReal.ofReal_one]
      rw [hc1, one_mul]
    have hBc_aesm : AEStronglyMeasurable Bc mu := by
      have hcomp : ∀ ij : Fin n × Fin m, Measurable (fun ω : ΩS => (f (X ij ω) - fcirc (X ij ω)) ^ 2) := by
        intro ij
        have h1 : Measurable (fun ω : ΩS => f (X ij ω) - fcirc (X ij ω)) :=
          (hf_meas.comp (hX_meas ij)).sub (hfcirc_meas.comp (hX_meas ij))
        simpa [pow_two] using h1.mul h1
      have hsum_meas : Measurable (fun ω : ΩS => ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2) :=
        Finset.measurable_sum _ (fun ij _ => hcomp ij)
      have hBc_meas : Measurable Bc := by
        rw [hBc]
        exact hsum_meas.const_mul _
      exact hBc_meas.aestronglyMeasurable
    have hIntBc : Integrable Bc mu := by
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hBc_aesm (Filter.Eventually.of_forall hbc_nonneg)).mp ?_
      rw [hBc_lintegral]
      exact hL_top
    have htrans := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := Bc) hIntBc (Filter.Eventually.of_forall hbc_nonneg)
    have htrans2 : ENNReal.ofReal (∫ ω, Bc ω ∂mu) = l2Err PX fcirc f := by
      rw [← hBc_lintegral, htrans]
    have hInt_nonneg : 0 ≤ ∫ ω, Bc ω ∂mu := integral_nonneg (fun ω => hbc_nonneg ω)
    rw [← htrans2, ENNReal.toReal_ofReal hInt_nonneg]
  have htail : ∀ s : ℝ, S < s → mu {ω : ΩS | s < H ω} ≤ ENNReal.ofReal (Real.exp (-(b * (s - S)))) := by
    intro s hs
    have hrs : rstar ≤ S := by rw [hS]; exact le_max_left _ _
    have h2S : 2 * c38 * B1 ^ 2 * rstar ≤ S := by rw [hS]; exact le_max_right _ _
    set t : ℝ := (s - 2 * c38 * B1 ^ 2 * rstar) * b with ht_def
    have ht_pos : 0 < t := by
      rw [ht_def]
      have h1 : 0 < s - 2 * c38 * B1 ^ 2 * rstar := by linarith
      exact mul_pos h1 hb_pos
    have hfeq : 2 * (c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ))) = s := by
      rw [ht_def, hb]
      field_simp
      ring
    have hkappa : c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) = s / 2 := by linarith
    have hreg : rstar ≤ 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) := by
      have h2 : 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) = s := by
        rw [← hfeq]
        ring
      linarith [h2, hrs, hs]
    have hdev'' : mu {ω : ΩS | |A ω - Bhat ω| > A ω / 2 + s / 2} ≤ ENNReal.ofReal (Real.exp (-t)) := by
      have hset : {ω : ΩS | |A ω - Bhat ω| > A ω / 2 + s / 2}
          = {ω : ΩS | |(l2Err PX fcirc (fhat ω)).toReal - (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2| > (1 / 2) * (l2Err PX fcirc (fhat ω)).toReal + c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ))} := by
        ext ω
        simp only [Set.mem_setOf_eq, hA, hBhat]
        constructor <;> intro h <;> linarith [hkappa, h]
      rw [hset]
      exact hdev t ht_pos hreg
    have hN : mu {ω : ΩS | ¬ (Bhat ω ≤ Bc ω)} = 0 := by
      have hmin' : ∀ᵐ ω ∂mu, Bhat ω ≤ Bc ω := by
        filter_upwards [hmin] with ω hω
        rw [hBhat, hBc]
        exact hω f hf
      exact ae_iff.mp hmin'
    have hsub : {ω : ΩS | s < H ω} ⊆ {ω : ΩS | |A ω - Bhat ω| > A ω / 2 + s / 2} ∪ {ω : ΩS | ¬ (Bhat ω ≤ Bc ω)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      by_cases hle : Bhat ω ≤ Bc ω
      · left
        rw [hH] at hω
        have hs_pos : 0 < s := by linarith
        have hA2bc : s < A ω - 2 * Bc ω := by
          by_contra hcon
          rw [not_lt] at hcon
          have hle2 : max (A ω - 2 * Bc ω) 0 ≤ s := max_le hcon (le_of_lt hs_pos)
          linarith
        have hA2bhat : s < A ω - 2 * Bhat ω := by linarith
        have habs : |A ω - Bhat ω| ≥ A ω - Bhat ω := le_abs_self _
        have hstep1 : A ω / 2 + s / 2 < A ω - Bhat ω := by linarith [hA2bhat]
        exact lt_of_lt_of_le hstep1 habs
      · right; exact hle
    calc mu {ω : ΩS | s < H ω}
        ≤ mu ({ω : ΩS | |A ω - Bhat ω| > A ω / 2 + s / 2} ∪ {ω : ΩS | ¬ (Bhat ω ≤ Bc ω)}) := measure_mono hsub
      _ ≤ mu {ω : ΩS | |A ω - Bhat ω| > A ω / 2 + s / 2} + mu {ω : ΩS | ¬ (Bhat ω ≤ Bc ω)} := measure_union_le _ _
      _ = mu {ω : ΩS | |A ω - Bhat ω| > A ω / 2 + s / 2} := by rw [hN, add_zero]
      _ ≤ ENNReal.ofReal (Real.exp (-t)) := hdev''
      _ ≤ ENNReal.ofReal (Real.exp (-(b * (s - S)))) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have htb : b * (s - S) ≤ t := by
            rw [ht_def, mul_comm (s - 2 * c38 * B1 ^ 2 * rstar) b]
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hb_pos)
            linarith
          linarith
  have hBc_meas : Measurable Bc := by
    have hcomp : ∀ ij : Fin n × Fin m, Measurable (fun ω : ΩS => (f (X ij ω) - fcirc (X ij ω)) ^ 2) := by
      intro ij
      have h1 : Measurable (fun ω : ΩS => f (X ij ω) - fcirc (X ij ω)) :=
        ((hF_meas f hf).comp (hX_meas ij)).sub (hfcirc_meas.comp (hX_meas ij))
      simpa [pow_two] using h1.mul h1
    have hsum_meas : Measurable (fun ω : ΩS => ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2) :=
      Finset.measurable_sum _ (fun ij _ => hcomp ij)
    rw [hBc]
    exact hsum_meas.const_mul _
  have hIntBc' : Integrable Bc mu := by
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hBc_meas.aestronglyMeasurable (Filter.Eventually.of_forall hbc_nonneg)).mp ?_
    have hle : ∫⁻ ω, ENNReal.ofReal (Bc ω) ∂mu ≤ ENNReal.ofReal (4 * B1 ^ 2) := by
      calc ∫⁻ ω, ENNReal.ofReal (Bc ω) ∂mu
          ≤ ∫⁻ ω, ENNReal.ofReal (4 * B1 ^ 2) ∂mu := by
            apply lintegral_mono
            intro ω
            exact ENNReal.ofReal_le_ofReal (hBc_le ω)
        _ = ENNReal.ofReal (4 * B1 ^ 2) := by rw [lintegral_const, measure_univ, mul_one]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hA_int : Integrable A mu := by
    refine MeasureTheory.Integrable.of_bound hA_meas.aestronglyMeasurable (4 * B1 ^ 2) ?_
    filter_upwards [hA_le] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hA_nonneg ω)]
    exact hω
  have hH_meas : AEMeasurable H mu := by
    rw [hH]
    exact AEMeasurable.max (hA_meas.sub (hBc_meas.const_mul 2).aemeasurable) aemeasurable_const
  have hH_int_int : Integrable H mu := by
    refine MeasureTheory.Integrable.of_bound hH_meas.aestronglyMeasurable (4 * B1 ^ 2) ?_
    filter_upwards [hA_le] with ω hω
    have hHA : H ω ≤ A ω := by
      rw [hH]
      exact max_le (by linarith [hbc_nonneg ω]) (hA_nonneg ω)
    rw [Real.norm_eq_abs, abs_of_nonneg (hH_nonneg ω)]
    linarith
  have hS_pos : 0 < S := by rw [hS]; exact lt_of_lt_of_le hrstar (le_max_left _ _)
  have hH_ae : ∀ᵐ ω ∂mu, 0 ≤ H ω := Filter.Eventually.of_forall hH_nonneg
  have hH_int : ∫ ω, H ω ∂mu ≤ S + 1 / b := by
    have hlc : ∫⁻ ω, ENNReal.ofReal (H ω) ∂mu = ∫⁻ t in Set.Ioi (0 : ℝ), mu {ω : ΩS | t < H ω} :=
      MeasureTheory.lintegral_eq_lintegral_meas_lt mu hH_ae hH_meas
    have hsplit : ∫⁻ t in Set.Ioi (0 : ℝ), mu {ω : ΩS | t < H ω} ≤ ENNReal.ofReal (S + 1 / b) := by
      have hprob : ∀ s : Set ΩS, mu s ≤ 1 := fun s => le_trans (measure_mono (Set.subset_univ s)) (le_of_eq measure_univ)
      have hIoc_bound : ∫⁻ t in Set.Ioc (0 : ℝ) S, mu {ω : ΩS | t < H ω} ≤ ENNReal.ofReal S := by
        calc ∫⁻ t in Set.Ioc (0 : ℝ) S, mu {ω : ΩS | t < H ω}
            ≤ ∫⁻ t in Set.Ioc (0 : ℝ) S, (1 : ENNReal) := by
              apply lintegral_mono
              intro t
              exact hprob _
          _ = ENNReal.ofReal S := by
              rw [lintegral_const, one_mul, Measure.restrict_apply, Set.univ_inter, Real.volume_Ioc]
              all_goals simp
      have hexp_int : ∫ t in Set.Ioi S, Real.exp ((-b) * t) = -Real.exp ((-b) * S) / (-b) :=
        integral_exp_mul_Ioi (by linarith : -b < 0) S
      have hval_ne : -Real.exp ((-b) * S) / (-b) ≠ 0 := by
        have h1 : -Real.exp ((-b) * S) / (-b) = Real.exp ((-b) * S) / b := by
          rw [neg_div_neg_eq]
        rw [h1]
        exact div_ne_zero (Real.exp_pos _).ne' (ne_of_gt hb_pos)
      have hIntExp : Integrable (fun x : ℝ => Real.exp ((-b) * x)) (volume.restrict (Set.Ioi S)) := by
        by_contra h
        rw [MeasureTheory.integral_undef h] at hexp_int
        exact hval_ne hexp_int.symm
      have hIntG : Integrable (fun t : ℝ => Real.exp (-(b * (t - S)))) (volume.restrict (Set.Ioi S)) := by
        refine (hIntExp.const_mul (Real.exp (b * S))).congr ?_
        filter_upwards with t
        show Real.exp (b * S) * Real.exp ((-b) * t) = Real.exp (-(b * (t - S)))
        rw [← Real.exp_add]
        congr 1
        ring
      have hreal : ∫ t in Set.Ioi S, Real.exp (-(b * (t - S))) = 1 / b := by
        have hpt : ∀ t : ℝ, Real.exp (-(b * (t - S))) = Real.exp (b * S) * Real.exp ((-b) * t) := by
          intro t
          rw [← Real.exp_add]
          congr 1
          ring
        simp only [hpt]
        rw [MeasureTheory.integral_const_mul, hexp_int]
        have hE : Real.exp (b * S) * Real.exp ((-b) * S) = 1 := by
          rw [← Real.exp_add, show b * S + (-b) * S = (0 : ℝ) from by ring, Real.exp_zero]
        rw [show Real.exp (b * S) * (-Real.exp ((-b) * S) / (-b)) = Real.exp (b * S) * Real.exp ((-b) * S) / b from by
          rw [neg_div_neg_eq]; ring]
        rw [hE]
      have hlin : ∫⁻ t in Set.Ioi S, ENNReal.ofReal (Real.exp (-(b * (t - S)))) = ENNReal.ofReal (1 / b) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := fun t : ℝ => Real.exp (-(b * (t - S)))) hIntG (Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le))]
        rw [hreal]
      have hpt_bound : ∀ t : ℝ, mu {ω : ΩS | t < H ω} ≤ ENNReal.ofReal (Real.exp (-(b * (t - S)))) := by
        intro t
        by_cases hle : t ≤ S
        · have hbS : b * (t - S) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb_pos) (by linarith)
          have hexp_ge : 1 ≤ Real.exp (-(b * (t - S))) := by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (neg_nonneg.mpr hbS)
          calc mu {ω | t < H ω} ≤ 1 := hprob _
            _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
            _ ≤ ENNReal.ofReal (Real.exp (-(b * (t - S)))) := ENNReal.ofReal_le_ofReal hexp_ge
        · exact htail t (not_le.mp hle)
      have hIoi_bound : ∫⁻ t in Set.Ioi S, mu {ω : ΩS | t < H ω} ≤ ENNReal.ofReal (1 / b) := by
        calc ∫⁻ t in Set.Ioi S, mu {ω : ΩS | t < H ω}
            ≤ ∫⁻ t in Set.Ioi S, ENNReal.ofReal (Real.exp (-(b * (t - S)))) := by
              apply lintegral_mono
              intro t
              exact hpt_bound t
          _ = ENNReal.ofReal (1 / b) := hlin
      have hset : Set.Ioi (0 : ℝ) = Set.Ioc 0 S ∪ Set.Ioi S := by
        ext t
        simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
        constructor
        · intro ht
          by_cases h : t ≤ S
          · exact Or.inl ⟨ht, h⟩
          · exact Or.inr (not_le.mp h)
        · rintro (⟨ht, _⟩ | h)
          · exact ht
          · linarith [hS_pos]
      have hdisj : Disjoint (Set.Ioc (0 : ℝ) S) (Set.Ioi S) := by
        rw [Set.disjoint_left]
        intro a ha1 ha2
        simp only [Set.mem_Ioc] at ha1
        simp only [Set.mem_Ioi] at ha2
        linarith [ha1.2, ha2]
      rw [hset, MeasureTheory.lintegral_union (A := Set.Ioc (0 : ℝ) S) (B := Set.Ioi S) measurableSet_Ioi hdisj]
      calc (∫⁻ t in Set.Ioc (0 : ℝ) S, mu {ω : ΩS | t < H ω}) + (∫⁻ t in Set.Ioi S, mu {ω : ΩS | t < H ω})
          ≤ ENNReal.ofReal S + ENNReal.ofReal (1 / b) := add_le_add hIoc_bound hIoi_bound
        _ = ENNReal.ofReal (S + 1 / b) := by
            rw [ENNReal.ofReal_add (le_of_lt hS_pos) (le_of_lt (one_div_pos.mpr hb_pos))]
    have hbound : ∫⁻ ω, ENNReal.ofReal (H ω) ∂mu ≤ ENNReal.ofReal (S + 1 / b) := by
      rw [hlc]
      exact hsplit
    have htrans := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := H) hH_int_int hH_ae
    have h1 : ENNReal.ofReal (∫ ω, H ω ∂mu) ≤ ENNReal.ofReal (S + 1 / b) := by
      rw [htrans]
      exact hbound
    have h2 : (ENNReal.ofReal (∫ ω, H ω ∂mu)).toReal ≤ (ENNReal.ofReal (S + 1 / b)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    have hIH : 0 ≤ ∫ ω, H ω ∂mu := integral_nonneg hH_nonneg
    have hS1b : 0 ≤ S + 1 / b := by
      apply add_nonneg (le_of_lt hS_pos)
      exact le_of_lt (one_div_pos.mpr hb_pos)
    rw [ENNReal.toReal_ofReal hIH, ENNReal.toReal_ofReal hS1b] at h2
    exact h2
  have hkey : ∫ ω, A ω ∂mu ≤ 2 * (l2Err PX fcirc f).toReal + S + 1 / b := by
    have h2_int : Integrable (fun ω : ΩS => 2 * Bc ω) mu := hIntBc'.const_mul 2
    have hsub_int : Integrable (fun ω : ΩS => A ω - 2 * Bc ω) mu := hA_int.sub h2_int
    have hid : ∫ ω, A ω ∂mu = ∫ ω, (A ω - 2 * Bc ω) ∂mu + 2 * ∫ ω, Bc ω ∂mu := by
      have e1 : ∫ ω, (A ω - 2 * Bc ω) ∂mu = ∫ ω, A ω ∂mu - ∫ ω, (2 * Bc ω) ∂mu :=
        integral_sub hA_int h2_int
      have e2 : ∫ ω, (2 * Bc ω) ∂mu = 2 * ∫ ω, Bc ω ∂mu := by
        have hc : (fun ω : ΩS => 2 * Bc ω) = (fun ω => Bc ω + Bc ω) := by funext ω; ring
        rw [hc, integral_add hIntBc' hIntBc']; ring
      linarith [e1, e2]
    have hmono : ∫ ω, (A ω - 2 * Bc ω) ∂mu ≤ ∫ ω, H ω ∂mu := by
      apply MeasureTheory.integral_mono hsub_int hH_int_int
      intro ω
      rw [hH]
      exact le_max_left _ _
    have hQ : ∫ ω, Bc ω ∂mu = (l2Err PX fcirc f).toReal := h_intBc
    linarith [hid, hmono, hH_int, hQ]
  change ∫ ω, A ω ∂mu ≤ 2 * (l2Err PX fcirc f).toReal + max rstar (2 * c38 * B1 ^ 2 * rstar) + 2 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ))
  have h1b : 1 / b = 2 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := by rw [hb]; field_simp
  calc ∫ ω, A ω ∂mu ≤ 2 * (l2Err PX fcirc f).toReal + S + 1 / b := hkey
    _ = 2 * (l2Err PX fcirc f).toReal + max rstar (2 * c38 * B1 ^ 2 * rstar) + 2 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := by rw [hS, h1b]
  /- @proof-region region.target-node.session.87478f9ae749b149 end -/

end Statlib.Imported
end

