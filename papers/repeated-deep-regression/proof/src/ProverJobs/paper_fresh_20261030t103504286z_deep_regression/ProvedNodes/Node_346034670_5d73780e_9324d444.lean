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
theorem statopia_math_node_346034670_5d73780e : ∀ {ΩS Ω : Type*} [MeasurableSpace ΩS] [MeasurableSpace Ω]
    (mu : Measure ΩS) [IsProbabilityMeasure mu]
    (PX : Measure Ω) [IsProbabilityMeasure PX]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (X : Fin n × Fin m → ΩS → Ω)
    (hX_meas : ∀ ij : Fin n × Fin m, Measurable (X ij))
    (hX_map : ∀ ij : Fin n × Fin m, Measure.map (X ij) mu = PX)
    (B1 : ℝ) (hB1 : 0 < B1)
    (fcirc : Ω → ℝ) (hfcirc_meas : Measurable fcirc)
    (hfcirc_bound : ∀ x : Ω, |fcirc x| ≤ B1)
    (g : Ω → ℝ) (hg_meas : Measurable g) (hg_bound : ∀ x : Ω, |g x| ≤ B1),
    let Bg : ΩS → ℝ := fun ω =>
      (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2
    let Q : ℝ := (∫⁻ x, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX).toReal
    Measurable Bg ∧ (∀ ω : ΩS, 0 ≤ Bg ω ∧ Bg ω ≤ 4 * B1 ^ 2) ∧ Integrable Bg mu ∧
      ∫ ω, Bg ω ∂mu = Q := by
  /- @proof-region region.target-node.session.967a6255966fc429 begin -/
  intro ΩS Ω _ _ mu _ PX _ n m hn hm X hX_meas hX_law B1 hB1 fcirc hfcirc_meas hfcirc_bound g
    hg_meas hg_bound
  dsimp only
  haveI hfin : IsFiniteMeasure mu := ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnm : (0 : ℝ) < (n : ℝ) * (m : ℝ) := mul_pos hn' hm'
  have hc_pos : (0 : ℝ) < 1 / ((n : ℝ) * (m : ℝ)) := div_pos one_pos hnm
  have hc_nonneg : (0 : ℝ) ≤ 1 / ((n : ℝ) * (m : ℝ)) := le_of_lt hc_pos
  have hΦ_meas : Measurable (fun x : Ω => ENNReal.ofReal ((g x - fcirc x) ^ 2)) := by
    have h2 : Measurable (fun x : Ω => g x - fcirc x) := hg_meas.sub hfcirc_meas
    have h3 : Measurable (fun x : Ω => (g x - fcirc x) ^ 2) := by
      simpa [pow_two] using h2.mul h2
    exact ENNReal.measurable_ofReal.comp h3
  have hterm : ∀ ij : Fin n × Fin m,
      Measurable (fun ω : ΩS => (g (X ij ω) - fcirc (X ij ω)) ^ 2) := by
    intro ij
    have h2 : Measurable (fun ω : ΩS => g (X ij ω) - fcirc (X ij ω)) :=
      (hg_meas.comp (hX_meas ij)).sub (hfcirc_meas.comp (hX_meas ij))
    simpa [pow_two] using h2.mul h2
  have hsum_meas : Measurable (fun ω : ΩS =>
      ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2) :=
    Finset.measurable_sum _ (fun ij _ => hterm ij)
  have hF_meas : Measurable (fun ω : ΩS => (1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2) :=
    hsum_meas.const_mul _
  have hpt : ∀ x : Ω, (g x - fcirc x) ^ 2 ≤ 4 * B1 ^ 2 := by
    intro x
    have h1 : |g x - fcirc x| ≤ 2 * B1 := by
      have hg1 := abs_le.mp (hg_bound x)
      have hf1 := abs_le.mp (hfcirc_bound x)
      rw [abs_le]
      constructor <;> nlinarith [hg1.1, hg1.2, hf1.1, hf1.2]
    rw [← sq_abs]
    nlinarith [h1, abs_nonneg (g x - fcirc x), hB1]
  have hF_nonneg : ∀ ω : ΩS, 0 ≤ (1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2 := by
    intro ω
    exact mul_nonneg hc_nonneg (Finset.sum_nonneg (fun ij _ => sq_nonneg _))
  have hF_upper : ∀ ω : ΩS, (1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2 ≤ 4 * B1 ^ 2 := by
    intro ω
    have hsum_le : (∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2)
        ≤ (n : ℝ) * (m : ℝ) * (4 * B1 ^ 2) := by
      calc (∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2)
          ≤ ∑ ij : Fin n × Fin m, 4 * B1 ^ 2 := Finset.sum_le_sum (fun ij _ => hpt (X ij ω))
        _ = (Finset.univ : Finset (Fin n × Fin m)).card • (4 * B1 ^ 2) :=
              Finset.sum_const (4 * B1 ^ 2)
        _ = ((n * m : ℕ) : ℝ) * (4 * B1 ^ 2) := by
              rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
                nsmul_eq_mul]
        _ = (n : ℝ) * (m : ℝ) * (4 * B1 ^ 2) := by
              push_cast
              ring
    calc (1 / ((n : ℝ) * (m : ℝ))) *
          (∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2)
        ≤ (1 / ((n : ℝ) * (m : ℝ))) * ((n : ℝ) * (m : ℝ) * (4 * B1 ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_le hc_nonneg
      _ = 4 * B1 ^ 2 := by
            have h1 : (1 / ((n : ℝ) * (m : ℝ))) * ((n : ℝ) * (m : ℝ)) = 1 := by
              rw [one_div, inv_mul_cancel₀ hnm.ne']
            calc (1 / ((n : ℝ) * (m : ℝ))) * ((n : ℝ) * (m : ℝ) * (4 * B1 ^ 2))
                = ((1 / ((n : ℝ) * (m : ℝ))) * ((n : ℝ) * (m : ℝ))) * (4 * B1 ^ 2) := by
                  ring
              _ = 4 * B1 ^ 2 := by rw [h1, one_mul]
  have hbound : ∀ ω : ΩS,
      0 ≤ (1 / ((n : ℝ) * (m : ℝ))) *
          ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2 ∧
      (1 / ((n : ℝ) * (m : ℝ))) *
          ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2 ≤ 4 * B1 ^ 2 :=
    fun ω => ⟨hF_nonneg ω, hF_upper ω⟩
  have hF_int : Integrable (fun ω : ΩS => (1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2) mu := by
    refine MeasureTheory.Integrable.of_bound hF_meas.aestronglyMeasurable (4 * B1 ^ 2) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg ω)]
    exact hF_upper ω
  have hsingle : ∀ ij : Fin n × Fin m,
      ∫⁻ ω : ΩS, ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu
        = ∫⁻ x : Ω, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX := by
    intro ij
    rw [← hX_law ij]
    exact (MeasureTheory.lintegral_map hΦ_meas (hX_meas ij)).symm
  have hterm_enn : ∀ ij : Fin n × Fin m,
      Measurable (fun ω : ΩS => ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2)) :=
    fun ij => hΦ_meas.comp (hX_meas ij)
  have hsum_enn_meas : Measurable (fun ω : ΩS =>
      ∑ ij : Fin n × Fin m, ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2)) :=
    Finset.measurable_sum _ (fun ij _ => hterm_enn ij)
  have hΦF : ∀ ω : ΩS, ENNReal.ofReal ((1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2)
      = ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) *
        ∑ ij : Fin n × Fin m, ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2) := by
    intro ω
    rw [ENNReal.ofReal_mul hc_nonneg,
      ENNReal.ofReal_sum_of_nonneg (fun ij _ => sq_nonneg _)]
  have hcard : (∑ ij : Fin n × Fin m,
        ∫⁻ x : Ω, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX)
      = ENNReal.ofReal ((n : ℝ) * (m : ℝ)) *
        ∫⁻ x : Ω, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, ← ENNReal.ofReal_natCast, Nat.cast_mul]
  have hnm_ne : ((n : ℝ) * (m : ℝ)) ≠ 0 := hnm.ne'
  have hcoef : ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) *
      ENNReal.ofReal ((n : ℝ) * (m : ℝ)) = 1 := by
    have h : 1 / ((n : ℝ) * (m : ℝ)) * ((n : ℝ) * (m : ℝ)) = 1 := by
      rw [one_div, inv_mul_cancel₀ hnm_ne]
    rw [← ENNReal.ofReal_mul hc_nonneg, h, ENNReal.ofReal_one]
  have hstep1 : ∫⁻ ω : ΩS, ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu
      = ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) * ∫⁻ ω : ΩS,
        ∑ ij : Fin n × Fin m, ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu := by
    simpa using (MeasureTheory.lintegral_const_mul
      (f := fun ω : ΩS => ∑ ij : Fin n × Fin m,
        ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2))
      (ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ)))) hsum_enn_meas)
  have hstep2 : ∫⁻ ω : ΩS, ∑ ij : Fin n × Fin m,
      ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu
      = ∑ ij : Fin n × Fin m,
        ∫⁻ ω : ΩS, ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu := by
    simpa using (MeasureTheory.lintegral_finset_sum (Finset.univ : Finset (Fin n × Fin m))
      (f := fun ij (ω : ΩS) => ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2))
      (fun ij _ => hterm_enn ij))
  have hlin : ∫⁻ ω : ΩS, ENNReal.ofReal ((1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu
      = ∫⁻ x : Ω, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX := by
    calc ∫⁻ ω : ΩS, ENNReal.ofReal ((1 / ((n : ℝ) * (m : ℝ))) *
          ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu
        = ∫⁻ ω : ΩS, ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) *
            ∑ ij : Fin n × Fin m,
              ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu := by
          simp only [hΦF]
      _ = ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) * (∫⁻ ω : ΩS,
            ∑ ij : Fin n × Fin m,
              ENNReal.ofReal ((g (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu) := hstep1
      _ = ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) *
            (∑ ij : Fin n × Fin m,
              ∫⁻ x : Ω, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX) := by
          rw [hstep2, Finset.sum_congr rfl (fun ij _ => hsingle ij)]
      _ = ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) *
            (ENNReal.ofReal ((n : ℝ) * (m : ℝ)) *
              ∫⁻ x : Ω, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX) := by
          rw [hcard]
      _ = (ENNReal.ofReal (1 / ((n : ℝ) * (m : ℝ))) *
            ENNReal.ofReal ((n : ℝ) * (m : ℝ))) *
              ∫⁻ x : Ω, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX := by
          rw [mul_assoc]
      _ = ∫⁻ x : Ω, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX := by
          rw [hcoef, one_mul]
  refine ⟨hF_meas, hbound, hF_int, ?_⟩
  have hnn : ∀ᵐ ω ∂mu, 0 ≤ (1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2 :=
    Filter.Eventually.of_forall hF_nonneg
  calc ∫ ω : ΩS, (1 / ((n : ℝ) * (m : ℝ))) *
        ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2 ∂mu
      = (∫⁻ ω : ΩS, ENNReal.ofReal ((1 / ((n : ℝ) * (m : ℝ))) *
          ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2) ∂mu).toReal :=
        Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
          hnn hF_int
    _ = (∫⁻ x : Ω, ENNReal.ofReal ((g x - fcirc x) ^ 2) ∂PX).toReal := by
        rw [hlin]
  /- @proof-region region.target-node.session.967a6255966fc429 end -/

end Statlib.Imported
end

