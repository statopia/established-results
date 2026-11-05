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
theorem statopia_math_node_4074864767_b4e01de1 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_nonneg : ∀ ω : Ω, 0 ≤ Z ω)
    (hZ_aesm : AEStronglyMeasurable Z μ)
    (hZ_int : Integrable Z μ)
    (hZ_pos : 0 < ∫ ω, Z ω ∂μ)
    (t : ℝ) (ht : 0 < t)
    (g : Ω → ℝ) (hg : ∀ ω : Ω, Z ω = Real.exp (t * g ω))
    (c : ℝ) (hc : Real.log (∫ ω, Z ω ∂μ) = t * c)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1),
    μ {ω : Ω | Z ω ≥ (∫ ω, Z ω ∂μ) / δ} ≤ ENNReal.ofReal δ ∧
      ∀ ω : Ω, ω ∈ {ω : Ω | Z ω ≥ (∫ ω, Z ω ∂μ) / δ}ᶜ →
        g ω ≤ c + t⁻¹ * Real.log (1 / δ) := by
  /- @proof-region region.target-node.session.7e681701338c8145 begin -/
  intro Ω _ μ _ Z hZ_nonneg hZ_aesm hZ_int hZ_pos t ht g hg c hc δ hδ0 hδ1
  constructor
  · have hdiv : (∫ ω, Z ω ∂μ) / ((∫ ω, Z ω ∂μ) / δ) = δ := by
      have ha : (∫ ω, Z ω ∂μ) ≠ 0 := ne_of_gt hZ_pos
      have hd : δ ≠ 0 := ne_of_gt hδ0
      field_simp
    have h := Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.meas_ge_le_ofReal_integral_div
      μ Z (Filter.Eventually.of_forall hZ_nonneg) hZ_int ((∫ ω, Z ω ∂μ) / δ) (div_pos hZ_pos hδ0)
    rw [hdiv] at h
    exact h
  · intro ω hω
    have hZlt : Z ω < (∫ ω, Z ω ∂μ) / δ := lt_of_not_ge hω
    have hZpos_pt : 0 < Z ω := by rw [hg ω]; exact Real.exp_pos _
    have hlog_lt : Real.log (Z ω) < Real.log ((∫ ω, Z ω ∂μ) / δ) :=
      Real.log_lt_log hZpos_pt hZlt
    have hlogZ : Real.log (Z ω) = t * g ω := by rw [hg ω, Real.log_exp]
    have hlogdiv : Real.log ((∫ ω, Z ω ∂μ) / δ) = t * c - Real.log δ := by
      rw [Real.log_div (ne_of_gt hZ_pos) (ne_of_gt hδ0), hc]
    rw [hlogZ, hlogdiv] at hlog_lt
    have htne : t ≠ 0 := ne_of_gt ht
    have hlog_inv : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    have hgt : g ω < c - t⁻¹ * Real.log δ := by
      have h2 : t * (g ω + t⁻¹ * Real.log δ) = t * g ω + Real.log δ := by
        rw [mul_add, ← mul_assoc, mul_inv_cancel₀ htne, one_mul]
      have h1 : t * (g ω + t⁻¹ * Real.log δ) < t * c := by
        rw [h2]; linarith
      have h3 : g ω + t⁻¹ * Real.log δ < c :=
        lt_of_mul_lt_mul_left h1 (le_of_lt ht)
      linarith
    rw [hlog_inv]
    linarith

  /- @proof-region region.target-node.session.7e681701338c8145 end -/

end
end Statlib.Imported
