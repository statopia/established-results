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
theorem statopia_math_node_4026486579_064ccf6a : ∀ (E : Type*) [MeasurableSpace E] (P : Measure E) [SigmaFinite P]
    (g1 g2 : E → ℝ≥0∞) (hg1 : Measurable g1) (hg2 : Measurable g2)
    (hg1_int : ∫⁻ u, g1 u ∂P = 1) (hg2_int : ∫⁻ u, g2 u ∂P = 1),
    hellingerDist (P.withDensity g1) (P.withDensity g2) =
      Real.sqrt ((1 / 2 : ℝ) *
        (∫⁻ u, ENNReal.ofReal ((Real.sqrt ((g1 u).toReal) -
          Real.sqrt ((g2 u).toReal)) ^ 2) ∂P).toReal) := by
  /- @proof-region region.target-node.session.397becaa99f1447e begin -/
  intro E _ P _ g1 g2 hg1 hg2 hg1_int hg2_int
  set H : E → ℝ≥0∞ := fun u => g1 u + g2 u with hHdef
  have hH_meas : Measurable H := by rw [hHdef]; exact hg1.add hg2
  have h1 : ∀ᵐ x ∂P, g1 x < ⊤ := MeasureTheory.ae_lt_top hg1 (by rw [hg1_int]; norm_num)
  have h2 : ∀ᵐ x ∂P, g2 x < ⊤ := MeasureTheory.ae_lt_top hg2 (by rw [hg2_int]; norm_num)
  have hH_lt : ∀ᵐ x ∂P, H x < ⊤ := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hHdef]
    exact ENNReal.add_lt_top.mpr ⟨hx1, hx2⟩
  have hLam : (P.withDensity g1) + (P.withDensity g2) = P.withDensity H := by
    rw [hHdef]
    exact (MeasureTheory.withDensity_add_left hg1 g2).symm
  haveI hfin1 : IsFiniteMeasure (P.withDensity g1) := MeasureTheory.isFiniteMeasure_withDensity (by rw [hg1_int]; norm_num)
  haveI hfin2 : IsFiniteMeasure (P.withDensity g2) := MeasureTheory.isFiniteMeasure_withDensity (by rw [hg2_int]; norm_num)
  haveI hS1 : SigmaFinite (P.withDensity g1) := inferInstance
  haveI hS2 : SigmaFinite (P.withDensity g2) := inferInstance
  haveI hSsum : SigmaFinite ((P.withDensity g1) + (P.withDensity g2)) := inferInstance
  set d1 : E → ℝ≥0∞ := fun x => g1 x / H x with hd1def
  set d2 : E → ℝ≥0∞ := fun x => g2 x / H x with hd2def
  have hd1_meas : Measurable d1 := by rw [hd1def]; exact hg1.div hH_meas
  have hd2_meas : Measurable d2 := by rw [hd2def]; exact hg2.div hH_meas
  have hmul1 : H * d1 =ᵐ[P] g1 := by
    filter_upwards [hH_lt] with x hx
    have hg1le : g1 x ≤ H x := by
      rw [hHdef]; simpa using add_le_add_left (zero_le (g2 x)) (g1 x)
    by_cases h0 : H x = 0
    · have hg1x0 : g1 x = 0 := by rw [h0] at hg1le; exact le_antisymm hg1le (zero_le _)
      change H x * (g1 x / H x) = g1 x
      rw [h0, hg1x0]; simp
    · change H x * (g1 x / H x) = g1 x
      rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.mul_inv_cancel h0 hx.ne, one_mul]
  have hmul2 : H * d2 =ᵐ[P] g2 := by
    filter_upwards [hH_lt] with x hx
    have hg2le : g2 x ≤ H x := by
      rw [hHdef]; simpa using add_le_add_right (zero_le (g1 x)) (g2 x)
    by_cases h0 : H x = 0
    · have hg2x0 : g2 x = 0 := by rw [h0] at hg2le; exact le_antisymm hg2le (zero_le _)
      change H x * (g2 x / H x) = g2 x
      rw [h0, hg2x0]; simp
    · change H x * (g2 x / H x) = g2 x
      rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.mul_inv_cancel h0 hx.ne, one_mul]
  have hν1 : (P.withDensity g1) = ((P.withDensity g1) + (P.withDensity g2)).withDensity d1 := by
    rw [hLam, ← MeasureTheory.withDensity_mul P hH_meas hd1_meas, MeasureTheory.withDensity_congr_ae hmul1]
  have hν2 : (P.withDensity g2) = ((P.withDensity g1) + (P.withDensity g2)).withDensity d2 := by
    rw [hLam, ← MeasureTheory.withDensity_mul P hH_meas hd2_meas, MeasureTheory.withDensity_congr_ae hmul2]
  have hrn1 : (P.withDensity g1).rnDeriv ((P.withDensity g1) + (P.withDensity g2)) =ᵐ[((P.withDensity g1) + (P.withDensity g2))] fun x => g1 x / H x := by
    have hbase := Measure.rnDeriv_withDensity ((P.withDensity g1) + (P.withDensity g2)) hd1_meas
    rw [← hν1] at hbase
    exact hbase
  have hrn2 : (P.withDensity g2).rnDeriv ((P.withDensity g1) + (P.withDensity g2)) =ᵐ[((P.withDensity g1) + (P.withDensity g2))] fun x => g2 x / H x := by
    have hbase := Measure.rnDeriv_withDensity ((P.withDensity g1) + (P.withDensity g2)) hd2_meas
    rw [← hν2] at hbase
    exact hbase
  set Phi : E → ℝ≥0∞ := fun x => ENNReal.ofReal ((Real.sqrt ((g1 x / H x).toReal) - Real.sqrt ((g2 x / H x).toReal)) ^ 2) with hPhidef
  have hPhi_meas : Measurable Phi := by
    have hm1 : Measurable (fun x => (g1 x / H x).toReal) := (hg1.div hH_meas).ennreal_toReal
    have hm2 : Measurable (fun x => (g2 x / H x).toReal) := (hg2.div hH_meas).ennreal_toReal
    have hsq : Measurable (fun x => (Real.sqrt ((g1 x / H x).toReal) - Real.sqrt ((g2 x / H x).toReal)) ^ 2) :=
      (Measurable.sub (Real.continuous_sqrt.measurable.comp hm1)
        (Real.continuous_sqrt.measurable.comp hm2)).pow_const 2
    exact ENNReal.measurable_ofReal.comp hsq
  have hpt : (H * Phi) =ᵐ[P] fun u => ENNReal.ofReal ((Real.sqrt ((g1 u).toReal) - Real.sqrt ((g2 u).toReal)) ^ 2) := by

    filter_upwards [hH_lt, h1, h2] with x hx hx1 hx2
    change H x * Phi x = ENNReal.ofReal ((Real.sqrt ((g1 x).toReal) - Real.sqrt ((g2 x).toReal)) ^ 2)
    have hH_toReal : ENNReal.ofReal (H x).toReal = H x := ENNReal.ofReal_toReal hx.ne
    rw [← hH_toReal, hPhidef, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    congr 1
    rw [ENNReal.toReal_div, ENNReal.toReal_div]
    have hsub : (H x).toReal = (g1 x).toReal + (g2 x).toReal := by
      rw [hHdef]; exact ENNReal.toReal_add hx1.ne hx2.ne
    rw [hsub]
    set a := (g1 x).toReal with ha
    set b := (g2 x).toReal with hb
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
    rcases eq_or_ne (a + b) 0 with hs0 | hs0
    · have hae : a = 0 := by nlinarith
      have hbe : b = 0 := by nlinarith
      rw [hae, hbe]; simp
    · have hs : 0 ≤ a + b := by positivity
      rw [Real.sqrt_div ha0 (a + b), Real.sqrt_div hb0 (a + b), ← sub_div, div_pow, Real.sq_sqrt hs]
      field_simp
  have e1 : (∫⁻ x, ENNReal.ofReal ((Real.sqrt (((P.withDensity g1).rnDeriv ((P.withDensity g1) + (P.withDensity g2))) x).toReal - Real.sqrt (((P.withDensity g2).rnDeriv ((P.withDensity g1) + (P.withDensity g2))) x).toReal) ^ 2) ∂((P.withDensity g1) + (P.withDensity g2)))
      = ∫⁻ x, Phi x ∂((P.withDensity g1) + (P.withDensity g2)) := by
    apply lintegral_congr_ae
    filter_upwards [hrn1, hrn2] with x hx1 hx2
    rw [hx1, hx2]
  have e2 : (∫⁻ x, Phi x ∂((P.withDensity g1) + (P.withDensity g2))) = ∫⁻ x, (H * Phi) x ∂P := by
    rw [hLam]
    exact lintegral_withDensity_eq_lintegral_mul P hH_meas hPhi_meas
  have e3 : (∫⁻ x, (H * Phi) x ∂P) = ∫⁻ u, ENNReal.ofReal ((Real.sqrt ((g1 u).toReal) - Real.sqrt ((g2 u).toReal)) ^ 2) ∂P := by
    apply lintegral_congr_ae
    simpa using hpt
  have hint : (∫⁻ x, ENNReal.ofReal ((Real.sqrt (((P.withDensity g1).rnDeriv ((P.withDensity g1) + (P.withDensity g2))) x).toReal - Real.sqrt (((P.withDensity g2).rnDeriv ((P.withDensity g1) + (P.withDensity g2))) x).toReal) ^ 2) ∂((P.withDensity g1) + (P.withDensity g2)))
      = ∫⁻ u, ENNReal.ofReal ((Real.sqrt ((g1 u).toReal) - Real.sqrt ((g2 u).toReal)) ^ 2) ∂P := by
    rw [e1, e2, e3]
  unfold hellingerDist
  simp only [hint]
  /- @proof-region region.target-node.session.397becaa99f1447e end -/

end Statlib.Imported
end

