import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4201298820_65915b46_bda39e24
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
theorem statopia_math_node_1496902400_516b8071 : ∀ {Θ U : Type*} [MeasurableSpace Θ] [MeasurableSpace U]
    (m : Measure Θ) (kap : Θ → Measure U)
    (hker : Measurable fun θ : Θ => Measure.map (fun u : U => (θ, u)) (kap θ))
    (f : Θ → U → ℝ) (hf : Measurable (Function.uncurry f))
    (hfib : ∀ θ : Θ, Integrable (f θ) (kap θ))
    (Hint : Integrable (fun x : Θ × U => f x.1 x.2)
      (m.bind fun θ : Θ => Measure.map (fun u : U => (θ, u)) (kap θ))),
    Integrable (fun θ : Θ => ∫ u, f θ u ∂(kap θ)) m ∧
    (∫ x : Θ × U, f x.1 x.2 ∂(m.bind fun θ : Θ => Measure.map (fun u : U => (θ, u)) (kap θ))
      = ∫ θ : Θ, (∫ u, f θ u ∂(kap θ)) ∂m) := by
  /- @proof-region region.target-node.session.cc7c5ffcfa473bf3 begin -/
  classical
  intro Θ U _ _ m kap hker f hf hfib Hint
  let K : Θ → Measure (Θ × U) := fun θ => Measure.map (fun u : U => (θ, u)) (kap θ)
  have hKmeas : Measurable K := hker
  let A : Θ → ℝ≥0∞ := fun θ => ∫⁻ u, ENNReal.ofReal (f θ u) ∂(kap θ)
  let B : Θ → ℝ≥0∞ := fun θ => ∫⁻ u, ENNReal.ofReal (-(f θ u)) ∂(kap θ)
  let E : Θ → ℝ≥0∞ := fun θ => ∫⁻ u, ‖f θ u‖ₑ ∂(kap θ)
  let E₂ : Θ → ℝ≥0∞ := fun θ => ∫⁻ u, ‖-(f θ u)‖ₑ ∂(kap θ)
  have hFubini : ∀ G : Θ × U → ℝ≥0∞, Measurable G →
      ∫⁻ x, G x ∂(m.bind K) = ∫⁻ θ, ∫⁻ u, G (θ, u) ∂(kap θ) ∂m := by
    intro G hG
    rw [Measure.lintegral_bind hKmeas.aemeasurable hG.aemeasurable]
    exact lintegral_congr fun θ => lintegral_map hG (measurable_prodMk_left (x := θ))
  have hEnorm_meas : Measurable (fun x : Θ × U => ‖f x.1 x.2‖ₑ) := hf.enorm
  have hEnorm₂_meas : Measurable (fun x : Θ × U => ‖-(f x.1 x.2)‖ₑ) := hf.neg.enorm
  have hAE : ∀ θ, A θ ≤ E θ := fun θ =>
    MeasureTheory.lintegral_ofReal_le_lintegral_enorm (μ := kap θ) (fun u => f θ u)
  have hBE : ∀ θ, B θ ≤ E₂ θ := fun θ =>
    MeasureTheory.lintegral_ofReal_le_lintegral_enorm (μ := kap θ) (fun u => -(f θ u))
  have hEfin : ∫⁻ θ, E θ ∂m ≠ ⊤ := by
    have hb : ∫⁻ x : Θ × U, ‖f x.1 x.2‖ₑ ∂(m.bind K) < ⊤ := by
      simpa only [HasFiniteIntegral] using Hint.2
    have hEq : ∫⁻ θ, E θ ∂m = ∫⁻ x : Θ × U, ‖f x.1 x.2‖ₑ ∂(m.bind K) :=
      (hFubini (fun x : Θ × U => ‖f x.1 x.2‖ₑ) hEnorm_meas).symm
    rw [hEq]
    exact ne_of_lt hb
  have hE₂fin : ∫⁻ θ, E₂ θ ∂m ≠ ⊤ := by
    have hb : ∫⁻ x : Θ × U, ‖-(f x.1 x.2)‖ₑ ∂(m.bind K) < ⊤ := by
      simpa only [HasFiniteIntegral] using (Hint.neg).2
    have hEq : ∫⁻ θ, E₂ θ ∂m = ∫⁻ x : Θ × U, ‖-(f x.1 x.2)‖ₑ ∂(m.bind K) :=
      (hFubini (fun x : Θ × U => ‖-(f x.1 x.2)‖ₑ) hEnorm₂_meas).symm
    rw [hEq]
    exact ne_of_lt hb
  have hAfin : ∫⁻ θ, A θ ∂m ≠ ⊤ := ne_top_of_le_ne_top hEfin (lintegral_mono hAE)
  have hBfin : ∫⁻ θ, B θ ∂m ≠ ⊤ := ne_top_of_le_ne_top hE₂fin (lintegral_mono hBE)
  have hAne : ∀ᵐ θ ∂m, A θ ≠ ⊤ := Filter.Eventually.of_forall fun θ =>
    ne_of_lt (lt_of_le_of_lt (hAE θ) (by simpa only [HasFiniteIntegral] using (hfib θ).2))
  have hBne : ∀ᵐ θ ∂m, B θ ≠ ⊤ := Filter.Eventually.of_forall fun θ =>
    ne_of_lt (lt_of_le_of_lt (hBE θ) (by simpa only [HasFiniteIntegral] using (hfib θ).neg.2))
  have hAmeas : Measurable A :=
    (statopia_math_node_4201298820_65915b46 m kap hker f hf hfib Hint).1
  have hAint : Integrable (fun θ => (A θ).toReal) m :=
    (statopia_math_node_4201298820_65915b46 m kap hker f hf hfib Hint).2
  have hAintegral : ∫ θ, (A θ).toReal ∂m = (∫⁻ θ, A θ ∂m).toReal := by
    have hcongr : ∫⁻ θ, ENNReal.ofReal ((A θ).toReal) ∂m = ∫⁻ θ, A θ ∂m :=
      lintegral_congr_ae (hAne.mono fun θ h => ENNReal.ofReal_toReal h)
    rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
      (Filter.Eventually.of_forall fun θ => ENNReal.toReal_nonneg) hAint, hcongr]
  have hBmeas : Measurable B :=
    (statopia_math_node_4201298820_65915b46 m kap hker (fun θ u => -(f θ u)) hf.neg
      (fun θ => (hfib θ).neg) Hint.neg).1
  have hBint : Integrable (fun θ => (B θ).toReal) m :=
    (statopia_math_node_4201298820_65915b46 m kap hker (fun θ u => -(f θ u)) hf.neg
      (fun θ => (hfib θ).neg) Hint.neg).2
  have hBintegral : ∫ θ, (B θ).toReal ∂m = (∫⁻ θ, B θ ∂m).toReal := by
    have hcongr : ∫⁻ θ, ENNReal.ofReal ((B θ).toReal) ∂m = ∫⁻ θ, B θ ∂m :=
      lintegral_congr_ae (hBne.mono fun θ h => ENNReal.ofReal_toReal h)
    rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
      (Filter.Eventually.of_forall fun θ => ENNReal.toReal_nonneg) hBint, hcongr]
  have hR : ∀ θ : Θ, ∫ u, f θ u ∂(kap θ) = (A θ).toReal - (B θ).toReal := fun θ =>
    MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hfib θ)
  refine ⟨?_, ?_⟩
  · exact (hAint.sub hBint).congr (Filter.Eventually.of_forall fun θ => (hR θ).symm)
  · have hL1 : ∫ x, f x.1 x.2 ∂(m.bind K)
        = (∫⁻ x, ENNReal.ofReal (f x.1 x.2) ∂(m.bind K)).toReal
          - (∫⁻ x, ENNReal.ofReal (-(f x.1 x.2)) ∂(m.bind K)).toReal :=
      MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part Hint
    have hL2 : ∫⁻ x, ENNReal.ofReal (f x.1 x.2) ∂(m.bind K) = ∫⁻ θ, A θ ∂m :=
      hFubini (fun x : Θ × U => ENNReal.ofReal (f x.1 x.2)) hf.ennreal_ofReal
    have hL3 : ∫⁻ x, ENNReal.ofReal (-(f x.1 x.2)) ∂(m.bind K) = ∫⁻ θ, B θ ∂m :=
      hFubini (fun x : Θ × U => ENNReal.ofReal (-(f x.1 x.2))) hf.neg.ennreal_ofReal
    have hRint : ∫ θ, (∫ u, f θ u ∂(kap θ)) ∂m = ∫ θ, ((A θ).toReal - (B θ).toReal) ∂m :=
      integral_congr_ae (Filter.Eventually.of_forall hR)
    have hsub : ∫ θ, ((A θ).toReal - (B θ).toReal) ∂m
        = ∫ θ, (A θ).toReal ∂m - ∫ θ, (B θ).toReal ∂m := integral_sub hAint hBint
    rw [hL1, hL2, hL3, hRint, hsub, hAintegral, hBintegral]
  /- @proof-region region.target-node.session.cc7c5ffcfa473bf3 end -/

end
end Statlib.Imported
