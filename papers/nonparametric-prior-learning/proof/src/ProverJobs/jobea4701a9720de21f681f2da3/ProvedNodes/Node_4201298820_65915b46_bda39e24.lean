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
theorem statopia_math_node_4201298820_65915b46 : ∀ {Θ U : Type*} [MeasurableSpace Θ] [MeasurableSpace U]
    (m : Measure Θ) (kap : Θ → Measure U)
    (hker : Measurable fun θ : Θ => Measure.map (fun u : U => (θ, u)) (kap θ))
    (f : Θ → U → ℝ) (hf : Measurable (Function.uncurry f))
    (hfib : ∀ θ : Θ, Integrable (f θ) (kap θ))
    (Hint : Integrable (fun x : Θ × U => f x.1 x.2)
      (m.bind fun θ : Θ => Measure.map (fun u : U => (θ, u)) (kap θ))),
    Measurable (fun θ : Θ => ∫⁻ u, ENNReal.ofReal (f θ u) ∂(kap θ)) ∧
    Integrable (fun θ : Θ => (∫⁻ u, ENNReal.ofReal (f θ u) ∂(kap θ)).toReal) m := by
  /- @proof-region region.target-node.session.e462a4f8ccf30d21 begin -/
  intro Θ U _ _ m kap hker f hf hfib Hint
  have hg_meas : Measurable fun x : Θ × U => ENNReal.ofReal (f x.1 x.2) := hf.ennreal_ofReal
  have hcap_meas : Measurable fun θ : Θ => ∫⁻ u, ENNReal.ofReal (f θ u) ∂(kap θ) := by
    have hcap_eq : ∀ θ : Θ, (∫⁻ u, ENNReal.ofReal (f θ u) ∂(kap θ))
        = ∫⁻ x, ENNReal.ofReal (f x.1 x.2) ∂(Measure.map (fun u : U => (θ, u)) (kap θ)) := by
      intro θ
      exact (MeasureTheory.lintegral_map (μ := kap θ)
        (f := fun x : Θ × U => ENNReal.ofReal (f x.1 x.2))
        (g := fun u : U => (θ, u)) hg_meas measurable_prodMk_left).symm
    have hsimple : ∀ s : SimpleFunc (Θ × U) ℝ≥0∞,
        Measurable fun θ : Θ =>
          ∫⁻ x, (s : Θ × U → ℝ≥0∞) x ∂(Measure.map (fun u : U => (θ, u)) (kap θ)) := by
      intro s
      have hsum : (fun θ : Θ => ∫⁻ x, (s : Θ × U → ℝ≥0∞) x
            ∂(Measure.map (fun u : U => (θ, u)) (kap θ)))
          = fun θ : Θ =>
            ∑ c ∈ s.range, c * (Measure.map (fun u : U => (θ, u)) (kap θ)) (s ⁻¹' {c}) := by
        funext θ
        rw [SimpleFunc.lintegral_eq_lintegral]
        simp only [SimpleFunc.lintegral]
      rw [hsum]
      exact Finset.measurable_sum _ fun c _ => Measurable.mul measurable_const
        ((MeasureTheory.Measure.measurable_measure.mp hker) (s ⁻¹' {c}) (s.measurableSet_fiber c))
    have hsup : (fun θ : Θ =>
          ∫⁻ x, ENNReal.ofReal (f x.1 x.2) ∂(Measure.map (fun u : U => (θ, u)) (kap θ)))
        = fun θ : Θ => ⨆ n, ∫⁻ x, ((SimpleFunc.eapprox
            (fun x : Θ × U => ENNReal.ofReal (f x.1 x.2)) n : SimpleFunc (Θ × U) ℝ≥0∞) :
            Θ × U → ℝ≥0∞) x ∂(Measure.map (fun u : U => (θ, u)) (kap θ)) := by
      funext θ
      rw [lintegral_eq_iSup_eapprox_lintegral hg_meas]
      simp only [← SimpleFunc.lintegral_eq_lintegral]
    rw [show (fun θ : Θ => ∫⁻ u, ENNReal.ofReal (f θ u) ∂(kap θ))
        = fun θ : Θ =>
          ∫⁻ x, ENNReal.ofReal (f x.1 x.2) ∂(Measure.map (fun u : U => (θ, u)) (kap θ))
        from funext hcap_eq]
    rw [hsup]
    exact Measurable.iSup fun n => hsimple _
  have hstep : ∀ θ : Θ, (∫⁻ u, ENNReal.ofReal (f θ u) ∂(kap θ)) ≤ ∫⁻ u, ‖f θ u‖ₑ ∂(kap θ) :=
    fun θ => MeasureTheory.lintegral_ofReal_le_lintegral_enorm (f θ)
  have hGmap : ∀ θ : Θ, (∫⁻ x, ‖f x.1 x.2‖ₑ ∂(Measure.map (fun u : U => (θ, u)) (kap θ)))
      = ∫⁻ u, ‖f θ u‖ₑ ∂(kap θ) := by
    intro θ
    exact MeasureTheory.lintegral_map (μ := kap θ) (f := fun x : Θ × U => ‖f x.1 x.2‖ₑ)
      (g := fun u : U => (θ, u)) hf.enorm measurable_prodMk_left
  have hFub : (∫⁻ x, ‖f x.1 x.2‖ₑ
        ∂((fun θ : Θ => Measure.map (fun u : U => (θ, u)) (kap θ)) ∘ₘ m))
      = ∫⁻ θ, (∫⁻ u, ‖f θ u‖ₑ ∂(kap θ)) ∂m := by
    rw [MeasureTheory.Measure.lintegral_bind (m := m)
      (μ := fun θ : Θ => Measure.map (fun u : U => (θ, u)) (kap θ))
      (f := fun x : Θ × U => ‖f x.1 x.2‖ₑ) hker.aemeasurable hf.enorm.aemeasurable]
    exact MeasureTheory.lintegral_congr fun θ => hGmap θ
  have hbudget_lt : (∫⁻ θ, (∫⁻ u, ‖f θ u‖ₑ ∂(kap θ)) ∂m) < ⊤ := by
    rw [← hFub]
    simpa only [HasFiniteIntegral] using Hint.2
  have hcap_fin_lt : (∫⁻ θ, (∫⁻ u, ENNReal.ofReal (f θ u) ∂(kap θ)) ∂m) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.lintegral_mono fun θ => hstep θ) hbudget_lt
  refine ⟨hcap_meas, ?_⟩
  refine ⟨hcap_meas.ennreal_toReal.aestronglyMeasurable, ?_⟩
  have hbound : ∀ a : ℝ≥0∞, ‖a.toReal‖ₑ ≤ a := by
    intro a
    rw [Real.enorm_eq_ofReal]
    all_goals first
      | exact ENNReal.ofReal_toReal_le
      | exact ENNReal.toReal_nonneg
      | positivity
  simp only [HasFiniteIntegral]
  exact lt_of_le_of_lt
    (MeasureTheory.lintegral_mono fun θ => hbound (∫⁻ u, ENNReal.ofReal (f θ u) ∂(kap θ)))
    hcap_fin_lt
  /- @proof-region region.target-node.session.e462a4f8ccf30d21 end -/

end
end Statlib.Imported
