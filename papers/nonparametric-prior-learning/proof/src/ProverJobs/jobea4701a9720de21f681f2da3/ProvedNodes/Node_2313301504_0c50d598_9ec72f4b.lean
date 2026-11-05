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
theorem statopia_math_node_2313301504_0c50d598 : ∀ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (mu nu : Measure α) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (kappa eta : Kernel α β) [IsFiniteKernel kappa] [IsFiniteKernel eta]
    [SigmaFinite (Measure.compProd nu eta)]
    (h_mu_nu : mu ≪ nu) (h_kappa_eta : ∀ᵐ a ∂mu, kappa a ≪ eta a),
    Measure.rnDeriv (Measure.compProd mu kappa) (Measure.compProd nu eta)
      =ᵐ[Measure.compProd nu eta]
      fun p : α × β =>
        Measure.rnDeriv mu nu p.1 * (Kernel.rnDeriv kappa eta) p.1 p.2 := by
  /- @proof-region region.target-node.session.466ae81d0c397dfb begin -/
  intro α β _ _ _ μ ν _ _ κ η _ _ _ hμν hκη
  have hf : Measurable fun a : α => Measure.rnDeriv μ ν a := Measure.measurable_rnDeriv μ ν
  have hg : Measurable fun p : α × β => (Kernel.rnDeriv κ η) p.1 p.2 :=
    Kernel.measurable_rnDeriv κ η
  have hF : Measurable fun p : α × β =>
      Measure.rnDeriv μ ν p.1 * (Kernel.rnDeriv κ η) p.1 p.2 :=
    hf.comp measurable_fst |>.mul hg
  have hμeq : ν.withDensity (Measure.rnDeriv μ ν) = μ := by
    haveI : μ.HaveLebesgueDecomposition ν :=
      Measure.haveLebesgueDecomposition_of_finiteMeasure
    exact Measure.withDensity_rnDeriv_eq μ ν hμν
  have hκeq : (⇑κ : α → Measure β) =ᵐ[μ] ⇑(η.withDensity (Kernel.rnDeriv κ η)) := by
    filter_upwards [hκη] with a ha
    rw [← Kernel.withDensity_rnDeriv_eq ha]
  have h1 : Measure.compProd μ κ = Measure.compProd μ (η.withDensity (Kernel.rnDeriv κ η)) :=
    Measure.compProd_congr hκeq
  have h3 : Measure.compProd ν (η.withDensity (Kernel.rnDeriv κ η))
      = (Measure.compProd ν η).withDensity
          (fun p : α × β => (Kernel.rnDeriv κ η) p.1 p.2) :=
    Measure.compProd_withDensity hg
  have hval : ∀ (μ' : Measure (α × β)) {φ : α × β → ℝ≥0∞}, Measurable φ →
      ∀ {u : Set (α × β)}, MeasurableSet u →
        (μ'.withDensity φ) u = ∫⁻ a, u.indicator φ a ∂μ' := by
    intro μ' φ hφ u hu
    have hg1 : Measurable (u.indicator (1 : α × β → ℝ≥0∞)) :=
      Measurable.indicator measurable_const hu
    calc (μ'.withDensity φ) u
        = ∫⁻ a, u.indicator (1 : α × β → ℝ≥0∞) a ∂(μ'.withDensity φ) :=
          (lintegral_indicator_one (μ := μ'.withDensity φ) hu).symm
      _ = ∫⁻ a, (φ * u.indicator (1 : α × β → ℝ≥0∞)) a ∂μ' :=
          lintegral_withDensity_eq_lintegral_mul μ' hφ hg1
      _ = ∫⁻ a, u.indicator φ a ∂μ' := by
          rw [show φ * u.indicator (1 : α × β → ℝ≥0∞) = u.indicator φ from by
            funext a
            by_cases ha : a ∈ u
            · simp [Set.indicator_of_mem ha]
            · simp [Set.indicator, ha]]
  have h4 : ((Measure.compProd ν η).withDensity
        (fun p : α × β => (Kernel.rnDeriv κ η) p.1 p.2)).withDensity
        (fun p : α × β => Measure.rnDeriv μ ν p.1)
      = (Measure.compProd ν η).withDensity
          (fun p : α × β => Measure.rnDeriv μ ν p.1 * (Kernel.rnDeriv κ η) p.1 p.2) := by
    ext u hu
    have hψ : Measurable fun p : α × β => Measure.rnDeriv μ ν p.1 := hf.comp measurable_fst
    calc (((Measure.compProd ν η).withDensity
            (fun p : α × β => (Kernel.rnDeriv κ η) p.1 p.2)).withDensity
            (fun p : α × β => Measure.rnDeriv μ ν p.1)) u
        = ∫⁻ p, u.indicator (fun p : α × β => Measure.rnDeriv μ ν p.1) p ∂
            ((Measure.compProd ν η).withDensity
              (fun p : α × β => (Kernel.rnDeriv κ η) p.1 p.2)) := hval _ hψ hu
      _ = ∫⁻ p, ((fun p : α × β => (Kernel.rnDeriv κ η) p.1 p.2) *
              u.indicator (fun p : α × β => Measure.rnDeriv μ ν p.1)) p ∂
            (Measure.compProd ν η) :=
          lintegral_withDensity_eq_lintegral_mul (Measure.compProd ν η) hg (hψ.indicator hu)
      _ = ∫⁻ p, u.indicator
              (fun p : α × β => Measure.rnDeriv μ ν p.1 * (Kernel.rnDeriv κ η) p.1 p.2) p ∂
            (Measure.compProd ν η) := by
          rw [show ((fun p : α × β => (Kernel.rnDeriv κ η) p.1 p.2) *
                u.indicator (fun p : α × β => Measure.rnDeriv μ ν p.1))
              = u.indicator (fun p : α × β =>
                  Measure.rnDeriv μ ν p.1 * (Kernel.rnDeriv κ η) p.1 p.2) from by
            funext p
            by_cases hp : p ∈ u
            · simp [Set.indicator_of_mem hp, mul_comm]
            · simp [Set.indicator, hp]]
      _ = ((Measure.compProd ν η).withDensity
              (fun p : α × β => Measure.rnDeriv μ ν p.1 * (Kernel.rnDeriv κ η) p.1 p.2)) u :=
          (hval _ hF hu).symm
  have hvalβ : ∀ (ρ : Measure β) {φ : β → ℝ≥0∞}, Measurable φ →
      ∀ {s : Set β}, MeasurableSet s → (ρ.withDensity φ) s = ∫⁻ b, s.indicator φ b ∂ρ := by
    intro ρ φ hφ s hs
    have hg1 : Measurable (s.indicator (1 : β → ℝ≥0∞)) :=
      Measurable.indicator measurable_const hs
    calc (ρ.withDensity φ) s
        = ∫⁻ b, s.indicator (1 : β → ℝ≥0∞) b ∂(ρ.withDensity φ) :=
          (lintegral_indicator_one (μ := ρ.withDensity φ) hs).symm
      _ = ∫⁻ b, (φ * s.indicator (1 : β → ℝ≥0∞)) b ∂ρ :=
          lintegral_withDensity_eq_lintegral_mul ρ hφ hg1
      _ = ∫⁻ b, s.indicator φ b ∂ρ := by
          rw [show φ * s.indicator (1 : β → ℝ≥0∞) = s.indicator φ from by
            funext b
            by_cases hb : b ∈ s
            · simp [Set.indicator_of_mem hb]
            · simp [Set.indicator, hb]]
  have hMP : Measure.compProd (ν.withDensity (Measure.rnDeriv μ ν))
        (η.withDensity (Kernel.rnDeriv κ η))
      = (Measure.compProd ν (η.withDensity (Kernel.rnDeriv κ η))).withDensity
          (fun p : α × β => Measure.rnDeriv μ ν p.1) := by
    ext u hu
    have hind : Measurable (u.indicator (1 : α × β → ℝ≥0∞)) :=
      Measurable.indicator measurable_const hu
    have hG : Measurable fun a : α =>
        ∫⁻ b, u.indicator (1 : α × β → ℝ≥0∞) (a, b)
          ∂((η.withDensity (Kernel.rnDeriv κ η)) a) :=
      Measurable.lintegral_kernel_prod_right' hind
    have hL : (Measure.compProd (ν.withDensity (Measure.rnDeriv μ ν))
          (η.withDensity (Kernel.rnDeriv κ η))) u
        = ∫⁻ a, Measure.rnDeriv μ ν a *
            (∫⁻ b, u.indicator (1 : α × β → ℝ≥0∞) (a, b)
              ∂((η.withDensity (Kernel.rnDeriv κ η)) a)) ∂ν := by
      calc (Measure.compProd (ν.withDensity (Measure.rnDeriv μ ν))
            (η.withDensity (Kernel.rnDeriv κ η))) u
          = ∫⁻ p, u.indicator (1 : α × β → ℝ≥0∞) p
              ∂(Measure.compProd (ν.withDensity (Measure.rnDeriv μ ν))
                (η.withDensity (Kernel.rnDeriv κ η))) :=
            (lintegral_indicator_one (μ := Measure.compProd
              (ν.withDensity (Measure.rnDeriv μ ν))
              (η.withDensity (Kernel.rnDeriv κ η))) hu).symm
        _ = ∫⁻ a, ∫⁻ b, u.indicator (1 : α × β → ℝ≥0∞) (a, b)
              ∂((η.withDensity (Kernel.rnDeriv κ η)) a)
              ∂(ν.withDensity (Measure.rnDeriv μ ν)) :=
            Measure.lintegral_compProd hind
        _ = ∫⁻ a, Measure.rnDeriv μ ν a *
              (∫⁻ b, u.indicator (1 : α × β → ℝ≥0∞) (a, b)
                ∂((η.withDensity (Kernel.rnDeriv κ η)) a)) ∂ν :=
            lintegral_withDensity_eq_lintegral_mul ν hf hG
    have hR : ((Measure.compProd ν (η.withDensity (Kernel.rnDeriv κ η))).withDensity
          (fun p : α × β => Measure.rnDeriv μ ν p.1)) u
        = ∫⁻ a, Measure.rnDeriv μ ν a *
            (∫⁻ b, u.indicator (1 : α × β → ℝ≥0∞) (a, b)
              ∂((η.withDensity (Kernel.rnDeriv κ η)) a)) ∂ν := by
      calc ((Measure.compProd ν (η.withDensity (Kernel.rnDeriv κ η))).withDensity
            (fun p : α × β => Measure.rnDeriv μ ν p.1)) u
          = ∫⁻ p, u.indicator (fun p : α × β => Measure.rnDeriv μ ν p.1) p
              ∂(Measure.compProd ν (η.withDensity (Kernel.rnDeriv κ η))) :=
            hval _ (hf.comp measurable_fst) hu
        _ = ∫⁻ a, ∫⁻ b, u.indicator (fun p : α × β => Measure.rnDeriv μ ν p.1) (a, b)
              ∂((η.withDensity (Kernel.rnDeriv κ η)) a) ∂ν :=
            Measure.lintegral_compProd ((hf.comp measurable_fst).indicator hu)
        _ = ∫⁻ a, Measure.rnDeriv μ ν a *
              (∫⁻ b, u.indicator (1 : α × β → ℝ≥0∞) (a, b)
                ∂((η.withDensity (Kernel.rnDeriv κ η)) a)) ∂ν := by
            refine lintegral_congr fun a => ?_
            have hpt : (fun b : β => u.indicator
                  (fun p : α × β => Measure.rnDeriv μ ν p.1) (a, b))
                = fun b : β => Measure.rnDeriv μ ν a *
                    u.indicator (1 : α × β → ℝ≥0∞) (a, b) := by
              funext b
              by_cases hb : (a, b) ∈ u
              · simp [Set.indicator_of_mem hb]
              · simp [Set.indicator, hb]
            have hsec : Measurable fun b : β => (a, b) := by
              measurability
            have hsecm : Measurable fun b : β =>
                u.indicator (1 : α × β → ℝ≥0∞) (a, b) :=
              hind.comp hsec
            rw [hpt]
            exact lintegral_const_mul _ hsecm
    exact hL.trans hR.symm
  have h2 : Measure.compProd μ (η.withDensity (Kernel.rnDeriv κ η))
      = (Measure.compProd ν (η.withDensity (Kernel.rnDeriv κ η))).withDensity
          (fun p : α × β => Measure.rnDeriv μ ν p.1) := by
    conv_lhs => rw [← hμeq]
    exact hMP
  have hW : Measure.compProd μ κ = (Measure.compProd ν η).withDensity
      (fun p : α × β => Measure.rnDeriv μ ν p.1 * (Kernel.rnDeriv κ η) p.1 p.2) := by
    rw [h1, h2, h3]
    exact h4
  have hfinal := Measure.rnDeriv_withDensity (Measure.compProd ν η) hF
  rw [← hW] at hfinal
  exact hfinal
  /- @proof-region region.target-node.session.466ae81d0c397dfb end -/

end
end Statlib.Imported
