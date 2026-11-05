import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4071402112_a85368f7_bd84369d
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
theorem statopia_math_node_4096909918_1936c781 : ∀ {X Y U Θ V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
    [TopologicalSpace.SeparableSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V] [MeasurableSpace V] [BorelSpace V]
    (M : Model X Y U Θ V)
    (hℓ : Measurable (Function.uncurry M.ℓ))
    (n : ℕ) (hn : 0 < n)
    (ω : Fin n → Block (X × Y))
    (calT : ProbabilityMeasure (ProbabilityMeasure (X × Y) × ℕ+))
    (hPost_meas : ∀ k : ℕ, Measurable fun q : (Fin k → X × Y) × Θ => basePost M k q.1 q.2)
    (hℓ_int : ∀ (u : U) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun z : X × Y => M.ℓ u z) (D : Measure (X × Y)))
    (hLgibbs_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun u : U => Lmean M.ℓ u (D : Measure (X × Y)))
        (basePost M k S θ : Measure U)),
    (Measurable fun θ : Θ => (1 / (n : ℝ)) * ∑ i : Fin n,
        Lgibbs M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)
          (DOf ω i : Measure (X × Y)))
      ∧ (Measurable fun θ : Θ => ∫ p : ProbabilityMeasure (X × Y) × ℕ+,
          transferAt M θ p ∂(calT : Measure (ProbabilityMeasure (X × Y) × ℕ+))) := by
  /- @proof-region region.target-node.session.02b191e57f7d77b1 begin -/
  intro X Y U Θ V
    _ _ _ _ _ _
    _ _ _ _ _ _
    _ _ _ _ _ _
    _ _ _ _ _ _
    _ _ _ _ _ _
    M hℓ n hn ω calT hPost_meas hℓ_int hLgibbs_int
  constructor
  · have hstep : ∀ (D : ProbabilityMeasure (X × Y)) (k : ℕ) (S : Fin k → X × Y),
        Measurable fun θ : Θ =>
          Lgibbs M.ℓ (basePost M k S θ : Measure U) (D : Measure (X × Y)) := by
      intro D k S
      have hu : Measurable fun u : U => Lmean M.ℓ u (D : Measure (X × Y)) := by
        have hpos : Measurable fun u : U =>
            ∫⁻ z : X × Y, ENNReal.ofReal (M.ℓ u z) ∂(D : Measure (X × Y)) := by
          have hf : Measurable fun p : U × (X × Y) => ENNReal.ofReal (M.ℓ p.1 p.2) :=
            hℓ.ennreal_ofReal
          have h := Measurable.lintegral_kernel_prod_right'
            (κ := Kernel.const U (D : Measure (X × Y))) hf
          simpa using h
        have hneg : Measurable fun u : U =>
            ∫⁻ z : X × Y, ENNReal.ofReal (-(M.ℓ u z)) ∂(D : Measure (X × Y)) := by
          have hf : Measurable fun p : U × (X × Y) => ENNReal.ofReal (-(M.ℓ p.1 p.2)) :=
            hℓ.neg.ennreal_ofReal
          have h := Measurable.lintegral_kernel_prod_right'
            (κ := Kernel.const U (D : Measure (X × Y))) hf
          simpa using h
        have h1 : Measurable fun u : U =>
            (∫⁻ z : X × Y, ENNReal.ofReal (M.ℓ u z) ∂(D : Measure (X × Y))).toReal :=
          hpos.ennreal_toReal
        have h2 : Measurable fun u : U =>
            (∫⁻ z : X × Y, ENNReal.ofReal (-(M.ℓ u z)) ∂(D : Measure (X × Y))).toReal :=
          hneg.ennreal_toReal
        have hsub := h1.sub h2
        have heq : (fun u : U => Lmean M.ℓ u (D : Measure (X × Y)))
            = fun u : U =>
                (∫⁻ z : X × Y, ENNReal.ofReal (M.ℓ u z) ∂(D : Measure (X × Y))).toReal
                - (∫⁻ z : X × Y, ENNReal.ofReal (-(M.ℓ u z)) ∂(D : Measure (X × Y))).toReal := by
          funext u
          exact MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hℓ_int u D)
        rw [heq]
        exact hsub
      have hκ : Measurable fun θ : Θ =>
          ((basePost M k S θ : ProbabilityMeasure U) : Measure U) :=
        measurable_subtype_coe.comp ((hPost_meas k).comp (measurable_const.prodMk measurable_id))
      let κ : Kernel Θ U :=
        ⟨fun θ => ((basePost M k S θ : ProbabilityMeasure U) : Measure U), hκ⟩
      have hA : Measurable fun θ : Θ =>
          ∫⁻ u : U, ENNReal.ofReal (Lmean M.ℓ u (D : Measure (X × Y))) ∂κ θ :=
        Measurable.lintegral_kernel (κ := κ)
          (f := fun u : U => ENNReal.ofReal (Lmean M.ℓ u (D : Measure (X × Y))))
          hu.ennreal_ofReal
      have hB : Measurable fun θ : Θ =>
          ∫⁻ u : U, ENNReal.ofReal (-(Lmean M.ℓ u (D : Measure (X × Y)))) ∂κ θ :=
        Measurable.lintegral_kernel (κ := κ)
          (f := fun u : U => ENNReal.ofReal (-(Lmean M.ℓ u (D : Measure (X × Y)))))
          hu.neg.ennreal_ofReal
      have h1 := hA.ennreal_toReal
      have h2 := hB.ennreal_toReal
      have heq : (fun θ : Θ => Lgibbs M.ℓ (basePost M k S θ : Measure U) (D : Measure (X × Y)))
          = fun θ : Θ =>
              (∫⁻ u : U, ENNReal.ofReal (Lmean M.ℓ u (D : Measure (X × Y))) ∂κ θ).toReal
              - (∫⁻ u : U, ENNReal.ofReal (-(Lmean M.ℓ u (D : Measure (X × Y)))) ∂κ θ).toReal := by
        funext θ
        exact MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hLgibbs_int k S θ D)
      rw [heq]
      exact h1.sub h2
    have hterm : ∀ i : Fin n, Measurable fun θ : Θ =>
        Lgibbs M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)
          (DOf ω i : Measure (X × Y)) :=
      fun i => hstep (DOf ω i) ((mOf ω i : ℕ)) (SOF ω i)
    have hsum : Measurable fun θ : Θ => ∑ i : Fin n,
        Lgibbs M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)
          (DOf ω i : Measure (X × Y)) :=
      Finset.measurable_sum Finset.univ (fun i _ => hterm i)
    exact hsum.const_mul (1 / (n : ℝ))
  · exact statopia_math_node_4071402112_a85368f7 M hℓ hPost_meas hℓ_int hLgibbs_int calT
  /- @proof-region region.target-node.session.02b191e57f7d77b1 end -/

end
end Statlib.Imported
