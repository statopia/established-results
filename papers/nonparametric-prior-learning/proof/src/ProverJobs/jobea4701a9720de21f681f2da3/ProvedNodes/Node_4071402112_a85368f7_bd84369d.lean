import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_79440718_8647c8d9_38e2d9f6
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
theorem statopia_math_node_4071402112_a85368f7 : ∀ {X Y U Θ V : Type*}
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
    (hPost_meas : ∀ k : ℕ, Measurable fun q : (Fin k → X × Y) × Θ => basePost M k q.1 q.2)
    (hℓ_int : ∀ (u : U) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun z : X × Y => M.ℓ u z) (D : Measure (X × Y)))
    (hLgibbs_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun u : U => Lmean M.ℓ u (D : Measure (X × Y))) (basePost M k S θ : Measure U))
    (calT : ProbabilityMeasure (ProbabilityMeasure (X × Y) × ℕ+)),
    Measurable (fun θ : Θ =>
      ∫ p : ProbabilityMeasure (X × Y) × ℕ+,
        transferAt M θ p ∂(calT : Measure (ProbabilityMeasure (X × Y) × ℕ+))) := by
  /- @proof-region region.target-node.session.6e7b85a91269682b begin -/
  classical
  intro X Y U Θ V
    _ _ _ _ _
    _ _ _ _ _
    _ _ _ _ _
    _ _ _ _ _
    _ _ _ _ _
    _ _ _ _ _
    M hℓ hPost_meas hℓ_int hLgibbs_int calT
  have key : StronglyMeasurable (fun q : (ProbabilityMeasure (X × Y) × ℕ+) × Θ =>
      transferAt M q.2 q.1) := by
    have hLmean_meas : Measurable (fun q : U × ProbabilityMeasure (X × Y) =>
        ∫ z : X × Y, M.ℓ q.1 z ∂(q.2 : Measure (X × Y))) := by
      have hf : StronglyMeasurable
          (fun w : (X × Y) × (U × ProbabilityMeasure (X × Y)) => M.ℓ w.2.1 w.1) := by
        have h1 : Measurable
            (fun w : (X × Y) × (U × ProbabilityMeasure (X × Y)) => (w.2.1, w.1)) := by
          fun_prop
        exact (hℓ.comp h1).stronglyMeasurable
      have hcoe : Measurable fun D : ProbabilityMeasure (X × Y) => (D : Measure (X × Y)) :=
        measurable_subtype_coe
      let κ : Kernel (U × ProbabilityMeasure (X × Y)) (X × Y) :=
        { toFun := fun q => (q.2 : Measure (X × Y))
          measurable' := hcoe.comp measurable_snd }
      haveI hfin : IsFiniteKernel κ :=
        { exists_univ_le := ⟨1, by simp, fun a => by simp [κ]⟩ }
      haveI : IsSFiniteKernel κ := inferInstance
      have h := MeasureTheory.StronglyMeasurable.integral_kernel_prod_left
        (κ := κ)
        (f := fun (z : X × Y) (q : U × ProbabilityMeasure (X × Y)) => M.ℓ q.1 z) hf
      exact h.measurable
    have hpost_int_meas : ∀ k : ℕ, Measurable
        (fun w : (Fin k → X × Y) × ProbabilityMeasure (X × Y) × Θ =>
          ∫ u, Lmean M.ℓ u (w.2.1 : Measure (X × Y))
            ∂(basePost M k w.1 w.2.2 : Measure U)) := by
      intro k
      have hf : StronglyMeasurable
          (fun p : U × ((Fin k → X × Y) × ProbabilityMeasure (X × Y) × Θ) =>
            ∫ z : X × Y, M.ℓ p.1 z ∂(p.2.2.1 : Measure (X × Y))) := by
        have hproj : Measurable
            (fun p : U × ((Fin k → X × Y) × ProbabilityMeasure (X × Y) × Θ) =>
              (p.1, p.2.2.1)) := by fun_prop
        exact (hLmean_meas.comp hproj).stronglyMeasurable
      have hpostmeas : Measurable
          (fun w : (Fin k → X × Y) × ProbabilityMeasure (X × Y) × Θ => (w.1, w.2.2)) := by
        fun_prop
      have hcot : Measurable fun D : ProbabilityMeasure U => (D : Measure U) :=
        measurable_subtype_coe
      let κ : Kernel ((Fin k → X × Y) × ProbabilityMeasure (X × Y) × Θ) U :=
        { toFun := fun w => (basePost M k w.1 w.2.2 : Measure U)
          measurable' := hcot.comp ((hPost_meas k).comp hpostmeas) }
      haveI hfin : IsFiniteKernel κ :=
        { exists_univ_le := ⟨1, by simp, fun a => by simp [κ]⟩ }
      haveI : IsSFiniteKernel κ := inferInstance
      have h := MeasureTheory.StronglyMeasurable.integral_kernel_prod_left (κ := κ)
        (f := fun (u : U) (w : (Fin k → X × Y) × ProbabilityMeasure (X × Y) × Θ) =>
          ∫ z : X × Y, M.ℓ u z ∂(w.2.1 : Measure (X × Y))) hf
      exact h.measurable
    have hG_meas : ∀ k : ℕ, Measurable (fun y : ProbabilityMeasure (X × Y) × Θ =>
        ∫ S : Fin k → X × Y,
          Lgibbs M.ℓ (basePost M k S y.2 : Measure U) (y.1 : Measure (X × Y))
          ∂(Measure.pi fun _ : Fin k => (y.1 : Measure (X × Y)))) := by
      intro k
      have hκmeas : Measurable (fun D : ProbabilityMeasure (X × Y) =>
          Measure.pi fun _ : Fin k => (D : Measure (X × Y))) :=
        statopia_math_node_79440718_8647c8d9 (Theta := ProbabilityMeasure (X × Y)) (U := X × Y) k
          (fun _ D => (D : Measure (X × Y))) (fun _ D => inferInstance)
          (fun _ => measurable_subtype_coe)
      have hf : StronglyMeasurable
          (fun p : (Fin k → X × Y) × (ProbabilityMeasure (X × Y) × Θ) =>
            ∫ u, Lmean M.ℓ u (p.2.1 : Measure (X × Y))
              ∂(basePost M k p.1 p.2.2 : Measure U)) := by
        have hproj : Measurable
            (fun p : (Fin k → X × Y) × (ProbabilityMeasure (X × Y) × Θ) =>
              (p.1, p.2.1, p.2.2)) := by fun_prop
        exact (hpost_int_meas k).comp hproj |>.stronglyMeasurable
      let κ : Kernel (ProbabilityMeasure (X × Y) × Θ) (Fin k → X × Y) :=
        { toFun := fun y => Measure.pi fun _ : Fin k => (y.1 : Measure (X × Y))
          measurable' := hκmeas.comp measurable_fst }
      haveI hfin : IsFiniteKernel κ :=
        { exists_univ_le := ⟨1, by simp, fun a => by simp [κ]⟩ }
      haveI : IsSFiniteKernel κ := inferInstance
      have h := MeasureTheory.StronglyMeasurable.integral_kernel_prod_left (κ := κ)
        (f := fun (S : Fin k → X × Y) (y : ProbabilityMeasure (X × Y) × Θ) =>
          Lgibbs M.ℓ (basePost M k S y.2 : Measure U) (y.1 : Measure (X × Y))) hf
      exact h.measurable
    have hpnat : Measurable
        (fun q : (ProbabilityMeasure (X × Y) × ℕ+) × Θ => (q.1.2 : ℕ)) :=
      measurable_subtype_coe.comp (by fun_prop)
    have hjoint : Measurable (fun q : (ProbabilityMeasure (X × Y) × ℕ+) × Θ =>
        transferAt M q.2 q.1) := by
      intro t ht
      have hdec : (fun q : (ProbabilityMeasure (X × Y) × ℕ+) × Θ => transferAt M q.2 q.1) ⁻¹' t
          = ⋃ n : ℕ, {q : (ProbabilityMeasure (X × Y) × ℕ+) × Θ | (q.1.2 : ℕ) = n} ∩
              ((fun q : (ProbabilityMeasure (X × Y) × ℕ+) × Θ => (q.1.1, q.2)) ⁻¹'
                ((fun y : ProbabilityMeasure (X × Y) × Θ =>
                  ∫ S : Fin n → X × Y,
                    Lgibbs M.ℓ (basePost M n S y.2 : Measure U) (y.1 : Measure (X × Y))
                    ∂(Measure.pi fun _ : Fin n => (y.1 : Measure (X × Y)))) ⁻¹' t)) := by
        ext q
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro h
          exact ⟨(q.1.2 : ℕ), rfl, h⟩
        · rintro ⟨n, hn, h⟩
          rw [← hn] at h
          exact h
      rw [hdec]
      exact MeasurableSet.iUnion fun n =>
        MeasurableSet.inter
          ((measurableSet_singleton n).preimage hpnat)
          ((hG_meas n ht).preimage (by fun_prop))
    exact hjoint.stronglyMeasurable
  have hmain : StronglyMeasurable (fun θ : Θ =>
      ∫ p : ProbabilityMeasure (X × Y) × ℕ+,
        transferAt M θ p ∂(calT : Measure (ProbabilityMeasure (X × Y) × ℕ+))) := by
    have h := MeasureTheory.StronglyMeasurable.integral_kernel_prod_left
      (κ := ProbabilityTheory.Kernel.const Θ (calT : Measure (ProbabilityMeasure (X × Y) × ℕ+)))
      (f := fun (p : ProbabilityMeasure (X × Y) × ℕ+) (θ : Θ) => transferAt M θ p) key
    simpa using h
  exact hmain.measurable
  /- @proof-region region.target-node.session.6e7b85a91269682b end -/

end
end Statlib.Imported
