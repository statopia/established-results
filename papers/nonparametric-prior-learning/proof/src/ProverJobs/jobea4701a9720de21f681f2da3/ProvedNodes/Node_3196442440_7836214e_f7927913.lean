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
theorem statopia_math_node_3196442440_7836214e : ∀ {Theta U : Type*} [MeasurableSpace Theta] [MeasurableSpace U]
    [MeasurableSpace.CountableOrCountablyGenerated Theta U]
    (Q : ProbabilityMeasure Theta) (K L : Kernel Theta U)
    [IsMarkovKernel K] [IsMarkovKernel L]
    (h : Measure.compProd (Q : Measure Theta) K ≪ Measure.compProd (Q : Measure Theta) L),
    (Q : Measure Theta) {theta : Theta | (K theta) (K.mutuallySingularSetSlice L theta) ≠ 0} = 0 := by
  /- @proof-region region.target-node.session.7df6e5cf4a392b12 begin -/
  intro Theta U _ _ _ Q K L _ _ h
  set W : Set (Theta × U) := K.mutuallySingularSet L with hWdef
  have hW : MeasurableSet W := by
    rw [hWdef]
    exact Kernel.measurableSet_mutuallySingularSet K L
  have hslice : ∀ a, Prod.mk a ⁻¹' W = K.mutuallySingularSetSlice L a := by
    intro a
    rw [hWdef]
    rfl
  have hmem : ∀ (a : Theta) {b : U},
      b ∈ K.mutuallySingularSetSlice L a → 1 ≤ K.rnDerivAux (K + L) a b := by
    intro a b hb
    simpa only [ProbabilityTheory.Kernel.mutuallySingularSetSlice, Set.mem_setOf_eq] using hb
  have hLslice : ∀ a, (L a) (K.mutuallySingularSetSlice L a) = 0 := by
    intro a
    have hSlmeas : MeasurableSet (K.mutuallySingularSetSlice L a) :=
      Kernel.measurableSet_mutuallySingularSetSlice K L a
    have hX := Kernel.withDensity_one_sub_rnDerivAux K L
    have hLa : (L a) = ((K + L).withDensity (fun (a : Theta) (x : U) =>
        ↑(1 - K.rnDerivAux (K + L) a x).toNNReal)) a :=
      (congrArg (fun m : Kernel Theta U => m a) hX).symm
    have hmeas : Measurable (Function.uncurry (fun (a : Theta) (x : U) =>
        (↑(1 - K.rnDerivAux (K + L) a x).toNNReal : ℝ≥0∞))) := by
      measurability

    have hval : (L a) (K.mutuallySingularSetSlice L a)
        = ∫⁻ x in K.mutuallySingularSetSlice L a,
            ↑(1 - K.rnDerivAux (K + L) a x).toNNReal ∂((K + L) a) := by
      rw [hLa]
      exact Kernel.withDensity_apply' (K + L) hmeas a (K.mutuallySingularSetSlice L a)
    have hint : ∫⁻ x in K.mutuallySingularSetSlice L a,
        ↑(1 - K.rnDerivAux (K + L) a x).toNNReal ∂((K + L) a) = 0 := by
      rw [← lintegral_indicator hSlmeas]
      have hzero : (K.mutuallySingularSetSlice L a).indicator
          (fun x => (↑(1 - K.rnDerivAux (K + L) a x).toNNReal : ℝ≥0∞)) = 0 := by
        funext x
        by_cases hx : x ∈ K.mutuallySingularSetSlice L a
        · rw [Set.indicator_of_mem hx]
          have hr : (1 : ℝ) ≤ K.rnDerivAux (K + L) a x := hmem a hx
          have h2 : (1 - K.rnDerivAux (K + L) a x).toNNReal = 0 := by
            apply Real.toNNReal_of_nonpos
            linarith
          rw [h2]
          simp
        · rw [Set.indicator_of_notMem hx]
          rfl

      rw [hzero]
      exact lintegral_zero
    rw [hval, hint]






  have hLW : Measure.compProd (Q : Measure Theta) L W = 0 := by
    rw [Measure.compProd_apply hW]
    have hzero : (fun a => (L a) (Prod.mk a ⁻¹' W)) = (fun _ => (0 : ℝ≥0∞)) := by
      funext a
      rw [hslice a]
      exact hLslice a
    rw [hzero]
    exact lintegral_zero
  have hKW : Measure.compProd (Q : Measure Theta) K W = 0 := h hLW
  have hlin : ∫⁻ a, (K a) (K.mutuallySingularSetSlice L a) ∂(Q : Measure Theta) = 0 := by
    have hcp := Measure.compProd_apply (μ := (Q : Measure Theta)) (κ := K) (s := W) hW
    rw [hKW] at hcp
    simp only [hslice] at hcp
    exact hcp.symm

  have hkey : ∀ a, (K a) (K.mutuallySingularSetSlice L a) = ((K.singularPart L) a) Set.univ := by
    intro a
    have hmeas : MeasurableSet (K.mutuallySingularSetSlice L a) :=
      Kernel.measurableSet_mutuallySingularSetSlice K L a
    have h1 : ((K.singularPart L) a) (K.mutuallySingularSetSlice L a)
        = (K a) (K.mutuallySingularSetSlice L a) :=
      Kernel.singularPart_of_subset_mutuallySingularSetSlice
        (κ := K) (η := L) (a := a) (s := K.mutuallySingularSetSlice L a) hmeas
        (fun x hx => hx)

    have h2 : ((K.singularPart L) a) (K.mutuallySingularSetSlice L a)ᶜ = 0 :=
      Kernel.singularPart_compl_mutuallySingularSetSlice K L a
    have h3 := measure_add_measure_compl (μ := (K.singularPart L) a) hmeas
    rw [h1, h2, add_zero] at h3
    exact h3
  have hSint : ∫⁻ a, ((K.singularPart L) a) Set.univ ∂(Q : Measure Theta) = 0 := by
    rw [show (fun a => ((K.singularPart L) a) Set.univ)
          = (fun a => (K a) (K.mutuallySingularSetSlice L a)) from
        funext (fun a => (hkey a).symm)]
    exact hlin
  have haeS : ∀ᵐ a ∂(Q : Measure Theta), ((K.singularPart L) a) Set.univ = 0 := by
    have hSmeas : Measurable (K.singularPart L : Theta → Measure U) :=
      (K.singularPart L).measurable'
    have hmeasS : Measurable fun a => ((K.singularPart L) a) Set.univ :=
      MeasureTheory.Measure.measurable_measure.mp hSmeas Set.univ MeasurableSet.univ
    exact (MeasureTheory.lintegral_eq_zero_iff' hmeasS.aemeasurable).mp hSint



  have hae : ∀ᵐ theta ∂(Q : Measure Theta), (K theta) (K.mutuallySingularSetSlice L theta) = 0 := by
    filter_upwards [haeS] with a ha
    rw [hkey a]
    exact ha
  exact MeasureTheory.ae_iff.mp hae


  /- @proof-region region.target-node.session.7df6e5cf4a392b12 end -/

end
end Statlib.Imported
