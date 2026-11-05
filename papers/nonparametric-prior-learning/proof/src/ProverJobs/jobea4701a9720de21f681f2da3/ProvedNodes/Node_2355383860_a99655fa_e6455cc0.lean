import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_3196442440_7836214e_f7927913
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
theorem statopia_math_node_2355383860_a99655fa : ∀ {Theta U : Type*} [MeasurableSpace Theta] [MeasurableSpace U]
    [MeasurableSpace.CountableOrCountablyGenerated Theta U]
    (Q : ProbabilityMeasure Theta) (K L : Kernel Theta U)
    [IsMarkovKernel K] [IsMarkovKernel L]
    (h : Measure.compProd (Q : Measure Theta) K ≪ Measure.compProd (Q : Measure Theta) L),
    ∀ᵐ theta ∂(Q : Measure Theta), (K theta : Measure U) ≪ (L theta : Measure U) := by
  /- @proof-region region.target-node.session.6691c61b8ed1bdba begin -/
  intro Theta U _ _ _ Q K L _ _ h
  rw [MeasureTheory.ae_iff]
  have hN : (Q : Measure Theta)
      {theta : Theta | (K theta) (K.mutuallySingularSetSlice L theta) ≠ 0} = 0 :=
    statopia_math_node_3196442440_7836214e Q K L h
  have hkey : ∀ theta : Theta,
      (K theta) (K.mutuallySingularSetSlice L theta) = 0 →
        (K theta : Measure U) ≪ (L theta : Measure U) := by
    intro theta h0
    have hS : MeasurableSet (K.mutuallySingularSetSlice L theta) :=
      Kernel.measurableSet_mutuallySingularSetSlice K L theta
    have hMle : ((L.withDensity (K.rnDeriv L)) theta : Measure U) ≤ (K theta : Measure U) :=
      Kernel.withDensity_rnDeriv_le K L theta
    have hD1 : ((K.singularPart L) theta) (K.mutuallySingularSetSlice L theta) = 0 := by
      rw [Kernel.singularPart_of_subset_mutuallySingularSetSlice
        (κ := K) (η := L) (a := theta) (s := K.mutuallySingularSetSlice L theta)
        (Kernel.measurableSet_mutuallySingularSetSlice K L theta) (subset_refl _)]
      exact h0
    have hD2 : ((K.singularPart L) theta) (K.mutuallySingularSetSlice L theta)ᶜ = 0 :=
      Kernel.singularPart_compl_mutuallySingularSetSlice K L theta
    have hD0 : (K.singularPart L) theta = 0 := by
      have hu : ((K.singularPart L) theta) Set.univ = 0 := by
        rw [← Set.union_compl_self (K.mutuallySingularSetSlice L theta)]
        exact measure_union_null hD1 hD2
      refine le_antisymm ?_ ?_
      · refine Measure.le_iff'.mpr (fun s => ?_)
        simpa using le_trans (measure_mono (Set.subset_univ s)) (le_of_eq hu)
      · refine Measure.le_iff'.mpr (fun s => ?_)
        simp

    have hsum := Kernel.rnDeriv_add_singularPart (κ := K) (η := L)
    have hpt := congrArg (fun f : Kernel Theta U => (f theta : Measure U)) hsum
    have hD : (K theta : Measure U) = ((L.withDensity (K.rnDeriv L)) theta : Measure U) := by
      simpa [hD0] using hpt.symm
    have hMpt : ((L.withDensity (K.rnDeriv L)) theta : Measure U)
        = (L theta).withDensity ((K.rnDeriv L) theta) :=
      Kernel.withDensity_apply (κ := L) (f := K.rnDeriv L) (by measurability) theta
    rw [hD, hMpt]
    exact MeasureTheory.withDensity_absolutelyContinuous (L theta) ((K.rnDeriv L) theta)






  refine measure_mono_null (fun theta htheta => ?_) hN
  exact fun h0 => htheta (hkey theta h0)
  /- @proof-region region.target-node.session.6691c61b8ed1bdba end -/

end
end Statlib.Imported
