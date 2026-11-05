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
theorem statopia_math_node_79440718_8647c8d9 : ∀ {Theta U : Type*} [MeasurableSpace Theta] [MeasurableSpace U]
    (n : ℕ) (kap : Fin n → Theta → Measure U)
    (hprob : ∀ (i : Fin n) (theta : Theta), IsProbabilityMeasure (kap i theta))
    (hmeas : ∀ i : Fin n, Measurable fun theta : Theta => kap i theta),
    Measurable fun theta : Theta => Measure.pi fun i : Fin n => kap i theta := by
  /- @proof-region region.target-node.session.aebae12183a6eba7 begin -/
  intro Theta U _ _ n kap hprob hmeas
  haveI hP : ∀ (i : Fin n) (θ : Theta), IsProbabilityMeasure (kap i θ) := hprob
  have hcrit : ∀ (μ : Theta → Measure (Fin n → U)), Measurable μ ↔
      ∀ s : Set (Fin n → U), MeasurableSet s → Measurable fun θ : Theta => μ θ s :=
    fun μ => Measure.measurable_measure
  refine (hcrit (fun θ : Theta => Measure.pi fun i : Fin n => kap i θ)).mpr ?_
  intro s hs
  let Pbox : Set (Set (Fin n → U)) :=
    {t | ∃ g : Fin n → Set U, (∀ i, MeasurableSet (g i)) ∧ t = Set.univ.pi g}
  have hbox_meas : ∀ t ∈ Pbox, MeasurableSet t := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := ht
    have hEq : Set.univ.pi g = ⋂ i, Function.eval i ⁻¹' g i := by
      ext x
      simp [Set.mem_univ_pi]
    rw [hEq]
    exact MeasurableSet.iInter fun i =>
      (hg i).preimage (measurable_pi_iff.mp measurable_id i)
  have hpi : IsPiSystem Pbox := by
    intro t1 ht1 t2 ht2 _
    obtain ⟨g1, hg1, rfl⟩ := ht1
    obtain ⟨g2, hg2, rfl⟩ := ht2
    refine ⟨fun i => g1 i ∩ g2 i, fun i => (hg1 i).inter (hg2 i), ?_⟩
    ext x
    exact ⟨fun h i _ => ⟨h.1 i trivial, h.2 i trivial⟩,
      fun h => ⟨fun i _ => (h i trivial).1, fun i _ => (h i trivial).2⟩⟩
  have hgen_le : MeasurableSpace.generateFrom Pbox ≤ (inferInstance : MeasurableSpace (Fin n → U)) :=
    MeasurableSpace.generateFrom_le hbox_meas
  have hgen_ge : (inferInstance : MeasurableSpace (Fin n → U)) ≤ MeasurableSpace.generateFrom Pbox := by
    have hcyl : ∀ i : Fin n, MeasurableSpace.comap (Function.eval i)
        (inferInstance : MeasurableSpace U) ≤ MeasurableSpace.generateFrom Pbox := by
      intro i
      intro s' hs'
      obtain ⟨A, hA, hfl⟩ := hs'
      rw [← hfl, Set.eval_preimage]
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨Function.update (fun _ => Set.univ) i A, fun j => by
          obtain rfl | hj := eq_or_ne j i
          · simpa using hA
          · simp [Function.update, hj],
          rfl⟩
    change (⨆ i : Fin n, MeasurableSpace.comap (Function.eval i)
      (inferInstance : MeasurableSpace U)) ≤ MeasurableSpace.generateFrom Pbox
    exact iSup_le hcyl
  have hgen : (inferInstance : MeasurableSpace (Fin n → U)) = MeasurableSpace.generateFrom Pbox :=
    le_antisymm hgen_ge hgen_le
  refine MeasurableSpace.induction_on_inter
    (C := fun t _ => Measurable fun θ : Theta => (Measure.pi fun i : Fin n => kap i θ) t)
    hgen hpi ?_ ?_ ?_ ?_ s hs
  · simp only [measure_empty]
    exact measurable_const
  · intro t ht
    obtain ⟨g, hg, rfl⟩ := ht
    have hform : ∀ θ : Theta,
        (Measure.pi fun i : Fin n => kap i θ) (Set.univ.pi g) = ∏ i, (kap i θ) (g i) := by
      intro θ
      haveI : ∀ i : Fin n, IsProbabilityMeasure (kap i θ) := fun i => hprob i θ
      exact Measure.pi_pi (μ := fun i => kap i θ) (s := g)
    have hprod : Measurable fun θ : Theta => ∏ i, (kap i θ) (g i) := by
      simpa using Finset.measurable_prod (Finset.univ : Finset (Fin n))
        (f := fun i θ => (kap i θ) (g i)) (fun i _ =>
          (Measure.measurable_measure.mp (hmeas i)) (g i) (hg i))
    rw [show (fun θ : Theta => (Measure.pi fun i : Fin n => kap i θ) (Set.univ.pi g))
        = fun θ => ∏ i, (kap i θ) (g i) from funext hform]
    exact hprod
  · intro t htm ih
    have huniv : ∀ θ : Theta, (Measure.pi fun i : Fin n => kap i θ) Set.univ = 1 := by
      intro θ
      haveI : ∀ i : Fin n, IsProbabilityMeasure (kap i θ) := fun i => hprob i θ
      have hU : (Set.univ : Set (Fin n → U)) = Set.univ.pi (fun _ => Set.univ) := by
        ext x
        simp [Set.mem_univ_pi]
      rw [hU, Measure.pi_pi (μ := fun i : Fin n => kap i θ) (s := fun _ => Set.univ)]
      simp
    have hpt : ∀ θ : Theta, (Measure.pi fun i : Fin n => kap i θ) tᶜ
        = 1 - (Measure.pi fun i : Fin n => kap i θ) t := by
      intro θ
      have hfin : (Measure.pi fun i : Fin n => kap i θ) t ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (by rw [← huniv θ]; exact measure_mono (Set.subset_univ t))
          ENNReal.one_lt_top)
      rw [measure_compl htm hfin, huniv]
    rw [show (fun θ : Theta => (Measure.pi fun i : Fin n => kap i θ) tᶜ)
        = fun θ => 1 - (Measure.pi fun i : Fin n => kap i θ) t from funext hpt]
    exact measurable_const.sub ih
  · intro f hdisj hfm ihf
    have hpt : ∀ θ : Theta, (Measure.pi fun i : Fin n => kap i θ) (⋃ i, f i)
        = ∑' i, (Measure.pi fun i : Fin n => kap i θ) (f i) := by
      intro θ
      haveI : ∀ i : Fin n, IsProbabilityMeasure (kap i θ) := fun i => hprob i θ
      exact measure_iUnion hdisj hfm
    rw [show (fun θ : Theta => (Measure.pi fun i : Fin n => kap i θ) (⋃ i, f i))
        = fun θ => ∑' i, (Measure.pi fun i : Fin n => kap i θ) (f i) from funext hpt]
    exact Measurable.ennreal_tsum ihf
  /- @proof-region region.target-node.session.aebae12183a6eba7 end -/

end
end Statlib.Imported
