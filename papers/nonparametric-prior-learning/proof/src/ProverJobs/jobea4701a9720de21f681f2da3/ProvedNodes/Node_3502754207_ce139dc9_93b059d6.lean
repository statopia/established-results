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
theorem statopia_math_node_3502754207_ce139dc9 : ∀ {X Y U Θ V : Type*}
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
    (n : ℕ) (hn : 0 < n)
    (ω : Fin n → Block (X × Y))
    (HQ : ProbabilityMeasure Θ) (HP : ProbabilityMeasure Θ)
    (hPost_meas : ∀ i : Fin n,
      Measurable fun θ : Θ => (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))
    (hPrior_meas : ∀ i : Fin n,
      Measurable fun θ : Θ => (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)),
    IsProbabilityMeasure
        ((HQ : Measure Θ).bind
          (fun θ =>
            (Measure.pi fun i : Fin n =>
              (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
              (fun u : Fin n → U => (θ, u))))
      ∧ IsProbabilityMeasure
        ((HP : Measure Θ).bind
          (fun θ =>
            (Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
              (fun u : Fin n → U => (θ, u)))) := by
  /- @proof-region region.target-node.session.a27bcf8d05a2ba35 begin -/
  intro X Y U Θ V
    iX1 iX2 iX3 iX4 iX5 iX6
    iY1 iY2 iY3 iY4 iY5 iY6
    iU1 iU2 iU3 iU4 iU5 iU6
    iΘ1 iΘ2 iΘ3 iΘ4 iΘ5 iΘ6
    iV1 iV2 iV3 iV4 iV5 iV6
    M n hn ω HQ HP hPost_meas hPrior_meas
  have key : ∀ (μ : ProbabilityMeasure Θ) (Q : Fin n → Θ → ProbabilityMeasure U),
      (∀ i, Measurable fun θ : Θ => (Q i θ : Measure U)) →
      IsProbabilityMeasure ((μ : Measure Θ).bind (fun θ =>
        (Measure.pi fun i : Fin n => (Q i θ : Measure U)).map
          (fun u : Fin n → U => (θ, u)))) := by
    intro μ Q hQ
    have hpi : ∀ θ : Θ, IsProbabilityMeasure (Measure.pi fun i : Fin n => (Q i θ : Measure U)) := by
      intro θ
      refine ⟨?_⟩
      rw [Measure.pi_univ]
      exact Finset.prod_eq_one (fun i _ => IsProbabilityMeasure.measure_univ)
    have hprob : ∀ θ : Θ, IsProbabilityMeasure
        ((Measure.pi fun i : Fin n => (Q i θ : Measure U)).map
          (fun u : Fin n → U => (θ, u))) := by
      intro θ
      haveI := hpi θ
      exact Measure.isProbabilityMeasure_map (f := fun u : Fin n → U => (θ, u))
        (by measurability : Measurable fun u : Fin n → U => (θ, u)).aemeasurable
    set Sbox : Set (Set (Fin n → U)) :=
      {s | ∃ t : Fin n → Set U, (∀ i, MeasurableSet (t i)) ∧ s = Set.univ.pi t} with hSbox
    have hboxPi : IsPiSystem Sbox := by
      rintro s₁ ⟨t₁, ht₁, rfl⟩ s₂ ⟨t₂, ht₂, rfl⟩ hne
      refine ⟨fun i => t₁ i ∩ t₂ i, fun i => (ht₁ i).inter (ht₂ i), ?_⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_univ_pi]
      exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
    have hgenBox : (inferInstance : MeasurableSpace (Fin n → U)) =
        MeasurableSpace.generateFrom Sbox := by
      refine le_antisymm ?_ ?_
      · have hdec : (inferInstance : MeasurableSpace (Fin n → U)) =
            ⨆ i : Fin n, MeasurableSpace.comap (Function.eval i)
              (inferInstance : MeasurableSpace U) := rfl
        rw [hdec]
        refine iSup_le (fun i => ?_)
        rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.le_def]
        intro t ht
        show (MeasurableSpace.generateFrom Sbox).MeasurableSet'
          ((fun x : Fin n → U => x i) ⁻¹' t)
        have hif : (fun x : Fin n → U => x i) ⁻¹' t =
            Set.univ.pi (fun j : Fin n => if j = i then t else (Set.univ : Set U)) := by
          ext x
          simp only [Set.mem_preimage, Set.mem_univ_pi]
          constructor
          · intro hx j
            show x j ∈ (if j = i then t else (Set.univ : Set U))
            by_cases hj : j = i
            · simpa [hj] using hx
            · simp [hj]
          · intro hx
            have h := hx i
            simpa using h
        rw [hif]
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨fun j : Fin n => if j = i then t else (Set.univ : Set U), fun j => by
            show MeasurableSet (if j = i then t else (Set.univ : Set U))
            by_cases hj : j = i
            · simpa [hj] using ht
            · simp [hj], rfl⟩
      · refine MeasurableSpace.generateFrom_le (fun t ht => ?_)
        obtain ⟨u, hu, rfl⟩ := ht
        exact MeasurableSet.pi Set.countable_univ (fun i _ => hu i)
    have hval : ∀ s ∈ Sbox, Measurable fun θ : Θ =>
        (Measure.pi fun i : Fin n => (Q i θ : Measure U)) s := by
      rintro s ⟨t, ht, rfl⟩
      have hbox : ∀ θ : Θ,
          (Measure.pi fun i : Fin n => (Q i θ : Measure U)) (Set.univ.pi t)
            = ∏ i, ((Q i θ : Measure U) (t i)) :=
        fun θ => Measure.pi_pi (fun i : Fin n => (Q i θ : Measure U)) t
      simp only [hbox]
      have hfac : ∀ i : Fin n, Measurable fun θ : Θ => (Q i θ : Measure U) (t i) := fun i =>
        Measure.measurable_measure.mp (hQ i) (t i) (ht i)
      exact Finset.measurable_prod Finset.univ (fun i _ => hfac i)
    haveI : ∀ θ : Θ, IsProbabilityMeasure (Measure.pi fun i : Fin n => (Q i θ : Measure U)) := hpi
    have hpiMeas : Measurable fun θ : Θ => (Measure.pi fun i : Fin n => (Q i θ : Measure U)) :=
      Measurable.measure_of_isPiSystem_of_isProbabilityMeasure hgenBox hboxPi hval
    let η : Kernel Θ (Fin n → U) :=
      ⟨fun θ => (Measure.pi fun i : Fin n => (Q i θ : Measure U)), hpiMeas⟩
    haveI : ∀ θ : Θ, IsProbabilityMeasure
        ((Measure.pi fun i : Fin n => (Q i θ : Measure U)).map
          (fun u : Fin n → U => (θ, u))) := hprob
    have hgenAll : (inferInstance : MeasurableSpace (Θ × (Fin n → U))) =
        MeasurableSpace.generateFrom {s : Set (Θ × (Fin n → U)) | MeasurableSet s} := by
      refine le_antisymm ?_ ?_
      · rw [MeasurableSpace.le_def]
        intro s hs
        exact MeasurableSpace.measurableSet_generateFrom hs
      · exact MeasurableSpace.generateFrom_le (fun t ht => ht)
    have hmeas : Measurable fun θ : Θ =>
        (Measure.pi fun i : Fin n => (Q i θ : Measure U)).map
          (fun u : Fin n → U => (θ, u)) := by
      refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure hgenAll
        MeasurableSpace.isPiSystem_measurableSet ?_
      rintro s hs
      have hfun : (fun θ : Θ => (Measure.map (fun u : Fin n → U => (θ, u))
            (Measure.pi fun i : Fin n => (Q i θ : Measure U))) s)
          = fun θ : Θ => (Measure.pi fun i : Fin n => (Q i θ : Measure U))
              ((fun u : Fin n → U => (θ, u)) ⁻¹' s) := by
        funext θ
        exact Measure.map_apply (by measurability : Measurable fun u : Fin n → U => (θ, u)) hs
      rw [hfun]
      exact Kernel.measurable_kernel_prodMk_left_of_finite (κ := η) hs (fun a => by
        haveI := hpi a
        infer_instance)
    refine ⟨?_⟩
    rw [Measure.bind_apply MeasurableSet.univ hmeas.aemeasurable]
    rw [show (∫⁻ θ, (Measure.pi fun i : Fin n => (Q i θ : Measure U)).map
          (fun u : Fin n → U => (θ, u)) Set.univ ∂(μ : Measure Θ))
        = ∫⁻ _θ, (1 : ℝ≥0∞) ∂(μ : Measure Θ) from
          lintegral_congr (fun θ => (hprob θ).measure_univ)]
    rw [lintegral_const, one_mul]
    exact IsProbabilityMeasure.measure_univ
  exact ⟨key HQ (fun i θ => basePost M ((mOf ω i : ℕ)) (SOF ω i) θ) hPost_meas,
    key HP (fun i θ => basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ) hPrior_meas⟩
  /- @proof-region region.target-node.session.a27bcf8d05a2ba35 end -/

end
end Statlib.Imported
