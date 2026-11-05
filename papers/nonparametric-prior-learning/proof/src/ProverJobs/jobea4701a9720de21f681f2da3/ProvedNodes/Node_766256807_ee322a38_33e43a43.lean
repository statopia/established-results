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
theorem statopia_math_node_766256807_ee322a38 : ∀ {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y],
    Measurable (fun p : ProbabilityMeasure (X × Y) × ℕ+ =>
      Measure.map (fun S : Fin ((p.2 : ℕ)) → (X × Y) => (p, padSample (p.2 : ℕ) S))
        (Measure.pi fun _ : Fin ((p.2 : ℕ)) => (p.1 : Measure (X × Y)))) := by
  /- @proof-region region.target-node.session.c272175599dbc4ca begin -/
  classical
  intros X Y
  intros
  have hpadmeas : ∀ (m : ℕ), Measurable fun S : Fin m → (X × Y) => padSample m S := by
    intro m
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j < m
    · simp only [padSample, dif_pos hj]
      exact measurable_pi_apply _
    · simp only [padSample, dif_neg hj]
      exact measurable_const
  set Φ : ProbabilityMeasure (X × Y) × ℕ+ → Measure ((ProbabilityMeasure (X × Y) × ℕ+) × (ℕ → X × Y)) :=
    fun p => Measure.map (fun S : Fin ((p.2 : ℕ)) → (X × Y) => (p, padSample (p.2 : ℕ) S))
      (Measure.pi fun _ : Fin ((p.2 : ℕ)) => (p.1 : Measure (X × Y))) with hΦ
  have hmap : ∀ p : ProbabilityMeasure (X × Y) × ℕ+,
      Measurable (fun S : Fin ((p.2 : ℕ)) → (X × Y) => (p, padSample (p.2 : ℕ) S)) := by
    intro p
    exact Measurable.prodMk measurable_const (hpadmeas (p.2 : ℕ))
  have hfib : ∀ p : ProbabilityMeasure (X × Y) × ℕ+, Φ p Set.univ = 1 := by
    intro p
    rw [hΦ]
    rw [Measure.map_apply (hmap p) MeasurableSet.univ, Set.preimage_univ, Measure.pi_univ]
    simp
  haveI hprob : ∀ p, IsProbabilityMeasure (Φ p) := fun p => ⟨hfib p⟩
  set boxSet : Set (Set ((ProbabilityMeasure (X × Y) × ℕ+) × (ℕ → X × Y))) :=
    {s | ∃ (u : Set (ProbabilityMeasure (X × Y) × ℕ+)) (F : Finset ℕ) (C : ℕ → Set (X × Y)),
      MeasurableSet u ∧ (∀ j, MeasurableSet (C j)) ∧ s = u ×ˢ {T : ℕ → X × Y | ∀ j ∈ F, T j ∈ C j}} with hboxSet
  have hcylmeas : ∀ (F : Finset ℕ) (C : ℕ → Set (X × Y)), (∀ j, MeasurableSet (C j)) →
      MeasurableSet {T : ℕ → X × Y | ∀ j ∈ F, T j ∈ C j} := by
    intro F
    induction F using Finset.induction with
    | empty =>
      intro C hC
      have h : {T : ℕ → X × Y | ∀ j ∈ (∅ : Finset ℕ), T j ∈ C j} = Set.univ := by
        ext T
        simp
      rw [h]
      exact MeasurableSet.univ
    | insert a s ha ih =>
      intro C hC
      have hsplit : {T : ℕ → X × Y | ∀ j ∈ insert a s, T j ∈ C j}
          = {T : ℕ → X × Y | T a ∈ C a} ∩ {T : ℕ → X × Y | ∀ j ∈ s, T j ∈ C j} := by
        ext T
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro h
          exact ⟨h a (Finset.mem_insert_self a s), fun j hj => h j (Finset.mem_insert_of_mem hj)⟩
        · rintro ⟨h1, h2⟩ j hj
          rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact h1
          · exact h2 j hj'
      rw [hsplit]
      exact MeasurableSet.inter ((hC a).preimage (measurable_pi_apply a)) (ih C hC)
  have hgen : (inferInstance : MeasurableSpace ((ProbabilityMeasure (X × Y) × ℕ+) × (ℕ → X × Y)))
      = MeasurableSpace.generateFrom boxSet := by
    refine le_antisymm ?_ ?_
    · rw [show (inferInstance : MeasurableSpace ((ProbabilityMeasure (X × Y) × ℕ+) × (ℕ → X × Y)))
          = (inferInstance : MeasurableSpace (ProbabilityMeasure (X × Y) × ℕ+)).prod
            (inferInstance : MeasurableSpace (ℕ → X × Y)) from rfl]
      refine sup_le ?_ ?_
      · rintro s ⟨u, hu, rfl⟩
        have hbox : (u ×ˢ {T : ℕ → X × Y | ∀ j ∈ (∅ : Finset ℕ), T j ∈ (Set.univ : Set (X × Y))}) ∈ boxSet :=
          ⟨u, ∅, fun _ => Set.univ, hu, fun _ => MeasurableSet.univ, rfl⟩
        have key : MeasurableSet[MeasurableSpace.generateFrom boxSet] (Prod.fst ⁻¹' u) := by
          convert MeasurableSpace.measurableSet_generateFrom hbox using 1
          ext x
          simp
        exact key
      · have hpi : (inferInstance : MeasurableSpace (ℕ → X × Y))
            = ⨆ i : ℕ,
              MeasurableSpace.comap (fun T : ℕ → X × Y => T i)
                (inferInstance : MeasurableSpace (X × Y)) := rfl
        rw [hpi, MeasurableSpace.comap_iSup]
        refine iSup_le fun i => ?_
        rintro s ⟨C, hC, rfl⟩
        obtain ⟨D, hD, rfl⟩ := hC
        refine MeasurableSpace.measurableSet_generateFrom ?_
        refine ⟨Set.univ, {i}, fun j => if j = i then D else Set.univ, MeasurableSet.univ, ?_, ?_⟩
        · intro j
          by_cases h : j = i
          · simpa [h] using hD
          · simp [h]
        · ext x
          simp [Finset.mem_singleton]
    · refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨u, F, C, hu, hC, rfl⟩
      exact MeasurableSet.prod hu (hcylmeas F C hC)
  have hpiS : IsPiSystem boxSet := by
    rintro s ⟨u₁, F₁, C₁, hu₁, hC₁, rfl⟩ t ⟨u₂, F₂, C₂, hu₂, hC₂, rfl⟩ _
    refine ⟨u₁ ∩ u₂, F₁ ∪ F₂,
      fun j => (if j ∈ F₁ then C₁ j else Set.univ) ∩ (if j ∈ F₂ then C₂ j else Set.univ),
      hu₁.inter hu₂, ?_, ?_⟩
    · intro j
      by_cases h1 : j ∈ F₁
      · by_cases h2 : j ∈ F₂
        · simpa [h1, h2] using (hC₁ j).inter (hC₂ j)
        · simpa [h1, h2] using hC₁ j
      · by_cases h2 : j ∈ F₂
        · simpa [h1, h2] using hC₂ j
        · simp [h1, h2]
    · rw [Set.prod_inter_prod]
      congr 1
      ext T
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2⟩ j (hj | hj)
        · refine ⟨?_, ?_⟩
          · simpa [hj] using h1 j hj
          · by_cases hj2 : j ∈ F₂
            · simpa [hj2] using h2 j hj2
            · simp [hj2]
        · refine ⟨?_, ?_⟩
          · by_cases hj1 : j ∈ F₁
            · simpa [hj1] using h1 j hj1
            · simp [hj1]
          · simpa [hj] using h2 j hj
      · intro h
        constructor
        · intro j hj
          simpa [hj] using (h j (Or.inl hj)).1
        · intro j hj
          simpa [hj] using (h j (Or.inr hj)).2
  have hmass : ∀ s ∈ boxSet, Measurable fun p => Φ p s := by
    rintro s ⟨u, F, C, hu, hC, rfl⟩
    have hB : MeasurableSet {T : ℕ → X × Y | ∀ j ∈ F, T j ∈ C j} := hcylmeas F C hC
    have hev : ∀ j : ℕ, Measurable fun p : ProbabilityMeasure (X × Y) × ℕ+ =>
        (p.1 : Measure (X × Y)) (C j) := by
      intro j
      have h1 : Measurable fun q : ProbabilityMeasure (X × Y) => (q : Measure (X × Y)) :=
        measurable_subtype_coe
      exact (MeasureTheory.Measure.measurable_measure.mp h1 (C j) (hC j)).comp measurable_fst
    have hlt : ∀ j : ℕ,
        MeasurableSet {p : ProbabilityMeasure (X × Y) × ℕ+ | j < (p.2 : ℕ)} := by
      intro j
      have h2 : Measurable fun p : ProbabilityMeasure (X × Y) × ℕ+ => (p.2 : ℕ) :=
        measurable_subtype_coe.comp measurable_snd
      exact h2 measurableSet_Ioi
    have hfac : ∀ j : ℕ, Measurable fun p : ProbabilityMeasure (X × Y) × ℕ+ =>
        (if j < (p.2 : ℕ) then (p.1 : Measure (X × Y)) (C j)
          else (if (0 : X × Y) ∈ C j then 1 else 0)) := by
      intro j
      by_cases h0 : (0 : X × Y) ∈ C j
      · have hgoal : (fun p : ProbabilityMeasure (X × Y) × ℕ+ =>
            (if j < (p.2 : ℕ) then (p.1 : Measure (X × Y)) (C j)
              else (if (0 : X × Y) ∈ C j then 1 else 0)))
            = fun p : ProbabilityMeasure (X × Y) × ℕ+ =>
              if j < (p.2 : ℕ) then (p.1 : Measure (X × Y)) (C j) else 1 := by
          funext p
          simp [h0]
        rw [hgoal]
        exact Measurable.ite (hlt j) (hev j) measurable_const
      · have hgoal : (fun p : ProbabilityMeasure (X × Y) × ℕ+ =>
            (if j < (p.2 : ℕ) then (p.1 : Measure (X × Y)) (C j)
              else (if (0 : X × Y) ∈ C j then 1 else 0)))
            = fun p : ProbabilityMeasure (X × Y) × ℕ+ =>
              if j < (p.2 : ℕ) then (p.1 : Measure (X × Y)) (C j) else 0 := by
          funext p
          simp [h0]
        rw [hgoal]
        exact Measurable.ite (hlt j) (hev j) measurable_const
    have hprod : Measurable fun p : ProbabilityMeasure (X × Y) × ℕ+ =>
        ∏ j ∈ F, (if j < (p.2 : ℕ) then (p.1 : Measure (X × Y)) (C j)
          else (if (0 : X × Y) ∈ C j then 1 else 0)) := by
      induction F using Finset.induction with
      | empty => simpa using measurable_const
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact (hfac a).mul (ih (hcylmeas s C hC))
    have hif : Measurable fun p : ProbabilityMeasure (X × Y) × ℕ+ =>
        if p ∈ u then ∏ j ∈ F, (if j < (p.2 : ℕ) then (p.1 : Measure (X × Y)) (C j)
          else (if (0 : X × Y) ∈ C j then 1 else 0)) else 0 :=
      Measurable.ite hu hprod measurable_const
    have hcylmass : ∀ (m : ℕ) (μ : Measure (X × Y)), IsProbabilityMeasure μ →
        (Measure.pi fun _ : Fin m => μ) {S : Fin m → (X × Y) | ∀ j ∈ F, padSample m S j ∈ C j}
          = ∏ j ∈ F, (if j < m then μ (C j) else (if (0 : X × Y) ∈ C j then 1 else 0)) := by
      intro m μ hμ
      haveI : IsProbabilityMeasure μ := hμ
      by_cases h : ∀ j ∈ F, m ≤ j → (0 : X × Y) ∈ C j
      · have hset : {S : Fin m → (X × Y) | ∀ j ∈ F, padSample m S j ∈ C j}
            = Set.pi Set.univ (fun i : Fin m => if (i : ℕ) ∈ F then C (i : ℕ) else Set.univ) := by
          ext S
          rw [Set.mem_setOf_eq, Set.mem_pi]
          constructor
          · intro hS i _
            by_cases hi : (i : ℕ) ∈ F
            · have hSi := hS (i : ℕ) hi
              rw [padSample, dif_pos i.2] at hSi
              simpa [hi] using hSi
            · simp [hi]
          · intro hS j hj
            by_cases hjm : j < m
            · have h' := hS ⟨j, hjm⟩ (Set.mem_univ _)
              rw [padSample, dif_pos hjm]
              rwa [if_pos hj] at h'
            · rw [padSample, dif_neg hjm]
              exact h j hj (not_lt.mp hjm)
        have hstep : ∏ i : Fin m, μ (if (i : ℕ) ∈ F then C (i : ℕ) else Set.univ)
            = ∏ i : Fin m, (if (i : ℕ) ∈ F then μ (C (i : ℕ)) else 1) := by
          refine Finset.prod_congr rfl ?_
          intro i _
          by_cases hi : (i : ℕ) ∈ F
          · simp [hi]
          · simp [hi]
        have hprod1 : ∏ i : Fin m, (if (i : ℕ) ∈ F then μ (C (i : ℕ)) else 1)
            = ∏ j ∈ F, (if j < m then μ (C j) else 1) := by
          rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => if j ∈ F then μ (C j) else 1)]
          rw [← Finset.prod_filter, ← Finset.prod_filter]
          congr 1
          ext j
          simp [Finset.mem_filter, Finset.mem_range, and_comm]
        have hrhs : ∏ j ∈ F, (if j < m then μ (C j) else (if (0 : X × Y) ∈ C j then 1 else 0))
            = ∏ j ∈ F, (if j < m then μ (C j) else 1) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          by_cases hjm : j < m
          · simp [hjm]
          · simp [hjm, h j hj (not_lt.mp hjm)]
        rw [hset, Measure.pi_pi, hrhs]
        exact hstep.trans hprod1
      · have hnex : ∃ j, j ∈ F ∧ m ≤ j ∧ (0 : X × Y) ∉ C j := by
          by_contra hc
          exact h fun j hjF hmj => by
            by_contra h0j
            exact hc ⟨j, hjF, hmj, h0j⟩
        obtain ⟨j₀, hj₀F, hmj₀, h0j₀⟩ := hnex
        have hempty : {S : Fin m → (X × Y) | ∀ j ∈ F, padSample m S j ∈ C j} = ∅ := by
          ext S
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro hS
          have h1 := hS j₀ hj₀F
          rw [padSample, dif_neg (not_lt.mpr hmj₀)] at h1
          exact h0j₀ h1
        have hz : (if j₀ < m then μ (C j₀) else (if (0 : X × Y) ∈ C j₀ then 1 else 0)) = 0 := by
          rw [if_neg (not_lt.mpr hmj₀), if_neg h0j₀]
        rw [hempty, Finset.prod_eq_zero hj₀F hz]
        simp
    have hform : ∀ p : ProbabilityMeasure (X × Y) × ℕ+,
        Φ p (u ×ˢ {T : ℕ → X × Y | ∀ j ∈ F, T j ∈ C j})
          = if p ∈ u then ∏ j ∈ F, (if j < (p.2 : ℕ) then (p.1 : Measure (X × Y)) (C j)
            else (if (0 : X × Y) ∈ C j then 1 else 0)) else 0 := by
      intro p
      have hpre : (fun S : Fin ((p.2 : ℕ)) → (X × Y) => (p, padSample (p.2 : ℕ) S)) ⁻¹'
          (u ×ˢ {T : ℕ → X × Y | ∀ j ∈ F, T j ∈ C j})
          = {S : Fin ((p.2 : ℕ)) → (X × Y) | p ∈ u ∧ ∀ j ∈ F, padSample (p.2 : ℕ) S j ∈ C j} := by
        ext S
        simp
      have hmapapp : Φ p (u ×ˢ {T : ℕ → X × Y | ∀ j ∈ F, T j ∈ C j})
          = (Measure.pi fun _ : Fin ((p.2 : ℕ)) => (p.1 : Measure (X × Y)))
              {S : Fin ((p.2 : ℕ)) → (X × Y) | p ∈ u ∧ ∀ j ∈ F, padSample (p.2 : ℕ) S j ∈ C j} := by
        rw [hΦ, Measure.map_apply (hmap p) (MeasurableSet.prod hu hB), hpre]
      rw [hmapapp]
      by_cases hpu : p ∈ u
      · rw [if_pos hpu]
        have hset : {S : Fin ((p.2 : ℕ)) → (X × Y) | p ∈ u ∧ ∀ j ∈ F, padSample (p.2 : ℕ) S j ∈ C j}
            = {S : Fin ((p.2 : ℕ)) → (X × Y) | ∀ j ∈ F, padSample (p.2 : ℕ) S j ∈ C j} := by
          ext S
          simp [hpu]
        rw [hset, hcylmass (p.2 : ℕ) (p.1 : Measure (X × Y)) inferInstance]
      · rw [if_neg hpu]
        have hempty : {S : Fin ((p.2 : ℕ)) → (X × Y) | p ∈ u ∧ ∀ j ∈ F, padSample (p.2 : ℕ) S j ∈ C j}
            = ∅ := by
          ext S
          simp [hpu]
        rw [hempty]
        simp
    simpa only [hform] using hif
  exact Measurable.measure_of_isPiSystem_of_isProbabilityMeasure (μ := Φ) (S := boxSet) hgen hpiS hmass
  /- @proof-region region.target-node.session.c272175599dbc4ca end -/

end
end Statlib.Imported
