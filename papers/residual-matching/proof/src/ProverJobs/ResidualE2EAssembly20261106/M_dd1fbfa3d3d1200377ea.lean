import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false in
theorem statopia_math_node_945620439_f6e84320 : ∀ {m n T : ℕ} {Ωs : Type*} [MeasurableSpace Ωs]
    (μ : Measure Ωs) (Om Hm : Ωs → Matrix (Fin m) (Fin n) ℝ)
    (G : Ωs → Fin T → Matrix (Fin m) (Fin n) ℝ)
    (hOm_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Om s i j)
    (hOm_indep : ProbabilityTheory.iIndepFun
      (fun (ij : Fin m × Fin n) (s : Ωs) => Om s ij.1 ij.2) μ)
    (hHm_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun s : Ωs => Hm s i j)
    (hHm_indep : ProbabilityTheory.iIndepFun
      (fun (ij : Fin m × Fin n) (s : Ωs) => Hm s ij.1 ij.2) μ)
    (hG_meas : ∀ (t : Fin T) (i : Fin m) (j : Fin n), Measurable fun s : Ωs => G s t i j)
    (hG_indep : ProbabilityTheory.iIndepFun
      (fun (tij : Fin T × Fin m × Fin n) (s : Ωs) => G s tij.1 tij.2.1 tij.2.2) μ)
    (hOmHm_indep : ProbabilityTheory.IndepFun (fun (s : Ωs) => Om s) (fun (s : Ωs) => Hm s) μ)
    (hG_joint : ProbabilityTheory.IndepFun
      (fun (s : Ωs) (tij : Fin T × Fin m × Fin n) => G s tij.1 tij.2.1 tij.2.2)
      (fun (s : Ωs) => (Om s, Hm s)) μ),
    ProbabilityTheory.iIndepFun
      (fun (x : (Fin m × Fin n) ⊕ ((Fin m × Fin n) ⊕ (Fin T × Fin m × Fin n))) (s : Ωs) =>
        match x with
        | Sum.inl q => Om s q.1 q.2
        | Sum.inr (Sum.inl q) => Hm s q.1 q.2
        | Sum.inr (Sum.inr q) => G s q.1 q.2.1 q.2.2) μ := by
  /- @proof-region region.target-node.session.97d8037743ba5666 begin -/
  intro m n T Ωs inst μ Om Hm G hOm_meas hOm_indep hHm_meas hHm_indep hG_meas hG_indep
    hOmHm_indep hG_joint
  classical
  let mOm : MeasurableSpace Ωs := MeasurableSpace.comap (fun x : Ωs => Om x)
    (inferInstance : MeasurableSpace (Matrix (Fin m) (Fin n) ℝ))
  let mHm : MeasurableSpace Ωs := MeasurableSpace.comap (fun x : Ωs => Hm x)
    (inferInstance : MeasurableSpace (Matrix (Fin m) (Fin n) ℝ))
  let mPair : MeasurableSpace Ωs := MeasurableSpace.comap (fun x : Ωs => (Om x, Hm x))
    (inferInstance : MeasurableSpace (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ))
  let mG : MeasurableSpace Ωs := MeasurableSpace.comap
    (fun x : Ωs => fun tij : Fin T × Fin m × Fin n => G x tij.1 tij.2.1 tij.2.2)
    (inferInstance : MeasurableSpace (Fin T × Fin m × Fin n → ℝ))
  have hOm' : Measurable[mOm] (fun x : Ωs => Om x) := measurable_iff_comap_le.mpr le_rfl
  have hHm' : Measurable[mHm] (fun x : Ωs => Hm x) := measurable_iff_comap_le.mpr le_rfl
  have hG' : Measurable[mG]
      (fun x : Ωs => fun tij : Fin T × Fin m × Fin n => G x tij.1 tij.2.1 tij.2.2) :=
    measurable_iff_comap_le.mpr le_rfl
  have hproj : ∀ q : Fin m × Fin n,
      Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M q.1 q.2) := by
    intro q
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hprojG : ∀ q : Fin T × Fin m × Fin n,
      Measurable (fun F : Fin T × Fin m × Fin n → ℝ => F q) := by
    intro q
    exact measurable_pi_apply q
  have hOm_le : mOm ≤ mPair := by
    have key : mOm = MeasurableSpace.comap (fun x : Ωs => (Om x, Hm x))
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace (Matrix (Fin m) (Fin n) ℝ))) := by
      rw [MeasurableSpace.comap_comp]
      rfl
    rw [key]
    exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp measurable_fst)
  have hHm_le : mHm ≤ mPair := by
    have key : mHm = MeasurableSpace.comap (fun x : Ωs => (Om x, Hm x))
        (MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace (Matrix (Fin m) (Fin n) ℝ))) := by
      rw [MeasurableSpace.comap_comp]
      rfl
    rw [key]
    exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp measurable_snd)
  have hAB : ∀ s t : Set Ωs, MeasurableSet[mOm] s → MeasurableSet[mHm] t →
      μ (s ∩ t) = μ s * μ t := by
    intro s t hs ht
    simpa using hOmHm_indep s t hs ht
  have hGC : ∀ s t : Set Ωs, MeasurableSet[mG] s → MeasurableSet[mPair] t →
      μ (s ∩ t) = μ s * μ t := by
    intro s t hs ht
    simpa using hG_joint s t hs ht
  have measInf : ∀ {ι' : Type} (m : MeasurableSpace Ωs) (S : Finset ι') (v : ι' → Set Ωs),
      (∀ i ∈ S, MeasurableSet[m] (v i)) → MeasurableSet[m] (⋂ i ∈ S, v i) := by
    intro ι' m S v hv
    exact MeasurableSet.biInter S.finite_toSet.countable (fun i hi => hv i hi)
  have measOm : ∀ (S : Finset (Fin m × Fin n)) (u : Fin m × Fin n → Set ℝ),
      (∀ i ∈ S, MeasurableSet (u i)) →
      MeasurableSet[mOm] (⋂ i ∈ S, (fun x : Ωs => Om x i.1 i.2) ⁻¹' u i) := by
    intro S u hu
    refine measInf mOm S _ (fun i hi => ?_)
    exact measurableSet_preimage (f := fun x : Ωs => Om x) hOm'
      (measurableSet_preimage (hproj i) (hu i hi))
  have measHm : ∀ (S : Finset (Fin m × Fin n)) (u : Fin m × Fin n → Set ℝ),
      (∀ i ∈ S, MeasurableSet (u i)) →
      MeasurableSet[mHm] (⋂ i ∈ S, (fun x : Ωs => Hm x i.1 i.2) ⁻¹' u i) := by
    intro S u hu
    refine measInf mHm S _ (fun i hi => ?_)
    exact measurableSet_preimage (f := fun x : Ωs => Hm x) hHm'
      (measurableSet_preimage (hproj i) (hu i hi))
  have measG : ∀ (S : Finset (Fin T × Fin m × Fin n)) (u : Fin T × Fin m × Fin n → Set ℝ),
      (∀ i ∈ S, MeasurableSet (u i)) →
      MeasurableSet[mG] (⋂ i ∈ S, (fun x : Ωs => G x i.1 i.2.1 i.2.2) ⁻¹' u i) := by
    intro S u hu
    refine measInf mG S _ (fun i hi => ?_)
    exact measurableSet_preimage
      (f := fun x : Ωs => fun tij : Fin T × Fin m × Fin n => G x tij.1 tij.2.1 tij.2.2) hG'
      (measurableSet_preimage (hprojG i) (hu i hi))
  let F : ((Fin m × Fin n) ⊕ ((Fin m × Fin n) ⊕ (Fin T × Fin m × Fin n))) → Ωs → ℝ :=
    fun x s =>
      match x with
      | Sum.inl q => Om s q.1 q.2
      | Sum.inr (Sum.inl q) => Hm s q.1 q.2
      | Sum.inr (Sum.inr q) => G s q.1 q.2.1 q.2.2
  have hμ1 : μ (Set.univ : Set Ωs) = 1 := by
    have h := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hOm_indep)
      (∅ : Finset (Fin m × Fin n)) (sets := fun _ => Set.univ) (fun i hi => by simp at hi)
    simpa using h
  have keyUniv :
      ∀ (sets : ((Fin m × Fin n) ⊕ ((Fin m × Fin n) ⊕ (Fin T × Fin m × Fin n))) → Set ℝ),
      (∀ x, MeasurableSet (sets x)) →
      μ (⋂ x, F x ⁻¹' sets x) = ∏ x, μ (F x ⁻¹' sets x) := by
    intro sets hsets
    set A : Set Ωs := ⋂ a : Fin m × Fin n, (fun x : Ωs => Om x a.1 a.2) ⁻¹' sets (Sum.inl a) with hA
    set B : Set Ωs := ⋂ b : Fin m × Fin n, (fun x : Ωs => Hm x b.1 b.2) ⁻¹' sets (Sum.inr (Sum.inl b)) with hB
    set C : Set Ωs := ⋂ c : Fin T × Fin m × Fin n,
      (fun x : Ωs => G x c.1 c.2.1 c.2.2) ⁻¹' sets (Sum.inr (Sum.inr c)) with hC
    have hA_meas : MeasurableSet[mOm] A := by
      rw [hA]
      refine MeasurableSet.iInter (fun a => ?_)
      exact measurableSet_preimage (f := fun x : Ωs => Om x) hOm'
        (measurableSet_preimage (hproj a) (hsets (Sum.inl a)))
    have hB_meas : MeasurableSet[mHm] B := by
      rw [hB]
      refine MeasurableSet.iInter (fun b => ?_)
      exact measurableSet_preimage (f := fun x : Ωs => Hm x) hHm'
        (measurableSet_preimage (hproj b) (hsets (Sum.inr (Sum.inl b))))
    have hC_meas : MeasurableSet[mG] C := by
      rw [hC]
      refine MeasurableSet.iInter (fun c => ?_)
      exact measurableSet_preimage
        (f := fun x : Ωs => fun tij : Fin T × Fin m × Fin n => G x tij.1 tij.2.1 tij.2.2) hG'
        (measurableSet_preimage (hprojG c) (hsets (Sum.inr (Sum.inr c))))
    have hsplit : (⋂ x, F x ⁻¹' sets x) = A ∩ (B ∩ C) := by
      rw [hA, hB, hC]
      rw [Set.iInter_sum]
      rw [Set.iInter_sum]
    have hprodA : μ A = ∏ a : Fin m × Fin n, μ (F (Sum.inl a) ⁻¹' sets (Sum.inl a)) := by
      rw [hA]
      have h := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hOm_indep)
        (Finset.univ : Finset (Fin m × Fin n)) (sets := fun a => sets (Sum.inl a))
        (fun a _ => hsets (Sum.inl a))
      simpa using h
    have hprodB : μ B = ∏ b : Fin m × Fin n, μ (F (Sum.inr (Sum.inl b)) ⁻¹' sets (Sum.inr (Sum.inl b))) := by
      rw [hB]
      have h := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hHm_indep)
        (Finset.univ : Finset (Fin m × Fin n)) (sets := fun b => sets (Sum.inr (Sum.inl b)))
        (fun b _ => hsets (Sum.inr (Sum.inl b)))
      simpa using h
    have hprodC : μ C = ∏ c : Fin T × Fin m × Fin n,
        μ (F (Sum.inr (Sum.inr c)) ⁻¹' sets (Sum.inr (Sum.inr c))) := by
      rw [hC]
      have h := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hG_indep)
        (Finset.univ : Finset (Fin T × Fin m × Fin n)) (sets := fun c => sets (Sum.inr (Sum.inr c)))
        (fun c _ => hsets (Sum.inr (Sum.inr c)))
      simpa using h
    have hmeas : μ (⋂ x, F x ⁻¹' sets x) = μ A * μ B * μ C := by
      rw [hsplit]
      have hpair : MeasurableSet[mPair] (A ∩ B) :=
        MeasurableSet.inter (hOm_le A hA_meas) (hHm_le B hB_meas)
      have step : μ (A ∩ (B ∩ C)) = μ C * μ (A ∩ B) := by
        rw [← Set.inter_assoc, Set.inter_comm (A ∩ B) C]
        exact hGC C (A ∩ B) hC_meas hpair
      rw [step, hAB A B hA_meas hB_meas]
      ring
    rw [hmeas, hprodA, hprodB, hprodC,
      Fintype.prod_sum_type (f := fun x : (Fin m × Fin n) ⊕ ((Fin m × Fin n) ⊕ (Fin T × Fin m × Fin n)) =>
        μ (F x ⁻¹' sets x)),
      Fintype.prod_sum_type (f := fun y : (Fin m × Fin n) ⊕ (Fin T × Fin m × Fin n) =>
        μ (F (Sum.inr y) ⁻¹' sets (Sum.inr y)))]
    ring
  have key : ∀ (S : Finset ((Fin m × Fin n) ⊕ ((Fin m × Fin n) ⊕ (Fin T × Fin m × Fin n))))
      (sets : ((Fin m × Fin n) ⊕ ((Fin m × Fin n) ⊕ (Fin T × Fin m × Fin n))) → Set ℝ),
      (∀ i ∈ S, MeasurableSet (sets i)) →
      μ (⋂ i ∈ S, F i ⁻¹' sets i) = ∏ i ∈ S, μ (F i ⁻¹' sets i) := by
    intro S sets hsets
    have hsets' : ∀ x : ((Fin m × Fin n) ⊕ ((Fin m × Fin n) ⊕ (Fin T × Fin m × Fin n))),
        MeasurableSet (if x ∈ S then sets x else Set.univ) := by
      intro x
      by_cases hx : x ∈ S
      · simpa [hx] using hsets x hx
      · simpa [hx]
    have h := keyUniv (fun x => if x ∈ S then sets x else Set.univ) hsets'
    have h1 : (⋂ x, F x ⁻¹' (if x ∈ S then sets x else Set.univ))
        = (⋂ x ∈ S, F x ⁻¹' sets x) := by
      ext ω
      simp only [Set.mem_iInter]
      constructor
      · intro hh x hx
        simpa [hx] using hh x
      · intro hh x
        by_cases hx : x ∈ S
        · simpa [hx] using hh x hx
        · simp [hx]
    have hstep : (∏ x, (if x ∈ S then μ (F x ⁻¹' sets x) else 1))
        = ∏ x ∈ S, μ (F x ⁻¹' sets x) := by
      rw [← Finset.prod_subset
        (f := fun x => if x ∈ S then μ (F x ⁻¹' sets x) else 1)
        (Finset.subset_univ S) (fun x _ hx => if_neg hx)]
      exact Finset.prod_congr rfl (fun x hx => by rw [if_pos hx])
    have h2 : (∏ x, μ (F x ⁻¹' (if x ∈ S then sets x else Set.univ)))
        = ∏ x ∈ S, μ (F x ⁻¹' sets x) := by
      rw [← hstep]
      exact Finset.prod_congr rfl (fun x _ => by
        by_cases hx : x ∈ S
        · simp [hx]
        · simp [hx, hμ1])
    rw [h1, h2] at h
    exact h
  refine ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mpr ?_
  intro S sets hsets
  exact key S sets hsets
  /- @proof-region region.target-node.session.97d8037743ba5666 end -/

end Statlib.Imported

