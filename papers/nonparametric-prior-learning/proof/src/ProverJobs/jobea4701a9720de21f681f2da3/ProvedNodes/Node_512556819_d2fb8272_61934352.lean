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
theorem statopia_math_node_512556819_d2fb8272 : ∀ {X Y U Th V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup Th] [NormedSpace ℝ Th] [CompleteSpace Th]
    [TopologicalSpace.SeparableSpace Th] [MeasurableSpace Th] [BorelSpace Th]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V] [MeasurableSpace V] [BorelSpace V]
    (M : Model X Y U Th V)
    (ha : Measurable (Function.uncurry M.ℓ))
    (hb : ∀ (u : U) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun z : X × Y => M.ℓ u z) (D : Measure (X × Y)))
    (hc : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Th) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun u : U => Lmean M.ℓ u (D : Measure (X × Y))) (basePost M k S θ : Measure U))
    (hd : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Th),
      Integrable (fun u : U => Lemp M.ℓ u S) (basePost M k S θ : Measure U))
    (HP : ProbabilityMeasure Th)
    (gam : ℝ) (hgam : 0 < gam)
    (n : ℕ) (hn : 0 < n)
    (ω : Fin n → Block (X × Y))
    (he : ∀ θ : Th, Integrable (Pi1Exp M n gam ω θ)
      (Measure.pi fun i : Fin n => (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)))
    (hf : Integrable (fun θ : Th => Pi1Inner M n gam ω θ) (HP : Measure Th))
    (hg : ∀ i : Fin n, Measurable fun θ : Th =>
      (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)),
    let phi : Th × (Fin n → U) → ℝ := fun x =>
      (1 / (n : ℝ)) * ∑ i : Fin n,
        (Lmean M.ℓ (x.2 i) (DOf ω i : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF ω i));
    let mu : Measure (Th × (Fin n → U)) := (HP : Measure Th).bind (fun θ =>
      (Measure.pi fun i : Fin n =>
        (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
        (fun u : Fin n → U => (θ, u)));
    Measurable phi ∧
      Integrable (fun x : Th × (Fin n → U) => Real.exp (gam * phi x)) mu ∧
      (∫ x : Th × (Fin n → U), Real.exp (gam * phi x) ∂mu =
        ∫ θ : Th, Pi1Inner M n gam ω θ ∂(HP : Measure Th)) := by
  /- @proof-region region.target-node.session.129b578e01e9f296 begin -/
  intro X Y U Th V
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro M ha hb hc hd HP gam hgam n hn ω he hf hg
  dsimp only
  let phi : Th × (Fin n → U) → ℝ := fun x =>
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Lmean M.ℓ (x.2 i) (DOf ω i : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF ω i))
  let mu : Measure (Th × (Fin n → U)) := (HP : Measure Th).bind (fun θ =>
    (Measure.pi fun i : Fin n =>
      (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
      (fun u : Fin n → U => (θ, u)))
  change Measurable phi ∧
    Integrable (fun x : Th × (Fin n → U) => Real.exp (gam * phi x)) mu ∧
    (∫ x : Th × (Fin n → U), Real.exp (gam * phi x) ∂mu =
      ∫ θ : Th, Pi1Inner M n gam ω θ ∂(HP : Measure Th))
  have hpoint : ∀ x : Th × (Fin n → U), Real.exp (gam * phi x) = Pi1Exp M n gam ω x.1 x.2 := by
    intro x
    have hterm : ∀ i : Fin n,
        (Lmean M.ℓ (x.2 i) (DOf ω i : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF ω i))
        = (1 / (((mOf ω i : ℕ)) : ℝ)) * ∑ j : Fin ((mOf ω i : ℕ)),
            (Lmean M.ℓ (x.2 i) (DOf ω i : Measure (X × Y)) - M.ℓ (x.2 i) ((ω i).2 j)) := by
      intro i
      have hm : (((mOf ω i : ℕ)) : ℝ) ≠ 0 := by
        exact_mod_cast (mOf ω i).pos.ne'
      simp only [Lemp, SOF, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
    simp only [Pi1Exp, phi, hterm]
    congr 1
    ring
  have hphi : Measurable phi := by
    have hL : ∀ i : Fin n, Measurable fun u : Fin n → U =>
        Lmean M.ℓ (u i) (DOf ω i : Measure (X × Y)) := by
      intro i
      have hsm : StronglyMeasurable fun u : Fin n → U =>
          ∫ z, M.ℓ (u i) z ∂(DOf ω i : Measure (X × Y)) := by
        refine StronglyMeasurable.integral_prod_right (ν := (DOf ω i : Measure (X × Y)))
          (f := fun (u : Fin n → U) (z : X × Y) => M.ℓ (u i) z) ?_
        have hmap : Measurable fun p : (Fin n → U) × (X × Y) => (p.1 i, p.2) :=
          ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
        exact (ha.comp (f := fun p : (Fin n → U) × (X × Y) => (p.1 i, p.2)) hmap).stronglyMeasurable
      exact hsm.measurable
    have hE : ∀ i : Fin n, Measurable fun u : Fin n → U => Lemp M.ℓ (u i) (SOF ω i) := by
      intro i
      have h1 : Measurable fun u : Fin n → U =>
          ∑ j : Fin ((mOf ω i : ℕ)), M.ℓ (u i) ((ω i).2 j) := by
        refine Finset.measurable_sum _ (fun j _ => ?_)
        have hmap : Measurable fun u : Fin n → U => (u i, ((ω i).2 j)) :=
          (measurable_pi_apply i).prodMk measurable_const
        exact ha.comp (f := fun u : Fin n → U => (u i, ((ω i).2 j))) hmap
      exact h1.const_mul (1 / (((mOf ω i : ℕ)) : ℝ))
    have hsum : Measurable fun u : Fin n → U => ∑ i : Fin n,
        (Lmean M.ℓ (u i) (DOf ω i : Measure (X × Y)) - Lemp M.ℓ (u i) (SOF ω i)) := by
      exact Finset.measurable_sum _ (fun i _ => (hL i).sub (hE i))
    exact (hsum.const_mul (1 / (n : ℝ))).comp measurable_snd
  have hK : Measurable fun θ : Th => (Measure.pi fun i : Fin n =>
      (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map (fun u : Fin n → U => (θ, u)) := by
    have huniv : ∀ θ : Th, (Measure.pi fun i : Fin n =>
        (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) Set.univ = 1 := by
      intro θ
      rw [show (Set.univ : Set (Fin n → U)) = Set.univ.pi (fun _ => Set.univ) from by
        ext x
        simp]
      rw [Measure.pi_pi]
      exact Finset.prod_eq_one fun i _ => measure_univ
    have hpi : Measurable fun θ : Th => Measure.pi fun i : Fin n =>
        (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) := by
      refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
      let S : Set (Set (Fin n → U)) :=
        {t | ∃ β : Fin n → Set U, (∀ i, MeasurableSet (β i)) ∧ t = Set.univ.pi β}
      have hgen : (inferInstance : MeasurableSpace (Fin n → U)) =
          MeasurableSpace.generateFrom S := by
        refine le_antisymm ?_ ?_
        · rw [show (inferInstance : MeasurableSpace (Fin n → U)) =
              ⨆ i, MeasurableSpace.comap (Function.eval i)
                (inferInstance : MeasurableSpace U) from rfl]
          refine iSup_le fun i s hs => ?_
          obtain ⟨u, hu, rfl⟩ := hs
          have hEq : Function.eval i ⁻¹' u = Set.univ.pi
              (Function.update (fun _ => (Set.univ : Set U)) i u) := Set.eval_preimage
          rw [hEq]
          refine MeasurableSpace.measurableSet_generateFrom ⟨
            Function.update (fun _ => (Set.univ : Set U)) i u, fun j => ?_, rfl⟩
          by_cases hji : j = i
          · subst hji
            simpa using hu
          · simp [Function.update, hji]
        · apply MeasurableSpace.generateFrom_le
          rintro t ⟨β, hβ, rfl⟩
          have hEq : Set.univ.pi β = ⋂ i, Function.eval i ⁻¹' β i := by
            ext x
            simp [Set.mem_pi]
          rw [hEq]
          exact MeasurableSet.iInter fun i => (hβ i).preimage (measurable_pi_apply i)
      have hpiSys : IsPiSystem S := by
        rintro t ⟨β, hβ, rfl⟩ t' ⟨γ, hγ, rfl⟩ _
        exact ⟨fun i => β i ∩ γ i, fun i => (hβ i).inter (hγ i), by
          ext x
          simp [Set.mem_inter_iff, Set.mem_pi, forall_and]⟩
      refine MeasurableSpace.induction_on_inter
        (C := fun t _ => Measurable fun θ : Th =>
          (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) t)
        hgen hpiSys ?_ ?_ ?_ ?_ t ht
      · simp only [MeasureTheory.measure_empty]
        exact measurable_const
      · rintro t ⟨β, hβ, rfl⟩
        have hEq : (fun θ : Th => (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) (Set.univ.pi β)) =
            fun θ : Th => ∏ i : Fin n,
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (β i) := by
          funext θ
          exact Measure.pi_pi _ _
        rw [hEq]
        exact Finset.measurable_prod _ fun i _ => (Measure.measurable_coe (hβ i)).comp (hg i)
      · intro t ht htm
        have hle : ∀ θ : Th, (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) t ≤ 1 := by
          intro θ
          rw [← huniv θ]
          exact measure_mono (Set.subset_univ t)
        have hEq : ∀ θ : Th, (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) tᶜ =
            1 - (Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) t := by
          intro θ
          rw [measure_compl ht (ne_top_of_le_ne_top ENNReal.one_ne_top (hle θ)), huniv θ]
        simp only [hEq]
        exact Measurable.sub measurable_const htm
      · intro f hdisj hfm hfM
        have hEq : ∀ θ : Th, (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) (⋃ i, f i) =
            ∑' i, (Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) (f i) := by
          intro θ
          exact measure_iUnion hdisj hfm
        simp only [hEq]
        exact Measurable.ennreal_tsum hfM
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    let R : Set (Set (Th × (Fin n → U))) :=
      {s | ∃ a : Set Th, MeasurableSet a ∧ ∃ b : Set (Fin n → U), MeasurableSet b ∧ s = a ×ˢ b}
    have hgenR : (inferInstance : MeasurableSpace (Th × (Fin n → U))) =
        MeasurableSpace.generateFrom R := by
      refine le_antisymm ?_ ?_
      · rw [show (inferInstance : MeasurableSpace (Th × (Fin n → U))) =
            MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Th) ⊔
              MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin n → U))
            from rfl]
        refine sup_le ?_ ?_
        · intro s hs
          obtain ⟨u, hu, rfl⟩ := hs
          have hEq : Prod.fst ⁻¹' u = u ×ˢ (Set.univ : Set (Fin n → U)) := by
            ext x
            simp [Set.mem_prod]
          rw [hEq]
          exact MeasurableSpace.measurableSet_generateFrom
            ⟨u, hu, Set.univ, MeasurableSet.univ, rfl⟩
        · intro s hs
          obtain ⟨u, hu, rfl⟩ := hs
          have hEq : Prod.snd ⁻¹' u = (Set.univ : Set Th) ×ˢ u := by
            ext x
            simp [Set.mem_prod]
          rw [hEq]
          exact MeasurableSpace.measurableSet_generateFrom
            ⟨Set.univ, MeasurableSet.univ, u, hu, rfl⟩
      · apply MeasurableSpace.generateFrom_le
        intro s hs
        simp only [R, Set.mem_setOf_eq] at hs
        obtain ⟨a, ha', b, hb', rfl⟩ := hs
        have hEq : a ×ˢ b = Prod.fst ⁻¹' a ∩ Prod.snd ⁻¹' b := by
          ext x
          simp [Set.mem_prod]
        rw [hEq]
        exact ((ha').preimage measurable_fst).inter ((hb').preimage measurable_snd)
    have hpiSysR : IsPiSystem R := by
      intro s hs s' hs'
      simp only [R, Set.mem_setOf_eq] at hs hs'
      obtain ⟨a, ha', b, hb', rfl⟩ := hs
      obtain ⟨a', ha'', b', hb'', rfl⟩ := hs'
      intro _
      exact ⟨a ∩ a', ha'.inter ha'', b ∩ b', hb'.inter hb'', by
        ext x
        simp [Set.mem_inter_iff, Set.mem_prod, and_left_comm, and_assoc]⟩
    have hKuniv : ∀ θ : Th, (Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n =>
        (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) Set.univ = 1 := by
      intro θ
      rw [← Measure.dirac_prod]
      rw [show (Set.univ : Set (Th × (Fin n → U))) = Set.univ ×ˢ Set.univ from by
        ext x
        simp]
      rw [Measure.prod_prod, measure_univ, huniv θ, mul_one]
    refine MeasurableSpace.induction_on_inter
      (C := fun s _ => Measurable fun θ : Th =>
        (Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) s)
      hgenR hpiSysR ?_ ?_ ?_ ?_ t ht
    · simp only [MeasureTheory.measure_empty]
      exact measurable_const
    · intro s hs
      simp only [R, Set.mem_setOf_eq] at hs
      obtain ⟨a, ha', b, hb', rfl⟩ := hs
      have hEq : ∀ θ : Th, (Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) (a ×ˢ b) =
          (Measure.dirac θ) a * (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) b := by
        intro θ
        rw [← Measure.dirac_prod]
        exact Measure.prod_prod a b
      simp only [hEq]
      have h1 : Measurable fun θ : Th => (Measure.dirac θ) a :=
        (Measure.measurable_coe ha').comp Measure.measurable_dirac
      have h2 : Measurable fun θ : Th => (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) b :=
        (Measure.measurable_coe hb').comp hpi
      exact h1.mul h2
    · intro s hs hsm
      have hle : ∀ θ : Th, (Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) s ≤ 1 := by
        intro θ
        rw [← hKuniv θ]
        exact measure_mono (Set.subset_univ s)
      have hEq : ∀ θ : Th, (Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) sᶜ =
          1 - (Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) s := by
        intro θ
        rw [measure_compl hs (ne_top_of_le_ne_top ENNReal.one_ne_top (hle θ)), hKuniv θ]
      simp only [hEq]
      exact Measurable.sub measurable_const hsm
    · intro f hdisj hfm hfM
      have hEq : ∀ θ : Th, (Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) (⋃ i, f i) =
          ∑' i, (Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) (f i) := by
        intro θ
        exact measure_iUnion hdisj hfm
      simp only [hEq]
      exact Measurable.ennreal_tsum hfM
  have hlin : ∫⁻ x, ENNReal.ofReal (Real.exp (gam * phi x)) ∂mu
      = ENNReal.ofReal (∫ θ : Th, Pi1Inner M n gam ω θ ∂(HP : Measure Th)) := by
    have hF : Measurable fun x : Th × (Fin n → U) =>
        ENNReal.ofReal (Real.exp (gam * phi x)) :=
      (Real.measurable_exp.comp (measurable_const.mul hphi)).ennreal_ofReal
    have hν : (fun θ : Th => ∫⁻ u, ENNReal.ofReal (Pi1Exp M n gam ω θ u)
        ∂(Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)))
        = fun θ : Th => ENNReal.ofReal (Pi1Inner M n gam ω θ) := by
      funext θ
      exact (ofReal_integral_eq_lintegral_ofReal (he θ)
        (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)).symm
    calc ∫⁻ x, ENNReal.ofReal (Real.exp (gam * phi x)) ∂mu
        = ∫⁻ θ, ∫⁻ x, ENNReal.ofReal (Real.exp (gam * phi x))
            ∂((Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
              fun u : Fin n → U => (θ, u)) ∂(HP : Measure Th) :=
          Measure.lintegral_bind hK.aemeasurable hF.aemeasurable
      _ = ∫⁻ θ, ∫⁻ u, ENNReal.ofReal (Real.exp (gam * phi (θ, u)))
            ∂(Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) ∂(HP : Measure Th) := by
          apply lintegral_congr
          intro θ
          exact lintegral_map hF (measurable_const.prodMk measurable_id)
      _ = ∫⁻ θ, ∫⁻ u, ENNReal.ofReal (Pi1Exp M n gam ω θ u)
            ∂(Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) ∂(HP : Measure Th) := by
          apply lintegral_congr
          intro θ
          apply lintegral_congr
          intro u
          rw [hpoint]
      _ = ∫⁻ θ, ENNReal.ofReal (Pi1Inner M n gam ω θ) ∂(HP : Measure Th) := by
          rw [hν]
      _ = ENNReal.ofReal (∫ θ : Th, Pi1Inner M n gam ω θ ∂(HP : Measure Th)) :=
          (ofReal_integral_eq_lintegral_ofReal hf
            (Filter.Eventually.of_forall fun θ =>
              integral_nonneg fun u => (Real.exp_pos _).le)).symm
  have hExp : Integrable (fun x : Th × (Fin n → U) => Real.exp (gam * phi x)) mu := by
    have hmeas : Measurable fun x : Th × (Fin n → U) => Real.exp (gam * phi x) :=
      Real.measurable_exp.comp (measurable_const.mul hphi)
    have hne : (∫⁻ x, ENNReal.ofReal (Real.exp (gam * phi x)) ∂mu) ≠ ⊤ := by
      rw [hlin]
      exact ENNReal.ofReal_ne_top
    have hfin : HasFiniteIntegral (fun x : Th × (Fin n → U) => Real.exp (gam * phi x)) mu := by
      simp only [HasFiniteIntegral]
      have hnorm : ∀ x : Th × (Fin n → U),
          ‖Real.exp (gam * phi x)‖ₑ = ENNReal.ofReal (Real.exp (gam * phi x)) :=
        fun x => Real.enorm_of_nonneg (Real.exp_pos _).le
      simp only [hnorm]
      exact lt_of_le_of_ne le_top hne
    exact ⟨hmeas.aestronglyMeasurable, hfin⟩
  refine ⟨hphi, hExp, ?_⟩
  · have h1 : ENNReal.ofReal (∫ x : Th × (Fin n → U), Real.exp (gam * phi x) ∂mu)
        = ∫⁻ x, ENNReal.ofReal (Real.exp (gam * phi x)) ∂mu :=
      ofReal_integral_eq_lintegral_ofReal hExp
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    have h3 : ENNReal.ofReal (∫ x : Th × (Fin n → U), Real.exp (gam * phi x) ∂mu)
        = ENNReal.ofReal (∫ θ : Th, Pi1Inner M n gam ω θ ∂(HP : Measure Th)) := by
      rw [h1]
      exact hlin
    have ha1 : 0 ≤ ∫ x : Th × (Fin n → U), Real.exp (gam * phi x) ∂mu :=
      integral_nonneg fun x => (Real.exp_pos _).le
    have ha2 : 0 ≤ ∫ θ : Th, Pi1Inner M n gam ω θ ∂(HP : Measure Th) :=
      integral_nonneg fun θ => integral_nonneg fun u => (Real.exp_pos _).le
    have h4 := congrArg ENNReal.toReal h3
    simpa only [ENNReal.toReal_ofReal ha1, ENNReal.toReal_ofReal ha2] using h4
  /- @proof-region region.target-node.session.129b578e01e9f296 end -/

end
end Statlib.Imported
