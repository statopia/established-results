import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_944887933_296b41c2_3665ec26

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1948306332_1c10abd5 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hX : ∀ i : Fin n, Measurable (X i))
    (hY : ∀ i : Fin m, Measurable (Y i))
    (hF : ∀ i : Fin n, Measurable (F i))
    (hG : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (i : Fin n),
    let Zstar : Ω × Ω → Fin p → ℝ := fun x k =>
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) +
          Real.sqrt (1 - t) * (F i x.2 k - muX k))
    let Z : Ω × Ω → Fin p → ℝ := fun x k =>
      (∑ i' : Fin n,
          (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (X i' x.1 k - muX k) + Real.sqrt (1 - v) * (F i' x.1 k - muX k)) +
              Real.sqrt (1 - t) * (F i' x.2 k - muX k))) +
        (∑ i' : Fin m,
          (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k - muY k) + Real.sqrt (1 - v) * (G i' x.1 k - muY k)) +
              Real.sqrt (1 - t) * (G i' x.2 k - muY k)))
    IndepFun (fun x : Ω × Ω => fun k : Fin p => Z x k - Zstar x k)
      (fun x : Ω × Ω => fun k : Fin p => (X i x.1 k, F i x.1 k, F i x.2 k)) (P.prod P) := by
  /- @proof-region region.target-node.session.c5fbf8262f6b9dd9 begin -/
  classical
  intro Ω _ P _ n m p delta muX muY X Y F G hX hY hF hG hindep v hv0 hv1 t ht0 ht1 i
  intro Zstar Z
  have hfam_meas : ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)), Measurable (jointFam X Y F G a) := by
    intro a
    cases a with
    | inl i' => exact hX i'
    | inr b =>
      cases b with
      | inl i' => exact hY i'
      | inr c =>
        cases c with
        | inl i' => exact hF i'
        | inr i' => exact hG i'
  set famD :
      (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕ (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) →
        Ω × Ω → (Fin p → ℝ) :=
    fun q =>
      Sum.elim (fun a x => jointFam X Y F G a x.1) (fun a x => jointFam X Y F G a x.2) q
    with hfamD
  have hfamD_meas : ∀ q, Measurable (famD q) := by
    rintro (a | a)
    · simpa [hfamD] using (hfam_meas a).comp measurable_fst
    · simpa [hfamD] using (hfam_meas a).comp measurable_snd
  have hfamD_indep : iIndepFun famD (P.prod P) := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    have hmain :
        ∀ (u : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
            (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))) → Set (Fin p → ℝ)),
          (∀ q, MeasurableSet (u q)) →
          (P.prod P) (⋂ q, famD q ⁻¹' u q) = ∏ q, (P.prod P) (famD q ⁻¹' u q) := by
      intro u hu
      have hcyl :
          (⋂ q, famD q ⁻¹' u q)
            = {y : Ω | ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
                jointFam X Y F G a y ∈ u (Sum.inl a)}
              ×ˢ {y : Ω | ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
                jointFam X Y F G a y ∈ u (Sum.inr a)} := by
        ext x
        simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq]
        constructor
        · intro h
          exact ⟨fun a => by simpa [hfamD] using h (Sum.inl a),
            fun a => by simpa [hfamD] using h (Sum.inr a)⟩
        · rintro ⟨h1, h2⟩ (a | a)
          · simpa [hfamD] using h1 a
          · simpa [hfamD] using h2 a
      have hL :
          P {y : Ω | ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
              jointFam X Y F G a y ∈ u (Sum.inl a)}
            = ∏ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
                P (jointFam X Y F G a ⁻¹' u (Sum.inl a)) := by
        have h0 := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hindep) Finset.univ
          (sets := fun a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)) => u (Sum.inl a))
          (fun a _ => hu (Sum.inl a))
        have hset : {y : Ω | ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
              jointFam X Y F G a y ∈ u (Sum.inl a)}
            = ⋂ a ∈ (Finset.univ : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))),
                jointFam X Y F G a ⁻¹' u (Sum.inl a) := by
          ext y
          simp
        rw [hset, h0]
      have hR :
          P {y : Ω | ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
              jointFam X Y F G a y ∈ u (Sum.inr a)}
            = ∏ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
                P (jointFam X Y F G a ⁻¹' u (Sum.inr a)) := by
        have h0 := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hindep) Finset.univ
          (sets := fun a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)) => u (Sum.inr a))
          (fun a _ => hu (Sum.inr a))
        have hset : {y : Ω | ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
              jointFam X Y F G a y ∈ u (Sum.inr a)}
            = ⋂ a ∈ (Finset.univ : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))),
                jointFam X Y F G a ⁻¹' u (Sum.inr a) := by
          ext y
          simp
        rw [hset, h0]
      have hfacL : ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
          (P.prod P) (famD (Sum.inl a) ⁻¹' u (Sum.inl a))
            = P (jointFam X Y F G a ⁻¹' u (Sum.inl a)) := by
        intro a
        have h : famD (Sum.inl a) ⁻¹' u (Sum.inl a)
            = (jointFam X Y F G a ⁻¹' u (Sum.inl a)) ×ˢ Set.univ := by
          ext x
          simp [hfamD]
        rw [h, Measure.prod_prod, measure_univ, mul_one]
      have hfacR : ∀ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
          (P.prod P) (famD (Sum.inr a) ⁻¹' u (Sum.inr a))
            = P (jointFam X Y F G a ⁻¹' u (Sum.inr a)) := by
        intro a
        have h : famD (Sum.inr a) ⁻¹' u (Sum.inr a)
            = Set.univ ×ˢ (jointFam X Y F G a ⁻¹' u (Sum.inr a)) := by
          ext x
          simp [hfamD]
        rw [h, Measure.prod_prod, measure_univ, one_mul]
      have hsplit :
          (∏ q : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
              (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))),
              (P.prod P) (famD q ⁻¹' u q))
            = (∏ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
                  P (jointFam X Y F G a ⁻¹' u (Sum.inl a)))
              * (∏ a : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
                  P (jointFam X Y F G a ⁻¹' u (Sum.inr a))) := by
        rw [Fintype.prod_sum_type]
        congr 1
        · exact Finset.prod_congr rfl (fun a _ => hfacL a)
        · exact Finset.prod_congr rfl (fun a _ => hfacR a)
      rw [hcyl, Measure.prod_prod, hL, hR, hsplit]
    have hu : ∀ q, MeasurableSet (if q ∈ S then sets q else Set.univ) := by
      intro q
      by_cases hq : q ∈ S
      · rw [if_pos hq]
        exact hsets q hq
      · rw [if_neg hq]
        exact MeasurableSet.univ
    have h1 := hmain (fun q => if q ∈ S then sets q else Set.univ) hu
    have hI : (⋂ q, famD q ⁻¹' (if q ∈ S then sets q else Set.univ))
        = ⋂ q ∈ S, famD q ⁻¹' sets q := by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro h q hq
        simpa [hq] using h q
      · intro h q
        by_cases hq : q ∈ S
        · simpa [hq] using h q hq
        · simp [hq]
    have hstep :
        ∀ q : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
            (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))),
          (P.prod P) (famD q ⁻¹' (if q ∈ S then sets q else Set.univ))
            = if q ∈ S then (P.prod P) (famD q ⁻¹' sets q) else 1 := by
      intro q
      by_cases hq : q ∈ S
      · rw [if_pos hq, if_pos hq]
      · rw [if_neg hq, if_neg hq, Set.preimage_univ, measure_univ]
    have hP :
        (∏ q : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
            (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))),
            (P.prod P) (famD q ⁻¹' (if q ∈ S then sets q else Set.univ)))
          = ∏ q ∈ S, (P.prod P) (famD q ⁻¹' sets q) := by
      have hcongr :
          (∏ q : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
              (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))),
              (P.prod P) (famD q ⁻¹' (if q ∈ S then sets q else Set.univ)))
            = ∏ q : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
                (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))),
                if q ∈ S then (P.prod P) (famD q ⁻¹' sets q) else 1 :=
            Finset.prod_congr rfl (fun q _ => hstep q)
      rw [hcongr]
      have hsub := (Finset.prod_subset (s₁ := S) (s₂ := Finset.univ)
        (f := fun q => if q ∈ S then (P.prod P) (famD q ⁻¹' sets q) else 1)
        (Finset.subset_univ S) (fun x _ hx => if_neg hx)).symm
      rw [hsub]
      exact Finset.prod_congr rfl (fun x hx => if_pos hx)
    rw [hI, hP] at h1
    exact h1
  set Sf : Finset
      ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕ (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))) :=
    {Sum.inl (Sum.inl i), Sum.inl (Sum.inr (Sum.inr (Sum.inl i))),
      Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))} with hSf
  set Tf : Finset
      ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕ (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))) :=
    Finset.univ \ Sf with hTf
  have hdisj : Disjoint Sf Tf := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  have hsplit := hfamD_indep.indepFun_finset Tf Sf hdisj.symm hfamD_meas
  have hmS1 : (Sum.inl (Sum.inl i) : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
      (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∈ Sf := by simp [hSf]
  have hmS2 : (Sum.inl (Sum.inr (Sum.inr (Sum.inl i))) : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
      (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∈ Sf := by simp [hSf]
  have hmS3 : (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
      (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∈ Sf := by simp [hSf]
  have hmemX : ∀ i' : Fin n, i' ≠ i → (Sum.inl (Sum.inl i') : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
      (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∈ Tf := by
    intro i' hi
    rw [hTf, Finset.mem_sdiff, hSf]
    exact ⟨Finset.mem_univ _, by simp [hi]⟩
  have hmemF1 : ∀ i' : Fin n, i' ≠ i → (Sum.inl (Sum.inr (Sum.inr (Sum.inl i'))) :
      ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕ (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∈ Tf := by
    intro i' hi
    rw [hTf, Finset.mem_sdiff, hSf]
    exact ⟨Finset.mem_univ _, by simp [hi]⟩
  have hmemF2 : ∀ i' : Fin n, i' ≠ i → (Sum.inr (Sum.inr (Sum.inr (Sum.inl i'))) :
      ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕ (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∈ Tf := by
    intro i' hi
    rw [hTf, Finset.mem_sdiff, hSf]
    exact ⟨Finset.mem_univ _, by simp [hi]⟩
  have hmemY : ∀ i' : Fin m, (Sum.inl (Sum.inr (Sum.inl i')) : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
      (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∈ Tf := by
    intro i'
    rw [hTf, Finset.mem_sdiff, hSf]
    exact ⟨Finset.mem_univ _, by simp⟩
  have hmemG1 : ∀ i' : Fin m, (Sum.inl (Sum.inr (Sum.inr (Sum.inr i'))) :
      ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕ (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∈ Tf := by
    intro i'
    rw [hTf, Finset.mem_sdiff, hSf]
    exact ⟨Finset.mem_univ _, by simp⟩
  have hmemG2 : ∀ i' : Fin m, (Sum.inr (Sum.inr (Sum.inr (Sum.inr i'))) :
      ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕ (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) ∈ Tf := by
    intro i'
    rw [hTf, Finset.mem_sdiff, hSf]
    exact ⟨Finset.mem_univ _, by simp⟩
  have hevS : ∀ (q : ↑Sf) (k : Fin p),
      Measurable (fun u : ((q' : ↑Sf) → (Fin p → ℝ)) => u q k) :=
    fun q k => measurable_pi_iff.mp (measurable_pi_iff.mp measurable_id q) k
  set φ : ((q : ↑Sf) → (Fin p → ℝ)) → Fin p → (ℝ × ℝ × ℝ) :=
    fun u k => (u ⟨Sum.inl (Sum.inl i), hmS1⟩ k,
      u ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inl i))), hmS2⟩ k,
      u ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl i))), hmS3⟩ k)
    with hφ
  have hφ_meas : Measurable φ := by
    rw [hφ, measurable_pi_iff]
    intro k
    exact Measurable.prodMk (hevS ⟨Sum.inl (Sum.inl i), hmS1⟩ k)
      (Measurable.prodMk (hevS ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inl i))), hmS2⟩ k)
        (hevS ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl i))), hmS3⟩ k))
  have hφblk : (φ ∘ fun a (q : ↑Sf) => famD (↑q) a)
      = fun x k => (X i x.1 k, F i x.1 k, F i x.2 k) := by
    funext x k
    simp only [Function.comp_apply, hφ]
    rfl
  set Ufun : ((q : ↑Tf) → (Fin p → ℝ)) →
      ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕ (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))) → Fin p → ℝ :=
    fun u q => if h : q ∈ Tf then u ⟨q, h⟩ else 0 with hUfun
  set ψ : ((q : ↑Tf) → (Fin p → ℝ)) → Fin p → ℝ :=
    fun u k =>
      (∑ i' : Fin n,
          (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (Ufun u (Sum.inl (Sum.inl i')) k - muX k) +
                Real.sqrt (1 - v) * (Ufun u (Sum.inl (Sum.inr (Sum.inr (Sum.inl i')))) k - muX k)) +
              Real.sqrt (1 - t) * (Ufun u (Sum.inr (Sum.inr (Sum.inr (Sum.inl i')))) k - muX k)))
        + (∑ i' : Fin m,
          (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Ufun u (Sum.inl (Sum.inr (Sum.inl i'))) k - muY k) +
                Real.sqrt (1 - v) * (Ufun u (Sum.inl (Sum.inr (Sum.inr (Sum.inr i')))) k - muY k)) +
              Real.sqrt (1 - t) * (Ufun u (Sum.inr (Sum.inr (Sum.inr (Sum.inr i')))) k - muY k)))
        + ((Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * muX k + Real.sqrt (1 - v) * muX k) +
              Real.sqrt (1 - t) * muX k))
    with hψ
  have hUmeas : ∀ (q : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) ⊕
      (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))))) (k : Fin p),
      Measurable (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) => Ufun u q k) := by
    intro q k
    by_cases hq : q ∈ Tf
    · have h1 : (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) => Ufun u q k)
          = fun u : ((q' : ↑Tf) → (Fin p → ℝ)) => u ⟨q, hq⟩ k := by
        funext u
        simp only [hUfun, dif_pos hq]
      rw [h1]
      exact measurable_pi_iff.mp (measurable_pi_iff.mp measurable_id (⟨q, hq⟩ : ↑Tf)) k
    · have h1 : (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) => Ufun u q k)
          = fun _ : ((q' : ↑Tf) → (Fin p → ℝ)) => (0 : ℝ) := by
        funext u
        simp [hUfun, dif_neg hq]
      rw [h1]
      exact measurable_const
  have hsum_meas : ∀ (ι : Type) (s : Finset ι) (g : ι → ((q' : ↑Tf) → (Fin p → ℝ)) → ℝ),
      (∀ i ∈ s, Measurable (g i)) → Measurable (fun u => ∑ i ∈ s, g i u) := by
    intro ι s
    induction s using Finset.induction_on with
    | empty =>
      intro g _
      simpa using (measurable_const : Measurable fun _ : ((q' : ↑Tf) → (Fin p → ℝ)) => (0 : ℝ))
    | insert a s ha ih =>
      intro g hg
      have h1 : Measurable (g a) := hg a (Finset.mem_insert_self a s)
      have h2 : Measurable (fun u => ∑ i ∈ s, g i u) :=
        ih g (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      have heq : (fun u => ∑ i ∈ insert a s, g i u) = fun u => g a u + ∑ i ∈ s, g i u := by
        funext u
        rw [Finset.sum_insert ha]
      rw [heq]
      exact h1.add h2
  have hψ_meas : Measurable ψ := by
    rw [hψ, measurable_pi_iff]
    intro k
    have hN : Measurable (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) =>
        ∑ i' : Fin n,
          (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (Ufun u (Sum.inl (Sum.inl i')) k - muX k) +
                Real.sqrt (1 - v) * (Ufun u (Sum.inl (Sum.inr (Sum.inr (Sum.inl i')))) k - muX k)) +
              Real.sqrt (1 - t) * (Ufun u (Sum.inr (Sum.inr (Sum.inr (Sum.inl i')))) k - muX k))) := by
      refine hsum_meas (Fin n) (Finset.univ : Finset (Fin n))
        (fun i' u => (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t * (Real.sqrt v * (Ufun u (Sum.inl (Sum.inl i')) k - muX k) +
                Real.sqrt (1 - v) * (Ufun u (Sum.inl (Sum.inr (Sum.inr (Sum.inl i')))) k - muX k)) +
              Real.sqrt (1 - t) * (Ufun u (Sum.inr (Sum.inr (Sum.inr (Sum.inl i')))) k - muX k))) ?_
      intro i' _
      have h1 : Measurable (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) =>
          Ufun u (Sum.inl (Sum.inl i')) k - muX k) :=
        (hUmeas (Sum.inl (Sum.inl i')) k).sub measurable_const
      have h2 : Measurable (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) =>
          Ufun u (Sum.inl (Sum.inr (Sum.inr (Sum.inl i')))) k - muX k) :=
        (hUmeas (Sum.inl (Sum.inr (Sum.inr (Sum.inl i')))) k).sub measurable_const
      have h3 : Measurable (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) =>
          Ufun u (Sum.inr (Sum.inr (Sum.inr (Sum.inl i')))) k - muX k) :=
        (hUmeas (Sum.inr (Sum.inr (Sum.inr (Sum.inl i')))) k).sub measurable_const
      exact ((((h1.const_mul (Real.sqrt v)).add (h2.const_mul (Real.sqrt (1 - v)))).const_mul
        (Real.sqrt t)).add (h3.const_mul (Real.sqrt (1 - t)))).const_mul ((Real.sqrt (n : ℝ))⁻¹)
    have hM : Measurable (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) =>
        ∑ i' : Fin m,
          (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Ufun u (Sum.inl (Sum.inr (Sum.inl i'))) k - muY k) +
                Real.sqrt (1 - v) * (Ufun u (Sum.inl (Sum.inr (Sum.inr (Sum.inr i')))) k - muY k)) +
              Real.sqrt (1 - t) * (Ufun u (Sum.inr (Sum.inr (Sum.inr (Sum.inr i')))) k - muY k))) := by
      refine hsum_meas (Fin m) (Finset.univ : Finset (Fin m))
        (fun i' u => (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t * (Real.sqrt v * (Ufun u (Sum.inl (Sum.inr (Sum.inl i'))) k - muY k) +
                Real.sqrt (1 - v) * (Ufun u (Sum.inl (Sum.inr (Sum.inr (Sum.inr i')))) k - muY k)) +
              Real.sqrt (1 - t) * (Ufun u (Sum.inr (Sum.inr (Sum.inr (Sum.inr i')))) k - muY k))) ?_
      intro i' _
      have h1 : Measurable (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) =>
          Ufun u (Sum.inl (Sum.inr (Sum.inl i'))) k - muY k) :=
        (hUmeas (Sum.inl (Sum.inr (Sum.inl i'))) k).sub measurable_const
      have h2 : Measurable (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) =>
          Ufun u (Sum.inl (Sum.inr (Sum.inr (Sum.inr i')))) k - muY k) :=
        (hUmeas (Sum.inl (Sum.inr (Sum.inr (Sum.inr i')))) k).sub measurable_const
      have h3 : Measurable (fun u : ((q' : ↑Tf) → (Fin p → ℝ)) =>
          Ufun u (Sum.inr (Sum.inr (Sum.inr (Sum.inr i')))) k - muY k) :=
        (hUmeas (Sum.inr (Sum.inr (Sum.inr (Sum.inr i')))) k).sub measurable_const
      exact ((((h1.const_mul (Real.sqrt v)).add (h2.const_mul (Real.sqrt (1 - v)))).const_mul
        (Real.sqrt t)).add (h3.const_mul (Real.sqrt (1 - t)))).const_mul
        ((Real.sqrt (m : ℝ))⁻¹ * delta n m)
    exact (hN.add hM).add measurable_const
  have hψW : (ψ ∘ fun a (q : ↑Tf) => famD (↑q) a) = fun x k => Z x k - Zstar x k := by
    funext x k
    set AX := fun i' : Fin n =>
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X i' x.1 k - muX k) + Real.sqrt (1 - v) * (F i' x.1 k - muX k)) +
          Real.sqrt (1 - t) * (F i' x.2 k - muX k)) with hAX
    set BY := fun i' : Fin m =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y i' x.1 k - muY k) + Real.sqrt (1 - v) * (G i' x.1 k - muY k)) +
          Real.sqrt (1 - t) * (G i' x.2 k - muY k)) with hBY
    set Dc : ℝ := (Real.sqrt (n : ℝ))⁻¹ *
      (Real.sqrt t * (Real.sqrt v * muX k + Real.sqrt (1 - v) * muX k) + Real.sqrt (1 - t) * muX k) with hDc
    set AU := fun i' : Fin n =>
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v *
              (Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inl (Sum.inl i')) k - muX k) +
            Real.sqrt (1 - v) *
              (Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inl (Sum.inr (Sum.inr (Sum.inl i')))) k - muX k)) +
          Real.sqrt (1 - t) *
            (Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inr (Sum.inr (Sum.inr (Sum.inl i')))) k - muX k)) with hAU
    set BU := fun i' : Fin m =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v *
              (Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inl (Sum.inr (Sum.inl i'))) k - muY k) +
            Real.sqrt (1 - v) *
              (Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inl (Sum.inr (Sum.inr (Sum.inr i')))) k - muY k)) +
          Real.sqrt (1 - t) *
            (Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inr (Sum.inr (Sum.inr (Sum.inr i')))) k - muY k)) with hBU
    have hUx1 : ∀ i' : Fin n, i' ≠ i →
        Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inl (Sum.inl i')) k = X i' x.1 k := by
      intro i' hi
      have hq : (Sum.inl (Sum.inl i')) ∈ Tf := hmemX i' hi
      simp only [hUfun, dif_pos hq]
      rfl
    have hUx2 : ∀ i' : Fin n, i' ≠ i →
        Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inl (Sum.inr (Sum.inr (Sum.inl i')))) k = F i' x.1 k := by
      intro i' hi
      have hq : (Sum.inl (Sum.inr (Sum.inr (Sum.inl i')))) ∈ Tf := hmemF1 i' hi
      simp only [hUfun, dif_pos hq]
      rfl
    have hUx3 : ∀ i' : Fin n, i' ≠ i →
        Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inr (Sum.inr (Sum.inr (Sum.inl i')))) k = F i' x.2 k := by
      intro i' hi
      have hq : (Sum.inr (Sum.inr (Sum.inr (Sum.inl i')))) ∈ Tf := hmemF2 i' hi
      simp only [hUfun, dif_pos hq]
      rfl
    have hUy1 : ∀ i' : Fin m,
        Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inl (Sum.inr (Sum.inl i'))) k = Y i' x.1 k := by
      intro i'
      have hq : (Sum.inl (Sum.inr (Sum.inl i'))) ∈ Tf := hmemY i'
      simp only [hUfun, dif_pos hq]
      rfl
    have hUy2 : ∀ i' : Fin m,
        Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inl (Sum.inr (Sum.inr (Sum.inr i')))) k = G i' x.1 k := by
      intro i'
      have hq : (Sum.inl (Sum.inr (Sum.inr (Sum.inr i')))) ∈ Tf := hmemG1 i'
      simp only [hUfun, dif_pos hq]
      rfl
    have hUy3 : ∀ i' : Fin m,
        Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inr (Sum.inr (Sum.inr (Sum.inr i')))) k = G i' x.2 k := by
      intro i'
      have hq : (Sum.inr (Sum.inr (Sum.inr (Sum.inr i')))) ∈ Tf := hmemG2 i'
      simp only [hUfun, dif_pos hq]
      rfl
    have hUz1 : Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inl (Sum.inl i)) k = 0 := by
      have hq : ¬ ((Sum.inl (Sum.inl i)) ∈ Tf) := by
        intro hc
        rw [hTf, Finset.mem_sdiff] at hc
        exact hc.2 hmS1
      simp [hUfun, dif_neg hq]
    have hUz2 : Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))) k = 0 := by
      have hq : ¬ ((Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))) ∈ Tf) := by
        intro hc
        rw [hTf, Finset.mem_sdiff] at hc
        exact hc.2 hmS2
      simp [hUfun, dif_neg hq]
    have hUz3 : Ufun (fun q' : ↑Tf => famD (↑q') x) (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) k = 0 := by
      have hq : ¬ ((Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) ∈ Tf) := by
        intro hc
        rw [hTf, Finset.mem_sdiff] at hc
        exact hc.2 hmS3
      simp [hUfun, dif_neg hq]
    have hAUev : ∀ i' : Fin n, i' ≠ i → AU i' = AX i' := by
      intro i' hi
      simp only [hAU, hAX, hUx1 i' hi, hUx2 i' hi, hUx3 i' hi]
    have hBUev : ∀ i' : Fin m, BU i' = BY i' := by
      intro i'
      simp only [hBU, hBY, hUy1 i', hUy2 i', hUy3 i']
    have hAUi : AU i = -Dc := by
      simp only [hAU, hDc, hUz1, hUz2, hUz3]
      ring
    have hsum1 : (∑ i' : Fin n, AU i') = (∑ i' : Fin n, AX i') - AX i - Dc := by
      have h1 := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) (f := AU) (Finset.mem_univ i)
      have h2 := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) (f := AX) (Finset.mem_univ i)
      have h3 : (∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i, AU i')
          = ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i, AX i' :=
        Finset.sum_congr rfl (fun i' hi => hAUev i' (Finset.mem_erase.mp hi).1)
      rw [hAUi] at h1
      linarith
    have hsum2 : (∑ i' : Fin m, BU i') = (∑ i' : Fin m, BY i') :=
      Finset.sum_congr rfl (fun i' _ => hBUev i')
    show (∑ i' : Fin n, AU i') + (∑ i' : Fin m, BU i') + Dc
      = (∑ i' : Fin n, AX i') + (∑ i' : Fin m, BY i') - AX i
    rw [hsum1, hsum2]
    ring
  have hmain := hsplit.comp hψ_meas hφ_meas
  rw [hψW, hφblk] at hmain
  exact hmain
  /- @proof-region region.target-node.session.c5fbf8262f6b9dd9 end -/

end

end Statlib.Imported

