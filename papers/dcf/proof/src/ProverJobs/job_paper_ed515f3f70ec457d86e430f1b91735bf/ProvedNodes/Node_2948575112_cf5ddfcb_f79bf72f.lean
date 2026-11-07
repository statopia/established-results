import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

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
theorem statopia_math_node_2948575112_cf5ddfcb : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (κ : (Fin p → ℝ) → ℝ) (j : Fin p)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hcont : Continuous (fun w : Fin p → ℝ => (fderiv ℝ κ w) (Pi.single j (1 : ℝ))))
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (i : Fin n),
    (let Zstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ :=
       fun t x i j =>
         (Real.sqrt (n : ℝ))⁻¹ *
           (Real.sqrt t * (Real.sqrt v * (X i x.1 j - muX j) +
               Real.sqrt (1 - v) * (F i x.1 j - muX j)) +
             Real.sqrt (1 - t) * (F i x.2 j - muX j))
     let Zstarstar : ℝ → Ω × Ω → Fin m → Fin p → ℝ :=
       fun t x i j =>
         (Real.sqrt (m : ℝ))⁻¹ * delta n m *
           (Real.sqrt t * (Real.sqrt v * (Y i x.1 j - muY j) +
               Real.sqrt (1 - v) * (G i x.1 j - muY j)) +
             Real.sqrt (1 - t) * (G i x.2 j - muY j))
     let Z : ℝ → Ω × Ω → Fin p → ℝ :=
       fun t x j => (∑ i : Fin n, Zstar t x i j) + (∑ i : Fin m, Zstarstar t x i j)
     let Zdotstar : ℝ → Ω × Ω → Fin n → Fin p → ℝ :=
       fun t x i j =>
         (Real.sqrt (n : ℝ))⁻¹ *
           ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) +
               Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
             (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
     (fun x : Ω × Ω =>
        (fderiv ℝ κ (fun k : Fin p => Z t x k - Zstar t x i k))
          (Pi.single j (1 : ℝ))) ⟂ᵢ[P.prod P]
       (fun x : Ω × Ω => Zdotstar t x i j)) := by
  /- @proof-region region.target-node.session.0c3db27321dd3037 begin -/
  intro Ω hΩ P hP n m p delta muX muY X Y F G κ j hXm hYm hFm hGm hindep hcont v hv0 hv1 t ht0 ht1 i
  dsimp only
  classical
  let g : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) → Ω → Fin p → ℝ := jointFam X Y F G
  let g' : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool → Ω × Ω → Fin p → ℝ :=
    fun kb => @Bool.rec (fun _ => Ω × Ω → Fin p → ℝ) (fun x => g kb.1 x.2) (fun x => g kb.1 x.1) kb.2
  have hgm : ∀ k : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)), Measurable (g k) := by
    intro k
    rcases k with l | l
    · exact hXm l
    · rcases l with l | l
      · exact hYm l
      · rcases l with l | l
        · exact hFm l
        · exact hGm l
  have hgm' : ∀ kb : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool, Measurable (g' kb) := by
    rintro ⟨k, b⟩
    cases b
    · exact (hgm k).comp measurable_snd
    · exact (hgm k).comp measurable_fst
  have hg' : iIndepFun g' (P.prod P) := by
    rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    have hprob : ∀ kb : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool,
        (P.prod P) (g' kb ⁻¹' sets kb) = P (g kb.1 ⁻¹' sets kb) := by
      rintro ⟨k, b⟩
      cases b
      · have h : g' (k, false) ⁻¹' sets (k, false) = Set.univ ×ˢ (g k ⁻¹' sets (k, false)) := by
          ext x
          show (g k x.2 ∈ sets (k, false)) ↔
            (x.1 ∈ Set.univ ∧ x.2 ∈ g k ⁻¹' sets (k, false))
          simp
        rw [h, Measure.prod_prod, measure_univ, one_mul]
      · have h : g' (k, true) ⁻¹' sets (k, true) = (g k ⁻¹' sets (k, true)) ×ˢ Set.univ := by
          ext x
          show (g k x.1 ∈ sets (k, true)) ↔
            (x.1 ∈ g k ⁻¹' sets (k, true) ∧ x.2 ∈ Set.univ)
          simp
        rw [h, Measure.prod_prod, measure_univ, mul_one]
    have hrect : (⋂ kb ∈ S, g' kb ⁻¹' sets kb)
        = (⋂ kb ∈ S.filter (fun kb => kb.2 = true), g kb.1 ⁻¹' sets kb) ×ˢ
          (⋂ kb ∈ S.filter (fun kb => ¬ (kb.2 = true)), g kb.1 ⁻¹' sets kb) := by
      ext x
      have key : ((∀ kb, kb ∈ S → g' kb x ∈ sets kb) ↔
          ((∀ kb, kb ∈ S ∧ kb.2 = true → g kb.1 x.1 ∈ sets kb) ∧
            (∀ kb, kb ∈ S ∧ ¬ (kb.2 = true) → g kb.1 x.2 ∈ sets kb))) := by
        constructor
        · intro h
          refine ⟨?_, ?_⟩
          · rintro ⟨a, b⟩ ⟨h1, h2⟩
            cases b
            · exact absurd h2 (by simp)
            · exact h (a, true) h1
          · rintro ⟨a, b⟩ ⟨h1, h2⟩
            cases b
            · exact h (a, false) h1
            · exact absurd rfl h2
        · rintro ⟨h1, h2⟩ kb hkb
          obtain ⟨a, b⟩ := kb
          cases b
          · exact h2 (a, false) ⟨hkb, by simp⟩
          · exact h1 (a, true) ⟨hkb, by simp⟩
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_prod, Finset.mem_filter]
      exact key
    let S₁ : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) :=
      (S.filter (fun kb => kb.2 = true)).image Prod.fst
    let S₂ : Finset (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) :=
      (S.filter (fun kb => ¬ (kb.2 = true))).image Prod.fst
    have hE₁ : ((⋂ kb ∈ S.filter (fun kb => kb.2 = true), g kb.1 ⁻¹' sets kb) : Set Ω)
        = ((⋂ k ∈ S₁, g k ⁻¹' sets (k, true)) : Set Ω) := by
      apply Set.ext
      intro x
      simp only [Set.mem_iInter, Set.mem_preimage, Finset.mem_coe]
      constructor
      · intro h k hk
        obtain ⟨kb, hkb, hfst⟩ := Finset.mem_image.mp hk
        obtain ⟨hS, hb⟩ := Finset.mem_filter.mp hkb
        obtain ⟨a, b⟩ := kb
        cases b
        · exact absurd hb (by simp)
        · rw [← hfst]
          exact h (a, true) hkb
      · intro h kb hkb
        obtain ⟨hS, hb⟩ := Finset.mem_filter.mp hkb
        obtain ⟨a, b⟩ := kb
        cases b
        · exact absurd hb (by simp)
        · exact h a (Finset.mem_image.mpr ⟨(a, true), hkb, rfl⟩)
    have hE₂ : ((⋂ kb ∈ S.filter (fun kb => ¬ (kb.2 = true)), g kb.1 ⁻¹' sets kb) : Set Ω)
        = ((⋂ k ∈ S₂, g k ⁻¹' sets (k, false)) : Set Ω) := by
      apply Set.ext
      intro x
      simp only [Set.mem_iInter, Set.mem_preimage, Finset.mem_coe]
      constructor
      · intro h k hk
        obtain ⟨kb, hkb, hfst⟩ := Finset.mem_image.mp hk
        obtain ⟨hS, hb⟩ := Finset.mem_filter.mp hkb
        obtain ⟨a, b⟩ := kb
        cases b
        · rw [← hfst]
          exact h (a, false) hkb
        · exact absurd rfl hb
      · intro h kb hkb
        obtain ⟨hS, hb⟩ := Finset.mem_filter.mp hkb
        obtain ⟨a, b⟩ := kb
        cases b
        · exact h a (Finset.mem_image.mpr ⟨(a, false), hkb, rfl⟩)
        · exact absurd rfl hb
    have hsets₁ : ∀ k ∈ S₁, MeasurableSet (sets (k, true)) := by
      intro k hk
      obtain ⟨kb, hkb, hfst⟩ := Finset.mem_image.mp hk
      obtain ⟨hS, hb⟩ := Finset.mem_filter.mp hkb
      obtain ⟨a, b⟩ := kb
      cases b
      · exact absurd hb (by simp)
      · rw [← hfst]
        exact hsets (a, true) hS
    have hsets₂ : ∀ k ∈ S₂, MeasurableSet (sets (k, false)) := by
      intro k hk
      obtain ⟨kb, hkb, hfst⟩ := Finset.mem_image.mp hk
      obtain ⟨hS, hb⟩ := Finset.mem_filter.mp hkb
      obtain ⟨a, b⟩ := kb
      cases b
      · rw [← hfst]
        exact hsets (a, false) hS
      · exact absurd rfl hb
    have hP₁ : P (⋂ k ∈ S₁, g k ⁻¹' sets (k, true))
        = ∏ k ∈ S₁, P (g k ⁻¹' sets (k, true)) :=
      (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hindep) S₁ hsets₁
    have hP₂ : P (⋂ k ∈ S₂, g k ⁻¹' sets (k, false))
        = ∏ k ∈ S₂, P (g k ⁻¹' sets (k, false)) :=
      (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hindep) S₂ hsets₂
    have hPE₁ : P (⋂ kb ∈ S.filter (fun kb => kb.2 = true), g kb.1 ⁻¹' sets kb)
        = ∏ k ∈ S₁, P (g k ⁻¹' sets (k, true)) := by
      rw [hE₁]
      exact hP₁
    have hPE₂ : P (⋂ kb ∈ S.filter (fun kb => ¬ (kb.2 = true)), g kb.1 ⁻¹' sets kb)
        = ∏ k ∈ S₂, P (g k ⁻¹' sets (k, false)) := by
      rw [hE₂]
      exact hP₂
    have himg : ∀ (b : Bool) (F : Finset ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool)),
        (∀ kb ∈ F, kb.2 = b) →
        (∏ kb ∈ F, P (g kb.1 ⁻¹' sets kb))
          = ∏ k ∈ F.image Prod.fst, P (g k ⁻¹' sets (k, b)) := by
      intro b F
      refine Finset.induction_on F ?_ ?_
      · intro _
        simp
      · intro a F ha ih hb
        have ha2 : a.2 = b := hb a (Finset.mem_insert_self a F)
        have hF : ∀ kb ∈ F, kb.2 = b := fun kb hkb => hb kb (Finset.mem_insert_of_mem hkb)
        have hnot : a.1 ∉ F.image Prod.fst := by
          intro hmem
          obtain ⟨kb, hkb, hfst⟩ := Finset.mem_image.mp hmem
          have hkb2 : kb.2 = b := hF kb hkb
          have hkey : kb = a := Prod.ext hfst (by rw [hkb2, ha2])
          rw [hkey] at hkb
          exact ha hkb
        have hs : sets a = sets (a.1, b) := by
          rw [show a = (a.1, b) from Prod.ext rfl ha2]
        rw [Finset.prod_insert ha, ih hF, Finset.image_insert, Finset.prod_insert hnot, hs]
    have hF₁ : (∏ kb ∈ S.filter (fun kb => kb.2 = true), P (g kb.1 ⁻¹' sets kb))
        = ∏ k ∈ S₁, P (g k ⁻¹' sets (k, true)) :=
      himg true (S.filter (fun kb => kb.2 = true)) (fun kb hkb => (Finset.mem_filter.mp hkb).2)
    have hF₂ : (∏ kb ∈ S.filter (fun kb => ¬ (kb.2 = true)), P (g kb.1 ⁻¹' sets kb))
        = ∏ k ∈ S₂, P (g k ⁻¹' sets (k, false)) :=
      himg false (S.filter (fun kb => ¬ (kb.2 = true))) (fun kb hkb => by
        have h := (Finset.mem_filter.mp hkb).2
        obtain ⟨k, b⟩ := kb
        cases b
        · rfl
        · exact absurd rfl h)
    have hstep : (∏ kb ∈ S, (P.prod P) (g' kb ⁻¹' sets kb))
        = ∏ kb ∈ S, P (g kb.1 ⁻¹' sets kb) :=
      Finset.prod_congr rfl (fun kb _ => hprob kb)
    rw [hrect, Measure.prod_prod, hPE₁, hPE₂, hstep,
      ← Finset.prod_filter_mul_prod_filter_not (s := S) (p := fun kb => kb.2 = true)
        (f := fun kb => P (g kb.1 ⁻¹' sets kb)), hF₁, hF₂]
  let qs : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool) → Prop :=
    fun kb => kb.1 = Sum.inl i ∨ kb.1 = Sum.inr (Sum.inr (Sum.inl i))
  let pT : ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool) → Prop :=
    fun q =>
      match q.1 with
      | Sum.inl l => l ≠ i
      | Sum.inr (Sum.inl _) => True
      | Sum.inr (Sum.inr (Sum.inl l)) => l ≠ i
      | Sum.inr (Sum.inr (Sum.inr _)) => True
  let Sblk : Finset ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool) := Finset.univ.filter qs
  let TB : Finset ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool) := Finset.univ.filter pT
  have hm1 : (Sum.inl i, true) ∈ Sblk :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
  have hm2 : (Sum.inr (Sum.inr (Sum.inl i)), true) ∈ Sblk :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl⟩
  have hm3 : (Sum.inr (Sum.inr (Sum.inl i)), false) ∈ Sblk :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl⟩
  have hdisj : Disjoint TB Sblk := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [TB, Sblk, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨a1, a2⟩ := a
    rcases a1 with l | (l | (l | l))
    · rcases hb with h | h
      · exact ha (by simpa using h)
      · cases h
    · rcases hb with h | h <;> cases h
    · rcases hb with h | h
      · cases h
      · exact ha (by simpa using h)
    · rcases hb with h | h <;> cases h
  have hT1 : ∀ l : Fin n, l ≠ i → (Sum.inl l, true) ∈ TB :=
    fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
  have hT2 : ∀ l : Fin n, l ≠ i → (Sum.inr (Sum.inr (Sum.inl l)), true) ∈ TB :=
    fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
  have hT3 : ∀ l : Fin n, l ≠ i → (Sum.inr (Sum.inr (Sum.inl l)), false) ∈ TB :=
    fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
  have hT4 : ∀ l : Fin m, (Sum.inr (Sum.inl l), true) ∈ TB :=
    fun l => Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩
  have hT5 : ∀ l : Fin m, (Sum.inr (Sum.inr (Sum.inr l)), true) ∈ TB :=
    fun l => Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩
  have hT6 : ∀ l : Fin m, (Sum.inr (Sum.inr (Sum.inr l)), false) ∈ TB :=
    fun l => Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩
  let Sfam : Ω × Ω → (↥Sblk → Fin p → ℝ) :=
    fun x q => g' (q : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool) x
  let Tfam : Ω × Ω → (↥TB → Fin p → ℝ) :=
    fun x q => g' (q : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool) x
  have hblock : Tfam ⟂ᵢ[P.prod P] Sfam :=
    ProbabilityTheory.iIndepFun.indepFun_finset TB Sblk hdisj hg' hgm'
  let hq1 : ↥Sblk := ⟨(Sum.inl i, true), hm1⟩
  let hq2 : ↥Sblk := ⟨(Sum.inr (Sum.inr (Sum.inl i)), true), hm2⟩
  let hq3 : ↥Sblk := ⟨(Sum.inr (Sum.inr (Sum.inl i)), false), hm3⟩
  let B : (↥Sblk → Fin p → ℝ) → ℝ :=
    fun d =>
      (Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (d hq1 j - muX j) +
            Real.sqrt (1 - v) * (d hq2 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (d hq3 j - muX j))
  have hBmeas : Measurable B := by
    change Measurable (fun d : (↥Sblk → Fin p → ℝ) =>
      (Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (d hq1 j - muX j) +
            Real.sqrt (1 - v) * (d hq2 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (d hq3 j - muX j)))
    have e1 : Measurable fun d : (↥Sblk → Fin p → ℝ) => d hq1 j :=
      (measurable_pi_apply j).comp (measurable_pi_apply hq1)
    have e2 : Measurable fun d : (↥Sblk → Fin p → ℝ) => d hq2 j :=
      (measurable_pi_apply j).comp (measurable_pi_apply hq2)
    have e3 : Measurable fun d : (↥Sblk → Fin p → ℝ) => d hq3 j :=
      (measurable_pi_apply j).comp (measurable_pi_apply hq3)
    have f1 : Measurable fun d : (↥Sblk → Fin p → ℝ) => Real.sqrt v * (d hq1 j - muX j) :=
      (e1.sub measurable_const).const_mul _
    have f2 : Measurable fun d : (↥Sblk → Fin p → ℝ) =>
        Real.sqrt (1 - v) * (d hq2 j - muX j) :=
      (e2.sub measurable_const).const_mul _
    have f3 : Measurable fun d : (↥Sblk → Fin p → ℝ) =>
        (2 * Real.sqrt (1 - t))⁻¹ * (d hq3 j - muX j) :=
      (e3.sub measurable_const).const_mul _
    exact ((((f1.add f2).const_mul _).sub f3).const_mul _)
  have key3 : ∀ x : Ω × Ω, B (Sfam x) = (Real.sqrt (n : ℝ))⁻¹ *
      ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) +
          Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
        (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)) := by
    intro x
    show (Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * ((Sfam x) hq1 j - muX j) +
            Real.sqrt (1 - v) * ((Sfam x) hq2 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * ((Sfam x) hq3 j - muX j))
      = (Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) +
            Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
    rfl
  let Zs : Ω × Ω → Fin n → Fin p → ℝ :=
    fun x l k =>
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X l x.1 k - muX k) +
            Real.sqrt (1 - v) * (F l x.1 k - muX k)) +
          Real.sqrt (1 - t) * (F l x.2 k - muX k))
  let Zss : Ω × Ω → Fin m → Fin p → ℝ :=
    fun x l k =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (Y l x.1 k - muY k) +
            Real.sqrt (1 - v) * (G l x.1 k - muY k)) +
          Real.sqrt (1 - t) * (G l x.2 k - muY k))
  have key1 : ∀ x : Ω × Ω,
      (fun k : Fin p => (∑ l : Fin n, Zs x l k) + (∑ l : Fin m, Zss x l k) - Zs x i k)
        = fun k : Fin p => (∑ l ∈ Finset.univ.erase i, Zs x l k) + (∑ l : Fin m, Zss x l k) := by
    intro x
    funext k
    have hsplit : (∑ l : Fin n, Zs x l k) = Zs x i k + ∑ l ∈ Finset.univ.erase i, Zs x l k := by
      conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ i)]
      rw [Finset.sum_insert (show i ∉ Finset.univ.erase i by simp)]
    rw [hsplit]
    ring
  let ext : (↥TB → Fin p → ℝ) → ((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool) → Fin p → ℝ :=
    fun d q k => if h : q ∈ TB then d ⟨q, h⟩ k else 0
  let ZsD : (((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool) → Fin p → ℝ) → Fin n → Fin p → ℝ :=
    fun D l k =>
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (D (Sum.inl l, true) k - muX k) +
            Real.sqrt (1 - v) * (D (Sum.inr (Sum.inr (Sum.inl l)), true) k - muX k)) +
          Real.sqrt (1 - t) * (D (Sum.inr (Sum.inr (Sum.inl l)), false) k - muX k))
  let ZssD : (((Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool) → Fin p → ℝ) → Fin m → Fin p → ℝ :=
    fun D l k =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t * (Real.sqrt v * (D (Sum.inr (Sum.inl l), true) k - muY k) +
            Real.sqrt (1 - v) * (D (Sum.inr (Sum.inr (Sum.inr l)), true) k - muY k)) +
          Real.sqrt (1 - t) * (D (Sum.inr (Sum.inr (Sum.inr l)), false) k - muY k))
  let lopVec : (↥TB → Fin p → ℝ) → Fin p → ℝ :=
    fun d k =>
      (∑ l ∈ Finset.univ.erase i, ZsD (ext d) l k) + (∑ l : Fin m, ZssD (ext d) l k)
  let A : (↥TB → Fin p → ℝ) → ℝ := fun d => (fderiv ℝ κ (lopVec d)) (Pi.single j 1)
  have hsum : ∀ {ι' : Type} (s : Finset ι') (φ : ι' → (↥TB → Fin p → ℝ) → ℝ),
      (∀ l, Measurable (φ l)) → Measurable fun d => ∑ l ∈ s, φ l d := by
    intro ι' s φ hφ
    refine Finset.induction_on s ?_ ?_
    · have h0 : (fun d : (↥TB → Fin p → ℝ) => ∑ l ∈ (∅ : Finset ι'), φ l d)
          = fun _ => (0 : ℝ) := by
        funext d
        simp
      rw [h0]
      exact measurable_const
    · intro a s ha ih
      have h1 : (fun d : (↥TB → Fin p → ℝ) => ∑ l ∈ insert a s, φ l d)
          = fun d => φ a d + ∑ l ∈ s, φ l d := by
        funext d
        rw [Finset.sum_insert ha]
      rw [h1]
      exact (hφ a).add ih
  have hext : ∀ (q : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool) (k : Fin p),
      Measurable fun d : (↥TB → Fin p → ℝ) => ext d q k := by
    intro q k
    by_cases hq : q ∈ TB
    · have h1 : (fun d : (↥TB → Fin p → ℝ) => ext d q k)
          = fun d => d (⟨q, hq⟩ : ↥TB) k := by
        funext d
        show (if h : q ∈ TB then d ⟨q, h⟩ k else 0) = d (⟨q, hq⟩ : ↥TB) k
        rw [dif_pos hq]
      rw [h1]
      exact (measurable_pi_apply k).comp (measurable_pi_apply (⟨q, hq⟩ : ↥TB))
    · have h1 : (fun d : (↥TB → Fin p → ℝ) => ext d q k) = fun _ => (0 : ℝ) := by
        funext d
        show (if h : q ∈ TB then d ⟨q, h⟩ k else 0) = 0
        rw [dif_neg hq]
      rw [h1]
      exact measurable_const
  have hZsD : ∀ (l : Fin n) (k : Fin p),
      Measurable fun d : (↥TB → Fin p → ℝ) => ZsD (ext d) l k := by
    intro l k
    have c1 : Measurable fun _ : (↥TB → Fin p → ℝ) => muX k := measurable_const
    have b1 : Measurable fun d : (↥TB → Fin p → ℝ) =>
        Real.sqrt v * (ext d (Sum.inl l, true) k - muX k) :=
      ((hext (Sum.inl l, true) k).sub c1).const_mul _
    have b2 : Measurable fun d : (↥TB → Fin p → ℝ) =>
        Real.sqrt (1 - v) * (ext d (Sum.inr (Sum.inr (Sum.inl l)), true) k - muX k) :=
      ((hext (Sum.inr (Sum.inr (Sum.inl l)), true) k).sub c1).const_mul _
    have b3 : Measurable fun d : (↥TB → Fin p → ℝ) =>
        Real.sqrt (1 - t) * (ext d (Sum.inr (Sum.inr (Sum.inl l)), false) k - muX k) :=
      ((hext (Sum.inr (Sum.inr (Sum.inl l)), false) k).sub c1).const_mul _
    exact (((b1.add b2).const_mul _).add b3).const_mul _
  have hZssD : ∀ (l : Fin m) (k : Fin p),
      Measurable fun d : (↥TB → Fin p → ℝ) => ZssD (ext d) l k := by
    intro l k
    have c1 : Measurable fun _ : (↥TB → Fin p → ℝ) => muY k := measurable_const
    have b1 : Measurable fun d : (↥TB → Fin p → ℝ) =>
        Real.sqrt v * (ext d (Sum.inr (Sum.inl l), true) k - muY k) :=
      ((hext (Sum.inr (Sum.inl l), true) k).sub c1).const_mul _
    have b2 : Measurable fun d : (↥TB → Fin p → ℝ) =>
        Real.sqrt (1 - v) * (ext d (Sum.inr (Sum.inr (Sum.inr l)), true) k - muY k) :=
      ((hext (Sum.inr (Sum.inr (Sum.inr l)), true) k).sub c1).const_mul _
    have b3 : Measurable fun d : (↥TB → Fin p → ℝ) =>
        Real.sqrt (1 - t) * (ext d (Sum.inr (Sum.inr (Sum.inr l)), false) k - muY k) :=
      ((hext (Sum.inr (Sum.inr (Sum.inr l)), false) k).sub c1).const_mul _
    exact (((b1.add b2).const_mul _).add b3).const_mul _
  have hlop : Measurable lopVec := by
    rw [measurable_pi_iff]
    intro k
    exact (hsum (Finset.univ.erase i) (fun l => fun d => ZsD (ext d) l k) (fun l => hZsD l k)).add
      (hsum (Finset.univ : Finset (Fin m)) (fun l => fun d => ZssD (ext d) l k)
        (fun l => hZssD l k))
  have hAmeas : Measurable A := hcont.measurable.comp hlop
  have hextT : ∀ (x : Ω × Ω) (q : (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m))) × Bool), q ∈ TB →
      ext (Tfam x) q = g' q x := by
    intro x q hq
    funext k
    show (if h : q ∈ TB then (Tfam x) ⟨q, h⟩ k else 0) = g' q x k
    rw [dif_pos hq]
  have hvec : ∀ x : Ω × Ω, lopVec (Tfam x)
      = fun k : Fin p => (∑ l ∈ Finset.univ.erase i, Zs x l k) + (∑ l : Fin m, Zss x l k) := by
    intro x
    funext k
    show (∑ l ∈ Finset.univ.erase i, ZsD (ext (Tfam x)) l k) +
        (∑ l : Fin m, ZssD (ext (Tfam x)) l k)
      = (∑ l ∈ Finset.univ.erase i, Zs x l k) + (∑ l : Fin m, Zss x l k)
    have hs1 : (∑ l ∈ Finset.univ.erase i, ZsD (ext (Tfam x)) l k)
        = ∑ l ∈ Finset.univ.erase i, Zs x l k := by
      apply Finset.sum_congr rfl
      intro l hl
      have hli : l ≠ i := (Finset.mem_erase.mp hl).1
      show (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (ext (Tfam x) (Sum.inl l, true) k - muX k) +
              Real.sqrt (1 - v) * (ext (Tfam x) (Sum.inr (Sum.inr (Sum.inl l)), true) k - muX k)) +
            Real.sqrt (1 - t) * (ext (Tfam x) (Sum.inr (Sum.inr (Sum.inl l)), false) k - muX k))
        = (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t * (Real.sqrt v * (X l x.1 k - muX k) +
              Real.sqrt (1 - v) * (F l x.1 k - muX k)) +
            Real.sqrt (1 - t) * (F l x.2 k - muX k))
      have e1 : ext (Tfam x) (Sum.inl l, true) k = X l x.1 k :=
        congrFun (hextT x (Sum.inl l, true) (hT1 l hli)) k
      have e2 : ext (Tfam x) (Sum.inr (Sum.inr (Sum.inl l)), true) k = F l x.1 k :=
        congrFun (hextT x (Sum.inr (Sum.inr (Sum.inl l)), true) (hT2 l hli)) k
      have e3 : ext (Tfam x) (Sum.inr (Sum.inr (Sum.inl l)), false) k = F l x.2 k :=
        congrFun (hextT x (Sum.inr (Sum.inr (Sum.inl l)), false) (hT3 l hli)) k
      rw [e1, e2, e3]
    have hs2 : (∑ l : Fin m, ZssD (ext (Tfam x)) l k) = ∑ l : Fin m, Zss x l k := by
      apply Finset.sum_congr rfl
      intro l _
      show (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (ext (Tfam x) (Sum.inr (Sum.inl l), true) k - muY k) +
              Real.sqrt (1 - v) * (ext (Tfam x) (Sum.inr (Sum.inr (Sum.inr l)), true) k - muY k)) +
            Real.sqrt (1 - t) * (ext (Tfam x) (Sum.inr (Sum.inr (Sum.inr l)), false) k - muY k))
        = (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t * (Real.sqrt v * (Y l x.1 k - muY k) +
              Real.sqrt (1 - v) * (G l x.1 k - muY k)) +
            Real.sqrt (1 - t) * (G l x.2 k - muY k))
      have e4 : ext (Tfam x) (Sum.inr (Sum.inl l), true) k = Y l x.1 k :=
        congrFun (hextT x (Sum.inr (Sum.inl l), true) (hT4 l)) k
      have e5 : ext (Tfam x) (Sum.inr (Sum.inr (Sum.inr l)), true) k = G l x.1 k :=
        congrFun (hextT x (Sum.inr (Sum.inr (Sum.inr l)), true) (hT5 l)) k
      have e6 : ext (Tfam x) (Sum.inr (Sum.inr (Sum.inr l)), false) k = G l x.2 k :=
        congrFun (hextT x (Sum.inr (Sum.inr (Sum.inr l)), false) (hT6 l)) k
      rw [e4, e5, e6]
    rw [hs1, hs2]
  have key2 : ∀ x : Ω × Ω, A (Tfam x)
      = (fderiv ℝ κ (fun k : Fin p => (∑ l : Fin n, Zs x l k) + (∑ l : Fin m, Zss x l k) - Zs x i k))
        (Pi.single j 1) := by
    intro x
    show (fderiv ℝ κ (lopVec (Tfam x))) (Pi.single j 1)
      = (fderiv ℝ κ (fun k : Fin p => (∑ l : Fin n, Zs x l k) + (∑ l : Fin m, Zss x l k) - Zs x i k))
        (Pi.single j 1)
    rw [hvec x, ← key1 x]
  have hfin : (fun x : Ω × Ω =>
        (fderiv ℝ κ (fun k : Fin p => (∑ l : Fin n, Zs x l k) + (∑ l : Fin m, Zss x l k) - Zs x i k))
          (Pi.single j 1))
      ⟂ᵢ[P.prod P]
      (fun x : Ω × Ω => (Real.sqrt (n : ℝ))⁻¹ *
        ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) +
            Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
          (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))) := by
    have hcomp := hblock.comp hAmeas hBmeas
    have e1 : (fun x : Ω × Ω => A (Tfam x))
        = fun x : Ω × Ω =>
          (fderiv ℝ κ (fun k : Fin p => (∑ l : Fin n, Zs x l k) + (∑ l : Fin m, Zss x l k) - Zs x i k))
            (Pi.single j 1) := funext key2
    have e2 : (fun x : Ω × Ω => B (Sfam x))
        = fun x : Ω × Ω => (Real.sqrt (n : ℝ))⁻¹ *
          ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) +
              Real.sqrt (1 - v) * (F i x.1 j - muX j)) -
            (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)) := funext key3
    rw [← e1, ← e2]
    exact hcomp
  exact hfin
  /- @proof-region region.target-node.session.0c3db27321dd3037 end -/

end

end Statlib.Imported

