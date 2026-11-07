import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.ProvedNodes.Node_436922874_8ad414b4_4d515167

namespace PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315

open MeasureTheory ProbabilityTheory
open Filter Topology

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported

noncomputable section
universe u
open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1447213522_6404e303 : ∀ (p : ℕ) (hp : 1 ≤ p) (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W Z : Ω → (Fin p → ℝ)),
    let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
      if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
      else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩;
    ∀ A : Set (Fin p → ℝ), A ∈ ARe p →
      |(μ {ω : Ω | W ω ∈ A}).toReal - (μ {ω : Ω | Z ω ∈ A}).toReal|
        ≤ ⨆ y : Fin (p + p) → ℝ,
            |(μ {ω : Ω | T (W ω) ≤ y}).toReal
              - (μ {ω : Ω | T (Z ω) ≤ y}).toReal| := by
  /- @proof-region region.target-node.session.44dfa5b82ae87d41 begin -/
  intro p hp Ω _ μ _ W Z
  have hERle : ∀ {a b : ℝ}, a ≤ b → Real.toEReal a ≤ Real.toEReal b := by
    intro a b hab
    first
      | exact_mod_cast hab
      | simpa using hab
      | exact hab
      | (unfold Real.toEReal; exact hab)
      | (simp only [Real.toEReal]; exact hab)
  have hERlt : ∀ {a b : ℝ}, a < b → Real.toEReal a < Real.toEReal b := by
    intro a b hab
    first
      | exact_mod_cast hab
      | simpa using hab
      | exact hab
      | (unfold Real.toEReal; exact hab)
      | (simp only [Real.toEReal]; exact hab)
  have hERrefl : ∀ {a b : ℝ}, Real.toEReal a ≤ Real.toEReal b → a ≤ b := by
    intro a b hab
    by_contra h
    have hlt : b < a := not_le.mp h
    exact absurd hab (not_le.mpr (hERlt hlt))
  have hsupLe : ∀ (g : (Fin (p + p) → ℝ) → ℝ), BddAbove (Set.range g) →
      ∀ y : Fin (p + p) → ℝ, g y ≤ ⨆ y, g y := by
    intro g hb y
    first
      | exact le_csSup hb (Set.mem_range_self y)
      | exact le_ciSup hb y
      | exact le_iSup g y
  have hfinprobe : ∀ (w : Fin p → ℝ), (Set.range (fun k : Fin p => |w k|)).Finite := by
    intro w
    first
      | exact Set.finite_range _
      | (rw [← Set.image_univ]; exact Set.finite_univ.image _)
  have hprobe : ∀ s : Set Ω, (μ s).toReal ≤ 1 := by
    intro s
    have h1 : μ s ≤ 1 := by
      calc μ s ≤ μ Set.univ := measure_mono (Set.subset_univ s)
        _ = 1 := measure_univ
    calc (μ s).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) h1
      _ = 1 := ENNReal.toReal_one
  have tstruct : ∀ (Tg : (Fin p → ℝ) → (Fin (p + p) → ℝ)),
      (∀ (z : Fin p → ℝ) (j : Fin (p + p)), Tg z j =
        if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
        else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩) →
      ∀ (A : Set (Fin p → ℝ)), A ∈ ARe p →
        |(μ {ω : Ω | W ω ∈ A}).toReal - (μ {ω : Ω | Z ω ∈ A}).toReal|
          ≤ ⨆ y : Fin (p + p) → ℝ,
              |(μ {ω : Ω | Tg (W ω) ≤ y}).toReal - (μ {ω : Ω | Tg (Z ω) ≤ y}).toReal| := by
    intro Tg hTg A hA
    have hTM1 : ∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : (j : ℕ) < p),
        Tg z j = z ⟨(j : ℕ), hj⟩ := by
      intro z j hj
      rw [hTg z j]
      split_ifs with h
      · rfl
    have hTM2 : ∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : p ≤ (j : ℕ)),
        Tg z j = -z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ := by
      intro z j hj
      rw [hTg z j]
      split_ifs with h
      · exact absurd h (by omega)
      · rfl
    have hstruct : ∀ a : EReal, a = ⊥ ∨ a = ⊤ ∨ ∃ r : ℝ, a = Real.toEReal r := by
      intro a
      first
        | (rcases a with _ | r | _
           · exact Or.inl rfl
           · exact Or.inr (Or.inr ⟨r, by first | rfl | simp⟩)
           · exact Or.inr (Or.inl rfl))
        | (rcases a with _ | a'
           · exact Or.inl rfl
           · rcases a' with h | r
             · exact Or.inr (Or.inl rfl)
             · exact Or.inr (Or.inr ⟨r, by first | rfl | simp⟩))
        | (match a with
           | ⊥ => exact Or.inl rfl
           | ⊤ => exact Or.inr (Or.inl rfl)
           | (r : ℝ) => exact Or.inr (Or.inr ⟨r, by first | rfl | simp⟩))

    classical
    obtain ⟨lo, hi, hle, rfl⟩ := hA
    have hBdd : BddAbove (Set.range (fun y : Fin (p + p) → ℝ =>
        |(μ {ω : Ω | Tg (W ω) ≤ y}).toReal - (μ {ω : Ω | Tg (Z ω) ≤ y}).toReal|)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨y, rfl⟩
      have h1 := hprobe {ω : Ω | Tg (W ω) ≤ y}
      have h2 := hprobe {ω : Ω | Tg (Z ω) ≤ y}
      have h3 : (0:ℝ) ≤ (μ {ω : Ω | Tg (W ω) ≤ y}).toReal := ENNReal.toReal_nonneg
      have h4 : (0:ℝ) ≤ (μ {ω : Ω | Tg (Z ω) ≤ y}).toReal := ENNReal.toReal_nonneg
      rw [abs_le]
      constructor <;> linarith
    by_cases hne : (hyperRect p lo hi).Nonempty
    · obtain ⟨w0, hw0⟩ := hne
      have hw0' : ∀ k : Fin p, lo k ≤ Real.toEReal (w0 k) ∧ Real.toEReal (w0 k) ≤ hi k := hw0
      let a : ℕ → Fin p → ℝ := fun M k =>
        if h : ∃ r : ℝ, lo k = Real.toEReal r then h.choose else -(M : ℝ)
      let b : ℕ → Fin p → ℝ := fun M k =>
        if h : ∃ r : ℝ, hi k = Real.toEReal r then h.choose else (M : ℝ)
      let R : ℕ → Set (Fin p → ℝ) := fun M => {w | ∀ k, a M k ≤ w k ∧ w k ≤ b M k}
      let yM : ℕ → Fin (p + p) → ℝ := fun M j =>
        if h : (j : ℕ) < p then b M ⟨(j : ℕ), h⟩
        else -(a M ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩)
      have hadef : ∀ (M : ℕ) (k : Fin p), a M k =
          (if h : ∃ r : ℝ, lo k = Real.toEReal r then h.choose else -(M : ℝ)) := fun _ _ => rfl
      have hbdef : ∀ (M : ℕ) (k : Fin p), b M k =
          (if h : ∃ r : ℝ, hi k = Real.toEReal r then h.choose else (M : ℝ)) := fun _ _ => rfl
      have ha_lo : ∀ (M : ℕ) (k : Fin p), lo k ≤ Real.toEReal (a M k) := by
        intro M k
        rw [hadef M k]
        by_cases h : ∃ r : ℝ, lo k = Real.toEReal r
        · rw [dif_pos h, h.choose_spec.symm]

        · rw [dif_neg h]
          rcases hstruct (lo k) with h1 | h1 | h1
          · rw [h1]; simp
          · exfalso
            have h1' := (hw0' k).1
            rw [h1] at h1'
            simp at h1'
          · exact absurd h1 h
      have hb_hi : ∀ (M : ℕ) (k : Fin p), Real.toEReal (b M k) ≤ hi k := by
        intro M k
        rw [hbdef M k]
        by_cases h : ∃ r : ℝ, hi k = Real.toEReal r
        · rw [dif_pos h, ← h.choose_spec]
        · rw [dif_neg h]
          rcases hstruct (hi k) with h1 | h1 | h1
          · exfalso
            have h1' := (hw0' k).2
            rw [h1] at h1'
            simp at h1'
          · rw [h1]; simp
          · exact absurd h1 h
      have ha_mono : ∀ (M M' : ℕ), M ≤ M' → ∀ k : Fin p, a M' k ≤ a M k := by
        intro M M' hMM' k
        rw [hadef M' k, hadef M k]
        by_cases h : ∃ r : ℝ, lo k = Real.toEReal r
        · rw [dif_pos h, dif_pos h]
        · rw [dif_neg h, dif_neg h]
          have hc : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hMM'
          linarith
      have hb_mono : ∀ (M M' : ℕ), M ≤ M' → ∀ k : Fin p, b M k ≤ b M' k := by
        intro M M' hMM' k
        rw [hbdef M k, hbdef M' k]
        by_cases h : ∃ r : ℝ, hi k = Real.toEReal r
        · rw [dif_pos h, dif_pos h]
        · rw [dif_neg h, dif_neg h]
          have hc : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hMM'
          linarith
      have hR_sub : ∀ M : ℕ, R M ⊆ hyperRect p lo hi := by
        intro M w hw
        have hw' : ∀ k, a M k ≤ w k ∧ w k ≤ b M k := hw
        intro k
        exact ⟨le_trans (ha_lo M k) (hERle (hw' k).1), le_trans (hERle (hw' k).2) (hb_hi M k)⟩
      have hR_mono : Monotone R := by
        intro M M' hMM' w hw
        have hw' : ∀ k, a M k ≤ w k ∧ w k ≤ b M k := hw
        exact fun k => ⟨le_trans (ha_mono M M' hMM' k) (hw' k).1,
          le_trans (hw' k).2 (hb_mono M M' hMM' k)⟩
      have hR_union : ∀ w, w ∈ hyperRect p lo hi → ∃ M, w ∈ R M := by
        intro w hw
        have hw' : ∀ k, lo k ≤ Real.toEReal (w k) ∧ Real.toEReal (w k) ≤ hi k := hw
        obtain ⟨C, hC⟩ := (hfinprobe w).bddAbove
        obtain ⟨M, hM⟩ := exists_nat_ge C
        refine ⟨M, ?_⟩
        have hMk : ∀ k : Fin p, |w k| ≤ (M : ℝ) := fun k =>
          le_trans (hC (Set.mem_range_self k)) hM

        intro k
        constructor
        · rw [hadef M k]
          by_cases h : ∃ r : ℝ, lo k = Real.toEReal r
          · rw [dif_pos h]
            apply hERrefl
            rw [← h.choose_spec]
            exact (hw' k).1
          · rw [dif_neg h]
            linarith [neg_abs_le (w k), hMk k]
        · rw [hbdef M k]
          by_cases h : ∃ r : ℝ, hi k = Real.toEReal r
          · rw [dif_pos h]
            apply hERrefl
            rw [← h.choose_spec]
            exact (hw' k).2
          · rw [dif_neg h]
            linarith [le_abs_self (w k), hMk k]
      have hyM1 : ∀ (M : ℕ) (j : Fin (p + p)) (hj : (j : ℕ) < p),
          yM M j = b M ⟨(j : ℕ), hj⟩ := by
        intro M j hj
        show (if h : (j : ℕ) < p then b M ⟨(j : ℕ), h⟩
          else -(a M ⟨(j : ℕ) - p, by have hj' := j.isLt; omega⟩)) = b M ⟨(j : ℕ), hj⟩
        split_ifs with h
        · rfl
      have hyM2 : ∀ (M : ℕ) (j : Fin (p + p)) (hj : p ≤ (j : ℕ)),
          yM M j = -(a M ⟨(j : ℕ) - p, by have hj' := j.isLt; omega⟩) := by
        intro M j hj
        show (if h : (j : ℕ) < p then b M ⟨(j : ℕ), h⟩
          else -(a M ⟨(j : ℕ) - p, by have hj' := j.isLt; omega⟩)) =
          -(a M ⟨(j : ℕ) - p, by have hj' := j.isLt; omega⟩)
        split_ifs with h
        · exact absurd h (by omega)
        · rfl
      have hhalf : ∀ (M : ℕ) (w : Fin p → ℝ), (w ∈ R M ↔ Tg w ≤ yM M) := by
        intro M w
        constructor
        · intro hw
          have hw' : ∀ k, a M k ≤ w k ∧ w k ≤ b M k := hw
          show ∀ j : Fin (p + p), Tg w j ≤ yM M j
          intro j
          by_cases hj : (j : ℕ) < p
          · rw [hTM1 w j hj, hyM1 M j hj]
            exact (hw' ⟨(j : ℕ), hj⟩).2
          · have hj' : p ≤ (j : ℕ) := by omega
            set k' : Fin p := ⟨(j : ℕ) - p, by have h2 := j.isLt; omega⟩ with hk'
            have e1 : Tg w j = -w k' := by
              rw [hTM2 w j hj']
            have e2 : yM M j = -(a M k') := by
              rw [hyM2 M j hj']
            rw [e1, e2]
            have h1 := (hw' k').1
            linarith
        · intro hle k
          have hle' : ∀ j : Fin (p + p), Tg w j ≤ yM M j := hle
          constructor
          · set i : Fin (p + p) := ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ with hi
            have hiv : (i : ℕ) = p + (k : ℕ) := by rw [hi]
            have hi' : p ≤ (i : ℕ) := by omega
            have h := hle' i
            rw [hTM2 w i hi', hyM2 M i hi'] at h
            have hx : (⟨(i : ℕ) - p, by have h2 := i.isLt; omega⟩ : Fin p) = k := by
              have h2 : (i : ℕ) - p = (k : ℕ) := by
                rw [hiv]
                omega
              exact Fin.ext h2

            rw [hx] at h
            linarith
          · have h := hle' ⟨(k : ℕ), by have hk := k.isLt; omega⟩
            rw [hTM1 w _ (by have hk := k.isLt; omega),
              hyM1 M _ (by have hk := k.isLt; omega)] at h
            exact h

      have hbound : ∀ M : ℕ, |(μ {ω : Ω | W ω ∈ R M}).toReal - (μ {ω : Ω | Z ω ∈ R M}).toReal|
          ≤ ⨆ y : Fin (p + p) → ℝ,
              |(μ {ω : Ω | Tg (W ω) ≤ y}).toReal - (μ {ω : Ω | Tg (Z ω) ≤ y}).toReal| := by
        intro M
        have e1 : {ω : Ω | W ω ∈ R M} = {ω : Ω | Tg (W ω) ≤ yM M} := by
          ext ω
          exact hhalf M (W ω)
        have e2 : {ω : Ω | Z ω ∈ R M} = {ω : Ω | Tg (Z ω) ≤ yM M} := by
          ext ω
          exact hhalf M (Z ω)
        rw [e1, e2]
        exact hsupLe _ hBdd (yM M)
      have hmonoW : Monotone (fun M : ℕ => {ω : Ω | W ω ∈ R M}) := by
        intro M M' hMM' ω hw
        have hw' : ∀ k, a M k ≤ W ω k ∧ W ω k ≤ b M k := hw
        exact fun k => ⟨le_trans (ha_mono M M' hMM' k) (hw' k).1,
          le_trans (hw' k).2 (hb_mono M M' hMM' k)⟩
      have hmonoZ : Monotone (fun M : ℕ => {ω : Ω | Z ω ∈ R M}) := by
        intro M M' hMM' ω hw
        have hw' : ∀ k, a M k ≤ Z ω k ∧ Z ω k ≤ b M k := hw
        exact fun k => ⟨le_trans (ha_mono M M' hMM' k) (hw' k).1,
          le_trans (hw' k).2 (hb_mono M M' hMM' k)⟩
      have hunionW : (⋃ M : ℕ, {ω : Ω | W ω ∈ R M}) = {ω : Ω | W ω ∈ hyperRect p lo hi} := by
        ext ω
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨fun ⟨M, hM⟩ => hR_sub M hM, fun h => hR_union (W ω) h⟩
      have hunionZ : (⋃ M : ℕ, {ω : Ω | Z ω ∈ R M}) = {ω : Ω | Z ω ∈ hyperRect p lo hi} := by
        ext ω
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨fun ⟨M, hM⟩ => hR_sub M hM, fun h => hR_union (Z ω) h⟩
      have hfinW : μ {ω : Ω | W ω ∈ hyperRect p lo hi} ≠ ⊤ := by
        have hle1 : μ {ω : Ω | W ω ∈ hyperRect p lo hi} ≤ 1 := by
          calc μ {ω : Ω | W ω ∈ hyperRect p lo hi} ≤ μ Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        intro htop
        rw [htop] at hle1
        simp at hle1
      have hfinZ : μ {ω : Ω | Z ω ∈ hyperRect p lo hi} ≠ ⊤ := by
        have hle1 : μ {ω : Ω | Z ω ∈ hyperRect p lo hi} ≤ 1 := by
          calc μ {ω : Ω | Z ω ∈ hyperRect p lo hi} ≤ μ Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        intro htop
        rw [htop] at hle1
        simp at hle1
      have hlimW : Filter.Tendsto (fun M : ℕ => (μ {ω : Ω | W ω ∈ R M}).toReal) atTop
          (𝓝 ((μ {ω : Ω | W ω ∈ hyperRect p lo hi}).toReal)) := by
        have h1 : Filter.Tendsto (fun M : ℕ => μ {ω : Ω | W ω ∈ R M}) atTop
            (𝓝 (μ (⋃ M : ℕ, {ω : Ω | W ω ∈ R M}))) :=
          MeasureTheory.tendsto_measure_iUnion_atTop hmonoW
        rw [hunionW] at h1
        exact (ENNReal.tendsto_toReal hfinW).comp h1
      have hlimZ : Filter.Tendsto (fun M : ℕ => (μ {ω : Ω | Z ω ∈ R M}).toReal) atTop
          (𝓝 ((μ {ω : Ω | Z ω ∈ hyperRect p lo hi}).toReal)) := by
        have h1 : Filter.Tendsto (fun M : ℕ => μ {ω : Ω | Z ω ∈ R M}) atTop
            (𝓝 (μ (⋃ M : ℕ, {ω : Ω | Z ω ∈ R M}))) :=
          MeasureTheory.tendsto_measure_iUnion_atTop hmonoZ
        rw [hunionZ] at h1
        exact (ENNReal.tendsto_toReal hfinZ).comp h1

      exact le_of_tendsto' (hlimW.sub hlimZ).abs hbound
    · have hW : {ω : Ω | W ω ∈ hyperRect p lo hi} = ∅ := by
        ext ω
        constructor
        · intro h
          exact absurd ⟨W ω, h⟩ hne
        · intro h
          exact absurd h (by simp)
      have hZ : {ω : Ω | Z ω ∈ hyperRect p lo hi} = ∅ := by
        ext ω
        constructor
        · intro h
          exact absurd ⟨Z ω, h⟩ hne
        · intro h
          exact absurd h (by simp)
      rw [hW, hZ]
      simp only [measure_empty, ENNReal.toReal_zero, sub_self, abs_zero]
      exact le_trans (abs_nonneg _) (hsupLe _ hBdd (fun _ => (0 : ℝ)))



  exact tstruct (fun z j =>
      if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
      else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩) (fun _ _ => rfl)


  /- @proof-region region.target-node.session.44dfa5b82ae87d41 end -/

end Statlib.Imported

end

