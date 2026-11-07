import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.ProvedNodes.Node_1447213522_6404e303_df8f8130
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.ProvedNodes.Node_436922874_8ad414b4_4d515167

namespace PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315

open MeasureTheory ProbabilityTheory
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
theorem statopia_math_node_1702548930_dc235873 : ∀ (n m p : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (μX μY : Fin p → ℝ) (d : ℝ)
    (X F : Fin n → Ω → (Fin p → ℝ)) (Y G : Fin m → Ω → (Fin p → ℝ))
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hF : ∀ i, Measurable (F i)) (hG : ∀ i, Measurable (G i)),
    let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
      if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
      else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩;
    (⨆ v ∈ Set.Icc (0 : ℝ) 1, ⨆ y : Fin (p + p) → ℝ,
        |(μ {ω : Ω |
              Real.sqrt v • partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω
                + Real.sqrt (1 - v) •
                    partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω ≤ y}).toReal
          - (μ {ω : Ω |
              partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω ≤ y}).toReal|)
      = rhoStar μ X Y F G μX μY d := by
  /- @proof-region region.target-node.session.78a2cb8710b4a966 begin -/
  intro n m p hn hm hp Ω _ μ _ μX μY d X F Y G hX hY hF hG
  dsimp only
  set T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
      if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
      else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩
  have hdep := statopia_math_node_436922874_8ad414b4 n m p hp PUnit
  dsimp only at hdep
  obtain ⟨-, -, -, -, -, -, -, -, hmix, hpf, hc1, hc2, -, -⟩ := hdep
  have hWmix : ∀ (v : ℝ) (ω : Ω),
      Real.sqrt v • partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω
        + Real.sqrt (1 - v) • partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω
      = T (Real.sqrt v • partXY X Y μX μY d ω + Real.sqrt (1 - v) • partFG F G μX μY d ω) := by
    intro v ω
    exact hmix (fun i _ => X i ω) (fun i _ => Y i ω) (fun i _ => F i ω) (fun i _ => G i ω)
      μX μY d v PUnit.unit
  have hZmix : ∀ (ω : Ω),
      partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω
        = T (partFG F G μX μY d ω) := by
    intro ω
    exact hpf (fun i _ => F i ω) (fun i _ => G i ω) (fun i _ => F i ω) (fun i _ => G i ω)
      μX μY d PUnit.unit
  set f : ℝ → (Fin (p + p) → ℝ) → ℝ := fun v y =>
    |(μ {ω : Ω |
          Real.sqrt v • partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω
            + Real.sqrt (1 - v) •
                partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω ≤ y}).toReal
      - (μ {ω : Ω |
          partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω ≤ y}).toReal|
  set ρ : ℝ := ⨆ v ∈ Set.Icc (0 : ℝ) 1, ⨆ y : Fin (p + p) → ℝ, f v y
  have hT1 : ∀ (z : Fin p → ℝ) (k : Fin p),
      T z ⟨(k : ℕ), by have hk := k.isLt; omega⟩ = z k := by
    intro z k
    exact hc1 z ⟨(k : ℕ), by have hk := k.isLt; omega⟩ (by have hk := k.isLt; omega)
  have hT2 : ∀ (z : Fin p → ℝ) (k : Fin p),
      T z ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ = - z k := by
    intro z k
    set j : Fin (p + p) := ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ with hj
    have hcj : T z j = -z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ :=
      hc2 z j (by show p ≤ p + (k : ℕ); omega)
    have hjp : (j : ℕ) - p = (k : ℕ) := by
      show p + (k : ℕ) - p = (k : ℕ)
      omega
    have hlast : -z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ = -z k :=
      congrArg (fun t : ℝ => -t) (congrArg z (Fin.ext hjp))
    exact hcj.trans hlast
  have hsplit : ∀ (P : Fin (p + p) → Prop), (∀ j, P j) ↔
      (∀ k : Fin p, P ⟨(k : ℕ), by have hk := k.isLt; omega⟩) ∧
      (∀ k : Fin p, P ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩) := by
    intro P
    constructor
    · intro h
      exact ⟨fun k => h _, fun k => h _⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : (j : ℕ) < p
      · rw [show j = ⟨(j : ℕ), by have hj' := j.isLt; omega⟩ from Fin.ext rfl]
        exact h1 ⟨(j : ℕ), hj⟩
      · rw [show j = ⟨p + ((j : ℕ) - p), by have hj' := j.isLt; omega⟩ from
          Fin.ext (by simp; have hj' := j.isLt; omega)]
        exact h2 ⟨(j : ℕ) - p, by have hj' := j.isLt; omega⟩
  have tE : ∀ (a b : ℝ), (Real.toEReal a ≤ Real.toEReal b) ↔ a ≤ b := by
    intro a b
    simp
  have key_k : ∀ (w : Fin p → ℝ) (y : Fin (p + p) → ℝ) (k : Fin p),
      (T w ⟨(k : ℕ), by have hk := k.isLt; omega⟩ ≤
          y ⟨(k : ℕ), by have hk := k.isLt; omega⟩) ↔
        Real.toEReal (w k) ≤ Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩) := by
    intro w y k
    rw [hT1 w k]
    exact (tE (w k) (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩)).symm
  have key_k2 : ∀ (w : Fin p → ℝ) (y : Fin (p + p) → ℝ) (k : Fin p),
      (T w ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ ≤
          y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩) ↔
        Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)) ≤
          Real.toEReal (w k) := by
    intro w y k
    rw [hT2 w k, tE]
    constructor <;> intro h <;> linarith
  have hkey : ∀ (w : Fin p → ℝ) (y : Fin (p + p) → ℝ),
      (T w ≤ y) ↔ w ∈ hyperRect p
        (fun k : Fin p => Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)))
        (fun k : Fin p => Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩)) := by
    intro w y
    simp only [Pi.le_def, hyperRect, Set.mem_setOf_eq]
    have hs := hsplit (fun j : Fin (p + p) => T w j ≤ y j)
    constructor
    · intro h k
      exact ⟨(key_k2 w y k).mp ((hs.mp h).2 k), (key_k w y k).mp ((hs.mp h).1 k)⟩
    · intro h
      exact hs.mpr ⟨fun k => (key_k w y k).mpr (h k).2,
        fun k => (key_k2 w y k).mpr (h k).1⟩
  have hR_def : rhoStar μ X Y F G μX μY d =
      sSup ((fun v : ℝ => sSup ((fun A : Set (Fin p → ℝ) =>
        |(μ {ω : Ω | (fun j : Fin p =>
              Real.sqrt v * partXY X Y μX μY d ω j
                + Real.sqrt (1 - v) * partFG F G μX μY d ω j) ∈ A}).toReal
          - (μ {ω : Ω | partFG F G μX μY d ω ∈ A}).toReal|) '' ARe p)) ''
          Set.Icc (0 : ℝ) 1) := rfl
  rw [hR_def]
  set g : ℝ → ℝ := fun v => sSup ((fun A : Set (Fin p → ℝ) =>
      |(μ {ω : Ω | (fun j : Fin p =>
            Real.sqrt v * partXY X Y μX μY d ω j
              + Real.sqrt (1 - v) * partFG F G μX μY d ω j) ∈ A}).toReal
        - (μ {ω : Ω | partFG F G μX μY d ω ∈ A}).toReal|) '' ARe p)
  set R : ℝ := sSup (g '' Set.Icc (0 : ℝ) 1)
  have hm1 : ∀ (s : Set Ω), (μ s).toReal ≤ 1 := by
    intro s
    have h2 : μ s ≤ μ Set.univ := measure_mono (Set.subset_univ s)
    rw [measure_univ] at h2
    have h3 : (μ s).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) h2
    simpa using h3
  have hb1 : ∀ (s t : Set Ω), |(μ s).toReal - (μ t).toReal| ≤ 1 := by
    intro s t
    have h1 := hm1 s
    have h2 := hm1 t
    have h3 : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
    have h4 : 0 ≤ (μ t).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  let V : ℝ → Set (Fin p → ℝ) → ℝ := fun v A =>
    |(μ {ω : Ω | (fun j : Fin p => Real.sqrt v * partXY X Y μX μY d ω j
        + Real.sqrt (1 - v) * partFG F G μX μY d ω j) ∈ A}).toReal
      - (μ {ω : Ω | partFG F G μX μY d ω ∈ A}).toReal|
  have hgV : ∀ (v : ℝ), g v = sSup (V v '' ARe p) := fun v => rfl
  obtain ⟨A₀, hA₀⟩ : (ARe p).Nonempty := by
    refine ⟨hyperRect p (fun _ => 0) (fun _ => 0), fun _ => 0, fun _ => 0, ?_, rfl⟩
    intro j
    exact le_refl 0
  have hVbdd : ∀ (v : ℝ), BddAbove (V v '' ARe p) := by
    intro v
    refine ⟨1, ?_⟩
    rintro _ ⟨A, -, rfl⟩
    exact hb1 _ _
  have hVsup : ∀ (v : ℝ), sSup (V v '' ARe p) ≤ 1 := by
    intro v
    exact csSup_le ⟨_, Set.mem_image_of_mem (V v) hA₀⟩
      (by rintro _ ⟨A, -, rfl⟩; exact hb1 _ _)
  have hVg : ∀ (v : ℝ) (A : Set (Fin p → ℝ)), A ∈ ARe p → V v A ≤ g v := by
    intro v A hA
    rw [hgV v]
    exact le_csSup (hVbdd v) (Set.mem_image_of_mem (V v) hA)
  have hgbdd : BddAbove (g '' Set.Icc (0 : ℝ) 1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨v, -, rfl⟩
    rw [hgV v]
    exact hVsup v
  have hgR : ∀ (v : ℝ), v ∈ Set.Icc (0 : ℝ) 1 → g v ≤ R := by
    intro v hv
    exact le_csSup hgbdd (Set.mem_image_of_mem g hv)
  have hg0 : ∀ (v : ℝ), 0 ≤ g v := by
    intro v
    rw [hgV v]
    have hle := le_csSup (hVbdd v) (Set.mem_image_of_mem (V v) hA₀)
    have h0 : 0 ≤ V v A₀ := abs_nonneg _
    linarith
  have hR0 : 0 ≤ R := le_trans (hg0 0) (hgR 0 (by constructor <;> norm_num))
  have hsetW : ∀ (v : ℝ) (y : Fin (p + p) → ℝ),
      {ω : Ω | Real.sqrt v • partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω
            + Real.sqrt (1 - v) •
                partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω ≤ y}
      = {ω : Ω | (fun j : Fin p => Real.sqrt v * partXY X Y μX μY d ω j
            + Real.sqrt (1 - v) * partFG F G μX μY d ω j) ∈ hyperRect p
              (fun k : Fin p =>
                Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)))
              (fun k : Fin p =>
                Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩))} := by
    intro v y
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hWmix v ω]
    exact hkey _ y
  have hsetZ : ∀ (y : Fin (p + p) → ℝ),
      {ω : Ω | partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω ≤ y}
      = {ω : Ω | partFG F G μX μY d ω ∈ hyperRect p
              (fun k : Fin p =>
                Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)))
              (fun k : Fin p =>
                Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩))} := by
    intro y
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hZmix ω]
    exact hkey _ y
  have hR1 : ρ ≤ R := by
    show (⨆ v ∈ Set.Icc (0 : ℝ) 1, ⨆ y : Fin (p + p) → ℝ, f v y) ≤ R
    refine Real.iSup_le (fun v => ?_) hR0
    refine Real.iSup_le (fun hv => ?_) hR0
    refine Real.iSup_le (fun y => ?_) hR0
    by_cases hfin : ∀ k : Fin p,
        Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)) ≤
          Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩)
    · have hAy : hyperRect p
          (fun k : Fin p =>
            Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)))
          (fun k : Fin p =>
            Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩)) ∈ ARe p :=
        ⟨_, _, hfin, rfl⟩
      have hval : f v y = V v (hyperRect p
          (fun k : Fin p =>
            Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)))
          (fun k : Fin p =>
            Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩))) := by
        have e1 := hsetW v y
        have e2 := hsetZ y
        simp only [f, V, e1, e2]
      rw [hval]
      exact le_trans (hVg v _ hAy) (hgR v hv)
    · push_neg at hfin
      obtain ⟨kk, hkk⟩ := hfin
      have hSW : {ω : Ω | Real.sqrt v • partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω
            + Real.sqrt (1 - v) •
                partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω ≤ y} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [hWmix v ω]
        constructor
        · intro hω
          have hmem := (hkey (Real.sqrt v • partXY X Y μX μY d ω
            + Real.sqrt (1 - v) • partFG F G μX μY d ω) y).mp hω
          simp only [hyperRect, Set.mem_setOf_eq] at hmem
          exact absurd (le_trans (hmem kk).1 (hmem kk).2) (not_le.mpr hkk)
        · intro h
          exact h.elim
      have hSZ : {ω : Ω | partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω ≤ y}
          = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [hZmix ω]
        constructor
        · intro hω
          have hmem := (hkey (partFG F G μX μY d ω) y).mp hω
          simp only [hyperRect, Set.mem_setOf_eq] at hmem
          exact absurd (le_trans (hmem kk).1 (hmem kk).2) (not_le.mpr hkk)
        · intro h
          exact h.elim
      have hval : f v y = 0 := by
        simp only [f, hSW, hSZ]
        simp
      rw [hval]
      exact hR0
  have hBY : ∀ (v : ℝ), BddAbove (Set.range (fun y : Fin (p + p) → ℝ => f v y)) := by
    intro v
    exact ⟨1, by rintro _ ⟨y, rfl⟩; exact hb1 _ _⟩
  have hY1 : ∀ (v : ℝ), (⨆ y : Fin (p + p) → ℝ, f v y) ≤ 1 := by
    intro v
    exact Real.iSup_le (fun y => hb1 _ _) zero_le_one
  have hBmid : ∀ (v : ℝ),
      BddAbove (Set.range (fun (_ : v ∈ Set.Icc (0 : ℝ) 1) =>
        ⨆ y : Fin (p + p) → ℝ, f v y)) := by
    intro v
    exact ⟨1, by rintro _ ⟨hv, rfl⟩; exact hY1 v⟩
  have hBout : BddAbove (Set.range (fun v : ℝ =>
      ⨆ (_ : v ∈ Set.Icc (0 : ℝ) 1), ⨆ y : Fin (p + p) → ℝ, f v y)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact Real.iSup_le (fun hv => hY1 v) zero_le_one
  have hle_rho : ∀ (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) (y : Fin (p + p) → ℝ),
      f v y ≤ ρ := by
    intro v hv y
    have h2 : (⨆ (_ : v ∈ Set.Icc (0 : ℝ) 1), ⨆ y : Fin (p + p) → ℝ, f v y) ≤ ρ :=
      le_ciSup hBout v
    exact le_trans (le_ciSup (hBY v) y) (le_trans (le_ciSup (hBmid v) hv) h2)
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg _) (hle_rho 0 (by constructor <;> norm_num) 0)
  have hVρ : ∀ (v : ℝ), v ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (A : Set (Fin p → ℝ)), A ∈ ARe p → V v A ≤ ρ := by
    intro v hv A hA
    let Wv : Ω → Fin p → ℝ := fun ω =>
      Real.sqrt v • partXY X Y μX μY d ω + Real.sqrt (1 - v) • partFG F G μX μY d ω
    let Zf : Ω → Fin p → ℝ := fun ω => partFG F G μX μY d ω
    have hchild := statopia_math_node_1447213522_6404e303 p hp Ω μ Wv Zf A hA
    have hchild' : V v A ≤ ⨆ y : Fin (p + p) → ℝ,
        |(μ {ω : Ω | T (Wv ω) ≤ y}).toReal - (μ {ω : Ω | T (Zf ω) ≤ y}).toReal| := hchild
    have hy : ∀ y : Fin (p + p) → ℝ,
        |(μ {ω : Ω | T (Wv ω) ≤ y}).toReal - (μ {ω : Ω | T (Zf ω) ≤ y}).toReal| = f v y := by
      intro y
      simp only [f, Wv, Zf, ← hWmix v, ← hZmix]
    refine le_trans hchild' (Real.iSup_le (fun y => ?_) hρ0)
    rw [hy y]
    exact hle_rho v hv y
  have hR2 : R ≤ ρ := by
    show sSup (g '' Set.Icc (0 : ℝ) 1) ≤ ρ
    refine csSup_le ⟨_, Set.mem_image_of_mem g (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [hgV v]
    exact csSup_le ⟨_, Set.mem_image_of_mem (V v) hA₀⟩ (fun x hx => by
      obtain ⟨A, hA, rfl⟩ := hx
      exact hVρ v hv A hA)
  exact le_antisymm hR1 hR2
  /- @proof-region region.target-node.session.78a2cb8710b4a966 end -/

end Statlib.Imported

end

