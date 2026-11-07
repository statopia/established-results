import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base
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
theorem statopia_math_node_456014529_6ee9db8b : ∀ (n m p : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (μX μY : Fin p → ℝ) (d : ℝ)
    (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
    (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ))
    (hX : ∀ i : Fin n, Measurable (X i))
    (hY : ∀ i : Fin m, Measurable (Y i))
    (hF : ∀ i : Fin n, Measurable (F i))
    (hG : ∀ i : Fin m, Measurable (G i)),
    let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) :=
      fun z j => if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
        else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩;
    (⨆ v ∈ Set.Icc (0 : ℝ) 1,
        ⨆ y : Fin (p + p) → ℝ,
          |(μ {ω : Ω |
              (fun j : Fin (p + p) =>
                  Real.sqrt v * partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j
                    + Real.sqrt (1 - v) *
                        partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω j) ≤ y}).toReal
            - (μ {ω : Ω |
                (partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω) ≤ y}).toReal|)
      = rhoStar μ X Y F G μX μY d := by
  /- @proof-region region.target-node.session.7c1490727e4d4936 begin -/
  intro n m p hn hm hp Ω instΩ μ instμ μX μY d X Y F G hX hY hF hG T
  obtain ⟨hadd, hsmul, hcont, hinj, hrange, hnorm, hXY, hFG, hmix, hFG', hc1, hc2, hμ1, hμ2⟩ :=
    statopia_math_node_436922874_8ad414b4 n m p hp Ω
  set W : ℝ → Ω → (Fin p → ℝ) := fun v ω j =>
    Real.sqrt v * partXY X Y μX μY d ω j + Real.sqrt (1 - v) * partFG F G μX μY d ω j with hWdef
  set Z : Ω → (Fin p → ℝ) := fun ω => partFG F G μX μY d ω with hZdef
  set Ay : (Fin (p + p) → ℝ) → Set (Fin p → ℝ) := fun y =>
    {w | ∀ k : Fin p,
      Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)) ≤ Real.toEReal (w k) ∧
      Real.toEReal (w k) ≤ Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩)} with hAydef
  set g : ℝ → Set (Fin p → ℝ) → ℝ := fun v A =>
    |(μ {ω : Ω | W v ω ∈ A}).toReal - (μ {ω : Ω | Z ω ∈ A}).toReal| with hgdef
  have hAymem : ∀ (y : Fin (p + p) → ℝ) (w : Fin p → ℝ),
      (w ∈ Ay y) ↔ ∀ k : Fin p,
        Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)) ≤ Real.toEReal (w k) ∧
        Real.toEReal (w k) ≤ Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩) := by
    intro y w
    simp only [hAydef, Set.mem_setOf_eq]
  have hc1T : ∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : (j : ℕ) < p), T z j = z ⟨(j : ℕ), hj⟩ :=
    fun z j hj => hc1 z j hj
  have hc2T : ∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : p ≤ (j : ℕ)),
      T z j = -z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ :=
    fun z j hj => hc2 z j hj
  have hT1 : ∀ (z : Fin p → ℝ) (k : Fin p), T z ⟨(k : ℕ), by have hk := k.isLt; omega⟩ = z k := by
    intro z k
    rw [hc1T z ⟨(k : ℕ), by have hk := k.isLt; omega⟩ (by show (k : ℕ) < p; omega)]
  have hT2 : ∀ (z : Fin p → ℝ) (k : Fin p), T z ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ = -z k := by
    intro z k
    rw [hc2T z ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ (by show p ≤ p + (k : ℕ); omega)]
    congr 1
    congr 1
    exact Fin.ext (by show p + (k : ℕ) - p = (k : ℕ); omega)
  have hTle : ∀ (w : Fin p → ℝ) (y : Fin (p + p) → ℝ), (T w ≤ y) ↔ w ∈ Ay y := by
    intro w y
    rw [hAymem y w, Pi.le_def]
    constructor
    · intro h k
      refine ⟨?_, ?_⟩
      · have h2 : T w ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ ≤
            y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ := h _
        rw [hT2 w k] at h2
        exact EReal.coe_le_coe_iff.mpr (neg_le.mp h2)
      · have h2 : T w ⟨(k : ℕ), by have hk := k.isLt; omega⟩ ≤
            y ⟨(k : ℕ), by have hk := k.isLt; omega⟩ := h _
        rw [hT1 w k] at h2
        exact EReal.coe_le_coe_iff.mpr h2
    · intro h j
      by_cases hj : (j : ℕ) < p
      · rw [hc1T w j hj]
        exact EReal.coe_le_coe_iff.mp (h ⟨(j : ℕ), by have := j.isLt; omega⟩).2
      · rw [hc2T w j (by omega)]
        have h4 : -(y ⟨p + ((j : ℕ) - p), by have := j.isLt; omega⟩) ≤
            w ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ :=
          EReal.coe_le_coe_iff.mp (h ⟨(j : ℕ) - p, by have := j.isLt; omega⟩).1
        have hy : (⟨p + ((j : ℕ) - p), by have := j.isLt; omega⟩ : Fin (p + p)) = j :=
          Fin.ext (by show p + ((j : ℕ) - p) = (j : ℕ); omega)
        have h5 : -w ⟨(j : ℕ) - p, by have := j.isLt; omega⟩ ≤
            y ⟨p + ((j : ℕ) - p), by have := j.isLt; omega⟩ := neg_le.mp h4
        exact le_trans h5 (le_of_eq (congrArg y hy))
  have hsetZ : ∀ (y : Fin (p + p) → ℝ),
      {ω : Ω | (partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω) ≤ y}
        = {ω : Ω | Z ω ∈ Ay y} := by
    intro y
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [show partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω = T (Z ω) from by
      simpa [hZdef] using hFG' X Y F G μX μY d ω]
    exact hTle (Z ω) y
  have hstep : ∀ (v : ℝ) (y : Fin (p + p) → ℝ),
      |(μ {ω : Ω | (fun j : Fin (p + p) =>
            Real.sqrt v * partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j
              + Real.sqrt (1 - v) *
                  partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω j) ≤ y}).toReal
        - (μ {ω : Ω | (partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω) ≤ y}).toReal|
        = g v (Ay y) := by
    intro v y
    rw [show {ω : Ω | (fun j : Fin (p + p) =>
            Real.sqrt v * partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j
              + Real.sqrt (1 - v) *
                  partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω j) ≤ y}
          = {ω : Ω | W v ω ∈ Ay y} from by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [show (fun j : Fin (p + p) =>
            Real.sqrt v * partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j
              + Real.sqrt (1 - v) *
                  partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω j)
            = Real.sqrt v • partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω
              + Real.sqrt (1 - v) •
                  partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω from by
        funext j
        simp]
      rw [hmix X Y F G μX μY d v ω]
      rw [show Real.sqrt v • partXY X Y μX μY d ω + Real.sqrt (1 - v) • partFG F G μX μY d ω
            = W v ω from by
        funext j
        simp [hWdef]]
      exact hTle (W v ω) y]
    rw [hsetZ y]
  have hgoal1 : (⨆ v ∈ Set.Icc (0 : ℝ) 1, ⨆ y : Fin (p + p) → ℝ,
      |(μ {ω : Ω | (fun j : Fin (p + p) =>
            Real.sqrt v * partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) d ω j
              + Real.sqrt (1 - v) *
                  partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω j) ≤ y}).toReal
        - (μ {ω : Ω | (partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) d ω) ≤ y}).toReal|)
      = ⨆ v ∈ Set.Icc (0 : ℝ) 1, ⨆ y : Fin (p + p) → ℝ, g v (Ay y) := by
    simp only [hstep]
  have hARe_ne : (ARe p).Nonempty :=
    ⟨hyperRect p (fun _ => ⊥) (fun _ => ⊤), fun _ => ⊥, fun _ => ⊤, fun _ => le_top, rfl⟩
  have hg_nonneg : ∀ (v : ℝ) (A : Set (Fin p → ℝ)), 0 ≤ g v A := by
    intro v A
    simp only [hgdef]
    exact abs_nonneg _
  have hg_le_one : ∀ (v : ℝ) (A : Set (Fin p → ℝ)), g v A ≤ 1 := by
    intro v A
    have h1 : 0 ≤ (μ {ω : Ω | W v ω ∈ A}).toReal := by
      rw [← MeasureTheory.measureReal_def]
      exact MeasureTheory.measureReal_nonneg
    have h2 : (μ {ω : Ω | W v ω ∈ A}).toReal ≤ 1 := by
      rw [← MeasureTheory.measureReal_def]
      exact MeasureTheory.measureReal_le_one
    have h3 : 0 ≤ (μ {ω : Ω | Z ω ∈ A}).toReal := by
      rw [← MeasureTheory.measureReal_def]
      exact MeasureTheory.measureReal_nonneg
    have h4 : (μ {ω : Ω | Z ω ∈ A}).toReal ≤ 1 := by
      rw [← MeasureTheory.measureReal_def]
      exact MeasureTheory.measureReal_le_one
    simp only [hgdef]
    rw [abs_le]
    constructor <;> linarith
  have h0rho : 0 ≤ rhoStar μ X Y F G μX μY d := by
    simp only [rhoStar]
    refine Real.sSup_nonneg ?_
    rintro _ ⟨v, _, rfl⟩
    refine Real.sSup_nonneg ?_
    rintro _ ⟨A, _, rfl⟩
    exact hg_nonneg v A
  have hkeyA : ∀ (v : ℝ), v ∈ Set.Icc (0 : ℝ) 1 → ∀ y : Fin (p + p) → ℝ,
      g v (Ay y) ≤ rhoStar μ X Y F G μX μY d := by
    intro v hv y
    by_cases hne : (Ay y).Nonempty
    · obtain ⟨w₀, hw₀⟩ := hne
      have hle : ∀ k : Fin p,
          Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)) ≤
            Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩) := by
        intro k
        exact le_trans ((hAymem y w₀).mp hw₀ k).1 ((hAymem y w₀).mp hw₀ k).2
      have hA : Ay y ∈ ARe p := by
        refine ⟨fun k => Real.toEReal (-(y ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)),
          fun k => Real.toEReal (y ⟨(k : ℕ), by have hk := k.isLt; omega⟩), hle, ?_⟩
        ext w
        simp only [hAydef, hyperRect, Set.mem_setOf_eq]
      have hbdd : BddAbove ((fun A : Set (Fin p → ℝ) => g v A) '' ARe p) :=
        ⟨1, by rintro _ ⟨A, _, rfl⟩; exact hg_le_one v A⟩
      have step1 : g v (Ay y) ≤ sSup ((fun A : Set (Fin p → ℝ) => g v A) '' ARe p) :=
        le_csSup hbdd ⟨Ay y, hA, rfl⟩
      have hbdd2 : BddAbove ((fun v' : ℝ =>
          sSup ((fun A : Set (Fin p → ℝ) => g v' A) '' ARe p)) '' Set.Icc (0 : ℝ) 1) :=
        ⟨1, by
          rintro _ ⟨v', _, rfl⟩
          exact csSup_le (hARe_ne.image _) (fun b hb => by
            obtain ⟨A, _, rfl⟩ := hb
            exact hg_le_one v' A)⟩
      have step2 : sSup ((fun A : Set (Fin p → ℝ) => g v A) '' ARe p)
          ≤ rhoStar μ X Y F G μX μY d := by
        simp only [rhoStar]
        exact le_csSup hbdd2 ⟨v, hv, rfl⟩
      exact le_trans step1 step2
    · have hemp : Ay y = ∅ := by
        ext w
        exact ⟨fun hw => False.elim (hne ⟨w, hw⟩), fun hw => False.elim (hw : False)⟩
      have hz : g v (Ay y) = 0 := by
        simp only [hgdef, hemp]
        simp
      rw [hz]
      exact h0rho
  have hAlu : (⨆ v ∈ Set.Icc (0 : ℝ) 1, ⨆ y : Fin (p + p) → ℝ, g v (Ay y))
      ≤ rhoStar μ X Y F G μX μY d := by
    refine Real.iSup_le (fun v => ?_) h0rho
    refine Real.iSup_le (fun hv => ?_) h0rho
    exact Real.iSup_le (fun y => hkeyA v hv y) h0rho
  have hmain : (⨆ v ∈ Set.Icc (0 : ℝ) 1, ⨆ y : Fin (p + p) → ℝ, g v (Ay y))
      = rhoStar μ X Y F G μX μY d := by
    refine le_antisymm hAlu ?_
    have key : ∀ x : EReal, x ≠ ⊤ → x ≠ ⊥ → Real.toEReal x.toReal = x := by
      intro x htop hbot
      rcases x with _ | ⟨_ | r⟩
      · exact absurd rfl hbot
      · exact absurd rfl htop
      · dsimp only [EReal.toReal, Real.toEReal]
        rfl
    have hsummand : ∀ (v : ℝ), v ∈ Set.Icc (0 : ℝ) 1 → ∀ A ∈ ARe p,
        g v A ≤ ⨆ v' ∈ Set.Icc (0 : ℝ) 1, ⨆ y : Fin (p + p) → ℝ, g v' (Ay y) := by
      intro v hv A hA
      obtain ⟨lo, hi, hle, hAeq⟩ := hA
      have hMv_nonneg : (0 : ℝ) ≤ ⨆ y : Fin (p + p) → ℝ, g v (Ay y) := by
        refine Real.sSup_nonneg ?_
        rintro _ ⟨y, rfl⟩
        exact hg_nonneg v (Ay y)
      have hAB : g v A ≤ ⨆ y : Fin (p + p) → ℝ, g v (Ay y) := by
        by_cases hne : A.Nonempty
        · obtain ⟨w₀, hw₀⟩ := hne
          have hw₀' : ∀ k : Fin p, lo k ≤ Real.toEReal (w₀ k) ∧ Real.toEReal (w₀ k) ≤ hi k := by
            intro k
            have h := hw₀
            rw [hAeq] at h
            exact h k
          have hlo_ne_top : ∀ k : Fin p, lo k ≠ ⊤ := by
            intro k htop
            have h := (hw₀' k).1
            rw [htop] at h
            simp at h
          have hhi_ne_bot : ∀ k : Fin p, hi k ≠ ⊥ := by
            intro k hbot
            have h := (hw₀' k).2
            rw [hbot] at h
            simp at h
          set lT : ℕ → Fin p → ℝ := fun M k =>
            if lo k = ⊥ then -((M : ℝ)) else max ((lo k).toReal) (-((M : ℝ))) with hlTdef
          set hU : ℕ → Fin p → ℝ := fun M k =>
            if hi k = ⊤ then ((M : ℝ)) else min ((hi k).toReal) ((M : ℝ)) with hhUdef
          set yM : ℕ → Fin (p + p) → ℝ := fun M j =>
            if h : (j : ℕ) < p then hU M ⟨(j : ℕ), h⟩
              else -(lT M ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩) with hyMdef
          have hyM_left : ∀ (M : ℕ) (k : Fin p),
              yM M ⟨(k : ℕ), by have hk := k.isLt; omega⟩ = hU M k := by
            intro M k
            simp only [hyMdef]
            rw [dif_pos (by show (k : ℕ) < p; omega)]
          have hyM_right : ∀ (M : ℕ) (k : Fin p),
              yM M ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩ = -(lT M k) := by
            intro M k
            simp only [hyMdef]
            rw [dif_neg (by show ¬ (p + (k : ℕ) < p); omega)]
            congr 1
            congr 1
            exact Fin.ext (by show p + (k : ℕ) - p = (k : ℕ); omega)
          have hF1 : ∀ (M : ℕ) (k : Fin p), Real.toEReal (hU M k) ≤ hi k := by
            intro M k
            simp only [hhUdef]
            by_cases htop : hi k = ⊤
            · rw [if_pos htop, htop]
              simp
            · rw [if_neg htop]
              have hfin : Real.toEReal (hi k).toReal = hi k := key (hi k) htop (hhi_ne_bot k)
              rw [← hfin]
              exact EReal.coe_le_coe_iff.mpr (min_le_left _ _)
          have hF2 : ∀ (M : ℕ) (k : Fin p), lo k ≤ Real.toEReal (lT M k) := by
            intro M k
            simp only [hlTdef]
            by_cases hbot : lo k = ⊥
            · rw [if_pos hbot, hbot]
              simp
            · rw [if_neg hbot]
              have hfin : Real.toEReal (lo k).toReal = lo k := key (lo k) (hlo_ne_top k) hbot
              rw [← hfin]
              exact EReal.coe_le_coe_iff.mpr (le_max_left _ _)
          have hF3a : ∀ (M : ℕ) (k : Fin p), hU M k ≤ hU (M + 1) k := by
            intro M k
            simp only [hhUdef]
            by_cases htop : hi k = ⊤
            · rw [if_pos htop, if_pos htop]
              push_cast
              linarith
            · rw [if_neg htop, if_neg htop]
              exact min_le_min le_rfl (by push_cast; linarith)
          have hF3b : ∀ (M : ℕ) (k : Fin p), lT (M + 1) k ≤ lT M k := by
            intro M k
            simp only [hlTdef]
            by_cases hbot : lo k = ⊥
            · rw [if_pos hbot, if_pos hbot]
              push_cast
              linarith
            · rw [if_neg hbot, if_neg hbot]
              exact max_le_max le_rfl (by push_cast; linarith)
          have hAySub : ∀ M : ℕ, Ay (yM M) ⊆ A := by
            intro M x hx
            have hxm := (hAymem (yM M) x).mp hx
            rw [hAeq]
            intro k
            refine ⟨le_trans (hF2 M k) ?_, le_trans ?_ (hF1 M k)⟩
            · have h := (hxm k).1
              rw [hyM_right M k] at h
              simpa using h
            · have h := (hxm k).2
              rw [hyM_left M k] at h
              exact h
          have hAyStep : ∀ M : ℕ, Ay (yM M) ⊆ Ay (yM (M + 1)) := by
            intro M x hx
            have hxm := (hAymem (yM M) x).mp hx
            rw [hAymem]
            intro k
            refine ⟨?_, ?_⟩
            · have h := (hxm k).1
              have hb : Real.toEReal (-(yM (M + 1) ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩))
                  ≤ Real.toEReal (-(yM M ⟨p + (k : ℕ), by have hk := k.isLt; omega⟩)) := by
                rw [hyM_right (M + 1) k, hyM_right M k]
                simpa using EReal.coe_le_coe_iff.mpr (hF3b M k)
              exact le_trans hb h
            · have h := (hxm k).2
              have hb : Real.toEReal (yM M ⟨(k : ℕ), by have hk := k.isLt; omega⟩)
                  ≤ Real.toEReal (yM (M + 1) ⟨(k : ℕ), by have hk := k.isLt; omega⟩) := by
                rw [hyM_left M k, hyM_left (M + 1) k]
                exact EReal.coe_le_coe_iff.mpr (hF3a M k)
              exact le_trans h hb
          have hAyCover : ∀ (x : Fin p → ℝ), x ∈ A → ∃ M : ℕ, x ∈ Ay (yM M) := by
            intro x hx
            have hx' : ∀ k : Fin p, lo k ≤ Real.toEReal (x k) ∧ Real.toEReal (x k) ≤ hi k := by
              intro k
              have h := hx
              rw [hAeq] at h
              exact h k
            obtain ⟨M, hM⟩ := exists_nat_ge (∑ k : Fin p, |x k|)
            have hbound : ∀ k : Fin p, |x k| ≤ (M : ℝ) := by
              intro k
              refine le_trans ?_ hM
              exact Finset.single_le_sum (f := fun k' => |x k'|) (fun i _ => abs_nonneg _) (Finset.mem_univ k)
            refine ⟨M, ?_⟩
            rw [hAymem]
            intro k
            have h1 : Real.toEReal (lT M k) ≤ Real.toEReal (x k) := by
              refine EReal.coe_le_coe_iff.mpr ?_
              simp only [hlTdef]
              by_cases hbot : lo k = ⊥
              · rw [if_pos hbot]
                linarith [neg_abs_le (x k), hbound k]
              · rw [if_neg hbot]
                have hlek : (lo k).toReal ≤ x k := by
                  have hfin : Real.toEReal (lo k).toReal = lo k := key (lo k) (hlo_ne_top k) hbot
                  have h2 : Real.toEReal (lo k).toReal ≤ Real.toEReal (x k) := by
                    rw [hfin]; exact (hx' k).1
                  exact EReal.coe_le_coe_iff.mp h2
                exact max_le hlek (by linarith [neg_abs_le (x k), hbound k])
            have h2 : Real.toEReal (x k) ≤ Real.toEReal (hU M k) := by
              refine EReal.coe_le_coe_iff.mpr ?_
              simp only [hhUdef]
              by_cases htop : hi k = ⊤
              · rw [if_pos htop]
                linarith [le_abs_self (x k), hbound k]
              · rw [if_neg htop]
                have hlek : x k ≤ (hi k).toReal := by
                  have hfin : Real.toEReal (hi k).toReal = hi k := key (hi k) htop (hhi_ne_bot k)
                  have h3 : Real.toEReal (x k) ≤ Real.toEReal (hi k).toReal := by
                    rw [hfin]; exact (hx' k).2
                  exact EReal.coe_le_coe_iff.mp h3
                exact le_min hlek (by linarith [le_abs_self (x k), hbound k])
            refine ⟨?_, ?_⟩
            · rw [hyM_right M k]
              simpa using h1
            · rw [hyM_left M k]
              exact h2
          have hmonoW : Monotone (fun M => {ω : Ω | W v ω ∈ Ay (yM M)}) :=
            monotone_nat_of_le_succ (fun M x hx => hAyStep M hx)
          have hmonoZ : Monotone (fun M => {ω : Ω | Z ω ∈ Ay (yM M)}) :=
            monotone_nat_of_le_succ (fun M x hx => hAyStep M hx)
          have hunionW : (⋃ M, {ω : Ω | W v ω ∈ Ay (yM M)}) = {ω : Ω | W v ω ∈ A} := by
            ext ω
            constructor
            · rintro hω
              obtain ⟨M, hM⟩ := Set.mem_iUnion.mp hω
              exact hAySub M hM
            · intro hω
              obtain ⟨M, hM⟩ := hAyCover (W v ω) hω
              exact Set.mem_iUnion.mpr ⟨M, hM⟩
          have hunionZ : (⋃ M, {ω : Ω | Z ω ∈ Ay (yM M)}) = {ω : Ω | Z ω ∈ A} := by
            ext ω
            constructor
            · rintro hω
              obtain ⟨M, hM⟩ := Set.mem_iUnion.mp hω
              exact hAySub M hM
            · intro hω
              obtain ⟨M, hM⟩ := hAyCover (Z ω) hω
              exact Set.mem_iUnion.mpr ⟨M, hM⟩
          have hfinW : μ {ω : Ω | W v ω ∈ A} ≠ ⊤ := by
            intro htop
            have hle1 : μ {ω : Ω | W v ω ∈ A} ≤ 1 := by
              have h := measure_mono (μ := μ) (Set.subset_univ {ω : Ω | W v ω ∈ A})
              rwa [measure_univ] at h
            rw [htop] at hle1
            simp at hle1
          have hfinZ : μ {ω : Ω | Z ω ∈ A} ≠ ⊤ := by
            intro htop
            have hle1 : μ {ω : Ω | Z ω ∈ A} ≤ 1 := by
              have h := measure_mono (μ := μ) (Set.subset_univ {ω : Ω | Z ω ∈ A})
              rwa [measure_univ] at h
            rw [htop] at hle1
            simp at hle1
          have htendW : Filter.Tendsto (fun M => (μ {ω : Ω | W v ω ∈ Ay (yM M)}).toReal) Filter.atTop
              (nhds ((μ {ω : Ω | W v ω ∈ A}).toReal)) := by
            have hbase : Filter.Tendsto (fun M => μ {ω : Ω | W v ω ∈ Ay (yM M)}) Filter.atTop
                (nhds (μ (⋃ M, {ω : Ω | W v ω ∈ Ay (yM M)}))) :=
              MeasureTheory.tendsto_measure_iUnion_atTop hmonoW
            rw [hunionW] at hbase
            exact (ENNReal.tendsto_toReal hfinW).comp hbase
          have htendZ : Filter.Tendsto (fun M => (μ {ω : Ω | Z ω ∈ Ay (yM M)}).toReal) Filter.atTop
              (nhds ((μ {ω : Ω | Z ω ∈ A}).toReal)) := by
            have hbase : Filter.Tendsto (fun M => μ {ω : Ω | Z ω ∈ Ay (yM M)}) Filter.atTop
                (nhds (μ (⋃ M, {ω : Ω | Z ω ∈ Ay (yM M)}))) :=
              MeasureTheory.tendsto_measure_iUnion_atTop hmonoZ
            rw [hunionZ] at hbase
            exact (ENNReal.tendsto_toReal hfinZ).comp hbase
          have hlim : Filter.Tendsto (fun M => g v (Ay (yM M))) Filter.atTop (nhds (g v A)) := by
            have h := (htendW.sub htendZ).abs
            simpa only [hgdef] using h
          have hbound : ∀ M : ℕ, g v (Ay (yM M)) ≤ ⨆ y : Fin (p + p) → ℝ, g v (Ay y) := by
            intro M
            exact le_ciSup (f := fun y : Fin (p + p) → ℝ => g v (Ay y))
              ⟨1, fun x hx => by obtain ⟨y, rfl⟩ := hx; exact hg_le_one v (Ay y)⟩ (yM M)
          exact le_of_tendsto_of_tendsto' hlim tendsto_const_nhds hbound
        · have hemp : A = ∅ := by
            ext w
            exact ⟨fun hw => False.elim (hne ⟨w, hw⟩), fun hw => False.elim (hw : False)⟩
          have hz : g v A = 0 := by
            simp only [hgdef, hemp, Set.mem_empty_iff_false, Set.setOf_false, measure_empty,
              ENNReal.toReal_zero, sub_self, abs_zero]
          rw [hz]
          exact hMv_nonneg
      have h1 : (⨆ y : Fin (p + p) → ℝ, g v (Ay y)) ≤
          ⨆ (_ : v ∈ Set.Icc (0 : ℝ) 1), ⨆ y : Fin (p + p) → ℝ, g v (Ay y) :=
        le_ciSup (f := fun (_ : v ∈ Set.Icc (0 : ℝ) 1) => ⨆ y : Fin (p + p) → ℝ, g v (Ay y))
          ⟨_, fun x hx => by obtain ⟨_, rfl⟩ := hx; exact le_refl _⟩ hv
      have h2 : (⨆ (_ : v ∈ Set.Icc (0 : ℝ) 1), ⨆ y : Fin (p + p) → ℝ, g v (Ay y)) ≤
          ⨆ v' : ℝ, ⨆ (_ : v' ∈ Set.Icc (0 : ℝ) 1), ⨆ y : Fin (p + p) → ℝ, g v' (Ay y) :=
        le_ciSup (f := fun v' : ℝ => ⨆ (_ : v' ∈ Set.Icc (0 : ℝ) 1),
            ⨆ y : Fin (p + p) → ℝ, g v' (Ay y)) ⟨1, by
          rintro _ ⟨v', rfl⟩
          exact Real.iSup_le (fun _ => Real.iSup_le (fun y => hg_le_one v' (Ay y)) zero_le_one)
            zero_le_one⟩ v
      exact le_trans hAB (le_trans h1 h2)
    simp only [rhoStar]
    refine csSup_le ⟨_, ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    refine csSup_le (hARe_ne.image _) ?_
    rintro _ ⟨A, hA, rfl⟩
    exact hsummand v hv A hA
  exact hgoal1.trans hmain
  /- @proof-region region.target-node.session.7c1490727e4d4936 end -/

end Statlib.Imported

end

