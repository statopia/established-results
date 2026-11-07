import Lean
import Mathlib

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open Set
noncomputable section
namespace DCFQReview
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `DCFQReview then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.DCFQReview))
variable {E : Type*} [TopologicalSpace E]
def Minorants (Q : E → ℝ) := {f : E → ℝ // LowerSemicontinuous f ∧ ∀ x, f x ≤ Q x}
noncomputable def envelope (Q : E → ℝ) (x : E) : ℝ := ⨆ f : Minorants Q, f.val x

lemma envelope_bdd (Q : E → ℝ) (x : E) : BddAbove (Set.range fun f : Minorants Q => f.val x) :=
  ⟨Q x, by rintro _ ⟨f, rfl⟩; exact f.property.2 x⟩

lemma envelope_spec (Q : E → ℝ) (hQ : ∀ x, 0 ≤ Q x) :
    LowerSemicontinuous (envelope Q) ∧ (∀ x, 0 ≤ envelope Q x ∧ envelope Q x ≤ Q x) ∧
    (∀ f : E → ℝ, LowerSemicontinuous f → (∀ x, f x ≤ Q x) → ∀ x, f x ≤ envelope Q x) := by
  let zeroMinorant : Minorants Q := ⟨fun _ => 0, continuous_const.lowerSemicontinuous, hQ⟩
  haveI : Nonempty (Minorants Q) := ⟨zeroMinorant⟩
  refine ⟨?_, ?_, ?_⟩
  · exact lowerSemicontinuous_ciSup (envelope_bdd Q) (fun f => f.property.1)
  · intro x
    exact ⟨le_ciSup (envelope_bdd Q x) zeroMinorant, ciSup_le (fun f => f.property.2 x)⟩
  · intro f hf hfle x
    exact le_ciSup (envelope_bdd Q x) ⟨f, hf, hfle⟩

variable [AddGroup E] [ContinuousAdd E]
lemma envelope_shift (Q : E → ℝ) (hQ : ∀ x, 0 ≤ Q x) (C : ℝ) (hC : 0 < C)
    (u : E) (hshift : ∀ x, Q (x + u) ≤ C * Q x) :
    ∀ x, envelope Q (x + u) ≤ C * envelope Q x := by
  obtain ⟨hls, hbounds, hmax⟩ := envelope_spec Q hQ
  have hls_shift : LowerSemicontinuous (fun x => envelope Q (x + u)) :=
    hls.comp (continuous_id.add continuous_const)
  have hls_div : LowerSemicontinuous (fun x => envelope Q (x + u) / C) := by
    exact (continuous_id.div_const C).comp_lowerSemicontinuous hls_shift
      (fun a b hab => div_le_div_of_nonneg_right hab hC.le)
  have hminorant : ∀ x, envelope Q (x + u) / C ≤ Q x := by
    intro x
    apply (div_le_iff₀ hC).mpr
    calc
      envelope Q (x + u) ≤ Q (x + u) := (hbounds _).2
      _ ≤ C * Q x := hshift x
      _ = Q x * C := mul_comm _ _
  intro x
  have h := hmax _ hls_div hminorant x
  exact (div_le_iff₀ hC).mp h |>.trans_eq (mul_comm _ _)

omit [AddGroup E] [ContinuousAdd E] in
lemma envelope_dominates_continuous (Q f : E → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hf : Continuous f) (hfQ : ∀ x, f x ≤ Q x) : ∀ x, f x ≤ envelope Q x :=
  (envelope_spec Q hQ).2.2 f hf.lowerSemicontinuous hfQ

lemma envelope_shift_pair (Q : E → ℝ) (hQ : ∀ x, 0 ≤ Q x) (C : ℝ) (hC : 0 < C)
    (u : E) (hshift : ∀ x, Q x ≤ C * Q (x + u) ∧ Q (x + u) ≤ C * Q x) :
    ∀ x, envelope Q x ≤ C * envelope Q (x + u) ∧
      envelope Q (x + u) ≤ C * envelope Q x := by
  have hminus : ∀ x, Q (x + -u) ≤ C * Q x := by
    intro x
    simpa only [neg_add_cancel_right] using (hshift (x + -u)).1
  have hback := envelope_shift Q hQ C hC (-u) hminus
  have hforward := envelope_shift Q hQ C hC u (fun x => (hshift x).2)
  intro x
  exact ⟨by simpa only [add_neg_cancel_right] using hback (x + u), hforward x⟩

variable [MeasurableSpace E] [OpensMeasurableSpace E]
omit [AddGroup E] [ContinuousAdd E] in
lemma envelope_measurable (Q : E → ℝ) (hQ : ∀ x, 0 ≤ Q x) : Measurable (envelope Q) :=
  (envelope_spec Q hQ).1.measurable

lemma family_regularization {I : Type*} [Fintype I]
    (Q D : I → E → ℝ) (hQ : ∀ i x, 0 ≤ Q i x)
    (hD : ∀ i, Continuous (D i)) (hDQ : ∀ i x, D i x ≤ Q i x)
    (B C : ℝ) (hC : 0 < C) (S : Set E)
    (hBudget : ∀ x, ∑ i, Q i x ≤ B)
    (hShift : ∀ u ∈ S, ∀ i x, Q i x ≤ C * Q i (x + u) ∧ Q i (x + u) ≤ C * Q i x) :
    ∃ R : I → E → ℝ,
      (∀ i, Measurable (R i)) ∧
      (∀ i x, 0 ≤ R i x ∧ R i x ≤ Q i x) ∧
      (∀ i x, D i x ≤ R i x) ∧
      (∀ x, ∑ i, R i x ≤ B) ∧
      (∀ u ∈ S, ∀ i x, R i x ≤ C * R i (x + u) ∧ R i (x + u) ≤ C * R i x) := by
  refine ⟨fun i => envelope (Q i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact envelope_measurable (Q i) (hQ i)
  · intro i; exact (envelope_spec (Q i) (hQ i)).2.1
  · intro i; exact envelope_dominates_continuous (Q i) (D i) (hQ i) (hD i) (hDQ i)
  · intro x
    exact (Finset.sum_le_sum (fun i _ => (envelope_spec (Q i) (hQ i)).2.1 x |>.2)).trans (hBudget x)
  · intro u hu i
    exact envelope_shift_pair (Q i) (hQ i) C hC u (hShift u hu i)
end DCFQReview

namespace DCFQReview
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `DCFQReview then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.DCFQReview))
lemma continuous_abs_third {p : ℕ} (κ : (Fin p → ℝ) → ℝ) (hκ : ContDiff ℝ 3 κ)
    (d : Fin 3 → Fin p) : Continuous (fun w =>
      |(iteratedFDeriv ℝ 3 κ w) (fun s : Fin 3 => Pi.single (d s) (1 : ℝ))|) := by
  exact ((continuous_eval_const (fun s : Fin 3 => Pi.single (d s) (1 : ℝ))).comp
    hκ.continuous_iteratedFDeriv').abs
end DCFQReview

namespace DCFQReview
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `DCFQReview then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.DCFQReview))
lemma triple_regularization {p : ℕ} (κ : (Fin p → ℝ) → ℝ) (hκ : ContDiff ℝ 3 κ)
    (Q : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ)
    (hQ : ∀ j k l w, 0 ≤ Q j k l w)
    (hD : ∀ (d : Fin 3 → Fin p) w,
      |(iteratedFDeriv ℝ 3 κ w) (fun s : Fin 3 => Pi.single (d s) (1 : ℝ))| ≤
        Q (d 0) (d 1) (d 2) w)
    (B1 B2 C : ℝ) (hC : 0 < C) (S : Set (Fin p → ℝ))
    (hB1 : ∀ w, ∑ j, ∑ k, ∑ l, Q j k l w ≤ B1)
    (hB2 : ∀ w, ∑ j, ∑ k, ∑ l, Q j k l w ≤ B2)
    (hShift : ∀ w u, u ∈ S → ∀ j k l,
      Q j k l w ≤ C * Q j k l (w + u) ∧ Q j k l (w + u) ≤ C * Q j k l w) :
    ∃ R : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ,
      (∀ j k l, Measurable (R j k l)) ∧
      (∀ j k l w, 0 ≤ R j k l w) ∧
      (∀ (d : Fin 3 → Fin p) w,
        |(iteratedFDeriv ℝ 3 κ w) (fun s : Fin 3 => Pi.single (d s) (1 : ℝ))| ≤
          R (d 0) (d 1) (d 2) w) ∧
      (∀ w, ∑ j, ∑ k, ∑ l, R j k l w ≤ B1) ∧
      (∀ w, ∑ j, ∑ k, ∑ l, R j k l w ≤ B2) ∧
      (∀ w u, u ∈ S → ∀ j k l,
        R j k l w ≤ C * R j k l (w + u) ∧ R j k l (w + u) ≤ C * R j k l w) := by
  let R := fun j k l => envelope (Q j k l)
  have hle : ∀ j k l w, R j k l w ≤ Q j k l w :=
    fun j k l w => (envelope_spec (Q j k l) (hQ j k l)).2.1 w |>.2
  have hsum : ∀ w, (∑ j, ∑ k, ∑ l, R j k l w) ≤ ∑ j, ∑ k, ∑ l, Q j k l w := by
    intro w
    exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ =>
      Finset.sum_le_sum (fun l _ => hle j k l w)))
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j k l
    exact envelope_measurable (Q j k l) (hQ j k l)
  · intro j k l w
    exact (envelope_spec (Q j k l) (hQ j k l)).2.1 w |>.1
  · intro d w
    exact envelope_dominates_continuous (Q (d 0) (d 1) (d 2))
      (fun v => |(iteratedFDeriv ℝ 3 κ v) (fun s : Fin 3 => Pi.single (d s) (1 : ℝ))|)
      (hQ (d 0) (d 1) (d 2)) (continuous_abs_third κ hκ d) (hD d) w
  · intro w; exact (hsum w).trans (hB1 w)
  · intro w; exact (hsum w).trans (hB2 w)
  · intro w u hu j k l
    exact envelope_shift_pair (Q j k l) (hQ j k l) C hC u
      (fun v => hShift v u hu j k l) w
end DCFQReview


