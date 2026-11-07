import Lean
import Mathlib

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DCFYReview
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `DCFYReview then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.DCFYReview))

/-- A measurable coordinatewise envelope for the continuous third derivatives.
The opaque Q is used only pointwise and need not be measurable. -/
noncomputable def boxEnvelope {p : ℕ} (D : (Fin p → ℝ) → ℝ)
    (r : ℝ) (w : Fin p → ℝ) : ℝ :=
  sSup ((fun u => |D (w + u)|) '' Metric.closedBall 0 r)

theorem boxEnvelope_continuous {p : ℕ} (D : (Fin p → ℝ) → ℝ)
    (hD : Continuous D) (r : ℝ) : Continuous (boxEnvelope D r) := by
  apply (isCompact_closedBall (0 : Fin p → ℝ) r).continuous_sSup
  exact (hD.comp (continuous_fst.add continuous_snd)).abs

theorem boxEnvelope_le {p : ℕ} (D Q : (Fin p → ℝ) → ℝ)
    (hD : ∀ z, |D z| ≤ Q z) (C r : ℝ) (hr : 0 ≤ r)
    (hQ : ∀ w u, ‖u‖ ≤ r → Q (w + u) ≤ C * Q w)
    (w : Fin p → ℝ) : boxEnvelope D r w ≤ C * Q w := by
  apply csSup_le
  · exact ⟨|D (w + 0)|, Set.mem_image_of_mem _ (by simpa using hr)⟩
  · rintro z ⟨u, hu, rfl⟩
    exact (hD (w + u)).trans (hQ w u (by simpa [Metric.mem_closedBall, dist_zero_right] using hu))

theorem le_boxEnvelope {p : ℕ} (D : (Fin p → ℝ) → ℝ)
    (hD : Continuous D) (r : ℝ) (w u : Fin p → ℝ) (hu : ‖u‖ ≤ r) :
    |D (w + u)| ≤ boxEnvelope D r w := by
  apply le_csSup
  · exact ((isCompact_closedBall (0 : Fin p → ℝ) r).image
      ((hD.comp (continuous_const.add continuous_id)).abs)).bddAbove
  · exact Set.mem_image_of_mem _ (by simpa [Metric.mem_closedBall, dist_zero_right] using hu)

/-- After transfer to the common base point, summing individual segment
suprema is legitimate. This does not commute sum and supremum. -/
theorem sum_boxEnvelope_le {p : ℕ}
    (D Q : Fin p → Fin p → Fin p → (Fin p → ℝ) → ℝ)
    (hD : ∀ j k l w, |D j k l w| ≤ Q j k l w)
    (C r budget : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hQ : ∀ j k l w u, ‖u‖ ≤ r → Q j k l (w + u) ≤ C * Q j k l w)
    (hmass : ∀ w, ∑ j, ∑ k, ∑ l, Q j k l w ≤ budget)
    (w : Fin p → ℝ) :
    ∑ j, ∑ k, ∑ l, boxEnvelope (D j k l) r w ≤ C * budget := by
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, C * Q j k l w := by
      exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ =>
        Finset.sum_le_sum (fun l _ => boxEnvelope_le (D j k l) (Q j k l)
          (hD j k l) C r hr (hQ j k l) w)))
    _ = C * (∑ j, ∑ k, ∑ l, Q j k l w) := by simp_rw [Finset.mul_sum]
    _ ≤ C * budget := mul_le_mul_of_nonneg_left (hmass w) hC

/-- Two box transfers express the measurable envelope at the leave-one-out
point in terms of the original pointwise majorant at the full interpolant. -/
theorem boxEnvelope_le_at_shift {p : ℕ} (D Q : (Fin p → ℝ) → ℝ)
    (hD : ∀ z, |D z| ≤ Q z) (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hQ : ∀ w u, ‖u‖ ≤ r → Q (w + u) ≤ C * Q w)
    (w u : Fin p → ℝ) (hu : ‖u‖ ≤ r) :
    boxEnvelope D r w ≤ C ^ 2 * Q (w + u) := by
  have hback : Q w ≤ C * Q (w + u) := by
    have H := hQ (w + u) (-u) (by simpa only [norm_neg] using hu)
    simpa using H
  calc
    _ ≤ C * Q w := boxEnvelope_le D Q hD C r hr hQ w
    _ ≤ C * (C * Q (w + u)) := mul_le_mul_of_nonneg_left hback hC
    _ = C ^ 2 * Q (w + u) := by ring

theorem boxEnvelope_measurable {p : ℕ} (D : (Fin p → ℝ) → ℝ)
    (hD : Continuous D) (r : ℝ) : Measurable (boxEnvelope D r) :=
  (boxEnvelope_continuous D hD r).measurable


/-- A nonnegative weight depending only on the leave-one-out data can be
reinserted into an independent truncation event without losing more than 2,
provided the event has probability at least one half. -/
theorem expectation_le_twice_good {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (good : Set Ω) (hgood : MeasurableSet good)
    (hind : IndepFun f (good.indicator (fun _ => (1 : ℝ))) μ)
    (hprob : (1 / 2 : ℝ) ≤ μ.real good) :
    (∫ x, f x ∂μ) ≤ 2 * ∫ x, good.indicator f x ∂μ := by
  have hi : (∫ x, good.indicator f x ∂μ) = (∫ x, f x ∂μ) * μ.real good := by
    have H := hind.integral_fun_mul_eq_mul_integral hf.aestronglyMeasurable
      ((measurable_const.indicator hgood).aestronglyMeasurable)
    have hone : (∫ x, good.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real good := by
      change (∫ x, good.indicator (1 : Ω → ℝ) x ∂μ) = μ.real good
      exact integral_indicator_one hgood
    rw [hone] at H
    convert H using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ good <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx])
  have hnonneg : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hf0
  have := mul_le_mul_of_nonneg_left hprob hnonneg
  rw [hi]
  nlinarith

/-- Coordinatewise common-interpolant transfer, before any summation over
rows or coordinates. Keeping this weight is necessary for max(sum moments). -/
theorem expectation_le_twice_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (good : Set Ω) (hgood : MeasurableSet good)
    (hind : IndepFun f (good.indicator (fun _ => (1 : ℝ))) μ)
    (hprob : (1 / 2 : ℝ) ≤ μ.real good)
    (C : ℝ) (hC : 0 ≤ C) (htransfer : ∀ x ∈ good, f x ≤ C * g x) :
    (∫ x, f x ∂μ) ≤ 2 * C * ∫ x, g x ∂μ := by
  have hmono : (∫ x, good.indicator f x ∂μ) ≤ ∫ x, C * g x ∂μ := by
    apply integral_mono (hf.indicator hgood) (hg.const_mul C)
    intro x
    by_cases hx : x ∈ good
    · simpa [hx] using htransfer x hx
    · simpa [hx] using mul_nonneg hC (hg0 x)
  calc
    _ ≤ 2 * ∫ x, good.indicator f x ∂μ :=
      expectation_le_twice_good μ f hf hf0 good hgood hind hprob
    _ ≤ 2 * ∫ x, C * g x ∂μ := mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = _ := by rw [integral_const_mul]; ring

/-- Pure bookkeeping for the small-good-probability branch. The preceding
probability and tail inequalities have to be proved from the actual data. -/
theorem small_good_moment_absorbed (q threshold tail moment : ℝ)
    (hq : q < (1 / 2 : ℝ)) (hthreshold : 0 ≤ threshold)
    (hlower : threshold * (1 - q) ≤ tail)
    (hmoment : moment ≤ threshold + tail) : moment ≤ 3 * tail := by
  have : threshold / 2 ≤ threshold * (1 - q) := by nlinarith
  linarith


/-- Sum the row moments only after all rows have been transferred to the
same coordinate weight. This matches max_j (sum_i moment_ij), rather than
the generally larger sum_i max_j moment_ij. -/
theorem weighted_row_sum_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (term moment : ι → κ → ℝ) (weight : κ → ℝ)
    (A cap budget : ℝ) (hA : 0 ≤ A) (hcap : 0 ≤ cap)
    (hweight : ∀ k, 0 ≤ weight k)
    (hterm : ∀ i k, term i k ≤ A * weight k * moment i k)
    (hmoment : ∀ k, ∑ i, moment i k ≤ cap)
    (hbudget : ∑ k, weight k ≤ budget) :
    ∑ i, ∑ k, term i k ≤ A * cap * budget := by
  calc
    _ ≤ ∑ i, ∑ k, A * weight k * moment i k :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hterm i k))
    _ = ∑ k, A * weight k * (∑ i, moment i k) := by
      rw [Finset.sum_comm]
      congr 1
      funext k
      exact (Finset.mul_sum ..).symm
    _ ≤ ∑ k, A * cap * weight k := by
      apply Finset.sum_le_sum
      intro k _
      have H := mul_le_mul_of_nonneg_left (hmoment k) (mul_nonneg hA (hweight k))
      nlinarith only [H]
    _ = A * cap * (∑ k, weight k) := (Finset.mul_sum ..).symm
    _ ≤ A * cap * budget := mul_le_mul_of_nonneg_left hbudget (mul_nonneg hA hcap)


/-- The bad truncation event incurs only each row's own third-moment tail.
There is no coordinate-count factor and no fourth moment. -/
theorem max_cube_bad_le_own_tails (a b c threshold : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (if threshold < max a (max b c) then (max a (max b c)) ^ 3 else 0) ≤
      (if threshold < a then a ^ 3 else 0) +
      (if threshold < b then b ^ 3 else 0) +
      (if threshold < c then c ^ 3 else 0) := by
  have hA : 0 ≤ (if threshold < a then a ^ 3 else 0) := by
    split_ifs <;> positivity
  have hB : 0 ≤ (if threshold < b then b ^ 3 else 0) := by
    split_ifs <;> positivity
  have hC : 0 ≤ (if threshold < c then c ^ 3 else 0) := by
    split_ifs <;> positivity
  by_cases hbad : threshold < max a (max b c)
  · rw [if_pos hbad]
    have hchoice : max a (max b c) = a ∨ max a (max b c) = b ∨ max a (max b c) = c := by
      by_cases habc : a ≤ max b c
      · rw [max_eq_right habc]
        by_cases hbc : b ≤ c
        · exact Or.inr (Or.inr (max_eq_right hbc))
        · exact Or.inr (Or.inl (max_eq_left (le_of_not_ge hbc)))
      · exact Or.inl (max_eq_left (le_of_not_ge habc))
    rcases hchoice with hchoice | hchoice | hchoice
    · rw [hchoice] at hbad ⊢
      rw [if_pos hbad]
      linarith
    · rw [hchoice] at hbad ⊢
      rw [if_pos hbad]
      linarith
    · rw [hchoice] at hbad ⊢
      rw [if_pos hbad]
      linarith
  · rw [if_neg hbad]
    linarith


end DCFYReview

