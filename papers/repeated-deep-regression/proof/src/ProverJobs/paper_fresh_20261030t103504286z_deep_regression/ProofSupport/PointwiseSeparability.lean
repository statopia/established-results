import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base

open MeasureTheory Filter
open scoped Topology BigOperators

namespace PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported

theorem countable_sup_reduction {α Ξ : Type*} (F : Set (α → ℝ))
    (hsep : PointwiseSeparable F) (V : (α → ℝ) → Ξ → ℝ)
    (hnn : ∀ f ∈ F, ∀ ω, 0 ≤ V f ω)
    (hbdd : ∀ ω, BddAbove (Set.range fun f : F => V f.1 ω))
    (hcont : ∀ f ∈ F, ∀ u : ℕ → (α → ℝ), (∀ k, u k ∈ F) →
      (∀ x, Tendsto (fun k => u k x) atTop (𝓝 (f x))) →
      ∀ ω, Tendsto (fun k => V (u k) ω) atTop (𝓝 (V f ω))) :
    ∃ s : Set F, s.Countable ∧ ∀ ω,
      (⨆ f : F, V f.1 ω) ≤ ⨆ f : s, V f.1.1 ω := by
  classical
  obtain ⟨F0, hF0, hsub, happ⟩ := hsep
  let s : Set F := Subtype.val ⁻¹' F0
  refine ⟨s, hF0.preimage Subtype.val_injective, ?_⟩
  intro ω
  have hbdds : BddAbove (Set.range fun f : s => V f.1.1 ω) :=
    (hbdd ω).mono (by rintro _ ⟨f, rfl⟩; exact ⟨f.1, rfl⟩)
  refine Real.iSup_le ?_ (Real.iSup_nonneg fun f : s => hnn f.1.1 f.1.2 ω)
  intro f
  obtain ⟨u, hu, hlim⟩ := happ f.1 f.2
  have hVlim := hcont f.1 f.2 u (fun k => hsub (hu k)) hlim ω
  apply le_of_tendsto hVlim
  apply Eventually.of_forall
  intro k
  exact le_ciSup hbdds (⟨⟨u k, hsub (hu k)⟩, hu k⟩ : s)

theorem predError_tendsto {α : Type*} [MeasurableSpace α]
    (PX : Measure α) [IsProbabilityMeasure PX]
    (F : Set (α → ℝ)) (f0 : α → ℝ) (B : ℝ) (hB : 0 < B)
    (hf0 : Measurable f0) (hF : ∀ f ∈ F, Measurable f)
    (hf0B : ∀ x, |f0 x| ≤ B) (hFB : ∀ f ∈ F, ∀ x, |f x| ≤ B)
    (f : α → ℝ) (u : ℕ → (α → ℝ)) (hu : ∀ k, u k ∈ F)
    (hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (f x))) :
    Tendsto (fun k => predError PX f0 (u k)) atTop (𝓝 (predError PX f0 f)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => 4 * B ^ 2)
  · intro k
    exact (((hF _ (hu k)).sub hf0).pow_const 2).aestronglyMeasurable
  · exact integrable_const _
  · intro k
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ha : |u k x - f0 x| ≤ 2 * B := by
      calc |u k x - f0 x| ≤ |u k x| + |f0 x| := by simpa [sub_eq_add_neg] using abs_add_le (u k x) (-f0 x)
        _ ≤ B + B := add_le_add (hFB _ (hu k) x) (hf0B x)
        _ = 2 * B := by ring
    rcases abs_le.mp ha with ⟨ha, hb⟩
    nlinarith
  · apply Eventually.of_forall
    intro x
    exact ((hlim x).sub tendsto_const_nhds).pow 2

theorem normalized_squared_process_separable {α Ξ : Type*} [MeasurableSpace α]
    (PX : Measure α) [IsProbabilityMeasure PX]
    (F : Set (α → ℝ)) (f0 : α → ℝ) (B : ℝ) (hB : 0 < B)
    (hf0 : Measurable f0) (hF : ∀ f ∈ F, Measurable f)
    (hf0B : ∀ x, |f0 x| ≤ B) (hFB : ∀ f ∈ F, ∀ x, |f x| ≤ B)
    (hFi : ∀ f ∈ F, Integrable (fun x => (f x - f0 x) ^ 2) PX)
    (hsep : PointwiseSeparable F) (N : ℕ) (X : Fin N → Ξ → α)
    (r : ℝ) (hr : 0 < r) :
    ∃ s : Set F, s.Countable ∧ ∀ ω,
      (⨆ f : F, |(1 / (N : ℝ)) * ∑ i,
        (predError PX f0 f.1 - (f.1 (X i ω) - f0 (X i ω)) ^ 2) /
          (predError PX f0 f.1 + r)|) ≤
      ⨆ f : s, |(1 / (N : ℝ)) * ∑ i,
        (predError PX f0 f.1.1 - (f.1.1 (X i ω) - f0 (X i ω)) ^ 2) /
          (predError PX f0 f.1.1 + r)| := by
  classical
  let V : (α → ℝ) → Ξ → ℝ := fun f ω => |(1 / (N : ℝ)) * ∑ i,
    (predError PX f0 f - (f (X i ω) - f0 (X i ω)) ^ 2) / (predError PX f0 f + r)|
  apply countable_sup_reduction F hsep V
  · intro f hf ω
    exact abs_nonneg _
  · intro ω
    have hterm : ∀ f ∈ F, ∀ i : Fin N,
        |(predError PX f0 f - (f (X i ω) - f0 (X i ω)) ^ 2) /
          (predError PX f0 f + r)| ≤ 8 * B ^ 2 / r := by
      intro f hf i
      have hsq : ∀ x, (f x - f0 x) ^ 2 ≤ 4 * B ^ 2 := by
        intro x
        have ha : |f x - f0 x| ≤ 2 * B := by
          calc |f x - f0 x| ≤ |f x| + |f0 x| := by simpa [sub_eq_add_neg] using abs_add_le (f x) (-f0 x)
            _ ≤ B + B := add_le_add (hFB f hf x) (hf0B x)
            _ = 2 * B := by ring
        rcases abs_le.mp ha with ⟨ha, hb⟩
        nlinarith
      have hp0 : 0 ≤ predError PX f0 f := integral_nonneg fun x => sq_nonneg _
      have hpB : predError PX f0 f ≤ 4 * B ^ 2 := by
        have h := integral_mono (hFi f hf) (integrable_const (4 * B ^ 2)) hsq
        simpa using h
      have hden : 0 < predError PX f0 f + r := by linarith
      have hnum : |predError PX f0 f - (f (X i ω) - f0 (X i ω)) ^ 2| ≤ 8 * B ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith [hsq (X i ω), sq_nonneg (f (X i ω) - f0 (X i ω)), sq_nonneg B]
      rw [abs_div, abs_of_pos hden]
      calc |predError PX f0 f - (f (X i ω) - f0 (X i ω)) ^ 2| / (predError PX f0 f + r)
          ≤ (8 * B ^ 2) / (predError PX f0 f + r) := div_le_div_of_nonneg_right hnum hden.le
        _ ≤ 8 * B ^ 2 / r := div_le_div_of_nonneg_left (by positivity) hr (by linarith)
    refine ⟨|1 / (N : ℝ)| * ∑ _i : Fin N, (8 * B ^ 2 / r), ?_⟩
    rintro _ ⟨f, rfl⟩
    dsimp [V]
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum fun i _ => hterm f.1 f.2 i)
  · intro f hf u hu hlim ω
    have hp := predError_tendsto PX F f0 B hB hf0 hF hf0B hFB f u hu hlim
    have hden : predError PX f0 f + r ≠ 0 := by
      have hp0 : 0 ≤ predError PX f0 f := integral_nonneg fun x => sq_nonneg _
      exact ne_of_gt (by linarith)
    have hterm : ∀ i : Fin N,
        Tendsto (fun k =>
          (predError PX f0 (u k) - (u k (X i ω) - f0 (X i ω)) ^ 2) /
            (predError PX f0 (u k) + r)) atTop
          (𝓝 ((predError PX f0 f - (f (X i ω) - f0 (X i ω)) ^ 2) /
            (predError PX f0 f + r))) := by
      intro i
      exact (hp.sub (((hlim (X i ω)).sub
        (tendsto_const_nhds (x := f0 (X i ω)))).pow 2)).div
          (hp.add (tendsto_const_nhds (x := r))) hden
    have hsum := tendsto_finset_sum Finset.univ (fun i _ => hterm i)
    exact ((tendsto_const_nhds (x := 1 / (N : ℝ))).mul hsum).abs

end PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported
