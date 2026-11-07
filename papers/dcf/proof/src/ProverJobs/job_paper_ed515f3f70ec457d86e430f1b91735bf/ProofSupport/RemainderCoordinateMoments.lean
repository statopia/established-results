import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DCFManualXAudit
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `DCFManualXAudit then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.DCFManualXAudit))

/-- Coordinate weights must remain intact until the sample index has been summed. -/
theorem weighted_coordinate_contraction (n p : ℕ)
    (a : Fin n → Fin p → ℝ) (r : Fin n → Fin p → Fin p → Fin p → ℝ)
    (q : Fin p → Fin p → Fin p → ℝ) (L B : ℝ)
    (hL : ∀ j, ∑ i, a i j ≤ L)
    (hr : ∀ i j k l, r i j k l ≤ a i j + a i k + a i l)
    (hq : ∀ j k l, 0 ≤ q j k l)
    (hB : ∑ j, ∑ k, ∑ l, q j k l ≤ B) (hL0 : 0 ≤ L) :
    (∑ j, ∑ k, ∑ l, q j k l * ∑ i, r i j k l) ≤ 3 * B * L := by
  have hsum : ∀ j k l, (∑ i, r i j k l) ≤ 3 * L := by
    intro j k l
    calc (∑ i, r i j k l) ≤ ∑ i, (a i j + a i k + a i l) :=
        Finset.sum_le_sum (fun i _ => hr i j k l)
      _ = (∑ i, a i j) + (∑ i, a i k) + ∑ i, a i l := by
        simp only [Finset.sum_add_distrib]
      _ ≤ 3 * L := by linarith [hL j, hL k, hL l]
  calc (∑ j, ∑ k, ∑ l, q j k l * ∑ i, r i j k l)
      ≤ ∑ j, ∑ k, ∑ l, q j k l * (3 * L) := by
        refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_))
        exact Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hsum j k l) (hq j k l))
    _ = (∑ j, ∑ k, ∑ l, q j k l) * (3 * L) := by
      simp only [Finset.sum_mul]
    _ ≤ B * (3 * L) := mul_le_mul_of_nonneg_right hB (by positivity)
    _ = 3 * B * L := by ring

theorem abs_triple_le_coordinate_cubes (a b c : ℝ) :
    |a * b * c| ≤ (|a| ^ 3 + |b| ^ 3 + |c| ^ 3) / 3 := by
  have hnn := mul_nonneg (show 0 ≤ |a| + |b| + |c| by positivity)
    (show 0 ≤ (|a| - |b|)^2 + (|b| - |c|)^2 + (|c| - |a|)^2 by positivity)
  have hid : (|a| + |b| + |c|) *
      ((|a| - |b|)^2 + (|b| - |c|)^2 + (|c| - |a|)^2) =
      2 * (|a|^3 + |b|^3 + |c|^3) - 6 * (|a| * |b| * |c|) := by ring
  rw [abs_mul, abs_mul]
  linarith

/-- The mixed third moment needs only the three coordinate third moments, not a fourth moment. -/
theorem integrable_abs_triple {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a b c : Ω → ℝ) (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (ha3 : Integrable (fun x => |a x|^3) P)
    (hb3 : Integrable (fun x => |b x|^3) P)
    (hc3 : Integrable (fun x => |c x|^3) P) :
    Integrable (fun x => |a x * b x * c x|) P ∧
      (∫ x, |a x * b x * c x| ∂P) ≤
        ((∫ x, |a x|^3 ∂P) + (∫ x, |b x|^3 ∂P) + (∫ x, |c x|^3 ∂P))/3 := by
  have hdom : Integrable (fun x => (|a x|^3 + |b x|^3 + |c x|^3)/3) P :=
    ((ha3.add hb3).add hc3).div_const 3
  have hi : Integrable (fun x => |a x * b x * c x|) P := by
    refine hdom.mono' (((ha.mul hb).mul hc).abs.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_abs] using abs_triple_le_coordinate_cubes (a x) (b x) (c x))
  refine ⟨hi, ?_⟩
  calc (∫ x, |a x * b x * c x| ∂P)
      ≤ ∫ x, (|a x|^3 + |b x|^3 + |c x|^3)/3 ∂P :=
        integral_mono hi hdom (fun x => abs_triple_le_coordinate_cubes (a x) (b x) (c x))
    _ = _ := by
      rw [integral_div]
      have h1 := integral_add (f := fun x => |a x|^3 + |b x|^3)
        (g := fun x => |c x|^3) (ha3.add hb3) hc3
      have h2 := integral_add (f := fun x => |a x|^3)
        (g := fun x => |b x|^3) ha3 hb3
      dsimp only [Pi.add_apply] at h1 h2
      rw [h1, h2]

/-- This is the exact sample-sum/maximum order used in source equation (73). -/
theorem sample_mixed_third_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n p : ℕ) (a : Fin n → Ω → Fin p → ℝ) (L : ℝ)
    (ha : ∀ i j, Measurable (fun x => a i x j))
    (ha3 : ∀ i j, Integrable (fun x => |a i x j|^3) P)
    (hL : ∀ j, (∑ i, ∫ x, |a i x j|^3 ∂P) ≤ L) (j k l : Fin p) :
    (∑ i, ∫ x, |a i x j * a i x k * a i x l| ∂P) ≤ L := by
  calc (∑ i, ∫ x, |a i x j * a i x k * a i x l| ∂P)
      ≤ ∑ i, ((∫ x, |a i x j|^3 ∂P) + (∫ x, |a i x k|^3 ∂P) +
        (∫ x, |a i x l|^3 ∂P))/3 := by
          exact Finset.sum_le_sum (fun i _ =>
            (integrable_abs_triple P _ _ _ (ha i j) (ha i k) (ha i l)
              (ha3 i j) (ha3 i k) (ha3 i l)).2)
    _ = ((∑ i, ∫ x, |a i x j|^3 ∂P) + (∑ i, ∫ x, |a i x k|^3 ∂P) +
        (∑ i, ∫ x, |a i x l|^3 ∂P))/3 := by
          let u : Fin n → ℝ := fun i => ∫ x, |a i x j|^3 ∂P
          let v : Fin n → ℝ := fun i => ∫ x, |a i x k|^3 ∂P
          let w : Fin n → ℝ := fun i => ∫ x, |a i x l|^3 ∂P
          change (∑ i : Fin n, (u i + v i + w i) / 3) =
            ((∑ i : Fin n, u i) + (∑ i : Fin n, v i) + (∑ i : Fin n, w i))/3
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ L := by linarith [hL j, hL k, hL l]

/-- Application of the mixed-moment bound to the actual locked LX definition. -/
theorem sample_mixed_third_moment_LX {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n p : ℕ) (hn : 0 < n) (a : Fin n → Ω → Fin p → ℝ) (mu : Fin p → ℝ)
    (ha : ∀ i j, Measurable (fun x => a i x j))
    (ha3 : ∀ i j, Integrable (fun x => |a i x j - mu j|^3) P)
    (j k l : Fin p) :
    (∑ i, ∫ x, |(a i x j - mu j) * (a i x k - mu k) * (a i x l - mu l)| ∂P)
      ≤ (n : ℝ) * Statlib.Imported.LX P n mu a := by
  apply sample_mixed_third_moment P n p (fun i x j => a i x j - mu j)
    ((n : ℝ) * Statlib.Imported.LX P n mu a)
    (fun i j => (ha i j).sub measurable_const) ha3
  intro r
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hmax := le_ciSup (Set.finite_range (fun r : Fin p =>
    (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ x, |a i x r - mu r|^3 ∂P)).bddAbove r
  have hmul := mul_le_mul_of_nonneg_left hmax hnreal.le
  rw [← mul_assoc, mul_inv_cancel₀ hnreal.ne', one_mul] at hmul
  exact hmul

/-- A finite witness that interchanging the row sum and coordinate maximum loses a factor. -/
example : max (1 : ℝ) 0 + max 0 1 > max (1 + 0) (0 + 1) := by norm_num

/-- The source (72) contraction after every coordinate weight has been moved to the SAME full Z.
The hypothesis on m is a sum-over-samples bound, not a sum of rowwise maxima. -/
theorem common_weight_integral_contraction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (n p : ℕ)
    (q : Fin p → Fin p → Fin p → Ω → ℝ) (h : Ω → ℝ)
    (m : Fin n → Fin p → Fin p → Fin p → ℝ) (M B : ℝ)
    (hq : ∀ j k l x, 0 ≤ q j k l x)
    (hqi : ∀ j k l, Integrable (q j k l) P)
    (hi : Integrable h P)
    (hbudget : ∀ x, (∑ j, ∑ k, ∑ l, q j k l x) ≤ B * h x)
    (hm : ∀ j k l, (∑ i, m i j k l) ≤ M) (hM : 0 ≤ M) :
    (∑ i, ∑ j, ∑ k, ∑ l, (∫ x, q j k l x ∂P) * m i j k l)
      ≤ B * (∫ x, h x ∂P) * M := by
  have hwi : Integrable (fun x => ∑ j, ∑ k, ∑ l, q j k l x) P := by
    exact integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ => hqi j k l)))
  have hweights : (∑ j, ∑ k, ∑ l, ∫ x, q j k l x ∂P) ≤ B * ∫ x, h x ∂P := by
    calc (∑ j, ∑ k, ∑ l, ∫ x, q j k l x ∂P)
        = ∫ x, (∑ j, ∑ k, ∑ l, q j k l x) ∂P := by
          rw [integral_finset_sum Finset.univ (fun j _ =>
            integrable_finset_sum Finset.univ (fun k _ =>
              integrable_finset_sum Finset.univ (fun l _ => hqi j k l)))]
          congr 1
          funext j
          rw [integral_finset_sum Finset.univ (fun k _ =>
            integrable_finset_sum Finset.univ (fun l _ => hqi j k l))]
          congr 1
          funext k
          rw [integral_finset_sum Finset.univ (fun l _ => hqi j k l)]
      _ ≤ ∫ x, B * h x ∂P := integral_mono hwi (hi.const_mul B) hbudget
      _ = B * ∫ x, h x ∂P := integral_const_mul B h
  have hreorder : (∑ i, ∑ j, ∑ k, ∑ l, (∫ x, q j k l x ∂P) * m i j k l)
      = ∑ j, ∑ k, ∑ l, (∫ x, q j k l x ∂P) * ∑ i, m i j k l := by
    calc (∑ i, ∑ j, ∑ k, ∑ l, (∫ x, q j k l x ∂P) * m i j k l)
        = ∑ j, ∑ i, ∑ k, ∑ l, (∫ x, q j k l x ∂P) * m i j k l := Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ i, ∑ l, (∫ x, q j k l x ∂P) * m i j k l :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
      _ = ∑ j, ∑ k, ∑ l, ∑ i, (∫ x, q j k l x ∂P) * m i j k l :=
        Finset.sum_congr rfl (fun j _ =>
          Finset.sum_congr rfl (fun k _ => Finset.sum_comm))
      _ = _ := by simp only [Finset.mul_sum]
  rw [hreorder]
  calc (∑ j, ∑ k, ∑ l, (∫ x, q j k l x ∂P) * ∑ i, m i j k l)
      ≤ ∑ j, ∑ k, ∑ l, (∫ x, q j k l x ∂P) * M := by
        exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ =>
          Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hm j k l)
            (integral_nonneg (hq j k l)))))
    _ = (∑ j, ∑ k, ∑ l, ∫ x, q j k l x ∂P) * M := by simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hweights hM

/-- At the pointwise maximum the tail cube is one of its own component tail cubes.
No cross products, fourth moments or independence are needed. -/
theorem truncated_max_cube_le (a b c threshold : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (if threshold < max a (max b c) then (max a (max b c))^3 else 0) ≤
      (if threshold < a then a^3 else 0) +
      (if threshold < b then b^3 else 0) +
      (if threshold < c then c^3 else 0) := by
  have ha0 : 0 ≤ (if threshold < a then a^3 else 0) := by split_ifs <;> positivity
  have hb0 : 0 ≤ (if threshold < b then b^3 else 0) := by split_ifs <;> positivity
  have hc0 : 0 ≤ (if threshold < c then c^3 else 0) := by split_ifs <;> positivity
  rcases le_total (max b c) a with h | h
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right h]
    rcases le_total c b with hbc | hbc
    · rw [max_eq_left hbc]
      linarith
    · rw [max_eq_right hbc]
      linarith

set_option autoImplicit false in
/-- Actual interpolation row: coordinate-local third moments, with no coordinate sum loss. -/
theorem real_row_coordinate_moment : ∀ (p : ℕ) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : δ ≠ 0)
    (t : ℝ) (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (v : ℝ) (hv_nonneg : 0 ≤ v) (hv_le_one : v ≤ 1) (μ : Fin p → ℝ)
    (Y G : Ω → Fin p → ℝ)
    (hY_meas : ∀ r : Fin p, Measurable (fun ω : Ω => Y ω r))
    (hG_meas : ∀ r : Fin p, Measurable (fun ω : Ω => G ω r))
    (L L' : Fin p → ℝ)
    (hL : ∀ r : Fin p,
      Integrable (fun ω : Ω => |Y ω r - μ r| ^ 3) P ∧
      (∫ ω : Ω, |Y ω r - μ r| ^ 3 ∂P) ≤ L r ∧
      Integrable (fun ω : Ω => |G ω r - μ r| ^ 3) P ∧
      (∫ ω : Ω, |G ω r - μ r| ^ 3 ∂P) ≤ L' r),
    (let A : Ω × Ω → Fin p → ℝ := fun x r => Y x.1 r - μ r
     let Abar : Ω × Ω → Fin p → ℝ := fun x r => G x.1 r - μ r
     let Bb : Ω × Ω → Fin p → ℝ := fun x r => G x.2 r - μ r
     let Pcut : Ω × Ω → Fin p → ℝ := fun x r => |A x r| + |Abar x r| + |Bb x r|
     let U : Ω × Ω → Fin p → ℝ := fun x r =>
       (Real.sqrt (m : ℝ))⁻¹ * δ *
         (Real.sqrt t * (Real.sqrt v * A x r + Real.sqrt (1 - v) * Abar x r)
           + Real.sqrt (1 - t) * Bb x r)
     let V : Ω × Ω → Fin p → ℝ := fun x r =>
       (Real.sqrt (m : ℝ))⁻¹ * δ *
         ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * A x r + Real.sqrt (1 - v) * Abar x r)
           - (2 * Real.sqrt (1 - t))⁻¹ * Bb x r)
     ∀ j k l : Fin p,
       Integrable (fun x : Ω × Ω => |U x k * U x l * V x j|) (P.prod P) ∧
       (∫ x : Ω × Ω, |U x k * U x l * V x j| ∂(P.prod P))
         ≤ (3 / 2) * ((Real.sqrt (m : ℝ))⁻¹) ^ 3 * |δ| ^ 3 *
             ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) *
               ((L j + 2 * L' j) + (L k + 2 * L' k) + (L l + 2 * L' l))) := by
  /- @proof-region region.target-node.session.be9b81869b9084f8 begin -/
  intro p Ω _ P _ m hm delta hdelta t ht_pos ht_lt v hv_nonneg hv_le mu Y G hY hG L L' hL
  dsimp only
  intro j k l
  set UU : Ω × Ω → Fin p → ℝ := fun x r =>
    (√(m : ℝ))⁻¹ * delta *
      (√t * (√v * (Y x.1 r - mu r) + √(1 - v) * (G x.1 r - mu r))
        + √(1 - t) * (G x.2 r - mu r)) with hUU
  set VV : Ω × Ω → Fin p → ℝ := fun x r =>
    (√(m : ℝ))⁻¹ * delta *
      ((2 * √t)⁻¹ * (√v * (Y x.1 r - mu r) + √(1 - v) * (G x.1 r - mu r))
        - (2 * √(1 - t))⁻¹ * (G x.2 r - mu r)) with hVV
  obtain ⟨hYk_i, hYk_b, hGk_i, hGk_b⟩ := hL k
  obtain ⟨hYl_i, hYl_b, hGl_i, hGl_b⟩ := hL l
  obtain ⟨hYj_i, hYj_b, hGj_i, hGj_b⟩ := hL j
  have hst0 : (0 : ℝ) ≤ √t := Real.sqrt_nonneg t
  have hstp : (0 : ℝ) < √t := Real.sqrt_pos.mpr ht_pos
  have hst1 : √t ≤ 1 := Real.sqrt_le_one.mpr ht_lt.le
  have hs1t0 : (0 : ℝ) ≤ √(1 - t) := Real.sqrt_nonneg (1 - t)
  have hs1tp : (0 : ℝ) < √(1 - t) := Real.sqrt_pos.mpr (by linarith)
  have hs1t1 : √(1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hsv0 : (0 : ℝ) ≤ √v := Real.sqrt_nonneg v
  have hsv1 : √v ≤ 1 := Real.sqrt_le_one.mpr hv_le
  have hs1v0 : (0 : ℝ) ≤ √(1 - v) := Real.sqrt_nonneg (1 - v)
  have hs1v1 : √(1 - v) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hc0 : (0 : ℝ) ≤ (√(m : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg (m : ℝ))
  have hW0 : (0 : ℝ) ≤ (√t)⁻¹ + (√(1 - t))⁻¹ := by
    have h1 : (0 : ℝ) < (√t)⁻¹ := inv_pos.mpr hstp
    have h2 : (0 : ℝ) < (√(1 - t))⁻¹ := inv_pos.mpr hs1tp
    linarith
  have keyU : ∀ a b c : ℝ,
      |(√(m : ℝ))⁻¹ * delta * (√t * (√v * a + √(1 - v) * b) + √(1 - t) * c)|
        ≤ (√(m : ℝ))⁻¹ * |delta| * (|a| + |b| + |c|) := by
    intro a b c
    have hin : |√v * a + √(1 - v) * b| ≤ |a| + |b| := by
      have h := abs_add_le (√v * a) (√(1 - v) * b)
      rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hs1v0] at h
      have h1 : √v * |a| ≤ |a| := by
        simpa using mul_le_mul_of_nonneg_right hsv1 (abs_nonneg a)
      have h2 : √(1 - v) * |b| ≤ |b| := by
        simpa using mul_le_mul_of_nonneg_right hs1v1 (abs_nonneg b)
      linarith
    have hin2 : |√t * (√v * a + √(1 - v) * b) + √(1 - t) * c| ≤ |a| + |b| + |c| := by
      have h := abs_add_le (√t * (√v * a + √(1 - v) * b)) (√(1 - t) * c)
      rw [abs_mul, abs_mul, abs_of_nonneg hst0, abs_of_nonneg hs1t0] at h
      have h1 : √t * |√v * a + √(1 - v) * b| ≤ |a| + |b| := by
        calc √t * |√v * a + √(1 - v) * b| ≤ 1 * (|a| + |b|) :=
              mul_le_mul hst1 hin (abs_nonneg _) (by norm_num)
          _ = |a| + |b| := one_mul _
      have h2 : √(1 - t) * |c| ≤ |c| := by
        simpa using mul_le_mul_of_nonneg_right hs1t1 (abs_nonneg c)
      linarith
    calc |(√(m : ℝ))⁻¹ * delta * (√t * (√v * a + √(1 - v) * b) + √(1 - t) * c)|
        = (√(m : ℝ))⁻¹ * |delta| * |√t * (√v * a + √(1 - v) * b) + √(1 - t) * c| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc0]
      _ ≤ (√(m : ℝ))⁻¹ * |delta| * (|a| + |b| + |c|) := by
          apply mul_le_mul_of_nonneg_left hin2
          positivity
  have keyV : ∀ a b c : ℝ,
      |(√(m : ℝ))⁻¹ * delta *
          ((2 * √t)⁻¹ * (√v * a + √(1 - v) * b) - (2 * √(1 - t))⁻¹ * c)|
        ≤ (√(m : ℝ))⁻¹ * |delta| *
            ((1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) * (|a| + |b| + |c|)) := by
    intro a b c
    have hinv0 : (0 : ℝ) ≤ (2 * √t)⁻¹ := by positivity
    have hinv1 : (0 : ℝ) ≤ (2 * √(1 - t))⁻¹ := by positivity
    have hX : |√v * a + √(1 - v) * b| ≤ |a| + |b| := by
      have h := abs_add_le (√v * a) (√(1 - v) * b)
      rw [abs_mul, abs_mul, abs_of_nonneg hsv0, abs_of_nonneg hs1v0] at h
      have h1 : √v * |a| ≤ |a| := by
        simpa using mul_le_mul_of_nonneg_right hsv1 (abs_nonneg a)
      have h2 : √(1 - v) * |b| ≤ |b| := by
        simpa using mul_le_mul_of_nonneg_right hs1v1 (abs_nonneg b)
      linarith
    have hstep : |(2 * √t)⁻¹ * (√v * a + √(1 - v) * b) - (2 * √(1 - t))⁻¹ * c|
        ≤ (2 * √t)⁻¹ * (|a| + |b|) + (2 * √(1 - t))⁻¹ * |c| := by
      have h := abs_add_le ((2 * √t)⁻¹ * (√v * a + √(1 - v) * b))
        (-((2 * √(1 - t))⁻¹ * c))
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hinv0, abs_of_nonneg hinv1] at h
      have h1 : (2 * √t)⁻¹ * |√v * a + √(1 - v) * b| ≤ (2 * √t)⁻¹ * (|a| + |b|) :=
        mul_le_mul_of_nonneg_left hX hinv0
      rw [sub_eq_add_neg]
      linarith
    have hstep2 : (2 * √t)⁻¹ * (|a| + |b|) + (2 * √(1 - t))⁻¹ * |c|
        ≤ (1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) * (|a| + |b| + |c|) := by
      have e0 : (2 * √t)⁻¹ = (1 / 2) * (√t)⁻¹ := by
        rw [mul_inv]
        norm_num
      have e1 : (2 * √(1 - t))⁻¹ = (1 / 2) * (√(1 - t))⁻¹ := by
        rw [mul_inv]
        norm_num
      rw [e0, e1]
      have h1 : (0 : ℝ) ≤ (√t)⁻¹ := inv_nonneg.mpr hst0
      have h2 : (0 : ℝ) ≤ (√(1 - t))⁻¹ := inv_nonneg.mpr hs1t0
      have h3 : (0 : ℝ) ≤ |a| + |b| := by positivity
      have h4 : (0 : ℝ) ≤ |c| := abs_nonneg c
      have h5 : (0 : ℝ) ≤ (√t)⁻¹ * |c| := mul_nonneg h1 h4
      have h6 : (0 : ℝ) ≤ (√(1 - t))⁻¹ * (|a| + |b|) := mul_nonneg h2 h3
      nlinarith [h5, h6]
    have hK : (0 : ℝ) ≤ (√(m : ℝ))⁻¹ * |delta| := mul_nonneg hc0 (abs_nonneg delta)
    calc |(√(m : ℝ))⁻¹ * delta *
            ((2 * √t)⁻¹ * (√v * a + √(1 - v) * b) - (2 * √(1 - t))⁻¹ * c)|
        = (√(m : ℝ))⁻¹ * |delta| *
            |(2 * √t)⁻¹ * (√v * a + √(1 - v) * b) - (2 * √(1 - t))⁻¹ * c| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc0]
      _ ≤ (√(m : ℝ))⁻¹ * |delta| *
            ((1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) * (|a| + |b| + |c|)) :=
          mul_le_mul_of_nonneg_left (le_trans hstep hstep2) hK
  let Qk : Ω × Ω → ℝ := fun x => |Y x.1 k - mu k| + |G x.1 k - mu k| + |G x.2 k - mu k|
  let Ql : Ω × Ω → ℝ := fun x => |Y x.1 l - mu l| + |G x.1 l - mu l| + |G x.2 l - mu l|
  let Qj : Ω × Ω → ℝ := fun x => |Y x.1 j - mu j| + |G x.1 j - mu j| + |G x.2 j - mu j|
  have hQk0 : ∀ x : Ω × Ω, (0 : ℝ) ≤ Qk x := by
    intro x
    show (0 : ℝ) ≤ |Y x.1 k - mu k| + |G x.1 k - mu k| + |G x.2 k - mu k|
    positivity
  have hQl0 : ∀ x : Ω × Ω, (0 : ℝ) ≤ Ql x := by
    intro x
    show (0 : ℝ) ≤ |Y x.1 l - mu l| + |G x.1 l - mu l| + |G x.2 l - mu l|
    positivity
  have hQj0 : ∀ x : Ω × Ω, (0 : ℝ) ≤ Qj x := by
    intro x
    show (0 : ℝ) ≤ |Y x.1 j - mu j| + |G x.1 j - mu j| + |G x.2 j - mu j|
    positivity
  have hUbd : ∀ (x : Ω × Ω) (r : Fin p), |UU x r| ≤ (√(m : ℝ))⁻¹ * |delta| *
      (|Y x.1 r - mu r| + |G x.1 r - mu r| + |G x.2 r - mu r|) := by
    intro x r
    rw [hUU]
    exact keyU _ _ _
  have hVbd : ∀ (x : Ω × Ω) (r : Fin p), |VV x r| ≤ (√(m : ℝ))⁻¹ * |delta| *
      ((1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) *
        (|Y x.1 r - mu r| + |G x.1 r - mu r| + |G x.2 r - mu r|)) := by
    intro x r
    rw [hVV]
    exact keyV _ _ _
  have hprod : ∀ x : Ω × Ω,
      |UU x k * UU x l * VV x j| ≤ (1 / 2) * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 *
        ((√t)⁻¹ + (√(1 - t))⁻¹) * (Qk x * Ql x * Qj x) := by
    intro x
    have hK : (0 : ℝ) ≤ (√(m : ℝ))⁻¹ * |delta| := mul_nonneg hc0 (abs_nonneg delta)
    have hk := hUbd x k
    have hl := hUbd x l
    have hj := hVbd x j
    have hmul1 : |UU x k| * |UU x l| ≤
        ((√(m : ℝ))⁻¹ * |delta| * Qk x) * ((√(m : ℝ))⁻¹ * |delta| * Ql x) := by
      refine mul_le_mul hk hl (abs_nonneg _) ?_
      exact mul_nonneg hK (hQk0 x)
    have hmul2 : |UU x k| * |UU x l| * |VV x j| ≤
        (((√(m : ℝ))⁻¹ * |delta| * Qk x) * ((√(m : ℝ))⁻¹ * |delta| * Ql x)) *
          ((√(m : ℝ))⁻¹ * |delta| * ((1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) * Qj x)) := by
      refine mul_le_mul hmul1 hj (abs_nonneg _) ?_
      exact mul_nonneg (mul_nonneg hK (hQk0 x)) (mul_nonneg hK (hQl0 x))
    rw [abs_mul, abs_mul]
    refine le_trans hmul2 (le_of_eq ?_)
    show (((√(m : ℝ))⁻¹ * |delta| * Qk x) * ((√(m : ℝ))⁻¹ * |delta| * Ql x)) *
        ((√(m : ℝ))⁻¹ * |delta| * ((1 / 2) * ((√t)⁻¹ + (√(1 - t))⁻¹) * Qj x)) =
      (1 / 2) * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 *
        ((√t)⁻¹ + (√(1 - t))⁻¹) * (Qk x * Ql x * Qj x)
    rw [← inv_pow]
    ring
  have honeP : (∫ _ : Ω, (1 : ℝ) ∂P) = 1 := by simp
  have hIk1 : (∫ x : Ω × Ω, |Y x.1 k - mu k| ^ 3 ∂(P.prod P))
      = ∫ ω : Ω, |Y ω k - mu k| ^ 3 ∂P := by
    have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
      (f := fun ω : Ω => |Y ω k - mu k| ^ 3) (g := fun _ : Ω => (1 : ℝ))
    simp only [honeP, mul_one] at h
    simpa using h
  have hIk2 : (∫ x : Ω × Ω, |G x.1 k - mu k| ^ 3 ∂(P.prod P))
      = ∫ ω : Ω, |G ω k - mu k| ^ 3 ∂P := by
    have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
      (f := fun ω : Ω => |G ω k - mu k| ^ 3) (g := fun _ : Ω => (1 : ℝ))
    simp only [honeP, mul_one] at h
    simpa using h
  have hIk3 : (∫ x : Ω × Ω, |G x.2 k - mu k| ^ 3 ∂(P.prod P))
      = ∫ ω : Ω, |G ω k - mu k| ^ 3 ∂P := by
    have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
      (f := fun _ : Ω => (1 : ℝ)) (g := fun ω : Ω => |G ω k - mu k| ^ 3)
    simp only [honeP, one_mul] at h
    simpa using h
  have hIY : Integrable (fun x : Ω × Ω => |Y x.1 k - mu k| ^ 3) (P.prod P) :=
    hYk_i.comp_fst P
  have hIG1 : Integrable (fun x : Ω × Ω => |G x.1 k - mu k| ^ 3) (P.prod P) :=
    hGk_i.comp_fst P
  have hIG2 : Integrable (fun x : Ω × Ω => |G x.2 k - mu k| ^ 3) (P.prod P) :=
    hGk_i.comp_snd P
  have hcube3 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      (a + b + c) ^ 3 ≤ 9 * (a ^ 3 + b ^ 3 + c ^ 3) := by
    intro a b c ha hb hc
    have hsq : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      have hexp : (a + b + c) ^ 2 =
          (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a * b + b * c + c * a) := by ring
      rw [hexp]
      have h1 : (0 : ℝ) ≤ (a - b) ^ 2 := sq_nonneg _
      have h2 : (0 : ℝ) ≤ (b - c) ^ 2 := sq_nonneg _
      have h3 : (0 : ℝ) ≤ (c - a) ^ 2 := sq_nonneg _
      have hid : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 =
          2 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a * b + b * c + c * a) := by ring
      linarith
    have h1 : a ^ 2 * b + a * b ^ 2 ≤ a ^ 3 + b ^ 3 := by
      have hh : (0 : ℝ) ≤ (a - b) ^ 2 * (a + b) :=
        mul_nonneg (sq_nonneg (a - b)) (by linarith)
      have he : a ^ 3 + b ^ 3 - (a ^ 2 * b + a * b ^ 2) = (a - b) ^ 2 * (a + b) := by
        ring
      linarith
    have h2 : a ^ 2 * c + a * c ^ 2 ≤ a ^ 3 + c ^ 3 := by
      have hh : (0 : ℝ) ≤ (a - c) ^ 2 * (a + c) :=
        mul_nonneg (sq_nonneg (a - c)) (by linarith)
      have he : a ^ 3 + c ^ 3 - (a ^ 2 * c + a * c ^ 2) = (a - c) ^ 2 * (a + c) := by
        ring
      linarith
    have h3 : b ^ 2 * c + b * c ^ 2 ≤ b ^ 3 + c ^ 3 := by
      have hh : (0 : ℝ) ≤ (b - c) ^ 2 * (b + c) :=
        mul_nonneg (sq_nonneg (b - c)) (by linarith)
      have he : b ^ 3 + c ^ 3 - (b ^ 2 * c + b * c ^ 2) = (b - c) ^ 2 * (b + c) := by
        ring
      linarith
    have hprod : (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 3 * (a ^ 3 + b ^ 3 + c ^ 3) := by
      have hexp : (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) = (a ^ 3 + b ^ 3 + c ^ 3) +
          ((a ^ 2 * b + a * b ^ 2) + (a ^ 2 * c + a * c ^ 2) + (b ^ 2 * c + b * c ^ 2)) := by
        ring
      rw [hexp]
      linarith
    have hsum : (0 : ℝ) ≤ a + b + c := by linarith
    have hstep : (a + b + c) ^ 3 ≤ (a + b + c) * (3 * (a ^ 2 + b ^ 2 + c ^ 2)) := by
      have h : (a + b + c) ^ 3 = (a + b + c) * (a + b + c) ^ 2 := by ring
      rw [h]
      exact mul_le_mul_of_nonneg_left hsq hsum
    refine le_trans hstep ?_
    have hmult : (a + b + c) * (3 * (a ^ 2 + b ^ 2 + c ^ 2)) =
        3 * ((a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2)) := by ring
    rw [hmult]
    have hna : (0 : ℝ) ≤ a ^ 3 := pow_nonneg ha 3
    have hnb : (0 : ℝ) ≤ b ^ 3 := pow_nonneg hb 3
    have hnc : (0 : ℝ) ≤ c ^ 3 := pow_nonneg hc 3
    linarith
  have hQkcube : ∀ x : Ω × Ω, Qk x ^ 3 ≤ 9 * (|Y x.1 k - mu k| ^ 3 +
      |G x.1 k - mu k| ^ 3 + |G x.2 k - mu k| ^ 3) := by
    intro x
    exact hcube3 _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
  show Integrable (fun x : Ω × Ω => |UU x k * UU x l * VV x j|) (P.prod P) ∧
      (∫ x : Ω × Ω, |UU x k * UU x l * VV x j| ∂(P.prod P)) ≤
        (3 / 2 : ℝ) * ((√(m : ℝ))⁻¹) ^ 3 * |delta| ^ 3 *
          ((√t)⁻¹ + (√(1 - t))⁻¹) *
            ((L j + 2 * L' j) + (L k + 2 * L' k) + (L l + 2 * L' l))
  have amgm3 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      3 * (a * b * c) ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
    intro a b c ha hb hc
    have h1 : (0 : ℝ) ≤ (a - b) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (b - c) ^ 2 := sq_nonneg _
    have h3 : (0 : ℝ) ≤ (c - a) ^ 2 := sq_nonneg _
    have hsum : (0 : ℝ) ≤ a + b + c := by linarith
    have hnn : (0 : ℝ) ≤ (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) :=
      mul_nonneg hsum (by linarith)
    have hid : (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) =
        2 * (a ^ 3 + b ^ 3 + c ^ 3) - 6 * (a * b * c) := by ring
    linarith
  have hQcube : ∀ (r : Fin p) (X : Ω × Ω → ℝ),
      (∀ x : Ω × Ω, X x = |Y x.1 r - mu r| + |G x.1 r - mu r| + |G x.2 r - mu r|) →
      Integrable (fun x : Ω × Ω => X x ^ 3) (P.prod P) ∧
        (∫ x : Ω × Ω, X x ^ 3 ∂(P.prod P)) ≤ 9 * (L r + 2 * L' r) := by
    intro r X hXeq
    obtain ⟨iY, bY, iG, bG⟩ := hL r
    have hi1 : Integrable (fun x : Ω × Ω => |Y x.1 r - mu r| ^ 3) (P.prod P) := iY.comp_fst P
    have hi2 : Integrable (fun x : Ω × Ω => |G x.1 r - mu r| ^ 3) (P.prod P) := iG.comp_fst P
    have hi3 : Integrable (fun x : Ω × Ω => |G x.2 r - mu r| ^ 3) (P.prod P) := iG.comp_snd P
    have hSI : Integrable (fun x : Ω × Ω =>
        |Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3 + |G x.2 r - mu r| ^ 3) (P.prod P) :=
      (hi1.add hi2).add hi3
    have m1 : (∫ x : Ω × Ω, |Y x.1 r - mu r| ^ 3 ∂(P.prod P))
        = ∫ ω : Ω, |Y ω r - mu r| ^ 3 ∂P := by
      have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
        (f := fun ω : Ω => |Y ω r - mu r| ^ 3) (g := fun _ : Ω => (1 : ℝ))
      simp only [honeP, mul_one] at h
      simpa using h
    have m2 : (∫ x : Ω × Ω, |G x.1 r - mu r| ^ 3 ∂(P.prod P))
        = ∫ ω : Ω, |G ω r - mu r| ^ 3 ∂P := by
      have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
        (f := fun ω : Ω => |G ω r - mu r| ^ 3) (g := fun _ : Ω => (1 : ℝ))
      simp only [honeP, mul_one] at h
      simpa using h
    have m3 : (∫ x : Ω × Ω, |G x.2 r - mu r| ^ 3 ∂(P.prod P))
        = ∫ ω : Ω, |G ω r - mu r| ^ 3 ∂P := by
      have h := MeasureTheory.integral_prod_mul (μ := P) (ν := P)
        (f := fun _ : Ω => (1 : ℝ)) (g := fun ω : Ω => |G ω r - mu r| ^ 3)
      simp only [honeP, one_mul] at h
      simpa using h
    have e2s : (∫ x : Ω × Ω,
        (|Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3 + |G x.2 r - mu r| ^ 3) ∂(P.prod P)) =
        (∫ x : Ω × Ω, (|Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3) ∂(P.prod P)) +
          (∫ x : Ω × Ω, |G x.2 r - mu r| ^ 3 ∂(P.prod P)) :=
      MeasureTheory.integral_add (hi1.add hi2) hi3
    have e1s : (∫ x : Ω × Ω, (|Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3) ∂(P.prod P)) =
        (∫ x : Ω × Ω, |Y x.1 r - mu r| ^ 3 ∂(P.prod P)) +
          (∫ x : Ω × Ω, |G x.1 r - mu r| ^ 3 ∂(P.prod P)) :=
      MeasureTheory.integral_add hi1 hi2
    have hSle : (∫ x : Ω × Ω,
        (|Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3 + |G x.2 r - mu r| ^ 3) ∂(P.prod P))
        ≤ L r + 2 * L' r := by
      rw [e2s, e1s, m1, m2, m3]
      linarith
    have hX0 : ∀ x : Ω × Ω, (0 : ℝ) ≤ X x := by
      intro x
      rw [hXeq x]
      positivity
    have hpt : ∀ x : Ω × Ω, X x ^ 3 ≤ 9 *
        (|Y x.1 r - mu r| ^ 3 + |G x.1 r - mu r| ^ 3 + |G x.2 r - mu r| ^ 3) := by
      intro x
      rw [hXeq x]
      exact hcube3 _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    have hXm : Measurable (fun x : Ω × Ω => X x ^ 3) := by
      have heq : (fun x : Ω × Ω => X x ^ 3) = fun x : Ω × Ω =>
          (|Y x.1 r - mu r| + |G x.1 r - mu r| + |G x.2 r - mu r|) ^ 3 := by
        funext x
        rw [hXeq x]
      rw [heq]
      fun_prop
    have hXint : Integrable (fun x : Ω × Ω => X x ^ 3) (P.prod P) := by
      refine (hSI.const_mul 9).mono' hXm.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hX0 x) 3)]
      exact hpt x
    refine ⟨hXint, ?_⟩
    have hcomp := MeasureTheory.integral_mono hXint (hSI.const_mul 9) hpt
    rw [MeasureTheory.integral_const_mul] at hcomp
    exact le_trans hcomp (by linarith [hSle])
  have hQk3 : Integrable (fun x : Ω × Ω => Qk x ^ 3) (P.prod P) ∧
      (∫ x : Ω × Ω, Qk x ^ 3 ∂(P.prod P)) ≤ 9 * (L k + 2 * L' k) :=
    hQcube k Qk (fun x => rfl)
  have hQl3 : Integrable (fun x : Ω × Ω => Ql x ^ 3) (P.prod P) ∧
      (∫ x : Ω × Ω, Ql x ^ 3 ∂(P.prod P)) ≤ 9 * (L l + 2 * L' l) :=
    hQcube l Ql (fun x => rfl)
  have hQj3 : Integrable (fun x : Ω × Ω => Qj x ^ 3) (P.prod P) ∧
      (∫ x : Ω × Ω, Qj x ^ 3 ∂(P.prod P)) ≤ 9 * (L j + 2 * L' j) :=
    hQcube j Qj (fun x => rfl)
  have hSI3 : Integrable (fun x : Ω × Ω => Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) (P.prod P) :=
    (hQk3.1.add hQl3.1).add hQj3.1
  have hDint : Integrable (fun x : Ω × Ω =>
      (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3)) (P.prod P) :=
    hSI3.const_mul _
  have hK0 : (0 : ℝ) ≤
      1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) := by
    have h1 : (0 : ℝ) ≤ ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ :=
      inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg (m : ℝ)) 3)
    have h2 : (0 : ℝ) ≤ |delta| ^ 3 := pow_nonneg (abs_nonneg delta) 3
    have h3 : (0 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
    exact mul_nonneg (mul_nonneg (mul_nonneg h3 h1) h2) hW0
  have hK3 : (0 : ℝ) ≤
      1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3 :=
    div_nonneg hK0 (by norm_num)
  have hfinpt : ∀ x : Ω × Ω, |UU x k * UU x l * VV x j| ≤
      (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) := by
    intro x
    have h1 := hprod x
    have h2 : 3 * (Qk x * Ql x * Qj x) ≤ Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3 :=
      amgm3 _ _ _ (hQk0 x) (hQl0 x) (hQj0 x)
    have h3 : Qk x * Ql x * Qj x ≤ (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) / 3 := by linarith
    have h4 : (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹)) *
        (Qk x * Ql x * Qj x) ≤
        (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹)) *
          ((Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) / 3) :=
      mul_le_mul_of_nonneg_left h3 hK0
    have h5 : (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹)) *
          ((Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) / 3) =
        (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
          (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) := by ring
    linarith
  have hfinint : Integrable (fun x : Ω × Ω => |UU x k * UU x l * VV x j|) (P.prod P) := by
    have hm : Measurable (fun x : Ω × Ω => |UU x k * UU x l * VV x j|) := by
      simp only [hUU, hVV]
      fun_prop
    refine hDint.mono' hm.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hfinpt x
  refine ⟨hfinint, ?_⟩
  have hmono := MeasureTheory.integral_mono hfinint hDint hfinpt
  have hDval : (∫ x : Ω × Ω,
      (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) ∂(P.prod P)) =
      (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        ((∫ x : Ω × Ω, Qk x ^ 3 ∂(P.prod P)) + (∫ x : Ω × Ω, Ql x ^ 3 ∂(P.prod P)) +
          (∫ x : Ω × Ω, Qj x ^ 3 ∂(P.prod P))) := by
    rw [MeasureTheory.integral_const_mul]
    have e2d : (∫ x : Ω × Ω, (Qk x ^ 3 + Ql x ^ 3 + Qj x ^ 3) ∂(P.prod P)) =
        (∫ x : Ω × Ω, (Qk x ^ 3 + Ql x ^ 3) ∂(P.prod P)) +
          (∫ x : Ω × Ω, Qj x ^ 3 ∂(P.prod P)) :=
      MeasureTheory.integral_add (hQk3.1.add hQl3.1) hQj3.1
    have e1d : (∫ x : Ω × Ω, (Qk x ^ 3 + Ql x ^ 3) ∂(P.prod P)) =
        (∫ x : Ω × Ω, Qk x ^ 3 ∂(P.prod P)) + (∫ x : Ω × Ω, Ql x ^ 3 ∂(P.prod P)) :=
      MeasureTheory.integral_add hQk3.1 hQl3.1
    rw [e2d, e1d]
  rw [hDval] at hmono
  refine le_trans hmono ?_
  have hbound : (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
      ((∫ x : Ω × Ω, Qk x ^ 3 ∂(P.prod P)) + (∫ x : Ω × Ω, Ql x ^ 3 ∂(P.prod P)) +
        (∫ x : Ω × Ω, Qj x ^ 3 ∂(P.prod P))) ≤
      (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        (9 * ((L k + 2 * L' k) + (L l + 2 * L' l) + (L j + 2 * L' j))) := by
    refine mul_le_mul_of_nonneg_left ?_ hK3
    linarith [hQk3.2, hQl3.2, hQj3.2]
  refine le_trans hbound ?_
  have hcalc : (1 / 2 * ((√(m : ℝ)) ^ (3 : ℕ))⁻¹ * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹) / 3) *
        (9 * ((L k + 2 * L' k) + (L l + 2 * L' l) + (L j + 2 * L' j))) =
      (3 / 2 * ((√(m : ℝ))⁻¹) ^ 3 * |delta| ^ 3 * ((√t)⁻¹ + (√(1 - t))⁻¹)) *
        ((L j + 2 * L' j) + (L k + 2 * L' k) + (L l + 2 * L' l)) := by
    rw [← inv_pow]
    ring
  exact le_of_eq hcalc

/-- Source-ready X-row specialization: the right side retains only j,k,l moments. -/
theorem real_x_row_coordinate_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n p : ℕ) (hn : 0 < n)
    (mu : Fin p → ℝ) (X F : Ω → Fin p → ℝ)
    (hX : Measurable X) (hF : Measurable F)
    (hX3 : ∀ r, Integrable (fun x => |X x r - mu r|^3) P)
    (hF3 : ∀ r, Integrable (fun x => |F x r - mu r|^3) P)
    (t v : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (j k l : Fin p) :
    let U : Ω × Ω → Fin p → ℝ := fun x r =>
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t * (Real.sqrt v * (X x.1 r - mu r) +
          Real.sqrt (1-v) * (F x.1 r - mu r)) +
          Real.sqrt (1-t) * (F x.2 r - mu r))
    let V : Ω × Ω → Fin p → ℝ := fun x r =>
      (Real.sqrt (n : ℝ))⁻¹ *
        ((2*Real.sqrt t)⁻¹ * (Real.sqrt v * (X x.1 r - mu r) +
          Real.sqrt (1-v) * (F x.1 r - mu r)) -
          (2*Real.sqrt (1-t))⁻¹ * (F x.2 r - mu r))
    let T : Fin p → ℝ := fun r => (∫ x, |X x r - mu r|^3 ∂P) +
      2*(∫ x, |F x r - mu r|^3 ∂P)
    Integrable (fun x => |U x k * U x l * V x j|) (P.prod P) ∧
      (∫ x, |U x k * U x l * V x j| ∂(P.prod P)) ≤
        (3/2) * ((Real.sqrt (n : ℝ))⁻¹)^3 *
          ((Real.sqrt t)⁻¹ + (Real.sqrt (1-t))⁻¹) * (T j + T k + T l) := by
  have h := real_row_coordinate_moment p Ω P n hn 1 one_ne_zero t ht0 ht1 v hv0 hv1
    mu X F (fun r => (measurable_pi_apply r).comp hX)
    (fun r => (measurable_pi_apply r).comp hF)
    (fun r => ∫ x, |X x r - mu r|^3 ∂P)
    (fun r => ∫ x, |F x r - mu r|^3 ∂P)
    (fun r => ⟨hX3 r, le_rfl, hF3 r, le_rfl⟩)
  dsimp only at h ⊢
  simpa only [abs_one, one_pow, mul_one] using h j k l



end DCFManualXAudit

