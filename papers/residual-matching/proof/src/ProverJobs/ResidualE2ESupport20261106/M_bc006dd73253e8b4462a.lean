import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_4274718050_2cbaed7c : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (S : Ω → Fin n → ℝ)
    (hmeas : ∀ i : Fin n, Measurable fun ω => S ω i)
    (hnonneg : ∀ (ω : Ω) (i : Fin n), 0 ≤ S ω i)
    (hint : ∀ i : Fin n, Integrable (fun ω => max (S ω i - 4) 0) μ)
    (nuA nuRho : Measure ℝ)
    (hFR_hi : ∀ x : ℝ, 4 ≤ x → (nuRho (Set.Iic x)).toReal = 1)
    (hFR_lo : ∀ x : ℝ, x ≤ -4 → (nuRho (Set.Iic x)).toReal = 0)
    (hFA_hi : ∀ x : ℝ, 0 ≤ x → 1 - (nuA (Set.Iic x)).toReal =
      ∫ ω, (2 * (n : ℝ))⁻¹ *
        ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ∂μ)
    (hFA_lo : ∀ x : ℝ, x < 0 → (nuA (Set.Iic x)).toReal =
      ∫ ω, (2 * (n : ℝ))⁻¹ *
        ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ) ∂μ),
    MeasureTheory.IntegrableOn
        (fun x : ℝ => |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|)
        {x : ℝ | 4 < |x|}
      ∧ (∫ x in {x : ℝ | 4 < |x|},
          |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|)
        = (n : ℝ)⁻¹ * ∫ ω, ∑ i : Fin n, max (S ω i - 4) 0 ∂μ := by
  /- @proof-region region.target-node.session.f27e732c489a0071 begin -/
  intro Ω _ μ _ n hn S hmeas hnonneg hint nuA nuRho hFR_hi hFR_lo hFA_hi hFA_lo
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hne : (2*(n:ℝ))⁻¹ + (2*(n:ℝ))⁻¹ = (n:ℝ)⁻¹ := by
    have hn' : (n:ℝ) ≠ 0 := ne_of_gt hnpos
    have h2 : (2*(n:ℝ)) ≠ 0 := by
      have : (0:ℝ) < 2*(n:ℝ) := by linarith
      exact ne_of_gt this
    field_simp
    ring
  have hsplit : {x : ℝ | 4 < |x|} = Set.Ioi 4 ∪ Set.Iio (-4) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, lt_abs, lt_neg]
  have hdisj : Disjoint (Set.Ioi (4:ℝ)) (Set.Iio (-4:ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ioi] at hx1
    simp only [Set.mem_Iio] at hx2
    linarith
  have hmeasU : MeasurableSet (Set.Ioi (4:ℝ)) := measurableSet_Ioi
  have hmeasL : MeasurableSet (Set.Iio (-4:ℝ)) := measurableSet_Iio
  have hU : ∀ x ∈ Set.Ioi 4, |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal| = ∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ∂μ := by
    intro x hx
    have hx4 : (4:ℝ) ≤ x := le_of_lt hx
    have hx0 : (0:ℝ) ≤ x := le_trans (by norm_num) hx4
    have hG1 : (nuRho (Set.Iic x)).toReal = 1 := hFR_hi x hx4
    have hFx : 1 - (nuA (Set.Iic x)).toReal = ∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ∂μ := hFA_hi x hx0
    have hnn : ∀ ω : Ω, 0 ≤ (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) := by
      intro ω
      have hcoef : (0:ℝ) ≤ (2*(n:ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
      exact mul_nonneg hcoef (by positivity)
    have hI0 : 0 ≤ ∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ∂μ := integral_nonneg hnn
    have hle : (nuA (Set.Iic x)).toReal ≤ 1 := by
      have hge : (0:ℝ) ≤ 1 - (nuA (Set.Iic x)).toReal := by rw [hFx]; exact hI0
      linarith
    calc |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|
        = |(nuA (Set.Iic x)).toReal - 1| := by rw [hG1]
      _ = 1 - (nuA (Set.Iic x)).toReal := by rw [abs_of_nonpos (by linarith)]; ring
      _ = _ := hFx
  have hL : ∀ x ∈ Set.Iio (-4), |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal| = ∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ) ∂μ := by
    intro x hx
    have hx4 : x ≤ -4 := le_of_lt hx
    have hx0 : x < 0 := by linarith
    have hG0 : (nuRho (Set.Iic x)).toReal = 0 := hFR_lo x hx4
    have hFx : (nuA (Set.Iic x)).toReal = ∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ) ∂μ := hFA_lo x hx0
    have hnn : ∀ ω : Ω, 0 ≤ (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ) := by
      intro ω
      exact mul_nonneg (inv_nonneg.mpr (by linarith)) (by positivity)
    have hF0 : 0 ≤ (nuA (Set.Iic x)).toReal := by rw [hFx]; exact integral_nonneg hnn
    calc |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|
        = |(nuA (Set.Iic x)).toReal - 0| := by rw [hG0]
      _ = (nuA (Set.Iic x)).toReal := by rw [sub_zero, abs_of_nonneg hF0]
      _ = _ := hFx
  have hind : ∀ (c : ℝ), (∫ x in Set.Ioi (4:ℝ), (if x < c then (1:ℝ) else 0)) = max (c - 4) 0 := by
    intro c
    have hstep : (∫ x in Set.Ioi (4:ℝ), (if x < c then (1:ℝ) else 0)) = ∫ x, (Set.Ioo (4:ℝ) c).indicator (fun _ => (1:ℝ)) x := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
      have hfun : (Set.Ioi (4:ℝ)).indicator (fun x => if x < c then (1:ℝ) else 0) = (Set.Ioo (4:ℝ) c).indicator (fun _ => (1:ℝ)) := by
        funext x
        by_cases hx : (4:ℝ) < x
        · simp [Set.indicator, Set.mem_Ioo, hx]
        · simp [Set.indicator, hx]
      rw [hfun]
    rw [hstep, MeasureTheory.integral_indicator_const (1:ℝ) measurableSet_Ioo]
    simp only [smul_eq_mul, mul_one]
    change (volume (Set.Ioo (4:ℝ) c)).toReal = max (c - 4) 0
    rw [Real.volume_Ioo]
    by_cases h : (0:ℝ) ≤ c - 4
    · rw [ENNReal.toReal_ofReal h, max_eq_left h]
    · push_neg at h
      rw [ENNReal.ofReal_eq_zero.mpr (le_of_lt h), ENNReal.toReal_zero, max_eq_right (le_of_lt h)]
  have hint_ind : ∀ (c : ℝ), Integrable (fun x : ℝ => if x < c then (1:ℝ) else 0) (volume.restrict (Set.Ioi (4:ℝ))) := by
    intro c
    have hfun : (fun x : ℝ => if x < c then (1:ℝ) else 0) = (Set.Iio c).indicator (fun _ => (1:ℝ)) := by
      funext x; simp [Set.indicator, Set.mem_Iio]
    rw [hfun]
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Iio]
    rw [MeasureTheory.integrableOn_const_iff]
    right
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
    rw [show Set.Iio c ∩ Set.Ioi (4:ℝ) = Set.Ioo (4:ℝ) c from by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]; tauto]
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hinner : ∀ (ω : Ω), (∫ x in Set.Ioi (4:ℝ), (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ)) = (2*(n:ℝ))⁻¹ * (∑ i : Fin n, max (S ω i - 4) 0) := by
    intro ω
    have hcard : ∀ x : ℝ, ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) = ∑ i : Fin n, (if x < S ω i then (1:ℝ) else 0) := by
      intro x
      rw [Finset.card_filter]
      push_cast
      simp
    rw [MeasureTheory.integral_const_mul]
    congr 1
    simp only [hcard]
    trans (∑ i : Fin n, ∫ x in Set.Ioi (4:ℝ), (if x < S ω i then (1:ℝ) else 0))
    · exact MeasureTheory.integral_finset_sum (f := fun (i : Fin n) (x : ℝ) => if x < S ω i then (1:ℝ) else 0) Finset.univ (fun i _ => hint_ind (S ω i))
    · exact Finset.sum_congr rfl (fun i _ => hind (S ω i))
  have hIntProd : Integrable (Function.uncurry (fun (x : ℝ) (ω : Ω) => (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ))) ((volume.restrict (Set.Ioi (4:ℝ))).prod μ) := by
    have hsetU : ∀ i : Fin n, MeasurableSet {p : ℝ × Ω | p.1 < S p.2 i} := by
      intro i
      have hm : Measurable (fun p : ℝ × Ω => S p.2 i - p.1) := ((hmeas i).comp measurable_snd).sub measurable_fst
      have heq : {p : ℝ × Ω | p.1 < S p.2 i} = (fun p : ℝ × Ω => S p.2 i - p.1) ⁻¹' (Set.Ioi (0:ℝ)) := by
        ext p; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi]; constructor <;> intro h <;> linarith
      rw [heq]
      exact measurableSet_Ioi.preimage hm
    have hprodU : ∀ i : Fin n, ((volume.restrict (Set.Ioi (4:ℝ))).prod μ) {p : ℝ × Ω | p.1 < S p.2 i} < ⊤ := by
      intro i
      rw [MeasureTheory.Measure.prod_apply_symm (hsetU i)]
      have hI : ∀ ω : Ω, (fun x : ℝ => (x, ω)) ⁻¹' {p : ℝ × Ω | p.1 < S p.2 i} = Set.Iio (S ω i) := by
        intro ω; ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Iio]
      simp only [hI]
      have hV : ∀ ω : Ω, (volume.restrict (Set.Ioi (4:ℝ))) (Set.Iio (S ω i)) = ENNReal.ofReal (max (S ω i - 4) 0) := by
        intro ω
        rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
        rw [show Set.Iio (S ω i) ∩ Set.Ioi (4:ℝ) = Set.Ioo (4:ℝ) (S ω i) from by
          ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]; tauto]
        rw [Real.volume_Ioo]
        by_cases h : (0:ℝ) ≤ S ω i - 4
        · rw [max_eq_left h]
        · push_neg at h
          rw [max_eq_right (le_of_lt h), ENNReal.ofReal_eq_zero.mpr (le_of_lt h), ENNReal.ofReal_zero]
      simp only [hV]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint i) (Filter.Eventually.of_forall (fun ω => le_max_right (S ω i - 4) 0))]
      exact ENNReal.ofReal_lt_top
    have hpt : (Function.uncurry (fun (x : ℝ) (ω : Ω) => (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ))) = fun p : ℝ × Ω => ∑ i : Fin n, (2*(n:ℝ))⁻¹ * (if p.1 < S p.2 i then (1:ℝ) else 0) := by
      funext p
      simp only [Function.uncurry]
      have hc : ((Finset.univ.filter (fun i : Fin n => p.1 < S p.2 i)).card : ℝ) = ∑ i : Fin n, (if p.1 < S p.2 i then (1:ℝ) else 0) := by
        rw [Finset.card_filter]; push_cast; simp
      rw [hc, Finset.mul_sum]
    rw [hpt]
    refine MeasureTheory.integrable_finset_sum (s := Finset.univ) (f := fun (i : Fin n) (p : ℝ × Ω) => (2*(n:ℝ))⁻¹ * (if p.1 < S p.2 i then (1:ℝ) else 0)) (fun i _ => ?_)
    have hi : Integrable (fun p : ℝ × Ω => if p.1 < S p.2 i then (1:ℝ) else 0) ((volume.restrict (Set.Ioi (4:ℝ))).prod μ) := by
      have hfun : (fun p : ℝ × Ω => if p.1 < S p.2 i then (1:ℝ) else 0) = {p : ℝ × Ω | p.1 < S p.2 i}.indicator (fun _ => (1:ℝ)) := by
        funext p; by_cases h : p.1 < S p.2 i <;> simp [Set.indicator, h]
      rw [hfun, MeasureTheory.integrable_indicator_iff (hsetU i)]
      rw [MeasureTheory.integrableOn_const_iff]
      exact Or.inr (hprodU i)
    exact hi.const_mul (2*(n:ℝ))⁻¹
  have keyU : (∫ x in Set.Ioi 4, (∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ∂μ)) = (2*(n:ℝ))⁻¹ * ∫ ω, ∑ i : Fin n, max (S ω i - 4) 0 ∂μ := by
    rw [show (∫ x in Set.Ioi 4, (∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ∂μ)) = ∫ x, (∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ∂μ) ∂(volume.restrict (Set.Ioi (4:ℝ))) from rfl]
    rw [MeasureTheory.integral_integral_swap hIntProd]
    simp only [hinner]
    rw [MeasureTheory.integral_const_mul]
  have hintU : MeasureTheory.IntegrableOn (fun x => ∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ∂μ) (Set.Ioi 4) := by
    have h := hIntProd.integral_prod_left
    simpa only [Function.uncurry] using h
  have hindL : ∀ (c : ℝ), (∫ x in Set.Iio (-4), (if -x ≤ c then (1:ℝ) else 0)) = max (c - 4) 0 := by
    intro c
    have hstep : (∫ x in Set.Iio (-4), (if -x ≤ c then (1:ℝ) else 0)) = ∫ x, (Set.Ico (-c) (-4)).indicator (fun _ => (1:ℝ)) x := by
      rw [← MeasureTheory.integral_indicator measurableSet_Iio]
      have hfun : (Set.Iio (-4)).indicator (fun x => if -x ≤ c then (1:ℝ) else 0) = (Set.Ico (-c) (-4)).indicator (fun _ => (1:ℝ)) := by
        funext x
        by_cases hx : x < -4
        · have hb : ((-x ≤ c) ↔ (-c ≤ x)) := by constructor <;> intro h <;> linarith
          simp [Set.indicator, Set.mem_Iio, Set.mem_Ico, hx, hb]
        · simp [Set.indicator, Set.mem_Iio, Set.mem_Ico, hx]
      rw [hfun]
    rw [hstep, MeasureTheory.integral_indicator_const (1:ℝ) measurableSet_Ico]
    simp only [smul_eq_mul, mul_one]
    change (volume (Set.Ico (-c) (-4))).toReal = max (c - 4) 0
    rw [Real.volume_Ico]
    rw [show (-4:ℝ) - (-c) = c - 4 from by ring]
    by_cases h : (0:ℝ) ≤ c - 4
    · rw [ENNReal.toReal_ofReal h, max_eq_left h]
    · push_neg at h
      rw [ENNReal.ofReal_eq_zero.mpr (le_of_lt h), ENNReal.toReal_zero, max_eq_right (le_of_lt h)]
  have hint_indL : ∀ (c : ℝ), Integrable (fun x : ℝ => if -x ≤ c then (1:ℝ) else 0) (volume.restrict (Set.Iio (-4))) := by
    intro c
    have hfun : (fun x : ℝ => if -x ≤ c then (1:ℝ) else 0) = (Set.Ici (-c)).indicator (fun _ => (1:ℝ)) := by
      funext x
      change (if -x ≤ c then (1:ℝ) else 0) = (if x ∈ Set.Ici (-c) then (1:ℝ) else 0)
      by_cases h : -x ≤ c
      · have h' : x ∈ Set.Ici (-c) := by simp only [Set.mem_Ici]; linarith
        rw [if_pos h, if_pos h']
      · have h' : x ∉ Set.Ici (-c) := by simp only [Set.mem_Ici]; linarith
        rw [if_neg h, if_neg h']
    rw [hfun]
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ici]
    rw [MeasureTheory.integrableOn_const_iff]
    right
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ici]
    rw [show Set.Ici (-c) ∩ Set.Iio (-4) = Set.Ico (-c) (-4) from by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iio, Set.mem_Ico]]
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hinnerL : ∀ (ω : Ω), (∫ x in Set.Iio (-4), (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ)) = (2*(n:ℝ))⁻¹ * (∑ i : Fin n, max (S ω i - 4) 0) := by
    intro ω
    have hcard : ∀ x : ℝ, ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ) = ∑ i : Fin n, (if -x ≤ S ω i then (1:ℝ) else 0) := by
      intro x
      rw [Finset.card_filter]; push_cast; simp
    rw [MeasureTheory.integral_const_mul]
    congr 1
    simp only [hcard]
    trans (∑ i : Fin n, ∫ x in Set.Iio (-4), (if -x ≤ S ω i then (1:ℝ) else 0))
    · exact MeasureTheory.integral_finset_sum (f := fun (i : Fin n) (x : ℝ) => if -x ≤ S ω i then (1:ℝ) else 0) Finset.univ (fun i _ => hint_indL (S ω i))
    · exact Finset.sum_congr rfl (fun i _ => hindL (S ω i))
  have hsetPrL : ∀ i : Fin n, MeasurableSet {p : ℝ × Ω | -p.1 ≤ S p.2 i} := by
    intro i
    have hm : Measurable (fun p : ℝ × Ω => S p.2 i + p.1) := ((hmeas i).comp measurable_snd).add measurable_fst
    have heq : {p : ℝ × Ω | -p.1 ≤ S p.2 i} = (fun p : ℝ × Ω => S p.2 i + p.1) ⁻¹' (Set.Ici (0:ℝ)) := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]; constructor <;> intro h <;> linarith
    rw [heq]
    exact measurableSet_Ici.preimage hm
  have hprodL : ∀ i : Fin n, ((volume.restrict (Set.Iio (-4))).prod μ) {p : ℝ × Ω | -p.1 ≤ S p.2 i} < ⊤ := by
    intro i
    rw [MeasureTheory.Measure.prod_apply_symm (hsetPrL i)]
    have hI : ∀ ω : Ω, (fun x : ℝ => (x, ω)) ⁻¹' {p : ℝ × Ω | -p.1 ≤ S p.2 i} = Set.Ici (-(S ω i)) := by
      intro ω; ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ici]; constructor <;> intro h <;> linarith
    simp only [hI]
    have hV : ∀ ω : Ω, (volume.restrict (Set.Iio (-4))) (Set.Ici (-(S ω i))) = ENNReal.ofReal (max (S ω i - 4) 0) := by
      intro ω
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ici]
      rw [show Set.Ici (-(S ω i)) ∩ Set.Iio (-4) = Set.Ico (-(S ω i)) (-4) from by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iio, Set.mem_Ico]]
      rw [Real.volume_Ico]
      rw [show (-4:ℝ) - (-(S ω i)) = S ω i - 4 from by ring]
      by_cases h : (0:ℝ) ≤ S ω i - 4
      · rw [max_eq_left h]
      · push_neg at h
        rw [max_eq_right (le_of_lt h), ENNReal.ofReal_eq_zero.mpr (le_of_lt h), ENNReal.ofReal_zero]
    simp only [hV]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint i) (Filter.Eventually.of_forall (fun ω => le_max_right (S ω i - 4) 0))]
    exact ENNReal.ofReal_lt_top
  have hIntProdL : Integrable (Function.uncurry (fun (x : ℝ) (ω : Ω) => (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ))) ((volume.restrict (Set.Iio (-4))).prod μ) := by
    have hpt : (Function.uncurry (fun (x : ℝ) (ω : Ω) => (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ))) = fun p : ℝ × Ω => ∑ i : Fin n, (2*(n:ℝ))⁻¹ * (if -p.1 ≤ S p.2 i then (1:ℝ) else 0) := by
      funext p
      simp only [Function.uncurry]
      have hc : ((Finset.univ.filter (fun i : Fin n => -p.1 ≤ S p.2 i)).card : ℝ) = ∑ i : Fin n, (if -p.1 ≤ S p.2 i then (1:ℝ) else 0) := by
        rw [Finset.card_filter]; push_cast; simp
      rw [hc, Finset.mul_sum]
    rw [hpt]
    refine MeasureTheory.integrable_finset_sum (s := Finset.univ) (f := fun (i : Fin n) (p : ℝ × Ω) => (2*(n:ℝ))⁻¹ * (if -p.1 ≤ S p.2 i then (1:ℝ) else 0)) (fun i _ => ?_)
    have hi : Integrable (fun p : ℝ × Ω => if -p.1 ≤ S p.2 i then (1:ℝ) else 0) ((volume.restrict (Set.Iio (-4))).prod μ) := by
      have hfun : (fun p : ℝ × Ω => if -p.1 ≤ S p.2 i then (1:ℝ) else 0) = {p : ℝ × Ω | -p.1 ≤ S p.2 i}.indicator (fun _ => (1:ℝ)) := by
        funext p; by_cases h : -p.1 ≤ S p.2 i <;> simp [Set.indicator, h]
      rw [hfun, MeasureTheory.integrable_indicator_iff (hsetPrL i)]
      rw [MeasureTheory.integrableOn_const_iff]
      exact Or.inr (hprodL i)
    exact hi.const_mul (2*(n:ℝ))⁻¹
  have keyL : (∫ x in Set.Iio (-4), (∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ) ∂μ)) = (2*(n:ℝ))⁻¹ * ∫ ω, ∑ i : Fin n, max (S ω i - 4) 0 ∂μ := by
    rw [show (∫ x in Set.Iio (-4), (∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ) ∂μ)) = ∫ x, (∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ) ∂μ) ∂(volume.restrict (Set.Iio (-4))) from rfl]
    rw [MeasureTheory.integral_integral_swap hIntProdL]
    simp only [hinnerL]
    rw [MeasureTheory.integral_const_mul]
  have hintL : MeasureTheory.IntegrableOn (fun x => ∫ ω, (2*(n:ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ) ∂μ) (Set.Iio (-4)) := by
    have h := hIntProdL.integral_prod_left
    simpa only [Function.uncurry] using h
  have hIU : MeasureTheory.IntegrableOn (fun x : ℝ => |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|) (Set.Ioi 4) :=
    hintU.congr_fun (fun x hx => (hU x hx).symm) hmeasU
  have hIL : MeasureTheory.IntegrableOn (fun x : ℝ => |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|) (Set.Iio (-4)) :=
    hintL.congr_fun (fun x hx => (hL x hx).symm) hmeasL
  have hvalU : (∫ x in Set.Ioi 4, |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|) = (2*(n:ℝ))⁻¹ * ∫ ω, ∑ i : Fin n, max (S ω i - 4) 0 ∂μ := by
    rw [MeasureTheory.setIntegral_congr_fun hmeasU (fun x hx => hU x hx)]
    exact keyU
  have hvalL : (∫ x in Set.Iio (-4), |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|) = (2*(n:ℝ))⁻¹ * ∫ ω, ∑ i : Fin n, max (S ω i - 4) 0 ∂μ := by
    rw [MeasureTheory.setIntegral_congr_fun hmeasL (fun x hx => hL x hx)]
    exact keyL
  constructor
  · rw [hsplit]
    exact hIU.union hIL
  · rw [hsplit, MeasureTheory.setIntegral_union hdisj hmeasL hIU hIL, hvalU, hvalL, ← add_mul, hne]
  /- @proof-region region.target-node.session.f27e732c489a0071 end -/

end Statlib.Imported

