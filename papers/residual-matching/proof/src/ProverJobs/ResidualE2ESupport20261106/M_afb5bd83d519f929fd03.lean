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
theorem statopia_math_node_1754775907_87353225 : ∀ (n : ℕ) (hn : 1 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (s : Ω → Fin n → ℝ)
    (hs : ∀ i : Fin n, Measurable fun ω => s ω i)
    (nuA : MeasureTheory.Measure ℝ) (hnuA : MeasureTheory.IsFiniteMeasure nuA)
    (hcdf : ∀ x : ℝ, (nuA (Set.Iic x)).toReal =
      ∫ ω, (2 * (n : ℝ))⁻¹ *
        (((Finset.univ.filter (fun i : Fin n => s ω i ≤ x)).card : ℝ) +
          ((Finset.univ.filter (fun i : Fin n => -(s ω i) ≤ x)).card : ℝ)) ∂μ)
    (z : ℂ) (hz : 0 < z.im),
    (∫ x, ((x : ℂ) - z)⁻¹ ∂nuA) = ∫ ω, symStieltjesSvals (s ω) z ∂μ := by
  /- @proof-region region.target-node.session.13e988237816b6e6 begin -/
  classical
  intro n hn Ω _ μ _ s hs nuA hnuA hcdf z hz
  haveI hμfin : IsFiniteMeasure μ := ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩
  have hc_nonneg : (0 : ℝ) ≤ (2 * (n : ℝ))⁻¹ := by
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  set ρ : Measure ℝ := ∑ i : Fin n, (μ.map (fun ω => s ω i) + μ.map (fun ω => -(s ω i))) with hρ
  set ν : Measure ℝ := ENNReal.ofReal ((2 * (n : ℝ))⁻¹) • ρ with hν
  have hmap_univ : ∀ (f : Ω → ℝ), Measurable f → (μ.map f) Set.univ = 1 := by
    intro f hf
    rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ, measure_univ]
  have hmap_ne_top : ∀ (f : Ω → ℝ), Measurable f → ∀ t : Set ℝ, (μ.map f) t ≠ ⊤ := by
    intro f hf t
    have hle : (μ.map f) t ≤ (μ.map f) Set.univ := measure_mono (Set.subset_univ t)
    rw [hmap_univ f hf] at hle
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have hρ_apply : ∀ t : Set ℝ,
      ρ t = ∑ i : Fin n, ((μ.map (fun ω => s ω i)) t + (μ.map (fun ω => -(s ω i))) t) := by
    intro t
    rw [hρ, Measure.finset_sum_apply]
    exact Finset.sum_congr rfl (fun i _ => Measure.add_apply _ _ t)
  have hpush : ∀ (i : Fin n), IsFiniteMeasure (μ.map (fun ω => s ω i)) := by
    intro i
    exact ⟨by rw [hmap_univ _ (hs i)]; exact ENNReal.one_lt_top⟩
  have hpush' : ∀ (i : Fin n), IsFiniteMeasure (μ.map (fun ω => -(s ω i))) := by
    intro i
    exact ⟨by rw [hmap_univ _ (hs i).neg]; exact ENNReal.one_lt_top⟩
  have hsum_ne_top : ∀ (I : Finset (Fin n)),
      (∑ i ∈ I, (μ.map (fun ω => s ω i) + μ.map (fun ω => -(s ω i)))) Set.univ ≠ ⊤ := by
    intro I
    induction I using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; simp
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Measure.add_apply]
        refine ENNReal.add_ne_top.mpr ⟨?_, ih⟩
        rw [Measure.add_apply, hmap_univ _ (hs a), hmap_univ _ (hs a).neg]
        norm_num
  have hsum2_ne_top : (∑ i : Fin n, (2 : ENNReal)) ≠ ⊤ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (by norm_num)
  have hρ_univ : ρ Set.univ = ∑ i : Fin n, (2 : ENNReal) := by
    rw [hρ_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hmap_univ _ (hs i), hmap_univ _ (hs i).neg]
    norm_num
  have hν_univ : ν Set.univ ≠ ⊤ := by
    rw [hν, Measure.smul_apply, smul_eq_mul, hρ_univ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum2_ne_top
  haveI hνfin : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hν_univ⟩
  have hind : ∀ (A : Set Ω), MeasurableSet A →
      ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ = (μ A).toReal := by
    intro A hA
    simpa using MeasureTheory.integral_indicator_one hA
  have hν_cdf : ∀ x : ℝ, (ν (Set.Iic x)).toReal =
      ∫ ω, (2 * (n : ℝ))⁻¹ *
        (((Finset.univ.filter (fun i : Fin n => s ω i ≤ x)).card : ℝ) +
          ((Finset.univ.filter (fun i : Fin n => -(s ω i) ≤ x)).card : ℝ)) ∂μ := by
    intro x
    have hstep : ∀ (f : Ω → ℝ), Measurable f →
        ((μ.map f) (Set.Iic x)).toReal = ∫ ω, (if f ω ≤ x then (1 : ℝ) else 0) ∂μ := by
      intro f hf
      have hA : MeasurableSet {ω : Ω | f ω ≤ x} := measurableSet_Iic.preimage hf
      rw [Measure.map_apply hf measurableSet_Iic]
      rw [show f ⁻¹' Set.Iic x = {ω : Ω | f ω ≤ x} from rfl, ← hind _ hA]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => by simp [Set.indicator]))
    have hint_if : ∀ (f : Ω → ℝ), Measurable f →
        Integrable (fun ω => (if f ω ≤ x then (1 : ℝ) else 0)) μ := by
      intro f hf
      have hA : MeasurableSet {ω : Ω | f ω ≤ x} := measurableSet_Iic.preimage hf
      have hm : Measurable fun ω => (if f ω ≤ x then (1 : ℝ) else 0) :=
        Measurable.ite hA measurable_const measurable_const
      refine Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun ω => ?_))
      split_ifs <;> simp
    have htoReal_sum : (ρ (Set.Iic x)).toReal
        = ∑ i : Fin n, (∫ ω, (if s ω i ≤ x then (1 : ℝ) else 0) ∂μ
            + ∫ ω, (if -(s ω i) ≤ x then (1 : ℝ) else 0) ∂μ) := by
      have hne : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          ((μ.map (fun ω => s ω i)) (Set.Iic x) + (μ.map (fun ω => -(s ω i))) (Set.Iic x)) ≠ ⊤ := by
        intro i _
        exact ENNReal.add_ne_top.mpr ⟨hmap_ne_top _ (hs i) _, hmap_ne_top _ (hs i).neg _⟩
      rw [hρ_apply, ENNReal.toReal_sum hne]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ENNReal.toReal_add (hmap_ne_top _ (hs i) _) (hmap_ne_top _ (hs i).neg _),
        hstep _ (hs i), hstep _ (hs i).neg]
    have hcardfun : (fun ω : Ω => (((Finset.univ.filter (fun i : Fin n => s ω i ≤ x)).card : ℝ)
          + ((Finset.univ.filter (fun i : Fin n => -(s ω i) ≤ x)).card : ℝ)))
        = fun ω : Ω => ∑ i : Fin n,
            ((if s ω i ≤ x then (1 : ℝ) else 0) + (if -(s ω i) ≤ x then (1 : ℝ) else 0)) := by
      funext ω
      rw [Finset.natCast_card_filter, Finset.natCast_card_filter, Finset.sum_add_distrib]
    have hrhs : ∫ ω, (2 * (n : ℝ))⁻¹ *
        (((Finset.univ.filter (fun i : Fin n => s ω i ≤ x)).card : ℝ) +
          ((Finset.univ.filter (fun i : Fin n => -(s ω i) ≤ x)).card : ℝ)) ∂μ
        = (2 * (n : ℝ))⁻¹ * ∑ i : Fin n, (∫ ω, (if s ω i ≤ x then (1 : ℝ) else 0) ∂μ
            + ∫ ω, (if -(s ω i) ≤ x then (1 : ℝ) else 0) ∂μ) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [hcardfun, MeasureTheory.integral_finset_sum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [MeasureTheory.integral_add (hint_if _ (hs i)) (hint_if _ (hs i).neg)]
      · intro i _
        exact (hint_if _ (hs i)).add (hint_if _ (hs i).neg)
    have htoReal_ν : (ν (Set.Iic x)).toReal = (2 * (n : ℝ))⁻¹ * (ρ (Set.Iic x)).toReal := by
      rw [hν, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc_nonneg]
    rw [htoReal_ν, htoReal_sum]
    exact hrhs.symm
  have hν_eq : nuA = ν := by
    haveI : IsFiniteMeasure nuA := hnuA
    refine Measure.ext_of_Iic nuA ν (fun x => ?_)
    rw [← ENNReal.ofReal_toReal (measure_ne_top nuA (Set.Iic x)), hcdf x, ← hν_cdf x,
      ENNReal.ofReal_toReal (measure_ne_top ν (Set.Iic x))]
  have hg_meas : Measurable fun x : ℝ => ((x : ℂ) - z)⁻¹ :=
    (Complex.continuous_ofReal.measurable.sub measurable_const).inv
  have hg_bound : ∀ x : ℝ, ‖((x : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := by
    intro x
    have hb : z.im ≤ ‖(x : ℂ) - z‖ := by
      have h := Complex.abs_im_le_norm ((x : ℂ) - z)
      rwa [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at h
    calc ‖((x : ℂ) - z)⁻¹‖ = (‖(x : ℂ) - z‖)⁻¹ := norm_inv ((x : ℂ) - z)
      _ ≤ z.im⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div]
          exact one_div_le_one_div_of_le hz hb
  have hg_int : ∀ (ν' : Measure ℝ), IsFiniteMeasure ν' →
      Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) ν' := by
    intro ν' hν'
    haveI := hν'
    exact Integrable.of_bound hg_meas.aestronglyMeasurable (z.im⁻¹) (Filter.Eventually.of_forall hg_bound)
  have hρ_int : ∫ x, ((x : ℂ) - z)⁻¹ ∂ρ
      = ∫ ω, (∑ i : Fin n, (((s ω i : ℂ) - z)⁻¹ + ((↑(-(s ω i)) : ℂ) - z)⁻¹)) ∂μ := by
    have hA : ∀ (I : Finset (Fin n)),
        ∫ x, ((x : ℂ) - z)⁻¹ ∂(∑ i ∈ I, (μ.map (fun ω => s ω i) + μ.map (fun ω => -(s ω i))))
        = ∑ i ∈ I, (∫ x, ((x : ℂ) - z)⁻¹ ∂(μ.map (fun ω => s ω i))
            + ∫ x, ((x : ℂ) - z)⁻¹ ∂(μ.map (fun ω => -(s ω i)))) := by
      intro I
      induction I using Finset.induction_on with
      | empty =>
          rw [Finset.sum_empty, Finset.sum_empty]
          simp
      | insert a t ha ih =>
          haveI i1 : IsFiniteMeasure (μ.map (fun ω => s ω a) + μ.map (fun ω => -(s ω a))) := by
            refine ⟨lt_top_iff_ne_top.mpr ?_⟩
            rw [Measure.add_apply, hmap_univ _ (hs a), hmap_univ _ (hs a).neg]
            norm_num
          haveI i2 : IsFiniteMeasure (∑ i ∈ t, (μ.map (fun ω => s ω i) + μ.map (fun ω => -(s ω i)))) :=
            ⟨lt_top_iff_ne_top.mpr (hsum_ne_top t)⟩
          rw [Finset.sum_insert ha, MeasureTheory.integral_add_measure (hg_int _ i1) (hg_int _ i2)]
          rw [MeasureTheory.integral_add_measure (hg_int _ (hpush a)) (hg_int _ (hpush' a)), ih,
            Finset.sum_insert ha]
    have hB : ∑ i : Fin n, (∫ x, ((x : ℂ) - z)⁻¹ ∂(μ.map (fun ω => s ω i))
          + ∫ x, ((x : ℂ) - z)⁻¹ ∂(μ.map (fun ω => -(s ω i))))
        = ∫ ω, (∑ i : Fin n, (((s ω i : ℂ) - z)⁻¹ + ((↑(-(s ω i)) : ℂ) - z)⁻¹)) ∂μ := by
      have hmap1 : ∀ i : Fin n,
          ∫ x, ((x : ℂ) - z)⁻¹ ∂(μ.map (fun ω => s ω i)) = ∫ ω, ((s ω i : ℂ) - z)⁻¹ ∂μ := by
        intro i
        exact MeasureTheory.integral_map (hs i).aemeasurable hg_meas.aestronglyMeasurable
      have hmap2 : ∀ i : Fin n,
          ∫ x, ((x : ℂ) - z)⁻¹ ∂(μ.map (fun ω => -(s ω i))) = ∫ ω, ((↑(-(s ω i)) : ℂ) - z)⁻¹ ∂μ := by
        intro i
        exact MeasureTheory.integral_map (hs i).neg.aemeasurable hg_meas.aestronglyMeasurable
      have hint1 : ∀ i : Fin n, Integrable (fun ω => ((s ω i : ℂ) - z)⁻¹) μ := by
        intro i
        exact Integrable.of_bound ((hg_meas.comp (hs i)).aestronglyMeasurable) (z.im⁻¹)
          (Filter.Eventually.of_forall (fun ω => hg_bound (s ω i)))
      have hint2 : ∀ i : Fin n, Integrable (fun ω => ((↑(-(s ω i)) : ℂ) - z)⁻¹) μ := by
        intro i
        exact Integrable.of_bound ((hg_meas.comp (hs i).neg).aestronglyMeasurable) (z.im⁻¹)
          (Filter.Eventually.of_forall (fun ω => hg_bound (-(s ω i))))
      have hmid : (∑ i : Fin n, (∫ x, ((x : ℂ) - z)⁻¹ ∂(μ.map (fun ω => s ω i))
            + ∫ x, ((x : ℂ) - z)⁻¹ ∂(μ.map (fun ω => -(s ω i)))))
          = ∑ i : Fin n, (∫ ω, ((s ω i : ℂ) - z)⁻¹ ∂μ
            + ∫ ω, ((↑(-(s ω i)) : ℂ) - z)⁻¹ ∂μ) :=
        Finset.sum_congr rfl (fun i _ => by rw [hmap1 i, hmap2 i])
      rw [hmid, MeasureTheory.integral_finset_sum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [MeasureTheory.integral_add (hint1 i) (hint2 i)]
      · intro i _
        exact (hint1 i).add (hint2 i)
    rw [hρ]
    exact Eq.trans (hA Finset.univ) hB
  have hν_int : ∫ x, ((x : ℂ) - z)⁻¹ ∂ν = ((2 * (n : ℝ))⁻¹) • ∫ x, ((x : ℂ) - z)⁻¹ ∂ρ := by
    rw [hν, MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hc_nonneg]
  have hsmul : ∀ w : ℂ, ((2 * (n : ℝ))⁻¹) • w = (((2 * (n : ℝ))⁻¹ : ℝ) : ℂ) * w := by
    intro w
    rw [Algebra.smul_def]
    rfl
  rw [hν_eq, hν_int, hρ_int, hsmul, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp only [symStieltjesSvals]
  push_cast
  rfl
  /- @proof-region region.target-node.session.13e988237816b6e6 end -/

end Statlib.Imported

