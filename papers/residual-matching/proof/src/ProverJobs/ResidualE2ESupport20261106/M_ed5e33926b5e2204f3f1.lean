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
theorem statopia_math_node_2968987631_02201a7a : ∀ (m n : ℕ) (hn : 1 ≤ n) (p : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hmeas : ∀ k : Fin n, Measurable fun ω => svals (maskedScaled p (Xi ω) (Mask ω)) k),
    ∃ nuA : Measure ℝ, IsFiniteMeasure nuA ∧ nuA Set.univ = 1 ∧
      ∀ x : ℝ, (nuA (Set.Iic x)).toReal =
        ∫ ω, (2 * (n : ℝ))⁻¹ *
          (((Finset.univ.filter
              (fun i : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ) +
            ((Finset.univ.filter
              (fun i : Fin n => -(svals (maskedScaled p (Xi ω) (Mask ω)) i) ≤ x)).card : ℝ)) ∂μ := by
  /- @proof-region region.target-node.session.863beccf2557eb9b begin -/
  classical
  intro m n hn p Ω _ μ _ Xi Mask hmeas
  set s : Ω → Fin n → ℝ := fun ω => svals (maskedScaled p (Xi ω) (Mask ω)) with hs
  have hsmeas : ∀ i : Fin n, Measurable fun ω => s ω i := by
    intro i
    simpa [hs] using hmeas i
  set c : ENNReal := ENNReal.ofReal ((2 * (n : ℝ))⁻¹) with hc
  have hc_ne_top : c ≠ ⊤ := by
    rw [hc]; exact ENNReal.ofReal_ne_top
  have hc_toReal : c.toReal = (2 * (n : ℝ))⁻¹ := by
    rw [hc, ENNReal.toReal_ofReal (by positivity)]
  set nuA : Measure ℝ :=
    c • ∑ i : Fin n, ((μ.map (fun ω => s ω i)) + (μ.map (fun ω => -(s ω i)))) with hnuA
  have huniv_term : ∀ i : Fin n,
      (μ.map (fun ω => s ω i)) Set.univ + (μ.map (fun ω => -(s ω i))) Set.univ = 2 := by
    intro i
    rw [Measure.map_apply (hsmeas i) MeasurableSet.univ,
      Measure.map_apply (hsmeas i).neg MeasurableSet.univ]
    simp
    first | norm_num | ring
  have h_univ : nuA Set.univ = 1 := by
    rw [hnuA, Measure.smul_apply, Measure.finset_sum_apply]
    simp only [Measure.add_apply, huniv_term, smul_eq_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnpos : (0:ℝ) < 2 * (n:ℝ) := by
      have h1 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      linarith
    have hncast : ((n : ENNReal) * 2) = ENNReal.ofReal (2 * (n:ℝ)) := by
      have h1 : ((n : ENNReal)) = ENNReal.ofReal (n:ℝ) := (ENNReal.ofReal_natCast n).symm
      have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := (ENNReal.ofReal_natCast 2).symm
      rw [h1, h2, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (n:ℝ))]
      congr 1
      ring
    rw [hc, hncast, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hnpos)),
      inv_mul_cancel₀ (ne_of_gt hnpos), ENNReal.ofReal_one]
  refine ⟨nuA, ?_, h_univ, ?_⟩
  · exact ⟨by rw [h_univ]; exact ENNReal.one_lt_top⟩
  · intro x
    set S : ENNReal := ∑ i : Fin n,
      ((μ.map (fun ω => s ω i)) (Set.Iic x) + (μ.map (fun ω => -(s ω i))) (Set.Iic x)) with hS
    have hval : nuA (Set.Iic x) = c * S := by
      rw [hnuA, hS, Measure.smul_apply, Measure.finset_sum_apply]
      simp only [Measure.add_apply, smul_eq_mul]
    have hbounded : ∀ (f : Ω → ℝ), Measurable f → (μ.map f) (Set.Iic x) ≤ 1 := by
      intro f hf
      have h1 : (μ.map f) Set.univ = 1 := by
        rw [Measure.map_apply hf MeasurableSet.univ]
        simp
      calc (μ.map f) (Set.Iic x) ≤ (μ.map f) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := h1
    have hF_ne : ∀ i : Fin n, (μ.map (fun ω => s ω i)) (Set.Iic x) ≠ ⊤ :=
      fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (hbounded _ (hsmeas i))
    have hG_ne : ∀ i : Fin n, (μ.map (fun ω => -(s ω i))) (Set.Iic x) ≠ ⊤ :=
      fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (hbounded _ (hsmeas i).neg)
    have hS_lt : S < ⊤ := by
      rw [hS]
      refine ENNReal.sum_lt_top.mpr (fun i _ => ?_)
      exact ENNReal.add_lt_top.mpr
        ⟨lt_top_iff_ne_top.mpr (hF_ne i), lt_top_iff_ne_top.mpr (hG_ne i)⟩
    have hS_toReal : S.toReal = ∑ i : Fin n,
        (((μ.map (fun ω => s ω i)) (Set.Iic x)).toReal +
          ((μ.map (fun ω => -(s ω i))) (Set.Iic x)).toReal) := by
      rw [hS, ENNReal.toReal_sum (fun i _ => ENNReal.add_ne_top.mpr ⟨hF_ne i, hG_ne i⟩)]
      exact Finset.sum_congr rfl (fun i _ => ENNReal.toReal_add (hF_ne i) (hG_ne i))
    have key : ∀ (f : Ω → ℝ), Measurable f →
        ((μ.map f) (Set.Iic x)).toReal = ∫ ω, (if f ω ≤ x then (1:ℝ) else 0) ∂μ := by
      intro f hf
      have hmeas : MeasurableSet (f ⁻¹' Set.Iic x) := measurableSet_Iic.preimage hf
      calc ((μ.map f) (Set.Iic x)).toReal
          = (μ (f ⁻¹' Set.Iic x)).toReal := by rw [Measure.map_apply hf measurableSet_Iic]
        _ = μ.real (f ⁻¹' Set.Iic x) := rfl
        _ = ∫ ω, (f ⁻¹' Set.Iic x).indicator (fun _ => (1:ℝ)) ω ∂μ := by
              rw [← MeasureTheory.setIntegral_one_eq_measureReal (μ := μ),
                MeasureTheory.integral_indicator hmeas]
        _ = ∫ ω, (if f ω ≤ x then (1:ℝ) else 0) ∂μ := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with ω
              simp [Set.indicator]
    have hmain : (nuA (Set.Iic x)).toReal = c.toReal * ∑ i : Fin n,
        (((μ.map (fun ω => s ω i)) (Set.Iic x)).toReal +
          ((μ.map (fun ω => -(s ω i))) (Set.Iic x)).toReal) := by
      rw [hval, ENNReal.toReal_mul, hS_toReal]
    have hInt1 : ∀ i : Fin n, Integrable (fun ω => (if s ω i ≤ x then (1:ℝ) else 0)) μ := by
      intro i
      have hm : Measurable fun ω => (if s ω i ≤ x then (1:ℝ) else 0) :=
        Measurable.ite (measurableSet_le (hsmeas i) measurable_const)
          measurable_const measurable_const
      refine MeasureTheory.Integrable.of_bound hm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun ω => ?_))
      split <;> simp
    have hInt2 : ∀ i : Fin n, Integrable (fun ω => (if -(s ω i) ≤ x then (1:ℝ) else 0)) μ := by
      intro i
      have hm : Measurable fun ω => (if -(s ω i) ≤ x then (1:ℝ) else 0) :=
        Measurable.ite (measurableSet_le (hsmeas i).neg measurable_const)
          measurable_const measurable_const
      refine MeasureTheory.Integrable.of_bound hm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun ω => ?_))
      split <;> simp
    have hsum_eq : ∑ i : Fin n, ((∫ ω, (if s ω i ≤ x then (1:ℝ) else 0) ∂μ) +
          (∫ ω, (if -(s ω i) ≤ x then (1:ℝ) else 0) ∂μ))
        = ∫ ω, ∑ i : Fin n, ((fun ω => (if s ω i ≤ x then (1:ℝ) else 0)) +
            (fun ω => (if -(s ω i) ≤ x then (1:ℝ) else 0))) ω ∂μ := by
      have hsumI : ∫ ω, ∑ i : Fin n, ((fun ω => (if s ω i ≤ x then (1:ℝ) else 0)) +
            (fun ω => (if -(s ω i) ≤ x then (1:ℝ) else 0))) ω ∂μ
          = ∑ i : Fin n, ∫ ω, ((fun ω => (if s ω i ≤ x then (1:ℝ) else 0)) +
            (fun ω => (if -(s ω i) ≤ x then (1:ℝ) else 0))) ω ∂μ :=
        MeasureTheory.integral_finset_sum Finset.univ (fun i _ => (hInt1 i).add (hInt2 i))
      rw [hsumI]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hconv : ∫ ω, ((fun ω => (if s ω i ≤ x then (1:ℝ) else 0)) +
            (fun ω => (if -(s ω i) ≤ x then (1:ℝ) else 0))) ω ∂μ
          = ∫ ω, ((if s ω i ≤ x then (1:ℝ) else 0) + (if -(s ω i) ≤ x then (1:ℝ) else 0)) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with ω
        simp
      rw [hconv, MeasureTheory.integral_add (hInt1 i) (hInt2 i)]
    have hcard1 : ∀ ω : Ω, (∑ i : Fin n, (if s ω i ≤ x then (1:ℝ) else 0)) =
        ((Finset.univ.filter (fun i : Fin n => s ω i ≤ x)).card : ℝ) := by
      intro ω
      rw [Finset.card_filter]
      push_cast
      rfl
    have hcard2 : ∀ ω : Ω, (∑ i : Fin n, (if -(s ω i) ≤ x then (1:ℝ) else 0)) =
        ((Finset.univ.filter (fun i : Fin n => -(s ω i) ≤ x)).card : ℝ) := by
      intro ω
      rw [Finset.card_filter]
      push_cast
      rfl
    have hpoint : ∀ ω : Ω, (∑ i : Fin n, ((fun ω => (if s ω i ≤ x then (1:ℝ) else 0)) +
          (fun ω => (if -(s ω i) ≤ x then (1:ℝ) else 0))) ω)
        = ((Finset.univ.filter (fun i : Fin n => s ω i ≤ x)).card : ℝ) +
          ((Finset.univ.filter (fun i : Fin n => -(s ω i) ≤ x)).card : ℝ) := by
      intro ω
      simp [Finset.sum_add_distrib, hcard1 ω, hcard2 ω]
    calc (nuA (Set.Iic x)).toReal
        = c.toReal * ∑ i : Fin n,
            (((μ.map (fun ω => s ω i)) (Set.Iic x)).toReal +
              ((μ.map (fun ω => -(s ω i))) (Set.Iic x)).toReal) := hmain
      _ = c.toReal * ∑ i : Fin n, ((∫ ω, (if s ω i ≤ x then (1:ℝ) else 0) ∂μ) +
              (∫ ω, (if -(s ω i) ≤ x then (1:ℝ) else 0) ∂μ)) := by
            congr 1
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [key (fun ω => s ω i) (hsmeas i), key (fun ω => -(s ω i)) (hsmeas i).neg]
      _ = c.toReal * ∫ ω, ∑ i : Fin n, ((fun ω => (if s ω i ≤ x then (1:ℝ) else 0)) +
              (fun ω => (if -(s ω i) ≤ x then (1:ℝ) else 0))) ω ∂μ := by
            rw [hsum_eq]
      _ = c.toReal * ∫ ω, (((Finset.univ.filter (fun i : Fin n => s ω i ≤ x)).card : ℝ) +
              ((Finset.univ.filter (fun i : Fin n => -(s ω i) ≤ x)).card : ℝ)) ∂μ := by
            rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
      _ = ∫ ω, (2 * (n : ℝ))⁻¹ * (((Finset.univ.filter
              (fun i : Fin n => s ω i ≤ x)).card : ℝ) +
            ((Finset.univ.filter
              (fun i : Fin n => -(s ω i) ≤ x)).card : ℝ)) ∂μ := by
            rw [hc_toReal, MeasureTheory.integral_const_mul]
  /- @proof-region region.target-node.session.863beccf2557eb9b end -/

end Statlib.Imported

