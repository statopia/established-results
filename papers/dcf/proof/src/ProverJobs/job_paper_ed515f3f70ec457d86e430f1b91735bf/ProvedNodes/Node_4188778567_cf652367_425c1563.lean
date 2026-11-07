import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_4188778567_cf652367 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n p : ℕ) (hn : 0 < n) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
    (muX : Fin p → ℝ) (X : Fin n → Ω → Fin p → ℝ) (F : Fin n → Ω → Fin p → ℝ)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (phi phi2 : ℝ) (hphi_ge : 1 ≤ phi) (hphi_le : phi ≤ phi2),
    MX P n muX X phi ≤ MX P n muX X phi2 ∧
    MF P n muX F phi ≤ MF P n muX F phi2 ∧
    Mn P n muX X F phi ≤ Mn P n muX X F phi2 := by
  /- @proof-region region.target-node.session.1e903cc7bcf4bade begin -/
  intro Ω _ P _ n p hn hp hlogp muX X F hXm hFm hX3 hF3 phi phi2 hphi_ge hphi_le
  have hcoef : (0:ℝ) ≤ (n:ℝ)⁻¹ := by positivity
  have hphi_pos : (0:ℝ) < phi := lt_of_lt_of_le zero_lt_one hphi_ge
  have hphi2_pos : (0:ℝ) < phi2 := lt_of_lt_of_le hphi_pos hphi_le
  have hmn : ∀ (x : Fin p → ℝ), 0 ≤ maxAbs x := by
    intro x
    have hbd : BddAbove (Set.range (fun j : Fin p => |x j|)) :=
      Finite.bddAbove_range (fun j : Fin p => |x j|)
    exact le_trans (abs_nonneg (x ⟨0, hp⟩)) (le_ciSup hbd ⟨0, hp⟩)
  have ht : Real.sqrt (n:ℝ) / (4 * phi2 * Real.log (p:ℝ)) ≤ Real.sqrt (n:ℝ) / (4 * phi * Real.log (p:ℝ)) := by
    have hden : (0:ℝ) < 4 * phi * Real.log (p:ℝ) := mul_pos (mul_pos (by norm_num) hphi_pos) hlogp
    have hml : phi * Real.log (p:ℝ) ≤ phi2 * Real.log (p:ℝ) :=
      mul_le_mul_of_nonneg_right hphi_le hlogp.le
    have hle : 4 * phi * Real.log (p:ℝ) ≤ 4 * phi2 * Real.log (p:ℝ) := by nlinarith [hml]
    have hinv : (4 * phi2 * Real.log (p:ℝ))⁻¹ ≤ (4 * phi * Real.log (p:ℝ))⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hden hle
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg _)
  have key : ∀ (Z : Fin n → Ω → Fin p → ℝ),
      (∀ i : Fin n, Measurable (Z i)) →
      (∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |Z i ω j - muX j| ^ 3) P) →
      (∑ i : Fin n, ∫ ω, Set.indicator
          {ω' : Ω | maxAbs (fun j => Z i ω' j - muX j) > Real.sqrt (n:ℝ) / (4 * phi * Real.log (p:ℝ))}
          (fun ω' => (maxAbs (fun j => Z i ω' j - muX j)) ^ 3) ω ∂P)
      ≤ (∑ i : Fin n, ∫ ω, Set.indicator
          {ω' : Ω | maxAbs (fun j => Z i ω' j - muX j) > Real.sqrt (n:ℝ) / (4 * phi2 * Real.log (p:ℝ))}
          (fun ω' => (maxAbs (fun j => Z i ω' j - muX j)) ^ 3) ω ∂P) := by
    intro Z hZm hZ3
    have hmeas : ∀ i : Fin n, Measurable (fun ω => maxAbs (fun j => Z i ω j - muX j)) := by
      intro i
      haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
      have hfun : (fun ω => maxAbs (fun j => Z i ω j - muX j))
          = Finset.univ.sup' Finset.univ_nonempty (fun j => fun ω => |Z i ω j - muX j|) := by
        funext ω
        rw [Finset.sup'_apply, Finset.sup'_univ_eq_ciSup]
        rfl
      rw [hfun]
      exact Finset.measurable_sup' Finset.univ_nonempty
        (fun j _ => (((measurable_pi_iff.mp (hZm i)) j).sub measurable_const).abs)
    have hint3 : ∀ i : Fin n, Integrable (fun ω => (maxAbs (fun j => Z i ω j - muX j)) ^ 3) P := by
      intro i
      have hsum_int : Integrable (fun ω => ∑ j : Fin p, |Z i ω j - muX j| ^ 3) P := by
        have h := MeasureTheory.integrable_finset_sum (Finset.univ : Finset (Fin p))
          (f := fun j ω => |Z i ω j - muX j| ^ 3) (fun j _ => hZ3 i j)
        simpa using h
      have hbd : ∀ ω, (maxAbs (fun j => Z i ω j - muX j)) ^ 3 ≤ ∑ j : Fin p, |Z i ω j - muX j| ^ 3 := by
        intro ω
        haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
        have hmax : maxAbs (fun j => Z i ω j - muX j)
            = Finset.univ.sup' Finset.univ_nonempty (fun j => |Z i ω j - muX j|) := by
          rw [Finset.sup'_univ_eq_ciSup]; rfl
        obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => |Z i ω j - muX j|)
        rw [hmax, hj0]
        simpa using Finset.single_le_sum (f := fun j => |Z i ω j - muX j| ^ 3)
          (fun j _ => by positivity) (Finset.mem_univ j0)
      have hcube_ae : AEStronglyMeasurable (fun ω => (maxAbs (fun j => Z i ω j - muX j)) ^ 3) P := by
        have h1 : AEStronglyMeasurable (fun ω => maxAbs (fun j => Z i ω j - muX j)) P :=
          hmeas i |>.aestronglyMeasurable
        exact h1.pow 3
      refine hsum_int.mono' hcube_ae ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hmn (fun j => Z i ω j - muX j)) 3)]
      exact hbd ω
    have ind_zero : ∀ (s : Set Ω) (g : Ω → ℝ) (a : Ω), a ∉ s → Set.indicator s g a = 0 := by
      intro s g a ha
      simp [Set.indicator, ha]
    have hnn : ∀ (s : Set Ω) (f : Ω → ℝ), (∀ x, 0 ≤ f x) → ∀ a, 0 ≤ Set.indicator s f a := by
      intro s f hf a
      by_cases ha : a ∈ s
      · rw [Set.indicator_of_mem ha]; exact hf a
      · rw [ind_zero s f a ha]
    have hstep : ∀ (s t : Set Ω) (f : Ω → ℝ), (∀ x, 0 ≤ f x) → s ⊆ t →
        ∀ a, Set.indicator s f a ≤ Set.indicator t f a := by
      intro s t f hf hst a
      by_cases ha : a ∈ s
      · have hat : a ∈ t := hst ha
        rw [Set.indicator_of_mem ha, Set.indicator_of_mem hat]
      · by_cases hat : a ∈ t
        · rw [ind_zero s f a ha, Set.indicator_of_mem hat]
          exact hf a
        · rw [ind_zero s f a ha, ind_zero t f a hat]
    apply Finset.sum_le_sum
    intro i _
    have hnn_i : ∀ a, 0 ≤ (fun ω' => (maxAbs (fun j => Z i ω' j - muX j)) ^ 3) a :=
      fun x => pow_nonneg (hmn (fun j => Z i x j - muX j)) 3
    have hsub : {ω' : Ω | maxAbs (fun j => Z i ω' j - muX j) > Real.sqrt (n:ℝ) / (4 * phi * Real.log (p:ℝ))}
        ⊆ {ω' : Ω | maxAbs (fun j => Z i ω' j - muX j) > Real.sqrt (n:ℝ) / (4 * phi2 * Real.log (p:ℝ))} := by
      intro ω' hω'
      simp only [Set.mem_setOf_eq] at hω' ⊢
      linarith [ht]
    apply MeasureTheory.integral_mono_of_nonneg
    · filter_upwards with ω
      exact hnn _ _ hnn_i ω
    · exact (hint3 i).indicator (hmeas i measurableSet_Ioi)
    · filter_upwards with ω
      exact hstep _ _ _ hnn_i hsub ω
  have hXmx : MX P n muX X phi ≤ MX P n muX X phi2 := by
    simp only [MX]
    exact mul_le_mul_of_nonneg_left (key X hXm hX3) hcoef
  have hFmx : MF P n muX F phi ≤ MF P n muX F phi2 := by
    simp only [MF]
    exact mul_le_mul_of_nonneg_left (key F hFm hF3) hcoef
  exact ⟨hXmx, hFmx, by simp only [Mn]; exact add_le_add hXmx hFmx⟩
  /- @proof-region region.target-node.session.1e903cc7bcf4bade end -/

end

end Statlib.Imported

