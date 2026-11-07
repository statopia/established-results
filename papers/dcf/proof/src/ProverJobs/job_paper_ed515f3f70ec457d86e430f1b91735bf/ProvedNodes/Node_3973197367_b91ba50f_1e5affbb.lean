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
theorem statopia_math_node_3973197367_b91ba50f : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m p : ℕ) (hlogp : 0 < Real.log (p : ℝ))
    (d : ℝ) (hd : d ≠ 0) (muY : Fin p → ℝ)
    (Y G : Fin m → Ω → Fin p → ℝ)
    (hYm : ∀ i : Fin m, Measurable (Y i)) (hGm : ∀ i : Fin m, Measurable (G i))
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
    (phi phi2 : ℝ) (hphi : 1 ≤ phi) (hphi2 : phi ≤ phi2),
    Mstar P m d muY Y G phi ≤ Mstar P m d muY Y G phi2 := by
  /- @proof-region region.target-node.session.d6da95209c250fb6 begin -/
  intro Ω _ P _ m p hlogp d hd muY Y G hYm hGm hY3 hG3 phi phi2 hphi hphi2
  have habsd : 0 < |d| := abs_pos.mpr hd
  have hphi1 : 0 < phi := lt_of_lt_of_le zero_lt_one hphi
  have hden1 : 0 < 4 * |d| * phi * Real.log (p : ℝ) := by
    have h4 : (0 : ℝ) < 4 := by norm_num
    exact mul_pos (mul_pos (mul_pos h4 habsd) hphi1) hlogp
  have hlevel : Real.sqrt (m : ℝ) / (4 * |d| * phi2 * Real.log (p : ℝ))
      ≤ Real.sqrt (m : ℝ) / (4 * |d| * phi * Real.log (p : ℝ)) := by
    have h4 : (0 : ℝ) < 4 := by norm_num
    have hC : (0 : ℝ) ≤ 4 * |d| * Real.log (p : ℝ) := le_of_lt (mul_pos (mul_pos h4 habsd) hlogp)
    have hcoef : 4 * |d| * Real.log (p : ℝ) * phi ≤ 4 * |d| * Real.log (p : ℝ) * phi2 :=
      mul_le_mul_of_nonneg_left hphi2 hC
    have hdenle : 4 * |d| * phi * Real.log (p : ℝ) ≤ 4 * |d| * phi2 * Real.log (p : ℝ) := by
      nlinarith [hcoef]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg (m : ℝ)) hden1 hdenle
  have hMaxMeas : ∀ (Z : Fin m → Ω → Fin p → ℝ), (∀ i : Fin m, Measurable (Z i)) →
      ∀ i : Fin m, Measurable (fun ω => maxAbs (fun j => Z i ω j - muY j)) := by
    intro Z hZ i
    have hc : ∀ j : Fin p, Measurable (fun ω => |Z i ω j - muY j|) := fun j =>
      continuous_abs.measurable.comp (((measurable_pi_apply j).comp (hZ i)).sub measurable_const)
    exact Measurable.iSup (f := fun j : Fin p => fun ω => |Z i ω j - muY j|) hc
  have hMaxInt : ∀ (Z : Fin m → Ω → Fin p → ℝ), (∀ i : Fin m, Measurable (Z i)) →
      (∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Z i ω j - muY j| ^ 3) P) →
      ∀ i : Fin m, Integrable (fun ω => (maxAbs (fun j => Z i ω j - muY j)) ^ 3) P := by
    intro Z hZ hZ3 i
    have hp : 0 < p := by
      rcases Nat.eq_zero_or_pos p with h | h
      · exfalso
        rw [h] at hlogp
        simpa using hlogp
      · exact h
    haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    have hmono3 : Monotone (fun t : ℝ => t ^ 3) := by
      intro a b hab
      have key : (0 : ℝ) ≤ a ^ 2 + a * b + b ^ 2 := by
        nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) key]
    have hsum : Integrable (fun ω => ∑ j : Fin p, |Z i ω j - muY j| ^ 3) P := by
      have h := integrable_finset_sum (s := Finset.univ)
        (f := fun j : Fin p => fun ω => |Z i ω j - muY j| ^ 3) (fun j _ => hZ3 i j)
      simpa using h
    refine MeasureTheory.Integrable.mono' hsum ?_ ?_
    · exact ((continuous_pow 3).measurable.comp (hMaxMeas Z hZ i)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      have hT : (maxAbs (fun j => Z i ω j - muY j)) ^ 3
          = ⨆ j : Fin p, |Z i ω j - muY j| ^ 3 :=
        Monotone.map_ciSup_of_continuousAt (f := fun t : ℝ => t ^ 3)
          (g := fun j : Fin p => |Z i ω j - muY j|) (by
            have hcont : Continuous fun t : ℝ => t ^ 3 := continuous_pow 3
            exact hcont.continuousAt) hmono3 (Set.Finite.bddAbove (Set.finite_range _))
      have hnn : (0 : ℝ) ≤ (maxAbs (fun j => Z i ω j - muY j)) ^ 3 :=
        pow_nonneg (Real.iSup_nonneg (f := fun j : Fin p => |Z i ω j - muY j|) (fun j => abs_nonneg _)) 3
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, hT]
      refine ciSup_le (fun j => ?_)
      simpa using Finset.single_le_sum (f := fun k : Fin p => |Z i ω k - muY k| ^ 3)
        (fun k _ => pow_nonneg (abs_nonneg _) 3) (Finset.mem_univ j)
  have key : ∀ (Z : Fin m → Ω → Fin p → ℝ), (∀ i : Fin m, Measurable (Z i)) →
      (∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Z i ω j - muY j| ^ 3) P) →
      ∀ (l1 l2 : ℝ), l2 ≤ l1 →
      (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, Set.indicator
          {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l1}
          (fun ω' => (maxAbs (fun j => Z i ω' j - muY j)) ^ 3) ω ∂P
        ≤ (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, Set.indicator
          {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l2}
          (fun ω' => (maxAbs (fun j => Z i ω' j - muY j)) ^ 3) ω ∂P := by
    intro Z hZm hZ3 l1 l2 hl
    have hrm : (0 : ℝ) ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg m)
    refine mul_le_mul_of_nonneg_left ?_ hrm
    refine Finset.sum_le_sum ?_
    intro i _
    have hmeas : Measurable (fun ω => maxAbs (fun j => Z i ω j - muY j)) := hMaxMeas Z hZm i
    have hint : Integrable (fun ω => (maxAbs (fun j => Z i ω j - muY j)) ^ 3) P := hMaxInt Z hZm hZ3 i
    classical
    have hstep : ∀ (S : Set Ω) (g : Ω → ℝ) (a : Ω), Set.indicator S g a = if a ∈ S then g a else 0 :=
      fun S g a => rfl
    have hnn : ∀ ω : Ω, (0 : ℝ) ≤ (maxAbs (fun j => Z i ω j - muY j)) ^ 3 :=
      fun ω => pow_nonneg (Real.iSup_nonneg (f := fun j : Fin p => |Z i ω j - muY j|) (fun j => abs_nonneg _)) 3
    have hB : MeasurableSet {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l2} := hmeas measurableSet_Ioi
    refine MeasureTheory.integral_mono_of_nonneg
      (f := Set.indicator {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l1}
        (fun ω' => (maxAbs (fun j => Z i ω' j - muY j)) ^ 3))
      (g := Set.indicator {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l2}
        (fun ω' => (maxAbs (fun j => Z i ω' j - muY j)) ^ 3))
      ?_ (MeasureTheory.Integrable.indicator hint hB) ?_
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [hstep]
      by_cases h1 : maxAbs (fun j => Z i ω j - muY j) > l1
      · rw [if_pos (show ω ∈ {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l1} from h1)]
        exact hnn ω
      · rw [if_neg (show ω ∉ {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l1} from h1)]
        exact le_refl 0
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [hstep, hstep]
      by_cases h1 : maxAbs (fun j => Z i ω j - muY j) > l1
      · have h2 : maxAbs (fun j => Z i ω j - muY j) > l2 := lt_of_le_of_lt hl h1
        rw [if_pos (show ω ∈ {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l1} from h1),
          if_pos (show ω ∈ {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l2} from h2)]
      · rw [if_neg (show ω ∉ {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l1} from h1)]
        by_cases h2 : maxAbs (fun j => Z i ω j - muY j) > l2
        · rw [if_pos (show ω ∈ {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l2} from h2)]
          exact hnn ω
        · rw [if_neg (show ω ∉ {ω' : Ω | maxAbs (fun j => Z i ω' j - muY j) > l2} from h2)]
  have hne : ¬ (d = 0) := hd
  have hY' : MY P m d muY Y phi ≤ MY P m d muY Y phi2 := by
    unfold MY
    rw [if_neg hne, if_neg hne]
    exact key Y hYm hY3 _ _ hlevel
  have hG' : MG P m d muY G phi ≤ MG P m d muY G phi2 := by
    unfold MG
    rw [if_neg hne, if_neg hne]
    exact key G hGm hG3 _ _ hlevel
  simpa only [Mstar] using add_le_add hY' hG'
  /- @proof-region region.target-node.session.d6da95209c250fb6 end -/

end

end Statlib.Imported

