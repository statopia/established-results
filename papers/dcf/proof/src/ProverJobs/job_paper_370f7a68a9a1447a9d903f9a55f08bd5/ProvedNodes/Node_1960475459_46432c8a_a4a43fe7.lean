import Lean
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Vocabulary
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Base

namespace PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5

open scoped BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported

noncomputable section
open scoped BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1960475459_46432c8a : ∀ (phi0 : ℝ → ℝ) (hC3 : ContDiff ℝ 3 phi0)
    (hleft : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hright : ∀ z : ℝ, 1 ≤ z → phi0 z = 0),
    ∃ d1 d2 d3 : ℝ,
      0 ≤ d1 ∧ 0 ≤ d2 ∧ 0 ≤ d3 ∧
      (∀ u : ℝ,
        |iteratedDeriv 1 phi0 u| ≤ d1 ∧
        |iteratedDeriv 2 phi0 u| ≤ d2 ∧
        |iteratedDeriv 3 phi0 u| ≤ d3) ∧
      (∀ phi : ℝ, 0 < phi → ContDiff ℝ 3 (fun t : ℝ => phi0 (phi * t))) ∧
      (∀ phi : ℝ, 0 < phi → ∀ t : ℝ,
        |iteratedDeriv 1 (fun s : ℝ => phi0 (phi * s)) t| ≤ phi ^ (1 : ℕ) * d1 ∧
        |iteratedDeriv 2 (fun s : ℝ => phi0 (phi * s)) t| ≤ phi ^ (2 : ℕ) * d2 ∧
        |iteratedDeriv 3 (fun s : ℝ => phi0 (phi * s)) t| ≤ phi ^ (3 : ℕ) * d3) := by
  /- @proof-region region.target-node.session.b2fdb1015b8926fd begin -/
  intro phi0 hC3 hleft hright
  have hconst : ∀ (c : ℝ) (n : ℕ) (u : ℝ), iteratedDeriv (n + 1) (fun _ : ℝ => c) u = 0 := by
    intro c n
    induction n with
    | zero =>
      intro u
      rw [iteratedDeriv_succ, iteratedDeriv_zero]
      simp
    | succ n ih =>
      intro u
      rw [iteratedDeriv_succ]
      have hf : iteratedDeriv (n + 1) (fun _ : ℝ => c) = fun _ => (0 : ℝ) := by
        funext v
        simpa using ih v
      rw [hf]
      simp
  have hzeroL : ∀ (n : ℕ) (u : ℝ), u < 0 → iteratedDeriv (n + 1) phi0 u = 0 := by
    intro n u hu
    have hEqOn : Set.EqOn (iteratedDeriv (n + 1) phi0)
        (iteratedDeriv (n + 1) (fun _ : ℝ => (1 : ℝ))) (Set.Iio (0 : ℝ)) :=
      Set.EqOn.iteratedDeriv_of_isOpen (fun z hz => hleft z (le_of_lt hz)) isOpen_Iio (n + 1)
    rw [hEqOn hu]
    exact hconst 1 n u
  have hzeroR : ∀ (n : ℕ) (u : ℝ), 1 < u → iteratedDeriv (n + 1) phi0 u = 0 := by
    intro n u hu
    have hEqOn : Set.EqOn (iteratedDeriv (n + 1) phi0)
        (iteratedDeriv (n + 1) (fun _ : ℝ => (0 : ℝ))) (Set.Ioi (1 : ℝ)) :=
      Set.EqOn.iteratedDeriv_of_isOpen (fun z hz => hright z (le_of_lt hz)) isOpen_Ioi (n + 1)
    rw [hEqOn hu]
    exact hconst 0 n u
  have mkbound : ∀ (f : ℝ → ℝ), Continuous f →
      (∀ u : ℝ, u < 0 → f u = 0) → (∀ u : ℝ, 1 < u → f u = 0) →
      ∃ d : ℝ, 0 ≤ d ∧ ∀ u : ℝ, |f u| ≤ d := by
    intro f hf hfl hfr
    obtain ⟨x, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (⟨0, by norm_num⟩ : (Set.Icc (0 : ℝ) 1).Nonempty) hf.abs.continuousOn
    refine ⟨|f x|, abs_nonneg _, fun u => ?_⟩
    by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
    · simpa using hmax hu
    · simp only [Set.mem_Icc, not_and_or, not_le] at hu
      rcases hu with hu | hu
      · rw [hfl u hu, abs_zero]
        exact abs_nonneg _
      · rw [hfr u hu, abs_zero]
        exact abs_nonneg _
  have hc1 : Continuous (iteratedDeriv 1 phi0) :=
    ContDiff.continuous_iteratedDeriv 1 hC3 (by decide)
  have hc2 : Continuous (iteratedDeriv 2 phi0) :=
    ContDiff.continuous_iteratedDeriv 2 hC3 (by decide)
  have hc3 : Continuous (iteratedDeriv 3 phi0) :=
    ContDiff.continuous_iteratedDeriv 3 hC3 (by decide)
  obtain ⟨d1, hd1, hb1⟩ := mkbound (iteratedDeriv 1 phi0) hc1
    (fun u hu => hzeroL 0 u hu) (fun u hu => hzeroR 0 u hu)
  obtain ⟨d2, hd2, hb2⟩ := mkbound (iteratedDeriv 2 phi0) hc2
    (fun u hu => hzeroL 1 u hu) (fun u hu => hzeroR 1 u hu)
  obtain ⟨d3, hd3, hb3⟩ := mkbound (iteratedDeriv 3 phi0) hc3
    (fun u hu => hzeroL 2 u hu) (fun u hu => hzeroR 2 u hu)
  have hC1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) phi0 := ContDiff.of_le hC3 (by decide)
  have hC2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) phi0 := ContDiff.of_le hC3 (by decide)
  have hC3le : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) phi0 := ContDiff.of_le hC3 (by decide)
  refine ⟨d1, d2, d3, hd1, hd2, hd3, ?_, ?_, ?_⟩
  · intro u
    exact ⟨hb1 u, hb2 u, hb3 u⟩
  · intro phi hphi
    fun_prop
  · intro phi hphi t
    refine ⟨?_, ?_, ?_⟩
    · have hcomp := iteratedDeriv_comp_const_mul (n := 1) hC1 phi
      have e1 : iteratedDeriv 1 (fun s : ℝ => phi0 (phi * s)) t
          = phi ^ (1 : ℕ) * iteratedDeriv 1 phi0 (phi * t) := by
        simpa using congrFun hcomp t
      rw [e1, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hphi) 1)]
      exact mul_le_mul_of_nonneg_left (hb1 (phi * t)) (pow_nonneg (le_of_lt hphi) 1)
    · have hcomp := iteratedDeriv_comp_const_mul (n := 2) hC2 phi
      have e2 : iteratedDeriv 2 (fun s : ℝ => phi0 (phi * s)) t
          = phi ^ (2 : ℕ) * iteratedDeriv 2 phi0 (phi * t) := by
        simpa using congrFun hcomp t
      rw [e2, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hphi) 2)]
      exact mul_le_mul_of_nonneg_left (hb2 (phi * t)) (pow_nonneg (le_of_lt hphi) 2)
    · have hcomp := iteratedDeriv_comp_const_mul (n := 3) hC3le phi
      have e3 : iteratedDeriv 3 (fun s : ℝ => phi0 (phi * s)) t
          = phi ^ (3 : ℕ) * iteratedDeriv 3 phi0 (phi * t) := by
        simpa using congrFun hcomp t
      rw [e3, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hphi) 3)]
      exact mul_le_mul_of_nonneg_left (hb3 (phi * t)) (pow_nonneg (le_of_lt hphi) 3)
  /- @proof-region region.target-node.session.b2fdb1015b8926fd end -/

end Statlib.Imported
end

