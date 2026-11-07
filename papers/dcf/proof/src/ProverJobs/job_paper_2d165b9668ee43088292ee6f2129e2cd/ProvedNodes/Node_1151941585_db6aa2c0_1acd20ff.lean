import Lean
import ProverJobs.job_paper_2d165b9668ee43088292ee6f2129e2cd.Vocabulary
import ProverJobs.job_paper_2d165b9668ee43088292ee6f2129e2cd.Base

namespace PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported.XuYaoL4 then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported.XuYaoL4))
open _root_.PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4
open XuYaoL4

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported.XuYaoL4 then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported.XuYaoL4))
open _root_.PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4

set_option autoImplicit false in
theorem statopia_math_node_1151941585_db6aa2c0 : ∀ {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → Fin p → ℝ) (hA : Measurable A) (hB : Measurable B),
    rho P A B ≤
      sSup {t : ℝ |
        ∃ v ∈ Set.Icc (0 : ℝ) 1, ∃ S : Set (Fin p → ℝ), IsHyperrect S ∧
          t = |Measure.real
                  (P.map (fun ω j => Real.sqrt v * A ω j + Real.sqrt (1 - v) * B ω j)) S
                - Measure.real (P.map B) S|} := by
  /- @proof-region region.target-node.session.f44ea344e449a688 begin -/
  intro p Ω msΩ P hP A B hA hB
  unfold rho
  set T₀ : Set ℝ := {t : ℝ | ∃ S : Set (Fin p → ℝ), IsHyperrect S ∧
      t = |Measure.real (P.map A) S - Measure.real (P.map B) S|} with hT₀
  set T : Set ℝ := {t : ℝ | ∃ v ∈ Set.Icc (0 : ℝ) 1, ∃ S : Set (Fin p → ℝ), IsHyperrect S ∧
          t = |Measure.real (P.map (fun ω j => Real.sqrt v * A ω j + Real.sqrt (1 - v) * B ω j)) S
                - Measure.real (P.map B) S|} with hT
  have hBprob : IsProbabilityMeasure (P.map B) := Measure.isProbabilityMeasure_map hB.aemeasurable
  have key : ∀ (f : Ω → Fin p → ℝ), IsProbabilityMeasure (P.map f) → ∀ S : Set (Fin p → ℝ),
      |Measure.real (P.map f) S - Measure.real (P.map B) S| ≤ 1 := by
    intro f hf S
    haveI : IsProbabilityMeasure (P.map f) := hf
    haveI : IsProbabilityMeasure (P.map B) := hBprob
    have ha0 : 0 ≤ Measure.real (P.map f) S := measureReal_nonneg
    have ha1 : Measure.real (P.map f) S ≤ 1 := measureReal_le_one
    have hb0 : 0 ≤ Measure.real (P.map B) S := measureReal_nonneg
    have hb1 : Measure.real (P.map B) S ≤ 1 := measureReal_le_one
    rw [abs_le]
    constructor <;> linarith
  have hsub : T₀ ⊆ T := by
    intro t ht
    rw [hT₀] at ht
    simp only [Set.mem_setOf_eq] at ht
    obtain ⟨S, hS, ht⟩ := ht
    rw [hT]
    simp only [Set.mem_setOf_eq]
    refine ⟨1, ⟨zero_le_one, le_refl 1⟩, S, hS, ?_⟩
    have hmap : (fun ω j => Real.sqrt (1:ℝ) * A ω j + Real.sqrt (1 - 1) * B ω j) = A := by
      funext ω j; simp
    rw [hmap]
    exact ht
  have hbdd : BddAbove T := by
    refine ⟨1, ?_⟩
    intro t ht
    rw [hT] at ht
    simp only [Set.mem_setOf_eq] at ht
    obtain ⟨v, hv, S, hS, ht⟩ := ht
    have hfmeas : Measurable (fun ω : Ω => fun j : Fin p =>
        Real.sqrt v * A ω j + Real.sqrt (1 - v) * B ω j) := by
      rw [measurable_pi_iff]
      intro j
      have h1 : Measurable (fun ω : Ω => Real.sqrt v * A ω j) :=
        measurable_const.mul ((measurable_pi_apply j).comp hA)
      have h2 : Measurable (fun ω : Ω => Real.sqrt (1 - v) * B ω j) :=
        measurable_const.mul ((measurable_pi_apply j).comp hB)
      exact h1.add h2
    have hfprob : IsProbabilityMeasure
        (P.map (fun ω j => Real.sqrt v * A ω j + Real.sqrt (1 - v) * B ω j)) :=
      Measure.isProbabilityMeasure_map hfmeas.aemeasurable
    rw [ht]
    exact key _ hfprob S
  have hne : T₀.Nonempty := by
    refine ⟨|Measure.real (P.map A) Set.univ - Measure.real (P.map B) Set.univ|, ?_⟩
    rw [hT₀]
    simp only [Set.mem_setOf_eq]
    refine ⟨Set.univ, ?_, rfl⟩
    refine ⟨fun _ => ⊥, fun _ => ⊤, ?_, ?_⟩
    · intro j; exact bot_le
    · ext w; simp
  exact csSup_le hne (fun t ht => le_csSup hbdd (hsub ht))
  /- @proof-region region.target-node.session.f44ea344e449a688 end -/

end Statlib.Imported

