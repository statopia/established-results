import Lean
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Vocabulary
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Base

namespace PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e

open _root_.PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_750611871_04cdf965 : ∀ (Ω : Type) [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (ι : Type) [Fintype ι]
    (eps : ℝ) (heps : 0 ≤ eps)
    (S : ι → Set Ω) (hS : ∀ j, MeasurableSet (S j))
    (hbad : ∀ j, mu.real ((S j)ᶜ) ≤ eps),
    MeasurableSet (⋂ j, S j) ∧
      1 - (Fintype.card ι : ℝ) * eps ≤ mu.real (⋂ j, S j) := by
  /- @proof-region region.target-node.session.323d1dab10ec95ff begin -/
  intro Ω _ mu _ ι _ eps heps S hS hbad
  have hmeas : MeasurableSet (⋂ j, S j) := MeasurableSet.iInter hS
  refine ⟨hmeas, ?_⟩
  have hreal_eq : ∀ s : Set Ω, mu.real s = (mu s).toReal := fun s => rfl
  have huniv : mu.real (Set.univ : Set Ω) = 1 := by
    rw [hreal_eq, measure_univ]
    simp
  have hcompl : (⋂ j, S j)ᶜ = ⋃ j, (S j)ᶜ := Set.compl_iInter S
  have hreal : mu.real (⋂ j, S j) = 1 - mu.real (⋃ j, (S j)ᶜ) := by
    have h := measureReal_compl (μ := mu) hmeas
    rw [hcompl, huniv] at h
    linarith
  have hterm_fin : ∀ j, mu ((S j)ᶜ) ≠ ⊤ := fun j => (measure_lt_top mu ((S j)ᶜ)).ne
  have hsum_fin : (∑ j, mu ((S j)ᶜ)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => hterm_fin j)

  have hunion_le : mu (⋃ j, (S j)ᶜ) ≤ ∑ j, mu ((S j)ᶜ) := by
    simpa using measure_biUnion_finset_le (μ := mu) (Finset.univ : Finset ι) (fun j => (S j)ᶜ)
  have hsub : mu.real (⋃ j, (S j)ᶜ) ≤ ∑ j, mu.real ((S j)ᶜ) := by
    calc mu.real (⋃ j, (S j)ᶜ) = (mu (⋃ j, (S j)ᶜ)).toReal := hreal_eq _
      _ ≤ (∑ j, mu ((S j)ᶜ)).toReal := ENNReal.toReal_mono hsum_fin hunion_le
      _ = ∑ j, (mu ((S j)ᶜ)).toReal := ENNReal.toReal_sum (fun j _ => hterm_fin j)
      _ = ∑ j, mu.real ((S j)ᶜ) :=
          Finset.sum_congr rfl (fun j _ => (hreal_eq ((S j)ᶜ)).symm)
  have hsum_le : ∑ j, mu.real ((S j)ᶜ) ≤ (Fintype.card ι : ℝ) * eps := by
    calc ∑ j, mu.real ((S j)ᶜ) ≤ ∑ _j : ι, eps := Finset.sum_le_sum (fun j _ => hbad j)
      _ = (Fintype.card ι : ℝ) * eps := by
          simp [Finset.sum_const, Finset.card_univ]

  have hbound : mu.real (⋃ j, (S j)ᶜ) ≤ (Fintype.card ι : ℝ) * eps := le_trans hsub hsum_le
  linarith
  /- @proof-region region.target-node.session.323d1dab10ec95ff end -/

end

end Statlib.Imported

