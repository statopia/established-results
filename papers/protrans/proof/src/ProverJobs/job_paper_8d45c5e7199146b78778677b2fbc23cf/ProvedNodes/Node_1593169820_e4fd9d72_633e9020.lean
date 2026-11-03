import Lean
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Vocabulary
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Base

namespace PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_1593169820_e4fd9d72 : ∀ (k n : ℕ) (hn : 1 ≤ n)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ℝ) (cA : NNReal) (hA : HasSubgaussianMGF A cA μ)
    (Y : Fin k → Ω → ℝ) (cY : NNReal)
    (hY : ∀ j : Fin k, HasSubgaussianMGF (Y j) cY μ)
    (delta : Fin k → ℝ) (Cst : ℝ),
    Integrable (fun ω => |A ω * (∑ j : Fin k, Y j ω * delta j) - Cst| ^ n) μ := by
  /- @proof-region region.target-node.session.f3c8411002d9a4f7 begin -/
  intro k n hn Ω ms μ prob A cA hA Y cY hY delta Cst
  have hmemA : MemLp A ((2 * n : ℕ) : ℝ≥0∞) μ := by
    simpa using hA.memLp ((2 * n : ℕ) : NNReal)
  have hmemY : ∀ j : Fin k, MemLp (Y j) ((2 * n : ℕ) : ℝ≥0∞) μ := fun j => by
    simpa using (hY j).memLp ((2 * n : ℕ) : NNReal)
  have hS : MemLp (fun ω => ∑ j : Fin k, Y j ω * delta j) ((2 * n : ℕ) : ℝ≥0∞) μ := by
    simpa using
      (memLp_finset_sum (Finset.univ : Finset (Fin k))
        (fun j _ => (hmemY j).mul_const (delta j)))
  haveI htriple : ((2 * n : ℕ) : ℝ≥0∞).HolderTriple ((2 * n : ℕ) : ℝ≥0∞) ((n : ℕ) : ℝ≥0∞) := by
    refine ENNReal.HolderTriple.of_toReal ?_
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hnn : ((n : ℝ)) ≠ 0 := ne_of_gt hnpos
    have h2npos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by
      have h : (0 : ℕ) < 2 * n := by omega
      exact_mod_cast h
    have h2nn : (2 : ℝ) * (n : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hnn
    refine ⟨?_, ?_, ?_⟩
    · have key : ((2 * n : ℕ) : ℝ)⁻¹ + ((2 * n : ℕ) : ℝ)⁻¹ = ((n : ℕ) : ℝ)⁻¹ := by
        have h2 : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
        rw [h2]
        field_simp
        ring
      first
        | exact key
        | exact key.symm
    · exact h2npos
    · exact h2npos
  have hAS : MemLp (fun ω => A ω * (∑ j : Fin k, Y j ω * delta j)) ((n : ℕ) : ℝ≥0∞) μ :=
    hS.mul hmemA
  have hconst : MemLp (fun _ : Ω => Cst) ((n : ℕ) : ℝ≥0∞) μ := memLp_const Cst
  have hsub : MemLp (fun ω => A ω * (∑ j : Fin k, Y j ω * delta j) - Cst) ((n : ℕ) : ℝ≥0∞) μ :=
    hAS.sub hconst
  have hnne : n ≠ 0 := by omega
  have hfin : Integrable (fun ω => ‖A ω * (∑ j : Fin k, Y j ω * delta j) - Cst‖ ^ n) μ :=
    hsub.integrable_norm_pow hnne
  simpa [Real.norm_eq_abs] using hfin
  /- @proof-region region.target-node.session.f3c8411002d9a4f7 end -/

end Statlib.Imported

