import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1861729969_f0cb78c5_26d7b60b

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
theorem statopia_math_node_1913777471_3deb48ab : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p n : ℕ} (muX : Fin p → ℝ) (X : Fin n → Ω → Fin p → ℝ) (i : Fin n)
    (hXL2 : ∀ j : Fin p, MemLp (fun ω => X i ω j) 2 P)
    (Y : Ω → Fin p → ℝ)
    (hY : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P Y (covX P muX X i)),
    (∀ j : Fin p, ∫ ω, Y ω j ∂P = 0) ∧
      (∀ j k : Fin p, ∫ ω, Y ω j * Y ω k ∂P = covX P muX X i j k) := by
  /- @proof-region region.target-node.session.8a3513f626e3875b begin -/
  intro Ω _ P _ p n muX X i hXL2 Y hY
  by_cases hp0 : p = 0
  · subst hp0
    exact ⟨fun j => j.elim0, fun j => j.elim0⟩
  · have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp0
    have hSigma : (covX P muX X i).PosSemidef := by
      have h := IsCenteredGaussianVector.posSemidef_symmetrizedCovariance hY hp1
      have hsym : (covX P muX X i).transpose = covX P muX X i := by
        ext a b
        simp only [Matrix.transpose_apply, covX]
        apply integral_congr_ae
        filter_upwards with ω
        ring
      rw [hsym] at h
      have hone : (2⁻¹ : ℝ) • (covX P muX X i + covX P muX X i) = covX P muX X i := by
        rw [smul_add, ← add_smul, show (2⁻¹ + 2⁻¹ : ℝ) = 1 by norm_num, one_smul]
      rw [hone] at h
      exact h
    refine ⟨?_, ?_⟩
    · intro j
      have hmap := IsCenteredGaussianVector.map_linearCombination P Y (covX P muX X i) hY hSigma (Pi.single j (1:ℝ))
      have hkey : (fun ω => ∑ m, (Pi.single j (1:ℝ) : Fin p → ℝ) m * Y ω m) = (fun ω => Y ω j) := by
        funext ω
        have hinner : ∑ m, (Pi.single j (1:ℝ) : Fin p → ℝ) m * Y ω m = Y ω j := by
          have hsum := Finset.sum_eq_single (s := Finset.univ) (f := fun m => (Pi.single j (1:ℝ) : Fin p → ℝ) m * Y ω m) j
            (by intro b _ hb; simp [Pi.single_eq_of_ne, Ne.symm hb, hb])
            (by intro hj; exact absurd (Finset.mem_univ j) hj)
          simpa using hsum
        exact hinner
      rw [hkey] at hmap
      have hf : AEMeasurable (fun ω => Y ω j) P := ((measurable_pi_iff.mp hY.measurable) j).aemeasurable
      have hInt : ∫ x, x ∂(Measure.map (fun ω => Y ω j) P) = ∫ ω, Y ω j ∂P :=
        MeasureTheory.integral_map hf (measurable_id.aestronglyMeasurable)
      rw [← hInt, hmap]
      exact integral_id_gaussianReal
    · intro j k
      exact statopia_math_node_1861729969_f0cb78c5 P (covX P muX X i) Y hY hSigma j k
  /- @proof-region region.target-node.session.8a3513f626e3875b end -/

end

end Statlib.Imported

