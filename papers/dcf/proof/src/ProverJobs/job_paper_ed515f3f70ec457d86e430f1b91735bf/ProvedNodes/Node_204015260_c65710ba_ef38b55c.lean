import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
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
theorem statopia_math_node_204015260_c65710ba : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) (hm : 0 < m) (X : Ω → Fin m → ℝ)
    (hXm : ∀ j : Fin m, Measurable (fun ω => X ω j))
    (Sigma : Matrix (Fin m) (Fin m) ℝ) (hX : IsCenteredGaussianVector P X Sigma)
    (j : Fin m),
    (∫ ω, X ω j ∂P = 0) ∧ MemLp (fun ω => X ω j) 2 P ∧
      Integrable (fun ω => X ω j) P := by
  /- @proof-region region.target-node.session.7aeaef961c572a91 begin -/
  intro Ω _ P _ m hm X hXm Sigma hX j
  classical
  let A : Matrix (Fin 1) (Fin m) ℝ := fun _ k => if k = j then 1 else 0
  have hA : ∀ v : Fin m → ℝ, (A.mulVec v) 0 = v j := by
    intro v
    simp only [A, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj; simp [hbj]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hY : IsCenteredGaussianVector P (fun ω => A.mulVec (X ω)) (A * Sigma * A.transpose) :=
    IsCenteredGaussianVector.linearImage P X Sigma hX A
  have hsym : (A * Sigma * A.transpose).transpose = A * Sigma * A.transpose := by
    ext i k; fin_cases i; fin_cases k; rfl
  have hMY := hY.posSemidef_symmetrizedCovariance (by norm_num : 1 ≤ 1)
  have h2inv : ∀ x : ℝ, (2 : ℝ)⁻¹ * (x + x) = x := by
    intro x
    rw [← two_mul, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul]
  have hMeq : ((2 : ℝ)⁻¹ • ((A * Sigma * A.transpose) + (A * Sigma * A.transpose)))
      = A * Sigma * A.transpose := by
    ext i k; fin_cases i; fin_cases k
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    exact h2inv _
  have hMpsd : (A * Sigma * A.transpose).PosSemidef := by
    simpa only [hsym, hMeq] using hMY
  have hLin := IsCenteredGaussianVector.map_linearCombination P (fun ω => A.mulVec (X ω))
    (A * Sigma * A.transpose) hY hMpsd (Pi.single (0 : Fin 1) (1 : ℝ))
  have hfun : (fun ω => ∑ k, (Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ) k * (A.mulVec (X ω)) k)
      = (fun ω => X ω j) := by
    funext ω
    simp only [Fin.sum_univ_one, Pi.single_eq_same, one_mul]
    exact hA (X ω)
  rw [hfun] at hLin
  have hIntEq : ∫ ω, X ω j ∂P = ∫ x, x ∂(Measure.map (fun ω => X ω j) P) := by
    have h : ∫ y, y ∂(Measure.map (fun ω => X ω j) P) = ∫ ω, X ω j ∂P :=
      MeasureTheory.integral_map (hXm j).aemeasurable measurable_id.aestronglyMeasurable
    simpa using h.symm
  have hmap : MemLp (fun x : ℝ => x) 2 (Measure.map (fun ω => X ω j) P) := by
    rw [hLin]
    simpa using memLp_pow_id_gaussianReal (μ₀ := 0) 1 2 (show (2 : ENNReal) ≠ ⊤ by norm_num)
  have hmem : MemLp (fun ω => X ω j) 2 P :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable (hXm j).aemeasurable).mp hmap
  refine ⟨?_, hmem, hmem.integrable (by norm_num)⟩
  simp only [hIntEq, hLin, integral_id_gaussianReal]
  /- @proof-region region.target-node.session.7aeaef961c572a91 end -/

end

end Statlib.Imported

