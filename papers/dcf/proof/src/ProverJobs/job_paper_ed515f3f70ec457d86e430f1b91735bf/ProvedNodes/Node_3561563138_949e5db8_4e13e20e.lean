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
theorem statopia_math_node_3561563138_949e5db8 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℕ} (hp : 1 ≤ p)
    (Z : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hZ : ∀ j : Fin p, AEMeasurable (fun ω => Z ω j) P)
    (hGauss : IsCenteredGaussianVector P Z Sigma),
    (∀ j : Fin p, ∫ ω, Z ω j ∂P = 0) ∧
    (∀ j : Fin p, MemLp (fun ω => Z ω j) 2 P) ∧
    (∀ j : Fin p, ∫ ω, Z ω j * Z ω j ∂P = Sigma j j) := by
  /- @proof-region region.target-node.session.3e6ada92e9a3607e begin -/
  intro Ω _ P _ p hp Z Sigma hZ hGauss
  have hsingle : ∀ (j : Fin p) (f : Fin p → ℝ),
      ∑ i, (Pi.single j (1 : ℝ) : Fin p → ℝ) i * f i = f j := by
    intro j f
    simp [Pi.single_apply]
  have hsingle' : ∀ (j : Fin p) (f : Fin p → ℝ),
      ∑ i, f i * (Pi.single j (1 : ℝ) : Fin p → ℝ) i = f j := by
    intro j f
    simpa only [mul_comm] using hsingle j f
  have key : ∀ j : Fin p, ∃ v : NNReal, (v : ℝ) = Sigma j j ∧
      Measure.map (fun ω => Z ω j) P = gaussianReal 0 v := by
    intro j
    set A : Matrix (Fin 1) (Fin p) ℝ := fun _ => Pi.single j (1 : ℝ) with hA
    have hG' : IsCenteredGaussianVector P (fun ω => A.mulVec (Z ω)) (A * Sigma * A.transpose) :=
      hGauss.linearImage P Z Sigma A
    have hrow : ∀ (M : Matrix (Fin p) (Fin p) ℝ) (i k : Fin 1),
        (A * M * A.transpose) i k = M j j := by
      intro M i k
      simp only [hA, Matrix.mul_apply, Matrix.transpose_apply, hsingle]
      exact hsingle' j (fun x => M j x)
    have hsym : (2⁻¹ : ℝ) • (A * Sigma * A.transpose + (A * Sigma * A.transpose).transpose)
        = A * Sigma * A.transpose := by
      ext i k
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.transpose_apply, hrow]
      ring
    have hpsd : (A * Sigma * A.transpose).PosSemidef := by
      rw [← hsym]
      exact hG'.posSemidef_symmetrizedCovariance (le_refl 1)
    have hc00 : (A * Sigma * A.transpose) 0 0 = Sigma j j := hrow Sigma 0 0
    set u : Fin 1 → ℝ := fun _ => (1 : ℝ) with hu
    have hmc := IsCenteredGaussianVector.map_linearCombination P (fun ω => A.mulVec (Z ω))
      (A * Sigma * A.transpose) hG' hpsd u
    have hmv : ∀ (x : Fin p → ℝ), (A.mulVec x) 0 = x j := by
      intro x
      have h1 : (A.mulVec x) 0 = ∑ i, (Pi.single j (1 : ℝ) : Fin p → ℝ) i * x i := rfl
      rw [h1]
      exact hsingle j x
    have hleft : (fun ω => ∑ k : Fin 1, u k * (A.mulVec (Z ω)) k) = fun ω => Z ω j := by
      funext ω
      rw [Fin.sum_univ_one]
      simp only [hu, one_mul]
      exact hmv (Z ω)
    have hval : (∑ i : Fin 1, ∑ k : Fin 1, u i * (A * Sigma * A.transpose) i k * u k) = Sigma j j := by
      simpa only [hu, Fin.sum_univ_one, one_mul, mul_one] using hc00
    have hsquares : (0 : ℝ) ≤
        ∑ i : Fin 1, ∑ k : Fin 1, u i * (A * Sigma * A.transpose) i k * u k := by
      rw [← Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_quadratic
        (A * Sigma * A.transpose) hpsd u]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hsjj : (0 : ℝ) ≤ Sigma j j := by
      rw [← hval]
      exact hsquares
    refine ⟨⟨Sigma j j, hsjj⟩, rfl, ?_⟩
    rw [← hleft, hmc]
    exact congrArg (fun v : NNReal => gaussianReal (0 : ℝ) v) (Subtype.ext hval)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    obtain ⟨v, hv, hmap⟩ := key j
    have h1 : ∫ x : ℝ, x ∂(Measure.map (fun ω => Z ω j) P) = ∫ ω, Z ω j ∂P :=
      integral_map (hZ j) (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable
    rw [hmap, integral_id_gaussianReal] at h1
    exact h1.symm
  · intro j
    obtain ⟨v, hv, hmap⟩ := key j
    have h2 : MemLp (fun x : ℝ => x ^ 1) 2 (Measure.map (fun ω => Z ω j) P) := by
      rw [hmap]
      exact memLp_pow_id_gaussianReal 1 2 (by simp)
    have h3 : MemLp ((fun x : ℝ => x ^ 1) ∘ (fun ω => Z ω j)) 2 P := h2.comp_of_map (hZ j)
    simpa using h3
  · intro j
    obtain ⟨v, hv, hmap⟩ := key j
    have h1 : ∫ x : ℝ, x * x ∂(Measure.map (fun ω => Z ω j) P) = ∫ ω, Z ω j * Z ω j ∂P :=
      integral_map (hZ j) (f := fun x : ℝ => x * x) ((measurable_id.mul measurable_id).aestronglyMeasurable)
    rw [hmap] at h1
    have hvar : ∫ x : ℝ, x * x ∂gaussianReal (0 : ℝ) v = (v : ℝ) := by
      have hv' := variance_id_gaussianReal (μ := (0 : ℝ)) (v := v)
      rw [ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable] at hv'
      simp only [id_eq, integral_id_gaussianReal, sub_zero, sq] at hv'
      simpa using hv'
    rw [hvar, hv] at h1
    exact h1.symm
  /- @proof-region region.target-node.session.3e6ada92e9a3607e end -/

end

end Statlib.Imported

