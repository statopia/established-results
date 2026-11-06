import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.HighDim.SpectralPerturbation.Weyl
import Statlib.HighDim.Vocabulary.Spectral
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
theorem statopia_math_node_1536250861_1a8485ab : ∀ (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (H : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hH_meas : ∀ a b : Fin n, Measurable fun ω : Ω => H ω a b)
    (hH : ∀ ω : Ω, (H ω).IsHermitian)
    (k : Fin n),
    Measurable fun ω : Ω =>
      Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) k := by
  /- @proof-region region.target-node.session.200dfb3fcc93ed2e begin -/
  intro n Ω _ H hH_meas hH k
  have hG : Measurable fun ω : Ω => (fun i j : Fin n => H ω i j) :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hH_meas i j
  have hHm : Measurable H := hG
  let herm : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun A i j => (2 : ℝ)⁻¹ * (A i j + A j i)
  have hherm : ∀ A : Matrix (Fin n) (Fin n) ℝ, (herm A).IsHermitian := by
    intro A
    show Matrix.conjTranspose (herm A) = herm A
    ext i j
    rw [Matrix.conjTranspose_apply]
    simp only [star_trivial]
    dsimp only [herm]
    rw [add_comm]
  let F : Matrix (Fin n) (Fin n) ℝ → ℝ :=
    fun A => Statlib.HighDim.Vocabulary.sortedEigenvalues (herm A) (hherm A) k
  have hgen : ∀ (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian),
      A = B → Statlib.HighDim.Vocabulary.sortedEigenvalues A hA k
        = Statlib.HighDim.Vocabulary.sortedEigenvalues B hB k := by
    intro A B hA hB hAB
    cases hAB
    exact congrArg (fun h => Statlib.HighDim.Vocabulary.sortedEigenvalues A h k)
      (Subsingleton.elim hA hB)
  have hherm_cont : Continuous herm := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have hij : Continuous fun A : Matrix (Fin n) (Fin n) ℝ => A i j :=
      (continuous_apply j : Continuous fun r : Fin n → ℝ => r j).comp
        (continuous_apply i : Continuous fun A : Fin n → Fin n → ℝ => A i)
    have hji : Continuous fun A : Matrix (Fin n) (Fin n) ℝ => A j i :=
      (continuous_apply i : Continuous fun r : Fin n → ℝ => r i).comp
        (continuous_apply j : Continuous fun A : Fin n → Fin n → ℝ => A j)
    dsimp only [herm]
    exact continuous_const.mul (hij.add hji)
  have hfun : (fun ω : Ω => F (H ω))
      = fun ω => Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) k := by
    funext ω
    show Statlib.HighDim.Vocabulary.sortedEigenvalues (herm (H ω)) (hherm (H ω)) k
      = Statlib.HighDim.Vocabulary.sortedEigenvalues (H ω) (hH ω) k
    have hsymm : ∀ i j : Fin n, H ω j i = H ω i j := by
      intro i j
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) (hH ω)
      simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
    have hhermH : herm (H ω) = H ω := by
      ext i j
      dsimp only [herm]
      rw [hsymm i j, ← two_mul, ← mul_assoc]
      rw [show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, one_mul]
    exact hgen (herm (H ω)) (H ω) (hherm (H ω)) (hH ω) hhermH
  have hF_cont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro A
    show Filter.Tendsto F (nhds A) (nhds (F A))
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hle : ∀ B : Matrix (Fin n) (Fin n) ℝ,
        dist (F B) (F A) ≤ dist (herm B) (herm A) := by
      intro B
      have heq : herm A + (herm B - herm A) = herm B := by abel
      have hAE : (herm A + (herm B - herm A)).IsHermitian := heq.symm ▸ hherm B
      have hw := Statlib.HighDim.SpectralPerturbation.weyl_sorted (herm A) (herm B - herm A)
        (hherm A) hAE k
      have hFB : F B = Statlib.HighDim.Vocabulary.sortedEigenvalues
          (herm A + (herm B - herm A)) hAE k :=
        hgen (herm B) (herm A + (herm B - herm A)) (hherm B) hAE heq.symm
      have hFA : F A = Statlib.HighDim.Vocabulary.sortedEigenvalues (herm A) (hherm A) k := rfl
      calc dist (F B) (F A) = |F B - F A| := by rw [Real.dist_eq]
        _ = |Statlib.HighDim.Vocabulary.sortedEigenvalues
              (herm A + (herm B - herm A)) hAE k
              - Statlib.HighDim.Vocabulary.sortedEigenvalues (herm A) (hherm A) k| := by
            rw [hFB, hFA]
        _ ≤ ‖herm B - herm A‖ := hw
        _ = dist (herm B) (herm A) := (dist_eq_norm _ _).symm
    have hball : ∀ᶠ B in nhds A, dist (herm B) (herm A) < ε := by
      have hc : Filter.Tendsto herm (nhds A) (nhds (herm A)) := hherm_cont.continuousAt
      rw [Metric.tendsto_nhds] at hc
      exact hc ε hε
    filter_upwards [hball] with B hB
    exact lt_of_le_of_lt (hle B) hB
  have hF_meas : Measurable F := hF_cont.measurable
  have hcomp : Measurable fun ω => F (H ω) := hF_meas.comp hHm
  simpa only [hfun] using hcomp
  /- @proof-region region.target-node.session.200dfb3fcc93ed2e end -/

end Statlib.Imported

