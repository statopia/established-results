import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_572064251_06b3b28d : ∀ (m n r : ℕ) (p Cc mu0 : ℝ)
    (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    {Ωs : Type*} [MeasurableSpace Ωs]
    (Om : Ωs → Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ (i : Fin m) (j : Fin n), Measurable (fun s : Ωs => Om s i j)),
    MeasurableSet
      {ω : Ωs |
        (Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om ω))
            ≤ Cc * Real.sqrt ((m : ℝ) / p)) ∧
          (∀ A B : Matrix (Fin m) (Fin n) ℝ,
            inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
              |matInner (TOmega (Om ω) U0 V0 A) B - p * matInner A B|
                ≤ Cc * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                    * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                    * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B)} := by
  /- @proof-region region.target-node.session.d905fb8842a68759 begin -/
  intro m n r p Cc mu0 U0 V0 Ωs instΩ Om hOm
  have hmeas : Measurable Om :=
    measurable_pi_iff.2 (fun i => measurable_pi_iff.2 (fun j => hOm i j))
  have hG : MeasurableSet ({M : Matrix (Fin m) (Fin n) ℝ |
      Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p M) ≤ Cc * Real.sqrt ((m : ℝ) / p) ∧
        ∀ A B : Matrix (Fin m) (Fin n) ℝ,
          inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
            |matInner (TOmega M U0 V0 A) B - p * matInner A B|
              ≤ Cc * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                  * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                  * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B} : Set (Matrix (Fin m) (Fin n) ℝ)) := by
    have h1 : MeasurableSet {M : Matrix (Fin m) (Fin n) ℝ |
        Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p M) ≤ Cc * Real.sqrt ((m : ℝ) / p)} := by
      have hmask : Continuous fun M : Matrix (Fin m) (Fin n) ℝ => centeredMaskOp p M := by
        show Continuous fun M : Matrix (Fin m) (Fin n) ℝ => fun i j => p⁻¹ * M i j - 1
        exact continuous_pi (fun i => continuous_pi (fun j =>
          (continuous_const.mul (continuous_apply_apply i j)).sub continuous_const))
      have hCLM : Continuous fun M : Matrix (Fin m) (Fin n) ℝ =>
          LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) := by
        let F : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
          LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
        have hF : Continuous F := LinearMap.continuous_of_finiteDimensional F
        rw [show (fun M : Matrix (Fin m) (Fin n) ℝ =>
            LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)) = ⇑F from rfl]
        exact hF
      have hnorm : Continuous fun M : Matrix (Fin m) (Fin n) ℝ =>
          Statlib.HighDim.MatrixAnalysis.opNorm M := by
        simpa only [Statlib.HighDim.MatrixAnalysis.opNorm] using continuous_norm.comp hCLM
      exact IsClosed.measurableSet (isClosed_le (hnorm.comp hmask) continuous_const)
    have h2 : MeasurableSet {M : Matrix (Fin m) (Fin n) ℝ |
        ∀ A B : Matrix (Fin m) (Fin n) ℝ,
          inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
            |matInner (TOmega M U0 V0 A) B - p * matInner A B|
              ≤ Cc * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                  * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                  * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B} := by
      have hmaskA : ∀ A : Matrix (Fin m) (Fin n) ℝ,
          Continuous fun M : Matrix (Fin m) (Fin n) ℝ => maskOp M A := by
        intro A
        show Continuous fun M : Matrix (Fin m) (Fin n) ℝ => fun i j => M i j * A i j
        exact continuous_pi (fun i => continuous_pi (fun j =>
          (continuous_apply_apply i j).mul continuous_const))
      let C : Matrix (Fin m) (Fin m) ℝ := 1 - U0 * U0.transpose
      let D : Matrix (Fin n) (Fin n) ℝ := 1 - V0 * V0.transpose
      have hL : Continuous fun N : Matrix (Fin m) (Fin n) ℝ => C * N := by
        show Continuous fun N : Matrix (Fin m) (Fin n) ℝ => fun i j => ∑ k, C i k * N k j
        exact continuous_pi (fun i => continuous_pi (fun j =>
          continuous_finset_sum _ (fun k _ => continuous_const.mul (continuous_apply_apply k j))))
      have hR : Continuous fun Y : Matrix (Fin m) (Fin n) ℝ => Y * D := by
        show Continuous fun Y : Matrix (Fin m) (Fin n) ℝ => fun i j => ∑ k, Y i k * D k j
        exact continuous_pi (fun i => continuous_pi (fun j =>
          continuous_finset_sum _ (fun k _ => (continuous_apply_apply i k).mul continuous_const)))
      have hproj : Continuous fun N : Matrix (Fin m) (Fin n) ℝ => projTangent U0 V0 N := by
        show Continuous fun N : Matrix (Fin m) (Fin n) ℝ => N - C * N * D
        exact continuous_id.sub (hR.comp hL)
      have hclosed : IsClosed {M : Matrix (Fin m) (Fin n) ℝ |
          ∀ A B : Matrix (Fin m) (Fin n) ℝ,
            inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
              |matInner (TOmega M U0 V0 A) B - p * matInner A B|
                ≤ Cc * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                    * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                    * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B} := by
        rw [show {M : Matrix (Fin m) (Fin n) ℝ |
            ∀ A B : Matrix (Fin m) (Fin n) ℝ,
              inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
                |matInner (TOmega M U0 V0 A) B - p * matInner A B|
                  ≤ Cc * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B}
            = ⋂ (A : Matrix (Fin m) (Fin n) ℝ), ⋂ (B : Matrix (Fin m) (Fin n) ℝ),
              {M : Matrix (Fin m) (Fin n) ℝ |
                inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
                  |matInner (TOmega M U0 V0 A) B - p * matInner A B|
                    ≤ Cc * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                        * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                        * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B} from by
          ext M
          simp only [Set.mem_setOf_eq, Set.mem_iInter]]
        refine isClosed_iInter (fun A => isClosed_iInter (fun B => ?_))
        by_cases hA : inTangentSpace U0 V0 A
        · by_cases hB : inTangentSpace U0 V0 B
          · have hcont : Continuous fun M : Matrix (Fin m) (Fin n) ℝ =>
                |matInner (TOmega M U0 V0 A) B - p * matInner A B| := by
              have hi : Continuous fun X : Matrix (Fin m) (Fin n) ℝ => matInner X B := by
                show Continuous fun X : Matrix (Fin m) (Fin n) ℝ => ∑ i, ∑ j, X i j * B i j
                exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _
                  (fun j _ => (continuous_apply_apply i j).mul continuous_const))
              exact ((hi.comp (hproj.comp (hmaskA A))).sub continuous_const).abs
            rw [show {M : Matrix (Fin m) (Fin n) ℝ |
                inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
                  |matInner (TOmega M U0 V0 A) B - p * matInner A B|
                    ≤ Cc * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                        * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                        * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B}
                = {M : Matrix (Fin m) (Fin n) ℝ |
                  |matInner (TOmega M U0 V0 A) B - p * matInner A B|
                    ≤ Cc * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                        * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                        * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B} from by
              ext M
              simp [hA, hB]]
            exact isClosed_le hcont continuous_const
          · rw [show {M : Matrix (Fin m) (Fin n) ℝ |
                inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
                  |matInner (TOmega M U0 V0 A) B - p * matInner A B|
                    ≤ Cc * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                        * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                        * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B} = Set.univ from by
              ext M
              simp [hA, hB]]
            exact isClosed_univ
        · rw [show {M : Matrix (Fin m) (Fin n) ℝ |
              inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
                |matInner (TOmega M U0 V0 A) B - p * matInner A B|
                  ≤ Cc * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B} = Set.univ from by
            ext M
            simp [hA]]
          exact isClosed_univ
      exact IsClosed.measurableSet hclosed
    exact MeasurableSet.inter h1 h2
  exact MeasurableSet.preimage hG hmeas
  /- @proof-region region.target-node.session.d905fb8842a68759 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_572064251_06b3b28d


