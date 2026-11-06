import Lean
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

/-- The sole open analytic input: one polynomial rate for the canonical real
Gaussian symmetrized expected CDF, uniform in the aspect ratio. -/
def DenseSymmetricPolynomialRate (beta : ℝ) : Prop :=
  ∀ (rhoMinus : ℝ), 0 < rhoMinus → rhoMinus ≤ 1 →
    ∃ C4 : ℝ, 0 < C4 ∧ ∃ mG : ℕ,
      ∀ (m n : ℕ), mG ≤ m → 1 ≤ n → n ≤ m →
        rhoMinus ≤ (n : ℝ) / (m : ℝ) → (n : ℝ) / (m : ℝ) ≤ 1 →
        ∀ x : ℝ,
          |(∫ g : Matrix (Fin m) (Fin n) ℝ,
              (2 * (n : ℝ))⁻¹ *
                (((Finset.univ.filter (fun i : Fin n =>
                    svals (fun a b => (Real.sqrt (m : ℝ))⁻¹ * g a b) i ≤ x)).card : ℝ) +
                  ((Finset.univ.filter (fun i : Fin n =>
                    -(svals (fun a b => (Real.sqrt (m : ℝ))⁻¹ * g a b) i) ≤ x)).card : ℝ))
              ∂(stdNormalMatrixMeasure m n)) -
            (∫ u in Set.Iic x,
              (rootedMPDensity ((n : ℝ) / (m : ℝ)) u +
                rootedMPDensity ((n : ℝ) / (m : ℝ)) (-u)) / 2)|
          ≤ C4 * Real.rpow (m : ℝ) (-beta)
end Statlib.Imported

