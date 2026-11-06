import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_49ff1782b721a9fe03a8

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
theorem statopia_math_node_1061731261_2101eec5 : ∀ (m n : ℕ) (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ)
    (z : ℂ) (hz : 0 < z.im),
    symStieltjesSvals (svals A) z =
      - (((((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ) *
          ((((((m : ℝ) + (n : ℝ))⁻¹ : ℝ)) : ℂ) *
            ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A
                  (Matrix.transpose A) (0 : Matrix (Fin n) (Fin n) ℝ)).map
                  Complex.ofReal)⁻¹).trace)
        + (((((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ) * z⁻¹ := by
  /- @proof-region region.target-node.session.45753ba5877533e1 begin -/
  classical
  intro m n hn A z hz
  set X : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
      (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal with hX
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hz0 : z ≠ 0 := by
    rintro rfl
    simpa using hz
  have key :
      (((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) - X)⁻¹.trace
        = -(∑ i : Fin n, (((svals A i : ℂ) - z)⁻¹ + (-(svals A i : ℂ) - z)⁻¹))
          + ((m : ℂ) - (n : ℂ)) * z⁻¹ := by
    simpa only [hX] using statopia_math_node_2776670489_0aa5642a m n hn A z hz
  have halg : ∀ S T : ℂ, T = -S + ((m : ℂ) - (n : ℂ)) * z⁻¹ →
      (2 * ((n : ℝ) : ℂ))⁻¹ * S
        = - (((((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ) *
              ((((((m : ℝ) + (n : ℝ))⁻¹ : ℝ)) : ℂ) * T)
          + (((((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ) * z⁻¹ := by
    intro S T hT
    rw [hT]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2nC : (2 * (n : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hnC
    have hmnR : ((m : ℝ) + (n : ℝ)) ≠ 0 := by
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hn0 : (0 : ℝ) < (n : ℝ) := hnR
      positivity
    have hmnC : (((m : ℝ) + (n : ℝ) : ℝ) : ℂ) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr hmnR)
    have hmnC' : ((m : ℂ) + (n : ℂ)) ≠ 0 := by
      push_cast at hmnC
      exact hmnC
    push_cast
    field_simp
    ring
  simp only [symStieltjesSvals]
  exact halg _ _ key
  /- @proof-region region.target-node.session.45753ba5877533e1 end -/

end Statlib.Imported

