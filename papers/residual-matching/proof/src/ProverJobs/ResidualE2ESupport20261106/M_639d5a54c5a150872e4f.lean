import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_b1d70f1c40e4e5140187
import ProverJobs.ResidualE2ESupport20261106.M_393f49f06ac135373093
import ProverJobs.ResidualE2ESupport20261106.M_7d613d7f530ddd0e0e17
import ProverJobs.ResidualE2ESupport20261106.M_2b7c5353cf73d2ddcea9

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
theorem statopia_math_node_2026933490_bd269a1d : ∀ (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus)
    (h_rhoMinus_le : rhoMinus ≤ 1),
    ∃ cRho tRho : ℝ, 0 < cRho ∧ 0 < tRho ∧
      ∀ (rho : ℝ), rhoMinus ≤ rho → rho ≤ 1 →
        ((∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u) = 1 ∧
          (∀ t : ℝ, t ≤ mpLambdaMinus rho → mpTail rho t = 1) ∧
          (∀ t : ℝ, mpLambdaPlus rho ≤ t → mpTail rho t = 0) ∧
          Continuous (mpTail rho) ∧
          StrictAntiOn (mpTail rho) (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) ∧
          (∀ (n : ℕ) (hn : 1 ≤ n) (i : Fin n),
            (mpLambdaMinus rho ≤ mpQuantile rho n i ∧ mpQuantile rho n i ≤ mpLambdaPlus rho) ∧
              mpTail rho (mpQuantile rho n i) = (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) ∧
              ((∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i), rootedMPDensity rho u)
                = 1 - (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ)) ∧
              (∀ s : ℝ, 0 < s →
                ((∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i + s), rootedMPDensity rho u)
                  = (∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i), rootedMPDensity rho u) +
                    (∫ u in (mpQuantile rho n i)..(mpQuantile rho n i + s), rootedMPDensity rho u))) ∧
              (∀ s : ℝ, 0 < s →
                ((∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i - s), rootedMPDensity rho u)
                  = (∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i), rootedMPDensity rho u) -
                    (∫ u in (mpQuantile rho n i - s)..(mpQuantile rho n i), rootedMPDensity rho u)))) ∧
          (∀ x : ℝ, mpLambdaMinus rho ≤ x → x ≤ mpLambdaPlus rho →
            ∀ t : ℝ, 0 < t → t ≤ tRho →
              (x + t ≤ mpLambdaPlus rho →
                cRho * t ^ ((3 : ℝ) / 2) ≤ (∫ u in x..(x + t), rootedMPDensity rho u)) ∧
              (mpLambdaMinus rho ≤ x - t →
                cRho * t ^ ((3 : ℝ) / 2) ≤ (∫ u in (x - t)..x, rootedMPDensity rho u)))) := by
  /- @proof-region region.target-node.session.7365fd8e3c4a7b9a begin -/
  intro rhoMinus h_rhoMinus_pos h_rhoMinus_le
  obtain ⟨cRho, tRho, hcRho, htRho, hmain⟩ :=
    statopia_math_node_4071678792_608a93f0 rhoMinus h_rhoMinus_pos h_rhoMinus_le
  refine ⟨cRho, tRho, hcRho, htRho, ?_⟩
  intro rho hrho_min hrho_le
  have hzero_ge : ∀ x : ℝ, mpLambdaPlus rho ≤ x → rootedMPDensity rho x = 0 := by
    intro x hx
    unfold rootedMPDensity
    by_cases h : x ≤ mpLambdaPlus rho
    · have hxeq : x = mpLambdaPlus rho := le_antisymm h hx
      subst hxeq
      simp
    · rw [if_neg (by rintro ⟨-, hle⟩; exact h hle)]
      simp
  have hA := statopia_math_node_384144625_a59c7546 rhoMinus h_rhoMinus_pos h_rhoMinus_le rho hrho_min hrho_le
  have hTailZero : ∀ t : ℝ, mpLambdaPlus rho ≤ t → mpTail rho t = 0 := by
    intro t ht
    unfold mpTail
    rw [intervalIntegral.integral_of_ge ht]
    rw [show (∫ x in Set.Ioc (mpLambdaPlus rho) t, rootedMPDensity rho x)
          = ∫ x in Set.Ioc (mpLambdaPlus rho) t, (0 : ℝ) from
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          (fun x hx => hzero_ge x (le_of_lt hx.1))]
    simp
  have hB := statopia_math_node_3459853827_bfe4599e rhoMinus h_rhoMinus_pos h_rhoMinus_le rho hrho_min hrho_le hA.1
  have hCont : Continuous (mpTail rho) := hB.1
  have hAnti : StrictAntiOn (mpTail rho) (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) := hB.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hA.1
  · exact hA.2.1
  · exact hTailZero
  · exact hCont
  · exact hAnti
  · intro n hn i
    exact statopia_math_node_3889982342_370fdb2e rhoMinus h_rhoMinus_pos h_rhoMinus_le rho hrho_min
      hrho_le hA.1 hA.2.1 hTailZero hCont hAnti n hn i
  · exact hmain rho hrho_min hrho_le
  /- @proof-region region.target-node.session.7365fd8e3c4a7b9a end -/

end Statlib.Imported

