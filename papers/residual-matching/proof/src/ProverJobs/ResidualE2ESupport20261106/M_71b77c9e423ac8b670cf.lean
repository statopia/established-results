import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_43e0fd7ab3637792100e

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
theorem statopia_math_node_1589508588_b622d3e8 : ∀ (rho x : ℝ) (hrho_pos : 0 < rho)
    (hrho_le : rho ≤ 1) (hx : 0 ≤ x)
    (hmass : ∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u = 1),
    (∫ u in Set.Iic x, (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2)
      = (1 + (∫ u in (mpLambdaMinus rho)..x, rootedMPDensity rho u)) / 2 := by
  /- @proof-region region.target-node.session.06fe99bb0ec50d8c begin -/
  intro rho x hrho_pos hrho_le hx hmass
  have hsqrt_nonneg : (0:ℝ) ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hsqrt_le_one : Real.sqrt rho ≤ 1 := by
    have h : Real.sqrt rho ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hrho_le
    simpa using h
  have ha_nonneg : (0:ℝ) ≤ mpLambdaMinus rho := by
    unfold mpLambdaMinus; linarith
  have hab : mpLambdaMinus rho ≤ mpLambdaPlus rho := by
    unfold mpLambdaMinus mpLambdaPlus; linarith
  have hν_out : ∀ u : ℝ, ¬ (mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho) → rootedMPDensity rho u = 0 := by
    intro u hu
    unfold rootedMPDensity
    rw [if_neg hu, mul_zero]
  have hν_at_a : rootedMPDensity rho (mpLambdaMinus rho) = 0 := by
    simp [rootedMPDensity]
  have hν_at_b : rootedMPDensity rho (mpLambdaPlus rho) = 0 := by
    simp [rootedMPDensity]
  have hν_le_a : ∀ u, u ≤ mpLambdaMinus rho → rootedMPDensity rho u = 0 := by
    intro u hu
    rcases lt_or_eq_of_le hu with h | h
    · exact hν_out u (by intro ⟨h1, _⟩; linarith)
    · rw [h]; exact hν_at_a
  have hν_ge_b_le : ∀ u, mpLambdaPlus rho ≤ u → rootedMPDensity rho u = 0 := by
    intro u hu
    rcases lt_or_eq_of_le hu with h | h
    · exact hν_out u (by intro ⟨_, h2⟩; linarith)
    · rw [← h]; exact hν_at_b
  have hIntν : Integrable (rootedMPDensity rho) := (statopia_math_node_39993368_ddc1c47b rho hrho_pos hrho_le).1
  have hIntneg : Integrable (fun u => rootedMPDensity rho (-u)) := (statopia_math_node_39993368_ddc1c47b rho hrho_pos hrho_le).2
  have hIic_zero : ∀ y, y ≤ mpLambdaMinus rho → ∫ u in Set.Iic y, rootedMPDensity rho u = 0 := by
    intro y hy
    have hzero : (fun u => rootedMPDensity rho u) =ᵐ[volume.restrict (Set.Iic y)] (0 : ℝ → ℝ) := by
      show ∀ᵐ u ∂(volume.restrict (Set.Iic y)), rootedMPDensity rho u = 0
      rw [ae_restrict_iff' measurableSet_Iic]
      filter_upwards with u hu
      exact hν_le_a u (le_trans hu hy)
    have h := MeasureTheory.integral_congr_ae hzero
    simpa using h
  have C1 : ∫ u in Set.Iic x, rootedMPDensity rho u = ∫ u in (mpLambdaMinus rho)..x, rootedMPDensity rho u := by
    have hIicA : IntegrableOn (rootedMPDensity rho) (Set.Iic (mpLambdaMinus rho)) volume := hIntν.integrableOn
    have hIicX : IntegrableOn (rootedMPDensity rho) (Set.Iic x) volume := hIntν.integrableOn
    have hsub := intervalIntegral.integral_Iic_sub_Iic hIicA hIicX
    rw [hIic_zero (mpLambdaMinus rho) le_rfl, sub_zero] at hsub
    exact hsub
  have C2 : ∫ u in Set.Iic x, rootedMPDensity rho (-u) = 1 := by
    have hSupp : Function.support (rootedMPDensity rho) ⊆ Set.Ioc (mpLambdaMinus rho) (mpLambdaPlus rho) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hmem : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho := by
        by_contra h
        exact hu (hν_out u h)
      rw [Set.mem_Ioc]
      refine ⟨?_, hmem.2⟩
      by_contra h
      push_neg at h
      exact hu (hν_le_a u h)
    have hfull : ∫ u in Set.Ioi (-x), rootedMPDensity rho u = ∫ u, rootedMPDensity rho u := by
      have hIic : IntegrableOn (rootedMPDensity rho) (Set.Iic (-x)) volume := hIntν.integrableOn
      have hIoi : IntegrableOn (rootedMPDensity rho) (Set.Ioi (-x)) volume := hIntν.integrableOn
      have hsplit := intervalIntegral.integral_Iic_add_Ioi (f := rootedMPDensity rho) (b := -x) hIic hIoi
      have hzero : ∫ u in Set.Iic (-x), rootedMPDensity rho u = 0 :=
        hIic_zero (-x) (by linarith [ha_nonneg, hx])
      rw [hzero, zero_add] at hsplit
      exact hsplit
    have hmass_full : ∫ u, rootedMPDensity rho u = 1 := by
      have h1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hSupp
      rw [← h1]
      exact hmass
    rw [integral_comp_neg_Iic x (rootedMPDensity rho), hfull, hmass_full]
  have hlin : ∫ u in Set.Iic x, (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2
      = ((∫ u in Set.Iic x, rootedMPDensity rho u) + (∫ u in Set.Iic x, rootedMPDensity rho (-u))) / 2 := by
    have hI1 : Integrable (fun u => rootedMPDensity rho u) (volume.restrict (Set.Iic x)) := hIntν.integrableOn
    have hI2 : Integrable (fun u => rootedMPDensity rho (-u)) (volume.restrict (Set.Iic x)) := hIntneg.integrableOn
    rw [integral_div, integral_add hI1 hI2] <;> rfl
  calc ∫ u in Set.Iic x, (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2
      = ((∫ u in Set.Iic x, rootedMPDensity rho u) + (∫ u in Set.Iic x, rootedMPDensity rho (-u))) / 2 := hlin
    _ = ((∫ u in (mpLambdaMinus rho)..x, rootedMPDensity rho u) + 1) / 2 := by rw [C1, C2]
    _ = (1 + (∫ u in (mpLambdaMinus rho)..x, rootedMPDensity rho u)) / 2 := by rw [add_comm]
  /- @proof-region region.target-node.session.06fe99bb0ec50d8c end -/

end Statlib.Imported

