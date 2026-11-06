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
theorem statopia_math_node_39993368_ddc1c47b : ∀ (rho : ℝ) (hrho_pos : 0 < rho) (hrho_le : rho ≤ 1),
    MeasureTheory.Integrable (Statlib.Imported.rootedMPDensity rho) MeasureTheory.volume ∧
      MeasureTheory.Integrable
        (fun u : ℝ => Statlib.Imported.rootedMPDensity rho (-u)) MeasureTheory.volume := by
  /- @proof-region region.target-node.session.5d4c2bfab3ea1440 begin -/
  intro rho hrho_pos hrho_le
  have hsqrt_le_one : Real.sqrt rho ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hrho_le
  have ha_nonneg : 0 ≤ mpLambdaMinus rho := by
    simp only [mpLambdaMinus]
    linarith
  have hb_pos : 0 < mpLambdaPlus rho := by
    simp only [mpLambdaPlus]
    have hs := Real.sqrt_nonneg rho
    linarith
  have hbrho_nonneg : 0 ≤ mpLambdaPlus rho / rho := div_nonneg hb_pos.le hrho_pos.le
  have hC_nonneg : 0 ≤ (1 / Real.pi) * (mpLambdaPlus rho / rho) :=
    mul_nonneg (by positivity) hbrho_nonneg
  have hbound : ∀ u : ℝ, ‖rootedMPDensity rho u‖ ≤ (1 / Real.pi) * (mpLambdaPlus rho / rho) := by
    intro u
    simp only [rootedMPDensity]
    by_cases hu : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho
    · rw [if_pos hu, mul_one]
      rcases lt_or_ge 0 u with hu_pos | hu_nonpos
      · have hfac1 : 0 ≤ mpLambdaPlus rho ^ 2 - u ^ 2 := by
          have h1 : 0 ≤ mpLambdaPlus rho - u := by linarith [hu.2]
          have h2 : 0 ≤ mpLambdaPlus rho + u := by linarith
          nlinarith [mul_nonneg h1 h2]
        have hfac2 : 0 ≤ u ^ 2 - mpLambdaMinus rho ^ 2 := by
          have h1 : 0 ≤ u - mpLambdaMinus rho := by linarith [hu.1]
          have h2 : 0 ≤ u + mpLambdaMinus rho := by linarith
          nlinarith [mul_nonneg h1 h2]
        have hle1 : mpLambdaPlus rho ^ 2 - u ^ 2 ≤ mpLambdaPlus rho ^ 2 := by
          nlinarith [sq_nonneg u]
        have hle2 : u ^ 2 - mpLambdaMinus rho ^ 2 ≤ u ^ 2 := by
          nlinarith [sq_nonneg (mpLambdaMinus rho)]
        have hsq1 : Real.sqrt (mpLambdaPlus rho ^ 2 - u ^ 2) ≤ mpLambdaPlus rho := by
          calc Real.sqrt (mpLambdaPlus rho ^ 2 - u ^ 2) ≤ Real.sqrt (mpLambdaPlus rho ^ 2) :=
                Real.sqrt_le_sqrt hle1
            _ = mpLambdaPlus rho := Real.sqrt_sq hb_pos.le
        have hsq2 : Real.sqrt (u ^ 2 - mpLambdaMinus rho ^ 2) ≤ u := by
          calc Real.sqrt (u ^ 2 - mpLambdaMinus rho ^ 2) ≤ Real.sqrt (u ^ 2) :=
                Real.sqrt_le_sqrt hle2
            _ = u := Real.sqrt_sq hu_pos.le
        have hprod : Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) ≤
            mpLambdaPlus rho * u := by
          rw [Real.sqrt_mul hfac1]
          exact mul_le_mul hsq1 hsq2 (Real.sqrt_nonneg _) hb_pos.le
        have hnonneg : 0 ≤ (1 / Real.pi) *
            Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u) :=
          div_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (mul_pos hrho_pos hu_pos).le
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        have h1 : (1 / Real.pi) *
              Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u)
            ≤ (1 / Real.pi) * (mpLambdaPlus rho * u) / (rho * u) := by
          gcongr
        have h2 : (1 / Real.pi) * (mpLambdaPlus rho * u) / (rho * u) =
            (1 / Real.pi) * (mpLambdaPlus rho / rho) := by
          have hru : rho * u ≠ 0 := ne_of_gt (mul_pos hrho_pos hu_pos)
          field_simp
        calc (1 / Real.pi) *
              Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u)
            ≤ (1 / Real.pi) * (mpLambdaPlus rho * u) / (rho * u) := h1
          _ = (1 / Real.pi) * (mpLambdaPlus rho / rho) := h2
      · have hu_zero : u = 0 := le_antisymm hu_nonpos (le_trans ha_nonneg hu.1)
        subst hu_zero
        have hz : (1 / Real.pi) *
              Real.sqrt ((mpLambdaPlus rho ^ 2 - (0 : ℝ) ^ 2) * ((0 : ℝ) ^ 2 - mpLambdaMinus rho ^ 2)) /
                (rho * (0 : ℝ)) = 0 := by
          simp
        rw [hz, norm_zero]
        exact hC_nonneg
    · rw [if_neg hu, mul_zero, norm_zero]
      exact hC_nonneg
  have hmeas : Measurable (rootedMPDensity rho) := by
    have hbase : Measurable fun u : ℝ =>
        (1 / Real.pi) *
          Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u) := by
      measurability
    have hind : Measurable (Set.indicator (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) (fun u : ℝ =>
        (1 / Real.pi) *
          Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u))) :=
      Measurable.indicator hbase measurableSet_Icc
    have heq : rootedMPDensity rho = Set.indicator (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho))
        (fun u : ℝ =>
          (1 / Real.pi) *
            Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u)) := by
      funext u
      by_cases hu : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho
      · have hu' : u ∈ Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho) := hu
        rw [Set.indicator_of_mem hu']
        simp only [rootedMPDensity, if_pos hu, mul_one]
      · have hu' : u ∉ Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho) := hu
        have hz : Set.indicator (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) (fun u : ℝ =>
            (1 / Real.pi) *
              Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u)) u = 0 := by
          simp [hu']
        rw [hz]
        simp only [rootedMPDensity, if_neg hu, mul_zero]
    rw [heq]
    exact hind
  have hmu : volume (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hsupp : Function.support (rootedMPDensity rho) ⊆ Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho) := by
    intro u hu
    by_contra h
    simp only [Set.mem_Icc] at h
    exact hu (by
      simp only [rootedMPDensity]
      rw [if_neg h, mul_zero])
  have hIntν : Integrable (rootedMPDensity rho) volume :=
    (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp).mp
      (MeasureTheory.IntegrableOn.of_bound hmu hmeas.aestronglyMeasurable _
        (Filter.Eventually.of_forall hbound))
  have hmeas_neg : Measurable (fun u : ℝ => -u) := measurable_neg
  have hmeas_refl : Measurable (fun u : ℝ => rootedMPDensity rho (-u)) := hmeas.comp hmeas_neg
  have hmu' : volume (Set.Icc (-(mpLambdaPlus rho)) (-(mpLambdaMinus rho))) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hsupp_refl : Function.support (fun u : ℝ => rootedMPDensity rho (-u)) ⊆
      Set.Icc (-(mpLambdaPlus rho)) (-(mpLambdaMinus rho)) := by
    intro u hu
    by_contra h
    simp only [Set.mem_Icc] at h
    have hb : ¬ (mpLambdaMinus rho ≤ -u ∧ -u ≤ mpLambdaPlus rho) := by
      rintro ⟨h1, h2⟩
      exact h ⟨by linarith, by linarith⟩
    exact hu (by
      simp only [rootedMPDensity]
      rw [if_neg hb, mul_zero])
  have hIntneg : Integrable (fun u : ℝ => rootedMPDensity rho (-u)) volume :=
    (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp_refl).mp
      (MeasureTheory.IntegrableOn.of_bound hmu' hmeas_refl.aestronglyMeasurable _
        (Filter.Eventually.of_forall fun u => hbound (-u)))
  exact ⟨hIntν, hIntneg⟩
  /- @proof-region region.target-node.session.5d4c2bfab3ea1440 end -/

end Statlib.Imported

