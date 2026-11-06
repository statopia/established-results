import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
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
theorem statopia_math_node_374445652_127c785c : ∀ (rho : ℝ) (hrho_pos : 0 < rho) (hrho_le : rho ≤ 1)
    (hmass : ∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u = 1),
    ∃ nuRho : Measure ℝ,
      IsFiniteMeasure nuRho ∧ nuRho Set.univ = 1 ∧
        ∀ x : ℝ,
          (nuRho (Set.Iic x)).toReal =
            ∫ u in Set.Iic x, (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2 := by
  /- @proof-region region.target-node.session.c03e57043110cb1f begin -/
  intro rho hrho_pos hrho_le hmass
  have hs0 : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hs1 : Real.sqrt rho ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hrho_le
  have hcd : mpLambdaMinus rho ≤ mpLambdaPlus rho := by
    unfold mpLambdaMinus mpLambdaPlus
    linarith
  have hc0 : 0 ≤ mpLambdaMinus rho := by
    unfold mpLambdaMinus
    linarith
  have hneg_le : -(mpLambdaPlus rho) ≤ -(mpLambdaMinus rho) := by linarith
  set g : ℝ → ℝ := fun u => (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2 with hg
  have hν_left : rootedMPDensity rho (mpLambdaMinus rho) = 0 := by
    unfold rootedMPDensity
    simp [hcd]
  have hν_right : rootedMPDensity rho (mpLambdaPlus rho) = 0 := by
    unfold rootedMPDensity
    simp [hcd]
  have hzero_off : ∀ u : ℝ, u ≤ mpLambdaMinus rho ∨ mpLambdaPlus rho ≤ u → rootedMPDensity rho u = 0 := by
    intro u hu
    rcases hu with hu | hu
    · rcases lt_or_eq_of_le hu with h | h
      · unfold rootedMPDensity
        rw [if_neg (by rintro ⟨h1, h2⟩; linarith)]
        ring
      · rw [h]
        exact hν_left
    · rcases lt_or_eq_of_le hu with h | h
      · unfold rootedMPDensity
        rw [if_neg (by rintro ⟨h1, h2⟩; linarith)]
        ring
      · rw [← h]
        exact hν_right
  have hν_nonneg : ∀ u : ℝ, 0 ≤ rootedMPDensity rho u := by
    intro u
    unfold rootedMPDensity
    split_ifs with h
    · have hnum : 0 ≤ (1 / Real.pi) *
          Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) :=
        mul_nonneg (by positivity) (Real.sqrt_nonneg _)
      have hden : 0 ≤ rho * u := mul_nonneg (le_of_lt hrho_pos) (le_trans hc0 h.1)
      simpa using div_nonneg hnum hden
    · simp
  have hg_pt : ∀ u : ℝ, g u = (1 / 2 : ℝ) * (rootedMPDensity rho u + rootedMPDensity rho (-u)) := by
    intro u
    have hval : g u = (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2 := by
      rw [hg]
    rw [hval]
    ring
  have hsuppν : ∀ u : ℝ, u ∉ Set.Ioc (mpLambdaMinus rho) (mpLambdaPlus rho) →
      rootedMPDensity rho u = 0 := by
    intro u hu
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
    rcases hu with h | h
    · exact hzero_off u (Or.inl h)
    · exact hzero_off u (Or.inr (le_of_lt h))
  have hsuppνneg : ∀ u : ℝ, u ∉ Set.Ioc (-(mpLambdaPlus rho)) (-(mpLambdaMinus rho)) →
      rootedMPDensity rho (-u) = 0 := by
    intro u hu
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
    apply hzero_off
    rcases hu with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  have hIntIoc_val : ∫ u in Set.Ioc (mpLambdaMinus rho) (mpLambdaPlus rho), rootedMPDensity rho u = 1 := by
    rw [← intervalIntegral.integral_of_le hcd]
    exact hmass
  have hIntIoc_val_neg :
      ∫ u in Set.Ioc (-(mpLambdaPlus rho)) (-(mpLambdaMinus rho)), rootedMPDensity rho (-u) = 1 := by
    rw [← intervalIntegral.integral_of_le hneg_le]
    rw [intervalIntegral.integral_comp_neg]
    simpa using hmass
  have key : ∀ (f : ℝ → ℝ) (p q : ℝ), p ≤ q → (∀ u : ℝ, u ∉ Set.Ioc p q → f u = 0) →
      (∫ u in Set.Ioc p q, f u = 1) → Integrable f volume ∧ ∫ u, f u = 1 := by
    intro f p q hpq hz hint
    have hI : IntegrableOn f (Set.Ioc p q) volume := by
      by_contra hcon
      have h0 : ∫ u in Set.Ioc p q, f u = 0 := MeasureTheory.integral_undef hcon
      rw [h0] at hint
      exact one_ne_zero hint.symm
    have hae : f =ᵐ[volume] (Set.Ioc p q).indicator f := by
      filter_upwards with u
      by_cases hu : u ∈ Set.Ioc p q
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, hz u hu]
    have hind : Integrable ((Set.Ioc p q).indicator f) volume :=
      (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).mpr hI
    refine ⟨hind.congr hae.symm, ?_⟩
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_indicator measurableSet_Ioc]
    exact hint
  have hν := key (rootedMPDensity rho) (mpLambdaMinus rho) (mpLambdaPlus rho) hcd hsuppν hIntIoc_val
  have hνneg := key (fun u => rootedMPDensity rho (-u)) (-(mpLambdaPlus rho)) (-(mpLambdaMinus rho))
    hneg_le hsuppνneg hIntIoc_val_neg
  have hg_int : Integrable g volume := by
    rw [hg]
    simpa only [Pi.add_apply] using (hν.1.add hνneg.1).div_const 2
  have hg_nonneg_pt : ∀ u : ℝ, 0 ≤ g u := by
    intro u
    rw [hg_pt u]
    have h1 := hν_nonneg u
    have h2 := hν_nonneg (-u)
    nlinarith
  have hg_val : ∫ u, g u = 1 := by
    simp only [hg_pt]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hν.1 hνneg.1, hν.2, hνneg.2]
    norm_num
  refine ⟨volume.withDensity fun u => ENNReal.ofReal (g u), ?_, ?_, ?_⟩
  · refine MeasureTheory.isFiniteMeasure_withDensity ?_
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_int
      (Filter.Eventually.of_forall hg_nonneg_pt), hg_val]
    simp
  · have h1 : (volume.withDensity fun u => ENNReal.ofReal (g u)) Set.univ
        = ∫⁻ u, ENNReal.ofReal (g u) := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h1, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_int
      (Filter.Eventually.of_forall hg_nonneg_pt), hg_val]
    simp
  · intro x
    have h1 : (volume.withDensity fun u => ENNReal.ofReal (g u)) (Set.Iic x)
        = ∫⁻ u in Set.Iic x, ENNReal.ofReal (g u) := by
      rw [withDensity_apply _ measurableSet_Iic]
    rw [h1]
    exact Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
      (Filter.Eventually.of_forall hg_nonneg_pt) hg_int.integrableOn
  /- @proof-region region.target-node.session.c03e57043110cb1f end -/

end Statlib.Imported

