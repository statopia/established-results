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
theorem statopia_math_node_763568752_c90d820b : ∀ (rho : ℝ) (hrho_pos : 0 < rho) (hrho_le : rho ≤ 1)
    (hnorm : ∫ x in Set.Icc (lambdaMinus rho) (lambdaPlus rho), nuRho rho x = 1)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin n),
    ∃! gamma : ℝ,
      (∫ x in Set.Icc gamma (lambdaPlus rho), nuRho rho x)
        = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) := by
  /- @proof-region region.target-node.session.16a0b5d84a4a71f7 begin -/
  intro rho hrho_pos hrho_le hnorm n hn i
  let a : ℝ := lambdaMinus rho
  let b : ℝ := lambdaPlus rho
  change ∃! gamma : ℝ, (∫ x in Set.Icc gamma b, nuRho rho x) = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ)
  have hsqrt_le : Real.sqrt rho ≤ 1 := by
    have h := Real.sqrt_le_sqrt hrho_le
    simpa using h
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
  have ha_nn : 0 ≤ a := by
    show 0 ≤ lambdaMinus rho
    simp only [lambdaMinus]
    linarith
  have hb_pos : 0 < b := by
    show 0 < lambdaPlus rho
    simp only [lambdaPlus]
    linarith
  have hab : a ≤ b := by
    show lambdaMinus rho ≤ lambdaPlus rho
    simp only [lambdaMinus, lambdaPlus]
    linarith
  have hnorm' : (∫ x in Set.Icc a b, nuRho rho x) = 1 := hnorm
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hLpos : 0 < (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) := by
    exact div_pos (by linarith) hnR
  have hLlt1 : (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) < 1 := by
    have hi1 : ((i : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
      have h2 : (i : ℕ) + 1 ≤ n := by omega
      exact_mod_cast h2
    rw [div_lt_one hnR]
    linarith
  have hpi_pos : (0:ℝ) < Real.pi := Real.pi_pos
  have hnu_meas : Measurable (nuRho rho) := by
    have hp : MeasurableSet {x : ℝ | lambdaMinus rho ≤ x ∧ x ≤ lambdaPlus rho} := by
      measurability
    have hf : Measurable (fun x : ℝ =>
        Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)) /
          (Real.pi * rho * x)) := by
      measurability
    unfold nuRho
    exact Measurable.ite hp hf measurable_const
  have hnu_bound : ∀ x : ℝ, ‖nuRho rho x‖ ≤ b / (Real.pi * rho) := by
    intro x
    have hnn : (0:ℝ) ≤ b / (Real.pi * rho) := div_nonneg hb_pos.le (mul_pos hpi_pos hrho_pos).le
    unfold nuRho
    split_ifs with hx
    · obtain ⟨hxa, hxb⟩ := hx
      have hx0 : 0 ≤ x := le_trans ha_nn hxa
      rcases lt_or_eq_of_le hx0 with hxpos | hxzero
      · have hxsq : x ^ 2 ≤ b ^ 2 := by nlinarith
        have hasq : a ^ 2 ≤ x ^ 2 := by nlinarith
        have hden : (0:ℝ) < Real.pi * rho * x := mul_pos (mul_pos hpi_pos hrho_pos) hxpos
        have hkey : Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - a ^ 2)) ≤ b * x := by
          have h1 : Real.sqrt ((b ^ 2 - x ^ 2) * (x ^ 2 - a ^ 2)) ≤ Real.sqrt (b ^ 2 * x ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith
          have h2 : Real.sqrt (b ^ 2 * x ^ 2) = b * x := by
            rw [Real.sqrt_mul (by positivity)]
            rw [Real.sqrt_sq hb_pos.le, Real.sqrt_sq hxpos.le]
          rwa [h2] at h1
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hden.le)]
        rw [div_le_iff₀ hden]
        have h4 : b / (Real.pi * rho) * (Real.pi * rho * x) = b * x := by
          rw [← mul_assoc, div_mul_cancel₀ b (ne_of_gt (mul_pos hpi_pos hrho_pos))]
        rw [h4]
        exact hkey
      · rw [← hxzero]
        simpa using hnn
    · rw [norm_zero]
      linarith
  have hIIon : ∀ c d : ℝ, IntegrableOn (fun x : ℝ => nuRho rho x) (Set.uIcc c d) volume := by
    intro c d
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc (min c d) (max c d))) :=
      Real.isFiniteMeasure_restrict_Icc (min c d) (max c d)
    have hfin : volume (Set.Icc (min c d) (max c d)) < ⊤ := by
      rw [← MeasureTheory.Measure.restrict_apply_univ (μ := volume) (Set.Icc (min c d) (max c d))]
      exact IsFiniteMeasure.measure_univ_lt_top
    exact MeasureTheory.IntegrableOn.of_bound hfin hnu_meas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hnu_bound)
  have hII : ∀ c d : ℝ, IntervalIntegrable (nuRho rho) volume c d := by
    intro c d
    exact MeasureTheory.IntegrableOn.intervalIntegrable (hIIon c d)
  have hnu_pos : ∀ x : ℝ, a < x → x < b → 0 < nuRho rho x := by
    intro x hxa hxb
    have hxpos : 0 < x := lt_of_le_of_lt ha_nn hxa
    unfold nuRho
    rw [if_pos ⟨le_of_lt hxa, le_of_lt hxb⟩]
    apply div_pos
    · apply Real.sqrt_pos.mpr
      apply mul_pos
      · nlinarith
      · nlinarith
    · exact mul_pos (mul_pos hpi_pos hrho_pos) hxpos
  have hnu_zero : ∀ x : ℝ, x ≤ a → nuRho rho x = 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx with h | h
    · unfold nuRho
      rw [if_neg (by rintro ⟨h1, _⟩; exact absurd h1 (not_le.mpr h))]
    · rw [h]
      unfold nuRho
      rw [if_pos ⟨le_rfl, hab⟩]
      have hz : a ^ 2 - lambdaMinus rho ^ 2 = 0 := by
        show lambdaMinus rho ^ 2 - lambdaMinus rho ^ 2 = 0
        ring
      rw [hz, mul_zero, Real.sqrt_zero, zero_div]
  have hbridge : ∀ gamma : ℝ, gamma ≤ b →
      (∫ x in Set.Icc gamma b, nuRho rho x) = ∫ x in gamma..b, nuRho rho x := by
    intro gamma hgamma
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [intervalIntegral.integral_of_le hgamma]
  have hFa : (∫ x in a..b, nuRho rho x) = 1 := by
    rw [← hbridge a hab]
    exact hnorm'
  have hFb : (∫ x in b..b, nuRho rho x) = 0 := by
    simp
  have hFcont : ContinuousOn (fun gamma : ℝ => ∫ x in gamma..b, nuRho rho x) (Set.Icc a b) := by
    have hcontU : ContinuousOn (fun gamma : ℝ => ∫ x in gamma..b, nuRho rho x) (Set.uIcc a b) :=
      intervalIntegral.continuousOn_primitive_interval_left (f := fun x : ℝ => nuRho rho x)
        (hIIon a b)
    exact hcontU.mono (fun x hx =>
      ⟨le_trans (min_le_left a b) hx.1, le_trans hx.2 (le_max_right a b)⟩)
  have hFstrict : ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s < t →
      (∫ x in t..b, nuRho rho x) < ∫ x in s..b, nuRho rho x := by
    intro s hs t ht hst
    have hpos : 0 < ∫ x in s..t, nuRho rho x := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on (hII s t)
      · intro x hx
        exact hnu_pos x (lt_trans hs.1 hx.1) (lt_trans hx.2 ht.2)
      · exact hst
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hII s t) (hII t b)
    linarith
  have hex : ∃ gamma ∈ Set.Icc a b,
      (∫ x in gamma..b, nuRho rho x) = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) := by
    have hmem : (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) ∈
        (fun gamma : ℝ => ∫ x in gamma..b, nuRho rho x) '' Set.Icc a b := by
      apply intermediate_value_Icc' hab hFcont
      constructor
      · show ∫ x in b..b, nuRho rho x ≤ (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ)
        rw [hFb]
        exact le_of_lt hLpos
      · show (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) ≤ ∫ x in a..b, nuRho rho x
        rw [hFa]
        exact le_of_lt hLlt1
    exact hmem
  obtain ⟨gamma0, hgamma0mem, hgamma0eq⟩ := hex
  have hg0a : a < gamma0 := by
    rcases lt_or_eq_of_le hgamma0mem.1 with h | h
    · exact h
    · exfalso
      rw [← h, hFa] at hgamma0eq
      linarith
  have hg0b : gamma0 < b := by
    rcases lt_or_eq_of_le hgamma0mem.2 with h | h
    · exact h
    · exfalso
      rw [h, hFb] at hgamma0eq
      linarith
  refine ⟨gamma0, ?_, ?_⟩
  · show (∫ x in Set.Icc gamma0 b, nuRho rho x) = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ)
    rw [hbridge gamma0 (le_of_lt hg0b)]
    exact hgamma0eq
  · intro y hy
    have hy' : (∫ x in Set.Icc y b, nuRho rho x) = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) := hy
    rcases lt_or_ge y b with hyb | hyb
    · have hyF : (∫ x in y..b, nuRho rho x) = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) := by
        rw [← hbridge y (le_of_lt hyb)]
        exact hy'
      by_cases hya : y ≤ a
      · have hya1 : (∫ x in y..b, nuRho rho x) = 1 := by
          have hza : (∫ x in y..a, nuRho rho x) = 0 := by
            have h0 : (∫ x in y..a, nuRho rho x) = ∫ x in y..a, (0:ℝ) := by
              apply intervalIntegral.integral_congr
              intro x hx
              show nuRho rho x = (0:ℝ)
              exact hnu_zero x (by
                have h1 : x ≤ max y a := hx.2
                rwa [max_eq_right hya] at h1)
            rw [h0]
            simp
          have h1 := intervalIntegral.integral_add_adjacent_intervals (hII y a) (hII a b)
          rw [hza, hFa] at h1
          linarith
        rw [hya1] at hyF
        linarith
      · have hya' : a < y := not_le.mp hya
        have hyIoo : y ∈ Set.Ioo a b := ⟨hya', hyb⟩
        rcases lt_trichotomy y gamma0 with h | h | h
        · have hlt := hFstrict y hyIoo gamma0 ⟨hg0a, hg0b⟩ h
          rw [hyF, hgamma0eq] at hlt
          linarith
        · exact h
        · have hlt := hFstrict gamma0 ⟨hg0a, hg0b⟩ y hyIoo h
          rw [hyF, hgamma0eq] at hlt
          linarith
    · rcases lt_or_eq_of_le hyb with hb' | hb'
      · exfalso
        have hempty : Set.Icc y b = ∅ := by
          ext x
          constructor
          · rintro ⟨h1, h2⟩
            exact absurd h2 (not_le.mpr (lt_of_lt_of_le hb' h1))
          · intro h
            exact absurd h (by simp)
        rw [hempty] at hy'
        simp at hy'
        linarith
      · exfalso
        rw [← hb'] at hy'
        have hzero : (∫ x in b..b, nuRho rho x) = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) := by
          rw [← hbridge b le_rfl]
          exact hy'
        rw [hFb] at hzero
        linarith
  /- @proof-region region.target-node.session.16a0b5d84a4a71f7 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_763568752_c90d820b


