import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Statlib.StatFoundation.Vocabulary.OrliczNorm
import Lean
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Vocabulary
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Base

namespace PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e

open _root_.PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1373677170_21fd32dd : ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (L : ℝ) (hL : 0 < L),
    HasSubgaussianMGF X ⟨L, hL.le⟩ μ →
      Statlib.StatFoundation.Vocabulary.subgaussianOrliczNorm X μ ≤
        ENNReal.ofReal (4 * (L + 1)) := by
  /- @proof-region region.target-node.session.53c4e29950287649 begin -/
  intro Ω _ μ _ X L hL hX
  unfold Statlib.StatFoundation.Vocabulary.subgaussianOrliczNorm
    Statlib.StatFoundation.Vocabulary.orliczNorm
    Statlib.StatFoundation.Vocabulary.psiOrlicz
  set T : ℝ := 4 * (L + 1) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; linarith
  have hkey : ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp ((|X ω| / T) ^ (2 : ℝ)) - 1) ∂μ ≤ 1 := by
    have hXint : Integrable X μ := hX.integrable
    have hXaem : AEMeasurable X μ := hXint.aestronglyMeasurable.aemeasurable
    have hexpint : ∀ t : ℝ, Integrable (fun ω : Ω => Real.exp (t * X ω)) μ := by
      have h := hX.integrableExpSet_eq_univ
      simp only [ProbabilityTheory.integrableExpSet, Set.eq_univ_iff_forall, Set.mem_setOf_eq] at h
      exact h
    cases hX
    have hm : ∀ t : ℝ, ∫ ω : Ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (L * t ^ 2 / 2) := by assumption
    have htail : ∀ s : ℝ, 0 < s → μ {ω : Ω | s ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-(s ^ 2) / (2 * L))) := by
      intro s hs
      have hsL : 0 < s / L := div_pos hs hL
      have hupper : μ {ω : Ω | s ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * L))) := by
        have h1 := Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.meas_ge_le_ofReal_integral_div μ
          (fun ω : Ω => Real.exp ((s / L) * X ω))
          (Filter.Eventually.of_forall fun ω => (Real.exp_pos ((s / L) * X ω)).le)
          (hexpint (s / L)) (Real.exp ((s / L) * s)) (Real.exp_pos _)
        have hset : {ω : Ω | Real.exp ((s / L) * s) ≤ Real.exp ((s / L) * X ω)} = {ω : Ω | s ≤ X ω} := by
          ext ω
          simp only [Set.mem_setOf_eq, Real.exp_le_exp]
          constructor
          · intro h; nlinarith
          · intro h; exact mul_le_mul_of_nonneg_left h hsL.le
        rw [hset] at h1
        have hnum : ∫ ω : Ω, Real.exp ((s / L) * X ω) ∂μ ≤ Real.exp (L * (s / L) ^ 2 / 2) := hm (s / L)
        refine le_trans h1 (ENNReal.ofReal_le_ofReal ?_)
        rw [div_le_iff₀ (Real.exp_pos _)]
        refine le_trans hnum (le_of_eq ?_)
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring
      have hlower : μ {ω : Ω | s ≤ -X ω} ≤ ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * L))) := by
        have h1 := Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.meas_ge_le_ofReal_integral_div μ
          (fun ω : Ω => Real.exp (-(s / L) * X ω))
          (Filter.Eventually.of_forall fun ω => (Real.exp_pos (-(s / L) * X ω)).le)
          (hexpint (-(s / L))) (Real.exp ((s / L) * s)) (Real.exp_pos _)
        have hset : {ω : Ω | Real.exp ((s / L) * s) ≤ Real.exp (-(s / L) * X ω)} = {ω : Ω | s ≤ -X ω} := by
          ext ω
          simp only [Set.mem_setOf_eq, Real.exp_le_exp]
          constructor
          · intro h; nlinarith
          · intro h; nlinarith
        rw [hset] at h1
        have hnum : ∫ ω : Ω, Real.exp (-(s / L) * X ω) ∂μ ≤ Real.exp (L * (-(s / L)) ^ 2 / 2) := hm (-(s / L))
        refine le_trans h1 (ENNReal.ofReal_le_ofReal ?_)
        rw [div_le_iff₀ (Real.exp_pos _)]
        refine le_trans hnum (le_of_eq ?_)
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring
      calc μ {ω : Ω | s ≤ |X ω|} ≤ μ ({ω : Ω | s ≤ X ω} ∪ {ω : Ω | s ≤ -X ω}) := by
            apply measure_mono
            intro ω h
            simp only [Set.mem_setOf_eq, Set.mem_union]
            by_cases hx : 0 ≤ X ω
            · left; simpa [abs_of_nonneg hx] using h
            · right; simpa [abs_of_neg (not_le.mp hx)] using h
        _ ≤ μ {ω : Ω | s ≤ X ω} + μ {ω : Ω | s ≤ -X ω} := measure_union_le _ _
        _ ≤ ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * L))) + ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * L))) := add_le_add hupper hlower
        _ = ENNReal.ofReal (2 * Real.exp (-(s ^ 2) / (2 * L))) := by
            have hp1 : (0:ℝ) ≤ Real.exp (-(s ^ 2) / (2 * L)) := (Real.exp_pos _).le
            rw [← ENNReal.ofReal_add hp1 hp1]
            congr 1
            ring
    obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = T ^ 2 / (2 * L) - 1 := ⟨_, rfl⟩
    have hb31 : 31 ≤ b := by
      rw [hbdef]
      have hc32 : 32 ≤ T ^ 2 / (2 * L) := by
        rw [hTdef, le_div_iff₀ (by positivity : (0:ℝ) < 2 * L)]
        nlinarith [sq_nonneg (L - 1)]
      linarith
    have hbpos : 0 < b := by linarith
    have hsqpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbpos
    have hmeas_le : ∀ t : ℝ, 0 < t → μ {a : Ω | t ≤ |X a| / T} ≤ ENNReal.ofReal (2 * Real.exp (-(b + 1) * t ^ 2)) := by
      intro t ht
      have h1 := htail (T * t) (by positivity)
      have hset : {a : Ω | t ≤ |X a| / T} = {a : Ω | T * t ≤ |X a|} := by
        ext a
        simp only [Set.mem_setOf_eq]
        rw [le_div_iff₀ hTpos]
        constructor <;> intro h <;> linarith
      rw [hset]
      refine le_trans h1 (ENNReal.ofReal_le_ofReal ?_)
      have hexp : -((T * t) ^ 2) / (2 * L) = -(b + 1) * t ^ 2 := by
        have hb1 : b + 1 = T ^ 2 / (2 * L) := by rw [hbdef]; ring
        rw [hb1]
        field_simp
      rw [hexp]
    have hdom : ∀ t : ℝ, 0 < t → 4 * t * Real.exp (-b * t ^ 2) ≤ (4 / Real.sqrt b) * Real.exp (-(b / 2) * t ^ 2) := by
      intro t ht
      have haux : ∀ u : ℝ, 0 ≤ u → u * Real.exp (-(u ^ 2) / 2) ≤ 1 := by
        intro u _
        have h1 : u ≤ 1 + u ^ 2 / 2 := by nlinarith [sq_nonneg (u - 1)]
        have h2 : 1 + u ^ 2 / 2 ≤ Real.exp (u ^ 2 / 2) := by
          have hh := Real.add_one_le_exp (u ^ 2 / 2)
          linarith
        have h3 : u ≤ Real.exp (u ^ 2 / 2) := le_trans h1 h2
        have h4 : 0 < Real.exp (-(u ^ 2) / 2) := Real.exp_pos _
        calc u * Real.exp (-(u ^ 2) / 2) ≤ Real.exp (u ^ 2 / 2) * Real.exp (-(u ^ 2) / 2) :=
              mul_le_mul_of_nonneg_right h3 h4.le
          _ = Real.exp (u ^ 2 / 2 + -(u ^ 2) / 2) := by rw [Real.exp_add]
          _ = 1 := by rw [show u ^ 2 / 2 + -(u ^ 2) / 2 = 0 by ring, Real.exp_zero]
      have hu : 0 ≤ Real.sqrt b * t := mul_nonneg hsqpos.le ht.le
      have hb1' := haux (Real.sqrt b * t) hu
      have hsq2 : (Real.sqrt b * t) ^ 2 = b * t ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hbpos.le]
      rw [hsq2, show -(b * t ^ 2) / 2 = -(b / 2) * t ^ 2 by ring] at hb1'
      set E : ℝ := Real.exp (-(b / 2) * t ^ 2) with hEdef
      have hEpos : 0 < E := Real.exp_pos _
      have hstep : t * E ≤ 1 / Real.sqrt b := by
        rw [le_div_iff₀ hsqpos]
        nlinarith [hb1']
      have hsplit : Real.exp (-b * t ^ 2) = E * E := by
        rw [hEdef, show -b * t ^ 2 = -(b / 2) * t ^ 2 + -(b / 2) * t ^ 2 by ring, Real.exp_add]
      calc 4 * t * Real.exp (-b * t ^ 2) = 4 * (t * E) * E := by rw [hsplit]; ring
        _ ≤ 4 * (1 / Real.sqrt b) * E := by
            have h4E : (0:ℝ) ≤ 4 * E := mul_nonneg (by norm_num) hEpos.le
            have h1 : 4 * (t * E) * E = (4 * E) * (t * E) := by ring
            have h2 : 4 * (1 / Real.sqrt b) * E = (4 * E) * (1 / Real.sqrt b) := by ring
            rw [h1, h2]
            exact mul_le_mul_of_nonneg_left hstep h4E
        _ = (4 / Real.sqrt b) * Real.exp (-(b / 2) * t ^ 2) := by rw [hEdef]; ring
    have hFTC : ∀ u : ℝ, ∫ t in (0:ℝ)..u, 2 * t * Real.exp (t ^ 2) = Real.exp (u ^ 2) - 1 := by
      intro u
      have hder : ∀ x ∈ Set.Ioo (min (0:ℝ) u) (max (0:ℝ) u), HasDerivAt (fun t : ℝ => Real.exp (t ^ 2)) (2 * x * Real.exp (x ^ 2)) x := by
        intro x _
        have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have h2 := h1.exp
        convert h2 using 1
        ring
      have hmain := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
        (u := fun t : ℝ => Real.exp (t ^ 2)) (v := fun _ : ℝ => (1:ℝ))
        (u' := fun t : ℝ => 2 * t * Real.exp (t ^ 2)) (v' := fun _ : ℝ => (0:ℝ))
        (a := (0:ℝ)) (b := u)
        (by fun_prop) continuous_const.continuousOn hder
        (fun x _ => hasDerivAt_const x 1)
        (by
          have hc : Continuous fun t : ℝ => 2 * t * Real.exp (t ^ 2) := by fun_prop
          exact hc.intervalIntegrable 0 u)
        (continuous_const.intervalIntegrable (0:ℝ) u)
      simpa using hmain
    have hgcont : Continuous fun t : ℝ => 2 * t * Real.exp (t ^ 2) := by fun_prop
    have hfaem : AEMeasurable (fun ω : Ω => |X ω| / T) μ := by
      have h0 : AEMeasurable X μ := hXaem
      measurability
    have hfnn : 0 ≤ᵐ[μ] (fun ω : Ω => |X ω| / T) :=
      Filter.Eventually.of_forall fun ω => div_nonneg (abs_nonneg _) hTpos.le
    have hgcake := MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul (μ := μ)
      (f := fun ω : Ω => |X ω| / T) (g := fun t : ℝ => 2 * t * Real.exp (t ^ 2))
      hfnn hfaem (fun t _ => hgcont.intervalIntegrable 0 t)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        have hpos : 0 < t := ht
        positivity)
    have hstep1 : ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp ((|X ω| / T) ^ (2 : ℝ)) - 1) ∂μ
        = ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a : Ω | t ≤ |X a| / T} * ENNReal.ofReal (2 * t * Real.exp (t ^ 2)) := by
      rw [← hgcake]
      refine lintegral_congr (fun ω => ?_)
      rw [hFTC (|X ω| / T), Real.rpow_two]
    have hmid : ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a : Ω | t ≤ |X a| / T} * ENNReal.ofReal (2 * t * Real.exp (t ^ 2))
        ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal (4 * t * Real.exp (-b * t ^ 2)) := by
      calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a : Ω | t ≤ |X a| / T} * ENNReal.ofReal (2 * t * Real.exp (t ^ 2))
          ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal (2 * Real.exp (-(b + 1) * t ^ 2)) * ENNReal.ofReal (2 * t * Real.exp (t ^ 2)) := by
            apply lintegral_mono
            intro t
            dsimp only
            by_cases ht : 0 < t
            · exact mul_le_mul (hmeas_le t ht) (le_refl _) (zero_le _) (zero_le _)
            · rw [show ENNReal.ofReal (2 * t * Real.exp (t ^ 2)) = 0 from ?_]
              · simp
              · apply ENNReal.ofReal_eq_zero.mpr
                have hE : 0 < Real.exp (t ^ 2) := Real.exp_pos _
                nlinarith
        _ = ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal (4 * t * Real.exp (-b * t ^ 2)) := by
            apply lintegral_congr
            intro t
            dsimp only
            have hexp : Real.exp (-(b + 1) * t ^ 2) * Real.exp (t ^ 2) = Real.exp (-b * t ^ 2) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            calc 2 * Real.exp (-(b + 1) * t ^ 2) * (2 * t * Real.exp (t ^ 2))
                = 4 * t * (Real.exp (-(b + 1) * t ^ 2) * Real.exp (t ^ 2)) := by ring
              _ = 4 * t * Real.exp (-b * t ^ 2) := by rw [hexp]
    have hfinal : ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal (4 * t * Real.exp (-b * t ^ 2)) ≤ 1 := by
      have hcmp : ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal (4 * t * Real.exp (-b * t ^ 2))
          ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal ((4 / Real.sqrt b) * Real.exp (-(b / 2) * t ^ 2)) := by
        apply lintegral_mono
        intro t
        dsimp only
        rcases lt_trichotomy t 0 with ht | ht | ht
        · have hE : 0 < Real.exp (-b * t ^ 2) := Real.exp_pos _
          have hneg : 4 * t * Real.exp (-b * t ^ 2) < 0 := by nlinarith
          rw [ENNReal.ofReal_eq_zero.mpr hneg.le]
          exact zero_le _
        · subst ht
          simp
        · exact ENNReal.ofReal_le_ofReal (hdom t ht)
      refine le_trans hcmp ?_
      have hIntOn : IntegrableOn (fun t : ℝ => (4 / Real.sqrt b) * Real.exp (-(b / 2) * t ^ 2)) (Set.Ioi 0) :=
        ((integrable_exp_neg_mul_sq (show (0:ℝ) < b / 2 by linarith)).const_mul (4 / Real.sqrt b)).integrableOn
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntOn
        (Filter.Eventually.of_forall fun t => mul_nonneg (by positivity) (Real.exp_pos _).le)]
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have hpi : Real.pi / (b / 2) ≤ 1 := by
        rw [div_le_one (by linarith)]
        nlinarith [Real.pi_le_four]
      have hs1 : Real.sqrt (Real.pi / (b / 2)) ≤ 1 := Real.sqrt_le_one.mpr hpi
      have h4 : (2:ℝ) ≤ Real.sqrt b := by
        nlinarith [Real.sq_sqrt hbpos.le, Real.sqrt_nonneg b]
      have hfac : (0:ℝ) ≤ 4 / Real.sqrt b := by positivity
      have hcv : ∫ (t : ℝ) in Set.Ioi 0, (4 / Real.sqrt b) * Real.exp (-(b / 2) * t ^ 2)
          = (4 / Real.sqrt b) * (Real.sqrt (Real.pi / (b / 2)) / 2) := by
        rw [MeasureTheory.integral_const_mul, integral_gaussian_Ioi]
      rw [hcv]
      calc (4 / Real.sqrt b) * (Real.sqrt (Real.pi / (b / 2)) / 2)
          ≤ (4 / Real.sqrt b) * (1 / 2) := by
            apply mul_le_mul_of_nonneg_left _ hfac
            linarith
        _ = 2 / Real.sqrt b := by ring
        _ ≤ 1 := by
            rw [div_le_iff₀ hsqpos]
            linarith
    calc ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp ((|X ω| / T) ^ (2 : ℝ)) - 1) ∂μ
        = ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a : Ω | t ≤ |X a| / T} * ENNReal.ofReal (2 * t * Real.exp (t ^ 2)) := hstep1
      _ ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal (4 * t * Real.exp (-b * t ^ 2)) := hmid
      _ ≤ 1 := hfinal
  refine sInf_le ?_
  constructor
  · exact ENNReal.ofReal_pos.mpr hTpos
  · rw [ENNReal.toReal_ofReal hTpos.le]
    exact hkey
  /- @proof-region region.target-node.session.53c4e29950287649 end -/

end

end Statlib.Imported

