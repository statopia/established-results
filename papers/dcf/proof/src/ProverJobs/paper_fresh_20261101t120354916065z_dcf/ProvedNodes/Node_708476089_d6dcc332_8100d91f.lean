import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Vocabulary
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Base
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.ProvedNodes.Node_1953254498_13530db2_5c1c557a
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.ExternalNodes.Node_103826e30030eda123b2

namespace PaperProofTasks.paper_fresh_20261101t120354916065z_dcf


open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261101t120354916065z_dcf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_708476089_d6dcc332 : ∀ (p N : ℕ) (hp : 2 ≤ p) (hN : 1 ≤ N)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B C1 c t : ℝ) (hB : 1 ≤ B) (hC1 : 0 < C1) (hcpos : 0 < c) (hclt : c < 1)
    (ht : 0 < t)
    (ξ ζ : Fin N → Ω → ℝ)
    (hξ_meas : ∀ i, Measurable (ξ i)) (hξ_nonneg : ∀ i, ∀ ω, 0 ≤ ξ i ω)
    (hζ_meas : ∀ i, Measurable (ζ i)) (hζ_nonneg : ∀ i, ∀ ω, 0 ≤ ζ i ω)
    (hξ_tail : ∀ (i : Fin N) (s : ℝ), 0 ≤ s →
      (P {ω : Ω | ξ i ω > s}).toReal ≤ 2 * (p : ℝ) * Real.exp (-(s / B)))
    (hζ_tail : ∀ (i : Fin N) (s : ℝ), 0 ≤ s →
      (P {ω : Ω | ζ i ω > s}).toReal ≤ 2 * (p : ℝ) * Real.exp (-(s ^ 2) / (2 * c * B ^ 2)))
    (hC : 3 * B * Real.log ((p : ℝ) * (N : ℝ)) ≤ t)
    (hD : 3 * Real.log ((p : ℝ) * (N : ℝ)) ≤ t ^ 2 / (2 * c * B ^ 2))
    (hE : t + B ≤ C1 * Real.sqrt (N : ℝ))
    (hsqrtc : Real.sqrt c ≤ 1),
    (∀ i, Integrable (fun ω => (ξ i ω) ^ 3) P) ∧
      (∀ i, Integrable (fun ω => (ζ i ω) ^ 3) P) ∧
        (1 / (N : ℝ)) * ∑ i : Fin N,
            ∫ ω, (ξ i ω) ^ 3 * (if ξ i ω > t then (1 : ℝ) else 0) ∂P
          ≤ 12 * C1 ^ 3 / Real.sqrt (N : ℝ) ∧
          (1 / (N : ℝ)) * ∑ i : Fin N,
              ∫ ω, (ζ i ω) ^ 3 * (if ζ i ω > t then (1 : ℝ) else 0) ∂P
            ≤ 20 * C1 ^ 3 / Real.sqrt (N : ℝ) := by
  /- @proof-region region.target-node.session.9b19adef48ddd3db begin -/
  intros
  rename_i p N hp hN Ω instΩ P instP B C1 c t hB hC1 hcpos hclt ht ξ ζ hξ_meas hξ_nonneg hζ_meas hζ_nonneg hξ_tail hζ_tail hC hD hE hsqrtc
  have hB0 : (0:ℝ) < B := by linarith
  have hBpos : (0:ℝ) ≤ B := le_of_lt hB0
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hpR : (0:ℝ) < (p:ℝ) := by linarith
  have hNR1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNR : (0:ℝ) < (N:ℝ) := by linarith
  have hu : (0:ℝ) < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNR
  have hu1 : (1:ℝ) ≤ Real.sqrt (N:ℝ) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hNR1
  have hu2 : (Real.sqrt (N:ℝ))^2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNR)
  have hPNpos : (0:ℝ) < (p:ℝ) * (N:ℝ) := mul_pos hpR hNR
  have hPN1 : (1:ℝ) ≤ (p:ℝ) * (N:ℝ) := by nlinarith
  have hlog3 : Real.exp (-(3 * Real.log ((p:ℝ) * (N:ℝ)))) = 1 / ((p:ℝ) * (N:ℝ))^3 := by
    have h3 : Real.exp (3 * Real.log ((p:ℝ) * (N:ℝ))) = ((p:ℝ) * (N:ℝ))^3 := by
      rw [show 3 * Real.log ((p:ℝ) * (N:ℝ))
            = Real.log ((p:ℝ) * (N:ℝ)) + Real.log ((p:ℝ) * (N:ℝ))
              + Real.log ((p:ℝ) * (N:ℝ)) by ring]
      rw [Real.exp_add, Real.exp_add, Real.exp_log hPNpos]
      ring
    rw [Real.exp_neg, h3, one_div]
  have hexpξ : Real.exp (- t / B) ≤ 1 / ((p:ℝ) * (N:ℝ))^3 := by
    have hlog : 3 * Real.log ((p:ℝ) * (N:ℝ)) ≤ t / B := by
      have h1 : 3 * Real.log ((p:ℝ) * (N:ℝ)) * B ≤ t := by nlinarith [hC]
      calc 3 * Real.log ((p:ℝ) * (N:ℝ)) = (3 * Real.log ((p:ℝ) * (N:ℝ)) * B) / B := by
            field_simp
        _ ≤ t / B := by gcongr
    calc Real.exp (- t / B) = Real.exp (-(t / B)) := by rw [neg_div]
      _ ≤ Real.exp (-(3 * Real.log ((p:ℝ) * (N:ℝ)))) := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = 1 / ((p:ℝ) * (N:ℝ))^3 := hlog3
  have hexpζ : Real.exp (-(t ^ 2) / (2 * (c * B ^ 2))) ≤ 1 / ((p:ℝ) * (N:ℝ))^3 := by
    rw [show -(t ^ 2) / (2 * (c * B ^ 2)) = -(t ^ 2 / (2 * c * B ^ 2)) from by rw [neg_div, mul_assoc]]
    calc Real.exp (-(t ^ 2 / (2 * c * B ^ 2))) ≤ Real.exp (-(3 * Real.log ((p:ℝ) * (N:ℝ)))) := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = 1 / ((p:ℝ) * (N:ℝ))^3 := hlog3
  have cube_mono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → a^3 ≤ b^3 := by
    intro a b ha hab
    have hb : (0:ℝ) ≤ b := le_trans ha hab
    have h2 : a^2 ≤ b^2 := by
      have hd : (0:ℝ) ≤ b - a := by linarith
      have hs : (0:ℝ) ≤ b + a := by linarith
      nlinarith [mul_nonneg hd hs]
    calc a^3 = a^2 * a := by ring
      _ ≤ b^2 * b := mul_le_mul h2 hab ha (by positivity)
      _ = b^3 := by ring
  have hcube : (t + B)^3 ≤ (C1 * Real.sqrt (N:ℝ))^3 :=
    cube_mono (t + B) (C1 * Real.sqrt (N:ℝ)) (by linarith) hE
  have hcore : (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * (1 / ((p:ℝ) * (N:ℝ))^3) * Real.sqrt (N:ℝ)
      ≤ C1^3 := by
    have hP3pos : (0:ℝ) < ((p:ℝ) * (N:ℝ))^3 := pow_pos hPNpos 3
    have hone : (1:ℝ) / ((p:ℝ) * (N:ℝ))^3 * ((p:ℝ) * (N:ℝ))^3 = 1 := by field_simp
    refine le_of_mul_le_mul_right ?_ hP3pos
    calc (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * (1 / ((p:ℝ) * (N:ℝ))^3) * Real.sqrt (N:ℝ)
          * ((p:ℝ) * (N:ℝ))^3
        = (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * Real.sqrt (N:ℝ)
            * ((1:ℝ) / ((p:ℝ) * (N:ℝ))^3 * ((p:ℝ) * (N:ℝ))^3) := by ring
      _ = (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * Real.sqrt (N:ℝ) := by rw [hone, mul_one]
      _ ≤ C1^3 * ((p:ℝ) * (N:ℝ))^3 := by
          have hu4 : (Real.sqrt (N:ℝ))^4 = (N:ℝ)^2 := by
            rw [show (4:ℕ) = 2 * 2 by norm_num, pow_mul, hu2]
          have hp1 : (1:ℝ) ≤ (p:ℝ)^2 := by nlinarith
          have hpN : (1:ℝ) ≤ (p:ℝ)^2 * (N:ℝ) := by
            have h := mul_le_mul hp1 hNR1 (by norm_num : (0:ℝ) ≤ 1)
              (by positivity : (0:ℝ) ≤ (p:ℝ)^2)
            linarith
          have hnn : (0:ℝ) ≤ (p:ℝ) * (N:ℝ)^2 := by positivity
          have hkey : (p:ℝ) * (Real.sqrt (N:ℝ))^4 ≤ (p:ℝ)^3 * (N:ℝ)^3 := by
            have hstep : (p:ℝ) * (N:ℝ)^2 ≤ (p:ℝ) * (N:ℝ)^2 * ((p:ℝ)^2 * (N:ℝ)) := by
              simpa using mul_le_mul_of_nonneg_left hpN hnn
            calc (p:ℝ) * (Real.sqrt (N:ℝ))^4 = (p:ℝ) * (N:ℝ)^2 := by rw [hu4]
              _ ≤ (p:ℝ) * (N:ℝ)^2 * ((p:ℝ)^2 * (N:ℝ)) := hstep
              _ = (p:ℝ)^3 * (N:ℝ)^3 := by ring
          have hC13 : (0:ℝ) < C1^3 := by positivity
          calc (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * Real.sqrt (N:ℝ)
              = C1^3 * ((p:ℝ) * (Real.sqrt (N:ℝ))^4) := by ring
            _ ≤ C1^3 * ((p:ℝ)^3 * (N:ℝ)^3) := mul_le_mul_of_nonneg_left hkey (le_of_lt hC13)
            _ = C1^3 * ((p:ℝ) * (N:ℝ))^3 := by ring
  have hnum : ∀ k : ℝ, 0 ≤ k →
      k * (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * (1 / ((p:ℝ) * (N:ℝ))^3)
        ≤ k * C1^3 / Real.sqrt (N:ℝ) := by
    intro k hk
    have key : k * (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * (1 / ((p:ℝ) * (N:ℝ))^3)
        * Real.sqrt (N:ℝ) ≤ k * C1^3 := by
      have h := mul_le_mul_of_nonneg_left hcore hk
      calc k * (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * (1 / ((p:ℝ) * (N:ℝ))^3)
            * Real.sqrt (N:ℝ)
          = k * ((p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * (1 / ((p:ℝ) * (N:ℝ))^3)
            * Real.sqrt (N:ℝ)) := by ring
        _ ≤ k * C1^3 := h
    calc k * (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * (1 / ((p:ℝ) * (N:ℝ))^3)
        = (k * (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * (1 / ((p:ℝ) * (N:ℝ))^3)
            * Real.sqrt (N:ℝ)) * (Real.sqrt (N:ℝ))⁻¹ := by field_simp
      _ ≤ (k * C1^3) * (Real.sqrt (N:ℝ))⁻¹ := mul_le_mul_of_nonneg_right key (by positivity)
      _ = k * C1^3 / Real.sqrt (N:ℝ) := by rw [div_eq_mul_inv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hξcubemeas : Measurable (fun ω => (ξ i ω)^3) := by
      have h : Measurable (fun ω => ξ i ω * ξ i ω * ξ i ω) :=
        ((hξ_meas i).mul (hξ_meas i)).mul (hξ_meas i)
      have heq : (fun ω => (ξ i ω)^3) = (fun ω => ξ i ω * ξ i ω * ξ i ω) := by
        funext ω
        ring
      rw [heq]
      exact h
    have hcubemeas : ∀ n : ℕ, Measurable (fun ω => (min (ξ i ω) (n:ℝ))^3) := by
      intro n
      have hη : Measurable (fun ω => min (ξ i ω) (n:ℝ)) := (hξ_meas i).min measurable_const
      have h : Measurable (fun ω => min (ξ i ω) (n:ℝ) * min (ξ i ω) (n:ℝ)
          * min (ξ i ω) (n:ℝ)) := (hη.mul hη).mul hη
      have heq : (fun ω => (min (ξ i ω) (n:ℝ))^3)
          = (fun ω => min (ξ i ω) (n:ℝ) * min (ξ i ω) (n:ℝ)
              * min (ξ i ω) (n:ℝ)) := by
        funext ω
        ring
      rw [heq]
      exact h
    have hint : ∀ n : ℕ, Integrable (fun ω => (min (ξ i ω) (n:ℝ))^3) P := by
      intro n
      refine Integrable.mono' (integrable_const ((n:ℝ)^3))
        (hcubemeas n).aestronglyMeasurable ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (le_min (hξ_nonneg i ω) (by positivity)) 3)]
      exact cube_mono _ _ (le_min (hξ_nonneg i ω) (by positivity)) (min_le_right _ _)
    have hmain : ∀ n : ℕ, ∫ ω, (min (ξ i ω) (n:ℝ))^3 ∂P
        ≤ t^3 + 6 * (2*(p:ℝ)) * (t + B)^3 * Real.exp (- t / B) := by
      intro n
      have hη : Measurable (fun ω => min (ξ i ω) (n:ℝ)) := (hξ_meas i).min measurable_const
      have hmin_nn : ∀ ω, (0:ℝ) ≤ min (ξ i ω) (n:ℝ) :=
        fun ω => le_min (hξ_nonneg i ω) (by positivity)
      have hset : MeasurableSet {ω : Ω | t < min (ξ i ω) (n:ℝ)} :=
        measurableSet_lt measurable_const hη
      have hconst : Integrable (fun _ : Ω => t^3) P := integrable_const _
      have hprod : Integrable (fun ω => (min (ξ i ω) (n:ℝ))^3
          * (if t < min (ξ i ω) (n:ℝ) then (1:ℝ) else 0)) P := by
        refine Integrable.mono' (integrable_const ((n:ℝ)^3)) ?_ ?_
        · exact ((hcubemeas n).mul
            (Measurable.ite hset measurable_const measurable_const)).aestronglyMeasurable
        · filter_upwards with ω
          have h1 : (0:ℝ) ≤ (min (ξ i ω) (n:ℝ))^3 := pow_nonneg (hmin_nn ω) 3
          have h2 : (0:ℝ) ≤ (if t < min (ξ i ω) (n:ℝ) then (1:ℝ) else 0) := by
            split_ifs with hh <;> norm_num
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2)]
          split_ifs with hh
          · simpa using cube_mono _ _ (hmin_nn ω) (min_le_right _ _)
          · have hn3 : (0:ℝ) ≤ (n:ℝ)^3 := by positivity
            simpa using hn3
      have htailmin : ∀ s : ℝ, 0 ≤ s →
          P {ω : Ω | s < min (ξ i ω) (n:ℝ)}
            ≤ ENNReal.ofReal (2 * (p:ℝ) * Real.exp (- s / B)) := by
        intro s hs
        by_cases hsn : s < (n:ℝ)
        · have hseteq : {ω : Ω | s < min (ξ i ω) (n:ℝ)} = {ω : Ω | s < ξ i ω} := by
            ext ω
            simp only [Set.mem_setOf_eq]
            exact lt_min_iff.trans (and_iff_left hsn)
          rw [hseteq]
          have hne : P {ω : Ω | s < ξ i ω} ≠ ⊤ := measure_ne_top P _
          calc P {ω : Ω | s < ξ i ω} = ENNReal.ofReal ((P {ω : Ω | s < ξ i ω}).toReal) := by
                rw [ENNReal.ofReal_toReal hne]
            _ ≤ ENNReal.ofReal (2 * (p:ℝ) * Real.exp (- s / B)) := by
                apply ENNReal.ofReal_le_ofReal
                have h := hξ_tail i s hs
                rw [← neg_div] at h
                exact h
        · have hempty : {ω : Ω | s < min (ξ i ω) (n:ℝ)} = ∅ := by
            ext ω
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            exact le_trans (min_le_right _ _) (not_lt.mp hsn)
          rw [hempty]
          simp
      have hmom := ext_model_4 Ω P (fun ω => min (ξ i ω) (n:ℝ)) hmin_nn hη (2 * (p:ℝ)) B
        (by positivity) hB0 htailmin t (le_of_lt ht)
      have hmono_int : ∫ ω, (min (ξ i ω) (n:ℝ))^3 ∂P
          ≤ ∫ ω, ((t^3 : ℝ) + (min (ξ i ω) (n:ℝ))^3
              * (if t < min (ξ i ω) (n:ℝ) then (1:ℝ) else 0)) ∂P := by
        apply integral_mono_ae (hint n) (hconst.add hprod)
        filter_upwards with ω
        have hpt : (min (ξ i ω) (n:ℝ))^3 ≤ (t^3 : ℝ) + (min (ξ i ω) (n:ℝ))^3
            * (if t < min (ξ i ω) (n:ℝ) then (1:ℝ) else 0) := by
          by_cases hc : t < min (ξ i ω) (n:ℝ)
          · rw [if_pos hc, mul_one]
            have ht3 : (0:ℝ) ≤ t^3 := by positivity
            linarith
          · rw [if_neg hc, mul_zero, add_zero]
            exact cube_mono _ _ (hmin_nn ω) (not_lt.mp hc)
        exact hpt
      calc ∫ ω, (min (ξ i ω) (n:ℝ))^3 ∂P
          ≤ ∫ ω, ((t^3 : ℝ) + (min (ξ i ω) (n:ℝ))^3
              * (if t < min (ξ i ω) (n:ℝ) then (1:ℝ) else 0)) ∂P := hmono_int
        _ = (∫ _ : Ω, (t^3 : ℝ) ∂P) + ∫ ω, (min (ξ i ω) (n:ℝ))^3
              * (if t < min (ξ i ω) (n:ℝ) then (1:ℝ) else 0) ∂P := integral_add hconst hprod
        _ = t^3 + ∫ ω, (min (ξ i ω) (n:ℝ))^3
              * (if t < min (ξ i ω) (n:ℝ) then (1:ℝ) else 0) ∂P := by
            rw [show (∫ _ : Ω, (t^3 : ℝ) ∂P) = t^3 by simp]
        _ ≤ t^3 + 6 * (2*(p:ℝ)) * (t + B)^3 * Real.exp (- t / B) := by linarith [hmom]
    have hsup : (fun ω => ⨆ n : ℕ, ENNReal.ofReal ((min (ξ i ω) (n:ℝ))^3))
        = (fun ω => ENNReal.ofReal ((ξ i ω)^3)) := by
      funext ω
      refine le_antisymm ?_ ?_
      · refine iSup_le (fun n => ?_)
        exact ENNReal.ofReal_le_ofReal
          (cube_mono _ _ (le_min (hξ_nonneg i ω) (by positivity)) (min_le_left _ _))
      · obtain ⟨n, hn⟩ := exists_nat_ge (ξ i ω)
        calc ENNReal.ofReal ((ξ i ω)^3)
            = ENNReal.ofReal ((min (ξ i ω) (n:ℝ))^3) := by
              rw [min_eq_left (by exact_mod_cast hn)]
          _ ≤ ⨆ m : ℕ, ENNReal.ofReal ((min (ξ i ω) (m:ℝ))^3) :=
              le_iSup (fun m : ℕ => ENNReal.ofReal ((min (ξ i ω) (m:ℝ))^3)) n
    have hlin : ∫⁻ ω, ENNReal.ofReal ((ξ i ω)^3) ∂P
        ≤ ENNReal.ofReal (t^3 + 6 * (2*(p:ℝ)) * (t + B)^3 * Real.exp (- t / B)) := by
      have hmeas : ∀ n : ℕ, Measurable (fun ω => ENNReal.ofReal ((min (ξ i ω) (n:ℝ))^3)) :=
        fun n => ENNReal.measurable_ofReal.comp (hcubemeas n)
      have hmono : Monotone (fun n : ℕ => fun ω => ENNReal.ofReal ((min (ξ i ω) (n:ℝ))^3)) :=
        fun m n hmn ω => ENNReal.ofReal_le_ofReal (cube_mono _ _
          (le_min (hξ_nonneg i ω) (by positivity))
          (le_min (min_le_left _ _)
            (le_trans (min_le_right _ _) (by exact_mod_cast hmn))))
      calc ∫⁻ ω, ENNReal.ofReal ((ξ i ω)^3) ∂P
          = ∫⁻ ω, ⨆ n : ℕ, ENNReal.ofReal ((min (ξ i ω) (n:ℝ))^3) ∂P := by rw [← hsup]
        _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal ((min (ξ i ω) (n:ℝ))^3) ∂P :=
            MeasureTheory.lintegral_iSup hmeas hmono
        _ ≤ ENNReal.ofReal (t^3 + 6 * (2*(p:ℝ)) * (t + B)^3 * Real.exp (- t / B)) := by
            refine iSup_le (fun n => ?_)
            rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint n)
              (Filter.Eventually.of_forall
                (fun ω => pow_nonneg (le_min (hξ_nonneg i ω) (by positivity)) 3))]
            exact ENNReal.ofReal_le_ofReal (hmain n)
    have hne_top : ∫⁻ ω, ENNReal.ofReal ((ξ i ω)^3) ∂P ≠ ⊤ := by
      intro htop
      rw [htop] at hlin
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hlin)
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hξcubemeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => pow_nonneg (hξ_nonneg i ω) 3))).mp hne_top
  · intro i
    exact (statopia_math_node_1953254498_13530db2 Ω P (2 * (p:ℝ)) (c * B^2) (by positivity)
      (mul_pos hcpos (pow_pos hB0 2)) (ζ i) (hζ_meas i) (hζ_nonneg i) (by
        intro s hs
        have h := hζ_tail i s hs
        have hargs : -(s ^ 2) / (2 * c * B ^ 2) = -(s ^ 2) / (2 * (c * B ^ 2)) := by
          rw [mul_assoc]
        rw [hargs] at h
        exact h)).1
  · have hper : ∀ i : Fin N, ∫ ω, (ξ i ω)^3 * (if ξ i ω > t then (1:ℝ) else 0) ∂P
        ≤ 12 * C1^3 / Real.sqrt (N:ℝ) := by
      intro i
      have htail' : ∀ x : ℝ, 0 ≤ x →
          P {ω : Ω | x < ξ i ω} ≤ ENNReal.ofReal (2 * (p:ℝ) * Real.exp (- x / B)) := by
        intro x hx
        have hne : P {ω : Ω | x < ξ i ω} ≠ ⊤ := measure_ne_top P _
        calc P {ω : Ω | x < ξ i ω} = ENNReal.ofReal ((P {ω : Ω | x < ξ i ω}).toReal) := by
              rw [ENNReal.ofReal_toReal hne]
          _ ≤ ENNReal.ofReal (2 * (p:ℝ) * Real.exp (- x / B)) := by
              apply ENNReal.ofReal_le_ofReal
              have h := hξ_tail i x hx
              rw [← neg_div] at h
              exact h
      have hkey := ext_model_4 Ω P (ξ i) (hξ_nonneg i) (hξ_meas i) (2 * (p:ℝ)) B
        (by positivity) hB0 htail' t (le_of_lt ht)
      have hstep : 6 * (2*(p:ℝ)) * (t + B)^3 * Real.exp (- t / B)
          ≤ 6 * (2*(p:ℝ)) * (C1 * Real.sqrt (N:ℝ))^3
            * (1 / ((p:ℝ) * (N:ℝ))^3) := by
        have hbc : 6 * (2*(p:ℝ)) * (t + B)^3
            ≤ 6 * (2*(p:ℝ)) * (C1 * Real.sqrt (N:ℝ))^3 := by
          apply mul_le_mul_of_nonneg_left hcube
          positivity
        exact mul_le_mul hbc hexpξ (by positivity) (by positivity)
      calc ∫ ω, (ξ i ω)^3 * (if ξ i ω > t then (1:ℝ) else 0) ∂P
          ≤ 6 * (2*(p:ℝ)) * (t + B)^3 * Real.exp (- t / B) := hkey
        _ ≤ 6 * (2*(p:ℝ)) * (C1 * Real.sqrt (N:ℝ))^3
              * (1 / ((p:ℝ) * (N:ℝ))^3) := hstep
        _ = 12 * (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * (1 / ((p:ℝ) * (N:ℝ))^3) := by ring
        _ ≤ 12 * C1^3 / Real.sqrt (N:ℝ) := hnum 12 (by norm_num)
    calc (1 / (N:ℝ)) * ∑ i : Fin N,
          ∫ ω, (ξ i ω)^3 * (if ξ i ω > t then (1:ℝ) else 0) ∂P
        ≤ (1 / (N:ℝ)) * ∑ i : Fin N, (12 * C1^3 / Real.sqrt (N:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun i _ => hper i)
      _ = 12 * C1^3 / Real.sqrt (N:ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNR
          field_simp
  · have hper : ∀ i : Fin N, ∫ ω, (ζ i ω)^3 * (if ζ i ω > t then (1:ℝ) else 0) ∂P
        ≤ 20 * C1^3 / Real.sqrt (N:ℝ) := by
      intro i
      have hnode := statopia_math_node_1953254498_13530db2 Ω P (2 * (p:ℝ)) (c * B^2)
        (by positivity) (mul_pos hcpos (pow_pos hB0 2)) (ζ i) (hζ_meas i) (hζ_nonneg i) (by
          intro s hs
          have h := hζ_tail i s hs
          have hargs : -(s ^ 2) / (2 * c * B ^ 2) = -(s ^ 2) / (2 * (c * B ^ 2)) := by
            rw [mul_assoc]
          rw [hargs] at h
          exact h)
      have hkey := hnode.2 t (le_of_lt ht)
      have hsqrtcB : Real.sqrt (c * B^2) ≤ B := by
        rw [Real.sqrt_mul (le_of_lt hcpos), Real.sqrt_sq hBpos]
        have h1 : Real.sqrt c * B ≤ 1 * B := mul_le_mul_of_nonneg_right hsqrtc hBpos
        linarith
      have hcube2 : (t + Real.sqrt (c * B^2))^3 ≤ (C1 * Real.sqrt (N:ℝ))^3 := by
        refine le_trans (cube_mono (t + Real.sqrt (c * B^2)) (t + B) ?_ ?_) hcube
        · positivity
        · linarith
      have hstep : 10 * (2*(p:ℝ)) * (t + Real.sqrt (c * B^2))^3
            * Real.exp (-(t ^ 2) / (2 * (c * B ^ 2)))
          ≤ 10 * (2*(p:ℝ)) * (C1 * Real.sqrt (N:ℝ))^3
            * (1 / ((p:ℝ) * (N:ℝ))^3) := by
        have hbc : 10 * (2*(p:ℝ)) * (t + Real.sqrt (c * B^2))^3
            ≤ 10 * (2*(p:ℝ)) * (C1 * Real.sqrt (N:ℝ))^3 := by
          apply mul_le_mul_of_nonneg_left hcube2
          positivity
        exact mul_le_mul hbc hexpζ (by positivity) (by positivity)
      calc ∫ ω, (ζ i ω)^3 * (if ζ i ω > t then (1:ℝ) else 0) ∂P
          ≤ 10 * (2*(p:ℝ)) * (t + Real.sqrt (c * B^2))^3
              * Real.exp (-(t ^ 2) / (2 * (c * B ^ 2))) := hkey
        _ ≤ 10 * (2*(p:ℝ)) * (C1 * Real.sqrt (N:ℝ))^3
              * (1 / ((p:ℝ) * (N:ℝ))^3) := hstep
        _ = 20 * (p:ℝ) * (C1 * Real.sqrt (N:ℝ))^3 * (1 / ((p:ℝ) * (N:ℝ))^3) := by ring
        _ ≤ 20 * C1^3 / Real.sqrt (N:ℝ) := hnum 20 (by norm_num)
    calc (1 / (N:ℝ)) * ∑ i : Fin N,
          ∫ ω, (ζ i ω)^3 * (if ζ i ω > t then (1:ℝ) else 0) ∂P
        ≤ (1 / (N:ℝ)) * ∑ i : Fin N, (20 * C1^3 / Real.sqrt (N:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun i _ => hper i)
      _ = 20 * C1^3 / Real.sqrt (N:ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNR
          field_simp
  /- @proof-region region.target-node.session.9b19adef48ddd3db end -/

end Statlib.Imported

