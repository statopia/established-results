import Lean
import ProverJobs.job_paper_8ff73b3c73e04139840b7ba5205a04c8.ExternalNodes.Node_8d0d0baf9ab4437481f0
import ProverJobs.job_paper_8ff73b3c73e04139840b7ba5205a04c8.Vocabulary
import ProverJobs.job_paper_8ff73b3c73e04139840b7ba5205a04c8.ProvedNodes
import ProverJobs.job_paper_8ff73b3c73e04139840b7ba5205a04c8.Base

namespace PaperProofTasks.job_paper_8ff73b3c73e04139840b7ba5205a04c8

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

theorem paper_8ff73b3c73e04139840b7ba5205a04c8 :
    ∀ (c V : ℝ) (q : ℕ), 0 < c → 0 < V → 0 < q →
      ∃ C N₀ : ℝ, 0 < C ∧ 0 < N₀ ∧
        ∀ (p : ℕ), 2 ≤ p → ∀ (N : ℕ), 0 < N →
          N₀ * Real.log (p : ℝ) ≤ (N : ℝ) →
          ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (m : ℕ), (m ≤ p ^ 2 ∨ m ≤ p * q) →
            ∀ (U : Fin m → Fin N → Ω → ℝ),
              (∀ (j : Fin m) (l : Fin N), Measurable (U j l)) →
              (∀ j : Fin m, iIndepFun (fun l : Fin N => U j l) μ) →
              (∀ (j : Fin m) (l : Fin N), Integrable (U j l) μ) →
              (∀ (j : Fin m) (l : Fin N), ∫ ω, U j l ω ∂μ = 0) →
              (∀ (j : Fin m) (l : Fin N) (r : ℕ), 2 ≤ r →
                ∫⁻ ω, ENNReal.ofReal (|U j l ω| ^ r) ∂μ ≤
                  ENNReal.ofReal ((r.factorial : ℝ) * V ^ r)) →
              μ {ω | ∃ j : Fin m,
                  C * Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) <
                    |(N : ℝ)⁻¹ * ∑ l : Fin N, U j l ω|} ≤
                ENNReal.ofReal (Real.rpow (p : ℝ) (-c) / 20)
:= by
  /- @proof-region region.root.ac1043ddbe94 begin -/
  intro c V q hc hV hq
  obtain ⟨b, hb, hBern⟩ := PaperProofTasks.job_paper_ebad183ded244602a77f3710a9957efa.Statlib.Imported.paper_ebad183ded244602a77f3710a9957efa
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have h : (1 : ℕ) ≤ q := hq
    exact_mod_cast h
  have hqR : (0 : ℝ) < (q : ℝ) := by linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog40q : (0 : ℝ) < Real.log (40 * (q : ℝ)) := by
    apply Real.log_pos
    nlinarith
  set σ : ℝ := Real.log (40 * (q : ℝ)) / Real.log 2 with hσdef
  have hσpos : 0 < σ := by
    rw [hσdef]
    exact div_pos hlog40q hlog2pos
  set δ : ℝ := 2 + c + σ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδb : 0 < δ / b := div_pos hδpos hb
  set C : ℝ := V * Real.sqrt (δ / b) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact mul_pos hV (Real.sqrt_pos.mpr hδb)
  set N₀ : ℝ := max 1 (δ / b) with hN0def
  have hN0pos : 0 < N₀ := by
    rw [hN0def]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hN0ge : δ / b ≤ N₀ := by
    rw [hN0def]
    exact le_max_right _ _
  have hCeq : C ^ 2 = V ^ 2 * δ / b := by
    rw [hCdef, mul_pow, Real.sq_sqrt (le_of_lt hδb)]
    ring
  refine ⟨C, N₀, hCpos, hN0pos, ?_⟩
  intro p hp N hN hNlog Ω instΩ μ instμ m hm U hUmeas hUindep hUint hUcenter hUmoment
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP2 : (0 : ℝ) < (p : ℝ) := by linarith
  have hN1 : (1 : ℕ) ≤ N := hN
  have hlogP : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hpR
  have h2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
  have hσlog : Real.log (40 * (q : ℝ)) ≤ σ * Real.log (p : ℝ) := by
    have hmul : Real.log (40 * (q : ℝ)) / Real.log 2 * Real.log 2 ≤
        Real.log (40 * (q : ℝ)) / Real.log 2 * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_left hlogP (le_of_lt (div_pos hlog40q hlog2pos))
    rw [div_mul_cancel₀ _ h2ne] at hmul
    rw [hσdef]
    exact hmul
  have hPpowσ : (p : ℝ) ^ (-σ) ≤ (40 * (q : ℝ))⁻¹ := by
    rw [Real.rpow_def_of_pos hP2]
    have hle : Real.log (p : ℝ) * (-σ) ≤ -Real.log (40 * (q : ℝ)) := by linarith
    calc Real.exp (Real.log (p : ℝ) * (-σ))
        ≤ Real.exp (-Real.log (40 * (q : ℝ))) := Real.exp_le_exp.mpr hle
      _ = (40 * (q : ℝ))⁻¹ := by
          rw [Real.exp_neg, Real.exp_log]
          positivity
  have hPcpos : 0 < (p : ℝ) ^ (-c) := Real.rpow_pos_of_pos hP2 (-c)
  have hpow2 : (p : ℝ) ^ 2 = (p : ℝ) ^ ((2 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
  have hpowR : (p : ℝ) ^ ((2 : ℕ) : ℝ) * (p : ℝ) ^ (-δ) = (p : ℝ) ^ (-c) * (p : ℝ) ^ (-σ) := by
    have key : ((2 : ℕ) : ℝ) + -δ = -c + -σ := by rw [hδdef]; ring
    calc (p : ℝ) ^ ((2 : ℕ) : ℝ) * (p : ℝ) ^ (-δ)
        = (p : ℝ) ^ (((2 : ℕ) : ℝ) + -δ) := (Real.rpow_add hP2 ((2 : ℕ) : ℝ) (-δ)).symm
      _ = (p : ℝ) ^ (-c + -σ) := by rw [key]
      _ = (p : ℝ) ^ (-c) * (p : ℝ) ^ (-σ) := Real.rpow_add hP2 (-c) (-σ)
  have hpow : (p : ℝ) ^ 2 * (p : ℝ) ^ (-δ) = (p : ℝ) ^ (-c) * (p : ℝ) ^ (-σ) := by
    rw [hpow2]
    exact hpowR
  have hfin : (q : ℝ) * (p : ℝ) ^ 2 * (2 * (p : ℝ) ^ (-δ)) ≤ (p : ℝ) ^ (-c) / 20 := by
    have step1 : (q : ℝ) * (p : ℝ) ^ 2 * (2 * (p : ℝ) ^ (-δ))
        = 2 * (q : ℝ) * ((p : ℝ) ^ 2 * (p : ℝ) ^ (-δ)) := by ring
    rw [step1, hpow]
    have step2 : 2 * (q : ℝ) * ((p : ℝ) ^ (-c) * (p : ℝ) ^ (-σ)) ≤
        2 * (q : ℝ) * ((p : ℝ) ^ (-c) * (40 * (q : ℝ))⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hPpowσ (le_of_lt hPcpos)
    refine le_trans step2 ?_
    have step3 : 2 * (q : ℝ) * ((p : ℝ) ^ (-c) * (40 * (q : ℝ))⁻¹) =
        (p : ℝ) ^ (-c) / 20 := by
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
      field_simp
      ring
    rw [step3]
  have hmR : (m : ℝ) ≤ (q : ℝ) * (p : ℝ) ^ 2 := by
    rcases hm with h | h
    · have h1 : (m : ℝ) ≤ (p : ℝ) ^ 2 := by
        have h' : (m : ℝ) ≤ ((p ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr h
        simpa using h'
      have hsq : (0 : ℝ) ≤ (p : ℝ) ^ 2 := by positivity
      have hprod : (0 : ℝ) ≤ ((q : ℝ) - 1) * (p : ℝ) ^ 2 := mul_nonneg (by linarith) hsq
      nlinarith
    · have h1 : (m : ℝ) ≤ (p : ℝ) * (q : ℝ) := by
        have h' : (m : ℝ) ≤ ((p * q : ℕ) : ℝ) := Nat.cast_le.mpr h
        simpa using h'
      have hpp : (p : ℝ) ≤ (p : ℝ) ^ 2 := by
        have h0 : (0 : ℝ) ≤ (p : ℝ) := le_of_lt hP2
        have h1' : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
        have hmul := mul_nonneg h0 h1'
        nlinarith
      have hpq : (p : ℝ) * (q : ℝ) ≤ (q : ℝ) * (p : ℝ) ^ 2 := by
        rw [mul_comm (p : ℝ) (q : ℝ)]
        exact mul_le_mul_of_nonneg_left hpp (le_of_lt hqR)
      linarith
  have hmE : (m : ℝ≥0∞) ≤ ENNReal.ofReal ((q : ℝ) * (p : ℝ) ^ 2) := by
    simpa using ENNReal.ofReal_le_ofReal hmR
  set T : ℝ := C * Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) with hTdef
  have hper : ∀ j : Fin m,
      μ {ω | T < |(N : ℝ)⁻¹ * ∑ l : Fin N, U j l ω|} ≤
        ENNReal.ofReal (2 * (p : ℝ) ^ (-δ)) := by
    intro j
    refine statopia_math_node_1647745287_d8e61bd0 b hb ?_ V hV δ hδpos C hCpos hCeq N₀ hN0pos
      hN0ge p hp N hN1 hNlog Ω μ (fun l => U j l) (fun l => hUmeas j l) (hUindep j)
      (fun l => hUint j l) (fun l => hUcenter j l) (fun r hr l => hUmoment j l r hr)
    intro N' hN' V' hV' Ω' instΩ' μ' instμ' U' hmeas hindep hint hcenter hmom t ht
    exact hBern N' hN' V' hV' Ω' μ' U' hmeas hindep hint hcenter (fun l r hr => hmom r hr l) t ht
  calc μ {ω | ∃ j : Fin m, T < |(N : ℝ)⁻¹ * ∑ l : Fin N, U j l ω|}
      = μ (⋃ j : Fin m, {ω | T < |(N : ℝ)⁻¹ * ∑ l : Fin N, U j l ω|}) := by
        congr 1
        ext ω
        simp
    _ ≤ ∑' j : Fin m, μ {ω | T < |(N : ℝ)⁻¹ * ∑ l : Fin N, U j l ω|} := measure_iUnion_le _
    _ ≤ ∑' _ : Fin m, ENNReal.ofReal (2 * (p : ℝ) ^ (-δ)) := ENNReal.tsum_le_tsum hper
    _ = (m : ℝ≥0∞) * ENNReal.ofReal (2 * (p : ℝ) ^ (-δ)) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((q : ℝ) * (p : ℝ) ^ 2) * ENNReal.ofReal (2 * (p : ℝ) ^ (-δ)) :=
        mul_le_mul_right' hmE _
    _ = ENNReal.ofReal ((q : ℝ) * (p : ℝ) ^ 2 * (2 * (p : ℝ) ^ (-δ))) := by
        exact (ENNReal.ofReal_mul (show (0 : ℝ) ≤ (q : ℝ) * (p : ℝ) ^ 2 by positivity)).symm
    _ ≤ ENNReal.ofReal ((p : ℝ) ^ (-c) / 20) := ENNReal.ofReal_le_ofReal hfin
  /- @proof-region region.root.ac1043ddbe94 end -/

end Statlib.Imported

