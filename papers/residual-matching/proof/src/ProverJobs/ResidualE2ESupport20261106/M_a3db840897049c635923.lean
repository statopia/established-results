import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_af44e491f7599a4b01ac
import ProverJobs.ResidualE2ESupport20261106.M_1826cf4a199ca47d64c5
import ProverJobs.ResidualE2ESupport20261106.M_e906bda11ab64df06902

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
theorem statopia_math_node_3786680764_db220746 : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CD : ℝ) (hCD : max (Kt * (D0 + 12)) (D0 + 20) ≤ CD),
    ∃ M1 : ℕ,
      ∀ (m : ℕ) (hm : 2 ≤ m) (hM1 : M1 ≤ m)
        (hrho_lo : rhoMinus ≤ (1 : ℝ) / (m : ℝ))
        (hrho_hi : (1 : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (XT Mask : Ω → Matrix (Fin m) (Fin 1) ℝ)
        (hXT_meas : ∀ (i : Fin m) (j : Fin 1), Measurable fun ω => XT ω i j)
        (hXT_int : ∀ (i : Fin m) (j : Fin 1), Integrable (fun ω => XT ω i j) μ)
        (hXT_sq_int : ∀ (i : Fin m) (j : Fin 1), Integrable (fun ω => (XT ω i j) ^ 2) μ)
        (hXT_indep : iIndepFun (fun (ij : Fin m × Fin 1) (ω : Ω) => XT ω ij.1 ij.2) μ)
        (hXT_mean : ∀ (i : Fin m) (j : Fin 1), ∫ ω, XT ω i j ∂μ = 0)
        (hXT_var : ∀ (i : Fin m) (j : Fin 1), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1)
        (hMask_meas : ∀ (i : Fin m) (j : Fin 1), Measurable fun ω => Mask ω i j)
        (hMask_val : ∀ (i : Fin m) (j : Fin 1) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
        (hMask_law : ∀ (i : Fin m) (j : Fin 1),
          μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
        (hMask_indep : iIndepFun (fun (ij : Fin m × Fin 1) (ω : Ω) => Mask ω ij.1 ij.2) μ)
        (hIndep : IndepFun (fun ω (ij : Fin m × Fin 1) => XT ω ij.1 ij.2)
          (fun ω (ij : Fin m × Fin 1) => Mask ω ij.1 ij.2) μ)
        (hXT_bound : let L : ℝ := CD * Real.log ((m : ℝ) * ((1 : ℕ) : ℝ)) +
            10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4;
          ∀ (ω : Ω) (i : Fin m) (j : Fin 1), |XT ω i j| ≤ 3 * L),
        μ {ω | Real.sqrt (∑ i : Fin m,
              (maskedScaled p (XT ω) (Mask ω) i (0 : Fin 1)) ^ 2) <
            1 - Real.sqrt ((1 : ℝ) / (m : ℝ)) - 1 * deltaM m} ≤
          ENNReal.ofReal (Real.rpow ((1 : ℕ) : ℝ) (-(D0 + 4)) / 2) := by
  /- @proof-region region.target-node.session.d8e968649f42b924 begin -/
  intro D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le Kt hKt alpha0 halpha0 CD hCD
  set C1 : ℝ := CD + 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 with hC1
  have hlog_tendsto : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog1 : ∀ᶠ (m : ℕ) in Filter.atTop, 1 ≤ Real.log (m : ℝ) :=
    hlog_tendsto.eventually (Filter.eventually_ge_atTop (1 : ℝ))
  have hlogbig : ∀ᶠ (m : ℕ) in Filter.atTop, 18 * C1 ^ 2 ≤ Real.log (m : ℝ) :=
    hlog_tendsto.eventually (Filter.eventually_ge_atTop (18 * C1 ^ 2))
  have hthree : ∀ᶠ (m : ℕ) in Filter.atTop, 3 ≤ m := Filter.eventually_ge_atTop 3
  have hlarge : ∀ᶠ (m : ℕ) in Filter.atTop,
      (3 ≤ m ∧ 1 ≤ Real.log (m : ℝ) ∧
        18 * C1 ^ 2 ≤ Real.rpow (Real.log (m : ℝ)) (alpha0 - 4)) := by
    refine (hthree.and (hlog1.and hlogbig)).mono ?_
    intro m hm
    rcases hm with ⟨h3, h1, hb⟩
    refine ⟨h3, h1, ?_⟩
    have h_exp : (1 : ℝ) ≤ alpha0 - 4 := by linarith
    calc 18 * C1 ^ 2 ≤ Real.log (m : ℝ) := hb
      _ ≤ Real.rpow (Real.log (m : ℝ)) (alpha0 - 4) := by
        have hmono := Real.rpow_le_rpow_of_exponent_le (x := Real.log (m : ℝ)) h1 h_exp
        rw [Real.rpow_one] at hmono
        exact hmono
  obtain ⟨M1, hM1⟩ := Filter.eventually_atTop.1 hlarge
  refine ⟨M1, ?_⟩
  intro m hm hM1m hrho_lo hrho_hi p hp0 hp1 hsparse Ω instΩ μ instμ
    XT Mask hXT_meas hXT_int hXT_sq_int hXT_indep hXT_mean hXT_var
    hMask_meas hMask_val hMask_law hMask_indep hIndep hXT_bound
  have hrw : Real.rpow ((1 : ℕ) : ℝ) (-(D0 + 4)) = (1 : ℝ) := by
    rw [Nat.cast_one]
    exact Real.one_rpow _
  rw [hrw]
  set s : ℝ := 1 - Real.sqrt ((1 : ℝ) / (m : ℝ)) - 1 * deltaM m with hs
  by_cases hscase : s ≤ 0
  · have hempty :
        {ω : Ω | Real.sqrt (∑ i : Fin m,
            (maskedScaled p (XT ω) (Mask ω) i (0 : Fin 1)) ^ 2) < s} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hlt
      have hnonneg : 0 ≤ Real.sqrt (∑ i : Fin m,
          (maskedScaled p (XT ω) (Mask ω) i (0 : Fin 1)) ^ 2) := Real.sqrt_nonneg _
      linarith
    rw [hempty, measure_empty]
    exact zero_le _
  · set Lv : ℝ := CD * Real.log ((m : ℝ) * ((1 : ℕ) : ℝ)) +
        10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 with hLvdef
    have hLv : ∀ (ω : Ω) (i : Fin m) (j : Fin 1), |XT ω i j| ≤ 3 * Lv := hXT_bound
    obtain ⟨hvar_int, hvar_bound⟩ :=
      statopia_math_node_3925995709_85201a55 m (by omega) p hp0 hp1 Lv μ XT Mask
        hXT_meas hXT_int hXT_sq_int hXT_indep hXT_mean hXT_var
        hMask_meas hMask_val hMask_law hMask_indep hIndep hLv
    let Sfun : Ω → ℝ := fun ω => ∑ i : Fin m, (maskedScaled p (XT ω) (Mask ω) i 0) ^ 2
    let v : ℝ := 9 * Lv ^ 2 / ((m : ℝ) * p)
    let t : ℝ := 1 - s ^ 2
    have hs_pos : 0 < s := not_le.mp hscase
    have hlog_ge : 1 ≤ Real.log (m : ℝ) := (hM1 m hM1m).2.1
    have hlog_pos : 0 < Real.log (m : ℝ) := by linarith
    have hdelta_pos : 0 < deltaM m := by
      show (0 : ℝ) < (Real.log (m : ℝ))⁻¹
      exact inv_pos.mpr hlog_pos
    have hsval : s = 1 - Real.sqrt ((1 : ℝ) / (m : ℝ)) - deltaM m := by rw [hs, one_mul]
    have hs_lt_one : s < 1 := by
      rw [hsval]
      have hsnn : 0 ≤ Real.sqrt ((1 : ℝ) / (m : ℝ)) := Real.sqrt_nonneg _
      linarith [hdelta_pos, hsnn]
    have hsq_lt : s ^ 2 < 1 := by
      have h := mul_lt_mul hs_lt_one (le_of_lt hs_lt_one) hs_pos zero_le_one
      simpa [pow_two, one_mul] using h
    have ht_val : t = 1 - s ^ 2 := rfl
    have ht_pos : 0 < t := by rw [ht_val]; linarith [hsq_lt]
    have hsub : {ω : Ω | Real.sqrt (Sfun ω) < s} ⊆ {ω : Ω | t ^ 2 ≤ (Sfun ω - 1) ^ 2} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have hSnn : 0 ≤ Sfun ω := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hSs : Sfun ω < s ^ 2 := (Real.sqrt_lt hSnn (le_of_lt hs_pos)).mp hω
      have hgt : t < 1 - Sfun ω := by rw [ht_val]; linarith [hSs]
      have hlt : t * t < (1 - Sfun ω) * (1 - Sfun ω) :=
        mul_lt_mul hgt (le_of_lt hgt) ht_pos
          (le_of_lt (by linarith [hgt, ht_pos] : (0 : ℝ) < 1 - Sfun ω))
      calc t ^ 2 = t * t := by rw [pow_two]
        _ ≤ (1 - Sfun ω) * (1 - Sfun ω) := le_of_lt hlt
        _ = (1 - Sfun ω) ^ 2 := by rw [pow_two]
        _ = (Sfun ω - 1) ^ 2 := by ring
    have hae : ∀ᵐ (ω : Ω) ∂μ, 0 ≤ (Sfun ω - 1) ^ 2 :=
      Filter.Eventually.of_forall (fun ω => sq_nonneg (Sfun ω - 1))
    have ht2pos : (0 : ℝ) < t ^ 2 := pow_pos ht_pos 2
    have hcheb_key :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.meas_ge_le_ofReal_integral_div
        μ (fun ω => (Sfun ω - 1) ^ 2) hae hvar_int (t ^ 2) ht2pos
    have hmono : μ {ω : Ω | Real.sqrt (Sfun ω) < s} ≤
        μ {ω : Ω | t ^ 2 ≤ (Sfun ω - 1) ^ 2} :=
      measure_mono hsub
    have hchain : μ {ω : Ω | Real.sqrt (Sfun ω) < s}
        ≤ ENNReal.ofReal ((∫ ω, (Sfun ω - 1) ^ 2 ∂μ) / t ^ 2) :=
      le_trans hmono hcheb_key
    have hfinal :
        ENNReal.ofReal ((∫ ω, (Sfun ω - 1) ^ 2 ∂μ) / t ^ 2) ≤ ENNReal.ofReal (1 / 2) := by
      apply ENNReal.ofReal_le_ofReal
      have h_div : (∫ ω, (Sfun ω - 1) ^ 2 ∂μ) / t ^ 2 ≤ v / t ^ 2 :=
        div_le_div_of_nonneg_right hvar_bound (le_of_lt ht2pos)
      have hnum : v / t ^ 2 ≤ 1 / 2 := by
        have hmpos : (0 : ℝ) < (m : ℝ) := by
          exact_mod_cast (show (0 : ℕ) < m by omega)
        have hCDpos : 0 < CD := by
          have h1 : D0 + 20 ≤ CD := le_trans (le_max_right (Kt * (D0 + 12)) (D0 + 20)) hCD
          linarith only [hD0, h1]
        generalize hKdef : (10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) = K at hLvdef hC1
        have hLvval : Lv = CD * Real.log (m : ℝ) + K := by
          rw [hLvdef, Nat.cast_one, mul_one]
        have hKpos : 0 ≤ K := by
          have hprod : 0 ≤ 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by positivity
          first
            | rw [hKdef] at hprod; exact hprod
            | rw [← hKdef] at hprod; exact hprod
        clear hKdef
        have hloc_nonneg : 0 ≤ CD * Real.log (m : ℝ) + K := by
          have h1 : 0 ≤ CD * Real.log (m : ℝ) := mul_nonneg (le_of_lt hCDpos) (le_of_lt hlog_pos)
          linarith only [h1, hKpos]
        have hloc_le : CD * Real.log (m : ℝ) + K ≤ C1 * Real.log (m : ℝ) := by
          rw [hC1, add_mul]
          have hKg : K ≤ K * Real.log (m : ℝ) := by
            have hmul := mul_le_mul_of_nonneg_left hlog_ge hKpos
            simpa using hmul
          linarith only [hKg]
        have hLv_nonneg : 0 ≤ Lv := by rw [hLvval]; exact hloc_nonneg
        have hLv_le : Lv ≤ C1 * Real.log (m : ℝ) := by rw [hLvval]; exact hloc_le
        have hgt_inv : (Real.log (m : ℝ))⁻¹ ≤ t := by
          have h1s : 1 - s = Real.sqrt ((1 : ℝ) / (m : ℝ)) + (Real.log (m : ℝ))⁻¹ := by
            have hd : deltaM m = (Real.log (m : ℝ))⁻¹ := rfl
            rw [hsval, hd]
            ring
          have h1s_ge : (Real.log (m : ℝ))⁻¹ ≤ 1 - s := by
            rw [h1s]
            have hsnn : 0 ≤ Real.sqrt ((1 : ℝ) / (m : ℝ)) := Real.sqrt_nonneg _
            linarith only [hsnn]
          have h1s_nn : 0 ≤ 1 - s :=
            le_trans (inv_nonneg.mpr (le_of_lt hlog_pos)) h1s_ge
          have h1ps : (1 : ℝ) ≤ 1 + s := by linarith only [hs_pos]
          have ht_fac : t = (1 - s) * (1 + s) := by rw [ht_val]; ring
          rw [ht_fac]
          calc (Real.log (m : ℝ))⁻¹ = (Real.log (m : ℝ))⁻¹ * 1 := by ring
            _ ≤ (1 - s) * (1 + s) := mul_le_mul h1s_ge h1ps zero_le_one h1s_nn
        show 9 * Lv ^ 2 / ((m : ℝ) * p) / t ^ 2 ≤ 1 / 2
        exact statopia_math_node_3217929161_d25f0da7 m alpha0 p Lv C1 t
          hmpos hp0 ht_pos hlog_ge hsparse (hM1 m hM1m).2.2 hLv_nonneg hLv_le hgt_inv
      exact le_trans h_div hnum
    exact le_trans hchain hfinal
  /- @proof-region region.target-node.session.d8e968649f42b924 end -/

end Statlib.Imported

