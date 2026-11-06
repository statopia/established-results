import Lean
import ProverJobs.ResidualE2ESupport20261106.M_639d5a54c5a150872e4f
import ProverJobs.ResidualE2ESupport20261106.M_9ebb17def6102ca6c226
import ProverJobs.ResidualE2ESupport20261106.M_b11b22849368ce1005c6
import ProverJobs.ResidualE2ESupport20261106.M_393f49f06ac135373093
import ProverJobs.ResidualE2ESupport20261106.M_2e445e9d131a16ed6935
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
universe u

set_option maxHeartbeats 4000000 in
set_option autoImplicit false in
theorem sparse_cdf_small_of_polynomial_rate (beta : ℝ) (hbeta : 1 / 10 < beta)
    (h_dense : DenseSymmetricPolynomialRate beta) : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0),
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ M2 : ℕ,
      ∀ (m n : ℕ), 1 ≤ n → n ≤ m → M2 ≤ m →
        rhoMinus ≤ (n : ℝ) / (m : ℝ) → (n : ℝ) / (m : ℝ) ≤ 1 →
        ∀ (p : ℝ), 0 < p → p ≤ 1 →
          Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p →
          ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ),
            (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j) →
            (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ) →
            (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ) →
            iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ →
            (∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0) →
            (∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1) →
            (∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
              μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt))) →
            (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
            (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
            (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
            iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
            IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
              (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
            ∀ tau : ℝ, 0 ≤ tau → ∃ G1 : Set Ω,
              MeasurableSet G1 ∧
                μ G1ᶜ ≤ ENNReal.ofReal (4 * Real.rpow (n : ℝ) (-(D0 + 2))) ∧
                  ∀ ω ∈ G1, ∀ i : Fin n,
                    |(n : ℝ)⁻¹ *
                        (((Finset.univ.filter (fun j : Fin n =>
                            svals (maskedScaled p (Xi ω) (Mask ω)) j ≤
                              mpQuantile ((n : ℝ) / (m : ℝ)) n i + tau)).card : ℝ)) -
                      (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..(mpQuantile ((n : ℝ) / (m : ℝ)) n i + tau),
                        rootedMPDensity ((n : ℝ) / (m : ℝ)) u)| ≤
                    2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) ∧
                    |(n : ℝ)⁻¹ *
                        (((Finset.univ.filter (fun j : Fin n =>
                            svals (maskedScaled p (Xi ω) (Mask ω)) j ≤
                              mpQuantile ((n : ℝ) / (m : ℝ)) n i - tau)).card : ℝ)) -
                      (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..(mpQuantile ((n : ℝ) / (m : ℝ)) n i - tau),
                        rootedMPDensity ((n : ℝ) / (m : ℝ)) u)| ≤
                    2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
  /- @proof-region region.target-node.session.22592961e5824058 begin -/
  have statopia_math_node_2704888616_ccc54d35 := sparse_cdf_comparison_of_polynomial_rate.{u} beta hbeta h_dense

  intro D0 hD0 rhoMinus h_rhoMinus_pos h_rhoMinus_le Kt hKt alpha0 h_alpha0
  obtain ⟨c0, hc0, m1, hExp⟩ :=
    statopia_math_node_2704888616_ccc54d35 D0 hD0 rhoMinus h_rhoMinus_pos h_rhoMinus_le Kt hKt
      alpha0 h_alpha0
  obtain ⟨cRho, tRho, hcRho, htRho, htail⟩ :=
    statopia_math_node_2026933490_bd269a1d rhoMinus h_rhoMinus_pos h_rhoMinus_le
  have harith : ∃ M2 : ℕ, m1 ≤ M2 ∧ ∀ (m n : ℕ), M2 ≤ m → 1 ≤ n → n ≤ m →
      rhoMinus ≤ (n : ℝ) / (m : ℝ) →
      (D0 + 3) * Real.log (n : ℝ) + Real.log 8 ≤
        (n : ℝ) * (c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2)) ^ 2 / 2 := by
    have hD3pos : (0 : ℝ) < D0 + 3 := by linarith
    have hratio : Filter.Tendsto (fun x : ℝ => Real.log x ^ 4 / x) Filter.atTop (nhds 0) :=
      (Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero
    have hratio3 : Filter.Tendsto (fun x : ℝ => Real.log x ^ 3 / x) Filter.atTop (nhds 0) :=
      (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero
    have hev4 : ∀ᶠ x : ℝ in Filter.atTop,
        Real.log x ^ 4 ≤ ((rhoMinus * c0 ^ 2 / 4) / (D0 + 3)) * x := by
      have hle : (0 : ℝ) < (rhoMinus * c0 ^ 2 / 4) / (D0 + 3) := by positivity
      filter_upwards [hratio.eventually (eventually_le_nhds hle),
        Filter.eventually_gt_atTop (0 : ℝ)] with x hx hx0
      have hx0' : x ≠ 0 := ne_of_gt hx0
      calc Real.log x ^ 4 = Real.log x ^ 4 / x * x := by field_simp
        _ ≤ ((rhoMinus * c0 ^ 2 / 4) / (D0 + 3)) * x :=
            mul_le_mul_of_nonneg_right hx (le_of_lt hx0)
    have hev3 : ∀ᶠ x : ℝ in Filter.atTop,
        Real.log 8 * Real.log x ^ 3 ≤ (rhoMinus * c0 ^ 2 / 4) * x := by
      have h8pos : (0 : ℝ) < Real.log 8 := Real.log_pos (by norm_num)
      have hle : (0 : ℝ) < (rhoMinus * c0 ^ 2 / 4) / Real.log 8 := by positivity
      filter_upwards [hratio3.eventually (eventually_le_nhds hle),
        Filter.eventually_gt_atTop (0 : ℝ)] with x hx hx0
      have hx0' : x ≠ 0 := ne_of_gt hx0
      have h1 : Real.log x ^ 3 ≤ ((rhoMinus * c0 ^ 2 / 4) / Real.log 8) * x := by
        calc Real.log x ^ 3 = Real.log x ^ 3 / x * x := by field_simp
          _ ≤ ((rhoMinus * c0 ^ 2 / 4) / Real.log 8) * x :=
              mul_le_mul_of_nonneg_right hx (le_of_lt hx0)
      calc Real.log 8 * Real.log x ^ 3
          ≤ Real.log 8 * (((rhoMinus * c0 ^ 2 / 4) / Real.log 8) * x) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt h8pos)
        _ = (rhoMinus * c0 ^ 2 / 4) * x := by field_simp
    have hAev : ∀ᶠ m : ℕ in Filter.atTop,
        (D0 + 3) * Real.log (m : ℝ) ^ 4 ≤ (rhoMinus * c0 ^ 2 / 4) * (m : ℝ) := by
      have hev4N : ∀ᶠ m : ℕ in Filter.atTop,
          Real.log (m : ℝ) ^ 4 ≤ ((rhoMinus * c0 ^ 2 / 4) / (D0 + 3)) * (m : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually hev4
      filter_upwards [hev4N] with m hm
      calc (D0 + 3) * Real.log (m : ℝ) ^ 4
          ≤ (D0 + 3) * (((rhoMinus * c0 ^ 2 / 4) / (D0 + 3)) * (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hm (le_of_lt hD3pos)
        _ = (rhoMinus * c0 ^ 2 / 4) * (m : ℝ) := by field_simp
    have hBev : ∀ᶠ m : ℕ in Filter.atTop,
        Real.log 8 * Real.log (m : ℝ) ^ 3 ≤ (rhoMinus * c0 ^ 2 / 4) * (m : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually hev3
    obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp (hAev.and hBev)
    refine ⟨max M0 (max m1 2), le_trans (le_max_left m1 2) (le_max_right M0 (max m1 2)), ?_⟩
    intro m n hm2 hn hnm hrho
    have hm0 : M0 ≤ m := le_trans (le_max_left M0 (max m1 2)) hm2
    have hm3 : 2 ≤ m := le_trans (le_trans (le_max_right m1 2) (le_max_right M0 (max m1 2))) hm2
    have hm1 : 1 ≤ m := le_trans hn hnm
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      have : (0 : ℕ) < m := lt_of_lt_of_le (by norm_num) hm1
      exact_mod_cast this
    have hlogpos : (0 : ℝ) < Real.log (m : ℝ) := by
      apply Real.log_pos
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
      linarith
    have hnlog : Real.log (n : ℝ) ≤ Real.log (m : ℝ) := by
      apply Real.log_le_log
      · have : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
        exact_mod_cast this
      · exact_mod_cast hnm
    have hD3nn : (0 : ℝ) ≤ D0 + 3 := le_of_lt hD3pos
    have h1 : (D0 + 3) * Real.log (n : ℝ) + Real.log 8 ≤
        (D0 + 3) * Real.log (m : ℝ) + Real.log 8 := by nlinarith [hD3nn]
    have hlog3pos : (0 : ℝ) < Real.log (m : ℝ) ^ 3 := by positivity
    have hrho_mul : rhoMinus * (m : ℝ) ≤ (n : ℝ) := by
      have h : rhoMinus * (m : ℝ) ≤ ((n : ℝ) / (m : ℝ)) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hrho (le_of_lt hmpos)
      have heq : ((n : ℝ) / (m : ℝ)) * (m : ℝ) = (n : ℝ) := by field_simp
      linarith [h, heq]
    have hbound := hM0 m hm0
    have step3 : 2 * ((D0 + 3) * Real.log (m : ℝ) ^ 4 + Real.log 8 * Real.log (m : ℝ) ^ 3)
        ≤ 2 * ((rhoMinus * c0 ^ 2 / 4) * (m : ℝ) + (rhoMinus * c0 ^ 2 / 4) * (m : ℝ)) := by
      linarith [hbound.1, hbound.2]
    have step4 : 2 * ((rhoMinus * c0 ^ 2 / 4) * (m : ℝ) + (rhoMinus * c0 ^ 2 / 4) * (m : ℝ))
        ≤ (n : ℝ) * c0 ^ 2 := by nlinarith [hrho_mul]
    have key : ((D0 + 3) * Real.log (n : ℝ) + Real.log 8) * (2 * Real.log (m : ℝ) ^ 3) ≤
        (n : ℝ) * c0 ^ 2 := by
      have hnon : (0 : ℝ) ≤ 2 * Real.log (m : ℝ) ^ 3 := le_of_lt (by positivity)
      have step1 : ((D0 + 3) * Real.log (n : ℝ) + Real.log 8) * (2 * Real.log (m : ℝ) ^ 3)
          ≤ ((D0 + 3) * Real.log (m : ℝ) + Real.log 8) * (2 * Real.log (m : ℝ) ^ 3) := by
        have h := mul_le_mul_of_nonneg_right h1 hnon
        linarith [h]
      have step2 : ((D0 + 3) * Real.log (m : ℝ) + Real.log 8) * (2 * Real.log (m : ℝ) ^ 3)
          = 2 * ((D0 + 3) * Real.log (m : ℝ) ^ 4 + Real.log 8 * Real.log (m : ℝ) ^ 3) := by
        ring
      calc ((D0 + 3) * Real.log (n : ℝ) + Real.log 8) * (2 * Real.log (m : ℝ) ^ 3)
          ≤ ((D0 + 3) * Real.log (m : ℝ) + Real.log 8) * (2 * Real.log (m : ℝ) ^ 3) := step1
        _ = 2 * ((D0 + 3) * Real.log (m : ℝ) ^ 4 + Real.log 8 * Real.log (m : ℝ) ^ 3) := step2
        _ ≤ 2 * ((rhoMinus * c0 ^ 2 / 4) * (m : ℝ) + (rhoMinus * c0 ^ 2 / 4) * (m : ℝ)) := step3
        _ ≤ (n : ℝ) * c0 ^ 2 := step4
    have hsq : (c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2)) ^ 2
        = c0 ^ 2 * (Real.log (m : ℝ) ^ 3)⁻¹ := by
      have hδ : deltaM m = (Real.log (m : ℝ))⁻¹ := rfl
      rw [mul_pow, hδ]
      congr 1
      have hpos : (0 : ℝ) < (Real.log (m : ℝ))⁻¹ := inv_pos.mpr hlogpos
      have hA : (Real.rpow ((Real.log (m : ℝ))⁻¹) ((3 : ℝ) / 2)) ^ 2
          = Real.rpow ((Real.log (m : ℝ))⁻¹) ((3 : ℝ) / 2 * ((2 : ℕ) : ℝ)) :=
        (Real.rpow_mul_natCast (le_of_lt hpos) ((3 : ℝ) / 2) 2).symm
      rw [hA, show (3 : ℝ) / 2 * ((2 : ℕ) : ℝ) = 3 by norm_num]
      have h2' : Real.rpow ((Real.log (m : ℝ))⁻¹) (3 : ℝ) = ((Real.log (m : ℝ))⁻¹) ^ 3 :=
        Real.rpow_natCast _ 3
      rw [h2', inv_pow]
    rw [hsq]
    have hne3 : Real.log (m : ℝ) ^ 3 ≠ 0 := ne_of_gt hlog3pos
    have hfinal : ((D0 + 3) * Real.log (n : ℝ) + Real.log 8)
        ≤ (n : ℝ) * (c0 ^ 2 * (Real.log (m : ℝ) ^ 3)⁻¹) / 2 := by
      have hmul := mul_le_mul_of_nonneg_right key
        (show (0 : ℝ) ≤ (Real.log (m : ℝ) ^ 3)⁻¹ / 2 by positivity)
      calc ((D0 + 3) * Real.log (n : ℝ) + Real.log 8)
          = ((D0 + 3) * Real.log (n : ℝ) + Real.log 8) * (2 * Real.log (m : ℝ) ^ 3) *
              ((Real.log (m : ℝ) ^ 3)⁻¹ / 2) := by field_simp
        _ ≤ ((n : ℝ) * c0 ^ 2) * ((Real.log (m : ℝ) ^ 3)⁻¹ / 2) := hmul
        _ = (n : ℝ) * (c0 ^ 2 * (Real.log (m : ℝ) ^ 3)⁻¹) / 2 := by ring
    exact hfinal
  obtain ⟨M2₀, hM2m1, hM2⟩ := harith
  refine ⟨c0, hc0, max M2₀ 2, ?_⟩
  intro m n hn hnm hM2le hrho_lo hrho_hi p hp0 hp1 hsparse Ω instΩ μ instμ Xi Mask hXi_meas
    hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val hMask_law
    hMask_indep hIndep tau htau
  have hm2 : 2 ≤ m := le_trans (le_max_right M2₀ 2) hM2le
  have hm : 1 ≤ m := le_trans hn hnm
  have hm1 : m1 ≤ m := le_trans hM2m1 (le_trans (le_max_left M2₀ 2) hM2le)
  have hsup := hExp m n hn hnm hm1 hrho_lo hrho_hi p hp0 hp1 hsparse μ Xi Mask hXi_meas
    hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val hMask_law
    hMask_indep hIndep
  have harith_m := hM2 m n (le_trans (le_max_left M2₀ 2) hM2le) hn hnm hrho_lo
  set rho : ℝ := (n : ℝ) / (m : ℝ) with hrho_def
  set d : ℝ := c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) with hd_def
  have hdpos : 0 < d := by
    rw [hd_def]
    have hδ : 0 < deltaM m := by
      rw [deltaM]
      exact inv_pos.mpr (Real.log_pos (by exact_mod_cast hm2))
    exact mul_pos hc0 (Real.rpow_pos_of_pos hδ _)
  have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
  set FA : Ω → ℝ → ℝ := fun ω x =>
    (n : ℝ)⁻¹ * ((Finset.univ.filter (fun j : Fin n =>
      svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)).card : ℝ) with hFA_def
  set EF : ℝ → ℝ := fun x => ∫ ω, FA ω x ∂μ with hEF_def
  set GR : ℝ → ℝ := fun x => ∫ u in (mpLambdaMinus rho)..x, rootedMPDensity rho u with hGR_def
  have hsup' : sSup (Set.range fun x : {y : ℝ // 0 ≤ y} => |EF (x : ℝ) - GR (x : ℝ)|) ≤ d :=
    hsup
  have hconc : ∀ (x u : ℝ), 0 < u →
      μ {ω | u ≤ |FA ω x - EF x|} ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * u ^ 2 / 2)) := by
    intro x u hu
    have h := statopia_math_node_3073978187_c577ca52 m n hm hn hnm p hp0 hp1 μ Xi Mask hXi_meas
      hMask_meas hXi_indep hMask_indep hIndep x u hu
    simpa [hFA_def, hEF_def] using h
  have harith_d : (D0 + 3) * Real.log (n : ℝ) + Real.log 8 ≤ (n : ℝ) * d ^ 2 / 2 := by
    rw [hd_def]
    exact harith_m
  have hnpos0 : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
    exact_mod_cast h
  have hGR_hi : ∀ x : ℝ, mpLambdaPlus rho ≤ x → GR x = 1 := by
    intro x hx
    have h := statopia_math_node_384144625_a59c7546 rhoMinus h_rhoMinus_pos h_rhoMinus_le rho
      hrho_lo hrho_hi
    rw [hGR_def]
    exact h.2.2 x hx
  have hGR_abs_hi : ∀ x : ℝ, mpLambdaPlus rho ≤ x → |GR x| ≤ 1 := by
    intro x hx
    rw [hGR_hi x hx]
    norm_num
  have hLam_minus_nonneg : (0 : ℝ) ≤ mpLambdaMinus rho := by
    have h1 : Real.sqrt rho ≤ 1 := by
      have h2 : Real.sqrt rho ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hrho_hi
      simpa using h2
    have h3 : mpLambdaMinus rho = 1 - Real.sqrt rho := rfl
    rw [h3]
    linarith
  have hQuant_mem : ∀ i : Fin n,
      mpLambdaMinus rho ≤ mpQuantile rho n i ∧ mpQuantile rho n i ≤ mpLambdaPlus rho := by
    intro i
    exact ((htail rho hrho_lo hrho_hi).2.2.2.2.2.1 n hn i).1
  have hQuant_nonneg : ∀ i : Fin n, (0 : ℝ) ≤ mpQuantile rho n i := by
    intro i
    exact le_trans hLam_minus_nonneg (hQuant_mem i).1
  have hGrid_nonneg : ∀ i : Fin n, (0 : ℝ) ≤ mpQuantile rho n i + tau := by
    intro i
    have h := hQuant_nonneg i
    linarith
  have hEF_zero : ∀ x : ℝ, x < 0 → EF x = 0 := by
    intro x hx
    have hFA0 : ∀ ω : Ω, FA ω x = 0 := by
      intro ω
      have hempty : (Finset.univ.filter (fun j : Fin n =>
          svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)) = ∅ := by
        apply Finset.filter_false_of_mem
        intro j _
        have h1 : (0 : ℝ) ≤ svals (maskedScaled p (Xi ω) (Mask ω)) j := Real.sqrt_nonneg _
        intro hle
        linarith
      rw [hFA_def]
      simp [hempty]
    rw [hEF_def]
    simp [hFA0]
  have hFA_abs : ∀ (ω : Ω) (x : ℝ), |FA ω x| ≤ 1 := by
    intro ω x
    have hcard : ((Finset.univ.filter (fun j : Fin n =>
        svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)).card : ℝ) ≤ (n : ℝ) := by
      have h := Finset.card_filter_le (Finset.univ : Finset (Fin n))
        (fun j : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)
      simpa using h
    have hnn : (0 : ℝ) ≤ ((Finset.univ.filter (fun j : Fin n =>
        svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)).card : ℝ) := by positivity
    have hval : FA ω x = (n : ℝ)⁻¹ * ((Finset.univ.filter (fun j : Fin n =>
        svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)).card : ℝ) := by
      rw [hFA_def]
    have hnonneg : (0 : ℝ) ≤ FA ω x := by
      rw [hval]
      positivity
    have hub : FA ω x ≤ 1 := by
      rw [hval]
      have hinv : (n : ℝ)⁻¹ * (n : ℝ) = 1 := by field_simp
      have hstep1 : (n : ℝ)⁻¹ * ((Finset.univ.filter (fun j : Fin n =>
          svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)).card : ℝ)
          ≤ (n : ℝ)⁻¹ * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hcard (le_of_lt (inv_pos.mpr hnpos0))
      rw [hinv] at hstep1
      exact hstep1
    rw [abs_of_nonneg hnonneg]
    exact hub
  have hdensity_zero : ∀ u : ℝ, u ≤ mpLambdaMinus rho → rootedMPDensity rho u = 0 := by
    intro u hu
    rcases lt_or_eq_of_le hu with hlt | heq
    · have hcond : ¬ (mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho) := by
        intro h
        exact absurd h.1 (not_le.mpr hlt)
      simp [rootedMPDensity, hcond]
    · rw [heq]
      simp [rootedMPDensity]
  have hGR_zero : ∀ x : ℝ, x ≤ mpLambdaMinus rho → GR x = 0 := by
    intro x hx
    have hcongr : (∫ u in (mpLambdaMinus rho)..x, rootedMPDensity rho u)
        = ∫ u in (mpLambdaMinus rho)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have h2 : u ∈ Set.Icc (min (mpLambdaMinus rho) x) (max (mpLambdaMinus rho) x) := hu
      rw [min_eq_right hx, max_eq_left hx] at h2
      exact hdensity_zero u h2.2
    rw [show GR x = (∫ u in (mpLambdaMinus rho)..x, rootedMPDensity rho u) from rfl]
    rw [hcongr]
    simp
  have hcdf_nonneg : ∀ x : ℝ, 0 ≤ x → |EF x - GR x| ≤ d := by
    have hEFb : ∀ y : ℝ, |EF y| ≤ 3 := by
      have hge4 : (4 : ℝ) ≤ Real.exp 2 := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by
          have h := Real.add_one_le_exp 1
          linarith only [h]
        have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith only [h2, hsq]
      have hquarter : Real.exp (-2) ≤ 1 / 4 := by
        have hpos : (0 : ℝ) < Real.exp (-2) := Real.exp_pos (-2)
        have hne : Real.exp 2 ≠ 0 := ne_of_gt (Real.exp_pos 2)
        have hprod : Real.exp (-2) * Real.exp 2 = 1 := by
          rw [Real.exp_neg]
          field_simp
        nlinarith only [hpos, hge4, hprod]
      have hsmall : 2 * Real.exp (-(n : ℝ) * (2 : ℝ) ^ 2 / 2) ≤ 1 / 2 := by
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hmono : Real.exp (-(n : ℝ) * (2 : ℝ) ^ 2 / 2) ≤ Real.exp (-2) := by
          apply Real.exp_monotone
          have harg : (-(n : ℝ) * (2 : ℝ) ^ 2 / 2) = -(2 * (n : ℝ)) := by ring
          rw [harg]
          linarith only [hn1]
        linarith only [hmono, hquarter]
      intro y
      have hstep : μ {ω : Ω | (2 : ℝ) ≤ |FA ω y - EF y|} ≤ ENNReal.ofReal (1 / 2) :=
        le_trans (hconc y 2 (by norm_num)) (ENNReal.ofReal_le_ofReal hsmall)
      have hne : {ω : Ω | (2 : ℝ) ≤ |FA ω y - EF y|} ≠ Set.univ := by
        intro hU
        rw [hU, measure_univ, ← ENNReal.ofReal_one] at hstep
        have hle' : (1 : ℝ) ≤ 1 / 2 :=
          (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hstep
        norm_num at hle'
      have hex : ∃ ω : Ω, ¬((2 : ℝ) ≤ |FA ω y - EF y|) := by
        by_contra h
        push_neg at h
        exact hne (by
          ext ω
          exact ⟨fun _ => Set.mem_univ ω, fun _ => h ω⟩)
      obtain ⟨ω, hω⟩ := hex
      have hω2 : |FA ω y - EF y| < 2 := not_le.mp hω
      have hd : FA ω y + -(FA ω y - EF y) = EF y := by ring
      have htri := abs_add_le (FA ω y) (-(FA ω y - EF y))
      rw [abs_neg, hd] at htri
      have hfa : |FA ω y| ≤ 1 := hFA_abs ω y
      linarith only [htri, hfa, hω2]
    have hGRb : ∀ y : ℝ, 0 ≤ y → |GR y| ≤ 1 := by
      intro y hy
      by_cases h1 : y ≤ mpLambdaMinus rho
      · rw [hGR_zero y h1, abs_zero]
        norm_num
      · by_cases h2 : mpLambdaPlus rho ≤ y
        · exact hGR_abs_hi y h2
        · have hy1 : mpLambdaMinus rho < y := not_le.mp h1
          have hy2 : y < mpLambdaPlus rho := not_le.mp h2
          have hLam_le : mpLambdaMinus rho ≤ mpLambdaPlus rho := by
            rw [show mpLambdaMinus rho = 1 - Real.sqrt rho from rfl,
              show mpLambdaPlus rho = 1 + Real.sqrt rho from rfl]
            linarith [Real.sqrt_nonneg rho]
          have hmass : (∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u)
              = 1 := (htail rho hrho_lo hrho_hi).1
          have hInt : IntervalIntegrable (rootedMPDensity rho) volume
              (mpLambdaMinus rho) (mpLambdaPlus rho) :=
            intervalIntegral.intervalIntegrable_of_integral_ne_zero (by rw [hmass]; norm_num)
          have hsub : Set.uIoc (mpLambdaMinus rho) y ⊆
              Set.uIoc (mpLambdaMinus rho) (mpLambdaPlus rho) := by
            intro z hz
            simp only [Set.uIoc, Set.mem_Ioc] at hz ⊢
            rw [min_eq_left (le_of_lt hy1), max_eq_right (le_of_lt hy1)] at hz
            rw [min_eq_left hLam_le, max_eq_right hLam_le]
            exact ⟨hz.1, le_trans hz.2 (le_of_lt hy2)⟩
          have hνnn : ∀ u : ℝ, 0 ≤ rootedMPDensity rho u := by
            intro u
            have hdef : rootedMPDensity rho u
                = (1 / Real.pi) *
                    Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) /
                      (rho * u) *
                    (if mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho then (1 : ℝ) else 0) := rfl
            rw [hdef]
            by_cases hc : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho
            · rw [if_pos hc]
              have hnum1 : (0 : ℝ) ≤ (1 / Real.pi) *
                  Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) :=
                mul_nonneg (by positivity) (Real.sqrt_nonneg _)
              have hden : (0 : ℝ) ≤ rho * u :=
                mul_nonneg (le_trans (le_of_lt h_rhoMinus_pos) hrho_lo)
                  (le_trans hLam_minus_nonneg hc.1)
              simpa using div_nonneg hnum1 hden
            · rw [if_neg hc]
              simp
          have hbound := intervalIntegral.abs_integral_mono_interval hsub
            (Filter.Eventually.of_forall hνnn) hInt
          rw [hmass] at hbound
          rw [show GR y = (∫ u in (mpLambdaMinus rho)..y, rootedMPDensity rho u) from rfl]
          simpa using hbound

    have hbdd : BddAbove (Set.range fun y : {z : ℝ // 0 ≤ z} => |EF (y : ℝ) - GR (y : ℝ)|) := by
      refine ⟨4, ?_⟩
      rintro _ ⟨y, rfl⟩
      show |EF (y : ℝ) - GR (y : ℝ)| ≤ 4
      have h1 : |EF (y : ℝ)| ≤ 3 := hEFb _
      have h2 : |GR (y : ℝ)| ≤ 1 := hGRb _ y.2
      have hup : EF (y : ℝ) - GR (y : ℝ) ≤ 4 := by
        linarith [le_abs_self (EF (y : ℝ)), neg_le_abs (GR (y : ℝ))]
      have hdn : -(4 : ℝ) ≤ EF (y : ℝ) - GR (y : ℝ) := by
        linarith [neg_le_abs (EF (y : ℝ)), le_abs_self (GR (y : ℝ))]
      by_cases hs : 0 ≤ EF (y : ℝ) - GR (y : ℝ)
      · rw [abs_of_nonneg hs]
        linarith
      · rw [abs_of_neg (not_le.mp hs)]
        linarith
    intro x hx
    have hmem : |EF x - GR x| ∈ Set.range fun y : {z : ℝ // 0 ≤ z} => |EF (y : ℝ) - GR (y : ℝ)| :=
      ⟨⟨x, hx⟩, rfl⟩
    exact le_trans (le_csSup hbdd hmem) hsup'
  have hcdf : ∀ x : ℝ, |EF x - GR x| ≤ d := by
    intro x
    by_cases hx : x < 0
    · rw [hEF_zero x hx, hGR_zero x (le_trans (le_of_lt hx) hLam_minus_nonneg)]
      simpa using le_of_lt hdpos
    · exact hcdf_nonneg x (not_lt.mp hx)
  set Bad : Fin n → Set Ω := fun i =>
    {ω | d ≤ |FA ω (mpQuantile rho n i + tau) - EF (mpQuantile rho n i + tau)|} with hBad_def
  set Bad2 : Fin n → Set Ω := fun i =>
    {ω | d ≤ |FA ω (mpQuantile rho n i - tau) - EF (mpQuantile rho n i - tau)|} with hBad2_def
  have hHullMeas : MeasurableSet (toMeasurable μ ((⋃ i, Bad i) ∪ (⋃ i, Bad2 i))) :=
    measurableSet_toMeasurable μ ((⋃ i, Bad i) ∪ (⋃ i, Bad2 i))
  have hHullSub : (⋃ i, Bad i) ∪ (⋃ i, Bad2 i) ⊆
      toMeasurable μ ((⋃ i, Bad i) ∪ (⋃ i, Bad2 i)) :=
    subset_toMeasurable μ ((⋃ i, Bad i) ∪ (⋃ i, Bad2 i))
  have hHullμ : μ (toMeasurable μ ((⋃ i, Bad i) ∪ (⋃ i, Bad2 i)))
      = μ ((⋃ i, Bad i) ∪ (⋃ i, Bad2 i)) := measure_toMeasurable _
  refine ⟨(toMeasurable μ ((⋃ i, Bad i) ∪ (⋃ i, Bad2 i)))ᶜ, ?_, ?_, ?_⟩
  · exact MeasurableSet.compl hHullMeas
  · rw [compl_compl, hHullμ]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
      exact_mod_cast this
    have hb1 : ∀ i : Fin n, μ (Bad i) ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2)) := by
      intro i
      simpa only [hBad_def] using hconc (mpQuantile rho n i + tau) d hdpos
    have hb2 : ∀ i : Fin n, μ (Bad2 i) ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2)) := by
      intro i
      simpa only [hBad2_def] using hconc (mpQuantile rho n i - tau) d hdpos
    have hsum : (∑ i : Fin n, ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2)))
        = ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (f := fun _ : Fin n => 2 * Real.exp (-(n : ℝ) * d ^ 2 / 2)) (fun i _ => by positivity)]
      congr 1
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hA1 : μ (⋃ i, Bad i) ≤
        ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) := by
      calc μ (⋃ i, Bad i) = μ (⋃ i ∈ Finset.univ, Bad i) := by simp
        _ ≤ ∑ i ∈ Finset.univ, μ (Bad i) :=
            MeasureTheory.measure_biUnion_finset_le Finset.univ Bad
        _ ≤ ∑ i ∈ Finset.univ, ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2)) :=
            Finset.sum_le_sum (fun i _ => hb1 i)
        _ = ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) := by
            simpa using hsum
    have hA2 : μ (⋃ i, Bad2 i) ≤
        ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) := by
      calc μ (⋃ i, Bad2 i) = μ (⋃ i ∈ Finset.univ, Bad2 i) := by simp
        _ ≤ ∑ i ∈ Finset.univ, μ (Bad2 i) :=
            MeasureTheory.measure_biUnion_finset_le Finset.univ Bad2
        _ ≤ ∑ i ∈ Finset.univ, ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2)) :=
            Finset.sum_le_sum (fun i _ => hb2 i)
        _ = ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) := by
            simpa using hsum
    have ha : Real.exp (-(n : ℝ) * d ^ 2 / 2) ≤ Real.rpow (n : ℝ) (-(D0 + 3)) / 8 := by
      have hexp1 : Real.exp (-(n : ℝ) * d ^ 2 / 2) ≤
          Real.exp (-((D0 + 3) * Real.log (n : ℝ) + Real.log 8)) := by
        apply Real.exp_le_exp.mpr
        linarith [harith_d]
      have hexp2 : Real.exp (-((D0 + 3) * Real.log (n : ℝ) + Real.log 8)) =
          Real.rpow (n : ℝ) (-(D0 + 3)) / 8 := by
        rw [show -((D0 + 3) * Real.log (n : ℝ) + Real.log 8)
            = (-(D0 + 3)) * Real.log (n : ℝ) + (-(Real.log 8)) by ring]
        rw [Real.exp_add]
        have h3 : Real.exp ((-(D0 + 3)) * Real.log (n : ℝ)) = Real.rpow (n : ℝ) (-(D0 + 3)) := by
          have h := Real.rpow_def_of_pos hn_pos (y := -(D0 + 3))
          rw [show Real.exp ((-(D0 + 3)) * Real.log (n : ℝ))
              = Real.exp (Real.log (n : ℝ) * (-(D0 + 3))) from by ring_nf]
          exact h.symm
        rw [h3]
        have h4 : Real.exp (-(Real.log 8)) = 1 / 8 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
          norm_num
        rw [h4]
        ring
      rw [hexp2] at hexp1
      exact hexp1
    have hb : (n : ℝ) * Real.rpow (n : ℝ) (-(D0 + 3)) = Real.rpow (n : ℝ) (-(D0 + 2)) := by
      have h1 : Real.rpow (n : ℝ) (1 + (-(D0 + 3)))
          = Real.rpow (n : ℝ) 1 * Real.rpow (n : ℝ) (-(D0 + 3)) :=
        Real.rpow_add hn_pos 1 (-(D0 + 3))
      rw [show (1 : ℝ) + (-(D0 + 3)) = -(D0 + 2) by ring] at h1
      have hone : Real.rpow (n : ℝ) 1 = (n : ℝ) := Real.rpow_one _
      rw [hone] at h1
      exact h1.symm
    have hreal : ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) * 2
        ≤ 4 * Real.rpow (n : ℝ) (-(D0 + 2)) := by
      have h8nn : (0 : ℝ) ≤ Real.rpow (n : ℝ) (-(D0 + 3)) :=
        Real.rpow_nonneg (le_of_lt hn_pos) _
      have hstep : Real.exp (-(n : ℝ) * d ^ 2 / 2) ≤ Real.rpow (n : ℝ) (-(D0 + 3)) := by
        linarith [ha, h8nn]
      have e1 : 2 * Real.exp (-(n : ℝ) * d ^ 2 / 2) ≤ 2 * Real.rpow (n : ℝ) (-(D0 + 3)) := by
        linarith [hstep]
      have e2 : (n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))
          ≤ (n : ℝ) * (2 * Real.rpow (n : ℝ) (-(D0 + 3))) :=
        mul_le_mul_of_nonneg_left e1 (le_of_lt hn_pos)
      have e3 : ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) * 2
          ≤ ((n : ℝ) * (2 * Real.rpow (n : ℝ) (-(D0 + 3)))) * 2 :=
        mul_le_mul_of_nonneg_right e2 (by norm_num)
      have e4 : ((n : ℝ) * (2 * Real.rpow (n : ℝ) (-(D0 + 3)))) * 2
          = 4 * Real.rpow (n : ℝ) (-(D0 + 2)) := by
        have hb' : (n : ℝ) * Real.rpow (n : ℝ) (-(D0 + 3)) = Real.rpow (n : ℝ) (-(D0 + 2)) := hb
        calc ((n : ℝ) * (2 * Real.rpow (n : ℝ) (-(D0 + 3)))) * 2
            = 4 * ((n : ℝ) * Real.rpow (n : ℝ) (-(D0 + 3))) := by ring
          _ = 4 * Real.rpow (n : ℝ) (-(D0 + 2)) := by rw [hb']
      calc ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) * 2
          ≤ ((n : ℝ) * (2 * Real.rpow (n : ℝ) (-(D0 + 3)))) * 2 := e3
        _ = 4 * Real.rpow (n : ℝ) (-(D0 + 2)) := e4
    have hunion : ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) +
          ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2)))
        = ENNReal.ofReal (((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) * 2) := by
      have hmul : ENNReal.ofReal (((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) * 2)
          = ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) *
              ENNReal.ofReal (2 : ℝ) :=
        ENNReal.ofReal_mul
          (p := (n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) (q := 2) (by positivity)
      have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := ENNReal.ofReal_natCast 2
      rw [hmul, h2]
      have hcomm : ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) * (2 : ENNReal)
          = 2 * ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) := mul_comm _ _
      rw [hcomm]
      exact (two_mul (ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))))).symm
    calc μ ((⋃ i, Bad i) ∪ (⋃ i, Bad2 i))
        ≤ μ (⋃ i, Bad i) + μ (⋃ i, Bad2 i) := MeasureTheory.measure_union_le _ _
      _ ≤ ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) +
            ENNReal.ofReal ((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) := add_le_add hA1 hA2
      _ = ENNReal.ofReal (((n : ℝ) * (2 * Real.exp (-(n : ℝ) * d ^ 2 / 2))) * 2) := hunion
      _ ≤ ENNReal.ofReal (4 * Real.rpow (n : ℝ) (-(D0 + 2))) := ENNReal.ofReal_le_ofReal hreal
  · intro ω hω i
    have hS : ω ∉ (⋃ i, Bad i) ∪ (⋃ i, Bad2 i) := fun h => hω (hHullSub h)
    have hA : ∀ j, ω ∉ Bad j := by
      have h : ω ∉ ⋃ j, Bad j := fun h => hS (Or.inl h)
      simpa only [Set.mem_iUnion, not_exists] using h
    have hB : ∀ j, ω ∉ Bad2 j := by
      have h : ω ∉ ⋃ j, Bad2 j := fun h => hS (Or.inr h)
      simpa only [Set.mem_iUnion, not_exists] using h
    have e1 : |FA ω (mpQuantile rho n i + tau) - EF (mpQuantile rho n i + tau)| < d := by
      have h := hA i
      simpa only [hBad_def, Set.mem_setOf_eq, not_le] using h
    have e2 : |FA ω (mpQuantile rho n i - tau) - EF (mpQuantile rho n i - tau)| < d := by
      have h := hB i
      simpa only [hBad2_def, Set.mem_setOf_eq, not_le] using h
    have tri : ∀ x : ℝ, |FA ω x - EF x| < d → |FA ω x - GR x| ≤ 2 * d := by
      intro x hx
      have hc : |EF x - GR x| ≤ d := hcdf x
      have hsplit : FA ω x - GR x = (FA ω x - EF x) + (EF x - GR x) := by ring
      rw [hsplit]
      have hle : |(FA ω x - EF x) + (EF x - GR x)| ≤ |FA ω x - EF x| + |EF x - GR x| :=
        abs_add_le _ _
      linarith
    have k1 : |FA ω (mpQuantile rho n i + tau) - GR (mpQuantile rho n i + tau)| ≤ 2 * d :=
      tri _ e1
    have k2 : |FA ω (mpQuantile rho n i - tau) - GR (mpQuantile rho n i - tau)| ≤ 2 * d :=
      tri _ e2
    have c1 : |(n : ℝ)⁻¹ * (((Finset.univ.filter (fun j : Fin n =>
        svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ mpQuantile rho n i + tau)).card : ℝ)) -
        (∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i + tau), rootedMPDensity rho u)|
        = |FA ω (mpQuantile rho n i + tau) - GR (mpQuantile rho n i + tau)| := by
      simp only [hFA_def, hGR_def]
    have c2 : |(n : ℝ)⁻¹ * (((Finset.univ.filter (fun j : Fin n =>
        svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ mpQuantile rho n i - tau)).card : ℝ)) -
        (∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i - tau), rootedMPDensity rho u)|
        = |FA ω (mpQuantile rho n i - tau) - GR (mpQuantile rho n i - tau)| := by
      simp only [hFA_def, hGR_def]
    constructor
    · rw [c1]
      calc |FA ω (mpQuantile rho n i + tau) - GR (mpQuantile rho n i + tau)| ≤ 2 * d := k1
        _ = 2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
            rw [hd_def]
            ring
    · rw [c2]
      calc |FA ω (mpQuantile rho n i - tau) - GR (mpQuantile rho n i - tau)| ≤ 2 * d := k2
        _ = 2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
            rw [hd_def]
            ring
  /- @proof-region region.target-node.session.22592961e5824058 end -/

end Statlib.Imported

#print axioms Statlib.Imported.sparse_cdf_small_of_polynomial_rate

