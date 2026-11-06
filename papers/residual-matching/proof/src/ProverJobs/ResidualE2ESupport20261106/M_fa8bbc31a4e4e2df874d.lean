import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_e317ebe39f07aa48afdc
import ProverJobs.ResidualE2ESupport20261106.M_47e7eee88feb252e903d
import ProverJobs.ResidualE2ESupport20261106.M_d7892410e4d5b04a53d5
import ProverJobs.ResidualE2ESupport20261106.M_2e445e9d131a16ed6935
import ProverJobs.ResidualE2ESupport20261106.M_639d5a54c5a150872e4f
import ProverJobs.ResidualE2ESupport20261106.M_464e186f7956b2f5bffe
import ProverJobs.ResidualE2ESupport20261106.M_eec6d395b85aaad6dc35
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

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
theorem sparse_coarse_rigidity_all_alpha_of_polynomial_rate (beta : ℝ) (hbeta : 1 / 10 < beta)
    (h_dense : DenseSymmetricPolynomialRate beta)
    (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (h_rhoMinus : 0 < rhoMinus)
    (Kt : ℝ) (hKt : 0 < Kt) :
    ∀ (alpha0 : ℝ), 15 < alpha0 →
        ∃ M0 : ℕ, 2 ≤ M0 ∧
          ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
            ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmM : M0 ≤ m)
              (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
              (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
              (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
              (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
              {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
              (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
              (hXi_meas : ∀ i j, Measurable fun ω => Xi ω i j)
              (hXi_int : ∀ i j, Integrable (fun ω => Xi ω i j) μ)
              (hXi_sq_int : ∀ i j, Integrable (fun ω => (Xi ω i j) ^ 2) μ)
              (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
              (hXi_mean : ∀ i j, ∫ ω, Xi ω i j ∂μ = 0)
              (hXi_var : ∀ i j, ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
              (hXi_tail : ∀ i j (t : ℝ), 0 < t →
                μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
              (hMask_meas : ∀ i j, Measurable fun ω => Mask ω i j)
              (hMask_val : ∀ i j ω, Mask ω i j = 0 ∨ Mask ω i j = 1)
              (hMask_law : ∀ i j, μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
              (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
              (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
                (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
            (μ {ω | C * deltaM m <
                  maxDeviation (svals (maskedScaled p (Xi ω) (Mask ω)))
                    (mpQuantile ((n : ℝ) / (m : ℝ)) n)} ≤
                ENNReal.ofReal (c * Real.rpow (n : ℝ) (-D0))) ∧
              (∀ ω, maxDeviation (svals (maskedScaled p (Xi ω) (Mask ω)))
                    (mpQuantile ((n : ℝ) / (m : ℝ)) n) ≤ C * deltaM m →
                  svals (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩ ≤
                    1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + C * deltaM m)
:= by
  have statopia_math_node_3251385243_a8c00c1e := sparse_cdf_small_of_polynomial_rate.{u} beta hbeta h_dense
  have statopia_math_node_270243578_23d43a52 := quantile_of_polynomial_rate.{u} beta hbeta h_dense

  /- @proof-region region.root.ff839656dea7 begin -/
  classical
  intro alpha0 h15
  by_cases hρ1 : rhoMinus ≤ 1
  · obtain ⟨c0, hc0, M2, hgrid_all⟩ :=
      statopia_math_node_3251385243_a8c00c1e D0 hD0 rhoMinus h_rhoMinus hρ1 Kt hKt
        alpha0 h15
    obtain ⟨Ce, hCe, M1, hedges_all⟩ :=
      statopia_math_node_387310739_6591aef4 D0 hD0 rhoMinus h_rhoMinus hρ1 Kt hKt
        alpha0 h15 (max (Kt * (D0 + 12)) 4) (le_max_left _ _)


    obtain ⟨cRho, tRho, hcRho, htRho, hMP⟩ :=
      statopia_math_node_2026933490_bd269a1d rhoMinus h_rhoMinus hρ1
    have hbase : (0 : ℝ) < 2 * c0 / cRho := by positivity
    have hrp : 0 < Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hbase ((2 : ℝ) / 3)
    have hDpos : (0 : ℝ) < Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1 := by linarith
    obtain ⟨mstar0, hmstar0_gt⟩ : ∃ mstar0 : ℕ,
        Real.exp (max 1 ((Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1) * tRho⁻¹)) < (mstar0 : ℝ) :=
      exists_nat_gt _
    have hdelta_gen : ∀ k : ℕ, mstar0 ≤ k →
        deltaM k ≤ min 1 (tRho / (Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1)) := by
      intro k hk
      have hle : (mstar0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hexp : Real.exp (max 1 ((Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1) * tRho⁻¹)) <
          (k : ℝ) := lt_of_lt_of_le hmstar0_gt hle
      have hloggt : max 1 ((Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1) * tRho⁻¹) <
          Real.log (k : ℝ) := by
        have h := Real.log_lt_log (Real.exp_pos _) hexp
        rwa [Real.log_exp] at h
      have h1 : (1 : ℝ) ≤ Real.log (k : ℝ) :=
        le_of_lt (lt_of_le_of_lt (le_max_left _ _) hloggt)
      have h2 : (Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1) * tRho⁻¹ < Real.log (k : ℝ) :=
        lt_of_le_of_lt (le_max_right _ _) hloggt
      have hlogpos : (0 : ℝ) < Real.log (k : ℝ) := by linarith
      refine le_min ?_ ?_
      · simp only [deltaM]
        rw [← one_div]
        exact (div_le_one hlogpos).mpr h1
      · simp only [deltaM]
        rw [div_eq_mul_inv]
        have h2' : Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1 < Real.log (k : ℝ) * tRho := by
          have hmul := mul_lt_mul_of_pos_right h2 htRho
          rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt htRho), mul_one] at hmul
        have hstep := mul_lt_mul_of_pos_left h2' (inv_pos.mpr hlogpos)
        have hgoal : (Real.log (k : ℝ))⁻¹ *
            (Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1) < tRho := by
          calc (Real.log (k : ℝ))⁻¹ * (Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1)
              < (Real.log (k : ℝ))⁻¹ * (Real.log (k : ℝ) * tRho) := hstep
            _ = tRho := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hlogpos), one_mul]
        have hstep2 := mul_lt_mul_of_pos_right hgoal (inv_pos.mpr hDpos)
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hDpos), mul_one] at hstep2
        exact le_of_lt hstep2
    obtain ⟨mstar, hmain⟩ :=
      statopia_math_node_270243578_23d43a52 rhoMinus h_rhoMinus hρ1 alpha0 h15 Kt hKt
        D0 hD0 c0 hc0 Ce hCe cRho hcRho tRho htRho
    refine ⟨max 2 (max mstar (max (max M1 M2) mstar0)),
      le_max_left 2 (max mstar (max (max M1 M2) mstar0)),
      Ce + (Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1), 5, ?_, by norm_num, ?_⟩
    · linarith [hCe, hrp]





    · intro m n hm hn hmM hlo hhi p hp0 hp1 hsparse Ω hΩ μ hμ Xi Mask
        hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
        hMask_meas hMask_val hMask_law hMask_indep hIndep
      have hinner : max mstar (max (max M1 M2) mstar0) ≤ m :=
        le_trans (le_max_right 2 (max mstar (max (max M1 M2) mstar0))) hmM
      have hm2 : 2 ≤ m := le_trans (le_max_left 2 (max mstar (max (max M1 M2) mstar0))) hmM
      have hmstar : mstar ≤ m := le_trans (le_max_left mstar (max (max M1 M2) mstar0)) hinner
      have hT : max (max M1 M2) mstar0 ≤ m :=
        le_trans (le_max_right mstar (max (max M1 M2) mstar0)) hinner
      have hM1 : M1 ≤ m :=
        le_trans (le_trans (le_max_left M1 M2) (le_max_left (max M1 M2) mstar0)) hT
      have hM2 : M2 ≤ m :=
        le_trans (le_trans (le_max_right M1 M2) (le_max_left (max M1 M2) mstar0)) hT
      have hmstar0 : mstar0 ≤ m := le_trans (le_max_right (max M1 M2) mstar0) hT

      have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
      have hnm : n ≤ m := by
        have h' : (n : ℝ) ≤ (m : ℝ) := (div_le_one hm0).mp hhi
        exact_mod_cast h'
      have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
      have hp_gt : 0 < p := by
        have hpos : (0 : ℝ) < Real.rpow (Real.log (m : ℝ)) alpha0 :=
          Real.rpow_pos_of_pos hlog alpha0
        exact pos_of_mul_pos_right (lt_of_lt_of_le hpos hsparse) (le_of_lt hm0)
      have hgridM := hgrid_all m n hn hnm hM2 hlo hhi p hp_gt hp1 hsparse μ Xi Mask
          hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
          hMask_meas hMask_val hMask_law hMask_indep hIndep



      have hMP' := hMP ((n : ℝ) / (m : ℝ)) hlo hhi
      have hquant : ∀ i : Fin n,
          mpLambdaMinus ((n : ℝ) / (m : ℝ)) ≤ mpQuantile ((n : ℝ) / (m : ℝ)) n i ∧
            mpQuantile ((n : ℝ) / (m : ℝ)) n i ≤ mpLambdaPlus ((n : ℝ) / (m : ℝ)) ∧
            (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..(mpQuantile ((n : ℝ) / (m : ℝ)) n i),
                rootedMPDensity ((n : ℝ) / (m : ℝ)) u) =
              1 - (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) := by
        intro i
        have hF := hMP'.2.2.2.2.2.1 n hn i
        exact ⟨hF.1.1, hF.1.2, hF.2.2.1⟩
      have hmass := hMP'.2.2.2.2.2.2
      obtain ⟨b, hb, c, hc, hc_pos, XT, hXT, hXT_mean, hXT_var, hXT_bound, htail, htransfer⟩ :=
        statopia_math_node_676634694_439e1a38 D0 hD0 Kt hKt alpha0 h15 rhoMinus h_rhoMinus hρ1
          (max (Kt * (D0 + 12)) 4) (le_max_left _ _) m n hm2 hn hnm hlo hhi p hp_gt hp1 hsparse
          (max (Kt * (D0 + 12)) 4 * Real.log ((m : ℝ) * (n : ℝ)) +
            10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
          (by rfl) μ Xi Mask
          hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
          hMask_meas hMask_val hMask_law hMask_indep hIndep
      obtain ⟨G2, _, hG2compl, hG2⟩ :=

        hedges_all m n hm hn hnm hM1 hlo hhi p hp_gt hp1 hsparse
          (max (Kt * (D0 + 12)) 4 * Real.log ((m : ℝ) * (n : ℝ)) +
            10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) (by rfl)
          μ Xi Mask
          hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
          hMask_meas hMask_val hMask_law hMask_indep hIndep
          b c hb hc hc_pos XT hXT hXT_mean hXT_var hXT_bound htail
          (by
            intro ω hω
            have hsv := htransfer ω hω
            have hbr := ((statopia_math_node_1519428770_08e15fe6 m n (by omega)
              (maskedScaled p (Xi ω) (Mask ω) -
                maskedScaled p (XT ω) (Mask ω))).2
                (Real.rpow (n : ℝ) (-(D0 + 5)))).mp hsv
            rwa [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2] at hbr)



      obtain ⟨G, hGcompl, hG⟩ :=
        hmain m n hm hn hnm hmstar hlo hhi p hp_gt hp1 hsparse (hdelta_gen m hmstar0) μ Xi Mask

          hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
          hMask_meas hMask_val hMask_law hMask_indep hIndep
          (by
            intro tau htau
            obtain ⟨G1, _, hG1compl, hG1pt⟩ := hgridM tau htau
            exact ⟨G1, hG1compl, hG1pt⟩)
          (by
            refine ⟨G2, hG2compl, ?_⟩
            intro ω hω
            simp only [mpLambdaPlus, mpLambdaMinus]
            exact ⟨(hG2 ω hω).1, (hG2 ω hω).2.1⟩)
          ⟨hquant, hmass⟩





      refine ⟨?_, ?_⟩
      · have hsub : {ω : Ω | (Ce + (Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1)) *
            deltaM m < maxDeviation (svals (maskedScaled p (Xi ω) (Mask ω)))
              (mpQuantile ((n : ℝ) / (m : ℝ)) n)} ⊆ Gᶜ := by
          intro ω hω hωG
          simp only [Set.mem_setOf_eq] at hω
          exact absurd hω (not_lt.mpr (hG ω hωG).2)
        refine le_trans (measure_mono hsub) (le_trans hGcompl ?_)
        apply ENNReal.ofReal_le_ofReal
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hmono : Real.rpow (n : ℝ) (-(D0 + 2)) ≤ Real.rpow (n : ℝ) (-D0) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        linarith
      · intro ω hω
        have hbdd : BddAbove (Set.range fun i : Fin n =>
            |svals (maskedScaled p (Xi ω) (Mask ω)) i -
              mpQuantile ((n : ℝ) / (m : ℝ)) n i|) :=
          Finite.bddAbove_range _
        have hle : |svals (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩ -
            mpQuantile ((n : ℝ) / (m : ℝ)) n ⟨0, by omega⟩| ≤
              (Ce + (Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1)) * deltaM m :=
          le_trans (le_csSup hbdd (Set.mem_range_self _)) hω
        have hγ : mpQuantile ((n : ℝ) / (m : ℝ)) n ⟨0, by omega⟩ ≤
            1 + Real.sqrt ((n : ℝ) / (m : ℝ)) := by
          have hq := (hquant ⟨0, by omega⟩).2.1
          simpa [mpLambdaPlus] using hq
        have h2 := (abs_le.mp hle).2
        linarith

  · have hρ1' : (1 : ℝ) < rhoMinus := not_le.mp hρ1
    refine ⟨2, le_refl 2, 1, 1, one_pos, one_pos, ?_⟩
    intro m n hm hn hmM hlo hhi
    exact absurd hlo (not_le.mpr (lt_of_le_of_lt hhi hρ1'))

  /- @proof-region region.root.ff839656dea7 end -/


set_option maxHeartbeats 4000000 in
theorem sparse_coarse_rigidity_all_alpha
    (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (h_rhoMinus : 0 < rhoMinus)
    (Kt : ℝ) (hKt : 0 < Kt) :
    ∀ (alpha0 : ℝ), 15 < alpha0 →
        ∃ M0 : ℕ, 2 ≤ M0 ∧
          ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
            ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmM : M0 ≤ m)
              (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
              (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
              (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
              (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
              {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
              (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
              (hXi_meas : ∀ i j, Measurable fun ω => Xi ω i j)
              (hXi_int : ∀ i j, Integrable (fun ω => Xi ω i j) μ)
              (hXi_sq_int : ∀ i j, Integrable (fun ω => (Xi ω i j) ^ 2) μ)
              (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
              (hXi_mean : ∀ i j, ∫ ω, Xi ω i j ∂μ = 0)
              (hXi_var : ∀ i j, ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
              (hXi_tail : ∀ i j (t : ℝ), 0 < t →
                μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
              (hMask_meas : ∀ i j, Measurable fun ω => Mask ω i j)
              (hMask_val : ∀ i j ω, Mask ω i j = 0 ∨ Mask ω i j = 1)
              (hMask_law : ∀ i j, μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
              (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
              (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
                (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
            (μ {ω | C * deltaM m <
                  maxDeviation (svals (maskedScaled p (Xi ω) (Mask ω)))
                    (mpQuantile ((n : ℝ) / (m : ℝ)) n)} ≤
                ENNReal.ofReal (c * Real.rpow (n : ℝ) (-D0))) ∧
              (∀ ω, maxDeviation (svals (maskedScaled p (Xi ω) (Mask ω)))
                    (mpQuantile ((n : ℝ) / (m : ℝ)) n) ≤ C * deltaM m →
                  svals (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩ ≤
                    1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + C * deltaM m) := by
  exact sparse_coarse_rigidity_all_alpha_of_polynomial_rate.{u} (1 / 9) (by norm_num)
    ResidualSparseRepair20261106.DenseGaussian.denseSymmetricPolynomialRate_one_ninth
    D0 hD0 rhoMinus h_rhoMinus Kt hKt

end Statlib.Imported

-- Paper root revision c019fa18-308f-420f-ab8a-d10bcfe11ca0


#print axioms Statlib.Imported.sparse_coarse_rigidity_all_alpha

