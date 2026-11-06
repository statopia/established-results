import Lean
import ProverJobs.ResidualE2ESupport20261106.M_9ebb17def6102ca6c226
import ProverJobs.ResidualE2ESupport20261106.M_b11b22849368ce1005c6
import ProverJobs.ResidualE2ESupport20261106.M_bfd32cde8e43b4eecc52
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
theorem empirical_cdf_of_polynomial_rate (beta : ℝ) (hbeta : 1 / 10 < beta)
    (h_dense : DenseSymmetricPolynomialRate beta) : ∀ (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus) (h_rhoMinus_le : rhoMinus ≤ 1)
    (alpha0 : ℝ) (hAlpha0 : 15 < alpha0)
    (Kt : ℝ) (hKt : 0 < Kt)
    (D0 : ℝ) (hD0 : 0 < D0)
    (c0 : ℝ) (hc0 : 0 < c0),
    ∃ m1 : ℕ,
      ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hm1 : m1 ≤ m)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        (t : ℝ) (ht : 0 ≤ t),
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ),
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0) →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1) →
          (∀ (i : Fin m) (j : Fin n) (s : ℝ), 0 < s →
            μ {ω | s < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-s / Kt))) →
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
          (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
          (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
          IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
            (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
          sSup (Set.range fun x : {y : ℝ // 0 ≤ y} =>
              |(∫ ω, (n : ℝ)⁻¹ *
                  ((Finset.univ.filter
                    (fun i : Fin n =>
                      svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ (x : ℝ))).card : ℝ) ∂μ) -
                (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..((x : ℝ)),
                    rootedMPDensity ((n : ℝ) / (m : ℝ)) u)|)
            ≤ c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) →
          ∃ G1 : Set Ω,
            μ (G1ᶜ) ≤ ENNReal.ofReal (4 * Real.rpow (n : ℝ) (-(D0 + 2))) ∧
              ∀ ω ∈ G1, ∀ i : Fin n,
                |(n : ℝ)⁻¹ *
                    ((Finset.univ.filter
                      (fun j : Fin n =>
                        svals (maskedScaled p (Xi ω) (Mask ω)) j ≤
                          mpQuantile ((n : ℝ) / (m : ℝ)) n i + t)).card : ℝ) -
                  (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..
                      (mpQuantile ((n : ℝ) / (m : ℝ)) n i + t),
                    rootedMPDensity ((n : ℝ) / (m : ℝ)) u)| ≤
                  2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) ∧
                |(n : ℝ)⁻¹ *
                    ((Finset.univ.filter
                      (fun j : Fin n =>
                        svals (maskedScaled p (Xi ω) (Mask ω)) j ≤
                          mpQuantile ((n : ℝ) / (m : ℝ)) n i - t)).card : ℝ) -
                  (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..
                      (mpQuantile ((n : ℝ) / (m : ℝ)) n i - t),
                    rootedMPDensity ((n : ℝ) / (m : ℝ)) u)| ≤
                  2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
  /- @proof-region region.target-node.session.6bc9f0552076b239 begin -/
  have statopia_math_node_2704888616_ccc54d35 := sparse_cdf_comparison_of_polynomial_rate.{u} beta hbeta h_dense

  intro rhoMinus h_rhoMinus_pos h_rhoMinus_le alpha0 hAlpha0 Kt hKt D0 hD0 c0 hc0
  classical
  have hexists : ∃ m1 : ℕ, ∀ m : ℕ, m1 ≤ m →
      (rhoMinus * c0 ^ 2 / 2) * (m : ℝ) * (deltaM m) ^ (3 : ℝ) ≥
        (D0 + 3) * Real.log (m : ℝ) + Real.log 4 := by
    have hApos : 0 < rhoMinus * c0 ^ 2 / 2 := by
      have h2 : (0:ℝ) < c0 ^ 2 := by positivity
      have h3 : (0:ℝ) < rhoMinus * c0 ^ 2 := mul_pos h_rhoMinus_pos h2
      linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (max (240 * (D0 + 3) / (rhoMinus * c0 ^ 2 / 2))
      (240 * Real.log 4 / (rhoMinus * c0 ^ 2 / 2) + 1)))
    refine ⟨max 2 (N + 1), ?_⟩
    intro m hm1le
    have hm2 : 2 ≤ m := le_trans (le_max_left 2 (N + 1)) hm1le
    have hNle : N ≤ m := by
      have h : N + 1 ≤ m := le_trans (le_max_right 2 (N + 1)) hm1le
      omega
    have hmR : (0:ℝ) < (m:ℝ) := by
      have h : 0 < m := by omega
      exact_mod_cast h
    have hm1R : (1:ℝ) < (m:ℝ) := by
      have h : 1 < m := by omega
      exact_mod_cast h
    have hLpos : 0 < Real.log (m:ℝ) := Real.log_pos hm1R
    have hLnn : (0:ℝ) ≤ Real.log (m:ℝ) := le_of_lt hLpos
    have h4nn : (0:ℝ) ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num))
    have hCle : max (240 * (D0 + 3) / (rhoMinus * c0 ^ 2 / 2))
        (240 * Real.log 4 / (rhoMinus * c0 ^ 2 / 2) + 1) ≤ Real.log (m:ℝ) := by
      have hlt : Real.exp (max (240 * (D0 + 3) / (rhoMinus * c0 ^ 2 / 2))
          (240 * Real.log 4 / (rhoMinus * c0 ^ 2 / 2) + 1)) < (m:ℝ) :=
        lt_of_lt_of_le hN (by exact_mod_cast hNle)
      have h := Real.log_le_log (Real.exp_pos _) (le_of_lt hlt)
      rwa [Real.log_exp] at h
    have hC1 : 240 * (D0 + 3) / (rhoMinus * c0 ^ 2 / 2) ≤ Real.log (m:ℝ) :=
      le_trans (le_max_left _ _) hCle
    have hC2 : 240 * Real.log 4 / (rhoMinus * c0 ^ 2 / 2) + 1 ≤ Real.log (m:ℝ) :=
      le_trans (le_max_right _ _) hCle
    have hp1 : 240 * (D0 + 3) ≤ (rhoMinus * c0 ^ 2 / 2) * Real.log (m:ℝ) := by
      have h := (div_le_iff₀ hApos).mp hC1
      linarith [h]
    have hp2 : 240 * Real.log 4 ≤ (rhoMinus * c0 ^ 2 / 2) * Real.log (m:ℝ) := by
      have h2 : 240 * Real.log 4 / (rhoMinus * c0 ^ 2 / 2) ≤ Real.log (m:ℝ) := by linarith
      have h := (div_le_iff₀ hApos).mp h2
      linarith [h]
    have hL1 : (1:ℝ) ≤ Real.log (m:ℝ) := by
      have h0 : (0:ℝ) ≤ 240 * Real.log 4 / (rhoMinus * c0 ^ 2 / 2) :=
        div_nonneg (by linarith) (le_of_lt hApos)
      linarith
    have hL5 : (Real.log (m:ℝ)) ^ 5 ≤ 120 * (m:ℝ) := by
      have h := Real.pow_div_factorial_le_exp (Real.log (m:ℝ)) hLnn 5
      rw [Real.exp_log hmR] at h
      have h5 : ((5:ℕ).factorial : ℝ) = 120 := by norm_num
      rw [h5] at h
      linarith
    have hδeq : (deltaM m) ^ (3:ℝ) = ((Real.log (m:ℝ)) ^ 3)⁻¹ := by
      show ((Real.log (m:ℝ))⁻¹) ^ (3:ℝ) = ((Real.log (m:ℝ)) ^ 3)⁻¹
      rw [Real.inv_rpow hLnn]
      exact congrArg (fun t => t⁻¹) (Real.rpow_natCast (Real.log (m:ℝ)) 3)
    have hquad : (D0 + 3) * Real.log (m:ℝ) + Real.log 4 ≤
        (rhoMinus * c0 ^ 2 / 2) * (Real.log (m:ℝ)) ^ 2 / 120 := by
      have hLL : (0:ℝ) ≤ 240 * Real.log 4 := by linarith
      have hqa : (D0 + 3) * Real.log (m:ℝ) ≤
          (rhoMinus * c0 ^ 2 / 2) * (Real.log (m:ℝ)) ^ 2 / 240 := by
        have h := mul_le_mul_of_nonneg_right hp1 (le_of_lt hLpos)
        linarith [h]
      have hqb : Real.log 4 ≤
          (rhoMinus * c0 ^ 2 / 2) * (Real.log (m:ℝ)) ^ 2 / 240 := by
        have h1 := mul_le_mul_of_nonneg_right hp2 (le_of_lt hLpos)
        have h2 := mul_le_mul_of_nonneg_left hL1 hLL
        linarith [h1, h2]
      linarith [hqa, hqb]
    have hfinal : ((D0 + 3) * Real.log (m:ℝ) + Real.log 4) * (Real.log (m:ℝ)) ^ 3
        ≤ (rhoMinus * c0 ^ 2 / 2) * (m:ℝ) := by
      have hL3 : (0:ℝ) < (Real.log (m:ℝ)) ^ 3 := pow_pos hLpos 3
      have h1 := mul_le_mul_of_nonneg_right hquad (le_of_lt hL3)
      have h120 : (0:ℝ) ≤ rhoMinus * c0 ^ 2 / 2 / 120 :=
        div_nonneg (le_of_lt hApos) (by norm_num)
      have h2 : ((rhoMinus * c0 ^ 2 / 2) * (Real.log (m:ℝ)) ^ 2 / 120) *
            (Real.log (m:ℝ)) ^ 3 ≤ (rhoMinus * c0 ^ 2 / 2) * (m:ℝ) := by
        have hstep : rhoMinus * c0 ^ 2 / 2 / 120 * (Real.log (m:ℝ)) ^ 5
            ≤ rhoMinus * c0 ^ 2 / 2 / 120 * (120 * (m:ℝ)) :=
          mul_le_mul_of_nonneg_left hL5 h120
        have heq : rhoMinus * c0 ^ 2 / 2 / 120 * (120 * (m:ℝ)) =
            (rhoMinus * c0 ^ 2 / 2) * (m:ℝ) := by ring
        have hLHS : ((rhoMinus * c0 ^ 2 / 2) * (Real.log (m:ℝ)) ^ 2 / 120) *
            (Real.log (m:ℝ)) ^ 3 = rhoMinus * c0 ^ 2 / 2 / 120 * (Real.log (m:ℝ)) ^ 5 := by
          ring
        rw [hLHS]
        linarith [hstep, heq]
      linarith [h1, h2]
    rw [hδeq]
    have hL3 : (0:ℝ) < (Real.log (m:ℝ)) ^ 3 := pow_pos hLpos 3
    have hstep := mul_le_mul_of_nonneg_right hfinal (le_of_lt (inv_pos.mpr hL3))
    rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hL3), mul_one] at hstep
  obtain ⟨m1, hm1⟩ := hexists
  refine ⟨m1, ?_⟩
  intro m n hm hn hnm hm1le hrho_lo hrho_hi p hp0 hp1 hsparse t ht
  intro Ω mΩ μ mμ Xi Mask
  intro hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
  intro hMask_meas hMask_val hMask_law hMask_indep hIndep hexp
  set rho : ℝ := (n : ℝ) / (m : ℝ) with hrho
  set d : ℝ := (deltaM m) ^ ((3 : ℝ) / 2) with hd
  set FA : Ω → ℝ → ℝ := fun ω x =>
    (n : ℝ)⁻¹ * ((Finset.univ.filter
      (fun j : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)).card : ℝ) with hFA
  set EF : ℝ → ℝ := fun x => ∫ ω, FA ω x ∂μ with hEF
  set Frho : ℝ → ℝ := fun x => ∫ uu in (mpLambdaMinus rho)..x, rootedMPDensity rho uu with hFrho
  set B : ℝ → Set Ω := fun x => {ω | c0 * d < |FA ω x - EF x|} with hB
  refine ⟨(⋃ i : Fin n,
      (B (mpQuantile rho n i + t) ∪ B (mpQuantile rho n i - t)))ᶜ, ?_, ?_⟩
  · rw [compl_compl]
    have hconc : ∀ (x u : ℝ), 0 ≤ u →
        μ {ω | u ≤ |FA ω x - EF x|} ≤
          ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * u ^ 2 / 2)) := by
      intro x u hu
      rcases lt_or_eq_of_le hu with hu' | hu0
      · exact statopia_math_node_3073978187_c577ca52 m n hm hn hnm p hp0 hp1
          (Ω := Ω) (μ := μ) Xi Mask hXi_meas hMask_meas hXi_indep hMask_indep hIndep x u hu'
      · rw [← hu0]
        have hμ1 : μ {ω : Ω | (0:ℝ) ≤ |FA ω x - EF x|} ≤ 1 := by
          have hsub := measure_mono (μ := μ) (Set.subset_univ {ω : Ω | (0:ℝ) ≤ |FA ω x - EF x|})
          rwa [measure_univ] at hsub
        have hz : -(n : ℝ) * (0 : ℝ) ^ 2 / 2 = 0 := by ring
        have h2le : (1:ENNReal) ≤
            ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (0 : ℝ) ^ 2 / 2)) := by
          rw [hz, Real.exp_zero, mul_one, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by norm_num)
        exact le_trans hμ1 h2le
    have hmc : ∀ x : ℝ, μ (B x) ≤
        ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)) := by
      intro x
      have hdnn : (0:ℝ) ≤ d := by
        show 0 ≤ (deltaM m) ^ ((3 : ℝ) / 2)
        exact Real.rpow_nonneg (inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast hm))) _
      have hu : (0:ℝ) ≤ c0 * d := mul_nonneg (le_of_lt hc0) hdnn
      refine le_trans (measure_mono ?_) (hconc x (c0 * d) hu)
      intro ω hω
      simp only [B, Set.mem_setOf_eq] at hω ⊢
      exact le_of_lt hω
    have hfin : μ (⋃ i : Fin n, (B (mpQuantile rho n i + t) ∪ B (mpQuantile rho n i - t)))
        ≤ ∑ i : Fin n,
            (μ (B (mpQuantile rho n i + t)) + μ (B (mpQuantile rho n i - t))) := by
      refine (measure_iUnion_le _).trans ?_
      rw [tsum_fintype]
      exact Finset.sum_le_sum fun i _ => measure_union_le _ _
    have hsum : ∑ i : Fin n,
          (μ (B (mpQuantile rho n i + t)) + μ (B (mpQuantile rho n i - t)))
        ≤ ∑ _i : Fin n,
            (ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)) +
              ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2))) :=
      Finset.sum_le_sum fun i _ => add_le_add (hmc _) (hmc _)
    have hmR : (0:ℝ) < (m:ℝ) := by
      have h : 0 < m := by omega
      exact_mod_cast h
    have hnR : (0:ℝ) < (n:ℝ) := by
      have h : 0 < n := by omega
      exact_mod_cast h
    have hδ3nn : (0:ℝ) ≤ (deltaM m) ^ (3:ℝ) :=
      Real.rpow_nonneg (inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast hm))) _
    have hnlog : Real.log (n:ℝ) ≤ Real.log (m:ℝ) :=
      Real.log_le_log hnR (by exact_mod_cast hnm)
    have hmrho : rhoMinus * (m:ℝ) ≤ (n:ℝ) := by
      have hρ : rhoMinus ≤ (n : ℝ) / (m : ℝ) := by simpa only [hrho] using hrho_lo
      exact (le_div_iff₀ hmR).mp hρ
    have hAn : (D0 + 3) * Real.log (n:ℝ) + Real.log 4 ≤
        (n:ℝ) * c0 ^ 2 * (deltaM m) ^ (3:ℝ) / 2 := by
      have h1 := hm1 m hm1le
      have hc : (0:ℝ) ≤ c0 ^ 2 / 2 * (deltaM m) ^ (3:ℝ) :=
        mul_nonneg (by positivity) hδ3nn
      have h3 := mul_le_mul_of_nonneg_right hmrho hc
      have h3' : rhoMinus * c0 ^ 2 / 2 * (m:ℝ) * (deltaM m) ^ (3:ℝ) ≤
          (n:ℝ) * c0 ^ 2 * (deltaM m) ^ (3:ℝ) / 2 := by
        have e1 : rhoMinus * c0 ^ 2 / 2 * (m:ℝ) * (deltaM m) ^ (3:ℝ)
            = rhoMinus * (m:ℝ) * (c0 ^ 2 / 2 * (deltaM m) ^ (3:ℝ)) := by ring
        have e2 : (n:ℝ) * c0 ^ 2 * (deltaM m) ^ (3:ℝ) / 2
            = (n:ℝ) * (c0 ^ 2 / 2 * (deltaM m) ^ (3:ℝ)) := by ring
        rw [e1, e2]
        exact h3
      have h5 : (D0 + 3) * Real.log (m:ℝ) + Real.log 4 ≤
          (n:ℝ) * c0 ^ 2 * (deltaM m) ^ (3:ℝ) / 2 := by
        linarith [h1, h3']
      have hDnn : (0:ℝ) ≤ D0 + 3 := by linarith
      have h4 := mul_le_mul_of_nonneg_left hnlog hDnn
      linarith [h4, h5]
    have hδ0 : (0:ℝ) ≤ deltaM m :=
      inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast hm))
    have hd2 : ((deltaM m) ^ ((3:ℝ)/2)) ^ 2 = (deltaM m) ^ (3:ℝ) := by
      rw [← Real.rpow_natCast (x := (deltaM m) ^ ((3:ℝ)/2)) 2, ← Real.rpow_mul hδ0]
      norm_num
    have hcd2 : (c0 * d) ^ 2 = c0 ^ 2 * (deltaM m) ^ (3:ℝ) := by
      show (c0 * (deltaM m) ^ ((3:ℝ)/2)) ^ 2 = c0 ^ 2 * (deltaM m) ^ (3:ℝ)
      rw [mul_pow, hd2]
    have hA' : (n:ℝ) * (c0 * d) ^ 2 / 2 ≥ (D0 + 3) * Real.log (n:ℝ) + Real.log 4 := by
      rw [hcd2, ← mul_assoc]
      exact hAn


    refine hfin.trans (hsum.trans ?_)
    have hexpB : Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2) ≤ (n : ℝ) ^ (-(D0 + 3)) := by
      have harg : -(n : ℝ) * (c0 * d) ^ 2 / 2 ≤
          -((D0 + 3) * Real.log (n : ℝ) + Real.log 4) := by
        linarith [hA']
      refine (Real.exp_le_exp.mpr harg).trans ?_
      rw [Real.rpow_def_of_pos hnR]
      refine Real.exp_le_exp.mpr ?_
      have h4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
      linarith
    have hsum_eq : ∑ _i : Fin n,
        (ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)) +
          ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)))
        = ENNReal.ofReal ((n : ℝ) * (4 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2))) := by
      have hnn : (0:ℝ) ≤ 2 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2) := by positivity
      have hterm : ∀ _i : Fin n,
          (ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)) +
            ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)))
          = ENNReal.ofReal (4 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)) := by
        intro _i
        rw [← ENNReal.ofReal_add hnn hnn]
        congr 1
        ring
      calc ∑ _i : Fin n,
            (ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)) +
              ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)))
          = ∑ _i : Fin n,
              ENNReal.ofReal (4 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)) :=
            Finset.sum_congr rfl fun i _ => hterm i
        _ = ENNReal.ofReal ((n : ℝ) * (4 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity)]
    rw [hsum_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hnn : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hmul : (n:ℝ) * (n : ℝ) ^ (-(D0 + 3)) = (n : ℝ) ^ (-(D0 + 2)) := by
      calc (n:ℝ) * (n : ℝ) ^ (-(D0 + 3))
          = (n:ℝ) ^ (1:ℝ) * (n : ℝ) ^ (-(D0 + 3)) := by rw [Real.rpow_one]
        _ = (n:ℝ) ^ ((1:ℝ) + -(D0 + 3)) := (Real.rpow_add hnR 1 (-(D0 + 3))).symm
        _ = (n:ℝ) ^ (-(D0 + 2)) := by
            congr 1
            ring
    have h1 : (n:ℝ) * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2) ≤ (n : ℝ).rpow (-(D0 + 2)) := by
      show (n:ℝ) * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2) ≤ (n : ℝ) ^ (-(D0 + 2))
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left hexpB hnn
    calc (n : ℝ) * (4 * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2))
        = 4 * ((n : ℝ) * Real.exp (-(n : ℝ) * (c0 * d) ^ 2 / 2)) := by ring
      _ ≤ 4 * (n : ℝ).rpow (-(D0 + 2)) := by linarith [h1]
  · intro ω hω i
    have hdnn : 0 ≤ d := by
      show 0 ≤ (deltaM m) ^ ((3 : ℝ) / 2)
      exact Real.rpow_nonneg (inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast hm))) _
    have hcd : 0 ≤ c0 * d := mul_nonneg (le_of_lt hc0) hdnn
    have h2 : ∀ x : ℝ, |EF x - Frho x| ≤ c0 * d := by
      intro x
      rcases lt_or_ge x 0 with hxneg | hxnonneg
      · have hFA0 : ∀ ω, FA ω x = 0 := by
          intro ω
          have hempty : (Finset.univ.filter
              (fun j : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro j _
            exact not_le.mpr (lt_of_lt_of_le hxneg (Real.sqrt_nonneg _))
          show (n : ℝ)⁻¹ * ((Finset.univ.filter
            (fun j : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)).card : ℝ) = 0
          rw [hempty]
          simp
        have hEF0 : EF x = 0 := by
          show ∫ ω, FA ω x ∂μ = 0
          rw [show (fun ω => FA ω x) = (fun _ => (0 : ℝ)) from funext hFA0]
          simp
        have hlam : (0 : ℝ) ≤ mpLambdaMinus rho := by
          show 0 ≤ 1 - Real.sqrt rho
          have hs : Real.sqrt rho ≤ 1 := by
            have h := Real.sqrt_le_sqrt hrho_hi
            rwa [Real.sqrt_one] at h
          linarith
        have hFrho0 : Frho x = 0 := by
          show ∫ uu in mpLambdaMinus rho..x, rootedMPDensity rho uu = 0
          have hxa : x < mpLambdaMinus rho := lt_of_lt_of_le hxneg hlam
          have hzero : ∀ uu, uu ≤ mpLambdaMinus rho → rootedMPDensity rho uu = 0 := by
            intro uu huu
            rcases lt_or_eq_of_le huu with h | h
            · simp only [rootedMPDensity]
              rw [if_neg (fun hc => absurd hc.1 (not_le.mpr h)), mul_zero]
            · subst h
              simp only [rootedMPDensity]
              rw [show (mpLambdaPlus rho ^ 2 - mpLambdaMinus rho ^ 2) *
                  (mpLambdaMinus rho ^ 2 - mpLambdaMinus rho ^ 2) = 0 by ring,
                Real.sqrt_zero]
              simp
          rw [intervalIntegral.integral_symm,
            intervalIntegral.integral_of_le (le_of_lt hxa)]
          rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun uu hu => hzero uu hu.2)]
          simp
        rw [hEF0, hFrho0, sub_self, abs_zero]
        exact hcd
      · have hnR' : (0:ℝ) < (n:ℝ) := by
          have h : 0 < n := by omega
          exact_mod_cast h
        have hEF : ∀ y : ℝ, |EF y| ≤ 1 := by
          intro y
          have hpt0 : ∀ ω : Ω, 0 ≤ FA ω y := by
            intro ω
            show (0:ℝ) ≤ (n : ℝ)⁻¹ * ((Finset.univ.filter
              (fun j : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ y)).card : ℝ)
            exact mul_nonneg (inv_nonneg.mpr (by positivity)) (by positivity)
          have hpt1 : ∀ ω : Ω, FA ω y ≤ 1 := by
            intro ω
            show (n : ℝ)⁻¹ * ((Finset.univ.filter
              (fun j : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ y)).card : ℝ) ≤ 1
            have hcard : (Finset.univ.filter
                (fun j : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ y)).card ≤ n := by
              have h := Finset.card_filter_le (Finset.univ : Finset (Fin n))
                (fun j : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ y)
              simpa using h
            have hcast : (((Finset.univ.filter
                (fun j : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ y)).card : ℕ) : ℝ)
                ≤ (n : ℝ) := by exact_mod_cast hcard
            have hinv : (0:ℝ) < (n:ℝ)⁻¹ := inv_pos.mpr hnR'
            calc (n : ℝ)⁻¹ * ((Finset.univ.filter
                  (fun j : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ y)).card : ℝ)
                ≤ (n : ℝ)⁻¹ * (n : ℝ) := mul_le_mul_of_nonneg_left hcast (le_of_lt hinv)
              _ = 1 := inv_mul_cancel₀ (ne_of_gt hnR')
          by_cases hint : Integrable (fun ω => FA ω y) μ
          · have hle1 : ∫ ω, FA ω y ∂μ ≤ 1 := by
              have hc : Integrable (fun _ : Ω => (1:ℝ)) μ := integrable_const 1
              have hle : (fun ω => FA ω y) ≤ᶠ[ae μ] (fun _ : Ω => (1:ℝ)) :=
                Filter.Eventually.of_forall hpt1
              have h := MeasureTheory.integral_mono_ae hint hc hle
              have hval : ∫ _ω : Ω, (1:ℝ) ∂μ = 1 := by
                rw [MeasureTheory.integral_const]
                show (μ Set.univ).toReal * 1 = 1
                rw [measure_univ]
                simp
              linarith [h, hval]
            have hge0 : 0 ≤ ∫ ω, FA ω y ∂μ := by
              have hc : Integrable (fun _ : Ω => (0:ℝ)) μ := integrable_const 0
              have hle : (fun _ : Ω => (0:ℝ)) ≤ᶠ[ae μ] (fun ω => FA ω y) :=
                Filter.Eventually.of_forall hpt0
              have h := MeasureTheory.integral_mono_ae hc hint hle
              simpa using h
            show |∫ ω, FA ω y ∂μ| ≤ 1
            rw [abs_le]
            exact ⟨by linarith, hle1⟩
          · show |∫ ω, FA ω y ∂μ| ≤ 1
            rw [MeasureTheory.integral_undef hint, abs_zero]
            exact zero_le_one
        have hρpos : (0:ℝ) < rho := lt_of_lt_of_le h_rhoMinus_pos hrho_lo
        have hlam : (0:ℝ) ≤ mpLambdaMinus rho := by
          show 0 ≤ 1 - Real.sqrt rho
          have hs : Real.sqrt rho ≤ 1 := by
            have h := Real.sqrt_le_sqrt hrho_hi
            rwa [Real.sqrt_one] at h
          linarith
        have hlamle : mpLambdaMinus rho ≤ mpLambdaPlus rho := by
          show 1 - Real.sqrt rho ≤ 1 + Real.sqrt rho
          have := Real.sqrt_nonneg rho
          linarith
        have hmass : ∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u = 1 :=
          statopia_math_node_503473485_2877602c rho hρpos hrho_hi
        have hνnonneg : ∀ u : ℝ, 0 ≤ rootedMPDensity rho u := by
          intro u
          by_cases hc : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho
          · have hu0 : (0:ℝ) ≤ u := le_trans hlam hc.1
            rcases eq_or_lt_of_le hu0 with h0 | hupos
            · subst h0
              simp only [rootedMPDensity, mul_zero, div_zero, zero_mul]
              exact le_refl 0
            · have hsqrt : (0:ℝ) ≤ Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) :=
                Real.sqrt_nonneg _
              have hnum : (0:ℝ) ≤ (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) :=
                mul_nonneg (by positivity) hsqrt
              have hden : (0:ℝ) ≤ rho * u := mul_nonneg (le_of_lt hρpos) hu0
              have h4 : (0:ℝ) ≤ (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u) :=
                div_nonneg hnum hden
              simpa only [rootedMPDensity, if_pos hc, mul_one] using h4
          · simp only [rootedMPDensity, if_neg hc, mul_zero]
            exact le_refl 0
        have hνzlow : ∀ u : ℝ, u ≤ mpLambdaMinus rho → rootedMPDensity rho u = 0 := by
          intro u huu
          rcases lt_or_eq_of_le huu with h | h
          · simp only [rootedMPDensity]
            rw [if_neg (fun hc => absurd hc.1 (not_le.mpr h)), mul_zero]
          · subst h
            simp only [rootedMPDensity]
            rw [show (mpLambdaPlus rho ^ 2 - mpLambdaMinus rho ^ 2) *
                (mpLambdaMinus rho ^ 2 - mpLambdaMinus rho ^ 2) = 0 by ring, Real.sqrt_zero]
            simp
        have hνzhigh : ∀ u : ℝ, mpLambdaPlus rho ≤ u → rootedMPDensity rho u = 0 := by
          intro u huu
          rcases lt_or_eq_of_le huu with h | h
          · simp only [rootedMPDensity]
            rw [if_neg (fun hc => absurd hc.2 (not_le.mpr h)), mul_zero]
          · subst h
            simp only [rootedMPDensity]
            rw [show (mpLambdaPlus rho ^ 2 - mpLambdaPlus rho ^ 2) *
                (mpLambdaPlus rho ^ 2 - mpLambdaMinus rho ^ 2) = 0 by ring, Real.sqrt_zero]
            simp

        have hbFrho : ∀ y : ℝ, |Frho y| ≤ 1 := by
          have hInt : Integrable (fun u => rootedMPDensity rho u)
              (volume.restrict (Set.Ioc (mpLambdaMinus rho) (mpLambdaPlus rho))) := by
            by_contra hcon
            have h0 : ∫ x, rootedMPDensity rho x
                ∂(volume.restrict (Set.Ioc (mpLambdaMinus rho) (mpLambdaPlus rho))) = 0 :=
              MeasureTheory.integral_undef hcon
            have h1 : ∫ x in Set.Ioc (mpLambdaMinus rho) (mpLambdaPlus rho),
                rootedMPDensity rho x = 1 := by
              rw [← intervalIntegral.integral_of_le hlamle]
              exact hmass
            rw [h1] at h0
            norm_num at h0
          have hIbig : IntervalIntegrable (fun u => rootedMPDensity rho u) volume
              (mpLambdaMinus rho) (mpLambdaPlus rho) :=
            (intervalIntegrable_iff_integrableOn_Ioc_of_le
              (f := fun u => rootedMPDensity rho u) (μ := volume) hlamle).mpr hInt
          intro y
          rcases lt_or_ge (mpLambdaMinus rho) y with hay | hya
          · rcases lt_or_ge (mpLambdaPlus rho) y with hby | hyb
            · have hF1 : Frho y = 1 := by
                show ∫ uu in (mpLambdaMinus rho)..y, rootedMPDensity rho uu = 1
                rw [intervalIntegral.integral_of_le (le_of_lt hay)]
                have hset : Set.Ioc (mpLambdaMinus rho) y ∩ {x : ℝ | x ≤ mpLambdaPlus rho}
                    = Set.Ioc (mpLambdaMinus rho) (mpLambdaPlus rho) := by
                  ext x
                  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_setOf_eq]
                  constructor
                  · rintro ⟨⟨h1, _⟩, h2⟩
                    exact ⟨h1, h2⟩
                  · intro h
                    exact ⟨⟨h.1, le_trans h.2 (le_of_lt hby)⟩, h.2⟩
                calc ∫ x in Set.Ioc (mpLambdaMinus rho) y, rootedMPDensity rho x
                    = ∫ x in Set.Ioc (mpLambdaMinus rho) y,
                        {x : ℝ | x ≤ mpLambdaPlus rho}.indicator
                          (fun u => rootedMPDensity rho u) x := by
                      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
                      intro x hx
                      rcases lt_or_ge (mpLambdaPlus rho) x with h | h
                      · have hz := hνzhigh x (le_of_lt h)
                        simp [h, hz]
                      · simp [h]
                  _ = ∫ x in Set.Ioc (mpLambdaMinus rho) y ∩ {x : ℝ | x ≤ mpLambdaPlus rho},
                        rootedMPDensity rho x :=
                      MeasureTheory.setIntegral_indicator
                        (s := Set.Ioc (mpLambdaMinus rho) y) measurableSet_Iic
                  _ = ∫ x in Set.Ioc (mpLambdaMinus rho) (mpLambdaPlus rho),
                        rootedMPDensity rho x := by
                      rw [hset]
                  _ = 1 := by
                      rw [← intervalIntegral.integral_of_le hlamle]
                      exact hmass
              rw [hF1, abs_one]
            · have hlow : (0:ℝ) ≤ Frho y := by
                show 0 ≤ ∫ uu in (mpLambdaMinus rho)..y, rootedMPDensity rho uu
                exact intervalIntegral.integral_nonneg_of_forall (le_of_lt hay) hνnonneg
              have hup : Frho y ≤ 1 := by
                have h := intervalIntegral.integral_mono_interval
                  (f := fun u => rootedMPDensity rho u) (μ := volume)
                  (a := mpLambdaMinus rho) (b := y)
                  (c := mpLambdaMinus rho) (d := mpLambdaPlus rho)
                  (le_refl _) (le_of_lt hay) hyb
                  (Filter.Eventually.of_forall hνnonneg) hIbig
                rw [hmass] at h
                exact h
              rw [abs_le]
              exact ⟨by linarith, hup⟩
          · have hF0 : Frho y = 0 := by
              show ∫ uu in (mpLambdaMinus rho)..y, rootedMPDensity rho uu = 0
              rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hya]
              rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
                (fun uu hu => hνzlow uu hu.2)]
              simp
            rw [hF0, abs_zero]
            exact zero_le_one
        have hbdd : BddAbove (Set.range (fun y : {y : ℝ // 0 ≤ y} =>
              |EF (y : ℝ) - Frho (y : ℝ)|)) := by
          refine ⟨2, ?_⟩
          rintro _ ⟨⟨y, hy⟩, rfl⟩
          have h1 := hEF y
          have h2 := hbFrho y
          have hab : |EF y - Frho y| ≤ |EF y| + |Frho y| := by
            have h := abs_add_le (EF y) (-(Frho y))
            rwa [← sub_eq_add_neg, abs_neg] at h
          linarith
        have hmem' : |EF x - Frho x| ∈ Set.range (fun y : {y : ℝ // 0 ≤ y} =>
            |EF (y : ℝ) - Frho (y : ℝ)|) := ⟨⟨x, hxnonneg⟩, rfl⟩
        exact (le_csSup hbdd hmem').trans hexp
    have hplus : |FA ω (mpQuantile rho n i + t) - EF (mpQuantile rho n i + t)| ≤ c0 * d := by
      have hnot : ¬ (c0 * d < |FA ω (mpQuantile rho n i + t) - EF (mpQuantile rho n i + t)|) :=
        fun hlt => hω (Set.mem_iUnion.mpr ⟨i, Or.inl hlt⟩)
      exact not_lt.mp hnot
    have hminus : |FA ω (mpQuantile rho n i - t) - EF (mpQuantile rho n i - t)| ≤ c0 * d := by
      have hnot : ¬ (c0 * d < |FA ω (mpQuantile rho n i - t) - EF (mpQuantile rho n i - t)|) :=
        fun hlt => hω (Set.mem_iUnion.mpr ⟨i, Or.inr hlt⟩)
      exact not_lt.mp hnot
    constructor
    · change |FA ω (mpQuantile rho n i + t) - Frho (mpQuantile rho n i + t)| ≤ 2 * c0 * d
      have h2p := h2 (mpQuantile rho n i + t)
      calc |FA ω (mpQuantile rho n i + t) - Frho (mpQuantile rho n i + t)|
          = |(FA ω (mpQuantile rho n i + t) - EF (mpQuantile rho n i + t)) +
              (EF (mpQuantile rho n i + t) - Frho (mpQuantile rho n i + t))| := by
            congr 1
            ring
        _ ≤ |FA ω (mpQuantile rho n i + t) - EF (mpQuantile rho n i + t)| +
              |EF (mpQuantile rho n i + t) - Frho (mpQuantile rho n i + t)| := abs_add_le _ _
        _ ≤ 2 * c0 * d := by linarith
    · change |FA ω (mpQuantile rho n i - t) - Frho (mpQuantile rho n i - t)| ≤ 2 * c0 * d
      have h2m := h2 (mpQuantile rho n i - t)
      calc |FA ω (mpQuantile rho n i - t) - Frho (mpQuantile rho n i - t)|
          = |(FA ω (mpQuantile rho n i - t) - EF (mpQuantile rho n i - t)) +
              (EF (mpQuantile rho n i - t) - Frho (mpQuantile rho n i - t))| := by
            congr 1
            ring
        _ ≤ |FA ω (mpQuantile rho n i - t) - EF (mpQuantile rho n i - t)| +
              |EF (mpQuantile rho n i - t) - Frho (mpQuantile rho n i - t)| := abs_add_le _ _
        _ ≤ 2 * c0 * d := by linarith

  /- @proof-region region.target-node.session.6bc9f0552076b239 end -/

end Statlib.Imported

#print axioms Statlib.Imported.empirical_cdf_of_polynomial_rate

