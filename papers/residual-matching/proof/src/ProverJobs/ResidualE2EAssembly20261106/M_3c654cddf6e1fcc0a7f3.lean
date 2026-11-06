import Statlib.HighDim.MatrixAnalysis.FrobeniusNormSvdRelation
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SoftThresholdDenoisingHelpers
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_7f3eea621b0d2e005d06
import ProverJobs.ResidualE2EAssembly20261106.M_093a03bfef2c6896ccf9
import ProverJobs.ResidualE2EAssembly20261106.M_eeb0c48628f53be1e6d9
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_25e23798cf853b4443c8
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

theorem Theorem_4_1_first_main_theorem_thm_upper_bound_for_rankr_rank_r_matrix_recovery_bound_including_the_uniform_low_loss_can
    (rho_min : ℝ) (h_rho_min : 0 < rho_min)
    (alpha0 : ℝ) (h_alpha0 : 15 < alpha0)
    (K_H : ℝ) (h_K_H : 0 < K_H)
    (C_L : ℝ) (h_C_L : 0 < C_L)
    (w : (n : ℕ) → Fin n → ℝ)
    (h_w_nonneg : ∀ (n : ℕ) (i : Fin n), 0 ≤ w n i)
    (h_w_sum : ∀ (n : ℕ) (hn : 0 < n), ∑ i : Fin n, w n i = 1)
    (h_w_large : ∀ c : ℝ, 0 < c → ∀ᶠ m : ℕ in Filter.atTop, ∀ (n : ℕ) (hn : 0 < n),
      (n : ℝ) / (m : ℝ) ≤ 1 → rho_min ≤ (n : ℝ) / (m : ℝ) →
      c * ((Real.log (m : ℝ))⁻¹) ^ 2 ≤ w n ⟨0, hn⟩) :
    ∃ C_samp C_err c_err : ℝ, 0 < C_samp ∧ 0 < C_err ∧ 0 < c_err ∧
      ∀ᶠ m : ℕ in Filter.atTop,
      
        ∀ (n : ℕ) (hn : 0 < n) (hnm : n ≤ m) (T : ℕ) (hT : 0 < T)
          (r : ℕ) (hr : 0 < r) (hrn : 12 * r ≤ n)
          (h_ratio_lo : rho_min ≤ (n : ℝ) / (m : ℝ))
          (h_ratio_hi : (n : ℝ) / (m : ℝ) ≤ 1)
          (mu0 : ℝ) (h_mu0 : 0 < mu0)
          (mu1 : ℝ) (h_mu1 : mu0 ≤ mu1)
          (M0 : Matrix (Fin m) (Fin n) ℝ)
          (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ) (d0 : Fin r → ℝ)
          (hM0 : M0 = U0 * Matrix.diagonal d0 * Matrix.transpose V0)
          (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
          (hd0 : ∀ i, 0 < d0 i)
          (hd0_anti : Antitone d0)
          (h_inc_U : ∀ i : Fin m, rowL2Sq U0 i ≤ mu0 * (r : ℝ) / (m : ℝ))
          (h_inc_V : ∀ j : Fin n, rowL2Sq V0 j ≤ mu0 * (r : ℝ) / (n : ℝ))
          (s_star : ℝ) (h_s_star_pos : 0 < s_star)
          (h_s_star : s_star = psi hnm M0 ⟨r - 1, by omega⟩)
          (s_1 : ℝ) (h_s_1 : s_1 = psi hnm M0 ⟨0, by omega⟩)
          (kappa : ℝ) (h_kappa : kappa = s_1 / s_star)
          (p : ℝ) (h_p_pos : 0 < p) (h_p_le : p ≤ 1)
          (sigma : ℝ) (h_sigma : 0 < sigma)
          (h_sparse : (m : ℝ) * p ≥ Real.log (m : ℝ) ^ alpha0)
          (h_samp : (n : ℝ) * p ≥ C_samp * kappa ^ 2 *
            (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2))
          (Om : Type*) [MeasurableSpace Om]
          (P : MeasureTheory.Measure Om) [IsProbabilityMeasure P]
          (mask : Om → Matrix (Fin m) (Fin n) ℝ)
          (Hn : Om → Matrix (Fin m) (Fin n) ℝ)
          (Gref : Om → Fin T → Matrix (Fin m) (Fin n) ℝ)
          (h_mask_meas : ∀ (i : Fin m) (j : Fin n), Measurable (fun x => mask x i j))
          (h_mask_law : ∀ (i : Fin m) (j : Fin n),
            MeasureTheory.Measure.map (fun x => mask x i j) P = bernoulliLaw p)
          (h_mask_indep : ProbabilityTheory.iIndepFun
            (fun (ij : Fin m × Fin n) (x : Om) => mask x ij.1 ij.2) P)
          (h_H_meas : ∀ (i : Fin m) (j : Fin n), Measurable (fun x => Hn x i j))
          (h_H_indep : ProbabilityTheory.iIndepFun
            (fun (ij : Fin m × Fin n) (x : Om) => Hn x ij.1 ij.2) P)
          (h_H_int : ∀ (i : Fin m) (j : Fin n), MeasureTheory.Integrable (fun x => Hn x i j) P)
          (h_H_mean : ∀ (i : Fin m) (j : Fin n), ∫ x, Hn x i j ∂P = 0)
          (h_H_var : ∀ (i : Fin m) (j : Fin n), ∫ x, (Hn x i j) ^ 2 ∂P = sigma ^ 2)
          (h_H_sq_int : ∀ (i : Fin m) (j : Fin n),
            MeasureTheory.Integrable (fun x => (Hn x i j) ^ 2) P)
          (h_H_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
            P {x | t * sigma < |Hn x i j|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / K_H))))
          (h_mask_H_indep : ProbabilityTheory.IndepFun mask Hn P)
          (h_G_meas : ∀ (t : Fin T) (i : Fin m) (j : Fin n), Measurable (fun x => Gref x t i j))
          (h_G_law : ∀ (t : Fin T) (i : Fin m) (j : Fin n),
            MeasureTheory.Measure.map (fun x => Gref x t i j) P = gaussianReal 0 1)
          (h_G_indep : ProbabilityTheory.iIndepFun
            (fun (tij : Fin T × Fin m × Fin n) (x : Om) => Gref x tij.1 tij.2.1 tij.2.2) P)
          (h_G_joint : ProbabilityTheory.IndepFun
            (fun (x : Om) (tij : Fin T × Fin m × Fin n) => Gref x tij.1 tij.2.1 tij.2.2)
            (fun x => (mask x, Hn x)) P),
        ∃ E : Set Om, MeasurableSet E ∧
          ENNReal.ofReal (1 - c_err * ((n : ℝ) ^ 3)⁻¹) ≤ P E ∧
          ∀ x ∈ E,
            (∀ Mtil : Matrix (Fin m) (Fin n) ℝ,
              IsArgminOn
                (fun M => normLoss hnm p (w n) (lambdaHat hnm (mask x) (Gref x))
                  (obsMatrix (mask x) M0 (Hn x)) (mask x) M)
                (candidateSet r mu1) Mtil →
              frobNorm (Mtil - M0) ≤ C_err * sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p)) ∧
            (∀ M : Matrix (Fin m) (Fin n) ℝ, M ∈ candidateSet r mu1 →
              normLoss hnm p (w n) (lambdaHat hnm (mask x) (Gref x))
                (obsMatrix (mask x) M0 (Hn x)) (mask x) M ≤ ((C_L * w n ⟨0, hn⟩ : ℝ) : WithTop ℝ) →
              frobNorm (M - M0) ≤ C_err * sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p))
:= by
  /- @proof-region region.root.56e0a97c9534 begin -/
  classical
  obtain ⟨c1A, c1bA, CA, C0A, hcA, hc1A, hCA, hC0A, m0A, hcalA⟩ :=
    ((@PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.paper_951aae9227d84800bf9113306ae458aa.{u_1, u_1, u_1}
      K_H rho_min h_K_H h_rho_min).1 alpha0 h_alpha0)
  
  
  
  
  
  
  
  
  obtain ⟨N0B, Cs, CLB, Cth, cB, hCs, hCLB, hCth, hcB, hgood⟩ :=
    @PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.paper_45fc93d926fd4099b9973daee59eb529.{u_1}
      rho_min h_rho_min alpha0 h_alpha0
  have hK_top : (1 : ℝ) ≤ 2 + CA := by linarith
  have hCLam_top : (1 : ℝ) ≤ max 1 CLB := le_max_left 1 CLB
  have hCthet_top : (1 : ℝ) ≤ max 1 Cth := le_max_left 1 Cth
  obtain ⟨N0E, CsampE, CerrE, hCsampE_pos, hCerrE_pos, hNode⟩ :=
    statopia_math_node_160158563_7abd8755 rho_min h_rho_min alpha0 h_alpha0 C_L h_C_L
      (2 + CA) c1A CA (max 1 CLB) (max 1 Cth) hK_top hcA hCA.le hCLam_top hCthet_top
  have hCsampE_le : CsampE ≤ max (max 1 Cs) (max 1 CsampE) :=
    le_trans (le_max_right 1 CsampE) (le_max_right (max 1 Cs) (max 1 CsampE))
  have hCs_le : max 1 Cs ≤ max (max 1 Cs) (max 1 CsampE) := le_max_left _ _
  have hCsamp_top_pos : (0 : ℝ) < max (max 1 Cs) (max 1 CsampE) :=
    lt_of_lt_of_le one_pos (le_trans (le_max_left 1 Cs) (le_max_left _ _))
  have hCerr_top_pos : (0 : ℝ) < max 1 CerrE := lt_of_lt_of_le one_pos (le_max_left 1 CerrE)
  
  have hcQ_pos : (0 : ℝ) < C0A / C_L := div_pos hC0A h_C_L
  have hCAev : ∀ᶠ m : ℕ in Filter.atTop, CA * (Real.log (m : ℝ))⁻¹ < 1 := by
    refine Filter.eventually_atTop.2 ⟨Nat.ceil (Real.exp (CA + 1)), fun m hm => ?_⟩
    have h1 : Real.exp (CA + 1) ≤ ((Nat.ceil (Real.exp (CA + 1)) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp (CA + 1)) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h3 : Real.exp (CA + 1) ≤ (m : ℝ) := le_trans h1 h2
    have h4 : CA + 1 ≤ Real.log (m : ℝ) := by
      have h5 := Real.log_le_log (Real.exp_pos (CA + 1)) h3
      rwa [Real.log_exp] at h5
    have hpos : (0 : ℝ) < Real.log (m : ℝ) := by linarith
    rw [← div_eq_mul_inv, div_lt_one hpos]
    linarith
  refine ⟨max (max 1 Cs) (max 1 CsampE), max 1 CerrE, max 1 (c1bA + cB),
    hCsamp_top_pos, hCerr_top_pos,
    lt_of_lt_of_le one_pos (le_max_left (1 : ℝ) (c1bA + cB)), ?_⟩
  
  
  
  
  filter_upwards [h_w_large 1 one_pos, h_w_large (C0A / C_L) hcQ_pos,
    Filter.eventually_ge_atTop 3, Filter.eventually_ge_atTop m0A, hCAev,
    Filter.eventually_ge_atTop N0B, Filter.eventually_ge_atTop N0E]
    with m hw1 hwCL hm3 hm0A hCAlt hmN0B hmN0E
  
  
  
  
  
  intro n hn hnm T hT r hr hrn h_ratio_lo h_ratio_hi
  intro mu0 h_mu0 mu1 h_mu1
  intro M0 U0 V0 d0 hM0 hU0 hV0 hd0 hd0_anti h_inc_U h_inc_V
  
  intro s_star h_s_star_pos h_s_star s_1 h_s_1 kappa h_kappa
  intro p h_p_pos h_p_le sigma h_sigma h_sparse h_samp
  intro Om inst P instP mask Hn Gref
  intro h_mask_meas h_mask_law h_mask_indep h_H_meas h_H_indep h_H_int h_H_mean h_H_var
    h_H_sq_int h_H_tail h_mask_H_indep h_G_meas h_G_law h_G_indep h_G_joint
  
  
  
  have hKH45 : ∃ KH : ℝ, 0 < KH ∧ ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 ≤ t →
      P {x : Om | t ≤ |Hn x i j|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / KH))) := by
    refine ⟨2 * sigma * K_H, mul_pos (mul_pos two_pos h_sigma) h_K_H, ?_⟩
    intro i j t ht
    rcases eq_or_lt_of_le ht with h0 | hpos
    · have ht0 : t = 0 := h0.symm
      subst ht0
      have huniv : {x : Om | (0 : ℝ) ≤ |Hn x i j|} = Set.univ := by
        ext x
        simp
      rw [huniv, MeasureTheory.measure_univ]
      have htwo : (2 : ℝ) * Real.exp (-((0 : ℝ) / (2 * sigma * K_H))) = 2 := by simp
      rw [htwo]
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by norm_num)
    · have ht2 : (0 : ℝ) < t / (2 * sigma) := div_pos hpos (by linarith)
      have htail := h_H_tail i j (t / (2 * sigma)) ht2
      have heq : (t / (2 * sigma)) * sigma = t / 2 := by
        field_simp
      have hsub : {x : Om | t ≤ |Hn x i j|} ⊆ {x : Om | (t / (2 * sigma)) * sigma < |Hn x i j|} := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [heq]
        exact lt_of_lt_of_le (half_lt_self hpos) hx
  
  
      have hexp : -((t / (2 * sigma)) / K_H) = -(t / (2 * sigma * K_H)) := by
        rw [div_div]
      rw [hexp] at htail
      exact le_trans (measure_mono hsub) htail
  
  
  
  have hw1_pos : (0 : ℝ) < w n ⟨0, hn⟩ := by
    have hstep := hw1 n hn h_ratio_hi h_ratio_lo
    have hlogpos : (0 : ℝ) < Real.log (m : ℝ) := by
      have hm1 : (1 : ℝ) < (m : ℝ) := by
        have hm1n : 1 < m := by omega
        exact_mod_cast hm1n
      exact Real.log_pos hm1
    have hpos : (0 : ℝ) < ((Real.log (m : ℝ))⁻¹) ^ 2 := pow_pos (inv_pos.mpr hlogpos) 2
    linarith
  have hm_pos_real : (0 : ℝ) < (m : ℝ) := by
    have hm0 : 0 < m := lt_of_lt_of_le hn hnm
    exact_mod_cast hm0
  have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr_pos_real : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hm_div_nonneg : (0 : ℝ) ≤ (r : ℝ) / (m : ℝ) := div_nonneg hr_pos_real.le hm_pos_real.le
  have hn_div_nonneg : (0 : ℝ) ≤ (r : ℝ) / (n : ℝ) := div_nonneg hr_pos_real.le hn_pos_real.le
  have hM0_rank_le : Matrix.rank M0 ≤ r := by
    have h1 : Matrix.rank M0 ≤ Matrix.rank (U0 * Matrix.diagonal d0) := by
      rw [hM0]
      exact Matrix.rank_mul_le_left (U0 * Matrix.diagonal d0) (Matrix.transpose V0)
    have h2 : Matrix.rank (U0 * Matrix.diagonal d0) ≤ Matrix.rank (Matrix.diagonal d0) :=
      Matrix.rank_mul_le_right U0 (Matrix.diagonal d0)
    have h3 : Matrix.rank (Matrix.diagonal d0) ≤ r := by
      rw [Matrix.rank_diagonal]
      simpa using Finset.card_le_univ d0.support
    exact le_trans h1 (le_trans h2 h3)
  have hM0_rank_eq : Matrix.rank M0 = r := by
    have hD : Matrix.rank (Matrix.diagonal d0) = r := by
      rw [Matrix.rank_diagonal]
      exact (Fintype.card_congr { toFun := fun i => ⟨i, ne_of_gt (hd0 i)⟩, invFun := fun x => x.1, left_inv := fun i => rfl, right_inv := fun x => Subtype.ext rfl }).symm.trans (Fintype.card_fin r)
    have h1 : Matrix.rank (U0 * Matrix.diagonal d0 * Matrix.transpose V0) ≤ Matrix.rank (Matrix.diagonal d0) := le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
    have h2 : Matrix.rank (Matrix.diagonal d0) ≤ Matrix.rank (U0 * Matrix.diagonal d0 * Matrix.transpose V0) := by
      have he : Matrix.transpose U0 * (U0 * Matrix.diagonal d0 * Matrix.transpose V0) * V0 = Matrix.diagonal d0 := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU0, Matrix.one_mul, Matrix.mul_assoc (Matrix.diagonal d0) (Matrix.transpose V0) V0, hV0, Matrix.mul_one]
      have hstep : Matrix.rank (Matrix.transpose U0 * (U0 * Matrix.diagonal d0 * Matrix.transpose V0) * V0) ≤ Matrix.rank (U0 * Matrix.diagonal d0 * Matrix.transpose V0) := le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
      rwa [he] at hstep
    rw [hM0, le_antisymm h1 h2, hD]
  
  
  
  
  
  
  
  
  have hM0_mem : M0 ∈ candidateSet r mu1 := by
    refine ⟨hM0_rank_le, r, U0, V0, d0, le_rfl, hd0, hU0, hV0, hM0, ?_, ?_⟩
    · intro i
      have hmono : mu0 * (r : ℝ) / (m : ℝ) ≤ mu1 * (r : ℝ) / (m : ℝ) := by
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right h_mu1 hm_div_nonneg
      exact le_trans (h_inc_U i) hmono
    · intro j
      have hmono : mu0 * (r : ℝ) / (n : ℝ) ≤ mu1 * (r : ℝ) / (n : ℝ) := by
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right h_mu1 hn_div_nonneg
      exact le_trans (h_inc_V j) hmono
  
  
  
  
  
  
  
  have hm_pos_nat : 0 < m := lt_of_lt_of_le hn hnm
  haveI : Nonempty (Fin m) := ⟨⟨0, hm_pos_nat⟩⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hrowU :
      PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.rowSupNorm U0
        ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) := by
    exact ciSup_le (fun i : Fin m => Real.sqrt_le_sqrt (h_inc_U i))
  have hrowV :
      PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.rowSupNorm V0
        ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) := by
    exact ciSup_le (fun j : Fin n => Real.sqrt_le_sqrt (h_inc_V j))
  have hisv :
      PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.IsIncoherentSVD
        M0 U0 d0 V0 mu0 :=
    ⟨hM0, hd0, hU0, hV0, hrowU, hrowV⟩
  have hrowU45 : PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm U0 ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) := hrowU
  have hrowV45 : PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm V0 ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) := hrowV
  have hpsile : psi hnm M0 ⟨r - 1, by omega⟩ ≤ psi hnm M0 ⟨0, hn⟩ := by
    simp only [psi]
    exact Statlib.HighDim.MatrixAnalysis.singularValues_antitone M0 (by simp [Fin.le_def])
  have hkappa_one : (1 : ℝ) ≤ kappa := by
    rw [h_kappa, h_s_1, le_div_iff₀ h_s_star_pos, one_mul, h_s_star]
    exact hpsile
  have hmu0_one : (1 : ℝ) ≤ mu0 := by
    have htr : ∑ i : Fin m, rowL2Sq U0 i = (r : ℝ) := by
      simp only [rowL2Sq]
      have h := (Statlib.HighDim.MatrixAnalysis.frobenius_norm_svd_relation U0).2.2
      rw [← h, hU0, Matrix.trace_one, Fintype.card_fin]
  
    have hle : ∑ i : Fin m, rowL2Sq U0 i ≤ ∑ _i : Fin m, mu0 * (r : ℝ) / (m : ℝ) :=
      Finset.sum_le_sum (fun i _ => h_inc_U i)
    have h2 : (r : ℝ) ≤ mu0 * (r : ℝ) := by
      rw [htr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
      rwa [show (m : ℝ) * (mu0 * (r : ℝ) / (m : ℝ)) = mu0 * (r : ℝ) by field_simp] at hle
    exact le_of_mul_le_mul_right (by linarith) hr_pos_real
  have hmax1Cs_nonneg : (0 : ℝ) ≤ max 1 Cs := le_trans zero_le_one (le_max_left 1 Cs)
  have hκ2 : (1 : ℝ) ≤ kappa ^ 2 := by
    have h := mul_le_mul hkappa_one hkappa_one zero_le_one (le_trans zero_le_one hkappa_one)
    simpa [pow_two] using h
  have hnp : Cs * mu0 * (r : ℝ) * Real.log (m : ℝ) ≤ (n : ℝ) * p := by
    have hL : Cs * mu0 ≤ max 1 Cs * kappa ^ 2 * max mu0 mu1 := by
      have h1 : Cs * mu0 ≤ max 1 Cs * mu0 :=
        mul_le_mul_of_nonneg_right (le_max_right 1 Cs) h_mu0.le
      have h2 : max 1 Cs * mu0 ≤ max 1 Cs * max mu0 mu1 :=
        mul_le_mul_of_nonneg_left (le_max_left mu0 mu1) hmax1Cs_nonneg
      have h3 : max 1 Cs * max mu0 mu1 ≤ max 1 Cs * kappa ^ 2 * max mu0 mu1 :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hmax1Cs_nonneg hκ2)
          (le_trans h_mu0.le (le_max_left mu0 mu1))
      linarith
    have hrl : (0 : ℝ) ≤ (r : ℝ) * Real.log (m : ℝ) := by
      have hm1 : (1 : ℝ) < (m : ℝ) := by
        have hm1n : 1 < m := by omega
        exact_mod_cast hm1n
      exact mul_nonneg hr_pos_real.le (Real.log_pos hm1).le
  
    calc Cs * mu0 * (r : ℝ) * Real.log (m : ℝ)
        = (Cs * mu0) * ((r : ℝ) * Real.log (m : ℝ)) := by ring
      _ ≤ (max 1 Cs * kappa ^ 2 * max mu0 mu1) * ((r : ℝ) * Real.log (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hL hrl
      _ = max 1 Cs * kappa ^ 2 * (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)) := by ring
      _ ≤ max 1 Cs * kappa ^ 2 * (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)
            + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hmax1Cs_nonneg (le_trans zero_le_one hκ2))
          have hnn : (0 : ℝ) ≤ (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 :=
            mul_nonneg (sq_nonneg _) (sq_nonneg _)
          linarith
      _ ≤ max (max 1 Cs) (max 1 CsampE) * kappa ^ 2 *
            (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)
              + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCs_le (by linarith [hκ2])) ?_
          have hnn : (0 : ℝ) ≤ (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 :=
            mul_nonneg (sq_nonneg _) (sq_nonneg _)
          have h1 : (0 : ℝ) ≤ max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) := by
            rw [mul_assoc]
            exact mul_nonneg (le_trans h_mu0.le (le_max_left mu0 mu1)) hrl
          linarith
      _ ≤ (n : ℝ) * p := h_samp
  
  
  
  
  
  
  have hn_two : 2 ≤ n := by omega
  have hT_one : 1 ≤ T := by omega
  have hw_nn' : ∀ i : Fin n, 0 ≤ w n i := fun i => h_w_nonneg n i
  have hw_sum' : (∑ i : Fin n, w n i) = 1 := h_w_sum n hn
  have hmp' : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p := h_sparse
  
  have hmass : ∀ (i : Fin m) (j : Fin n), P {x | mask x i j = 1} = ENNReal.ofReal p := by
    intro i j
    have hmap : Measure.map (fun x => mask x i j) P ({1} : Set ℝ)
        = P ((fun x => mask x i j) ⁻¹' ({1} : Set ℝ)) :=
      Measure.map_apply (h_mask_meas i j) (measurableSet_singleton (1 : ℝ))
    have hbern : bernoulliLaw p ({1} : Set ℝ) = ENNReal.ofReal p := by
      simp [bernoulliLaw]
    rw [h_mask_law i j, hbern] at hmap
    exact hmap.symm
  set mask' : Om → Matrix (Fin m) (Fin n) ℝ :=
    fun x i j => if mask x i j = 1 then (1 : ℝ) else 0 with hmask'
  have hmask'_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun x => mask' x i j := by
    intro i j
    simp only [hmask']
    exact measurable_const.indicator ((h_mask_meas i j) (measurableSet_singleton (1 : ℝ)))
  have hmask'_bin : ∀ (x : Om) (i : Fin m) (j : Fin n),
      mask' x i j = 0 ∨ mask' x i j = 1 := by
    intro x i j
    simp only [hmask']
    by_cases h : mask x i j = 1
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  have hmask'_set : ∀ (i : Fin m) (j : Fin n),
      {x : Om | mask' x i j = 1} = {x : Om | mask x i j = 1} := by
    intro i j
    ext x
    simp only [Set.mem_setOf_eq, hmask']
    by_cases h : mask x i j = 1
    · exact ⟨fun _ => h, fun _ => if_pos h⟩
    · refine ⟨?_, ?_⟩
      · intro hh
        rw [if_neg h] at hh
        exact absurd hh zero_ne_one
      · intro hh
        exact absurd hh h
  have hmask'_mass : ∀ (i : Fin m) (j : Fin n),
      P {x : Om | mask' x i j = 1} = ENNReal.ofReal p := by
    intro i j
    rw [hmask'_set i j]
    exact hmass i j
  have hmask'_int : ∀ (i : Fin m) (j : Fin n), MeasureTheory.Integrable (fun x => mask' x i j) P := by
    intro i j
    have hset : MeasurableSet {x : Om | mask x i j = 1} :=
      (h_mask_meas i j) (measurableSet_singleton (1 : ℝ))
    have h : MeasureTheory.Integrable
        (Set.indicator {x : Om | mask x i j = 1} fun _ => (1 : ℝ)) P :=
      (integrable_const (μ := P) (1 : ℝ)).indicator hset
    simpa only [hmask', Set.indicator, Set.mem_setOf_eq] using h
  
  have hmask'_bin_ae : ∀ (i : Fin m) (j : Fin n), ∀ᵐ x ∂P, mask' x i j = 0 ∨ mask' x i j = 1 :=
    fun i j => Filter.Eventually.of_forall (fun x => hmask'_bin x i j)
  have hmask'_mean : ∀ (i : Fin m) (j : Fin n), ∫ x, mask' x i j ∂P = p := by
    intro i j
    have hset : MeasurableSet {x : Om | mask x i j = 1} := (h_mask_meas i j) (measurableSet_singleton (1 : ℝ))
    have hfun : (fun x => mask' x i j) = {x : Om | mask x i j = 1}.indicator (fun _ => (1 : ℝ)) := by
      funext x; simp [hmask', Set.indicator]
    rw [hfun, MeasureTheory.integral_indicator_const (1 : ℝ) hset, smul_eq_mul, mul_one]
    show (P {x : Om | mask x i j = 1}).toReal = p
    rw [hmass i j, ENNReal.toReal_ofReal h_p_pos.le]
  
  
  
  
  have hbern_bin : bernoulliLaw p ({0, 1} : Set ℝ) = 1 := by
    have hp1 : (0 : ℝ) ≤ 1 - p := by linarith
    have hd1 : MeasureTheory.Measure.dirac (1 : ℝ) ({0, 1} : Set ℝ) = 1 :=
      MeasureTheory.Measure.dirac_apply_of_mem (by simp : (1 : ℝ) ∈ ({0, 1} : Set ℝ))
    have hd0 : MeasureTheory.Measure.dirac (0 : ℝ) ({0, 1} : Set ℝ) = 1 :=
      MeasureTheory.Measure.dirac_apply_of_mem (by simp : (0 : ℝ) ∈ ({0, 1} : Set ℝ))
    rw [bernoulliLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hd1, hd0,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add h_p_pos.le hp1,
      show p + (1 - p) = 1 by ring, ENNReal.ofReal_one]
  have hmeasPair : MeasurableSet ({0, 1} : Set ℝ) :=
    (measurableSet_singleton (1 : ℝ)).insert (0 : ℝ)
  have hmask_ae_entry : ∀ (i : Fin m) (j : Fin n),
      ∀ᵐ x ∂P, mask x i j = 0 ∨ mask x i j = 1 := by
    intro i j
    have hpre : P ((fun x => mask x i j) ⁻¹' ({0, 1} : Set ℝ)) = 1 := by
      rw [← MeasureTheory.Measure.map_apply (h_mask_meas i j) hmeasPair]
      rw [h_mask_law i j, hbern_bin]
    have hzero : P ((fun x => mask x i j) ⁻¹' ({0, 1} : Set ℝ))ᶜ = 0 := by
      rw [MeasureTheory.measure_compl (h_mask_meas i j hmeasPair)
        (by rw [hpre]; exact ENNReal.one_ne_top), hpre, MeasureTheory.measure_univ]
      simp
    refine (MeasureTheory.mem_ae_iff).mpr ?_
    refine measure_mono_null ?_ hzero
    intro x hx
    simpa using hx
  
  
  have hmask_ae_bin : ∀ᵐ x ∂P, ∀ (i : Fin m) (j : Fin n),
      mask x i j = 0 ∨ mask x i j = 1 := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact hmask_ae_entry i j
  set S : Set Om := {x | ∀ (i : Fin m) (j : Fin n), mask x i j = 0 ∨ mask x i j = 1} with hS
  have hS_meas : MeasurableSet S := by
    rw [hS]
    have hset : {x : Om | ∀ (i : Fin m) (j : Fin n), mask x i j = 0 ∨ mask x i j = 1}
        = ⋂ (i : Fin m), ⋂ (j : Fin n), {x : Om | mask x i j = 0 ∨ mask x i j = 1} := by
      ext x
      simp
    rw [hset]
    refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    exact ((h_mask_meas i j) (measurableSet_singleton 0)).union
      ((h_mask_meas i j) (measurableSet_singleton 1))
  have hS_prob : P S = 1 := by
    have hae : ∀ᵐ x ∂P, x ∈ S := by
      simpa [hS] using hmask_ae_bin
    have hzero : P Sᶜ = 0 := (MeasureTheory.mem_ae_iff).mp hae
    have h := MeasureTheory.measure_add_measure_compl (μ := P) hS_meas
    rw [hzero, add_zero, MeasureTheory.measure_univ] at h
    exact h
  have hmask'_eq_of : ∀ x ∈ S, mask' x = mask x := by
    intro x hx
    ext i j
    have h := hx i j
    simp only [hmask']
    rcases h with h | h
    · rw [if_neg (by rw [h]; exact zero_ne_one), h]
    · rw [if_pos h, h]
  have hmask'_indep : ProbabilityTheory.iIndepFun
      (fun (ij : Fin m × Fin n) (x : Om) => mask' x ij.1 ij.2) P := by
    have haeS : ∀ᵐ x ∂P, x ∈ S := by
      simpa [hS] using hmask_ae_bin
    refine (ProbabilityTheory.iIndepFun_congr
      (f := fun (ij : Fin m × Fin n) (x : Om) => mask x ij.1 ij.2)
      (g := fun (ij : Fin m × Fin n) (x : Om) => mask' x ij.1 ij.2) ?_).mp h_mask_indep
    intro ij
    filter_upwards [haeS] with x hx
    show mask x ij.1 ij.2 = mask' x ij.1 ij.2
    rw [hmask'_eq_of x hx]
  have hmaskH_indep' : ProbabilityTheory.IndepFun mask' Hn P := by
    have haeS : ∀ᵐ x ∂P, x ∈ S := by simpa [hS] using hmask_ae_bin
    have h1 : ∀ᵐ x ∂P, mask x = mask' x := by
      filter_upwards [haeS] with x hx
      exact (hmask'_eq_of x hx).symm
    exact ProbabilityTheory.IndepFun.congr h_mask_H_indep h1
      (Filter.Eventually.of_forall (fun _ => rfl))
  have hGood_meas : MeasurableSet {x : Om |
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
        p (CLB * Real.sqrt ((m : ℝ) / p))
        (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))) (mask x) U0 V0} :=
    statopia_math_node_1023666064_4c15a721 p (CLB * Real.sqrt ((m : ℝ) / p))
      (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))) mask U0 V0 h_mask_meas
  have hmask_int : ∀ (i : Fin m) (j : Fin n), MeasureTheory.Integrable (fun x => mask x i j) P := by
    intro i j
    have haeS : ∀ᵐ x ∂P, x ∈ S := by simpa [hS] using hmask_ae_bin
    refine (hmask'_int i j).congr ?_
    filter_upwards [haeS] with x hx
    simp only [hmask'_eq_of x hx]
  have hmask_mean : ∀ (i : Fin m) (j : Fin n), ∫ x, mask x i j ∂P = p := by
    intro i j
    have haeS : ∀ᵐ x ∂P, x ∈ S := by simpa [hS] using hmask_ae_bin
    rw [← hmask'_mean i j]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [haeS] with x hx
    simp only [hmask'_eq_of x hx]
  have hMH_indep : ProbabilityTheory.IndepFun
      (fun omega (ij : Fin m × Fin n) => mask omega ij.1 ij.2)
      (fun omega (ij : Fin m × Fin n) => Hn omega ij.1 ij.2) P := by
    have hφ : Measurable fun A : Matrix (Fin m) (Fin n) ℝ =>
        (fun ij : Fin m × Fin n => A ij.1 ij.2) := by
      rw [measurable_pi_iff]
      intro ij
      exact (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)
    exact ProbabilityTheory.IndepFun.comp h_mask_H_indep hφ hφ
  have hG_prob : 1 - ENNReal.ofReal (cB / (n : ℝ) ^ 4) ≤
      P {x : Om | PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
        p (CLB * Real.sqrt ((m : ℝ) / p))
        (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
        (mask x) U0 V0} := by
    have hraw :=
      hgood m n r p mu0 sigma hm_pos_nat hn hmN0B hnm h_p_pos.le h_p_le h_ratio_lo h_ratio_hi
        h_sigma hrn hmp' hnp M0 U0 V0 d0 hM0_rank_eq hU0 hV0 hd0 hM0 hrowU45 hrowV45
        P (fun i j => fun x => Hn x i j) (fun i j => fun x => mask x i j)
        h_H_meas h_H_int h_H_indep h_H_mean h_H_var hKH45 h_mask_meas h_mask_indep
        hmask_ae_entry hmass hmask_int hmask_mean hMH_indep
    refine le_trans hraw ?_
    refine measure_mono ?_
    intro x hx
    exact ⟨hx.1, hx.2.2.1, hx.2.2.2, hx.2.1⟩
  have hG_meas : MeasurableSet {x : Om |
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
        p (CLB * Real.sqrt ((m : ℝ) / p))
        (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))) (mask x) U0 V0} :=
    hGood_meas
  
  
  
  
  
  
  
  
  
  
  
  
  have hmin_pos : 0 < min m n := lt_min hm_pos_nat hn
  have hpsi_zero : ∀ A : Matrix (Fin m) (Fin n) ℝ, psi hnm A ⟨0, hn⟩ = spectralNorm A := by
    intro A
    rw [spectralNorm, dif_pos hmin_pos]
    simp only [psi]
    exact congrArg (Statlib.HighDim.MatrixAnalysis.singularValues A) (Fin.ext (by simp))
  have hpsi_sv : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n),
      psi hnm A i =
        PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.sv hnm A i := by
    intro A i
    simp only [psi,
      PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.sv]
    exact congrArg (Statlib.HighDim.MatrixAnalysis.singularValues A) (Fin.ext (by simp))
  have hspec_le_opNorm : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      spectralNorm A ≤ Statlib.HighDim.MatrixAnalysis.opNorm A := by
    intro A
    have h := Statlib.HighDim.MatrixAnalysis.singularValues_tail_le_of_rank_add_opNorm_le
      (r := 0) (k := 0) (lam := Statlib.HighDim.MatrixAnalysis.opNorm A)
      (0 : Matrix (Fin m) (Fin n) ℝ) A (by simp) le_rfl (le_refl 0) hmin_pos
    rw [spectralNorm, dif_pos hmin_pos]
    simpa using h
  
  have hop_le_spec : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      Statlib.HighDim.MatrixAnalysis.opNorm A ≤ spectralNorm A := by
    intro A
    have hsv := (Statlib.HighDim.MatrixAnalysis.singular_value_properties A
      (Or.inr ⟨⟨0, hn⟩⟩)).1 hmin_pos
    rw [spectralNorm, dif_pos hmin_pos]
    exact le_of_eq hsv.symm
  have hspec_eq_op : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      spectralNorm A = Statlib.HighDim.MatrixAnalysis.opNorm A := by
    intro A
    exact le_antisymm (hspec_le_opNorm A) (hop_le_spec A)
  
  
  
  
  have hpsi_one : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      psi hnm A ⟨0, hn⟩ = Statlib.HighDim.MatrixAnalysis.opNorm A := by
    intro A
    rw [hpsi_zero, hspec_eq_op]
  have hmsqrt_pos : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos_real
  have hsigma_sqrt_pos : (0 : ℝ) < sigma * Real.sqrt (m : ℝ) := mul_pos h_sigma hmsqrt_pos
  
  have hlog_one : (1 : ℝ) ≤ Real.log (m : ℝ) := by
    have h3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      have hexp : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      have h := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at h
    exact le_trans hlog3 (Real.log_le_log (show (0 : ℝ) < 3 by norm_num) h3)
  have hlog_pos : (0 : ℝ) < Real.log (m : ℝ) := lt_of_lt_of_le one_pos hlog_one
  
  have hlog_inv_le_one : (Real.log (m : ℝ))⁻¹ ≤ 1 := by
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hlog_one
    simpa using h
  
  
  
  
  
  have hrefMaskOp : ∀ (OmF : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ),
      refMatrix OmF A =
        PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.maskOp OmF
          ((Real.sqrt (m : ℝ))⁻¹ • A) := by
    intro OmF A
    ext i j
    simp only [refMatrix, projMask,
      PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.maskOp,
      Matrix.smul_apply, smul_eq_mul]
    ring
  have hlamHat_ext : ∀ (x : Om) (i : Fin n),
      lambdaHat hnm (mask x) (Gref x) i =
        PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lambdaHat
          hnm (mask x) (Gref x) i := by
    intro x i
    simp only [lambdaHat,
      PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lambdaHat,
      hrefMaskOp, hpsi_sv, div_eq_inv_mul]
  have hIdx : bulkIdx n =
      PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.indexSet n := rfl
  have hmaskOp_eq : ∀ (OmF : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ),
      projMask OmF A =
        PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.maskOp OmF A :=
    fun _ _ => rfl
  have hobs_eq : ∀ (OmF M0F AF : Matrix (Fin m) (Fin n) ℝ),
      obsMatrix OmF M0F AF =
        PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.Yobs
          OmF M0F AF :=
    fun _ _ _ => rfl
  have hTmask_eq : ∀ (OmF : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ),
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p OmF A
        = p⁻¹ • projMask OmF A - A := by
    intro OmF A
    ext i j
    simp only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask,
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Wmask,
      projMask, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  
  
  
  
  
  
  have hsqrt_mul : Real.sqrt (C_L * p) = Real.sqrt C_L * Real.sqrt p :=
    Real.sqrt_mul h_C_L.le p
  have hsigmaHat_eq : ∀ (x : Om) (A : Matrix (Fin m) (Fin n) ℝ),
      sigmaHat hnm (lambdaHat hnm (mask x) (Gref x)) (obsMatrix (mask x) M0 (Hn x)) (mask x) A =
        PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.sigmaHat
          hnm
          (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.indexSet n)
          (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lambdaHat
            hnm (mask x) (Gref x))
          (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.Yobs
            (mask x) M0 (Hn x))
          (mask x) A := by
    intro x A
    simp only [sigmaHat,
      PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.sigmaHat,
      hIdx, hlamHat_ext x, hobs_eq, hmaskOp_eq, hpsi_sv]
  have hcriterion_eq : ∀ (x : Om) (N : Matrix (Fin m) (Fin n) ℝ),
      weightedLoss hnm (w n) (lambdaHat hnm (mask x) (Gref x)) N =
        PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.criterion
          hnm (w n)
          (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lambdaHat
            hnm (mask x) (Gref x)) N := by
    intro x N
    simp only [weightedLoss,
      PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.criterion,
      hlamHat_ext x, hpsi_sv]
  have harg_eq : ∀ (x : Om) (M : Matrix (Fin m) (Fin n) ℝ),
      (fun i j => (obsMatrix (mask x) M0 (Hn x) - projMask (mask x) M) i j /
          (Real.sqrt (m : ℝ) *
            sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
              (obsMatrix (mask x) M0 (Hn x)) (mask x) M))
        = (Real.sqrt (m : ℝ) *
            PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.sigmaHat
              hnm
              (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.indexSet n)
              (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lambdaHat
                hnm (mask x) (Gref x))
              (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.Yobs
                (mask x) M0 (Hn x))
              (mask x) M)⁻¹ •
          (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.Yobs
              (mask x) M0 (Hn x) -
            PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.maskOp
              (mask x) M) := by
    intro x M
    simp only [hobs_eq, hmaskOp_eq, ← hsigmaHat_eq x M]
    ext i j
    simp only [Matrix.smul_apply, div_eq_mul_inv]
    exact mul_comm _ _
  
  
  have hloss_bridge : ∀ (x : Om) (M : Matrix (Fin m) (Fin n) ℝ),
      sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
        (obsMatrix (mask x) M0 (Hn x)) (mask x) M ≠ 0 →
      ENNReal.ofReal (p⁻¹ * weightedLoss hnm (w n) (lambdaHat hnm (mask x) (Gref x))
          (fun i j => (obsMatrix (mask x) M0 (Hn x) - projMask (mask x) M) i j /
            (Real.sqrt (m : ℝ) * sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
              (obsMatrix (mask x) M0 (Hn x)) (mask x) M)))
        = PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.loss
            hnm
            (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.indexSet n)
            p (w n)
            (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lambdaHat
              hnm (mask x) (Gref x))
            (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.Yobs
              (mask x) M0 (Hn x))
            (mask x) M := by
    intro x M hne
    rw [PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.loss,
      if_neg ?_]
    · congr 1
      rw [harg_eq x M, hcriterion_eq x _]
    · rw [← hsigmaHat_eq x M]
      exact hne
  
  have hsigmaHat_M0_ne : ∀ (x : Om) (C : ℝ),
      |sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
          (obsMatrix (mask x) M0 (Hn x)) (mask x) M0 / sigma - 1| ≤ C →
      C < 1 →
      sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
          (obsMatrix (mask x) M0 (Hn x)) (mask x) M0 ≠ 0 := by
    intro x C hC hlt hzero
    rw [hzero, zero_div, zero_sub, abs_neg, abs_one] at hC
    linarith
  have htruth : ∀ (x : Om),
      (∃ C0 : ℝ, 0 ≤ C0 ∧
        PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.loss
            hnm
            (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.indexSet n)
            p (w n)
            (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lambdaHat
              hnm (mask x) (Gref x))
            (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.Yobs
              (mask x) M0 (Hn x))
            (mask x) M0 ≤ ENNReal.ofReal (C0 * ((Real.log (m : ℝ))⁻¹) ^ 2) ∧
        C0 * ((Real.log (m : ℝ))⁻¹) ^ 2 ≤ C_L * w n ⟨0, hn⟩) →
      sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
          (obsMatrix (mask x) M0 (Hn x)) (mask x) M0 ≠ 0 →
      normLoss hnm p (w n) (lambdaHat hnm (mask x) (Gref x))
          (obsMatrix (mask x) M0 (Hn x)) (mask x) M0
        ≤ ((C_L * w n ⟨0, hn⟩ : ℝ) : WithTop ℝ) := by
    intro x hdisp hne
    obtain ⟨C0, hC0, hcal, hcmp⟩ := hdisp
    have hb := hloss_bridge x M0 hne
    rw [← hb] at hcal
    have hle : p⁻¹ * weightedLoss hnm (w n) (lambdaHat hnm (mask x) (Gref x))
        (fun i j => (obsMatrix (mask x) M0 (Hn x) - projMask (mask x) M0) i j /
          (Real.sqrt (m : ℝ) * sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
            (obsMatrix (mask x) M0 (Hn x)) (mask x) M0)) ≤
        C0 * ((Real.log (m : ℝ))⁻¹) ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 (sq_nonneg _))).mp hcal
    rw [normLoss, if_neg hne]
    exact WithTop.coe_le_coe.mpr (le_trans hle hcmp)
  
  
  
  
  
  
  
  have hlaw_indep :
      ProbabilityTheory.iIndepFun
        (fun (x : PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lawIndex
              m n T) (s : Om) =>
          PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lawVar
            (mask' s) (Hn s) (Gref s) x) P := by
    have hbase :
        ProbabilityTheory.iIndepFun
          (fun (x : PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lawIndex
                m n T) (s : Om) =>
            PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lawVar
              (mask s) (Hn s) (Gref s) x) P :=
      statopia_math_node_945620439_f6e84320 P mask Hn Gref h_mask_meas h_mask_indep
        h_H_meas h_H_indep h_G_meas h_G_indep h_mask_H_indep h_G_joint
    have haeS : ∀ᵐ s ∂P, s ∈ S := by
      simpa [hS] using hmask_ae_bin
    refine (ProbabilityTheory.iIndepFun_congr ?_).mp hbase
    intro x
    rcases x with q | q
    · filter_upwards [haeS] with s hs
      show mask s q.1 q.2 = mask' s q.1 q.2
      rw [hmask'_eq_of s hs]
    · rcases q with q | q
      · filter_upwards [haeS] with s hs
        rfl
      · filter_upwards [haeS] with s hs
        rfl
  have hlaw' :
      @PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.IsSamplingLaw
        Om inst m n T P mask' Hn Gref p sigma K_H :=
    ⟨hmask'_meas, hmask'_bin, hmask'_mass, h_H_meas, h_H_int, h_H_mean, h_H_sq_int, h_H_var,
      h_H_tail, h_G_meas, h_G_law, hlaw_indep⟩
  
  
  
  
  obtain ⟨Ecal, hEcal_meas, hEcal_prob, hEcal_disp⟩ :=
    hcalA m n p T r sigma P mask' Hn Gref M0 (w n) U0 d0 V0 mu0
      h_sigma hm0A hn_two hnm h_p_pos h_p_le h_ratio_lo h_ratio_hi hT_one hmp' hw_nn' hw_sum'
      hisv hlaw'
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  have hMaster : ∀ (x : Om), x ∈ Ecal → x ∈ S →
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
        p (CLB * Real.sqrt ((m : ℝ) / p))
        (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))) (mask x) U0 V0 →
      ∀ (M : Matrix (Fin m) (Fin n) ℝ), M ∈ candidateSet r mu1 →
      normLoss hnm p (w n) (lambdaHat hnm (mask x) (Gref x))
        (obsMatrix (mask x) M0 (Hn x)) (mask x) M ≤ ((C_L * w n ⟨0, hn⟩ : ℝ) : WithTop ℝ) →
      frobNorm (M - M0) ≤ max 1 CerrE * sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p) := by
    intro x hxE hxS hxG
  
    have hbin : ∀ (i : Fin m) (j : Fin n), mask x i j = 0 ∨ mask x i j = 1 := by
      simpa [hS] using hxS
    have hdisp := hEcal_disp x hxE
    rw [hmask'_eq_of x hxS] at hdisp
    intro M hM hloss
  
    have hwork : ∀ (K c : ℝ), 1 ≤ K → 0 < c →
        (∀ (i : Fin m) (j : Fin n), mask x i j = 0 ∨ mask x i j = 1) →
        Matrix.rank (M - M0) ≤ 2 * r →
        Statlib.HighDim.MatrixAnalysis.opNorm (projMask (mask x) (Hn x))
          ≤ K * sigma * Real.sqrt ((m : ℝ) * p) →
        c * (n : ℝ) * Real.sqrt p ≤ ∑ i ∈ bulkIdx n, lambdaHat hnm (mask x) (Gref x) i →
        0 ≤ sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
              (obsMatrix (mask x) M0 (Hn x)) (mask x) M ∧
          sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
                (obsMatrix (mask x) M0 (Hn x)) (mask x) M * Real.sqrt ((m : ℝ) / p)
            ≤ c⁻¹ * (K * sigma * Real.sqrt ((m : ℝ) / p) +
                spectralNorm ((p : ℝ)⁻¹ • projMask (mask x) (M - M0) - (M - M0))) := by
      intro K c hK hc hbin hrank hnoise hbulk
      have hnoise' : spectralNorm (projMask (mask x) (Hn x))
          ≤ K * sigma * Real.sqrt ((m : ℝ) * p) := by
        rw [hspec_eq_op]
        exact hnoise
      exact statopia_math_node_1461725421_1cd7d47b m n r hn hnm hr hrn p sigma K c
        h_p_pos h_p_le h_sigma hK hc (mask x) (Hn x) M0 M hbin
        (lambdaHat hnm (mask x) (Gref x)) hrank hnoise' hbulk
  
    have hbound4 : max (Statlib.HighDim.MatrixAnalysis.opNorm (projMask (mask x) (Hn x))
          / (sigma * Real.sqrt (m : ℝ)))
        (lambdaHat hnm (mask x) (Gref x) ⟨0, hn⟩) ≤ (2 + CA) * Real.sqrt p := by
      have h4 := hdisp.2.2.2.1
      rw [← hmaskOp_eq (mask x) (Hn x), ← hlamHat_ext x ⟨0, hn⟩] at h4
      have hrho : Real.sqrt (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.rho m n) ≤ 1 := by
        have he : PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.rho m n
            = (n : ℝ) / (m : ℝ) := rfl
        rw [he, ← Real.sqrt_one]
        exact Real.sqrt_le_sqrt h_ratio_hi
      have hd : PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.deltaM m ≤ 1 := by
        have he : PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.deltaM m
            = (Real.log (m : ℝ))⁻¹ := rfl
        rw [he]
        exact hlog_inv_le_one
      have hstep : Real.sqrt p *
          (1 + Real.sqrt (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.rho m n)
            + CA * PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.deltaM m)
          ≤ (2 + CA) * Real.sqrt p := by
        have h1 : 1 + Real.sqrt (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.rho m n)
            + CA * PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.deltaM m
            ≤ 2 + CA := by
          have hd' : CA * PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.deltaM m ≤ CA := by
            simpa using mul_le_mul_of_nonneg_left hd hCA.le
          linarith
        calc Real.sqrt p *
              (1 + Real.sqrt (PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.rho m n)
                + CA * PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.deltaM m)
            ≤ Real.sqrt p * (2 + CA) := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg p)
          _ = (2 + CA) * Real.sqrt p := by ring
      exact le_trans h4 hstep
    have hlam1 : lambdaHat hnm (mask x) (Gref x) ⟨0, hn⟩ ≤ (2 + CA) * Real.sqrt p :=
      le_trans (le_max_right _ _) hbound4
    have hnoise : spectralNorm (projMask (mask x) (Hn x))
        ≤ (2 + CA) * sigma * Real.sqrt ((m : ℝ) * p) := by
      have h1 : Statlib.HighDim.MatrixAnalysis.opNorm (projMask (mask x) (Hn x))
          / (sigma * Real.sqrt (m : ℝ)) ≤ (2 + CA) * Real.sqrt p :=
        le_trans (le_max_left _ _) hbound4
      have hmul := (div_le_iff₀ hsigma_sqrt_pos).mp h1
      rw [hspec_eq_op]
      calc Statlib.HighDim.MatrixAnalysis.opNorm (projMask (mask x) (Hn x))
          ≤ (2 + CA) * Real.sqrt p * (sigma * Real.sqrt (m : ℝ)) := hmul
        _ = (2 + CA) * sigma * Real.sqrt ((m : ℝ) * p) := by
            rw [Real.sqrt_mul hm_pos_real.le]
            ring
    have hbulk : c1A * (n : ℝ) * Real.sqrt p
        ≤ ∑ i ∈ bulkIdx n, lambdaHat hnm (mask x) (Gref x) i := by
      have hE := hdisp.2.2.2.2.1
      have hsum : (∑ i ∈ bulkIdx n, lambdaHat hnm (mask x) (Gref x) i)
          = ∑ i ∈ bulkIdx n,
              PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.lambdaHat
                hnm (mask x) (Gref x) i :=
        Finset.sum_congr rfl (fun i _ => hlamHat_ext x i)
      rw [hsum, hIdx]
      exact hE
  
    have hZnn : (0 : ℝ) ≤ max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)
        + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 := by
      have hmnm : (0 : ℝ) ≤ max mu0 mu1 := le_trans h_mu0.le (le_max_left mu0 mu1)
      have h1 : (0 : ℝ) ≤ max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) := by
        rw [mul_assoc]
        exact mul_nonneg hmnm (mul_nonneg hr_pos_real.le hlog_pos.le)
      exact add_nonneg h1 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hsampE : CsampE * kappa ^ 2 *
        (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2)
        ≤ (n : ℝ) * p := by
      refine le_trans ?_ h_samp
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCsampE_le (by linarith [hκ2])) hZnn
    have hlast : r - 1 < n := by omega
    have h_s_star' : s_star = psi hnm M0 ⟨r - 1, hlast⟩ := by
      rw [h_s_star]
    have h_s_1' : s_1 = psi hnm M0 ⟨0, hn⟩ := by
      rw [h_s_1]
  
    have hLam_nn : (0 : ℝ) ≤ CLB * Real.sqrt ((m : ℝ) / p) :=
      mul_nonneg hCLB.le (Real.sqrt_nonneg _)
    have hth_nn : (0 : ℝ) ≤ Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) :=
      mul_nonneg hCth.le (Real.sqrt_nonneg _)
    have hLam_le : CLB * Real.sqrt ((m : ℝ) / p) ≤ max 1 CLB * Real.sqrt ((m : ℝ) / p) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 CLB) (Real.sqrt_nonneg _)
    have hth_le : Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
        ≤ max 1 Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 Cth) (Real.sqrt_nonneg _)
    have hscale : |sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
        (obsMatrix (mask x) M0 (Hn x)) (mask x) M / sigma - 1| ≤
        CA * (Real.log (m : ℝ))⁻¹ + CA * frobNorm (projMask (mask x) (M - M0)) /
          (sigma * Real.sqrt ((m : ℝ) * (n : ℝ) * p)) := by
      have h := hdisp.2.2.2.2.2.2.2 M
      rw [← hsigmaHat_eq x M, ← hmaskOp_eq (mask x) (M - M0)] at h
      exact h
    have hkey := hNode (m := m) (n := n) hm_pos_nat hmN0E hn hnm hlog_one r hr hrn p sigma
      (CLB * Real.sqrt ((m : ℝ) / p))
      (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))) mu0 mu1
      h_p_pos h_p_le h_sigma hLam_nn hth_nn h_mu0 h_mu1 h_ratio_lo h_ratio_hi hmp'
      hLam_le hth_le M0 U0 V0 d0 hM0 hU0 hV0 hd0 hd0_anti h_inc_U h_inc_V
      hlast s_star h_s_star_pos h_s_star' s_1 h_s_1' kappa h_kappa hsampE
      (mask x) (Hn x) hbin hxG (lambdaHat hnm (mask x) (Gref x))
      hnoise hlam1 hbulk M hM (w n) hw_nn' hw1_pos hloss hscale
    refine le_trans hkey ?_
    calc CerrE * sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p)
        = CerrE * (sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p)) := by ring
      _ ≤ max 1 CerrE * (sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p)) :=
          mul_le_mul_of_nonneg_right (le_max_right 1 CerrE)
            (mul_nonneg h_sigma.le (Real.sqrt_nonneg _))
      _ = max 1 CerrE * sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p) := by ring
  
  
  refine ⟨Ecal ∩ S ∩ {x : Om |
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
        p (CLB * Real.sqrt ((m : ℝ) / p))
        (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
        (mask x) U0 V0},
    hEcal_meas.inter hS_meas |>.inter hG_meas, ?_, ?_⟩
  · have hSc : P Sᶜ = 0 := by
      rw [MeasureTheory.measure_compl hS_meas (by rw [hS_prob]; exact ENNReal.one_ne_top),
        hS_prob, MeasureTheory.measure_univ]
      simp
    have hcBnn : (0 : ℝ) ≤ cB := hcB.le
    have hn3nn : (0 : ℝ) ≤ ((n : ℝ) ^ 3)⁻¹ := (inv_pos.mpr (pow_pos hn_pos_real 3)).le
    have hr4nn : (0 : ℝ) ≤ cB / (n : ℝ) ^ 4 := div_nonneg hcBnn (by positivity)
    have hcompl : ∀ (G0 : Set Om), MeasurableSet G0 →
        1 - ENNReal.ofReal (cB / (n : ℝ) ^ 4) ≤ P G0 →
        P G0ᶜ ≤ ENNReal.ofReal (cB / (n : ℝ) ^ 4) := by
      intro G0 hG0 hprob
      have hfin : P G0 ≠ ⊤ := by
        refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        calc P G0 ≤ P Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := MeasureTheory.measure_univ
      rw [MeasureTheory.measure_compl hG0 hfin, MeasureTheory.measure_univ]
      refine tsub_le_iff_right.mpr ?_
      have h := tsub_le_iff_right.mp hprob
      rwa [add_comm] at h
  
    have hinter : ∀ (G0 : Set Om), MeasurableSet G0 →
        P G0ᶜ ≤ ENNReal.ofReal (cB / (n : ℝ) ^ 4) →
        P Ecal ≤ P ((Ecal ∩ S) ∩ G0) + ENNReal.ofReal (cB / (n : ℝ) ^ 4) := by
      intro G0 hG0 hc
      have hunion : P (Sᶜ ∪ G0ᶜ) ≤ P G0ᶜ := by
        refine le_trans (measure_union_le _ _) ?_
        rw [hSc, zero_add]
      have hsub : Ecal ⊆ ((Ecal ∩ S) ∩ G0) ∪ (Sᶜ ∪ G0ᶜ) := by
        intro y hy
        by_cases h1 : y ∈ S
        · by_cases h2 : y ∈ G0
          · exact Or.inl ⟨⟨hy, h1⟩, h2⟩
          · exact Or.inr (Or.inr h2)
        · exact Or.inr (Or.inl h1)
      calc P Ecal ≤ P (((Ecal ∩ S) ∩ G0) ∪ (Sᶜ ∪ G0ᶜ)) := measure_mono hsub
        _ ≤ P ((Ecal ∩ S) ∩ G0) + P (Sᶜ ∪ G0ᶜ) := measure_union_le _ _
        _ ≤ P ((Ecal ∩ S) ∩ G0) + P G0ᶜ := add_le_add le_rfl hunion
        _ ≤ P ((Ecal ∩ S) ∩ G0) + ENNReal.ofReal (cB / (n : ℝ) ^ 4) := add_le_add le_rfl hc
    have hgoal : 1 - max 1 (c1bA + cB) * ((n : ℝ) ^ 3)⁻¹ ≤
        (1 - c1bA * ((n : ℝ) ^ 3)⁻¹) - cB / (n : ℝ) ^ 4 := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hm4 : cB / (n : ℝ) ^ 4 ≤ cB * ((n : ℝ) ^ 3)⁻¹ := by
        have hp3 : (0 : ℝ) < (n : ℝ) ^ 3 := pow_pos hn_pos_real 3
        have h34 : ((n : ℝ) ^ 3) ≤ ((n : ℝ) ^ 4) := by
          have hs : ((n : ℝ) ^ 3) * 1 ≤ ((n : ℝ) ^ 3) * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hn1 hp3.le
          calc ((n : ℝ) ^ 3) = ((n : ℝ) ^ 3) * 1 := (mul_one _).symm
            _ ≤ ((n : ℝ) ^ 3) * (n : ℝ) := hs
            _ = ((n : ℝ) ^ 4) := by ring
        have hinv : 1 / (n : ℝ) ^ 4 ≤ 1 / (n : ℝ) ^ 3 :=
          one_div_le_one_div_of_le hp3 h34
        have hmul := mul_le_mul_of_nonneg_left hinv hcBnn
        calc cB / (n : ℝ) ^ 4 = cB * (1 / (n : ℝ) ^ 4) := by ring
          _ ≤ cB * (1 / (n : ℝ) ^ 3) := hmul
          _ = cB * ((n : ℝ) ^ 3)⁻¹ := by ring
      have hkey : c1bA * ((n : ℝ) ^ 3)⁻¹ + cB / (n : ℝ) ^ 4
          ≤ max 1 (c1bA + cB) * ((n : ℝ) ^ 3)⁻¹ := by
        have hstep1 : c1bA * ((n : ℝ) ^ 3)⁻¹ + cB / (n : ℝ) ^ 4
            ≤ c1bA * ((n : ℝ) ^ 3)⁻¹ + cB * ((n : ℝ) ^ 3)⁻¹ := add_le_add le_rfl hm4
        have hstep2 : (c1bA + cB) * ((n : ℝ) ^ 3)⁻¹
            ≤ max 1 (c1bA + cB) * ((n : ℝ) ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hn3nn
        calc c1bA * ((n : ℝ) ^ 3)⁻¹ + cB / (n : ℝ) ^ 4
            ≤ c1bA * ((n : ℝ) ^ 3)⁻¹ + cB * ((n : ℝ) ^ 3)⁻¹ := hstep1
          _ = (c1bA + cB) * ((n : ℝ) ^ 3)⁻¹ := by ring
          _ ≤ max 1 (c1bA + cB) * ((n : ℝ) ^ 3)⁻¹ := hstep2
      have hfin : 1 - max 1 (c1bA + cB) * ((n : ℝ) ^ 3)⁻¹
          ≤ 1 - (c1bA * ((n : ℝ) ^ 3)⁻¹ + cB / (n : ℝ) ^ 4) := sub_le_sub_left hkey 1
  
      calc 1 - max 1 (c1bA + cB) * ((n : ℝ) ^ 3)⁻¹
          ≤ 1 - (c1bA * ((n : ℝ) ^ 3)⁻¹ + cB / (n : ℝ) ^ 4) := hfin
        _ = (1 - c1bA * ((n : ℝ) ^ 3)⁻¹) - cB / (n : ℝ) ^ 4 := by ring
    refine le_trans (ENNReal.ofReal_le_ofReal hgoal) ?_
    rw [ENNReal.ofReal_sub (1 - c1bA * ((n : ℝ) ^ 3)⁻¹) hr4nn]
    exact tsub_le_iff_right.mpr
      (le_trans hEcal_prob (hinter _ hG_meas (hcompl _ hG_meas hG_prob)))
  
  
  
  
  
  
  · intro x hx
    have hmaskx : mask' x = mask x := hmask'_eq_of x hx.1.2
    have hdisp := hEcal_disp x hx.1.1
    rw [hmaskx] at hdisp
    refine ⟨?_, fun M hM hloss => hMaster x hx.1.1 hx.1.2 hx.2 M hM hloss⟩
    · intro Mtil hMtil
      have hmin := hMtil.2 hM0_mem
      have hcmp : C0A * ((Real.log (m : ℝ))⁻¹) ^ 2 ≤ C_L * w n ⟨0, hn⟩ := by
        have hb := hwCL n hn h_ratio_hi h_ratio_lo
        have hCLd : C_L * (C0A / C_L) = C0A := by
          rw [div_eq_mul_inv, ← mul_assoc, mul_comm C_L C0A, mul_assoc,
            mul_inv_cancel₀ h_C_L.ne', mul_one]
        have hmul := mul_le_mul_of_nonneg_left hb h_C_L.le
        have heq : C_L * ((C0A / C_L) * ((Real.log (m : ℝ))⁻¹) ^ 2)
            = C0A * ((Real.log (m : ℝ))⁻¹) ^ 2 := by
          rw [← mul_assoc, hCLd]
        rw [heq] at hmul
        exact hmul
      have hne0 : sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
          (obsMatrix (mask x) M0 (Hn x)) (mask x) M0 ≠ 0 := by
        have hv : |sigmaHat hnm (lambdaHat hnm (mask x) (Gref x))
            (obsMatrix (mask x) M0 (Hn x)) (mask x) M0 / sigma - 1|
            ≤ CA * PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.deltaM m := by
          have h := hdisp.2.2.2.2.2.1
          rw [← hsigmaHat_eq x M0] at h
          exact h
        exact hsigmaHat_M0_ne x
          (CA * PaperProofTasks.job_paper_951aae9227d84800bf9113306ae458aa.Statlib.Imported.deltaM m)
          hv hCAlt
      exact hMaster x hx.1.1 hx.1.2 hx.2 Mtil hMtil.1
        (le_trans hmin (htruth x ⟨C0A, hC0A.le, hdisp.2.2.2.2.2.2.1, hcmp⟩ hne0))
  /- @proof-region region.root.56e0a97c9534 end -/

end Statlib.Imported

-- Paper root revision 3f57f9ee-70df-4acc-8c5d-b6bdab1799c4

