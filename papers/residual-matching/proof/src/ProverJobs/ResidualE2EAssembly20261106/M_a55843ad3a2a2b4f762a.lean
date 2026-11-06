import Statlib.HighDim.MatrixAnalysis.FrobeniusNormSvdRelation
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SoftThresholdDenoisingHelpers
import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.MatrixRecovery.MatrixRipRecoveryBound
import Statlib.HighDim.Vocabulary.SVD
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548
import ProverJobs.ResidualE2EAssembly20261106.M_faf850de1c7aeae55a9f
import ProverJobs.ResidualE2EAssembly20261106.M_e30b684369848ae77427
import ProverJobs.ResidualE2EAssembly20261106.M_f9f1d7c2712dc5f86173
import ProverJobs.ResidualE2EAssembly20261106.M_420ada0a005e01361335
import ProverJobs.ResidualE2EAssembly20261106.M_557c8318b7a0920ef473
import ProverJobs.ResidualE2EAssembly20261106.M_3b7837ec897a8f11f4d4
import ProverJobs.ResidualE2EAssembly20261106.M_7f3eea621b0d2e005d06
import ProverJobs.ResidualE2EAssembly20261106.M_eeb0c48628f53be1e6d9

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching








run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false in
theorem statopia_math_node_160158563_7abd8755 : ∀ (rho_min : ℝ) (h_rho_min : 0 < rho_min)
    (alpha0 : ℝ) (h_alpha0 : 15 < alpha0)
    (C_L : ℝ) (h_C_L : 0 < C_L)
    (K c Ks CLam Cthet : ℝ)
    (hK : 1 ≤ K) (hc : 0 < c) (hKs : 0 ≤ Ks) (hCLam : 1 ≤ CLam) (hCthet : 1 ≤ Cthet),
    ∃ N0E : ℕ, ∃ CsampE CerrE : ℝ, 0 < CsampE ∧ 0 < CerrE ∧
      ∀ {m n : ℕ} (hm : 0 < m) (hmN : N0E ≤ m) (hn : 0 < n) (hnm : n ≤ m)
        (hlog1 : 1 ≤ Real.log (m : ℝ))
        (r : ℕ) (hr : 0 < r) (hrn : 12 * r ≤ n)
        (p sigma Lam th mu0 mu1 : ℝ)
        (hp : 0 < p) (hp1 : p ≤ 1) (hsig : 0 < sigma)
        (hLam_nn : 0 ≤ Lam) (hth_nn : 0 ≤ th) (hmu0 : 0 < mu0) (hmu01 : mu0 ≤ mu1)
        (rlo : rho_min ≤ (n : ℝ) / (m : ℝ)) (rhi : (n : ℝ) / (m : ℝ) ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        (hLam_le : Lam ≤ CLam * Real.sqrt ((m : ℝ) / p))
        (hth_le : th ≤ Cthet * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
        (M0 : Matrix (Fin m) (Fin n) ℝ) (U0 : Matrix (Fin m) (Fin r) ℝ)
        (V0 : Matrix (Fin n) (Fin r) ℝ) (d0 : Fin r → ℝ)
        (hM0 : M0 = U0 * Matrix.diagonal d0 * Matrix.transpose V0)
        (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
        (hd0 : ∀ i : Fin r, 0 < d0 i) (hd0_anti : Antitone d0)
        (hlevU0 : ∀ i : Fin m, rowL2Sq U0 i ≤ mu0 * (r : ℝ) / (m : ℝ))
        (hlevV0 : ∀ j : Fin n, rowL2Sq V0 j ≤ mu0 * (r : ℝ) / (n : ℝ))
        (hlast : r - 1 < n)
        (s_star : ℝ) (h_s_star_pos : 0 < s_star)
        (h_s_star : s_star = psi hnm M0 ⟨r - 1, hlast⟩)
        (s_1 : ℝ) (h_s_1 : s_1 = psi hnm M0 ⟨0, hn⟩)
        (kappa : ℝ) (h_kappa : kappa = s_1 / s_star)
        (h_samp : CsampE * kappa ^ 2 *
            (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2)
          ≤ (n : ℝ) * p)
        (mask : Matrix (Fin m) (Fin n) ℝ) (H : Matrix (Fin m) (Fin n) ℝ)
        (hbin : ∀ (i : Fin m) (j : Fin n), mask i j = 0 ∨ mask i j = 1)
        (hGood : PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
          p Lam th mask U0 V0)
        (lamHat : Fin n → ℝ)
        (hnoise : spectralNorm (projMask mask H) ≤ K * sigma * Real.sqrt ((m : ℝ) * p))
        (hlam1 : lamHat ⟨0, hn⟩ ≤ K * Real.sqrt p)
        (hbulk : c * (n : ℝ) * Real.sqrt p ≤ ∑ i ∈ bulkIdx n, lamHat i)
        (M : Matrix (Fin m) (Fin n) ℝ) (hMmem : M ∈ candidateSet r mu1)
        (w : Fin n → ℝ) (hw_nn : ∀ i : Fin n, 0 ≤ w i) (hw0 : 0 < w ⟨0, hn⟩)
        (hloss : normLoss hnm p w lamHat (obsMatrix mask M0 H) mask M
          ≤ ((C_L * w ⟨0, hn⟩ : ℝ) : WithTop ℝ))
        (hscale : |sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M / sigma - 1|
          ≤ Ks * (Real.log (m : ℝ))⁻¹ +
            Ks * frobNorm (projMask mask (M - M0)) /
              (sigma * Real.sqrt ((m : ℝ) * (n : ℝ) * p))),
        frobNorm (M - M0) ≤ CerrE * sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p) := by
  /- @proof-region region.target-node.session.e3a9352899725178 begin -/
  classical
  intro rho_min h_rho_min alpha0 h_alpha0 C_L hC_L K c Ks CLam Cthet hK hc hKs hCLam hCthet
  obtain ⟨C165, c165, hC165_pos, hc165_pos, h165⟩ :=
    PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.paper_165f462a7e494b7a9c0f4fb377733656.{0}
      rho_min h_rho_min CLam Cthet hCLam hCthet
  obtain ⟨N165, hN165⟩ := h165 alpha0 h_alpha0
  obtain ⟨K', hK'_def⟩ : ∃ t : ℝ, t = max (K + Real.sqrt C_L) (max K (max Ks 1)) := ⟨_, rfl⟩
  have hK'_geKC : K + Real.sqrt C_L ≤ K' := by
    rw [hK'_def]
    exact le_max_left (K + Real.sqrt C_L) (max K (max Ks 1))
  have hK'_geK : K ≤ K' := by
    rw [hK'_def]
    exact le_trans (le_max_left K (max Ks 1))
      (le_max_right (K + Real.sqrt C_L) (max K (max Ks 1)))
  have hK'_ge1 : 1 ≤ K' := le_trans hK hK'_geK
  have hK'_pos : 0 < K' := lt_of_lt_of_le zero_lt_one hK'_ge1
  have hK'_geKs : Ks ≤ K' := by
    rw [hK'_def]
    exact le_trans (le_trans (le_max_left Ks 1) (le_max_right K (max Ks 1)))
      (le_max_right (K + Real.sqrt C_L) (max K (max Ks 1)))
  have h40 : 0 < 40 * K' ^ 4 := mul_pos (by norm_num) (pow_pos hK'_pos 4)
  obtain ⟨C1, hC1_def⟩ : ∃ t : ℝ, t = K + (K + Real.sqrt C_L) * (K' + 1) / c + 1 := ⟨_, rfl⟩
  have hmid_pos : 0 < (K + Real.sqrt C_L) * (K' + 1) / c :=
    div_pos (mul_pos (by linarith [Real.sqrt_nonneg C_L]) (by linarith)) hc
  have hC1_pos : 0 < C1 := by rw [hC1_def]; linarith
  have hC1_ge1 : 1 ≤ C1 := by rw [hC1_def]; linarith
  clear hmid_pos
  obtain ⟨CM, hCM_def⟩ : ∃ t : ℝ, t = 1 + 3 * C1 := ⟨_, rfl⟩
  have hCM_ge1 : 1 ≤ CM := by rw [hCM_def]; linarith
  obtain ⟨CCM, hCCM_pos, hCCM⟩ := hN165 CM hCM_ge1
  clear h165 hN165

  obtain ⟨CsampE, hCsampE_def⟩ :
      ∃ t : ℝ, t = max (max C165 CCM) (max (16 * C1 ^ 2 * CLam ^ 2) (40 * K' ^ 4)) := ⟨_, rfl⟩
  have hCsampE_pos : 0 < CsampE := by
    rw [hCsampE_def]
    exact lt_of_lt_of_le h40 (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨CerrE, hCerrE_def⟩ :
      ∃ t : ℝ, t = max (3 * Real.sqrt 2 * C1) (40 * K' ^ 4) := ⟨_, rfl⟩
  have hCerrE_pos : 0 < CerrE := by
    rw [hCerrE_def]
    exact lt_of_lt_of_le h40 (le_max_right _ _)
  refine ⟨max N165 3, CsampE, CerrE, hCsampE_pos, hCerrE_pos, ?_⟩
  intro m n hm hmN hn hnm hlog1 r hr hrn p sigma Lam th mu0 mu1 hp hp1 hsig hLam_nn hth_nn
    hmu0 hmu01 rlo rhi hsparse hLam_le hth_le M0 U0 V0 d0 hM0 hU0 hV0 hd0 hd0_anti hlevU0 hlevV0
    hlast s_star h_s_star_pos h_s_star s_1 h_s_1 kappa h_kappa h_samp mask H hbin hGood lamHat hnoise
    hlam1 hbulk M hMmem w hw_nn hw0 hloss hscale
  have hN165_le : N165 ≤ m := le_trans (le_max_left N165 3) hmN
  have hC165_le : C165 ≤ CsampE := by
    rw [hCsampE_def]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCCM_le : CCM ≤ CsampE := by
    rw [hCsampE_def]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have h16_le : 16 * C1 ^ 2 * CLam ^ 2 ≤ CsampE := by
    rw [hCsampE_def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h40_le : 40 * K' ^ 4 ≤ CsampE := by
    rw [hCsampE_def]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have h40_le_err : 40 * K' ^ 4 ≤ CerrE := by
    rw [hCerrE_def]
    exact le_max_right _ _
  have hC3_le_err : 3 * Real.sqrt 2 * C1 ≤ CerrE := by
    rw [hCerrE_def]
    exact le_max_left _ _
  have hm_real : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hn_real : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnp_pos : (0:ℝ) < (n:ℝ) * p := mul_pos hn_real hp
  have hlog_pos : (0:ℝ) < Real.log (m:ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hmp_pos : (0:ℝ) < (m:ℝ) / p := div_pos hm_real hp
  have hsqrt_mp_pos : 0 < Real.sqrt ((m:ℝ) / p) := by positivity
  obtain ⟨H0, hH0def⟩ : ∃ t : ℝ, t = sigma * Real.sqrt ((m : ℝ) / p) := ⟨_, rfl⟩
  have hH0_nonneg : 0 ≤ H0 := by
    rw [hH0def]
    exact le_of_lt (mul_pos hsig hsqrt_mp_pos)
  obtain ⟨B, hBdef⟩ :
      ∃ t : ℝ, t = CLam * max mu0 mu1 * (r : ℝ) / Real.sqrt ((n : ℝ) * p) := ⟨_, rfl⟩
  have hspecM0 : spectralNorm M0 = s_1 := by
    have hmin : 0 < min m n := lt_min hm hn
    rw [h_s_1]
    simp only [psi, spectralNorm, dif_pos hmin]
    congr 1
  have hs_star_le_s1 : s_star ≤ s_1 := by
    rw [h_s_star, h_s_1]
    simp only [psi]
    refine Statlib.HighDim.MatrixAnalysis.singularValues_antitone M0 ?_
    simp [Fin.le_def]
  have hkappa1 : 1 ≤ kappa := by
    rw [h_kappa, div_eq_mul_inv]
    have h1 := mul_le_mul_of_nonneg_right hs_star_le_s1
      (inv_nonneg.mpr (le_of_lt h_s_star_pos))
    rwa [mul_inv_cancel₀ (ne_of_gt h_s_star_pos)] at h1
  have hs1_pos : 0 < s_1 := lt_of_lt_of_le h_s_star_pos hs_star_le_s1
  have hspec_eq_opNorm : ∀ (A : Matrix (Fin m) (Fin n) ℝ),
      spectralNorm A = Statlib.HighDim.MatrixAnalysis.opNorm A := by
    intro A
    have hmin : 0 < min m n := lt_min hm hn
    rw [spectralNorm, dif_pos hmin]
    exact ((Statlib.HighDim.MatrixAnalysis.singular_value_properties A
        (Or.inl ⟨⟨0, hm⟩⟩)).1 hmin).trans
      (Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 A).symm
  have hsumU : ∑ i : Fin m, rowL2Sq U0 i = (r : ℝ) := by
    have hrel : ((U0 : Matrix (Fin m) (Fin r) ℝ).transpose * U0).trace
        = ∑ i : Fin m, ∑ j : Fin r, U0 i j ^ 2 :=
      (Statlib.HighDim.MatrixAnalysis.frobenius_norm_svd_relation U0).2.2
    have hone : (1 : Matrix (Fin r) (Fin r) ℝ).trace = (r : ℝ) := by
      simp [Matrix.trace]
    have hrow : (∑ i : Fin m, rowL2Sq U0 i) = ∑ i : Fin m, ∑ j : Fin r, U0 i j ^ 2 := by
      simp [rowL2Sq]
    rw [hrow, ← hrel, hU0, hone]
  have hmu0_ge1 : 1 ≤ mu0 := by
    have hle : ∑ i : Fin m, rowL2Sq U0 i ≤ ∑ i : Fin m, (mu0 * (r : ℝ) / (m : ℝ)) :=
      Finset.sum_le_sum (fun i _ => hlevU0 i)
    have hconst : ∑ i : Fin m, (mu0 * (r : ℝ) / (m : ℝ)) = mu0 * (r : ℝ) := by
      have hmne : ((m : ℝ)) ≠ 0 := ne_of_gt hm_real
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_comm (m : ℝ), div_mul_cancel₀ _ hmne]
    rw [hsumU, hconst] at hle
    have hrpos : (0:ℝ) < (r : ℝ) := by exact_mod_cast hr
    have h1 := mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr (le_of_lt hrpos))
    have h2 : (mu0 * (r : ℝ)) * (r : ℝ)⁻¹ = mu0 := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hrpos), mul_one]
    rw [mul_inv_cancel₀ (ne_of_gt hrpos), h2] at h1
    exact h1
  have hmu_max_ge1 : 1 ≤ max mu0 mu1 := le_trans hmu0_ge1 (le_max_left _ _)
  have hkappa_sq : 1 ≤ kappa ^ 2 := by
    have h0 : (0:ℝ) ≤ kappa := le_trans zero_le_one hkappa1
    have h := mul_le_mul hkappa1 hkappa1 (by norm_num : (0:ℝ) ≤ 1) h0
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ kappa * kappa := h
      _ = kappa ^ 2 := by ring
  obtain ⟨S0, hS0def⟩ : ∃ t : ℝ, t = max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)
      + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 := ⟨_, rfl⟩
  have hS0nn : (0:ℝ) ≤ S0 := by
    rw [hS0def]
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (mul_nonneg (le_trans (le_of_lt hmu0) (le_max_left mu0 mu1))
        (by positivity)) (le_of_lt hlog_pos)
    · positivity
  have hC165np : C165 * mu0 * (r : ℝ) * Real.log (m : ℝ) ≤ (n : ℝ) * p := by
    have hlogm : (0:ℝ) ≤ Real.log (m:ℝ) := le_of_lt hlog_pos
    have hrnn : (0:ℝ) ≤ (r:ℝ) := by positivity
    have hmun : (0:ℝ) ≤ mu0 := le_of_lt hmu0
    have hmnl : (0:ℝ) ≤ mu0 * (r:ℝ) * Real.log (m:ℝ) :=
      mul_nonneg (mul_nonneg hmun hrnn) hlogm
    have h1 : mu0 * (r:ℝ) * Real.log (m:ℝ) ≤ max mu0 mu1 * (r:ℝ) * Real.log (m:ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left mu0 mu1) hrnn) hlogm
    have h2 : max mu0 mu1 * (r:ℝ) * Real.log (m:ℝ) ≤ S0 := by
      rw [hS0def]
      exact le_add_of_nonneg_right (by positivity)
    have h3 : S0 ≤ kappa ^ 2 * S0 := by
      calc S0 = 1 * S0 := by ring
        _ ≤ kappa ^ 2 * S0 := mul_le_mul_of_nonneg_right hkappa_sq hS0nn
    have h4 : mu0 * (r:ℝ) * Real.log (m:ℝ) ≤ kappa ^ 2 * S0 := le_trans h1 (le_trans h2 h3)
    have h5 : C165 * (mu0 * (r:ℝ) * Real.log (m:ℝ)) ≤ CsampE * (kappa ^ 2 * S0) :=
      mul_le_mul hC165_le h4 hmnl (le_of_lt hCsampE_pos)
    calc C165 * mu0 * (r:ℝ) * Real.log (m:ℝ)
        = C165 * (mu0 * ((r:ℝ) * Real.log (m:ℝ))) := by ring
      _ = C165 * (mu0 * (r:ℝ) * Real.log (m:ℝ)) := by ring
      _ ≤ CsampE * (kappa ^ 2 * S0) := h5
      _ = CsampE * kappa ^ 2 * S0 := by ring
      _ = CsampE * kappa ^ 2 * (max mu0 mu1 * (r:ℝ) * Real.log (m:ℝ)
            + (max mu0 mu1) ^ 2 * (r:ℝ) ^ 2) := by rw [hS0def]
      _ ≤ (n:ℝ) * p := h_samp
  have hSMin_pos :
      0 < PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.SMin d0 := by
    unfold PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.SMin
    have hmin : r - 1 < min m n := lt_min (by omega : r - 1 < m) hlast
    have hchild := statopia_math_node_919610516_79178f41 hr (by omega : r ≤ n) hnm
      M0 U0 V0 d0 hM0 hU0 hV0 hd0 hmin
    have hpos : (0:ℝ) < Statlib.HighDim.MatrixAnalysis.singularValues M0 ⟨r - 1, hmin⟩ := by
      have h2 : (0:ℝ) < psi hnm M0 ⟨r - 1, hlast⟩ := by
        rw [← h_s_star]
        exact h_s_star_pos
      simp only [psi] at h2
      have hidx : (Fin.cast (Nat.min_eq_right hnm).symm ⟨r - 1, hlast⟩ : Fin (min m n))
          = ⟨r - 1, hmin⟩ := Fin.ext rfl
      rwa [hidx] at h2
    exact lt_of_lt_of_le hpos hchild
  have h2U : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm U0
      ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) := by
    unfold PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm
    exact Real.iSup_le (fun i => Real.sqrt_le_sqrt (hlevU0 i)) (Real.sqrt_nonneg _)
  have h2V : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm V0
      ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) := by
    unfold PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm
    exact Real.iSup_le (fun i => Real.sqrt_le_sqrt (hlevV0 i)) (Real.sqrt_nonneg _)
  have hRSCax : ∀ {Omegas : Type} [inst : MeasurableSpace Omegas] (mu : Measure Omegas)
      [IsProbabilityMeasure mu] (Om : Omegas → Matrix (Fin m) (Fin n) ℝ),
      (∀ (i : Fin m) (j : Fin n), Measurable fun omega => Om omega i j) →
      ProbabilityTheory.iIndepFun
        (fun (ij : Fin m × Fin n) (omega : Omegas) => Om omega ij.1 ij.2) mu →
      (∀ (i : Fin m) (j : Fin n),
        mu {omega : Omegas | Om omega i j = 1} = ENNReal.ofReal p) →
      (∀ (i : Fin m) (j : Fin n) (omega : Omegas), Om omega i j = 0 ∨ Om omega i j = 1) →
      ∀ (omega : Omegas),
        PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.MaskEvent
            Lam th p (Om omega)
            (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.tangentSpace
              U0 V0) →
          PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.npCondition
              CCM mu0 mu1 d0 p m n →
            ∀ (Mprime : Matrix (Fin m) (Fin n) ℝ),
              PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.InLowRankClass
                  r mu1 Mprime →
                PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.spectralNorm
                    Mprime ≤
                  CM *
                    PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.SMax d0 →
                  (p / 2) *
                      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq
                        (Mprime - M0) ≤
                    PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq
                      (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.projMask
                        (Om omega) (Mprime - M0)) := by
    intro Omegas instOm mu instP Om hmeas hindep hmarg hbin' omega hmask hnp Mprime hInLow hSMax
    exact ((hCCM m n hN165_le hm hn hnm rlo rhi r hr hrn p hp hp1 hsparse mu0 mu1 hmu01
      U0 V0 d0 M0 hU0 hV0 hM0 hd0_anti hSMin_pos h2U h2V
      mu Om hmeas hindep hmarg hbin' hC165np Lam th hLam_nn hth_nn hLam_le hth_le
      omega hmask).2.2 hnp Mprime hInLow hSMax).1
  clear hCCM

  have hnp_big : 40 * K' ^ 4 * (r : ℝ) ≤ (n : ℝ) * p := by
    have hrnn : (0:ℝ) ≤ (r : ℝ) := by positivity
    have hmu_nn : (0:ℝ) ≤ max mu0 mu1 := le_trans zero_le_one hmu_max_ge1
    have hterm1 : (r : ℝ) ≤ max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) := by
      have h1 : (1:ℝ) ≤ max mu0 mu1 * Real.log (m : ℝ) := by
        have h2 := mul_le_mul hmu_max_ge1 hlog1 (show (0:ℝ) ≤ 1 by norm_num) hmu_nn
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ max mu0 mu1 * Real.log (m : ℝ) := h2
      calc (r : ℝ) = 1 * (r : ℝ) := by ring
        _ ≤ (max mu0 mu1 * Real.log (m : ℝ)) * (r : ℝ) := mul_le_mul_of_nonneg_right h1 hrnn
        _ = max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) := by ring
    have hterm2 : (0:ℝ) ≤ (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 := by positivity
    have hsum_ge : (r : ℝ) ≤
        max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 :=
      le_trans hterm1 (le_add_of_nonneg_right hterm2)
    have hprod : (r : ℝ) ≤ kappa ^ 2 *
        (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) := by
      calc (r : ℝ) = 1 * (r : ℝ) := by ring
        _ ≤ kappa ^ 2 * (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) +
              (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) :=
            mul_le_mul hkappa_sq hsum_ge hrnn (by positivity)
    have hkey : 40 * K' ^ 4 * (r : ℝ) ≤ CsampE * kappa ^ 2 *
        (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) := by
      have h1 : 40 * K' ^ 4 * (r : ℝ) ≤ CsampE *
          (kappa ^ 2 * (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) +
            (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2)) :=
        mul_le_mul h40_le hprod hrnn (le_of_lt hCsampE_pos)
      calc 40 * K' ^ 4 * (r : ℝ) ≤ CsampE *
            (kappa ^ 2 * (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) +
              (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2)) := h1
        _ = CsampE * kappa ^ 2 * (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) +
              (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) := by ring
    exact le_trans hkey h_samp
  have hbeta_le : 2 * C1 * B ≤ 1 / 2 := by
    have hnp16 : 16 * C1 ^ 2 * CLam ^ 2 * (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 ≤ (n : ℝ) * p := by
      have hsq : (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 ≤
          max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 :=
        le_add_of_nonneg_left (by positivity)
      have hchain : 16 * C1 ^ 2 * CLam ^ 2 * (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 ≤
          16 * C1 ^ 2 * CLam ^ 2 *
            (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) := by
        have hcoef : (0:ℝ) ≤ 16 * C1 ^ 2 * CLam ^ 2 := by positivity
        calc 16 * C1 ^ 2 * CLam ^ 2 * (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2
            = (16 * C1 ^ 2 * CLam ^ 2) * ((max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) := by ring
          _ ≤ (16 * C1 ^ 2 * CLam ^ 2) *
                (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hsq hcoef
          _ = 16 * C1 ^ 2 * CLam ^ 2 *
                (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) :=
              by ring
      have hstep : 16 * C1 ^ 2 * CLam ^ 2 *
            (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) ≤
          CsampE * kappa ^ 2 *
            (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) := by
        have hSnn : (0:ℝ) ≤ max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) +
            (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 := by positivity
        have hcoef2 : 16 * C1 ^ 2 * CLam ^ 2 ≤ CsampE * kappa ^ 2 := by
          calc 16 * C1 ^ 2 * CLam ^ 2 = (16 * C1 ^ 2 * CLam ^ 2) * 1 := by ring
            _ ≤ (16 * C1 ^ 2 * CLam ^ 2) * kappa ^ 2 :=
                mul_le_mul_of_nonneg_left hkappa_sq (by positivity)
            _ ≤ CsampE * kappa ^ 2 := mul_le_mul_of_nonneg_right h16_le (by positivity)
        exact mul_le_mul_of_nonneg_right hcoef2 hSnn
      exact le_trans hchain (le_trans hstep h_samp)
    have h4sq : (4 * C1 * CLam * max mu0 mu1 * (r : ℝ)) ^ 2 ≤ (n : ℝ) * p := by
      have heq : (4 * C1 * CLam * max mu0 mu1 * (r : ℝ)) ^ 2
          = 16 * C1 ^ 2 * CLam ^ 2 * (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 := by ring
      rw [heq]
      exact hnp16
    have h4nn : (0:ℝ) ≤ 4 * C1 * CLam * max mu0 mu1 * (r : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4)
        (le_of_lt hC1_pos)) (by linarith : (0:ℝ) ≤ CLam))
        (le_trans zero_le_one hmu_max_ge1)) (by positivity)
    have hsqrt4 : 4 * C1 * CLam * max mu0 mu1 * (r : ℝ) ≤ Real.sqrt ((n : ℝ) * p) := by
      have hsq' : (4 * C1 * CLam * max mu0 mu1 * (r : ℝ)) ^ 2 ≤ (Real.sqrt ((n : ℝ) * p)) ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hnp_pos)]
        exact h4sq
      have habs := (sq_le_sq.mp hsq')
      rwa [abs_of_nonneg h4nn, abs_of_nonneg (Real.sqrt_nonneg _)] at habs
    have hsqrt_np_pos : (0:ℝ) < Real.sqrt ((n : ℝ) * p) := by positivity
    have hBeq : 2 * C1 * B = (2 * C1 * (CLam * max mu0 mu1 * (r : ℝ))) / Real.sqrt ((n : ℝ) * p) := by
      rw [hBdef]
      ring
    rw [hBeq, div_le_iff₀ hsqrt_np_pos]
    have hhalf : 2 * C1 * CLam * max mu0 mu1 * (r : ℝ) ≤ 1 / 2 * Real.sqrt ((n : ℝ) * p) := by
      have h := mul_le_mul_of_nonneg_left hsqrt4 (by norm_num : (0:ℝ) ≤ 1 / 2)
      calc 2 * C1 * CLam * max mu0 mu1 * (r : ℝ)
          = 1 / 2 * (4 * C1 * CLam * max mu0 mu1 * (r : ℝ)) := by ring
        _ ≤ 1 / 2 * Real.sqrt ((n : ℝ) * p) := h
    calc 2 * C1 * (CLam * max mu0 mu1 * (r : ℝ)) = 2 * C1 * CLam * max mu0 mu1 * (r : ℝ) := by ring
      _ ≤ 1 / 2 * Real.sqrt ((n : ℝ) * p) := hhalf
  have hrn' : r ≤ n := by omega
  have hMmem' := hMmem
  obtain ⟨hMrank, k, U, V, d, hk, hd, hU, hV, hMfac, hlevU, hlevV⟩ := hMmem'
  have hrank : Matrix.rank (M - M0) ≤ 2 * r := by
    set A : Matrix (Fin m) (Fin k ⊕ Fin r) ℝ :=
      fun i s => Sum.elim (fun j => (U * Matrix.diagonal d) i j)
        (fun j => -((U0 * Matrix.diagonal d0) i j)) s with hAdef
    set Bm : Matrix (Fin n) (Fin k ⊕ Fin r) ℝ :=
      fun l s => Sum.elim (fun j => V l j) (fun j => V0 l j) s with hBdef
    have hfac : M - M0 = A * Matrix.transpose Bm := by
      ext i l
      simp only [hAdef, hBdef, Matrix.sub_apply, hMfac, hM0, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.diagonal_apply, Fintype.sum_sum_type,
        Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
    rw [hfac]
    refine le_trans (Matrix.rank_mul_le_left _ _) ?_
    refine le_trans (Matrix.rank_le_card_width _) ?_
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hGood' := hGood
  unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent at hGood'
  obtain ⟨hWmask, hTmSchur, hTangBilin, hFourBilin⟩ := hGood'
  clear hWmask hTmSchur hTangBilin hFourBilin

  obtain ⟨Dlt, hDltdef⟩ : ∃ t : ℝ, t = spectralNorm (M - M0) := ⟨_, rfl⟩
  have hcoarse : Dlt ≤ 2 * C1 * H0 + 4 * C1 * B * s_1 := by
    have hC1spec : K + (K + Real.sqrt C_L) * (max K (max Ks 1) + 1) / c + 1 ≤ C1 := by
      have h4 : C1 =
          K + (K + Real.sqrt C_L) * (max (K + Real.sqrt C_L) (max K (max Ks 1)) + 1) / c + 1 := by
        rw [hC1_def, hK'_def]
      rw [h4]
      have h2 : (K + Real.sqrt C_L) * (max K (max Ks 1) + 1)
          ≤ (K + Real.sqrt C_L) * (max (K + Real.sqrt C_L) (max K (max Ks 1)) + 1) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (le_max_right (K + Real.sqrt C_L) (max K (max Ks 1))) (le_refl 1))
          (add_nonneg (le_trans zero_le_one hK) (Real.sqrt_nonneg C_L))
      have h3 : (K + Real.sqrt C_L) * (max K (max Ks 1) + 1) / c
          ≤ (K + Real.sqrt C_L) * (max (K + Real.sqrt C_L) (max K (max Ks 1)) + 1) / c :=
        (by
          rw [div_le_iff₀ hc, div_mul_cancel₀ _ (ne_of_gt hc)]
          exact h2)
      exact add_le_add (add_le_add (le_refl K) h3) (le_refl 1)
    have hchild := statopia_math_node_2171761119_a4c573e9 m n hm hn hnm r hr hrn
      p sigma K c Ks C_L CLam mu0 mu1 Lam th hp hp1 hsig hK hc hCLam hmu0 hmu01 hLam_le
      M0 U0 V0 d0 hM0 hU0 hV0 hd0 hlevU0 hlevV0 mask H M hbin hGood lamHat hnoise hlam1 hbulk
      hMmem w hw_nn hw0 hloss hrank C1 B hC1spec hC1_ge1 hBdef hbeta_le
    rw [hDltdef, hH0def, ← hspecM0]
    exact hchild
  have hd_op : frobNorm (M - M0) ≤ Real.sqrt (2 * (r : ℝ)) * Dlt := by
    have hmin : 0 < min m n := lt_min hm hn
    obtain ⟨hψtop, hψnn, hψanti, hψzero⟩ :=
      Statlib.HighDim.MatrixAnalysis.singular_value_properties (M - M0) (Or.inl ⟨⟨0, hm⟩⟩)
    have hψ0nn : 0 ≤ Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩ :=
      hψnn ⟨0, hmin⟩
    have hDlt : Dlt = Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩ := by
      rw [hDltdef, spectralNorm, dif_pos hmin]
    have hfnn : 0 ≤ frobNorm (M - M0) := by
      simp only [frobNorm, Statlib.HighDim.MatrixAnalysis.frobeniusNorm]
      positivity
    have hunf : frobNorm (M - M0) ^ 2 = ∑ i : Fin (min m n),
        Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i ^ 2 := by
      have hsum : frobNorm (M - M0) ^ 2 = ∑ i : Fin m, ∑ j : Fin n, (M - M0) i j ^ 2 := by
        simp only [frobNorm, Statlib.HighDim.MatrixAnalysis.frobeniusNorm]
        rw [Real.sq_sqrt (by positivity)]
      rw [hsum, (Statlib.HighDim.MatrixAnalysis.frobenius_norm_svd_relation (M - M0)).1]
    have hstep1 : ∑ i : Fin (min m n),
          Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i ^ 2
        ≤ Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩
          * ∑ i : Fin (min m n), Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hle : Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i
          ≤ Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩ :=
        hψanti (i := ⟨0, hmin⟩) (j := i) (by simp [Fin.le_def])
      calc Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i ^ 2
          = Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i
              * Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i := by ring
        _ ≤ Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩
              * Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i :=
            mul_le_mul_of_nonneg_right hle (hψnn i)
    have hnuc : Statlib.HighDim.Vocabulary.nuclearNorm (M - M0)
        = ∑ i : Fin (min m n), Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i := by
      simp [Statlib.HighDim.Vocabulary.nuclearNorm,
        Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary]
    have hnucle : Statlib.HighDim.Vocabulary.nuclearNorm (M - M0)
        ≤ Real.sqrt (2 * (r : ℝ)) * frobNorm (M - M0) :=
      Statlib.HighDim.MatrixRecovery.nuclearNorm_le_sqrt_two_mul_rank_mul_frobenius_of_rank_le
        (r := r) hrank
    have hCnn : (0:ℝ) ≤ Real.sqrt (2 * (r : ℝ)) *
        Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩ :=
      mul_nonneg (Real.sqrt_nonneg _) hψ0nn
    have hkey : frobNorm (M - M0) ^ 2
        ≤ Real.sqrt (2 * (r : ℝ)) * frobNorm (M - M0)
            * Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩ := by
      calc frobNorm (M - M0) ^ 2
          = ∑ i : Fin (min m n), Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i ^ 2 :=
            hunf
        _ ≤ Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩
              * ∑ i : Fin (min m n), Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) i :=
            hstep1
        _ = Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩
              * Statlib.HighDim.Vocabulary.nuclearNorm (M - M0) := by rw [hnuc]
        _ ≤ Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩
              * (Real.sqrt (2 * (r : ℝ)) * frobNorm (M - M0)) :=
            mul_le_mul_of_nonneg_left hnucle hψ0nn
        _ = Real.sqrt (2 * (r : ℝ)) * frobNorm (M - M0)
              * Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩ := by ring
    rw [hDlt]
    by_cases hzero : frobNorm (M - M0) = 0
    · rw [hzero]
      exact hCnn
    · have hfpos : 0 < frobNorm (M - M0) := lt_of_le_of_ne hfnn (Ne.symm hzero)
      by_contra hcon
      push_neg at hcon
      have hlt : Real.sqrt (2 * (r : ℝ)) *
            Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩
            * frobNorm (M - M0)
          < frobNorm (M - M0) * frobNorm (M - M0) :=
        mul_lt_mul_of_pos_right hcon hfpos
      have hkey' : frobNorm (M - M0) * frobNorm (M - M0)
          ≤ Real.sqrt (2 * (r : ℝ)) *
              Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩
              * frobNorm (M - M0) := by
        calc frobNorm (M - M0) * frobNorm (M - M0) = frobNorm (M - M0) ^ 2 := by ring
          _ ≤ Real.sqrt (2 * (r : ℝ)) * frobNorm (M - M0)
                * Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩ := hkey
          _ = Real.sqrt (2 * (r : ℝ)) *
                Statlib.HighDim.MatrixAnalysis.singularValues (M - M0) ⟨0, hmin⟩
                * frobNorm (M - M0) := by ring
      exact (not_lt_of_ge hkey') hlt
  have hDlt_nonneg : 0 ≤ Dlt := by
    rw [hDltdef, hspec_eq_opNorm]
    exact Statlib.HighDim.MatrixAnalysis.opNorm_nonneg _
  have hfrob_nonneg : 0 ≤ frobNorm (M - M0) := by
    simp only [frobNorm, Statlib.HighDim.MatrixAnalysis.frobeniusNorm]
    positivity
  have hsigHat := statopia_math_node_1461725421_1cd7d47b m n r hn hnm hr hrn p sigma K c
    hp hp1 hsig hK hc mask H M0 M hbin lamHat hrank hnoise hbulk
  have hsigHat_nn : 0 ≤ sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M := hsigHat.1
  have hsigHat_le :
      sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M * Real.sqrt ((m : ℝ) / p)
        ≤ c⁻¹ * (K * sigma * Real.sqrt ((m : ℝ) / p) +
            spectralNorm ((p : ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))) := hsigHat.2
  have hB_nonneg : 0 ≤ B := by
    rw [hBdef]
    refine div_nonneg ?_ (Real.sqrt_nonneg _)
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · exact le_trans zero_le_one hCLam
    · exact le_of_lt (lt_of_lt_of_le hmu0 (le_max_left _ _))
    · positivity
  by_cases hcase : H0 < s_1
  · have hpsi0 : ∀ (A : Matrix (Fin m) (Fin n) ℝ), psi hnm A ⟨0, hn⟩ = spectralNorm A := by
      intro A
      have hmin : 0 < min m n := lt_min hm hn
      simp only [psi, spectralNorm, dif_pos hmin]
      congr 1
    have hsmul : ∀ (x : ℝ) (A : Matrix (Fin m) (Fin n) ℝ),
        spectralNorm (x • A) = |x| * spectralNorm A := by
      intro x A
      rw [hspec_eq_opNorm, hspec_eq_opNorm, Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2,
        Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
      rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def, map_smul, norm_smul, Real.norm_eq_abs]
    set N : Matrix (Fin m) (Fin n) ℝ :=
      fun i j => (obsMatrix mask M0 H - projMask mask M) i j /
        (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M) with hNdef
    have hsigHat_ne : sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M ≠ 0 := by
      intro hz
      rw [normLoss, if_pos hz] at hloss
      exact absurd hloss (not_le.mpr (WithTop.coe_lt_top _))
    have hloss' : p⁻¹ * weightedLoss hnm w lamHat N ≤ C_L * w ⟨0, hn⟩ := by
      have h := hloss
      rw [normLoss, if_neg hsigHat_ne] at h
      rw [← hNdef] at h
      exact WithTop.coe_le_coe.mp h
    have hsingle : w ⟨0, hn⟩ * (psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2
        ≤ weightedLoss hnm w lamHat N := by
      simp only [weightedLoss]
      exact Finset.single_le_sum (f := fun i : Fin n => w i * (psi hnm N i - lamHat i) ^ 2)
        (fun i _ => mul_nonneg (hw_nn i) (sq_nonneg _)) (Finset.mem_univ _)
    have hsq_le : (psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2 ≤ p * C_L := by
      have hwne : w ⟨0, hn⟩ ≠ 0 := ne_of_gt hw0
      have h1 : p⁻¹ * (w ⟨0, hn⟩ * (psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2)
          ≤ p⁻¹ * weightedLoss hnm w lamHat N :=
        mul_le_mul_of_nonneg_left hsingle (inv_nonneg.mpr (le_of_lt hp))
      have h3 : p⁻¹ * (w ⟨0, hn⟩ * (psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2)
          ≤ C_L * w ⟨0, hn⟩ := le_trans h1 hloss'
      have h4 := mul_le_mul_of_nonneg_left h3 (le_of_lt hp)
      have h5 : w ⟨0, hn⟩ * (psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2
          ≤ p * C_L * w ⟨0, hn⟩ := by
        calc w ⟨0, hn⟩ * (psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2
            = p * (p⁻¹ * (w ⟨0, hn⟩ * (psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2)) := by
              rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp), one_mul]
          _ ≤ p * (C_L * w ⟨0, hn⟩) := h4
          _ = p * C_L * w ⟨0, hn⟩ := by ring
      have h6 := mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr (le_of_lt hw0))
      have e1 : (w ⟨0, hn⟩)⁻¹ * (w ⟨0, hn⟩ * (psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2)
          = (psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2 := by
        rw [← mul_assoc, inv_mul_cancel₀ hwne, one_mul]
      have e2 : (w ⟨0, hn⟩)⁻¹ * (p * C_L * w ⟨0, hn⟩) = p * C_L := by
        rw [mul_comm (p * C_L) (w ⟨0, hn⟩), ← mul_assoc, inv_mul_cancel₀ hwne, one_mul]
      rwa [e1, e2] at h6
    have hpsi_le : psi hnm N ⟨0, hn⟩ ≤ (K + Real.sqrt C_L) * Real.sqrt p := by
      have habs : |psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩| ≤ Real.sqrt (p * C_L) := by
        have h := Real.sqrt_le_sqrt hsq_le
        rwa [Real.sqrt_sq_eq_abs] at h
      have h1 : psi hnm N ⟨0, hn⟩ - lamHat ⟨0, hn⟩ ≤ Real.sqrt (p * C_L) :=
        le_trans (le_abs_self _) habs
      have h2 : psi hnm N ⟨0, hn⟩ ≤ lamHat ⟨0, hn⟩ + Real.sqrt (p * C_L) := by
        have h1' := add_le_add_left h1 (lamHat ⟨0, hn⟩)
        rw [sub_add_cancel] at h1'
        exact le_trans h1' (le_of_eq (add_comm (Real.sqrt (p * C_L)) (lamHat ⟨0, hn⟩)))
      have h3 : Real.sqrt (p * C_L) = Real.sqrt p * Real.sqrt C_L := by
        rw [Real.sqrt_mul (le_of_lt hp)]
      have h4 : lamHat ⟨0, hn⟩ + Real.sqrt (p * C_L)
          ≤ K * Real.sqrt p + Real.sqrt p * Real.sqrt C_L := by
        rw [h3]
        exact add_le_add hlam1 (le_refl _)
      have h5 : K * Real.sqrt p + Real.sqrt p * Real.sqrt C_L
          = (K + Real.sqrt C_L) * Real.sqrt p := by ring
      exact le_trans h2 (le_trans h4 (le_of_eq h5))
    have hc_s : (0:ℝ) < Real.sqrt (m : ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M :=
      mul_pos (Real.sqrt_pos.mpr hm_real) (lt_of_le_of_ne hsigHat_nn (Ne.symm hsigHat_ne))
    have hNsmul : N = (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)⁻¹ •
        (obsMatrix mask M0 H - projMask mask M) := by
      ext i j
      rw [hNdef]
      simp only [Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    have hEkey : (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M) • N
        = obsMatrix mask M0 H - projMask mask M := by
      rw [hNsmul, smul_smul, mul_inv_cancel₀ (ne_of_gt hc_s), one_smul]
    have hEM : spectralNorm (obsMatrix mask M0 H - projMask mask M)
        ≤ (K + Real.sqrt C_L) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
          * Real.sqrt ((m : ℝ) * p) := by
      have hNs : spectralNorm N ≤ (K + Real.sqrt C_L) * Real.sqrt p := by
        rw [← hpsi0 N]
        exact hpsi_le
      have hstep : spectralNorm (obsMatrix mask M0 H - projMask mask M)
          = (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)
              * spectralNorm N := by
        rw [← hEkey, hsmul, abs_of_pos hc_s]
      rw [hstep]
      have hle := mul_le_mul_of_nonneg_left hNs (le_of_lt hc_s)
      calc (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M) * spectralNorm N
          ≤ (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)
              * ((K + Real.sqrt C_L) * Real.sqrt p) := hle
        _ = (K + Real.sqrt C_L) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
              * Real.sqrt ((m : ℝ) * p) := by
            rw [Real.sqrt_mul (le_of_lt hm_real)]
            ring
    have htri : ∀ (A B : Matrix (Fin m) (Fin n) ℝ),
        spectralNorm (A - B) ≤ spectralNorm A + spectralNorm B := by
      intro A B
      have hmin : 0 < min m n := lt_min hm hn
      have hψtop : ∀ (X : Matrix (Fin m) (Fin n) ℝ),
          Statlib.HighDim.MatrixAnalysis.singularValues X ⟨0, hmin⟩ = spectralNorm X := by
        intro X
        rw [spectralNorm, dif_pos hmin]
      have hweyl := Statlib.HighDim.MatrixAnalysis.rectangular_singularValues_weyl_upper A
        ((-1 : ℝ) • B) ⟨0, hmin⟩
      rw [show A - B = A + (-1 : ℝ) • B by rw [sub_eq_add_neg, neg_one_smul]]
      calc spectralNorm (A + (-1 : ℝ) • B)
          = Statlib.HighDim.MatrixAnalysis.singularValues (A + (-1 : ℝ) • B) ⟨0, hmin⟩ :=
            (hψtop _).symm
        _ ≤ Statlib.HighDim.MatrixAnalysis.singularValues A ⟨0, hmin⟩
              + Statlib.HighDim.MatrixAnalysis.opNorm ((-1 : ℝ) • B) := hweyl
        _ = spectralNorm A + spectralNorm ((-1 : ℝ) • B) := by
              rw [hψtop A, ← hspec_eq_opNorm]
        _ = spectralNorm A + spectralNorm B := by
              rw [hsmul, abs_neg, abs_one, one_mul]
    have hPid : projMask mask (M - M0)
        = projMask mask H - (obsMatrix mask M0 H - projMask mask M) := by
      ext i j
      show mask i j * (M i j - M0 i j)
        = mask i j * H i j - (mask i j * (M0 i j + H i j) - mask i j * M i j)
      ring
    have hop : spectralNorm (projMask mask (M - M0))
        ≤ K' * (sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M + sigma)
          * Real.sqrt ((m : ℝ) * p) := by
      have hsnn : (0:ℝ) ≤ Real.sqrt ((m : ℝ) * p) := Real.sqrt_nonneg _
      have h1 : spectralNorm (projMask mask (M - M0))
          ≤ K * sigma * Real.sqrt ((m : ℝ) * p)
            + (K + Real.sqrt C_L) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
              * Real.sqrt ((m : ℝ) * p) := by
        rw [hPid]
        exact le_trans (htri _ _) (add_le_add hnoise hEM)
      have h2 : K * sigma * Real.sqrt ((m : ℝ) * p)
          ≤ K' * sigma * Real.sqrt ((m : ℝ) * p) := by
        have h := mul_le_mul_of_nonneg_right hK'_geK (mul_nonneg (le_of_lt hsig) hsnn)
        calc K * sigma * Real.sqrt ((m : ℝ) * p)
            = K * (sigma * Real.sqrt ((m : ℝ) * p)) := by ring
          _ ≤ K' * (sigma * Real.sqrt ((m : ℝ) * p)) := h
          _ = K' * sigma * Real.sqrt ((m : ℝ) * p) := by ring
      have h3 : (K + Real.sqrt C_L) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
              * Real.sqrt ((m : ℝ) * p)
          ≤ K' * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
              * Real.sqrt ((m : ℝ) * p) := by
        have h := mul_le_mul_of_nonneg_right hK'_geKC (mul_nonneg hsigHat_nn hsnn)
        calc (K + Real.sqrt C_L) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
                * Real.sqrt ((m : ℝ) * p)
            = (K + Real.sqrt C_L) * (sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
                * Real.sqrt ((m : ℝ) * p)) := by ring
          _ ≤ K' * (sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
                * Real.sqrt ((m : ℝ) * p)) := h
          _ = K' * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
                * Real.sqrt ((m : ℝ) * p) := by ring
      calc spectralNorm (projMask mask (M - M0))
          ≤ K * sigma * Real.sqrt ((m : ℝ) * p)
            + (K + Real.sqrt C_L) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
              * Real.sqrt ((m : ℝ) * p) := h1
        _ ≤ K' * sigma * Real.sqrt ((m : ℝ) * p)
            + K' * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
              * Real.sqrt ((m : ℝ) * p) := add_le_add h2 h3
        _ = K' * (sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M + sigma)
              * Real.sqrt ((m : ℝ) * p) := by ring
    have hscale' : sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
        ≤ sigma * (1 + K' / Real.log (m : ℝ))
          + K' * Real.sqrt ((frobNorm (projMask mask (M - M0))) ^ 2) /
              Real.sqrt ((m : ℝ) * (n : ℝ) * p) := by
      have hSpos : (0:ℝ) < Real.sqrt ((m:ℝ)*(n:ℝ)*p) := Real.sqrt_pos.mpr (by positivity)
      have hσne : sigma ≠ 0 := ne_of_gt hsig
      have hFnn : (0:ℝ) ≤ frobNorm (projMask mask (M - M0)) := by
        simp only [frobNorm, Statlib.HighDim.MatrixAnalysis.frobeniusNorm]
        positivity
      have h1 : sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M / sigma - 1
          ≤ Ks * (Real.log (m:ℝ))⁻¹ + Ks * frobNorm (projMask mask (M - M0)) /
              (sigma * Real.sqrt ((m:ℝ)*(n:ℝ)*p)) := le_trans (le_abs_self _) hscale
      have h2 : sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M / sigma
          ≤ 1 + (Ks * (Real.log (m:ℝ))⁻¹ + Ks * frobNorm (projMask mask (M - M0)) /
              (sigma * Real.sqrt ((m:ℝ)*(n:ℝ)*p))) := by
        linarith
      have h3 : sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
          ≤ (1 + (Ks * (Real.log (m:ℝ))⁻¹ + Ks * frobNorm (projMask mask (M - M0)) /
              (sigma * Real.sqrt ((m:ℝ)*(n:ℝ)*p)))) * sigma := (div_le_iff₀ hsig).mp h2
      have hkey : sigma * (Ks * frobNorm (projMask mask (M - M0)) /
            (sigma * Real.sqrt ((m:ℝ)*(n:ℝ)*p)))
          = Ks * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, _root_.mul_inv_rev]
        calc sigma * (Ks * frobNorm (projMask mask (M - M0))
              * ((Real.sqrt ((m:ℝ)*(n:ℝ)*p))⁻¹ * sigma⁻¹))
            = (sigma * sigma⁻¹) * (Ks * frobNorm (projMask mask (M - M0))
                * (Real.sqrt ((m:ℝ)*(n:ℝ)*p))⁻¹) := by ring
          _ = 1 * (Ks * frobNorm (projMask mask (M - M0))
                * (Real.sqrt ((m:ℝ)*(n:ℝ)*p))⁻¹) := by rw [mul_inv_cancel₀ hσne]
          _ = Ks * frobNorm (projMask mask (M - M0))
                * (Real.sqrt ((m:ℝ)*(n:ℝ)*p))⁻¹ := by rw [one_mul]
      have h4 : (1 + (Ks * (Real.log (m:ℝ))⁻¹ + Ks * frobNorm (projMask mask (M - M0)) /
            (sigma * Real.sqrt ((m:ℝ)*(n:ℝ)*p)))) * sigma
          = sigma + sigma * (Ks * (Real.log (m:ℝ))⁻¹)
            + sigma * (Ks * frobNorm (projMask mask (M - M0)) /
                (sigma * Real.sqrt ((m:ℝ)*(n:ℝ)*p))) := by ring
      have h5 : sigma + sigma * (Ks * (Real.log (m:ℝ))⁻¹)
            + sigma * (Ks * frobNorm (projMask mask (M - M0)) /
                (sigma * Real.sqrt ((m:ℝ)*(n:ℝ)*p)))
          = sigma + sigma * (Ks * (Real.log (m:ℝ))⁻¹)
            + Ks * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p) := by
        rw [hkey]
      have h6 : sigma + sigma * (Ks * (Real.log (m:ℝ))⁻¹)
            + Ks * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p)
          ≤ sigma + sigma * (K' * (Real.log (m:ℝ))⁻¹)
            + K' * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p) := by
        have hL1 : (0:ℝ) ≤ (Real.log (m:ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt hlog_pos)
        have hAs : sigma * Ks ≤ sigma * K' := mul_le_mul_of_nonneg_left hK'_geKs (le_of_lt hsig)
        have hA : sigma * (Ks * (Real.log (m:ℝ))⁻¹) ≤ sigma * (K' * (Real.log (m:ℝ))⁻¹) := by
          calc sigma * (Ks * (Real.log (m:ℝ))⁻¹) = (sigma * Ks) * (Real.log (m:ℝ))⁻¹ := by ring
            _ ≤ (sigma * K') * (Real.log (m:ℝ))⁻¹ := mul_le_mul_of_nonneg_right hAs hL1
            _ = sigma * (K' * (Real.log (m:ℝ))⁻¹) := by ring
        have hFS : (0:ℝ) ≤ frobNorm (projMask mask (M - M0)) /
            Real.sqrt ((m:ℝ)*(n:ℝ)*p) := div_nonneg hFnn (le_of_lt hSpos)
        have hB : Ks * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p)
            ≤ K' * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p) := by
          calc Ks * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p)
              = Ks * (frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p)) := by ring
            _ ≤ K' * (frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p)) :=
                mul_le_mul_of_nonneg_right hK'_geKs hFS
            _ = K' * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p) := by ring
        exact add_le_add (add_le_add (le_refl _) hA) hB
      have h7 : sigma + sigma * (K' * (Real.log (m:ℝ))⁻¹)
            + K' * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p)
          = sigma * (1 + K' / Real.log (m : ℝ))
            + K' * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p) := by
        rw [div_eq_mul_inv]
        ring
      have h8 : K' * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p)
          = K' * Real.sqrt ((frobNorm (projMask mask (M - M0))) ^ 2) /
              Real.sqrt ((m:ℝ)*(n:ℝ)*p) := by
        rw [Real.sqrt_sq hFnn]
      calc sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M
          ≤ (1 + (Ks * (Real.log (m:ℝ))⁻¹ + Ks * frobNorm (projMask mask (M - M0)) /
              (sigma * Real.sqrt ((m:ℝ)*(n:ℝ)*p)))) * sigma := h3
        _ = sigma + sigma * (Ks * (Real.log (m:ℝ))⁻¹)
              + sigma * (Ks * frobNorm (projMask mask (M - M0)) /
                  (sigma * Real.sqrt ((m:ℝ)*(n:ℝ)*p))) := h4
        _ = sigma + sigma * (Ks * (Real.log (m:ℝ))⁻¹)
              + Ks * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p) := h5
        _ ≤ sigma + sigma * (K' * (Real.log (m:ℝ))⁻¹)
              + K' * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p) := h6
        _ = sigma * (1 + K' / Real.log (m : ℝ))
              + K' * frobNorm (projMask mask (M - M0)) / Real.sqrt ((m:ℝ)*(n:ℝ)*p) := h7
        _ = sigma * (1 + K' / Real.log (m : ℝ))
              + K' * Real.sqrt ((frobNorm (projMask mask (M - M0))) ^ 2) /
                  Real.sqrt ((m:ℝ)*(n:ℝ)*p) := by rw [h8]
    have hQbound := statopia_math_node_3618029434_b97fb471 m n r hm hn hnm hr p sigma K'
      hp hp1 hsig hK'_ge1 hlog1 mask M0 M hbin hrank
      (sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M) hsigHat_nn hop hscale'
    clear hEM hNsmul hEkey htri hPid hop hscale' hsigHat_le hpsi0 hsmul hsigHat_nn hsigHat

    have hRSC : (p / 2) * (frobNorm (M - M0)) ^ 2
        ≤ (frobNorm (projMask mask (M - M0))) ^ 2 := by
      have hDltb : spectralNorm (M - M0)
          ≤ 2 * C1 * (sigma * Real.sqrt ((m:ℝ) / p)) + 4 * C1 * B * s_1 := by
        rw [← hDltdef, ← hH0def]
        exact hcoarse
      have hHard : sigma * Real.sqrt ((m:ℝ) / p) < s_1 := by
        rw [← hH0def]
        exact hcase
      exact statopia_math_node_201159926_475d9972 hm hn hnm hlog1 r hr hrn hlast
        p sigma mu0 mu1 Lam th CLam Cthet hp hp1 hsig hmu0 hmu01 hLam_le hth_le
        M0 U0 V0 d0 hM0 hU0 hV0 hd0 hd0_anti hlevU0 hlevV0 mask hbin hGood
        s_1 s_star kappa h_s_1 h_s_star h_s_star_pos h_kappa CsampE hCsampE_pos h_samp
        CM CCM C1 B hCM_def hC1_ge1 hCCM_pos hCCM_le hBdef hbeta_le M hMmem hHard hDltb
        hRSCax
    have hcoin : 10 * K' ^ 4 * ((r:ℝ)/(n:ℝ)) ≤ p / 4 := by
      have hstep1 : 10 * K' ^ 4 * (r:ℝ) ≤ (p / 4) * (n:ℝ) := by
        have h := mul_le_mul_of_nonneg_left hnp_big (by norm_num : (0:ℝ) ≤ 1/4)
        calc 10 * K' ^ 4 * (r:ℝ) = 1/4 * (40 * K' ^ 4 * (r:ℝ)) := by ring
          _ ≤ 1/4 * ((n:ℝ) * p) := h
          _ = (p / 4) * (n:ℝ) := by ring
      have hL : 10 * K' ^ 4 * ((r:ℝ)/(n:ℝ)) = (10 * K' ^ 4 * (r:ℝ)) / (n:ℝ) := by ring
      rw [hL]
      exact (div_le_iff₀ hn_real).mpr hstep1
    have hb2 : 10 * K' ^ 4 * (((r:ℝ)/(n:ℝ)) * (frobNorm (M - M0)) ^ 2)
        ≤ (p / 4) * (frobNorm (M - M0)) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hcoin (sq_nonneg (frobNorm (M - M0)))
      calc 10 * K' ^ 4 * (((r:ℝ)/(n:ℝ)) * (frobNorm (M - M0)) ^ 2)
          = (10 * K' ^ 4 * ((r:ℝ)/(n:ℝ))) * (frobNorm (M - M0)) ^ 2 := by ring
        _ ≤ (p / 4) * (frobNorm (M - M0)) ^ 2 := h
    have h4 : (p / 4) * (frobNorm (M - M0)) ^ 2
        ≤ 10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p) * frobNorm (M - M0)) := by
      have hcomb : (p / 2) * (frobNorm (M - M0)) ^ 2
          ≤ 10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p) * frobNorm (M - M0)
              + ((r:ℝ)/(n:ℝ)) * (frobNorm (M - M0)) ^ 2) := le_trans hRSC hQbound.2
      have hsplit : 10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p) * frobNorm (M - M0)
            + ((r:ℝ)/(n:ℝ)) * (frobNorm (M - M0)) ^ 2)
          = 10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p) * frobNorm (M - M0))
            + 10 * K' ^ 4 * (((r:ℝ)/(n:ℝ)) * (frobNorm (M - M0)) ^ 2) := by ring
      have hkey : (p / 4) * (frobNorm (M - M0)) ^ 2 + (p / 4) * (frobNorm (M - M0)) ^ 2
          ≤ 10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p) * frobNorm (M - M0))
            + (p / 4) * (frobNorm (M - M0)) ^ 2 := by
        calc (p / 4) * (frobNorm (M - M0)) ^ 2 + (p / 4) * (frobNorm (M - M0)) ^ 2
            = (p / 2) * (frobNorm (M - M0)) ^ 2 := by ring
          _ ≤ 10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p) * frobNorm (M - M0)
                + ((r:ℝ)/(n:ℝ)) * (frobNorm (M - M0)) ^ 2) := hcomb
          _ = 10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p) * frobNorm (M - M0))
                + 10 * K' ^ 4 * (((r:ℝ)/(n:ℝ)) * (frobNorm (M - M0)) ^ 2) := hsplit
          _ ≤ 10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p) * frobNorm (M - M0))
                + (p / 4) * (frobNorm (M - M0)) ^ 2 := add_le_add (le_refl _) hb2
      linarith [hkey]
    have hsqrt_p : Real.sqrt ((r:ℝ) * (m:ℝ) * p) = Real.sqrt ((m:ℝ) * (r:ℝ) / p) * p := by
      have hpnn : (0:ℝ) ≤ p := le_of_lt hp
      have h1 : Real.sqrt ((m:ℝ) * (r:ℝ) / p) * p
          = Real.sqrt ((m:ℝ) * (r:ℝ) / p) * Real.sqrt (p * p) := by
        rw [Real.sqrt_mul_self hpnn]
      rw [h1, ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ (m:ℝ) * (r:ℝ) / p)]
      congr 1
      have hpne : p ≠ 0 := ne_of_gt hp
      field_simp
    have hd_bound : frobNorm (M - M0)
        ≤ 40 * K' ^ 4 * sigma * Real.sqrt ((m:ℝ) * (r:ℝ) / p) := by
      rcases eq_or_lt_of_le hfrob_nonneg with hzero | hpos
      · rw [← hzero]
        exact mul_nonneg (mul_nonneg (le_of_lt h40) (le_of_lt hsig)) (Real.sqrt_nonneg _)
      · have h5 : (p / 4) * ((frobNorm (M - M0)) * (frobNorm (M - M0))) / (frobNorm (M - M0))
            ≤ 10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p)) := by
          refine (div_le_iff₀ hpos).mpr ?_
          calc (p / 4) * ((frobNorm (M - M0)) * (frobNorm (M - M0)))
              = (p / 4) * (frobNorm (M - M0)) ^ 2 := by ring
            _ ≤ 10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p) * frobNorm (M - M0)) := h4
            _ = (10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p)))
                  * frobNorm (M - M0) := by ring
        have hs : (p / 4) * ((frobNorm (M - M0)) * (frobNorm (M - M0))) / (frobNorm (M - M0))
            = (p / 4) * frobNorm (M - M0) := by
          rw [div_eq_mul_inv]
          calc (p / 4) * ((frobNorm (M - M0)) * (frobNorm (M - M0)))
                * (frobNorm (M - M0))⁻¹
              = (p / 4) * frobNorm (M - M0)
                  * (frobNorm (M - M0) * (frobNorm (M - M0))⁻¹) := by ring
            _ = (p / 4) * frobNorm (M - M0) * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hpos)]
            _ = (p / 4) * frobNorm (M - M0) := by ring
        rw [hs] at h5
        have hstep := mul_le_mul_of_nonneg_left h5
          (div_nonneg (by norm_num : (0:ℝ) ≤ 4) (le_of_lt hp))
        have hL : (4 / p) * ((p / 4) * frobNorm (M - M0)) = frobNorm (M - M0) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          calc (4 * p⁻¹) * (p * 4⁻¹ * frobNorm (M - M0))
              = (4 * 4⁻¹) * ((p * p⁻¹) * frobNorm (M - M0)) := by ring
            _ = 1 * (1 * frobNorm (M - M0)) := by
                rw [mul_inv_cancel₀ (ne_of_gt hp),
                  mul_inv_cancel₀ (by norm_num : (4:ℝ) ≠ 0)]
            _ = frobNorm (M - M0) := by ring
        have hR : (4 / p) * (10 * K' ^ 4 * (sigma * Real.sqrt ((r:ℝ) * (m:ℝ) * p)))
            = 40 * K' ^ 4 * sigma * Real.sqrt ((m:ℝ) * (r:ℝ) / p) := by
          rw [hsqrt_p]
          have hpne : p ≠ 0 := ne_of_gt hp
          field_simp
          ring
        rw [hL, hR] at hstep
        exact hstep
    have hfinal : frobNorm (M - M0)
        ≤ CerrE * sigma * Real.sqrt ((m:ℝ) * (r:ℝ) / p) := by
      have hSnn : (0:ℝ) ≤ sigma * Real.sqrt ((m:ℝ) * (r:ℝ) / p) :=
        mul_nonneg (le_of_lt hsig) (Real.sqrt_nonneg _)
      have hmul := mul_le_mul_of_nonneg_right h40_le_err hSnn
      calc frobNorm (M - M0)
          ≤ 40 * K' ^ 4 * sigma * Real.sqrt ((m:ℝ) * (r:ℝ) / p) := hd_bound
        _ = (40 * K' ^ 4) * (sigma * Real.sqrt ((m:ℝ) * (r:ℝ) / p)) := by ring
        _ ≤ CerrE * (sigma * Real.sqrt ((m:ℝ) * (r:ℝ) / p)) := hmul
        _ = CerrE * sigma * Real.sqrt ((m:ℝ) * (r:ℝ) / p) := by ring
    exact hfinal
  · push_neg at hcase
    have hH0C1 : H0 ≤ C1 * H0 := by
      have h := mul_le_mul_of_nonneg_right hC1_ge1 hH0_nonneg
      calc H0 = 1 * H0 := by ring
        _ ≤ C1 * H0 := h
    have hs1C1 : s_1 ≤ C1 * H0 := le_trans hcase hH0C1
    have h2 : Dlt ≤ 3 * C1 * H0 := by
      by_cases hs1 : 0 ≤ s_1
      · have h5 : 2 * (2 * C1 * B) ≤ 2 * (1 / 2) :=
          mul_le_mul_of_nonneg_left hbeta_le (by norm_num)
        have h6 : 2 * (2 * C1 * B) * s_1 ≤ 2 * (1 / 2) * s_1 :=
          mul_le_mul_of_nonneg_right h5 hs1
        have h4 : 4 * C1 * B * s_1 ≤ s_1 := by
          calc 4 * C1 * B * s_1 = 2 * (2 * C1 * B) * s_1 := by ring
            _ ≤ 2 * (1 / 2) * s_1 := h6
            _ = s_1 := by ring
        have h1 : Dlt ≤ 2 * C1 * H0 + s_1 := by
          have h4' : 4 * C1 * B * s_1 + 2 * C1 * H0 ≤ s_1 + 2 * C1 * H0 :=
            add_le_add_left h4 (2 * C1 * H0)
          calc Dlt ≤ 2 * C1 * H0 + 4 * C1 * B * s_1 := hcoarse
            _ = 4 * C1 * B * s_1 + 2 * C1 * H0 := by ring
            _ ≤ s_1 + 2 * C1 * H0 := h4'
            _ = 2 * C1 * H0 + s_1 := by ring
        have h3 : 2 * C1 * H0 + s_1 ≤ 2 * C1 * H0 + C1 * H0 := by
          have h3' : s_1 + 2 * C1 * H0 ≤ C1 * H0 + 2 * C1 * H0 :=
            add_le_add_left hs1C1 (2 * C1 * H0)
          calc 2 * C1 * H0 + s_1 = s_1 + 2 * C1 * H0 := by ring
            _ ≤ C1 * H0 + 2 * C1 * H0 := h3'
            _ = 2 * C1 * H0 + C1 * H0 := by ring
        have h7 : 2 * C1 * H0 + C1 * H0 = 3 * C1 * H0 := by ring
        exact le_trans h1 (le_trans h3 (le_of_eq h7))
      · push_neg at hs1
        have h45 : 0 ≤ 4 * C1 * B :=
          mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC1_pos)) hB_nonneg
        have h4 : 4 * C1 * B * s_1 ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos h45 (le_of_lt hs1)
        have h1 : Dlt ≤ 2 * C1 * H0 := by
          have h4'' : 4 * C1 * B * s_1 + 2 * C1 * H0 ≤ 0 + 2 * C1 * H0 :=
            add_le_add_left h4 (2 * C1 * H0)
          calc Dlt ≤ 2 * C1 * H0 + 4 * C1 * B * s_1 := hcoarse
            _ = 4 * C1 * B * s_1 + 2 * C1 * H0 := by ring
            _ ≤ 0 + 2 * C1 * H0 := h4''
            _ = 2 * C1 * H0 := by ring
        have hC1H0 : 0 ≤ C1 * H0 := mul_nonneg (le_of_lt hC1_pos) hH0_nonneg
        have h3 : 2 * C1 * H0 ≤ 3 * C1 * H0 := by
          calc 2 * C1 * H0 ≤ 2 * C1 * H0 + C1 * H0 := le_add_of_nonneg_right hC1H0
            _ = 3 * C1 * H0 := by ring
        exact le_trans h1 h3
    have h6 : Real.sqrt (2 * (r : ℝ)) * Real.sqrt ((m : ℝ) / p)
        = Real.sqrt 2 * Real.sqrt ((m : ℝ) * (r : ℝ) / p) := by
      have hr2 : Real.sqrt (2 * (r : ℝ)) = Real.sqrt 2 * Real.sqrt (r : ℝ) := by
        rw [Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num)]
      have hrm : Real.sqrt ((r : ℝ) * ((m : ℝ) / p))
          = Real.sqrt ((m : ℝ) * (r : ℝ) / p) := by
        congr 1
        rw [mul_comm (m : ℝ) (r : ℝ), mul_div_assoc]
      rw [hr2, mul_assoc, ← Real.sqrt_mul (show (0:ℝ) ≤ (r : ℝ) by positivity), hrm]
    have hb : frobNorm (M - M0) ≤ Real.sqrt (2 * (r : ℝ)) * (3 * C1 * H0) := by
      have h5 : Real.sqrt (2 * (r : ℝ)) * Dlt
          ≤ Real.sqrt (2 * (r : ℝ)) * (3 * C1 * H0) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      exact le_trans hd_op h5
    have hfin : frobNorm (M - M0) ≤
        3 * Real.sqrt 2 * C1 * (sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p)) := by
      calc frobNorm (M - M0)
          ≤ Real.sqrt (2 * (r : ℝ)) * (3 * C1 * H0) := hb
        _ = 3 * C1 * (Real.sqrt (2 * (r : ℝ)) * Real.sqrt ((m : ℝ) / p)) * sigma := by
            rw [hH0def]; ring
        _ = 3 * C1 * (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (r : ℝ) / p)) * sigma := by rw [h6]
        _ = 3 * Real.sqrt 2 * C1 * (sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p)) := by ring
    have hnine : 3 * Real.sqrt 2 * C1 * (sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p))
        ≤ CerrE * sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p) := by
      have hSnn : (0:ℝ) ≤ sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p) :=
        mul_nonneg (le_of_lt hsig) (Real.sqrt_nonneg _)
      have h5 := mul_le_mul_of_nonneg_right hC3_le_err hSnn
      calc 3 * Real.sqrt 2 * C1 * (sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p))
          = (3 * Real.sqrt 2 * C1) * (sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p)) := by ring
        _ ≤ CerrE * (sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p)) := h5
        _ = CerrE * sigma * Real.sqrt ((m : ℝ) * (r : ℝ) / p) := by ring
    exact le_trans hfin hnine
  /- @proof-region region.target-node.session.e3a9352899725178 end -/

end Statlib.Imported

