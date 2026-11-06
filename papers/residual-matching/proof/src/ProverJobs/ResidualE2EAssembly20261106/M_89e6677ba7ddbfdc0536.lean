import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548
import ProverJobs.ResidualE2EAssembly20261106.M_3b7837ec897a8f11f4d4
import ProverJobs.ResidualE2EAssembly20261106.M_eeb0c48628f53be1e6d9

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching


run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal
open scoped Matrix.Norms.L2Operator

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
theorem statopia_math_node_81579216_84cc7772 : ∀ {m n r : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hnm : n ≤ m) (hr : 0 < r) (hlast : r - 1 < n)
    (p sigma mu0 mu1 CM CCM C1 B s_1 s_star kappa CsampE : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hsig : 0 < sigma) (hmu0 : 0 < mu0) (hmu01 : mu0 ≤ mu1)
    (hlog1 : 1 ≤ Real.log (m : ℝ))
    (M0 : Matrix (Fin m) (Fin n) ℝ) (U0 : Matrix (Fin m) (Fin r) ℝ)
    (V0 : Matrix (Fin n) (Fin r) ℝ) (d0 : Fin r → ℝ)
    (hM0 : M0 = U0 * Matrix.diagonal d0 * Matrix.transpose V0)
    (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
    (hd0 : ∀ i : Fin r, 0 < d0 i) (hd0_anti : Antitone d0)
    (h_s_1 : s_1 = psi hnm M0 ⟨0, hn⟩)
    (h_s_star : s_star = psi hnm M0 ⟨r - 1, hlast⟩)
    (hs_star_pos : 0 < s_star) (hkappa : kappa = s_1 / s_star)
    (h_samp : CsampE * kappa ^ 2 * (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)
        + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) ≤ (n : ℝ) * p)
    (hCMdef : CM = 1 + 3 * C1) (hC1_ge1 : 1 ≤ C1)
    (hCCM_pos : 0 < CCM) (hCCM_le : CCM ≤ CsampE)
    (hBeta : 2 * C1 * B ≤ 1 / 2)
    (hHard : sigma * Real.sqrt ((m : ℝ) / p) < s_1)
    (M : Matrix (Fin m) (Fin n) ℝ)
    (hDltb : spectralNorm (M - M0)
        ≤ 2 * C1 * (sigma * Real.sqrt ((m : ℝ) / p)) + 4 * C1 * B * s_1),
    PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.npCondition
        CCM mu0 mu1 d0 p m n ∧
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.spectralNorm M
        ≤ CM * PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.SMax d0 := by
  /- @proof-region region.target-node.session.92ff7cbf53fb5ee8 begin -/
  intro m n r hm hn hnm hr hlast p sigma mu0 mu1 CM CCM C1 B s_1 s_star kappa CsampE
    hp hp1 hsig hmu0 hmu01 hlog1 M0 U0 V0 d0 hM0 hU0 hV0 hd0 hd0_anti h_s_1 h_s_star hs_star_pos
    hkappa h_samp hCMdef hC1_ge1 hCCM_pos hCCM_le hBeta hHard M hDltb
  have hmin : 0 < min m n := Nat.lt_min.mpr ⟨hm, hn⟩
  have hrmin : r - 1 < min m n := Nat.lt_min.mpr ⟨by omega, hlast⟩
  have hsv1 : s_1 = Statlib.HighDim.MatrixAnalysis.singularValues M0 ⟨0, hmin⟩ := by
    rw [h_s_1]
    have hidx : (Fin.cast (Nat.min_eq_right hnm).symm ⟨0, hn⟩ : Fin (min m n))
        = ⟨0, hmin⟩ := Fin.ext rfl
    simp only [psi]
    rw [hidx]
  have hsvstar : s_star = Statlib.HighDim.MatrixAnalysis.singularValues M0 ⟨r - 1, hrmin⟩ := by
    rw [h_s_star]
    have hidx : (Fin.cast (Nat.min_eq_right hnm).symm ⟨r - 1, hlast⟩ : Fin (min m n))
        = ⟨r - 1, hrmin⟩ := Fin.ext rfl
    simp only [psi]
    rw [hidx]
  have hs_star_le_s1 : s_star ≤ s_1 := by
    rw [hsvstar, hsv1]
    exact Statlib.HighDim.MatrixAnalysis.singularValues_antitone M0 (by simp)
  have hs1pos : 0 < s_1 := lt_of_lt_of_le hs_star_pos hs_star_le_s1
  have hsv_opNorm : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      Statlib.HighDim.MatrixAnalysis.singularValues A ⟨0, hmin⟩
        = Statlib.HighDim.MatrixAnalysis.opNorm A := by
    intro A
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 A]
    exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties A (Or.inl ⟨⟨0, hm⟩⟩)).1 hmin
  have hspecNorm_sv : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      spectralNorm A = Statlib.HighDim.MatrixAnalysis.singularValues A ⟨0, hmin⟩ := by
    intro A
    unfold spectralNorm
    rw [dif_pos hmin]
  have hspec_eq : ∀ A : Matrix (Fin m) (Fin n) ℝ, spectralNorm A = ‖A‖ := by
    intro A
    rw [hspecNorm_sv A, hsv_opNorm A, Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 A]
  have hM0norm : ‖M0‖ = s_1 := by
    rw [← Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 M0, ← hsv_opNorm M0, ← hsv1]
  have hcol : ∀ j : Fin r, d0 j ≤ ‖M0‖ := by
    have hnormE_n : ∀ y : Fin n → ℝ,
        ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ = Real.sqrt (∑ i, (y i) ^ 2) := by
      intro y
      rw [EuclideanSpace.norm_eq]
      have hy : ((EuclideanSpace.equiv (Fin n) ℝ).symm y).ofLp = y := rfl
      rw [hy]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
    have hnormE_m : ∀ y : Fin m → ℝ,
        ‖(EuclideanSpace.equiv (Fin m) ℝ).symm y‖ = Real.sqrt (∑ a, (y a) ^ 2) := by
      intro y
      rw [EuclideanSpace.norm_eq]
      have hy : ((EuclideanSpace.equiv (Fin m) ℝ).symm y).ofLp = y := rfl
      rw [hy]
      congr 1
      exact Finset.sum_congr rfl (fun a _ => by rw [Real.norm_eq_abs, sq_abs])
    intro j
    have hVsum : ∑ i, (V0 i j) ^ 2 = 1 := by
      have h := congrFun (congrFun hV0 j) j
      simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
    have hUsum : ∑ a, (U0 a j) ^ 2 = 1 := by
      have h := congrFun (congrFun hU0 j) j
      simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
    have hyof : ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => V0 i j)).ofLp
        = fun i => V0 i j := rfl
    have hynorm : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => V0 i j)‖ = 1 := by
      rw [hnormE_n]
      rw [show (∑ i, ((fun i => V0 i j) i) ^ 2) = 1 from hVsum, Real.sqrt_one]
    have hmv : M0.mulVec (fun i => V0 i j) = fun a => d0 j * U0 a j := by
      rw [hM0, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      funext a
      have hVt : (Matrix.transpose V0).mulVec (fun i => V0 i j)
          = fun k => (1 : Matrix (Fin r) (Fin r) ℝ) k j := by
        funext k
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        rw [← hV0]
        simp [Matrix.mul_apply]
      rw [hVt]
      have hdiag : (Matrix.diagonal d0).mulVec (fun k => (1 : Matrix (Fin r) (Fin r) ℝ) k j)
          = fun k => if k = j then d0 k else 0 := by
        funext k
        rw [Matrix.mulVec_diagonal, Matrix.one_apply]
        by_cases hk : k = j
        · rw [if_pos hk, if_pos hk, mul_one]
        · rw [if_neg hk, if_neg hk, mul_zero]
      rw [hdiag]
      show ∑ x, U0 a x * (if x = j then d0 x else 0) = d0 j * U0 a j
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl]; ring
      · intro b _ hb
        rw [if_neg hb, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have hlhs : ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (M0.mulVec (fun i => V0 i j))‖ = d0 j := by
      rw [hmv, hnormE_m]
      have hs : ∑ a, ((fun a => d0 j * U0 a j) a) ^ 2 = d0 j ^ 2 := by
        have h2 : ∑ a, ((fun a => d0 j * U0 a j) a) ^ 2
            = d0 j ^ 2 * ∑ a, (U0 a j) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun a _ => by ring)
        rw [h2, hUsum, mul_one]
      rw [hs, Real.sqrt_sq (le_of_lt (hd0 j))]
    have hmain := Matrix.l2_opNorm_mulVec M0 ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => V0 i j))
    rw [hyof] at hmain
    rw [hynorm, mul_one] at hmain
    rw [hlhs] at hmain
    exact hmain
  have hrow : ‖M0‖ ≤ d0 ⟨0, hr⟩ := by
    haveI hne : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    haveI hnz : NeZero r := ⟨by omega⟩
    have hd0nn : 0 ≤ d0 ⟨0, hr⟩ := le_of_lt (hd0 ⟨0, hr⟩)
    have hconjU : Matrix.conjTranspose U0 = Matrix.transpose U0 := by
      ext i j
      simp [Matrix.conjTranspose]
    have hU1 : ‖U0‖ ≤ 1 := by
      have h0 : 0 ≤ ‖U0‖ := norm_nonneg U0
      have h1 : ‖U0‖ * ‖U0‖ = 1 := by
        have h := Matrix.l2_opNorm_conjTranspose_mul_self U0
        rw [hconjU, hU0, CStarRing.norm_one] at h
        exact h.symm
      rcases le_total ‖U0‖ 1 with hle | hle
      · exact hle
      · calc ‖U0‖ = ‖U0‖ * 1 := (mul_one _).symm
          _ ≤ ‖U0‖ * ‖U0‖ := mul_le_mul_of_nonneg_left hle h0
          _ = 1 := h1
    have hconjV : Matrix.conjTranspose V0 = Matrix.transpose V0 := by
      ext i j
      simp [Matrix.conjTranspose]
    have hV1 : ‖Matrix.transpose V0‖ ≤ 1 := by
      have h0 : 0 ≤ ‖V0‖ := norm_nonneg V0
      have h1 : ‖V0‖ * ‖V0‖ = 1 := by
        have h := Matrix.l2_opNorm_conjTranspose_mul_self V0
        rw [hconjV, hV0, CStarRing.norm_one] at h
        exact h.symm
      have hVle : ‖V0‖ ≤ 1 := by
        rcases le_total ‖V0‖ 1 with hle | hle
        · exact hle
        · calc ‖V0‖ = ‖V0‖ * 1 := (mul_one _).symm
            _ ≤ ‖V0‖ * ‖V0‖ := mul_le_mul_of_nonneg_left hle h0
            _ = 1 := h1
      rw [← hconjV, Matrix.l2_opNorm_conjTranspose]
      exact hVle
    have hD : ‖Matrix.diagonal d0‖ ≤ d0 ⟨0, hr⟩ := by
      rw [Matrix.l2_opNorm_def]
      refine ContinuousLinearMap.opNorm_le_bound _ hd0nn (fun x => ?_)
      change ‖(Matrix.toEuclideanLin (Matrix.diagonal d0)) x‖ ≤ d0 ⟨0, hr⟩ * ‖x‖
      set y : EuclideanSpace ℝ (Fin r) := (Matrix.toEuclideanLin (Matrix.diagonal d0)) x with hy
      have hyof : y.ofLp = fun i => d0 i * x.ofLp i := by
        rw [hy, Matrix.ofLp_toEuclideanLin_apply]
        funext i
        rw [Matrix.mulVec_diagonal]
      have hy2 : ‖y‖ ^ 2 = ∑ i, (d0 i * x.ofLp i) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, hyof]
        exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
      have hx2 : ‖x‖ ^ 2 = ∑ i, (x.ofLp i) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
      have hle : ∑ i, (d0 i * x.ofLp i) ^ 2 ≤ (d0 ⟨0, hr⟩) ^ 2 * ∑ i, (x.ofLp i) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hi1 : d0 i ≤ d0 ⟨0, hr⟩ := hd0_anti (Nat.zero_le i.val)
        have hi2 : 0 ≤ d0 i := le_of_lt (hd0 i)
        have hi3 : d0 i ^ 2 ≤ d0 ⟨0, hr⟩ ^ 2 := by
          calc d0 i ^ 2 = d0 i * d0 i := sq _
            _ ≤ d0 ⟨0, hr⟩ * d0 ⟨0, hr⟩ := mul_le_mul hi1 hi1 hi2 (le_trans hi2 hi1)
            _ = d0 ⟨0, hr⟩ ^ 2 := (sq _).symm
        calc (d0 i * x.ofLp i) ^ 2 = d0 i ^ 2 * (x.ofLp i) ^ 2 := by ring
          _ ≤ d0 ⟨0, hr⟩ ^ 2 * (x.ofLp i) ^ 2 := mul_le_mul_of_nonneg_right hi3 (sq_nonneg _)
      have hsq : ‖y‖ ^ 2 ≤ (d0 ⟨0, hr⟩ * ‖x‖) ^ 2 := by
        rw [hy2, mul_pow, hx2]
        exact hle
      calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg y)).symm
        _ ≤ Real.sqrt ((d0 ⟨0, hr⟩ * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = d0 ⟨0, hr⟩ * ‖x‖ := Real.sqrt_sq (mul_nonneg hd0nn (norm_nonneg x))
    have h1 : ‖U0 * Matrix.diagonal d0‖ ≤ 1 * d0 ⟨0, hr⟩ :=
      (Matrix.l2_opNorm_mul U0 (Matrix.diagonal d0)).trans
        (mul_le_mul hU1 hD (norm_nonneg (Matrix.diagonal d0)) zero_le_one)
    have h2 : ‖U0 * Matrix.diagonal d0‖ * ‖Matrix.transpose V0‖ ≤ (1 * d0 ⟨0, hr⟩) * 1 :=
      mul_le_mul h1 hV1 (norm_nonneg (Matrix.transpose V0)) (by rw [one_mul]; exact hd0nn)
    calc ‖M0‖ = ‖U0 * Matrix.diagonal d0 * Matrix.transpose V0‖ := by rw [hM0]
      _ ≤ ‖U0 * Matrix.diagonal d0‖ * ‖Matrix.transpose V0‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (1 * d0 ⟨0, hr⟩) * 1 := h2
      _ = d0 ⟨0, hr⟩ := by ring
  have hsup_le : (⨆ i, d0 i) ≤ s_1 :=
    Real.iSup_le (fun i => (hcol i).trans hM0norm.le) (le_of_lt hs1pos)
  have hsup_ge : s_1 ≤ ⨆ i, d0 i := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hbdd : BddAbove (Set.range d0) :=
      ⟨‖M0‖, by rintro _ ⟨i, rfl⟩; exact hcol i⟩
    have hle : d0 ⟨0, hr⟩ ≤ ⨆ i, d0 i := le_ciSup (f := d0) hbdd ⟨0, hr⟩
    rw [← hM0norm]
    exact hrow.trans hle
  have hSMin_ge : s_star ≤ ⨅ i, d0 i := by
    have hrn : r ≤ n := by omega
    have hchild := statopia_math_node_919610516_79178f41 hr hrn hnm M0 U0 V0 d0 hM0 hU0 hV0 hd0 hrmin
    rw [hsvstar]
    exact hchild
  have hSMin_pos : 0 < ⨅ i, d0 i := lt_of_lt_of_le hs_star_pos hSMin_ge
  have hbr_nonneg : 0 ≤ max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)
      + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 := by
    have hmu : 0 < max mu0 mu1 := lt_of_lt_of_le hmu0 (le_max_left _ _)
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    have hlog : 0 < Real.log (m : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
    have h1 : 0 < max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) :=
      mul_pos (mul_pos hmu hrpos) hlog
    have h2 : 0 ≤ (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 :=
      le_of_lt (mul_pos (pow_pos hmu 2) (pow_pos hrpos 2))
    linarith
  refine ⟨?_, ?_⟩
  · unfold PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.npCondition
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.kappaOf
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.barMuOf
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.SMax
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.SMin
    set K : ℝ := (⨆ i, d0 i) / (⨅ i, d0 i) with hKdef
    set br : ℝ := max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)
      + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2 with hbrdef
    have hKle : K ≤ kappa := by
      rw [hKdef, hkappa]
      calc (⨆ i, d0 i) / (⨅ i, d0 i) ≤ s_1 / (⨅ i, d0 i) :=
            (div_le_div_iff_of_pos_right hSMin_pos).mpr hsup_le
        _ ≤ s_1 / s_star :=
            (div_le_div_iff_of_pos_left hs1pos hSMin_pos hs_star_pos).mpr hSMin_ge
    have hKnn : 0 ≤ K := by
      rw [hKdef]
      exact div_nonneg (le_trans (le_of_lt hs1pos) hsup_ge) (le_of_lt hSMin_pos)
    have hK2 : K ^ 2 ≤ kappa ^ 2 := by
      have hkk : K * K ≤ kappa * kappa :=
        mul_le_mul hKle hKle hKnn (le_trans hKnn hKle)
      calc K ^ 2 = K * K := sq K
        _ ≤ kappa * kappa := hkk
        _ = kappa ^ 2 := (sq kappa).symm
    have hCsampE_pos : 0 < CsampE := lt_of_lt_of_le hCCM_pos hCCM_le
    have hstep1 : CCM * K ^ 2 * br ≤ CsampE * K ^ 2 * br := by
      apply mul_le_mul_of_nonneg_right _ hbr_nonneg
      exact mul_le_mul_of_nonneg_right hCCM_le (sq_nonneg K)
    have hstep2 : CsampE * K ^ 2 * br ≤ CsampE * kappa ^ 2 * br := by
      apply mul_le_mul_of_nonneg_right _ hbr_nonneg
      exact mul_le_mul_of_nonneg_left hK2 (le_of_lt hCsampE_pos)
    exact hstep1.trans (hstep2.trans h_samp)
  · unfold PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.spectralNorm
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 M]
    have hSMax_eq : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.SMax d0
        = s_1 := by
      show (⨆ i : Fin r, d0 i) = s_1
      exact le_antisymm hsup_le hsup_ge
    rw [hSMax_eq]
    have hdle : ‖M - M0‖ ≤ 2 * C1 * (sigma * Real.sqrt ((m : ℝ) / p)) + 4 * C1 * B * s_1 := by
      rw [← hspec_eq (M - M0)]
      exact hDltb
    have htri : ‖M‖ ≤ ‖M0‖ + ‖M - M0‖ := by
      have heq : M = M0 + (M - M0) := by abel
      calc ‖M‖ = ‖M0 + (M - M0)‖ := congrArg (fun A => ‖A‖) heq
        _ ≤ ‖M0‖ + ‖M - M0‖ := norm_add_le _ _

    have hC1nn : 0 ≤ C1 := le_trans zero_le_one hC1_ge1
    have h2C1 : (0 : ℝ) ≤ 2 * C1 := mul_nonneg (by norm_num) hC1nn
    have hterm1 : 2 * C1 * (sigma * Real.sqrt ((m : ℝ) / p)) ≤ 2 * C1 * s_1 :=
      mul_le_mul_of_nonneg_left (le_of_lt hHard) h2C1
    have h4 : 4 * C1 * B ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hBeta (by norm_num : (0 : ℝ) ≤ 2)
      have he : (2 : ℝ) * (2 * C1 * B) = 4 * C1 * B := by ring
      rw [he, show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h
      exact h
    have hterm2 : 4 * C1 * B * s_1 ≤ s_1 :=
      (mul_le_mul_of_nonneg_right h4 (le_of_lt hs1pos)).trans (one_mul s_1).le
    have h3 : ‖M0‖ + ‖M - M0‖ ≤ s_1 + (2 * C1 * s_1 + s_1) := by
      have hd' : ‖M - M0‖ ≤ 2 * C1 * s_1 + s_1 := hdle.trans (add_le_add hterm1 hterm2)
      rw [hM0norm]
      exact add_le_add le_rfl hd'
    have hbound : ‖M‖ ≤ 2 * C1 * s_1 + 2 * s_1 := by
      have hs3 : s_1 + (2 * C1 * s_1 + s_1) = 2 * C1 * s_1 + 2 * s_1 := by ring
      exact htri.trans (h3.trans hs3.le)
    have hCs1 : s_1 ≤ C1 * s_1 := by
      have h := mul_le_mul_of_nonneg_right hC1_ge1 (le_of_lt hs1pos)
      rwa [one_mul] at h
    have hCM : CM * s_1 = s_1 + 3 * C1 * s_1 := by
      rw [hCMdef]; ring
    calc ‖M‖ ≤ 2 * C1 * s_1 + 2 * s_1 := hbound
      _ ≤ CM * s_1 := by
          rw [hCM]
          have hsum : 2 * s_1 ≤ C1 * s_1 + s_1 := by
            rw [two_mul]
            exact add_le_add hCs1 le_rfl
          have hstep : 2 * C1 * s_1 + 2 * s_1 ≤ 2 * C1 * s_1 + (C1 * s_1 + s_1) :=
            add_le_add le_rfl hsum
          have heq : 2 * C1 * s_1 + (C1 * s_1 + s_1) = s_1 + 3 * C1 * s_1 := by ring
          exact hstep.trans heq.le
  /- @proof-region region.target-node.session.92ff7cbf53fb5ee8 end -/

end Statlib.Imported

