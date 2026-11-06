import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_290215883_e35c90a8 : ∀ (m n r : ℕ) (hm : 0 < m) (hn : 0 < n) (hr : 1 ≤ r)
    (sig : Fin r → ℝ) (hSigNonneg : ∀ t, 0 ≤ sig t)
    (mu1 mubar : ℝ) (hmu1 : mu1 ≤ mubar) (hmubar : 0 ≤ mubar)
    (CM : ℝ) (hCM : 1 ≤ CM)
    (M : Matrix (Fin m) (Fin n) ℝ)
    (hMclass : InLowRankClass r mu1 M)
    (hMnorm : spectralNorm M ≤ CM * SMax sig),
    ∃ X : Matrix (Fin m) (Fin r) ℝ, ∃ Y : Matrix (Fin n) (Fin r) ℝ,
      M = X * Matrix.transpose Y ∧
      Matrix.transpose X * X = Matrix.transpose Y * Y ∧
      spectralNorm X = Real.sqrt (spectralNorm M) ∧
      spectralNorm Y = Real.sqrt (spectralNorm M) ∧
      twoInfNorm X ≤ Real.sqrt (CM * SMax sig) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) ∧
      twoInfNorm Y ≤ Real.sqrt (CM * SMax sig) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)) := by
  /- @proof-region region.target-node.session.eee8505d00334385 begin -/
  intro m n r hm hn hr sig hSigNonneg mu1 mubar hmu1 hmubar CM hCM M hMclass hMnorm
  have norm_transpose : ∀ (a b : ℕ) (A : Matrix (Fin a) (Fin b) ℝ),
      ‖Matrix.transpose A‖ = ‖A‖ := by
    intro a b A
    have h := Statlib.HighDim.MatrixAnalysis.opNorm_transpose A
    rwa [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2,
      Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2] at h
  have isometry : ∀ (a b c : ℕ) (W : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin c) ℝ),
      Matrix.transpose W * W = 1 → ‖W * B‖ = ‖B‖ := by
    intro a b c W B hW
    have hconj : W.conjTranspose * W = 1 := by simpa using hW
    have hsq : ‖W * B‖ * ‖W * B‖ = ‖B‖ * ‖B‖ := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self (W * B),
        ← Matrix.l2_opNorm_conjTranspose_mul_self B]
      congr 1
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc B.conjTranspose W.conjTranspose (W * B),
        ← Matrix.mul_assoc W.conjTranspose W B, hconj, Matrix.one_mul]
    calc ‖W * B‖ = Real.sqrt (‖W * B‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖W * B‖ * ‖W * B‖) := by rw [pow_two]
      _ = Real.sqrt (‖B‖ * ‖B‖) := by rw [hsq]
      _ = Real.sqrt (‖B‖ ^ 2) := by rw [pow_two]
      _ = ‖B‖ := Real.sqrt_sq (norm_nonneg B)
  rcases hMclass with hM0 | ⟨k, U, V, s, hk1, hkr, hU, hV, hMUV, hbU, hbV⟩
  · subst hM0
    refine ⟨0, 0, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · simp [spectralNorm, Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    · simp [spectralNorm, Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      have h0 : twoInfNorm (0 : Matrix (Fin m) (Fin r) ℝ) = 0 := by simp [twoInfNorm]
      rw [h0]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      have h0 : twoInfNorm (0 : Matrix (Fin n) (Fin r) ℝ) = 0 := by simp [twoInfNorm]
      rw [h0]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · classical
    have isometry_right : ∀ (a b c : ℕ) (B : Matrix (Fin a) (Fin b) ℝ) (W : Matrix (Fin c) (Fin b) ℝ),
        Matrix.transpose W * W = 1 → ‖B * Matrix.transpose W‖ = ‖B‖ := by
      intro a b c B W hW
      rw [← norm_transpose a c (B * Matrix.transpose W), Matrix.transpose_mul,
        Matrix.transpose_transpose]
      rw [isometry c b a W (Matrix.transpose B) hW, norm_transpose a b B]
    set P : Matrix (Fin k) (Fin r) ℝ := fun t j => if j = Fin.castLE hkr t then 1 else 0 with hP
    set e : Fin k → ℝ := fun t => if s t < 0 then -Real.sqrt |s t| else Real.sqrt |s t| with he
    set ff : Fin k → ℝ := fun t => Real.sqrt |s t| with hff
    set X : Matrix (Fin m) (Fin r) ℝ := U * Matrix.diagonal e * P with hX
    set Y : Matrix (Fin n) (Fin r) ℝ := V * Matrix.diagonal ff * P with hY
    have diagT : ∀ (d : Fin k → ℝ), Matrix.transpose (Matrix.diagonal d) = Matrix.diagonal d := by
      intro d
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.transpose_apply, Matrix.diagonal]
      · simp [Matrix.transpose_apply, Matrix.diagonal, h, Ne.symm h]
    have hPPt : P * Matrix.transpose P = 1 := by
      ext t t'
      rw [Matrix.mul_apply, Matrix.one_apply]
      show ∑ j : Fin r, P t j * P t' j = if t = t' then 1 else 0
      have key : ∀ j : Fin r, j ≠ Fin.castLE hkr t → P t j * P t' j = 0 := by
        intro j hj
        have h1 : P t j = 0 := by
          simp only [hP]
          exact if_neg hj
        rw [h1, zero_mul]
      rw [Finset.sum_eq_single (Fin.castLE hkr t) (fun j _ hj => key j hj)
        (by intro h; exact absurd (Finset.mem_univ _) h)]
      simp only [hP]
      by_cases htt : t = t'
      · subst htt; simp
      · have hne : Fin.castLE hkr t ≠ Fin.castLE hkr t' := fun h => htt (Fin.castLE_injective hkr h)
        simp [hne, htt]
    have hee : ∀ t, e t * ff t = s t := by
      intro t
      simp only [he, hff]
      by_cases h : s t < 0
      · have h1 : |s t| = -s t := abs_of_neg h
        have h2 : Real.sqrt |s t| ^ 2 = |s t| := Real.sq_sqrt (abs_nonneg (s t))
        simp only [if_pos h]
        nlinarith [Real.sqrt_nonneg |s t|]
      · have h0 : 0 ≤ s t := not_lt.mp h
        have h1 : |s t| = s t := abs_of_nonneg h0
        have h2 : Real.sqrt |s t| ^ 2 = |s t| := Real.sq_sqrt (abs_nonneg (s t))
        simp only [if_neg h]
        nlinarith [Real.sqrt_nonneg |s t|]
    have hee_abs : ∀ t, e t * e t = |s t| := by
      intro t
      simp only [he]
      by_cases h : s t < 0
      · have h2 : Real.sqrt |s t| ^ 2 = |s t| := Real.sq_sqrt (abs_nonneg (s t))
        simp only [if_pos h]
        nlinarith [Real.sqrt_nonneg |s t|]
      · have h2 : Real.sqrt |s t| ^ 2 = |s t| := Real.sq_sqrt (abs_nonneg (s t))
        simp only [if_neg h]
        nlinarith [Real.sqrt_nonneg |s t|]
    have hff_sq : ∀ t, ff t * ff t = |s t| := by
      intro t
      simp only [hff]
      exact Real.mul_self_sqrt (abs_nonneg (s t))
    have he_abs : ∀ t, |e t| = Real.sqrt |s t| := by
      intro t
      simp only [he]
      by_cases h : s t < 0
      · simp [h]
      · simp [h]
    have hff_abs : ∀ t, |ff t| = Real.sqrt |s t| := by
      intro t
      simp only [hff]
      exact abs_of_nonneg (Real.sqrt_nonneg _)
    have sqrt_norm : ∀ (g : Fin k → ℝ), (∀ t, |g t| = Real.sqrt |s t|) → ‖g‖ = Real.sqrt ‖s‖ := by
      intro g hg
      have hsqrt : (0:ℝ) ≤ Real.sqrt ‖s‖ := Real.sqrt_nonneg _
      have hup : ‖g‖ ≤ Real.sqrt ‖s‖ := by
        refine (pi_norm_le_iff_of_nonneg hsqrt).mpr ?_
        intro t
        rw [Real.norm_eq_abs, hg t]
        exact Real.sqrt_le_sqrt (norm_le_pi_norm s t)
      have hlow : Real.sqrt ‖s‖ ≤ ‖g‖ := by
        have h1 : ‖s‖ ≤ ‖g‖ * ‖g‖ := by
          refine (pi_norm_le_iff_of_nonneg
            (mul_nonneg (norm_nonneg g) (norm_nonneg g))).mpr ?_
          intro t
          have h3 : ‖s t‖ = |g t| ^ 2 := by
            rw [Real.norm_eq_abs, hg t, Real.sq_sqrt (abs_nonneg (s t))]
          have h5 : |g t| ≤ ‖g‖ := by
            have h := norm_le_pi_norm g t
            rwa [Real.norm_eq_abs] at h
          rw [h3]
          nlinarith [norm_nonneg g, abs_nonneg (g t), h5]
        calc Real.sqrt ‖s‖ ≤ Real.sqrt (‖g‖ * ‖g‖) := Real.sqrt_le_sqrt h1
          _ = Real.sqrt (‖g‖ ^ 2) := by rw [pow_two]
          _ = ‖g‖ := Real.sqrt_sq (norm_nonneg g)
      exact le_antisymm hup hlow
    have hnormM : ‖M‖ = ‖s‖ := by
      rw [hMUV, isometry_right m k n (U * Matrix.diagonal s) V hV,
        isometry m k k U (Matrix.diagonal s) hU, Matrix.l2_opNorm_diagonal]
    have hDe : ‖Matrix.diagonal e * P‖ = ‖Matrix.diagonal e‖ :=
      isometry_right k k r (Matrix.diagonal e) (Matrix.transpose P) hPPt
    have hDf : ‖Matrix.diagonal ff * P‖ = ‖Matrix.diagonal ff‖ :=
      isometry_right k k r (Matrix.diagonal ff) (Matrix.transpose P) hPPt
    have hnormX : ‖X‖ = Real.sqrt ‖s‖ := by
      rw [hX, Matrix.mul_assoc, isometry m k r U (Matrix.diagonal e * P) hU, hDe,
        Matrix.l2_opNorm_diagonal]
      exact sqrt_norm e he_abs
    have hnormY : ‖Y‖ = Real.sqrt ‖s‖ := by
      rw [hY, Matrix.mul_assoc, isometry n k r V (Matrix.diagonal ff * P) hV, hDf,
        Matrix.l2_opNorm_diagonal]
      exact sqrt_norm ff hff_abs
    have hXY : M = X * Matrix.transpose Y := by
      rw [hMUV, hX, hY]
      simp only [Matrix.transpose_mul, diagT]
      rw [← Matrix.mul_assoc (U * Matrix.diagonal e * P) (Matrix.transpose P)
            (Matrix.diagonal ff * Matrix.transpose V),
        Matrix.mul_assoc (U * Matrix.diagonal e) P (Matrix.transpose P),
        hPPt, Matrix.mul_one,
        Matrix.mul_assoc U (Matrix.diagonal e) (Matrix.diagonal ff * Matrix.transpose V),
        ← Matrix.mul_assoc (Matrix.diagonal e) (Matrix.diagonal ff) (Matrix.transpose V),
        Matrix.diagonal_mul_diagonal, funext hee,
        ← Matrix.mul_assoc U (Matrix.diagonal s) (Matrix.transpose V)]
    have hXXt : X * Matrix.transpose X
        = U * Matrix.diagonal (fun t => |s t|) * Matrix.transpose U := by
      rw [hX]
      simp only [Matrix.transpose_mul, diagT]
      rw [← Matrix.mul_assoc (U * Matrix.diagonal e * P) (Matrix.transpose P)
            (Matrix.diagonal e * Matrix.transpose U),
        Matrix.mul_assoc (U * Matrix.diagonal e) P (Matrix.transpose P),
        hPPt, Matrix.mul_one,
        Matrix.mul_assoc U (Matrix.diagonal e) (Matrix.diagonal e * Matrix.transpose U),
        ← Matrix.mul_assoc (Matrix.diagonal e) (Matrix.diagonal e) (Matrix.transpose U),
        Matrix.diagonal_mul_diagonal, funext hee_abs,
        ← Matrix.mul_assoc U (Matrix.diagonal (fun t => |s t|)) (Matrix.transpose U)]
    have hYYt : Y * Matrix.transpose Y
        = V * Matrix.diagonal (fun t => |s t|) * Matrix.transpose V := by
      rw [hY]
      simp only [Matrix.transpose_mul, diagT]
      rw [← Matrix.mul_assoc (V * Matrix.diagonal ff * P) (Matrix.transpose P)
            (Matrix.diagonal ff * Matrix.transpose V),
        Matrix.mul_assoc (V * Matrix.diagonal ff) P (Matrix.transpose P),
        hPPt, Matrix.mul_one,
        Matrix.mul_assoc V (Matrix.diagonal ff) (Matrix.diagonal ff * Matrix.transpose V),
        ← Matrix.mul_assoc (Matrix.diagonal ff) (Matrix.diagonal ff) (Matrix.transpose V),
        Matrix.diagonal_mul_diagonal, funext hff_sq,
        ← Matrix.mul_assoc V (Matrix.diagonal (fun t => |s t|)) (Matrix.transpose V)]
    have hXtX : Matrix.transpose X * X
        = Matrix.transpose P * Matrix.diagonal (fun t => |s t|) * P := by
      simp only [hX, Matrix.transpose_mul, diagT]
      rw [Matrix.mul_assoc (Matrix.transpose P) (Matrix.diagonal e * Matrix.transpose U)
            ((U * Matrix.diagonal e) * P),
        Matrix.mul_assoc (Matrix.diagonal e) (Matrix.transpose U) ((U * Matrix.diagonal e) * P),
        ← Matrix.mul_assoc (Matrix.transpose U) (U * Matrix.diagonal e) P,
        ← Matrix.mul_assoc (Matrix.transpose U) U (Matrix.diagonal e), hU, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal e) (Matrix.diagonal e) P,
        Matrix.diagonal_mul_diagonal, funext hee_abs, Matrix.mul_assoc]
    have hYtY : Matrix.transpose Y * Y
        = Matrix.transpose P * Matrix.diagonal (fun t => |s t|) * P := by
      simp only [hY, Matrix.transpose_mul, diagT]
      rw [Matrix.mul_assoc (Matrix.transpose P) (Matrix.diagonal ff * Matrix.transpose V)
            ((V * Matrix.diagonal ff) * P),
        Matrix.mul_assoc (Matrix.diagonal ff) (Matrix.transpose V) ((V * Matrix.diagonal ff) * P),
        ← Matrix.mul_assoc (Matrix.transpose V) (V * Matrix.diagonal ff) P,
        ← Matrix.mul_assoc (Matrix.transpose V) V (Matrix.diagonal ff), hV, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal ff) (Matrix.diagonal ff) P,
        Matrix.diagonal_mul_diagonal, funext hff_sq, Matrix.mul_assoc]
    have hbal : Matrix.transpose X * X = Matrix.transpose Y * Y := by rw [hXtX, hYtY]
    have hrowX : twoInfNorm X ≤ Real.sqrt ‖s‖ * twoInfNorm U := by
      have hstep1 : twoInfNorm X
          = ⨆ i : Fin m, Real.sqrt ((X * Matrix.transpose X) i i) := by
        simp only [twoInfNorm, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
      rw [hstep1]
      haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      apply ciSup_le
      intro i
      rw [hXXt]
      have hii : (U * Matrix.diagonal (fun t => |s t|) * Matrix.transpose U) i i
          = ∑ t : Fin k, (U i t) ^ 2 * |s t| := by
        rw [Matrix.mul_apply]
        simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
        exact Finset.sum_congr rfl (fun t _ => by ring)
      rw [hii]
      have hUrow : Real.sqrt (∑ t : Fin k, U i t ^ 2) ≤ twoInfNorm U := by
        show Real.sqrt (∑ t : Fin k, U i t ^ 2)
          ≤ ⨆ i : Fin m, Real.sqrt (∑ t : Fin k, U i t ^ 2)
        exact le_ciSup (f := fun i : Fin m => Real.sqrt (∑ t : Fin k, U i t ^ 2))
          (Finite.bddAbove_range _) i
      have h1 : ∑ t : Fin k, (U i t) ^ 2 * |s t| ≤ ∑ t : Fin k, (U i t) ^ 2 * ‖s‖ := by
        apply Finset.sum_le_sum
        intro t _
        have habs : |s t| ≤ ‖s‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm s t
        exact mul_le_mul_of_nonneg_left habs (sq_nonneg _)
      have h2 : ∑ t : Fin k, (U i t) ^ 2 * ‖s‖ = (∑ t : Fin k, (U i t) ^ 2) * ‖s‖ := by
        rw [Finset.sum_mul]
      calc Real.sqrt (∑ t : Fin k, (U i t) ^ 2 * |s t|)
          ≤ Real.sqrt ((∑ t : Fin k, (U i t) ^ 2) * ‖s‖) := by
            rw [← h2]; exact Real.sqrt_le_sqrt h1
        _ = Real.sqrt (∑ t : Fin k, (U i t) ^ 2) * Real.sqrt ‖s‖ :=
            Real.sqrt_mul (Finset.sum_nonneg (fun t _ => sq_nonneg _)) _
        _ ≤ twoInfNorm U * Real.sqrt ‖s‖ :=
            mul_le_mul_of_nonneg_right hUrow (Real.sqrt_nonneg _)
        _ = Real.sqrt ‖s‖ * twoInfNorm U := mul_comm _ _
    have hrowY : twoInfNorm Y ≤ Real.sqrt ‖s‖ * twoInfNorm V := by
      have hstep1 : twoInfNorm Y
          = ⨆ i : Fin n, Real.sqrt ((Y * Matrix.transpose Y) i i) := by
        simp only [twoInfNorm, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
      rw [hstep1]
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      apply ciSup_le
      intro i
      rw [hYYt]
      have hii : (V * Matrix.diagonal (fun t => |s t|) * Matrix.transpose V) i i
          = ∑ t : Fin k, (V i t) ^ 2 * |s t| := by
        rw [Matrix.mul_apply]
        simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
        exact Finset.sum_congr rfl (fun t _ => by ring)
      rw [hii]
      have hVrow : Real.sqrt (∑ t : Fin k, V i t ^ 2) ≤ twoInfNorm V := by
        show Real.sqrt (∑ t : Fin k, V i t ^ 2)
          ≤ ⨆ i : Fin n, Real.sqrt (∑ t : Fin k, V i t ^ 2)
        exact le_ciSup (f := fun i : Fin n => Real.sqrt (∑ t : Fin k, V i t ^ 2))
          (Finite.bddAbove_range _) i
      have h1 : ∑ t : Fin k, (V i t) ^ 2 * |s t| ≤ ∑ t : Fin k, (V i t) ^ 2 * ‖s‖ := by
        apply Finset.sum_le_sum
        intro t _
        have habs : |s t| ≤ ‖s‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm s t
        exact mul_le_mul_of_nonneg_left habs (sq_nonneg _)
      have h2 : ∑ t : Fin k, (V i t) ^ 2 * ‖s‖ = (∑ t : Fin k, (V i t) ^ 2) * ‖s‖ := by
        rw [Finset.sum_mul]
      calc Real.sqrt (∑ t : Fin k, (V i t) ^ 2 * |s t|)
          ≤ Real.sqrt ((∑ t : Fin k, (V i t) ^ 2) * ‖s‖) := by
            rw [← h2]; exact Real.sqrt_le_sqrt h1
        _ = Real.sqrt (∑ t : Fin k, (V i t) ^ 2) * Real.sqrt ‖s‖ :=
            Real.sqrt_mul (Finset.sum_nonneg (fun t _ => sq_nonneg _)) _
        _ ≤ twoInfNorm V * Real.sqrt ‖s‖ :=
            mul_le_mul_of_nonneg_right hVrow (Real.sqrt_nonneg _)
        _ = Real.sqrt ‖s‖ * twoInfNorm V := mul_comm _ _
    refine ⟨X, Y, hXY, hbal, ?_, ?_, ?_, ?_⟩
    · simp only [spectralNorm, Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2, hnormX, hnormM]
    · simp only [spectralNorm, Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2, hnormY, hnormM]
    · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      have hMnorm' : ‖M‖ ≤ CM * SMax sig := by
        rw [← Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
        exact hMnorm
      have hU0 : 0 ≤ twoInfNorm U := by
        show (0:ℝ) ≤ ⨆ i : Fin m, Real.sqrt (∑ t : Fin k, U i t ^ 2)
        exact le_trans (Real.sqrt_nonneg (∑ t : Fin k, U (⟨0, hm⟩ : Fin m) t ^ 2))
          (le_ciSup (f := fun i : Fin m => Real.sqrt (∑ t : Fin k, U i t ^ 2))
            (Finite.bddAbove_range _) (⟨0, hm⟩ : Fin m))
      have hU2 : twoInfNorm U ≤ Real.sqrt (mubar * (r:ℝ)/(m:ℝ)) := by
        have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
        have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
        have hmono : Real.sqrt (mu1 * (r:ℝ)/(m:ℝ))
            ≤ Real.sqrt (mubar * (r:ℝ)/(m:ℝ)) := by
          apply Real.sqrt_le_sqrt
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmu1 hr0) (le_of_lt hm0)
        calc twoInfNorm U ≤ Real.sqrt (mu1 * (r:ℝ)/(m:ℝ)) := by
              rw [← Real.sqrt_sq hU0]
              exact Real.sqrt_le_sqrt hbU
          _ ≤ Real.sqrt (mubar * (r:ℝ)/(m:ℝ)) := hmono
      have hMle : ‖s‖ ≤ CM * SMax sig := by
        rw [← hnormM]
        exact hMnorm'
      have hsqrtS : Real.sqrt ‖s‖ ≤ Real.sqrt (CM * SMax sig) := Real.sqrt_le_sqrt hMle
      calc twoInfNorm X ≤ Real.sqrt ‖s‖ * twoInfNorm U := hrowX
        _ ≤ Real.sqrt (CM * SMax sig) * Real.sqrt (mubar * (r:ℝ)/(m:ℝ)) :=
            mul_le_mul hsqrtS hU2 hU0 (Real.sqrt_nonneg _)
    · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      have hMnorm' : ‖M‖ ≤ CM * SMax sig := by
        rw [← Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
        exact hMnorm
      have hV0 : 0 ≤ twoInfNorm V := by
        show (0:ℝ) ≤ ⨆ i : Fin n, Real.sqrt (∑ t : Fin k, V i t ^ 2)
        exact le_trans (Real.sqrt_nonneg (∑ t : Fin k, V (⟨0, hn⟩ : Fin n) t ^ 2))
          (le_ciSup (f := fun i : Fin n => Real.sqrt (∑ t : Fin k, V i t ^ 2))
            (Finite.bddAbove_range _) (⟨0, hn⟩ : Fin n))
      have hV2 : twoInfNorm V ≤ Real.sqrt (mubar * (r:ℝ)/(n:ℝ)) := by
        have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
        have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
        have hmono : Real.sqrt (mu1 * (r:ℝ)/(n:ℝ))
            ≤ Real.sqrt (mubar * (r:ℝ)/(n:ℝ)) := by
          apply Real.sqrt_le_sqrt
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmu1 hr0) (le_of_lt hn0)
        calc twoInfNorm V ≤ Real.sqrt (mu1 * (r:ℝ)/(n:ℝ)) := by
              rw [← Real.sqrt_sq hV0]
              exact Real.sqrt_le_sqrt hbV
          _ ≤ Real.sqrt (mubar * (r:ℝ)/(n:ℝ)) := hmono
      have hMle : ‖s‖ ≤ CM * SMax sig := by
        rw [← hnormM]
        exact hMnorm'
      have hsqrtS : Real.sqrt ‖s‖ ≤ Real.sqrt (CM * SMax sig) := Real.sqrt_le_sqrt hMle
      calc twoInfNorm Y ≤ Real.sqrt ‖s‖ * twoInfNorm V := hrowY
        _ ≤ Real.sqrt (CM * SMax sig) * Real.sqrt (mubar * (r:ℝ)/(n:ℝ)) :=
            mul_le_mul hsqrtS hV2 hV0 (Real.sqrt_nonneg _)
  /- @proof-region region.target-node.session.eee8505d00334385 end -/

end

end Statlib.Imported

