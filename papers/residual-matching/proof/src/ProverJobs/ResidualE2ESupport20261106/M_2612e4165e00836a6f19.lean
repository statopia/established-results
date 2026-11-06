import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_655541399eba6e711ce1
import ProverJobs.ResidualE2ESupport20261106.M_fcdbf385f97b07d4c7eb
import ProverJobs.ResidualE2ESupport20261106.M_16393836de1500c0c075
import ProverJobs.ResidualE2ESupport20261106.M_1826cf4a199ca47d64c5
import ProverJobs.ResidualE2ESupport20261106.M_fd4cdab3b3f7ab294c05
import ProverJobs.ResidualE2ESupport20261106.M_2435fdb8926ff7f3b332

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
theorem statopia_math_node_3249198672_935a9270 : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CD : ℝ) (hCD : max (Kt * (D0 + 12)) (D0 + 20) ≤ CD),
    ∃ M1 : ℕ,
      ∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hM1 : M1 ≤ m)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p),
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (XT Mask : Ω → Matrix (Fin m) (Fin n) ℝ) (L : ℝ),
        L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
              (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 →
        (∀ (i : Fin m) (j : Fin n), Measurable fun ω => XT ω i j) →
        (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => XT ω i j) μ) →
        (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (XT ω i j) ^ 2) μ) →
        (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
        (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
        (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
        iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => XT ω ij.1 ij.2) μ →
        iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
        IndepFun (fun ω (ij : Fin m × Fin n) => XT ω ij.1 ij.2)
          (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
        (∀ (i : Fin m) (j : Fin n), ∫ ω, XT ω i j ∂μ = 0) →
        (∀ (i : Fin m) (j : Fin n), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1) →
        (∀ (ω : Ω) (i : Fin m) (j : Fin n), |XT ω i j| ≤ 3 * L) →
        μ {ω | 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m <
              svals (maskedScaled p (XT ω) (Mask ω)) ⟨0, by omega⟩} ≤
          ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 4)) / 2) := by
  /- @proof-region region.target-node.session.c232d77e8fc352ee begin -/
  classical
  intro D0 hD0 rhoMinus hrhoMinus_pos hrhoMinus_le Kt hKt alpha0 halpha0 CD hCD
  obtain ⟨M1_E, hE_child⟩ :=
    statopia_math_node_2034633510_f859b6bb D0 hD0 Kt hKt alpha0 halpha0 CD hCD
  refine ⟨M1_E + 100, ?_⟩
  intro m n hm hn hnm hM1 hrho_lo hrho_hi p hp0 hp1 hsparse
  intro Ω _ μ _ XT Mask L hL hXTmeas hXTint hXTint2 hMaskmeas hMask01 hMasklaw
    hXTindep hMaskindep hIndep hXTmean hXT2 hXTb
  have hM1_E' : M1_E ≤ m := by omega
  have hmom : ∀ h h' : Fin m × Fin n,
      Integrable (fun ω => maskedScaled p (XT ω) (Mask ω) h.1 h.2) μ ∧
      (∫ ω, maskedScaled p (XT ω) (Mask ω) h.1 h.2 ∂μ = 0) ∧
      Integrable (fun ω => maskedScaled p (XT ω) (Mask ω) h.1 h.2
        * maskedScaled p (XT ω) (Mask ω) h'.1 h'.2) μ ∧
      (∫ ω, maskedScaled p (XT ω) (Mask ω) h.1 h.2
          * maskedScaled p (XT ω) (Mask ω) h'.1 h'.2 ∂μ
        = if h = h' then 1 / (m : ℝ) else 0) :=
    fun h h' => statopia_math_node_3553486712_c6cf8bba m n (by omega) hn p hp0 hp1 μ XT Mask
      hXTmeas hXTint hXTint2 hXTindep hXTmean hXT2 hMaskmeas hMask01 hMasklaw hMaskindep
      hIndep h h'
  have hmean : ∀ (i : Fin m) (j : Fin n),
      ∫ ω, maskedScaled p (XT ω) (Mask ω) i j ∂μ = 0 :=
    fun i j => (hmom (i, j) (i, j)).2.1
  have hsecond : ∀ (h h' : Fin m × Fin n),
      ∫ ω, maskedScaled p (XT ω) (Mask ω) h.1 h.2
          * maskedScaled p (XT ω) (Mask ω) h'.1 h'.2 ∂μ
        = if h = h' then 1 / (m : ℝ) else 0 :=
    fun h h' => (hmom h h').2.2.2
  have hLpos : 0 < L := by
    have hCDpos : 0 < CD := by
      have h := le_trans (le_max_right (Kt * (D0 + 12)) (D0 + 20)) hCD
      linarith
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmn1 : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by nlinarith
    have hlog : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := Real.log_nonneg hmn1
    have hT1 : 0 < Kt + 1 := by linarith
    have hT2 : 0 < D0 + 1 := by linarith
    have hT3 : 0 < alpha0 + 1 := by linarith
    have hconst : 0 < (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
      positivity
    have hprod : 0 ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := mul_nonneg (le_of_lt hCDpos) hlog
    rw [hL]
    linarith
  have hden : 0 < Real.sqrt ((m : ℝ) * p) := by
    apply Real.sqrt_pos.mpr
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    exact mul_pos hm0 hp0
  have hentry : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
      |maskedScaled p (XT ω) (Mask ω) i j| ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := by
    intro ω i j
    have hMabs : |Mask ω i j| ≤ 1 := by
      rcases hMask01 i j ω with h | h <;> rw [h] <;> norm_num
    have hstep : |Mask ω i j * XT ω i j| ≤ 3 * L := by
      rw [abs_mul]
      exact le_trans (mul_le_of_le_one_left (abs_nonneg _) hMabs) (hXTb ω i j)
    unfold maskedScaled
    rw [abs_div, abs_of_pos hden, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hstep (le_of_lt (inv_pos.mpr hden))
  have hR0 : 0 ≤ 3 * L / Real.sqrt ((m : ℝ) * p) :=
    div_nonneg (by linarith) (le_of_lt hden)
  have hAmeas : ∀ (i : Fin m) (j : Fin n),
      Measurable fun ω => maskedScaled p (XT ω) (Mask ω) i j := by
    intro i j
    unfold maskedScaled
    exact ((hMaskmeas i j).mul (hXTmeas i j)).div measurable_const
  have hsqrt_sparse : Real.sqrt (Real.rpow (Real.log ((m : ℝ))) alpha0)
      ≤ Real.sqrt ((m : ℝ) * p) :=
    Real.sqrt_le_sqrt hsparse
  have hlogpos : 0 < Real.log (m : ℝ) := by
    refine Real.log_pos ?_
    exact_mod_cast (show 1 < m by omega)
  have hR_le : 3 * L / Real.sqrt ((m : ℝ) * p)
      ≤ 3 * L / Real.sqrt (Real.rpow (Real.log (m : ℝ)) alpha0) := by
    have h3 : (0 : ℝ) ≤ 3 * L := by linarith
    have hb : (0 : ℝ) < Real.sqrt (Real.rpow (Real.log (m : ℝ)) alpha0) :=
      Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hlogpos alpha0)
    gcongr
  have hsqrt_rpow : Real.sqrt (Real.rpow (Real.log (m : ℝ)) alpha0)
      = Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) := by
    have hw : 0 < Real.log (m : ℝ) := hlogpos
    have hpos : 0 < Real.rpow (Real.log (m : ℝ)) alpha0 := Real.rpow_pos_of_pos hw alpha0
    have hlog : Real.log (Real.rpow (Real.log (m : ℝ)) alpha0)
        = alpha0 * Real.log (Real.log (m : ℝ)) := by
      have h := Real.rpow_def_of_pos hw alpha0
      have h' : Real.rpow (Real.log (m : ℝ)) alpha0
          = Real.exp (Real.log (Real.log (m : ℝ)) * alpha0) := h
      rw [h', Real.log_exp]
      ring
    calc Real.sqrt (Real.rpow (Real.log (m : ℝ)) alpha0)
        = (Real.rpow (Real.log (m : ℝ)) alpha0) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ = Real.exp (Real.log (Real.rpow (Real.log (m : ℝ)) alpha0) * (1 / 2)) := by
          have h := Real.rpow_def_of_pos hpos (1 / 2 : ℝ)
          exact h
      _ = Real.exp ((alpha0 / 2) * Real.log (Real.log (m : ℝ))) := by
          rw [hlog]
          congr 1
          ring
      _ = Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) := by
          have h := Real.rpow_def_of_pos hw (alpha0 / 2)
          have h2 : Real.rpow (Real.log (m : ℝ)) (alpha0 / 2)
              = Real.exp (Real.log (Real.log (m : ℝ)) * (alpha0 / 2)) := h
          rw [h2]
          congr 1
          ring
  have hR_le' : 3 * L / Real.sqrt ((m : ℝ) * p)
      ≤ 3 * L / Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) := by
    rw [← hsqrt_rpow]
    exact hR_le
  have hdeltaM_pos : 0 < deltaM m := by
    unfold deltaM
    exact inv_pos.mpr hlogpos
  have hlog_rpow_le : ∀ (x ε : ℝ), 0 < x → 0 < ε →
      Real.log x ≤ (1 / ε) * Real.rpow x ε := by
    intro x ε hx hε
    have hxε : 0 < Real.rpow x ε := Real.rpow_pos_of_pos hx ε
    have h1 : Real.log (Real.rpow x ε) = ε * Real.log x := by
      have h := Real.rpow_def_of_pos hx ε
      have h' : Real.rpow x ε = Real.exp (Real.log x * ε) := h
      rw [h', Real.log_exp]
      ring
    have h2 : Real.log (Real.rpow x ε) ≤ Real.rpow x ε - 1 :=
      Real.log_le_sub_one_of_pos hxε
    have h3 : Real.rpow x ε - 1 ≤ Real.rpow x ε := by linarith
    calc Real.log x = (1 / ε) * (ε * Real.log x) := by field_simp
      _ = (1 / ε) * Real.log (Real.rpow x ε) := by rw [h1]
      _ ≤ (1 / ε) * (Real.rpow x ε - 1) := by
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (1 / ε) * Real.rpow x ε := by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hlog_ge_one : 1 ≤ Real.log (m : ℝ) := by
    have hm100 : (100 : ℝ) ≤ (m : ℝ) := by
      have h : 100 ≤ m := by omega
      exact_mod_cast h
    have h100pos : (0 : ℝ) < 100 := by norm_num
    have hexp1 : Real.exp 1 ≤ (100 : ℝ) := by
      have h := Real.exp_one_lt_d9
      norm_num at h
      linarith
    have h1 : Real.log (Real.exp 1) ≤ Real.log 100 := Real.log_le_log (Real.exp_pos 1) hexp1
    rw [Real.log_exp] at h1
    exact le_trans h1 (Real.log_le_log h100pos hm100)
  have hrpow_le_one : ∀ s : ℝ, s ≤ 0 → Real.rpow (Real.log (m : ℝ)) s ≤ 1 := by
    intro s hs
    calc Real.rpow (Real.log (m : ℝ)) s ≤ Real.rpow (Real.log (m : ℝ)) 0 :=
          Real.rpow_le_rpow_of_exponent_le hlog_ge_one hs
      _ = 1 := Real.rpow_zero _
  have hlog_bound : Real.log (m : ℝ) ≤ 8 * Real.rpow (m : ℝ) (1 / 8 : ℝ) := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
    have h := hlog_rpow_le (m : ℝ) (1 / 8) hm0 (by norm_num)
    calc Real.log (m : ℝ) ≤ (1 / (1 / 8 : ℝ)) * Real.rpow (m : ℝ) (1 / 8) := h
      _ = 8 * Real.rpow (m : ℝ) (1 / 8) := by norm_num
  have hlogne : Real.log (m : ℝ) ≠ 0 := ne_of_gt hlogpos
  have hdeltaM_mul : deltaM m * Real.log (m : ℝ) = 1 := by
    unfold deltaM
    exact inv_mul_cancel₀ hlogne
  have hdeltaM_le_one : deltaM m ≤ 1 := by
    have h1 : (Real.log (m : ℝ))⁻¹ * 1 ≤ (Real.log (m : ℝ))⁻¹ * Real.log (m : ℝ) :=
      mul_le_mul_of_nonneg_left hlog_ge_one (le_of_lt (inv_pos.mpr hlogpos))
    rw [mul_one, inv_mul_cancel₀ hlogne] at h1
    unfold deltaM
    exact h1
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog_le : Real.log (n : ℝ) ≤ Real.log (m : ℝ) := by
    refine Real.log_le_log hn0' ?_
    exact_mod_cast hnm
  have hlog_mul' : Real.log ((m : ℝ) * (n : ℝ)) = Real.log (m : ℝ) + Real.log (n : ℝ) :=
    Real.log_mul (ne_of_gt (by exact_mod_cast (show 0 < m by omega) : (0 : ℝ) < (m : ℝ)))
      (ne_of_gt hn0')
  have hL_le : L ≤ 2 * CD * Real.log (m : ℝ)
      + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
    have hCDpos : 0 < CD := by
      have h := le_trans (le_max_right (Kt * (D0 + 12)) (D0 + 20)) hCD
      linarith
    have h1 : Real.log (m : ℝ) + Real.log (n : ℝ) ≤ 2 * Real.log (m : ℝ) := by linarith
    have h2 : CD * (Real.log (m : ℝ) + Real.log (n : ℝ))
        ≤ CD * (2 * Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hCDpos)
    rw [hL, hlog_mul']
    linarith
  have hR_bound : 3 * L / Real.sqrt ((m : ℝ) * p)
      ≤ 3 * (2 * CD * Real.log (m : ℝ)
          + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
        / Real.rpow (Real.log (m : ℝ)) (alpha0 / 2) := by
    refine le_trans hR_le' ?_
    have hX : 3 * L ≤ 3 * (2 * CD * Real.log (m : ℝ)
        + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) := by
      linarith [hL_le]
    have hd : (0 : ℝ) ≤ (Real.rpow (Real.log (m : ℝ)) (alpha0 / 2))⁻¹ :=
      le_of_lt (inv_pos.mpr (Real.rpow_pos_of_pos hlogpos (alpha0 / 2)))
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hX hd
  have hAprod_meas : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      Measurable fun ω => maskedScaled p (XT ω) (Mask ω) i j
        * maskedScaled p (XT ω) (Mask ω) k l := by
    intro i j k l
    exact (hAmeas i j).mul (hAmeas k l)
  have hsq_mean : ∀ (i : Fin m) (j : Fin n),
      (∫ ω, maskedScaled p (XT ω) (Mask ω) i j
        * maskedScaled p (XT ω) (Mask ω) i j ∂μ) = 1 / (m : ℝ) := by
    intro i j
    rw [hsecond (i, j) (i, j), if_pos rfl]
  have hrho_nonneg : (0 : ℝ) ≤ (n : ℝ) / (m : ℝ) :=
    div_nonneg (le_of_lt hn0')
      (le_of_lt (by exact_mod_cast (show 0 < m by omega) : (0 : ℝ) < (m : ℝ)))
  have hAindep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) =>
      maskedScaled p (XT ω) (Mask ω) ij.1 ij.2) μ := by
    have h := statopia_math_node_2156877478_7316b341
      (ι := Fin m × Fin n) (Ω := Ω) (μ := μ) (α := ℝ) (β := ℝ) (γ := ℝ)
      (fun (ij : Fin m × Fin n) (ω : Ω) => XT ω ij.1 ij.2)
      (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2)
      (fun (q : ℝ × ℝ) => q.2 * q.1 / Real.sqrt ((m : ℝ) * p))
      hXTindep hMaskindep hIndep
      (fun ij => (hXTmeas ij.1 ij.2).aemeasurable)
      (fun ij => (hMaskmeas ij.1 ij.2).aemeasurable)
      (by fun_prop : Measurable fun q : ℝ × ℝ => q.2 * q.1 / Real.sqrt ((m : ℝ) * p))
    simpa only [maskedScaled] using h
  have hexp_tail : ∀ (m n : ℕ), 2 ≤ m → 1 ≤ n → n ≤ m →
      ((m : ℝ) + (n : ℝ)) * Real.exp (-(CD * Real.log ((m : ℝ) * (n : ℝ))))
        ≤ Real.exp (-(D0 + 4) * Real.log (n : ℝ)) / 2 := by
    intro m n hm hn hnm
    have hA1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    have hA2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hA0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogA : 0 ≤ Real.log ((m : ℝ)) := Real.log_nonneg hA1
    have hlogN : 0 ≤ Real.log ((n : ℝ)) := Real.log_nonneg hN1
    have hCD20 : D0 + 20 ≤ CD := le_trans (le_max_right _ _) hCD
    have hCD4 : D0 + 4 ≤ CD := by linarith
    have hsum : (m : ℝ) + (n : ℝ) ≤ 2 * (m : ℝ) := by
      have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith
    have hlog_mul : Real.log ((m : ℝ) * (n : ℝ))
        = Real.log ((m : ℝ)) + Real.log ((n : ℝ)) :=
      Real.log_mul (ne_of_gt hA0) (ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ)))
    have hsplit : Real.exp (-(CD * Real.log ((m : ℝ) * (n : ℝ))))
        = Real.exp (-(CD * Real.log ((m : ℝ))))
          * Real.exp (-(CD * Real.log ((n : ℝ)))) := by
      rw [hlog_mul, ← Real.exp_add]
      congr 1
      ring
    have hexpA : (m : ℝ) * Real.exp (-(CD * Real.log ((m : ℝ))))
        = Real.exp ((1 - CD) * Real.log ((m : ℝ))) := by
      nth_rewrite 1 [← Real.exp_log hA0]
      rw [← Real.exp_add]
      congr 1
      ring
    have hnum : Real.exp (-19 * Real.log (2 : ℝ)) ≤ (1 : ℝ) / 8 := by
      have h4 : Real.exp (-19 * Real.log (2 : ℝ)) = ((2 : ℝ) ^ 19)⁻¹ := by
        rw [show -19 * Real.log (2 : ℝ) = -(19 * Real.log (2 : ℝ)) by ring, Real.exp_neg]
        rw [show (19 * Real.log (2 : ℝ)) = ((19 : ℕ) : ℝ) * Real.log 2 by norm_num]
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [h4]
      norm_num
    have hexpA_le : Real.exp ((1 - CD) * Real.log ((m : ℝ))) ≤ (1 : ℝ) / 8 := by
      have h1 : (1 - CD) * Real.log ((m : ℝ)) ≤ -19 * Real.log ((m : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith : (1 - CD) ≤ -19) hlogA
      have h2 : -19 * Real.log ((m : ℝ)) ≤ -19 * Real.log (2 : ℝ) := by
        have h2a : Real.log (2 : ℝ) ≤ Real.log ((m : ℝ)) := Real.log_le_log (by norm_num) hA2
        exact mul_le_mul_of_nonpos_left h2a (by norm_num : (-19 : ℝ) ≤ 0)
      exact le_trans (Real.exp_le_exp.mpr h1) (le_trans (Real.exp_le_exp.mpr h2) hnum)
    have hAterm : (m : ℝ) * Real.exp (-(CD * Real.log ((m : ℝ)))) ≤ (1 : ℝ) / 8 := by
      rw [hexpA]
      exact hexpA_le
    have heN0 : 0 ≤ Real.exp (-(CD * Real.log ((n : ℝ)))) := le_of_lt (Real.exp_pos _)
    have hNexp : Real.exp (-(CD * Real.log ((n : ℝ))))
        ≤ Real.exp (-(D0 + 4) * Real.log ((n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have h : (-CD) * Real.log ((n : ℝ)) ≤ (-(D0 + 4)) * Real.log ((n : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith : -CD ≤ -(D0 + 4)) hlogN
      calc -(CD * Real.log ((n : ℝ))) = (-CD) * Real.log ((n : ℝ)) := by ring
        _ ≤ (-(D0 + 4)) * Real.log ((n : ℝ)) := h
        _ = -(D0 + 4) * Real.log ((n : ℝ)) := by ring
    have hNpos : (0 : ℝ) < Real.exp (-(D0 + 4) * Real.log ((n : ℝ))) := Real.exp_pos _
    calc ((m : ℝ) + (n : ℝ)) * Real.exp (-(CD * Real.log ((m : ℝ) * (n : ℝ))))
        = ((m : ℝ) + (n : ℝ)) * (Real.exp (-(CD * Real.log ((m : ℝ))))
            * Real.exp (-(CD * Real.log ((n : ℝ))))) := by rw [hsplit]
      _ ≤ (2 * (m : ℝ)) * (Real.exp (-(CD * Real.log ((m : ℝ))))
            * Real.exp (-(CD * Real.log ((n : ℝ))))) :=
          mul_le_mul_of_nonneg_right hsum (mul_nonneg (le_of_lt (Real.exp_pos _)) heN0)
      _ = 2 * ((m : ℝ) * Real.exp (-(CD * Real.log ((m : ℝ)))))
            * Real.exp (-(CD * Real.log ((n : ℝ)))) := by ring
      _ ≤ 2 * ((1 : ℝ) / 8) * Real.exp (-(CD * Real.log ((n : ℝ)))) :=
          mul_le_mul_of_nonneg_right (by linarith [hAterm] :
            2 * ((m : ℝ) * Real.exp (-(CD * Real.log ((m : ℝ)))))
              ≤ 2 * ((1 : ℝ) / 8)) heN0
      _ = (1 / 4) * Real.exp (-(CD * Real.log ((n : ℝ)))) := by ring
      _ ≤ (1 / 4) * Real.exp (-(D0 + 4) * Real.log ((n : ℝ))) :=
          mul_le_mul_of_nonneg_left hNexp (by norm_num)
      _ ≤ Real.exp (-(D0 + 4) * Real.log ((n : ℝ))) / 2 := by
          have hpos := hNpos
          linarith
  have hmain : ∀ (E : Set Ω),
      (∀ ω, 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m <
          svals (maskedScaled p (XT ω) (Mask ω)) ⟨0, by omega⟩ → ω ∈ E) →
      μ E ≤ ENNReal.ofReal (((m : ℝ) + (n : ℝ))
        * Real.exp (-(CD * Real.log ((m : ℝ) * (n : ℝ))))) →
      μ {ω | 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m <
          svals (maskedScaled p (XT ω) (Mask ω)) ⟨0, by omega⟩} ≤
        ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 4)) / 2) := by
    intro E hsub hE
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hrpow : Real.rpow (n : ℝ) (-(D0 + 4))
        = Real.exp (-(D0 + 4) * Real.log (n : ℝ)) := by
      have h := Real.rpow_def_of_pos hn0 (-(D0 + 4))
      rw [show Real.log (n : ℝ) * (-(D0 + 4)) = -(D0 + 4) * Real.log (n : ℝ) by ring] at h
      exact h
    refine le_trans (le_trans (measure_mono hsub) hE) ?_
    apply ENNReal.ofReal_le_ofReal
    rw [hrpow]
    exact hexp_tail m n hm hn hnm
  have hsvals_op : ∀ ω : Ω,
      svals (maskedScaled p (XT ω) (Mask ω)) ⟨0, by omega⟩
        = Statlib.HighDim.MatrixAnalysis.opNorm (maskedScaled p (XT ω) (Mask ω)) := by
    intro ω
    exact (statopia_math_node_3797206296_f8b95f54 m n
        (maskedScaled p (XT ω) (Mask ω)) (by omega)).trans
      (Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 _).symm

  have hexists_E : ∃ E : Set Ω,
      (∀ ω : Ω, 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m <
          Statlib.HighDim.MatrixAnalysis.opNorm (maskedScaled p (XT ω) (Mask ω)) → ω ∈ E) ∧
      μ E ≤ ENNReal.ofReal (((m : ℝ) + (n : ℝ))
        * Real.exp (-(CD * Real.log ((m : ℝ) * (n : ℝ))))) := by
    exact hE_child m n hm hn hnm hM1_E' p hp0 hp1 hsparse μ XT Mask L hL
      hXTmeas hXTint hXTint2 hMaskmeas hMask01 hMasklaw hXTindep hMaskindep hIndep
      hXTmean hXT2 hXTb
  have hcore_op : μ {ω | 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m <
        Statlib.HighDim.MatrixAnalysis.opNorm (maskedScaled p (XT ω) (Mask ω))} ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 4)) / 2) := by
    obtain ⟨E, hsub, hE⟩ := hexists_E
    have hsub' : ∀ ω : Ω, 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m <
        svals (maskedScaled p (XT ω) (Mask ω)) ⟨0, by omega⟩ → ω ∈ E := by
      intro ω hω
      exact hsub ω (by simpa only [hsvals_op] using hω)
    simpa only [hsvals_op] using hmain E hsub' hE
  simpa only [hsvals_op] using hcore_op
  /- @proof-region region.target-node.session.c232d77e8fc352ee end -/

#print axioms statopia_math_node_3249198672_935a9270
end Statlib.Imported

