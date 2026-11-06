import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_672368337bcecb533534
import ProverJobs.ResidualE2ESupport20261106.M_6e7317e5561effbf18fe
import ProverJobs.ResidualE2ESupport20261106.M_1826cf4a199ca47d64c5
import ProverJobs.ResidualE2ESupport20261106.M_33749604ca0940be1dc6
import ProverJobs.ResidualE2ESupport20261106.M_6ff0d38f88616a5f3939
import ProverJobs.ResidualE2ESupport20261106.M_a8791fa1d3e4fe57b534

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_298819435_21fe1421 : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le_one : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
    (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
    (CD : ℝ) (hCD_pos : 0 < CD) (hCD_ge : Kt * (D0 + 12) ≤ CD)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ)
    (hXi_sq_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
    (hXi_mean : ∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0)
    (hXi_var : ∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
    (hXi_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
      μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ)
    (L : ℝ)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
      10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
    (b : Fin m → Fin n → ℝ)
    (hb : ∀ (i : Fin m) (j : Fin n),
      b i j = ∫ ω, Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) ∂μ)
    (c : Fin m → Fin n → ℝ)
    (hc : ∀ (i : Fin m) (j : Fin n),
      c i j = Real.sqrt (∫ ω, (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂μ))
    (XT : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXT : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
      XT ω i j = (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j),
    (max 2 (40 * (Kt + 1)) ≤ L) ∧
    (∀ (i : Fin m) (j : Fin n), 0 < c i j ∧ (1 : ℝ) / 2 ≤ c i j ∧ c i j ≤ 3 / 2) ∧
    (∀ (i : Fin m) (j : Fin n), ∫ ω, XT ω i j ∂μ = 0) ∧
    (∀ (i : Fin m) (j : Fin n), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1) ∧
    (∀ (j j' : Fin n),
      ∫ ω, (∑ i : Fin m,
        maskedScaled p (XT ω) (Mask ω) i j * maskedScaled p (XT ω) (Mask ω) i j') ∂μ
        = if j = j' then (1 : ℝ) else 0) ∧
    (∀ (i i' : Fin m),
      ∫ ω, (∑ j : Fin n,
        maskedScaled p (XT ω) (Mask ω) i j * maskedScaled p (XT ω) (Mask ω) i' j) ∂μ
        = if i = i' then (n : ℝ) / (m : ℝ) else 0) ∧
    (∀ (ω : Ω) (i : Fin m) (j : Fin n), |XT ω i j| ≤ 3 * L) ∧
    (∀ (ω : Ω), ‖maskedScaled p (XT ω) (Mask ω)‖ ≤ 3 * L * Real.sqrt ((n : ℝ) / p)) ∧
    (μ {ω : Ω | ∃ (i : Fin m) (j : Fin n), L < |Xi ω i j|} ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10)))) ∧
    (∀ (ω : Ω), (∀ (i : Fin m) (j : Fin n), |Xi ω i j| ≤ L) →
      (‖maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)‖ ≤
          Real.rpow (n : ℝ) (-(D0 + 5)) ∧
        ∀ (k : Fin n),
          |svals (maskedScaled p (Xi ω) (Mask ω)) k -
              svals (maskedScaled p (XT ω) (Mask ω)) k| ≤ Real.rpow (n : ℝ) (-(D0 + 5)))) := by
  /- @proof-region region.target-node.session.b257db6070d45c1c begin -/
  classical
  intro D0 hD0 rhoMinus h_rhoMinus_pos h_rhoMinus_le Kt hKt alpha0 h_alpha0
  intro m n hm hn hnm hrho_lo hrho_hi p hp0 hp1 hsparse CD hCD_pos hCDK
  intro Ω _ μ _ Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
    hMask_meas hMask_val hMask_law hMask_indep hIndep
  intro L hL_def b hb c hc XTilde hXTilde
  have hm_gt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := le_of_lt hm_gt1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmn_ge1 : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by nlinarith [hm1, hn1]
  have hlog_nonneg : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := Real.log_nonneg hmn_ge1
  set T : ℝ := 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 with hTdef
  have hpow40 : 40 * (Kt + 1) ≤ 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
    have hKt1 : (1 : ℝ) ≤ Kt + 1 := by linarith
    have hD01 : (1 : ℝ) ≤ D0 + 1 := by linarith
    have ha01 : (1 : ℝ) ≤ alpha0 + 1 := by linarith
    have hsq_le : ∀ a : ℝ, (1 : ℝ) ≤ a → (1 : ℝ) ≤ a ^ 2 := by
      intro a ha
      have h0 : (0 : ℝ) ≤ a := le_trans (by norm_num) ha
      have h := mul_le_mul ha ha (by norm_num : (0 : ℝ) ≤ 1) h0
      simpa [pow_two] using h
    have hmul_le : ∀ a b : ℝ, (1 : ℝ) ≤ a → (1 : ℝ) ≤ b → (1 : ℝ) ≤ a * b := by
      intro a b ha hb
      have h0 : (0 : ℝ) ≤ a := le_trans (by norm_num) ha
      have h := mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1) h0
      simpa using h
    have hKsq : (1 : ℝ) ≤ (Kt + 1) ^ 2 := hsq_le _ hKt1
    have hDsq : (1 : ℝ) ≤ (D0 + 1) ^ 2 := hsq_le _ hD01
    have hasq : (1 : ℝ) ≤ (alpha0 + 1) ^ 2 := hsq_le _ ha01
    have hK3 : (1 : ℝ) ≤ (Kt + 1) ^ 3 := by
      have h := hmul_le _ _ hKsq hKt1
      calc (1 : ℝ) ≤ (Kt + 1) ^ 2 * (Kt + 1) := h
        _ = (Kt + 1) ^ 3 := by ring
    have hKq : (1 : ℝ) ≤ (Kt + 1) ^ 4 := by
      have h := hsq_le _ hKsq
      calc (1 : ℝ) ≤ ((Kt + 1) ^ 2) ^ 2 := h
        _ = (Kt + 1) ^ 4 := by ring
    have hDq : (1 : ℝ) ≤ (D0 + 1) ^ 4 := by
      have h := hsq_le _ hDsq
      calc (1 : ℝ) ≤ ((D0 + 1) ^ 2) ^ 2 := h
        _ = (D0 + 1) ^ 4 := by ring
    have haq : (1 : ℝ) ≤ (alpha0 + 1) ^ 4 := by
      have h := hsq_le _ hasq
      calc (1 : ℝ) ≤ ((alpha0 + 1) ^ 2) ^ 2 := h
        _ = (alpha0 + 1) ^ 4 := by ring
    have hF : (1 : ℝ) ≤ (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := hmul_le _ _ hDq haq
    have hK41 : Kt + 1 ≤ (Kt + 1) ^ 4 := by
      have h0 : (0 : ℝ) ≤ Kt + 1 := by linarith
      have h := mul_le_mul_of_nonneg_left hK3 h0
      calc Kt + 1 = (Kt + 1) * 1 := by ring
        _ ≤ (Kt + 1) * (Kt + 1) ^ 3 := h
        _ = (Kt + 1) ^ 4 := by ring
    have h1 : 40 * (Kt + 1) ≤ 10 ^ 6 * (Kt + 1) :=
      mul_le_mul_of_nonneg_right (by norm_num : (40 : ℝ) ≤ 10 ^ 6)
        (by linarith : (0 : ℝ) ≤ Kt + 1)
    have h2 : (10 ^ 6 : ℝ) * (Kt + 1) ≤ 10 ^ 6 * (Kt + 1) ^ 4 :=
      mul_le_mul_of_nonneg_left hK41 (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
    have hP4 : (0 : ℝ) ≤ 10 ^ 6 * (Kt + 1) ^ 4 :=
      mul_nonneg (by norm_num) (le_trans (by norm_num) hKq)
    have h3 : (10 ^ 6 : ℝ) * (Kt + 1) ^ 4
        ≤ 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
      have hm := mul_le_mul_of_nonneg_left hF hP4
      calc (10 ^ 6 : ℝ) * (Kt + 1) ^ 4 = (10 ^ 6 * (Kt + 1) ^ 4) * 1 := by ring
        _ ≤ (10 ^ 6 * (Kt + 1) ^ 4) * ((D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) := hm
        _ = 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by ring
    linarith [h1, h2, h3]
  have hTbig : 40 * (Kt + 1) ≤ T := by
    rw [hTdef]
    exact hpow40
  have hT2 : (2 : ℝ) ≤ T := by
    rw [hTdef]
    linarith [hpow40, (by linarith : (1 : ℝ) ≤ Kt + 1)]
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT2
  clear hpow40 hTdef
  have hTL : T ≤ L := by
    rw [hL_def]
    have h0 : (0 : ℝ) ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) :=
      mul_nonneg (le_of_lt hCD_pos) hlog_nonneg
    linarith
  have hconj1 : max 2 (40 * (Kt + 1)) ≤ L :=
    max_le (le_trans hT2 hTL) (le_trans hTbig hTL)
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      (le_trans (le_max_left 2 (40 * (Kt + 1))) hconj1)
  have hLp : (0 : ℝ) < L := hLpos
  have hL2 : (2 : ℝ) ≤ L := le_trans (le_max_left 2 (40 * (Kt + 1))) hconj1
  have h4K : 40 * (Kt + 1) ≤ L := le_trans (le_max_right 2 (40 * (Kt + 1))) hconj1
  have hp_pos : 0 < p := by
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hm_gt1
    have hrpow : 0 < (Real.log (m : ℝ)).rpow alpha0 := Real.rpow_pos_of_pos hlogm alpha0
    have hmul : 0 < (m : ℝ) * p := lt_of_lt_of_le hrpow hsparse
    exact pos_of_mul_pos_right hmul (le_of_lt hm_pos)

  have hSetL : ∀ (i : Fin m) (j : Fin n), MeasurableSet {ω : Ω | |Xi ω i j| ≤ L} := by
    intro i j
    exact (continuous_abs.measurable.comp (hXi_meas i j)) measurableSet_Iic
  have hTruncInt : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω => Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0)) μ := by
    intro i j
    have hite1 : Measurable fun ω : Ω => (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) :=
      Measurable.ite (hSetL i j) measurable_const measurable_const
    refine MeasureTheory.Integrable.mono (hXi_int i j)
      ((hXi_meas i j).mul hite1).aestronglyMeasurable ?_
    filter_upwards with ω
    by_cases h : (|Xi ω i j| ≤ L)
    · rw [if_pos h, mul_one]
    · rw [if_neg h, mul_zero, norm_zero]
      exact norm_nonneg _
  have hTailInt : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω => (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1)) μ := by
    intro i j
    have hsqM : Measurable fun ω : Ω => (Xi ω i j) ^ 2 := by
      simpa [pow_two] using (hXi_meas i j).mul (hXi_meas i j)
    have hite0 : Measurable fun ω : Ω => (if |Xi ω i j| ≤ L then (0 : ℝ) else 1) :=
      Measurable.ite (hSetL i j) measurable_const measurable_const
    refine MeasureTheory.Integrable.mono (hXi_sq_int i j) (hsqM.mul hite0).aestronglyMeasurable ?_
    filter_upwards with ω
    by_cases h : (|Xi ω i j| ≤ L)
    · rw [if_pos h, mul_zero, norm_zero]
      exact norm_nonneg _
    · rw [if_neg h, mul_one]
  obtain ⟨hbig16, hbig4⟩ :=
    statopia_math_node_3865474750_001c1756 L Kt CD D0 alpha0 m n hKt hD0 h_alpha0 hCD_pos
      (by omega : 1 ≤ m) hn hL_def
  have hmom : ∀ (i : Fin m) (j : Fin n),
      |∫ ω, Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) ∂μ|
          ≤ 2 * (L + Kt) * Real.exp (-L / Kt)
        ∧ (∫ ω, (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1) ∂μ)
          ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) := by
    intro i j
    exact statopia_math_node_895243969_77380b6a μ (fun ω => Xi ω i j) Kt L hKt hLpos
      (hXi_meas i j) (hXi_int i j) (hXi_mean i j) (hXi_sq_int i j) (hXi_var i j)
      (hXi_tail i j) (hTruncInt i j) (hTailInt i j)
  have hb_le : ∀ (i : Fin m) (j : Fin n), |b i j| ≤ 1 / 4 := by
    intro i j
    have h1 := (hmom i j).1
    rw [hb i j]
    exact le_trans h1 hbig4
  have hbnd : ∀ (i : Fin m) (j : Fin n), |b i j| ≤ L / 2 := by
    intro i j
    have h1 : |b i j| ≤ 1 / 4 := hb_le i j
    linarith [hL2]
  have hc_bounds : ∀ (i : Fin m) (j : Fin n),
      0 < c i j ∧ (1 : ℝ) / 2 ≤ c i j ∧ c i j ≤ 3 / 2 :=
    statopia_math_node_1683139888_f744e102 D0 Kt alpha0 CD L m n hD0 hKt h_alpha0 hCD_pos
      (by omega : 1 ≤ m) hn hL_def μ Xi hXi_meas hXi_int hXi_sq_int hXi_mean hXi_var
      hXi_tail b c hb hc
  have hc_pos : ∀ (i : Fin m) (j : Fin n), 0 < c i j := fun i j => (hc_bounds i j).1
  have hcge : ∀ (i : Fin m) (j : Fin n), (1 : ℝ) / 2 ≤ c i j := fun i j => (hc_bounds i j).2.1
  have hcle : ∀ (i : Fin m) (j : Fin n), c i j ≤ 3 / 2 := fun i j => (hc_bounds i j).2.2
  have hXT : ∀ (ω : Ω) (i : Fin m) (j : Fin n), |XTilde ω i j| ≤ 3 * L := by
    intro ω i j
    have hc0 : 0 < c i j := hc_pos i j
    have hb1 : |b i j| ≤ L / 2 := hbnd i j
    have hprod : 3 * L * (1 / 2) ≤ 3 * L * c i j :=
      mul_le_mul_of_nonneg_left (hcge i j) (by linarith)
    rw [hXTilde ω i j, abs_div, abs_of_pos hc0]
    first
      | rw [div_le_iff₀ hc0]
      | rw [div_le_iff hc0]
      | rw [div_le_iff_of_pos hc0]
    by_cases h : (|Xi ω i j| ≤ L)
    · rw [if_pos h, mul_one]
      rw [sub_eq_add_neg]
      have hstep : |Xi ω i j + -b i j| ≤ L + L / 2 := by
        have h1 := abs_add_le (Xi ω i j) (-b i j)
        rw [abs_neg] at h1
        exact le_trans h1 (add_le_add h hb1)
      linarith
    · rw [if_neg h, mul_zero, zero_sub, abs_neg]
      linarith
  have hmean : ∀ (i : Fin m) (j : Fin n), ∫ ω, XTilde ω i j ∂μ = 0 := by
    intro i j
    simp only [hXTilde]
    have hint : Integrable (fun ω => Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0)) μ :=
      hTruncInt i j
    have h1 : ∫ ω, (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ∂μ = 0 := by
      calc ∫ ω, (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ∂μ
          = (∫ ω, Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) ∂μ) - ∫ ω, b i j ∂μ := by
            rw [integral_sub hint (integrable_const _)]
        _ = 0 := by
            rw [hb i j]
            simp
    rw [MeasureTheory.integral_div, h1]
    simp
  have hsecond : ∀ (i : Fin m) (j : Fin n), ∫ ω, (XTilde ω i j) ^ 2 ∂μ = 1 := by
    intro i j
    simp only [hXTilde]
    have hne : c i j ≠ 0 := ne_of_gt (hc_pos i j)
    have hnn : 0 ≤ ∫ ω,
        (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂μ := by
      first
        | exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        | exact integral_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        | exact integral_nonneg_of_forall fun ω => sq_nonneg _
    have hC2 : (c i j) ^ 2 = ∫ ω,
        (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂μ := by
      rw [hc i j]
      exact Real.sq_sqrt hnn
    simp only [div_pow]
    rw [integral_div, hC2]
    exact div_self (by rw [← hC2]; exact pow_ne_zero 2 hne)
  have hMaskMean : ∀ (i : Fin m) (j : Fin n), ∫ ω, Mask ω i j ∂μ = p := by
    intro i j
    have hmeas : Measurable fun ω => Mask ω i j := hMask_meas i j
    have hs : MeasurableSet {ω : Ω | Mask ω i j = 1} := hmeas (measurableSet_singleton 1)
    have hfun : (fun ω => Mask ω i j)
        = Set.indicator {ω : Ω | Mask ω i j = 1} (fun _ => (1 : ℝ)) := by
      funext ω
      rcases hMask_val i j ω with h0 | h1
      · simp [h0]
      · simp [h1]
    have hreal : μ.real {ω : Ω | Mask ω i j = 1}
        = (μ {ω : Ω | Mask ω i j = 1}).toReal := rfl
    rw [hfun, MeasureTheory.integral_indicator hs, MeasureTheory.setIntegral_const, hreal,
      hMask_law i j]
    simp only [smul_eq_mul, mul_one]
    exact ENNReal.toReal_ofReal (le_of_lt hp0)
  have hφmeas : ∀ (i : Fin m) (j : Fin n),
      Measurable fun x : ℝ => (x * (if |x| ≤ L then (1 : ℝ) else 0) - b i j) / c i j := by
    intro i j
    have hS : MeasurableSet {x : ℝ | |x| ≤ L} := continuous_abs.measurable measurableSet_Iic
    have hite : Measurable fun x : ℝ => (if |x| ≤ L then (1 : ℝ) else 0) := by
      have hEq : (fun x : ℝ => (if |x| ≤ L then (1 : ℝ) else 0))
          = Set.indicator {x : ℝ | |x| ≤ L} (fun _ => (1 : ℝ)) := by
        funext x
        by_cases h : (|x| ≤ L)
        · simp [h]
        · simp [h]
      rw [hEq]
      exact measurable_const.indicator hS
    first
      | exact ((measurable_id.mul hite).sub measurable_const).div_const (c i j)
      | exact Measurable.div_const ((measurable_id.mul hite).sub measurable_const) (c i j)
  have hXTilde_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => XTilde ω i j := by
    intro i j
    have hEq : (fun ω => XTilde ω i j)
        = fun ω => ((Xi ω i j) * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j := by
      funext ω
      exact hXTilde ω i j
    rw [hEq]
    exact (hφmeas i j).comp (hXi_meas i j)
  have hindep_pair : ∀ (i : Fin m) (j : Fin n),
      IndepFun (fun ω => Xi ω i j) (fun ω => Mask ω i j) μ := by
    intro i j
    exact hIndep.comp (measurable_pi_apply (i, j)) (measurable_pi_apply (i, j))
  have hmp0 : (0 : ℝ) ≤ (m : ℝ) * p := mul_nonneg (by positivity) (le_of_lt hp0)
  have hinv0 : (0 : ℝ) ≤ (Real.sqrt ((m : ℝ) * p))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hLnn0 : (0 : ℝ) ≤ 3 * L := by linarith
  have hAone : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
      ‖maskedScaled p (XTilde ω) (Mask ω) i j‖
        ≤ 3 * L * (Real.sqrt ((m : ℝ) * p))⁻¹ := by
    intro ω i j
    have hM : |Mask ω i j| ≤ 1 := by
      rcases hMask_val i j ω with h0 | h1
      · simp [h0]
      · simp [h1]
    have hprod : |Mask ω i j * XTilde ω i j| ≤ 3 * L := by
      rw [abs_mul]
      calc |Mask ω i j| * |XTilde ω i j| ≤ 1 * (3 * L) :=
            mul_le_mul hM (hXT ω i j) (abs_nonneg _) (by norm_num)
        _ = 3 * L := one_mul _
    calc ‖maskedScaled p (XTilde ω) (Mask ω) i j‖
        = |Mask ω i j * XTilde ω i j| * (Real.sqrt ((m : ℝ) * p))⁻¹ := by
          rw [show maskedScaled p (XTilde ω) (Mask ω) i j
              = Mask ω i j * XTilde ω i j / Real.sqrt ((m : ℝ) * p) from rfl,
            Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), div_eq_mul_inv]
      _ ≤ (3 * L) * (Real.sqrt ((m : ℝ) * p))⁻¹ :=
          mul_le_mul_of_nonneg_right hprod hinv0
  have hentryG : ∀ (ω : Ω) (i₁ i₂ : Fin m) (j₁ j₂ : Fin n),
      ‖maskedScaled p (XTilde ω) (Mask ω) i₁ j₁
        * maskedScaled p (XTilde ω) (Mask ω) i₂ j₂‖
        ≤ (3 * L) ^ 2 * ((m : ℝ) * p)⁻¹ := by
    intro ω i₁ i₂ j₁ j₂
    calc ‖maskedScaled p (XTilde ω) (Mask ω) i₁ j₁
          * maskedScaled p (XTilde ω) (Mask ω) i₂ j₂‖
        = ‖maskedScaled p (XTilde ω) (Mask ω) i₁ j₁‖
          * ‖maskedScaled p (XTilde ω) (Mask ω) i₂ j₂‖ := norm_mul _ _
      _ ≤ (3 * L * (Real.sqrt ((m : ℝ) * p))⁻¹)
            * (3 * L * (Real.sqrt ((m : ℝ) * p))⁻¹) :=
          mul_le_mul (hAone ω i₁ j₁) (hAone ω i₂ j₂) (norm_nonneg _)
            (mul_nonneg hLnn0 hinv0)
      _ = (3 * L) ^ 2 * ((m : ℝ) * p)⁻¹ := by
          have hs : (Real.sqrt ((m : ℝ) * p))⁻¹ * (Real.sqrt ((m : ℝ) * p))⁻¹
              = ((m : ℝ) * p)⁻¹ := by
            rw [← mul_inv, ← pow_two, Real.sq_sqrt hmp0]
          calc (3 * L * (Real.sqrt ((m : ℝ) * p))⁻¹)
                * (3 * L * (Real.sqrt ((m : ℝ) * p))⁻¹)
              = (3 * L) ^ 2
                * ((Real.sqrt ((m : ℝ) * p))⁻¹ * (Real.sqrt ((m : ℝ) * p))⁻¹) := by ring
            _ = (3 * L) ^ 2 * ((m : ℝ) * p)⁻¹ := by rw [hs]
  have hXT_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => XTilde ω i j) μ := by
    intro i j
    refine MeasureTheory.Integrable.of_bound (hXTilde_meas i j).aestronglyMeasurable (3 * L) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hXT ω i j
  have hXT_sq_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (XTilde ω i j) ^ 2) μ := by
    intro i j
    have hmeas : AEStronglyMeasurable (fun ω => (XTilde ω i j) ^ 2) μ := by
      have h2 : Measurable fun ω : Ω => (XTilde ω i j) ^ 2 := by
        simpa [pow_two] using (hXTilde_meas i j).mul (hXTilde_meas i j)
      exact h2.aestronglyMeasurable
    refine MeasureTheory.Integrable.of_bound hmeas ((3 * L) ^ 2) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (XTilde ω i j) ^ 2 = |XTilde ω i j| ^ 2 := by rw [sq_abs]
      _ ≤ (3 * L) ^ 2 := by
          rw [pow_two, pow_two]
          exact mul_le_mul (hXT ω i j) (hXT ω i j) (abs_nonneg _) hLnn0
  have hind_pair_XT : iIndepFun
      (fun (ij : Fin m × Fin n) (ω : Ω) => XTilde ω ij.1 ij.2) μ := by
    have hφall : iIndepFun
        (fun (ij : Fin m × Fin n) (ω : Ω) =>
          ((Xi ω ij.1 ij.2 * if |Xi ω ij.1 ij.2| ≤ L then (1 : ℝ) else 0)
            - b ij.1 ij.2) / c ij.1 ij.2) μ :=
      hXi_indep.comp
        (fun (ij : Fin m × Fin n) (x : ℝ) =>
          ((x * if |x| ≤ L then (1 : ℝ) else 0) - b ij.1 ij.2) / c ij.1 ij.2)
        (fun ij => hφmeas ij.1 ij.2)
    have hfam : (fun (ij : Fin m × Fin n) (ω : Ω) =>
          ((Xi ω ij.1 ij.2 * if |Xi ω ij.1 ij.2| ≤ L then (1 : ℝ) else 0)
            - b ij.1 ij.2) / c ij.1 ij.2)
        = fun (ij : Fin m × Fin n) (ω : Ω) => XTilde ω ij.1 ij.2 := by
      funext ij ω
      exact (hXTilde ω ij.1 ij.2).symm
    rw [hfam] at hφall
    exact hφall
  have hind_array_XT : IndepFun (fun ω (ij : Fin m × Fin n) => XTilde ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ := by
    have hc : IndepFun
        (Function.comp (fun (ξ : (Fin m × Fin n) → ℝ) (ij : Fin m × Fin n) =>
          ((ξ ij * if |ξ ij| ≤ L then (1 : ℝ) else 0) - b ij.1 ij.2) / c ij.1 ij.2)
          (fun (ω : Ω) (ij : Fin m × Fin n) => Xi ω ij.1 ij.2))
        (Function.comp (fun (ξ : (Fin m × Fin n) → ℝ) (ij : Fin m × Fin n) => ξ ij)
          (fun (ω : Ω) (ij : Fin m × Fin n) => Mask ω ij.1 ij.2)) μ :=
      hIndep.comp
        (measurable_pi_iff.mpr fun (ij : Fin m × Fin n) =>
          (hφmeas ij.1 ij.2).comp (measurable_pi_apply ij))
        (measurable_pi_iff.mpr fun (ij : Fin m × Fin n) => measurable_pi_apply ij)
    rw [show Function.comp
          (fun (ξ : (Fin m × Fin n) → ℝ) (ij : Fin m × Fin n) =>
            ((ξ ij * if |ξ ij| ≤ L then (1 : ℝ) else 0) - b ij.1 ij.2) / c ij.1 ij.2)
          (fun (ω : Ω) (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
          = fun (ω : Ω) (ij : Fin m × Fin n) => XTilde ω ij.1 ij.2 from by
        funext ω ij
        exact (hXTilde ω ij.1 ij.2).symm] at hc
    rw [show Function.comp (fun (ξ : (Fin m × Fin n) → ℝ) (ij : Fin m × Fin n) => ξ ij)
          (fun (ω : Ω) (ij : Fin m × Fin n) => Mask ω ij.1 ij.2)
          = fun (ω : Ω) (ij : Fin m × Fin n) => Mask ω ij.1 ij.2 from rfl] at hc
    exact hc
  have hAll : ∀ (h h' : Fin m × Fin n),
      Integrable (fun ω => maskedScaled p (XTilde ω) (Mask ω) h.1 h.2
          * maskedScaled p (XTilde ω) (Mask ω) h'.1 h'.2) μ
        ∧ (∫ ω, maskedScaled p (XTilde ω) (Mask ω) h.1 h.2
            * maskedScaled p (XTilde ω) (Mask ω) h'.1 h'.2 ∂μ
          = if h = h' then 1 / (m : ℝ) else 0) := by
    intro h h'
    obtain ⟨-, -, hI, hV⟩ := statopia_math_node_3553486712_c6cf8bba m n
      (by omega : 1 ≤ m) hn p hp0 hp1 μ XTilde Mask hXTilde_meas hXT_int hXT_sq_int
      hind_pair_XT hmean hsecond hMask_meas hMask_val hMask_law hMask_indep hind_array_XT h h'
    exact ⟨hI, hV⟩
  have hrow : ∀ (j j' : Fin n),
      ∫ ω, (∑ i : Fin m,
        maskedScaled p (XTilde ω) (Mask ω) i j * maskedScaled p (XTilde ω) (Mask ω) i j') ∂μ
        = if j = j' then (1 : ℝ) else 0 := by
    intro j j'
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun i _ => (hAll (i, j) (i, j')).1)]
    by_cases h : j = j'
    · rw [if_pos h]
      have hbase : ∀ i : Fin m, (∫ ω, maskedScaled p (XTilde ω) (Mask ω) i j
          * maskedScaled p (XTilde ω) (Mask ω) i j' ∂μ) = 1 / (m : ℝ) := by
        intro i
        have hp : ((i, j) : Fin m × Fin n) = (i, j') := by simp [h]
        have hh := (hAll (i, j) (i, j')).2
        rw [if_pos hp] at hh
        exact hh
      calc (∑ i : Fin m, ∫ ω, maskedScaled p (XTilde ω) (Mask ω) i j
              * maskedScaled p (XTilde ω) (Mask ω) i j' ∂μ)
          = ∑ _i : Fin m, (1 / (m : ℝ)) := Finset.sum_congr rfl fun i _ => hbase i
        _ = 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hp : ¬ (((i, j) : Fin m × Fin n) = (i, j')) := by
        intro hh'
        exact h (by simpa using congrArg Prod.snd hh')
      have hh := (hAll (i, j) (i, j')).2
      rw [if_neg hp] at hh
      exact hh
  have hcol : ∀ (i i' : Fin m),
      ∫ ω, (∑ j : Fin n,
        maskedScaled p (XTilde ω) (Mask ω) i j * maskedScaled p (XTilde ω) (Mask ω) i' j) ∂μ
        = if i = i' then (n : ℝ) / (m : ℝ) else 0 := by
    intro i i'
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun j _ => (hAll (i, j) (i', j)).1)]
    by_cases h : i = i'
    · rw [if_pos h]
      have hbase : ∀ j : Fin n, (∫ ω, maskedScaled p (XTilde ω) (Mask ω) i j
          * maskedScaled p (XTilde ω) (Mask ω) i' j ∂μ) = 1 / (m : ℝ) := by
        intro j
        have hp : ((i, j) : Fin m × Fin n) = (i', j) := by simp [h]
        have hh := (hAll (i, j) (i', j)).2
        rw [if_pos hp] at hh
        exact hh
      calc (∑ j : Fin n, ∫ ω, maskedScaled p (XTilde ω) (Mask ω) i j
              * maskedScaled p (XTilde ω) (Mask ω) i' j ∂μ)
          = ∑ _j : Fin n, (1 / (m : ℝ)) := Finset.sum_congr rfl fun j _ => hbase j
        _ = (n : ℝ) / (m : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hp : ¬ (((i, j) : Fin m × Fin n) = (i', j)) := by
        intro hh'
        exact h (by simpa using congrArg Prod.fst hh')
      have hh := (hAll (i, j) (i', j)).2
      rw [if_neg hp] at hh
      exact hh
  refine ⟨hconj1, hc_bounds, hmean, hsecond, hrow, hcol, hXT, ?_, ?_, ?_⟩
  · intro ω
    refine le_trans (statopia_math_node_1409213541_c481236b m n (maskedScaled p (XTilde ω) (Mask ω))) ?_
    have hsq : ∀ (i : Fin m) (j : Fin n),
        (maskedScaled p (XTilde ω) (Mask ω) i j) ^ 2 ≤ (3 * L) ^ 2 * ((m : ℝ) * p)⁻¹ := by
      intro i j
      have h := hentryG ω i i j j
      have h2 : ‖maskedScaled p (XTilde ω) (Mask ω) i j
          * maskedScaled p (XTilde ω) (Mask ω) i j‖
          = (maskedScaled p (XTilde ω) (Mask ω) i j) ^ 2 := by
        rw [norm_mul, Real.norm_eq_abs, abs_mul_abs_self, pow_two]
      rwa [h2] at h
    have hsum : (∑ i : Fin m, ∑ j : Fin n, (maskedScaled p (XTilde ω) (Mask ω) i j) ^ 2)
        ≤ (m : ℝ) * (n : ℝ) * ((3 * L) ^ 2 * ((m : ℝ) * p)⁻¹) := by
      calc (∑ i : Fin m, ∑ j : Fin n, (maskedScaled p (XTilde ω) (Mask ω) i j) ^ 2)
          ≤ ∑ i : Fin m, ∑ j : Fin n, ((3 * L) ^ 2 * ((m : ℝ) * p)⁻¹) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsq i j
        _ = (m : ℝ) * (n : ℝ) * ((3 * L) ^ 2 * ((m : ℝ) * p)⁻¹) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hsum' : Real.sqrt
        (∑ i : Fin m, ∑ j : Fin n, (maskedScaled p (XTilde ω) (Mask ω) i j) ^ 2)
        ≤ Real.sqrt ((m : ℝ) * (n : ℝ) * ((3 * L) ^ 2 * ((m : ℝ) * p)⁻¹)) :=
      Real.sqrt_le_sqrt hsum
    refine le_trans hsum' ?_
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hpne : p ≠ 0 := ne_of_gt hp0
    have hft : (m : ℝ) * (n : ℝ) * ((3 * L) ^ 2 * ((m : ℝ) * p)⁻¹)
        = (3 * L) ^ 2 * ((n : ℝ) / p) := by
      field_simp
    rw [hft, Real.sqrt_mul (by positivity), Real.sqrt_sq hLnn0]
  · have hS : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := hlog_nonneg
    have hlogM : Real.log ((m : ℝ) * (n : ℝ)) = Real.log (m : ℝ) + Real.log (n : ℝ) :=
      Real.log_mul (ne_of_gt hm_pos) (ne_of_gt hn_pos)
    have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
    have hCDlog : CD * Real.log ((m : ℝ) * (n : ℝ)) ≤ L := by
      rw [hL_def]
      linarith [hTpos]
    have hA1 : Kt * ((D0 + 12) * Real.log ((m : ℝ) * (n : ℝ))) ≤ L := by
      have h1 := mul_le_mul_of_nonneg_right hCDK hS
      calc Kt * ((D0 + 12) * Real.log ((m : ℝ) * (n : ℝ)))
          = (Kt * (D0 + 12)) * Real.log ((m : ℝ) * (n : ℝ)) := by ring
        _ ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := h1
        _ ≤ L := hCDlog
    have hexp1 : Real.exp (-L / Kt)
        ≤ Real.exp (Real.log ((m : ℝ) * (n : ℝ)) * (-(D0 + 12))) := by
      refine Real.exp_le_exp.mpr ?_
      rw [div_le_iff₀ hKt]
      have h4 : Real.log ((m : ℝ) * (n : ℝ)) * (-(D0 + 12)) * Kt
          = -(Kt * ((D0 + 12) * Real.log ((m : ℝ) * (n : ℝ)))) := by ring
      rw [h4]
      linarith
    have hprod2 : (2 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by
      have h2m : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h := mul_le_mul h2m hn1 (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hm_pos)
      simpa using h
    have hmn2pos : (0 : ℝ) < (m : ℝ) * (n : ℝ) := mul_pos hm_pos hn_pos
    have hexpM : Real.exp (Real.log ((m : ℝ) * (n : ℝ))) = (m : ℝ) * (n : ℝ) :=
      Real.exp_log hmn2pos
    have hmain : (m : ℝ) * (n : ℝ) * (2 * Real.exp (-L / Kt))
        ≤ Real.rpow (n : ℝ) (-(D0 + 10)) := by
      have hX : (0 : ℝ) ≤ Real.exp (-L / Kt) := le_of_lt (Real.exp_pos _)
      calc (m : ℝ) * (n : ℝ) * (2 * Real.exp (-L / Kt))
          = 2 * (((m : ℝ) * (n : ℝ)) * Real.exp (-L / Kt)) := by ring
        _ ≤ ((m : ℝ) * (n : ℝ)) * (((m : ℝ) * (n : ℝ)) * Real.exp (-L / Kt)) :=
            mul_le_mul_of_nonneg_right hprod2 (mul_nonneg (le_of_lt hmn2pos) hX)
        _ = (((m : ℝ) * (n : ℝ)) * ((m : ℝ) * (n : ℝ))) * Real.exp (-L / Kt) := by ring
        _ = Real.exp (Real.log ((m : ℝ) * (n : ℝ)) + Real.log ((m : ℝ) * (n : ℝ)))
              * Real.exp (-L / Kt) := by rw [Real.exp_add, hexpM]
        _ ≤ Real.exp (Real.log ((m : ℝ) * (n : ℝ)) + Real.log ((m : ℝ) * (n : ℝ)))
              * Real.exp (Real.log ((m : ℝ) * (n : ℝ)) * (-(D0 + 12))) :=
            mul_le_mul_of_nonneg_left hexp1 (le_of_lt (Real.exp_pos _))
        _ = Real.exp ((Real.log ((m : ℝ) * (n : ℝ)) + Real.log ((m : ℝ) * (n : ℝ)))
              + Real.log ((m : ℝ) * (n : ℝ)) * (-(D0 + 12))) := by rw [← Real.exp_add]
        _ ≤ Real.exp (-(D0 + 10) * Real.log (n : ℝ)) := by
            refine Real.exp_le_exp.mpr ?_
            have h1 : (Real.log ((m : ℝ) * (n : ℝ)) + Real.log ((m : ℝ) * (n : ℝ)))
                + Real.log ((m : ℝ) * (n : ℝ)) * (-(D0 + 12))
                = (-(D0 + 10)) * Real.log ((m : ℝ) * (n : ℝ)) := by ring
            rw [h1]
            have h2 : Real.log (n : ℝ) ≤ Real.log ((m : ℝ) * (n : ℝ)) := by
              rw [hlogM]
              linarith
            exact mul_le_mul_of_nonpos_left h2 (by linarith : -(D0 + 10) ≤ 0)
        _ = Real.rpow (n : ℝ) (-(D0 + 10)) := by
            have hpow : Real.rpow (n : ℝ) (-(D0 + 10))
                = Real.exp (Real.log (n : ℝ) * (-(D0 + 10))) :=
              Real.rpow_def_of_pos hn_pos (-(D0 + 10))
            rw [hpow]
            congr 1
            ring
    have hmono : μ {ω : Ω | ∃ (i : Fin m) (j : Fin n), L < |Xi ω i j|}
        ≤ μ (⋃ (ij : Fin m × Fin n), {ω : Ω | L < |Xi ω ij.1 ij.2|}) := by
      refine measure_mono ?_
      intro ω hω
      obtain ⟨i, j, hij⟩ := hω
      exact Set.mem_iUnion.mpr ⟨(i, j), hij⟩
    refine le_trans hmono ?_
    refine le_trans (MeasureTheory.measure_iUnion_fintype_le μ
      (fun ij : Fin m × Fin n => ({ω : Ω | L < |Xi ω ij.1 ij.2|} : Set Ω))) ?_
    refine le_trans (Finset.sum_le_sum fun ij _ => hXi_tail ij.1 ij.2 L hLpos) ?_
    have hcast : ((m * n : ℕ) : ENNReal) = ENNReal.ofReal ((m : ℝ) * (n : ℝ)) := by
      rw [← ENNReal.ofReal_natCast, Nat.cast_mul]
    have hsum : (∑ _ij : Fin m × Fin n, ENNReal.ofReal (2 * Real.exp (-L / Kt)))
        = ENNReal.ofReal ((m : ℝ) * (n : ℝ) * (2 * Real.exp (-L / Kt))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]
      rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
    rw [hsum]
    exact ENNReal.ofReal_le_ofReal hmain
  · intro ω hω
    have hb_sharp : ∀ (i : Fin m) (j : Fin n), |b i j| ≤ 2 * (L + Kt) * Real.exp (-L / Kt) := by
      intro i j
      have h1 := (hmom i j).1
      rw [hb i j]
      exact h1
    have hQ_sharp : ∀ (i : Fin m) (j : Fin n),
        ∫ ω, (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1) ∂μ
          ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) :=
      fun i j => (hmom i j).2
    exact statopia_math_node_467938922_fa16f85f μ D0 Kt alpha0 CD L p m n hD0 hKt h_alpha0
      hCD_pos hCDK hm hn hnm hp0 hp1 hsparse hL_def Xi Mask b c XTilde hMask_meas hMask_val
      hXi_meas hXi_int hXi_sq_int hXi_var hb hc hXTilde hc_bounds hb_sharp hQ_sharp ω hω
  /- @proof-region region.target-node.session.b257db6070d45c1c end -/

end Statlib.Imported

