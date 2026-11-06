import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_6dd646d80d4b86b21eac
import ProverJobs.ResidualE2ESupport20261106.M_d580ac9e42f19ac4b981
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
theorem statopia_math_node_676634694_439e1a38 : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (rhoMinus : ℝ) (hrho_pos : 0 < rhoMinus) (hrho_le_one : rhoMinus ≤ 1)
    (CD : ℝ) (hCD : Kt * (D0 + 12) ≤ CD)
    (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
    (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
    (L : ℝ)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
        10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
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
    (hMask_law : ∀ (i : Fin m) (j : Fin n),
      μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
    ∃ (b : Fin m → Fin n → ℝ),
      (∀ (i : Fin m) (j : Fin n),
        b i j = ∫ ω, Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) ∂μ) ∧
      ∃ (c : Fin m → Fin n → ℝ),
        (∀ (i : Fin m) (j : Fin n),
          c i j = Real.sqrt
            (∫ ω, (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂μ)) ∧
        (∀ (i : Fin m) (j : Fin n), 0 < c i j) ∧
        ∃ (XT : Ω → Matrix (Fin m) (Fin n) ℝ),
          (∀ (ω : Ω) (i : Fin m) (j : Fin n),
            XT ω i j =
              (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j) ∧
          (∀ (i : Fin m) (j : Fin n), ∫ ω, XT ω i j ∂μ = 0) ∧
          (∀ (i : Fin m) (j : Fin n), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1) ∧
          (∀ (ω : Ω) (i : Fin m) (j : Fin n), |XT ω i j| ≤ 3 * L) ∧
          (μ {ω : Ω | ∃ (i : Fin m) (j : Fin n), L < |Xi ω i j|} ≤
            ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10)))) ∧
                                  (∀ (ω : Ω), (∀ (i : Fin m) (j : Fin n), |Xi ω i j| ≤ L) →
                                    svals (maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω))
                                        ⟨0, by omega⟩ ≤
                                      Real.rpow (n : ℝ) (-(D0 + 5))) := by
  /- @proof-region region.target-node.session.926e308f7ee290c9 begin -/
  intro D0 hD0 Kt hKt alpha0 halpha0 rhoMinus hrho_pos hrho_le_one CD hCD m n hm hn hnm
    hrho_lo hrho_hi p hp0 hp1 hsparse L hL Ω mΩ μ iP Xi Mask hXi_meas hXi_int hXi_sq_int
    hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val hMask_law hMask_indep hIndep
  let Y : Fin m → Fin n → Ω → ℝ :=
    fun i j ω => Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0)
  let b : Fin m → Fin n → ℝ :=
    fun i j => ∫ ω, Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) ∂μ
  let c : Fin m → Fin n → ℝ :=
    fun i j => Real.sqrt
      (∫ ω, (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂μ)
  let XT : Ω → Matrix (Fin m) (Fin n) ℝ :=
    fun ω i j => (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j
  have hYunfold : ∀ (i : Fin m) (j : Fin n) (ω : Ω),
      Y i j ω = Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) := fun i j ω => rfl
  have hYmeas : ∀ (i : Fin m) (j : Fin n), Measurable (Y i j) := by
    intro i j
    have hm : Measurable fun ω => Xi ω i j := hXi_meas i j
    have habs : Measurable fun ω => |Xi ω i j| := continuous_abs.measurable.comp hm
    have hpre : MeasurableSet ((fun ω : Ω => |Xi ω i j|) ⁻¹' Set.Iic L) :=
      habs measurableSet_Iic
    have hset : MeasurableSet {ω : Ω | |Xi ω i j| ≤ L} := by
      simpa only [Set.mem_preimage, Set.mem_Iic] using hpre
    have h1 : Measurable fun ω =>
        Xi ω i j * (if ω ∈ {ω : Ω | |Xi ω i j| ≤ L} then (1 : ℝ) else 0) :=
      hm.mul (Measurable.ite hset measurable_const measurable_const)
    exact h1
  have hK1 : (1 : ℝ) ≤ (Kt + 1) ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ Kt + 1)
  have hD1 : (1 : ℝ) ≤ (D0 + 1) ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ D0 + 1)
  have hA1 : (1 : ℝ) ≤ (alpha0 + 1) ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ alpha0 + 1)
  have hDA : (1 : ℝ) ≤ (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by nlinarith only [hD1, hA1]
  have hK0 : (0 : ℝ) ≤ 10 ^ 6 * (Kt + 1) ^ 4 := by nlinarith only [hK1]
  have hstep : (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 ≤
      10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
    have hle := mul_le_mul_of_nonneg_left hDA hK0
    calc (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 = (10 ^ 6 * (Kt + 1) ^ 4) * 1 := by ring
      _ ≤ (10 ^ 6 * (Kt + 1) ^ 4) * ((D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) := hle
      _ = 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by ring
  have hlog : (0 : ℝ) ≤ Real.log ((m : ℝ) * (n : ℝ)) := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      have h : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact Real.log_nonneg (by nlinarith [hm1, hn1])
  have hCDpos : 0 < CD :=
    lt_of_lt_of_le (mul_pos hKt (by linarith : (0 : ℝ) < D0 + 12)) hCD
  have hCDlog : 0 ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) :=
    mul_nonneg (le_of_lt hCDpos) hlog
  have hLbig : (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 ≤ L := by
    rw [hL]
    linarith only [hstep, hCDlog]
  have hL2 : (2 : ℝ) ≤ L := by
    have h2 : (2 : ℝ) ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 := by nlinarith only [hK1]
    linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hYbound : ∀ (i : Fin m) (j : Fin n) (ω : Ω), |Y i j ω| ≤ L := by
    intro i j ω
    rw [hYunfold i j ω]
    by_cases hle : |Xi ω i j| ≤ L
    · rw [if_pos hle, mul_one]
      exact hle
    · rw [if_neg hle, mul_zero, abs_zero]
      linarith
  have hYint : ∀ (i : Fin m) (j : Fin n), Integrable (Y i j) μ := by
    intro i j
    refine MeasureTheory.Integrable.of_bound (hYmeas i j).aestronglyMeasurable L ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hYbound i j ω
  have hdiffint : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω => Y i j ω - b i j) μ := by
    intro i j
    exact (hYint i j).sub (integrable_const (b i j))
  have hnn : ∀ (i : Fin m) (j : Fin n), 0 ≤ ∫ ω, (Y i j ω - b i j) ^ 2 ∂μ := by
    intro i j
    exact integral_nonneg fun ω => sq_nonneg (Y i j ω - b i j)
  have hc2 : ∀ (i : Fin m) (j : Fin n),
      c i j ^ 2 = ∫ ω, (Y i j ω - b i j) ^ 2 ∂μ := by
    intro i j
    exact Real.sq_sqrt (hnn i j)
  have hchild : ∀ (i : Fin m) (j : Fin n), (|b i j| ≤ 1) ∧ ((1 : ℝ) / 2 ≤ c i j) := by
    intro i j
    exact statopia_math_node_2318467292_e95fa886 μ (fun ω => Xi ω i j) Kt L hKt
      (hXi_meas i j) (hXi_int i j) (hXi_sq_int i j) (hXi_mean i j) (hXi_var i j)
      (hXi_tail i j) hLbig
  have hb1 : ∀ (i : Fin m) (j : Fin n), |b i j| ≤ 1 := fun i j => (hchild i j).1
  have hYb : ∀ (i : Fin m) (j : Fin n) (ω : Ω), |Y i j ω - b i j| ≤ L + 1 := by
    intro i j ω
    calc |Y i j ω - b i j| ≤ |Y i j ω| + |b i j| := abs_sub _ _
      _ ≤ L + 1 := by
        have h1 := hYbound i j ω
        have h2 := hb1 i j
        linarith
  have hsqint : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω => (Y i j ω - b i j) ^ 2) μ := by
    intro i j
    have hl : Measurable fun ω => Y i j ω - b i j := (hYmeas i j).sub measurable_const
    have hmeas : Measurable fun ω => (Y i j ω - b i j) ^ 2 := by
      simpa only [sq] using hl.mul hl
    refine MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable ((L + 1) ^ 2) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y i j ω - b i j))]
    have h := hYb i j ω
    have h1 : (0 : ℝ) ≤ L + 1 := by linarith
    rw [sq_le_sq, abs_of_nonneg h1]
    exact h
  have hcge : ∀ (i : Fin m) (j : Fin n), (1 : ℝ) / 2 ≤ c i j := fun i j => (hchild i j).2
  have hbig := statopia_math_node_298819435_21fe1421 D0 hD0 rhoMinus hrho_pos hrho_le_one Kt
    hKt alpha0 halpha0 m n hm hn hnm hrho_lo hrho_hi p hp0 hp1 hsparse CD hCDpos hCD μ Xi
    Mask hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val
    hMask_law hMask_indep hIndep L hL b (fun i j => rfl) c (fun i j => rfl) XT
    (fun ω i j => rfl)
  refine ⟨b, ?_, c, ?_, ?_, XT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rfl
  · intro i j
    rfl
  · intro i j
    linarith [hcge i j]
  · intro ω i j
    rfl
  · intro i j
    have hb : (∫ ω, Y i j ω ∂μ) = b i j := rfl
    have h0 : ∫ ω, (Y i j ω - b i j) ∂μ = 0 := by
      rw [integral_sub (hYint i j) (integrable_const (b i j)), hb]
      simp
    show ∫ ω, (Y i j ω - b i j) / c i j ∂μ = 0
    simp only [div_eq_mul_inv]
    rw [integral_mul_const, h0, zero_mul]
  · intro i j
    have hc0 : c i j ≠ 0 := by linarith [hcge i j]
    have hp : ∀ ω : Ω, ((Y i j ω - b i j) / c i j) ^ 2
        = (Y i j ω - b i j) ^ 2 * (c i j ^ 2)⁻¹ := by
      intro ω
      rw [div_pow, div_eq_mul_inv]
    show ∫ ω, ((Y i j ω - b i j) / c i j) ^ 2 ∂μ = 1
    simp only [hp]
    rw [integral_mul_const, ← hc2 i j]
    exact mul_inv_cancel₀ (pow_ne_zero 2 hc0)
  · intro ω i j
    have hc0 : 0 < c i j := by linarith [hcge i j]
    show |(Y i j ω - b i j) / c i j| ≤ 3 * L
    rw [abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
    have hnum : |Y i j ω - b i j| ≤ L + 1 := hYb i j ω
    have hstep1 : 3 * L * (1 / 2 : ℝ) ≤ 3 * L * c i j :=
      mul_le_mul_of_nonneg_left (hcge i j) (by linarith : (0 : ℝ) ≤ 3 * L)
    have hL3 : L + 1 ≤ 3 * L * (1 / 2 : ℝ) := by linarith
    exact le_trans hnum (le_trans hL3 hstep1)
  · exact hbig.2.2.2.2.2.2.2.2.1
  · intro ω hω
    have htrans := (hbig.2.2.2.2.2.2.2.2.2 ω hω).1
    have hsv :=
      statopia_math_node_3797206296_f8b95f54 m n
        (maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)) (by omega)
    rw [hsv]
    exact htrans
  /- @proof-region region.target-node.session.926e308f7ee290c9 end -/

end Statlib.Imported

