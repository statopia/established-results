import Lean
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

set_option autoImplicit false in
theorem statopia_math_node_500654225_d67edb99 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Kt L : ℝ) (m n : ℕ)
    (hKt : 0 < Kt) (hL0 : 0 ≤ L) (hLK : 1 ≤ L + Kt)
    (Xi : Ω → Matrix (Fin m) (Fin n) ℝ) (b c : Fin m → Fin n → ℝ)
    (XT : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ)
    (hXi_sq_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_var : ∀ (i : Fin m) (j : Fin n), ∫ (ω : Ω), (Xi ω i j) ^ 2 ∂μ = 1)
    (hb : ∀ (i : Fin m) (j : Fin n),
      b i j = ∫ (ω : Ω), Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) ∂μ)
    (hc : ∀ (i : Fin m) (j : Fin n),
      c i j = Real.sqrt
        (∫ (ω : Ω), (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂μ))
    (hXT : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
      XT ω i j = (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j)
    (hcrange : ∀ (i : Fin m) (j : Fin n), 0 < c i j ∧ (1 : ℝ) / 2 ≤ c i j ∧ c i j ≤ 3 / 2)
    (hb_sharp : ∀ (i : Fin m) (j : Fin n), |b i j| ≤ 2 * (L + Kt) * Real.exp (-L / Kt))
    (hQ_sharp : ∀ (i : Fin m) (j : Fin n),
      ∫ (ω : Ω), (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1) ∂μ
        ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt)),
    ∀ (ω : Ω), (∀ (i : Fin m) (j : Fin n), |Xi ω i j| ≤ L) →
      ∀ (i : Fin m) (j : Fin n),
        |XT ω i j - Xi ω i j| ≤ 24 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := by
  /- @proof-region region.target-node.session.67c6d47a7130544a begin -/
  intro Ω instΩ μ instμ Kt L m n hKt hL0 hLK Xi b c XT hXi_meas hXi_int hXi_sq_int hXi_var hb hc hXT hcrange hb_sharp hQ_sharp ω hω i j
  obtain ⟨hc_pos, hc_half, _⟩ := hcrange i j
  have hcne : c i j ≠ 0 := ne_of_gt hc_pos
  set Y : Ω → ℝ := fun ω => Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) with hY
  set Q : ℝ := ∫ (ω : Ω), (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1) ∂μ with hQ
  have hs : MeasurableSet {ω : Ω | |Xi ω i j| ≤ L} := by
    have hm : Measurable fun ω : Ω => |Xi ω i j| := (hXi_meas i j).abs
    have h : MeasurableSet ((fun ω : Ω => |Xi ω i j|) ⁻¹' Set.Iic L) := hm measurableSet_Iic
    have hEq : ((fun ω : Ω => |Xi ω i j|) ⁻¹' Set.Iic L) = {ω : Ω | |Xi ω i j| ≤ L} := by
      ext ω
      simp
    rwa [hEq] at h
  have hY_eq_ind : Y = {ω : Ω | |Xi ω i j| ≤ L}.indicator (fun ω => Xi ω i j) := by
    funext ω
    rw [hY]
    by_cases h : |Xi ω i j| ≤ L <;> simp [h]
  have hY_int : Integrable Y μ := by
    rw [hY_eq_ind]
    exact (hXi_int i j).indicator hs
  have hY2_eq_ind : (fun ω : Ω => Y ω ^ 2)
      = {ω : Ω | |Xi ω i j| ≤ L}.indicator (fun ω => (Xi ω i j) ^ 2) := by
    funext ω
    rw [hY]
    by_cases h : |Xi ω i j| ≤ L <;> simp [h]
  have hY2_int : Integrable (fun ω : Ω => Y ω ^ 2) μ := by
    rw [hY2_eq_ind]
    exact (hXi_sq_int i j).indicator hs
  have hQf_eq_ind : (fun ω : Ω => (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1))
      = ({ω : Ω | |Xi ω i j| ≤ L} : Set Ω)ᶜ.indicator (fun ω => (Xi ω i j) ^ 2) := by
    funext ω
    by_cases h : |Xi ω i j| ≤ L <;> simp [h]
  have hQf_int : Integrable (fun ω : Ω => (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1)) μ := by
    rw [hQf_eq_ind]
    exact (hXi_sq_int i j).indicator hs.compl
  have hYint_eq : ∫ ω, Y ω ∂μ = b i j := by
    rw [hY]
    exact (hb i j).symm
  have hpt : ∀ ω : Ω, Y ω ^ 2 + (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1) = (Xi ω i j) ^ 2 := by
    intro ω
    rw [hY]
    by_cases h : |Xi ω i j| ≤ L <;> simp [h]
  have hQ_nonneg : 0 ≤ Q := by
    rw [hQ]
    refine integral_nonneg fun ω => ?_
    have h1 : (0 : ℝ) ≤ (if |Xi ω i j| ≤ L then (0 : ℝ) else 1) := by split_ifs <;> norm_num
    exact mul_nonneg (sq_nonneg _) h1
  have hQ_le : Q ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) := by
    rw [hQ]
    exact hQ_sharp i j
  have hsum : ∫ ω, Y ω ^ 2 ∂μ + ∫ ω, (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1) ∂μ = 1 := by
    have hadd : ∫ ω, (Y ω ^ 2 + (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1)) ∂μ
        = ∫ ω, Y ω ^ 2 ∂μ + ∫ ω, (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1) ∂μ :=
      integral_add hY2_int hQf_int
    rw [← hadd]
    simpa only [hpt] using hXi_var i j
  have hA : ∫ ω, Y ω ^ 2 ∂μ = 1 - Q := by
    rw [hQ]
    linarith [hsum]
  have hRealUniv : μ.real Set.univ = 1 := by
    show (μ Set.univ).toReal = 1
    rw [instμ.measure_univ]
    simp
  have hbY_int : Integrable (fun ω : Ω => b i j * Y ω) μ := hY_int.const_mul (b i j)
  have hB : ∫ ω, (Y ω - b i j) ^ 2 ∂μ = 1 - Q - (b i j) ^ 2 := by
    have h1 : ∫ ω, (Y ω - b i j) ^ 2 ∂μ
        = ∫ ω, (Y ω ^ 2 - 2 * (b i j * Y ω) + b i j * b i j) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    have h2 : ∫ ω, (Y ω ^ 2 - 2 * (b i j * Y ω) + b i j * b i j) ∂μ
        = (∫ ω, Y ω ^ 2 ∂μ - 2 * ∫ ω, b i j * Y ω ∂μ) + b i j * b i j := by
      have hP1 : ∫ ω, (Y ω ^ 2 - 2 * (b i j * Y ω) + b i j * b i j) ∂μ
          = ∫ ω, (Y ω ^ 2 - 2 * (b i j * Y ω)) ∂μ + ∫ ω, (b i j * b i j) ∂μ :=
        integral_add (hY2_int.sub (hbY_int.const_mul 2)) (integrable_const (b i j * b i j))
      have hP2 : ∫ ω, (Y ω ^ 2 - 2 * (b i j * Y ω)) ∂μ
          = ∫ ω, Y ω ^ 2 ∂μ - ∫ ω, 2 * (b i j * Y ω) ∂μ :=
        integral_sub hY2_int (hbY_int.const_mul 2)
      have hP3 : ∫ ω, 2 * (b i j * Y ω) ∂μ = 2 * ∫ ω, b i j * Y ω ∂μ :=
        integral_const_mul 2 (fun ω : Ω => b i j * Y ω)
      have hP4 : ∫ ω, (b i j * b i j) ∂μ = b i j * b i j := by
        rw [integral_const, hRealUniv]
        simp
      rw [hP1, hP2, hP3, hP4]
    rw [h1, h2, integral_const_mul, hYint_eq, hA]
    ring
  have hnonneg : 0 ≤ ∫ ω, (Y ω - b i j) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hc_sq : c i j ^ 2 = 1 - Q - (b i j) ^ 2 := by
    rw [hc i j, Real.sq_sqrt hnonneg]
    exact hB
  have hone : 1 - c i j ^ 2 = Q + (b i j) ^ 2 := by
    rw [hc_sq]
    ring
  have habs : |1 - c i j ^ 2| = Q + (b i j) ^ 2 := by
    rw [hone, abs_of_nonneg (add_nonneg hQ_nonneg (sq_nonneg (b i j)))]
  have hfac : |1 - c i j ^ 2| = |1 - c i j| * (1 + c i j) := by
    rw [← abs_of_pos (by linarith : (0 : ℝ) < 1 + c i j), ← abs_mul]
    congr 1
    ring
  have h1mc : |1 - c i j| ≤ |1 - c i j ^ 2| := by
    rw [hfac]
    nlinarith [mul_nonneg (abs_nonneg (1 - c i j)) (by linarith : (0 : ℝ) ≤ c i j)]
  have hEpos : 0 < Real.exp (-L / Kt) := Real.exp_pos _
  have hE1 : Real.exp (-L / Kt) ≤ 1 := by
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    have hdiv : 0 ≤ L / Kt := div_nonneg hL0 (le_of_lt hKt)
    have hneg : -L / Kt = -(L / Kt) := by ring
    rw [hneg]
    linarith
  have hE2le : Real.exp (-L / Kt) ^ 2 ≤ Real.exp (-L / Kt) := by
    nlinarith [mul_nonneg hEpos.le (sub_nonneg.mpr hE1)]
  have hb2a : (b i j) ^ 2 ≤ 4 * (L + Kt) ^ 2 * Real.exp (-L / Kt) ^ 2 := by
    calc (b i j) ^ 2 = |b i j| * |b i j| := by rw [← sq_abs, pow_two]
      _ ≤ (2 * (L + Kt) * Real.exp (-L / Kt)) * (2 * (L + Kt) * Real.exp (-L / Kt)) :=
          mul_self_le_mul_self (abs_nonneg _) (hb_sharp i j)
      _ = 4 * (L + Kt) ^ 2 * Real.exp (-L / Kt) ^ 2 := by ring
  have hb2 : (b i j) ^ 2 ≤ 4 * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
    have h4 : (0 : ℝ) ≤ 4 * (L + Kt) ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hE2le h4
    linarith [hb2a]
  have hdiff2 : XT ω i j - Xi ω i j = (Xi ω i j * (1 - c i j) - b i j) / c i j := by
    rw [hXT ω i j, if_pos (hω i j), mul_one]
    field_simp
    ring
  have htri : |Xi ω i j * (1 - c i j) - b i j| ≤ |Xi ω i j| * |1 - c i j| + |b i j| := by
    have h1 : |Xi ω i j * (1 - c i j) - b i j| ≤ |Xi ω i j * (1 - c i j)| + |b i j| := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;>
        nlinarith [le_abs_self (Xi ω i j * (1 - c i j)), neg_abs_le (Xi ω i j * (1 - c i j)),
          le_abs_self (b i j), neg_abs_le (b i j)]
    rwa [abs_mul] at h1
  have hstep1 : |XT ω i j - Xi ω i j| ≤ (|Xi ω i j| * |1 - c i j| + |b i j|) / c i j := by
    rw [hdiff2, abs_div, abs_of_pos hc_pos, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right htri (inv_nonneg.mpr (le_of_lt hc_pos))
  have h1mc' : |1 - c i j| ≤ Q + (b i j) ^ 2 := by
    rw [← habs]
    exact h1mc
  have hnum : |Xi ω i j| * |1 - c i j| + |b i j| ≤ L * (Q + (b i j) ^ 2) + |b i j| := by
    have hmul : |Xi ω i j| * |1 - c i j| ≤ L * (Q + (b i j) ^ 2) :=
      mul_le_mul (hω i j) h1mc' (abs_nonneg _) hL0
    linarith
  have hcinv : (c i j)⁻¹ ≤ 2 := by
    have h : 1 / c i j ≤ 1 / ((1 : ℝ) / 2) := one_div_le_one_div_of_le (by norm_num) hc_half
    have h2 : (1 : ℝ) / ((1 : ℝ) / 2) = 2 := by norm_num
    calc (c i j)⁻¹ = 1 / c i j := by rw [one_div]
      _ ≤ 1 / ((1 : ℝ) / 2) := h
      _ = 2 := h2
  have hstep2 : (|Xi ω i j| * |1 - c i j| + |b i j|) / c i j
      ≤ 2 * (L * (Q + (b i j) ^ 2) + |b i j|) := by
    have hAnn : (0 : ℝ) ≤ |Xi ω i j| * |1 - c i j| + |b i j| := by positivity
    rw [div_eq_mul_inv]
    calc (|Xi ω i j| * |1 - c i j| + |b i j|) * (c i j)⁻¹
        ≤ (|Xi ω i j| * |1 - c i j| + |b i j|) * 2 := mul_le_mul_of_nonneg_left hcinv hAnn
      _ ≤ (L * (Q + (b i j) ^ 2) + |b i j|) * 2 := mul_le_mul_of_nonneg_right hnum (by norm_num)
      _ = 2 * (L * (Q + (b i j) ^ 2) + |b i j|) := by ring
  have hmain : |XT ω i j - Xi ω i j| ≤ 2 * (L * (Q + (b i j) ^ 2) + |b i j|) := by
    linarith [hstep1, hstep2]
  have hLS : L ≤ L + Kt := by linarith
  have hKS : Kt ≤ L + Kt := by linarith
  have hSnn : (0 : ℝ) ≤ L + Kt := by linarith
  have hL2S2 : L ^ 2 ≤ (L + Kt) ^ 2 := by
    have h := mul_self_le_mul_self hL0 hLS
    simpa [pow_two] using h
  have hL3S3 : L ^ 3 ≤ (L + Kt) ^ 3 := by
    have h2 : L ^ 2 * L ≤ (L + Kt) ^ 2 * L := mul_le_mul_of_nonneg_right hL2S2 hL0
    have h3 : (L + Kt) ^ 2 * L ≤ (L + Kt) ^ 2 * (L + Kt) :=
      mul_le_mul_of_nonneg_left hLS (sq_nonneg (L + Kt))
    calc L ^ 3 = L ^ 2 * L := by ring
      _ ≤ (L + Kt) ^ 2 * L := h2
      _ ≤ (L + Kt) ^ 2 * (L + Kt) := h3
      _ = (L + Kt) ^ 3 := by ring
  have hKtS : Kt * (L + Kt) ≤ (L + Kt) ^ 2 := by
    have h : Kt * (L + Kt) ≤ (L + Kt) * (L + Kt) := mul_le_mul_of_nonneg_right hKS hSnn
    calc Kt * (L + Kt) ≤ (L + Kt) * (L + Kt) := h
      _ = (L + Kt) ^ 2 := by ring
  have hLKS : L * (Kt * (L + Kt)) ≤ (L + Kt) ^ 3 := by
    have hnn : (0 : ℝ) ≤ Kt * (L + Kt) := by positivity
    have h : L * (Kt * (L + Kt)) ≤ (L + Kt) * ((L + Kt) ^ 2) := mul_le_mul hLS hKtS hnn hSnn
    calc L * (Kt * (L + Kt)) ≤ (L + Kt) * ((L + Kt) ^ 2) := h
      _ = (L + Kt) ^ 3 := by ring
  have hLS2 : L * (L + Kt) ^ 2 ≤ (L + Kt) ^ 3 := by
    have h : L * (L + Kt) ^ 2 ≤ (L + Kt) * (L + Kt) ^ 2 :=
      mul_le_mul_of_nonneg_right hLS (sq_nonneg (L + Kt))
    calc L * (L + Kt) ^ 2 ≤ (L + Kt) * (L + Kt) ^ 2 := h
      _ = (L + Kt) ^ 3 := by ring
  have hS2 : (L + Kt) ≤ (L + Kt) ^ 2 := by
    have h : (L + Kt) * 1 ≤ (L + Kt) * (L + Kt) := mul_le_mul_of_nonneg_left hLK hSnn
    calc (L + Kt) = (L + Kt) * 1 := by ring
      _ ≤ (L + Kt) * (L + Kt) := h
      _ = (L + Kt) ^ 2 := by ring
  have hS3 : (L + Kt) ≤ (L + Kt) ^ 3 := by
    have hSQ : (L + Kt) ^ 2 ≤ (L + Kt) ^ 3 := by
      have h : (L + Kt) ^ 2 * 1 ≤ (L + Kt) ^ 2 * (L + Kt) :=
        mul_le_mul_of_nonneg_left hLK (sq_nonneg (L + Kt))
      calc (L + Kt) ^ 2 = (L + Kt) ^ 2 * 1 := by ring
        _ ≤ (L + Kt) ^ 2 * (L + Kt) := h
        _ = (L + Kt) ^ 3 := by ring
    exact le_trans hS2 hSQ
  have hA1 : 2 * L * Q ≤ (4 * L ^ 3 + 8 * (L * (Kt * (L + Kt)))) * Real.exp (-L / Kt) := by
    have h2L : (0 : ℝ) ≤ 2 * L := mul_nonneg (by norm_num) hL0
    have h := mul_le_mul_of_nonneg_left hQ_le h2L
    calc 2 * L * Q ≤ 2 * L * ((2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt)) := h
      _ = (4 * L ^ 3 + 8 * (L * (Kt * (L + Kt)))) * Real.exp (-L / Kt) := by ring
  have hA1' : 2 * L * Q ≤ 12 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := by
    have h4 : 4 * L ^ 3 ≤ 4 * (L + Kt) ^ 3 := mul_le_mul_of_nonneg_left hL3S3 (by norm_num)
    have h8 : 8 * (L * (Kt * (L + Kt))) ≤ 8 * (L + Kt) ^ 3 :=
      mul_le_mul_of_nonneg_left hLKS (by norm_num)
    calc 2 * L * Q ≤ (4 * L ^ 3 + 8 * (L * (Kt * (L + Kt)))) * Real.exp (-L / Kt) := hA1
      _ ≤ (4 * (L + Kt) ^ 3 + 8 * (L + Kt) ^ 3) * Real.exp (-L / Kt) :=
          mul_le_mul_of_nonneg_right (add_le_add h4 h8) hEpos.le
      _ = 12 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := by ring
  have hA2 : 2 * L * (b i j) ^ 2 ≤ 8 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := by
    have h2L : (0 : ℝ) ≤ 2 * L := mul_nonneg (by norm_num) hL0
    have h := mul_le_mul_of_nonneg_left hb2 h2L
    have h8 : 8 * (L * (L + Kt) ^ 2) ≤ 8 * (L + Kt) ^ 3 :=
      mul_le_mul_of_nonneg_left hLS2 (by norm_num)
    calc 2 * L * (b i j) ^ 2 ≤ 2 * L * (4 * (L + Kt) ^ 2 * Real.exp (-L / Kt)) := h
      _ = 8 * (L * (L + Kt) ^ 2) * Real.exp (-L / Kt) := by ring
      _ ≤ 8 * (L + Kt) ^ 3 * Real.exp (-L / Kt) :=
          mul_le_mul_of_nonneg_right h8 hEpos.le
  have hA3 : 2 * |b i j| ≤ 4 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := by
    have hb1 : 2 * |b i j| ≤ 2 * (2 * (L + Kt) * Real.exp (-L / Kt)) :=
      mul_le_mul_of_nonneg_left (hb_sharp i j) (by norm_num)
    have h4 : 4 * (L + Kt) ≤ 4 * (L + Kt) ^ 3 := mul_le_mul_of_nonneg_left hS3 (by norm_num)
    calc 2 * |b i j| ≤ 2 * (2 * (L + Kt) * Real.exp (-L / Kt)) := hb1
      _ = 4 * (L + Kt) * Real.exp (-L / Kt) := by ring
      _ ≤ 4 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := mul_le_mul_of_nonneg_right h4 hEpos.le
  have hfinal : 2 * (L * (Q + (b i j) ^ 2) + |b i j|) ≤ 24 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := by
    have h1 := add_le_add hA1' hA2
    have h2 := add_le_add h1 hA3
    have h3 : 2 * L * Q + 2 * L * (b i j) ^ 2 + 2 * |b i j|
        ≤ 24 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := by
      have hc : 12 * (L + Kt) ^ 3 * Real.exp (-L / Kt) + 8 * (L + Kt) ^ 3 * Real.exp (-L / Kt)
          + 4 * (L + Kt) ^ 3 * Real.exp (-L / Kt) = 24 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := by
        ring
      rw [hc] at h2
      exact h2
    have h4 : 2 * (L * (Q + (b i j) ^ 2) + |b i j|)
        = 2 * L * Q + 2 * L * (b i j) ^ 2 + 2 * |b i j| := by ring
    rw [h4]
    exact h3
  calc |XT ω i j - Xi ω i j| ≤ 2 * (L * (Q + (b i j) ^ 2) + |b i j|) := hmain
    _ ≤ 24 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := hfinal
  /- @proof-region region.target-node.session.67c6d47a7130544a end -/

end Statlib.Imported

