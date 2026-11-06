import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_33749604ca0940be1dc6
import ProverJobs.ResidualE2ESupport20261106.M_a8791fa1d3e4fe57b534

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
theorem statopia_math_node_1683139888_f744e102 : ∀ (D0 Kt alpha0 CD L : ℝ) (m n : ℕ)
    (hD0 : 0 < D0) (hKt : 0 < Kt) (h_alpha0 : 15 < alpha0) (hCD_pos : 0 < CD)
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
        10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xi : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ)
    (hXi_sq_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_mean : ∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0)
    (hXi_var : ∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
    (hXi_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
      μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (b c : Fin m → Fin n → ℝ)
    (hb : ∀ (i : Fin m) (j : Fin n),
      b i j = ∫ ω, Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) ∂μ)
    (hc : ∀ (i : Fin m) (j : Fin n),
      c i j = Real.sqrt (∫ ω, (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂μ)), ∀ (i : Fin m) (j : Fin n), 0 < c i j ∧ (1 : ℝ) / 2 ≤ c i j ∧ c i j ≤ 3 / 2 := by
  /- @proof-region region.target-node.session.df1ae50c5121e7a6 begin -/
  intro D0 Kt alpha0 CD L m n hD0 hKt h_alpha0 hCD_pos hm hn hL Ω hΩ μ hμ Xi hXi_meas hXi_int
    hXi_sq_int hXi_mean hXi_var hXi_tail b c hb hc i j
  haveI : IsProbabilityMeasure μ := hμ
  have hlog_nonneg : (0 : ℝ) ≤ Real.log ((m : ℝ) * (n : ℝ)) := by
    refine Real.log_nonneg ?_
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (m : ℝ) * (n : ℝ) := mul_le_mul h1 h2 zero_le_one (by linarith)
  have sqge : ∀ x : ℝ, 1 ≤ x → 1 ≤ x ^ 2 := by
    intro x hx
    nlinarith [hx, sq_nonneg (x - 1)]
  have pow4ge : ∀ x : ℝ, 1 ≤ x → 1 ≤ x ^ 4 := by
    intro x hx
    have h2 : (1 : ℝ) ≤ x ^ 2 := sqge x hx
    have h4 : (1 : ℝ) ≤ (x ^ 2) ^ 2 := sqge (x ^ 2) h2
    calc (1 : ℝ) ≤ (x ^ 2) ^ 2 := h4
      _ = x ^ 4 := by ring
  have hK4 : (1 : ℝ) ≤ (Kt + 1) ^ 4 := pow4ge _ (by linarith)
  have hD4 : (1 : ℝ) ≤ (D0 + 1) ^ 4 := pow4ge _ (by linarith)
  have hal4 : (1 : ℝ) ≤ (alpha0 + 1) ^ 4 := pow4ge _ (by linarith)
  have hprod : (1 : ℝ) ≤ (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
    have h12 : (1 : ℝ) ≤ (Kt + 1) ^ 4 * (D0 + 1) ^ 4 := by
      calc (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ (Kt + 1) ^ 4 * (D0 + 1) ^ 4 := mul_le_mul hK4 hD4 zero_le_one (by linarith)
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ ((Kt + 1) ^ 4 * (D0 + 1) ^ 4) * (alpha0 + 1) ^ 4 :=
          mul_le_mul h12 hal4 zero_le_one (by linarith)
  have hLge : (2 : ℝ) ≤ L := by
    have hT : (2 : ℝ) ≤ 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
      calc (2 : ℝ) ≤ 10 ^ 6 := by norm_num
        _ = 10 ^ 6 * 1 := by ring
        _ ≤ 10 ^ 6 * ((Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) :=
            mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ = 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by ring
    have hcd : (0 : ℝ) ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) :=
      mul_nonneg hCD_pos.le hlog_nonneg
    rw [hL]
    linarith
  have hLpos : (0 : ℝ) < L := by linarith
  let ξ : Ω → ℝ := fun ω => Xi ω i j
  let Y : Ω → ℝ := fun ω => ξ ω * (if |ξ ω| ≤ L then (1 : ℝ) else 0)
  let Z : Ω → ℝ := fun ω => (ξ ω) ^ 2 * (if |ξ ω| ≤ L then (0 : ℝ) else 1)
  have hYv : ∀ ω : Ω, Y ω = ξ ω * (if |ξ ω| ≤ L then (1 : ℝ) else 0) := fun ω => rfl
  have hZv : ∀ ω : Ω, Z ω = (ξ ω) ^ 2 * (if |ξ ω| ≤ L then (0 : ℝ) else 1) := fun ω => rfl
  have hξ_meas : Measurable ξ := hXi_meas i j
  have hξ_int : Integrable ξ μ := hXi_int i j
  have hξ_sq_int : Integrable (fun ω => (ξ ω) ^ 2) μ := hXi_sq_int i j
  have hξ_mean : ∫ ω, ξ ω ∂μ = 0 := hXi_mean i j
  have hξ_var : ∫ ω, (ξ ω) ^ 2 ∂μ = 1 := hXi_var i j
  have hξ_tail : ∀ t : ℝ, 0 < t →
      μ {ω | t < |ξ ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)) :=
    fun t ht => hXi_tail i j t ht
  have hSmeas : MeasurableSet {ω : Ω | |ξ ω| ≤ L} :=
    measurableSet_le (continuous_abs.measurable.comp hξ_meas) measurable_const
  have hI1meas : Measurable fun ω : Ω => if |ξ ω| ≤ L then (1 : ℝ) else 0 :=
    Measurable.ite hSmeas measurable_const measurable_const
  have hI2meas : Measurable fun ω : Ω => if |ξ ω| ≤ L then (0 : ℝ) else 1 :=
    Measurable.ite hSmeas measurable_const measurable_const
  have hY_eq : Y = Set.indicator {ω : Ω | |ξ ω| ≤ L} ξ := by
    funext ω
    rw [hYv ω, Set.indicator_apply]
    by_cases hh : |ξ ω| ≤ L
    · simp [if_pos hh, hh]
    · simp [if_neg hh, hh]
  have hY_int : Integrable Y μ := by
    rw [hY_eq]
    exact hξ_int.indicator hSmeas
  have hZ_eq : Z = Set.indicator {ω : Ω | ¬ (|ξ ω| ≤ L)} (fun ω => (ξ ω) ^ 2) := by
    funext ω
    rw [hZv ω, Set.indicator_apply]
    by_cases hh : |ξ ω| ≤ L
    · simp [if_pos hh, hh]
    · simp [if_neg hh, hh]
  have hZ_int : Integrable Z μ := by
    rw [hZ_eq]
    exact hξ_sq_int.indicator hSmeas.compl
  have hYsq_ind : (fun ω : Ω => (Y ω) ^ 2)
      = Set.indicator {ω : Ω | |ξ ω| ≤ L} (fun ω => (ξ ω) ^ 2) := by
    funext ω
    rw [hYv ω, Set.indicator_apply]
    by_cases hh : |ξ ω| ≤ L
    · simp [if_pos hh, hh]
    · simp [if_neg hh, hh]
  have hYsq_int : Integrable (fun ω : Ω => (Y ω) ^ 2) μ := by
    rw [hYsq_ind]
    exact hξ_sq_int.indicator hSmeas
  obtain ⟨hmomA, hmomB⟩ :=
    statopia_math_node_895243969_77380b6a μ ξ Kt L hKt hLpos hξ_meas hξ_int hξ_mean hξ_sq_int
      hξ_var hξ_tail hY_int hZ_int
  obtain ⟨hsharpQ, hsharpb⟩ :=
    statopia_math_node_3865474750_001c1756 L Kt CD D0 alpha0 m n hKt hD0 h_alpha0 hCD_pos hm hn hL
  have hYint_eq : ∫ ω, Y ω ∂μ = b i j := (hb i j).symm
  have hQle : ∫ ω, Z ω ∂μ ≤ 1 / 16 := le_trans hmomB hsharpQ
  have hb_abs : |b i j| ≤ 1 / 4 := by
    rw [show b i j = ∫ ω, Y ω ∂μ from hYint_eq.symm]
    exact le_trans hmomA hsharpb
  have hb2 : (b i j) ^ 2 ≤ 1 / 16 := by
    have habs := abs_le.mp hb_abs
    nlinarith [habs.1, habs.2]
  have hsplit : (fun ω : Ω => (Y ω) ^ 2 + Z ω) = fun ω => (ξ ω) ^ 2 := by
    funext ω
    by_cases h : |ξ ω| ≤ L
    · simp [hYv ω, hZv ω, if_pos h]
    · simp [hYv ω, hZv ω, if_neg h]
  have hYsq_add : ∫ ω, (Y ω) ^ 2 ∂μ + ∫ ω, Z ω ∂μ = 1 := by
    rw [← integral_add hYsq_int hZ_int, hsplit, hξ_var]
  have hYsq_eq : ∫ ω, (Y ω) ^ 2 ∂μ = 1 - ∫ ω, Z ω ∂μ := by linarith
  have hinner_nonneg : (0 : ℝ) ≤ ∫ ω, (Y ω - b i j) ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  have hcsq' : c i j = Real.sqrt (∫ ω, (Y ω - b i j) ^ 2 ∂μ) := hc i j
  have hBint : Integrable (fun ω => (-(2 * (b i j))) * Y ω) μ :=
    hY_int.const_mul (-(2 * (b i j)))
  have hCint : Integrable (fun ω : Ω => (b i j) ^ 2) μ := integrable_const _
  have hconst : (∫ ω : Ω, (b i j) ^ 2 ∂μ) = (b i j) ^ 2 := by simp
  have hcongr : (fun ω : Ω => (Y ω - b i j) ^ 2)
      = fun ω => (Y ω) ^ 2 + (-(2 * (b i j))) * Y ω + (b i j) ^ 2 := by
    funext ω
    ring
  have hterm : ∫ ω, (Y ω - b i j) ^ 2 ∂μ
      = ∫ ω, ((Y ω) ^ 2 + (-(2 * (b i j))) * Y ω + (b i j) ^ 2) ∂μ := by
    rw [hcongr]
  have hA : ∫ ω, ((Y ω) ^ 2 + (-(2 * (b i j))) * Y ω + (b i j) ^ 2) ∂μ
      = ∫ ω, ((Y ω) ^ 2 + (-(2 * (b i j))) * Y ω) ∂μ + ∫ ω, (b i j) ^ 2 ∂μ :=
    integral_add (hYsq_int.add hBint) hCint
  have hB : ∫ ω, ((Y ω) ^ 2 + (-(2 * (b i j))) * Y ω) ∂μ
      = ∫ ω, (Y ω) ^ 2 ∂μ + ∫ ω, (-(2 * (b i j))) * Y ω ∂μ :=
    integral_add hYsq_int hBint
  have hC : ∫ ω, (-(2 * (b i j))) * Y ω ∂μ = (-(2 * (b i j))) * ∫ ω, Y ω ∂μ :=
    integral_const_mul_of_integrable (c := -(2 * (b i j))) hY_int
  have hexp : ∫ ω, (Y ω - b i j) ^ 2 ∂μ
      = ∫ ω, (Y ω) ^ 2 ∂μ + (-(2 * (b i j))) * (∫ ω, Y ω ∂μ) + (b i j) ^ 2 := by
    rw [hterm, hA, hB, hC, hconst]
  have hcsq : (c i j) ^ 2 = 1 - ∫ ω, Z ω ∂μ - (b i j) ^ 2 := by
    have hsq : (Real.sqrt (∫ ω, (Y ω - b i j) ^ 2 ∂μ)) ^ 2 = ∫ ω, (Y ω - b i j) ^ 2 ∂μ := by
      rw [pow_two]
      exact Real.mul_self_sqrt hinner_nonneg
    rw [hcsq', hsq, hexp, hYint_eq, hYsq_eq]
    ring
  have hZ_nonneg : (0 : ℝ) ≤ ∫ ω, Z ω ∂μ := by
    refine integral_nonneg fun ω => ?_
    rw [hZv ω]
    by_cases h : |ξ ω| ≤ L
    · rw [if_pos h]; simp
    · rw [if_neg h]; positivity
  have hc2_ge : (7 / 8 : ℝ) ≤ (c i j) ^ 2 := by
    rw [hcsq]
    linarith
  have hc2_le : (c i j) ^ 2 ≤ 1 := by
    rw [hcsq]
    linarith [sq_nonneg (b i j)]
  have hc_nonneg : (0 : ℝ) ≤ c i j := by
    rw [hcsq']
    exact Real.sqrt_nonneg _
  have hcsq_sqrt : Real.sqrt ((c i j) ^ 2) = c i j := Real.sqrt_sq hc_nonneg
  refine ⟨?_, ?_, ?_⟩
  · rcases eq_or_lt_of_le hc_nonneg with h0 | h0
    · rw [← h0] at hc2_ge
      norm_num at hc2_ge
    · linarith
  · have h4 : (1 / 4 : ℝ) ≤ (c i j) ^ 2 := by linarith
    have hs := Real.sqrt_le_sqrt h4
    rw [hcsq_sqrt] at hs
    have h14 : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  · have hs := Real.sqrt_le_sqrt hc2_le
    rw [hcsq_sqrt, Real.sqrt_one] at hs
    linarith
  /- @proof-region region.target-node.session.df1ae50c5121e7a6 end -/

end Statlib.Imported

