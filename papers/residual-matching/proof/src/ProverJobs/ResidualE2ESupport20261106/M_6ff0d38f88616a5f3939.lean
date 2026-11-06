import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_672368337bcecb533534
import ProverJobs.ResidualE2ESupport20261106.M_603be9b01d60bdf91269
import ProverJobs.ResidualE2ESupport20261106.M_59cea9764fdceee5a11a
import ProverJobs.ResidualE2ESupport20261106.M_6ceb7bf91d3ff5e77ab8

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
theorem statopia_math_node_467938922_fa16f85f : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D0 Kt alpha0 CD L p : ℝ) (m n : ℕ)
    (hD0 : 0 < D0) (hKt : 0 < Kt) (h_alpha0 : 15 < alpha0) (hCD_pos : 0 < CD)
    (hCD_ge : Kt * (D0 + 12) ≤ CD)
    (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
        10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ) (b c : Fin m → Fin n → ℝ)
    (XT : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ)
    (hXi_sq_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_var : ∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
    (hb : ∀ (i : Fin m) (j : Fin n),
        b i j = ∫ ω, Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) ∂μ)
    (hc : ∀ (i : Fin m) (j : Fin n),
        c i j = Real.sqrt (∫ ω, (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂μ))
    (hXT : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
        XT ω i j = (Xi ω i j * (if |Xi ω i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j)
    (hcrange : ∀ (i : Fin m) (j : Fin n), 0 < c i j ∧ (1 : ℝ) / 2 ≤ c i j ∧ c i j ≤ 3 / 2)
    (hb_sharp : ∀ (i : Fin m) (j : Fin n), |b i j| ≤ 2 * (L + Kt) * Real.exp (-L / Kt))
    (hQ_sharp : ∀ (i : Fin m) (j : Fin n),
        ∫ ω, (Xi ω i j) ^ 2 * (if |Xi ω i j| ≤ L then (0 : ℝ) else 1) ∂μ
          ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt)),
    ∀ (ω : Ω), (∀ (i : Fin m) (j : Fin n), |Xi ω i j| ≤ L) →
      (‖maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)‖
          ≤ Real.rpow (n : ℝ) (-(D0 + 5)) ∧
        ∀ (k : Fin n),
          |svals (maskedScaled p (Xi ω) (Mask ω)) k -
              svals (maskedScaled p (XT ω) (Mask ω)) k| ≤ Real.rpow (n : ℝ) (-(D0 + 5))) := by
  /- @proof-region region.target-node.session.2653f1e92da9a359 begin -/
  intro Ω hΩ μ hμ D0 Kt alpha0 CD L p m n
  intro hD0 hKt h_alpha0 hCD_pos hCD_ge hm hn hnm hp0 hp1 hsparse hL
  intro Xi Mask b c XT
  intro hMask_meas hMask_val hXi_meas hXi_int hXi_sq_int hXi_var hb hc hXT hcrange hb_sharp hQ_sharp
  intro ω hω
  have hLpos : 0 < L := by
    rw [hL]
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := by
      apply Real.log_nonneg
      nlinarith
    have hT : (0 : ℝ) < 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
      positivity
    have hcd : 0 ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := mul_nonneg hCD_pos.le hlog
    linarith
  set epsL : ℝ := 24 * (L + Kt) ^ 3 * Real.exp (-L / Kt) with hepsL_def
  have hL0 : 0 ≤ L := hLpos.le
  have hKt1 : (1 : ℝ) ≤ Kt + 1 := by linarith
  have hD01 : (1 : ℝ) ≤ D0 + 1 := by linarith
  have hKtp : (1 : ℝ) ≤ (Kt + 1) ^ 4 := by
    have h2 : (1 : ℝ) ^ 4 ≤ (Kt + 1) ^ 4 := by gcongr
    simpa using h2
  have hD0p : (1 : ℝ) ≤ (D0 + 1) ^ 4 := by
    have h2 : (1 : ℝ) ^ 4 ≤ (D0 + 1) ^ 4 := by gcongr
    simpa using h2
  have ha01 : (1 : ℝ) ≤ alpha0 + 1 := by linarith
  have ha0p : (1 : ℝ) ≤ (alpha0 + 1) ^ 4 := by
    have h2 : (1 : ℝ) ^ 4 ≤ (alpha0 + 1) ^ 4 := by gcongr
    simpa using h2
  have hLK1 : 1 ≤ L + Kt := by
    have hlog : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := by
      apply Real.log_nonneg
      have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
      have h2 := mul_le_mul h1 hn1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ (m : ℝ))
      simpa using h2
    have hcd : 0 ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := mul_nonneg hCD_pos.le hlog
    have hT1 : (1 : ℝ) ≤ 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
      have h10 : (1 : ℝ) ≤ 10 ^ 6 := by norm_num
      have hA : (1 : ℝ) ≤ 10 ^ 6 * (Kt + 1) ^ 4 := by
        have h := mul_le_mul h10 hKtp (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
        simpa using h
      have hB : (1 : ℝ) ≤ 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 := by
        have h := mul_le_mul hA hD0p (by norm_num : (0 : ℝ) ≤ 1)
          (by positivity : (0 : ℝ) ≤ 10 ^ 6 * (Kt + 1) ^ 4)
        simpa using h
      have h := mul_le_mul hB ha0p (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4)
      simpa using h
    rw [hL]
    linarith
  have hentry : ∀ (i : Fin m) (j : Fin n), |XT ω i j - Xi ω i j| ≤ epsL := by
    rw [hepsL_def]
    intro i j
    exact statopia_math_node_500654225_d67edb99 μ Kt L m n hKt hL0 hLK1 Xi b c XT hXi_meas
      hXi_int hXi_sq_int hXi_var hb hc hXT hcrange hb_sharp hQ_sharp ω hω i j
  have hsum : (∑ i : Fin m, ∑ j : Fin n,
      ((maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)) i j) ^ 2)
      ≤ (n : ℝ) * epsL ^ 2 / p := by
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hmp : (0 : ℝ) < (m : ℝ) * p := mul_pos hm0 hp0
    have hepsL0 : 0 ≤ epsL := by
      rw [hepsL_def]
      have hLK : (0 : ℝ) ≤ L + Kt := by linarith
      have h1 : (0 : ℝ) ≤ (L + Kt) ^ 3 := pow_nonneg hLK 3
      have h2 : (0 : ℝ) ≤ Real.exp (-L / Kt) := (Real.exp_pos _).le
      exact mul_nonneg (mul_nonneg (by norm_num) h1) h2
    have hent : ∀ (i : Fin m) (j : Fin n),
        ((maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)) i j) ^ 2
          ≤ epsL ^ 2 / ((m : ℝ) * p) := by
      intro i j
      have hsq : (Xi ω i j - XT ω i j) ^ 2 ≤ epsL ^ 2 := by
        have h1 := abs_le.mp (hentry i j)
        have h2 : (0 : ℝ) ≤ epsL - (XT ω i j - Xi ω i j) := by linarith [h1.2]
        have h3 : (0 : ℝ) ≤ epsL + (XT ω i j - Xi ω i j) := by linarith [h1.1]
        have h4 : (0 : ℝ) ≤ (epsL - (XT ω i j - Xi ω i j)) * (epsL + (XT ω i j - Xi ω i j)) :=
          mul_nonneg h2 h3
        nlinarith [h4]
      have hmask2 : (Mask ω i j) ^ 2 ≤ 1 := by
        rcases hMask_val i j ω with h0 | h1
        · rw [h0]; norm_num
        · rw [h1]; norm_num
      have hexp : (maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)) i j
          = Mask ω i j * (Xi ω i j - XT ω i j) / Real.sqrt ((m : ℝ) * p) := by
        show Mask ω i j * Xi ω i j / Real.sqrt ((m : ℝ) * p) -
            Mask ω i j * XT ω i j / Real.sqrt ((m : ℝ) * p)
          = Mask ω i j * (Xi ω i j - XT ω i j) / Real.sqrt ((m : ℝ) * p)
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [hexp, div_pow, mul_pow, Real.sq_sqrt hmp.le]
      have hnum : (Mask ω i j) ^ 2 * (Xi ω i j - XT ω i j) ^ 2 ≤ epsL ^ 2 := by
        have h1 : (Mask ω i j) ^ 2 * (Xi ω i j - XT ω i j) ^ 2 ≤ 1 * epsL ^ 2 :=
          mul_le_mul hmask2 hsq (sq_nonneg _) (by norm_num)
        linarith [h1]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hmp.le)
    calc (∑ i : Fin m, ∑ j : Fin n,
        ((maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)) i j) ^ 2)
        ≤ ∑ i : Fin m, ∑ j : Fin n, epsL ^ 2 / ((m : ℝ) * p) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
      _ = (n : ℝ) * epsL ^ 2 / p := by
          have hmp' : (m : ℝ) * p ≠ 0 := ne_of_gt hmp
          have hp0' : p ≠ 0 := ne_of_gt hp0
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          field_simp
  have hop_le : ‖maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)‖
      ≤ Real.sqrt ((n : ℝ) * epsL ^ 2 / p) := by
    refine le_trans (statopia_math_node_1409213541_c481236b m n _) ?_
    exact Real.sqrt_le_sqrt hsum
  have harith : Real.sqrt ((n : ℝ) * epsL ^ 2 / p) ≤ Real.rpow (n : ℝ) (-(D0 + 5)) := by
    rw [hepsL_def]
    exact statopia_math_node_1813084325_ae3c2094 D0 Kt alpha0 CD L p m n hD0 hKt h_alpha0
      hCD_pos hCD_ge hm hn hnm hp0 hp1 hsparse hL
  have hop : ‖maskedScaled p (Xi ω) (Mask ω) - maskedScaled p (XT ω) (Mask ω)‖
      ≤ Real.rpow (n : ℝ) (-(D0 + 5)) := le_trans hop_le harith
  refine ⟨hop, ?_⟩
  intro k
  exact le_trans (statopia_math_node_1482569421_d5eba7e6
    (maskedScaled p (Xi ω) (Mask ω)) (maskedScaled p (XT ω) (Mask ω)) k) hop
  /- @proof-region region.target-node.session.2653f1e92da9a359 end -/

end Statlib.Imported

