import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_9fda07d1f665f6d93763
import ProverJobs.ResidualE2ESupport20261106.M_603335f5be13fed88090
import ProverJobs.ResidualE2ESupport20261106.M_044cb30572bfcb4aec8e
import ProverJobs.ResidualE2ESupport20261106.M_6a5763320d58217f30a5
import ProverJobs.ResidualE2ESupport20261106.M_f112259cfc64c1dcb4f3
import ProverJobs.ResidualE2ESupport20261106.M_1eaf2b752f06fe72941e
import ProverJobs.ResidualE2ESupport20261106.M_1826cf4a199ca47d64c5
import ProverJobs.ResidualE2ESupport20261106.ExternalNodes.Node_4e757cd702eee1ecc4cb

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
theorem statopia_math_node_2849745169_758d55f9 : ∃ c1 : ℝ, 0 < c1 ∧
      ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
        (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus) (h_rhoMinus_le : rhoMinus ≤ 1)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
        (Kt : ℝ) (hKt : 0 < Kt)
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
        (z : ℂ) (hz : 0 < z.im),
        ‖(∫ ω, symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z ∂μ)
            - ∫ g : Matrix (Fin m) (Fin n) ℝ,
                symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z
              ∂(stdNormalMatrixMeasure m n)‖
          ≤ c1 * (1 + Kt) ^ 3 * ((1 + rhoMinus⁻¹) / 2) *
              (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹ := by
  /- @proof-region region.target-node.session.bcf4a73b7deb2e67 begin -/
  obtain ⟨C, hCpos, hC⟩ := statopia_math_node_2072908945_35593386

  refine ⟨24 * C + 1, by linarith, ?_⟩
  intro m n hm hn rhoMinus h_rhoMinus_pos h_rhoMinus_le hrho_lo hrho_hi p hp hp1 Kt hKt
  intro Ω mΩ μ hμ Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
    hMask_meas hMask_val hMask_law hMask_indep hIndep z hz
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure μ := hμ
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm


  have hR : (0 : ℝ) ≤ (Real.sqrt ((m : ℝ) * p))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg ((m : ℝ) * p))
  have hE : (0 : ℝ) ≤ (z.im ^ 4)⁻¹ := inv_nonneg.mpr (pow_nonneg (le_of_lt hz) 4)
  have hS1 : 1 ≤ (1 + rhoMinus⁻¹) / 2 := by
    have hinv : (1 : ℝ) ≤ rhoMinus⁻¹ := by
      have hprod : rhoMinus * rhoMinus⁻¹ = (1 : ℝ) := by field_simp
      have hle : rhoMinus * rhoMinus⁻¹ ≤ 1 * rhoMinus⁻¹ :=
        mul_le_mul_of_nonneg_right h_rhoMinus_le (inv_nonneg.mpr (le_of_lt h_rhoMinus_pos))
      rw [hprod, one_mul] at hle
      exact hle
    linarith
  have hSnn : (0 : ℝ) ≤ (1 + rhoMinus⁻¹) / 2 := by linarith
  have hnum : ∀ A : ℝ,
      A ≤ 24 * C * Kt ^ 3 * ((1 + rhoMinus⁻¹) / 2)
          * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹ →
      A ≤ (24 * C + 1) * (1 + Kt) ^ 3 * ((1 + rhoMinus⁻¹) / 2)
        * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹ := by
    intro A hA
    have h0 : (0 : ℝ) ≤ 24 * C := by linarith
    have hKt0 : (0 : ℝ) ≤ Kt := le_of_lt hKt
    have hp1Kt : (0 : ℝ) ≤ 1 + Kt := by linarith
    have hpow : Kt ^ 3 ≤ (1 + Kt) ^ 3 := by nlinarith [hKt0, sq_nonneg Kt]
    have hstep1 : 24 * C * Kt ^ 3 * ((1 + rhoMinus⁻¹) / 2) ≤
        24 * C * (1 + Kt) ^ 3 * ((1 + rhoMinus⁻¹) / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow h0) hSnn
    have hstep2 : 24 * C * (1 + Kt) ^ 3 * ((1 + rhoMinus⁻¹) / 2) ≤
        (24 * C + 1) * (1 + Kt) ^ 3 * ((1 + rhoMinus⁻¹) / 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show 24 * C ≤ 24 * C + 1 by linarith)
          (pow_nonneg hp1Kt 3)) hSnn
    have hmid := le_trans hstep1 hstep2
    exact le_trans hA (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmid hR) hE)
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have h : (0 : ℕ) < m := by omega
    exact_mod_cast h
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℕ) < n := by omega
    exact_mod_cast h
  have hmn_le : (m : ℝ) * rhoMinus ≤ (n : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hrho_lo (le_of_lt hmpos)
    have h2 : (m : ℝ) * ((n : ℝ) / (m : ℝ)) = (n : ℝ) := by field_simp
    rw [h2] at h1
    exact h1
  have hfac : ((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ)) ≤ (1 + rhoMinus⁻¹) / 2 := by
    field_simp
    nlinarith [hmn_le, hmpos, hnpos, h_rhoMinus_pos]
  have hYnn : (0 : ℝ) ≤
      24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹ := by
    have h0 : (0 : ℝ) ≤ 24 * C := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg h0 (pow_nonneg (le_of_lt hKt) 3)) hR) hE
  have hd0pos : (0 : ℝ) < (m : ℝ) + (n : ℝ) := by linarith


  have hd0ne : ((m : ℝ) + (n : ℝ)) ≠ 0 := ne_of_gt hd0pos


  have hterm : ∀ x : ℝ, ‖(((x : ℂ) - z))⁻¹‖ ≤ (z.im)⁻¹ := by
    intro x
    have h1 : (((x : ℂ) - z)).im = -z.im := by simp
    have h2 : |(((x : ℂ) - z)).im| ≤ ‖((x : ℂ) - z)‖ := Complex.abs_im_le_norm _
    rw [h1, abs_neg, abs_of_pos hz] at h2
    calc ‖(((x : ℂ) - z))⁻¹‖ = ‖((x : ℂ) - z)‖⁻¹ := norm_inv _
      _ ≤ (z.im)⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le hz h2
  have hterm' : ∀ x : ℝ, ‖(-(x : ℂ) - z)⁻¹‖ ≤ (z.im)⁻¹ := by
    intro x
    simpa using hterm (-x)
  have hsum : ∀ (s : Fin n → ℝ),
      ‖∑ i : Fin n, (((s i : ℂ) - z)⁻¹ + (-(s i : ℂ) - z)⁻¹)‖
        ≤ (n : ℝ) * (2 * (z.im)⁻¹) := by
    intro s
    calc ‖∑ i : Fin n, (((s i : ℂ) - z)⁻¹ + (-(s i : ℂ) - z)⁻¹)‖
        ≤ ∑ i : Fin n, ‖(((s i : ℂ) - z)⁻¹ + (-(s i : ℂ) - z)⁻¹)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, (2 * (z.im)⁻¹) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc ‖(((s i : ℂ) - z)⁻¹ + (-(s i : ℂ) - z)⁻¹)‖
              ≤ ‖(((s i : ℂ) - z)⁻¹)‖ + ‖(-(s i : ℂ) - z)⁻¹‖ := norm_add_le _ _
            _ ≤ (z.im)⁻¹ + (z.im)⁻¹ := add_le_add (hterm (s i)) (hterm' (s i))
            _ = 2 * (z.im)⁻¹ := by ring
      _ = (n : ℝ) * (2 * (z.im)⁻¹) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hStieltjesBound : ∀ (s : Fin n → ℝ), ‖symStieltjesSvals s z‖ ≤ (z.im)⁻¹ := by
    intro s
    simp only [symStieltjesSvals]
    have hcoef : ‖((2 * (n : ℝ))⁻¹ : ℂ)‖ = (2 * (n : ℝ))⁻¹ := by
      rw [norm_inv]
      have hcast : ((2 : ℂ) * (((n : ℕ) : ℝ) : ℂ)) = (((2 : ℝ) * (n : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      have hnf : ‖(((2 : ℝ) * (n : ℝ) : ℝ) : ℂ)‖ = |(2 : ℝ) * (n : ℝ)| :=
        RCLike.norm_ofReal _
      rw [hcast, hnf, abs_of_pos (by linarith : (0 : ℝ) < 2 * (n : ℝ))]
    calc ‖((2 * (n : ℝ))⁻¹ : ℂ) * (∑ i : Fin n, (((s i : ℂ) - z)⁻¹ + (-(s i : ℂ) - z)⁻¹))‖
        = ‖((2 * (n : ℝ))⁻¹ : ℂ)‖
            * ‖∑ i : Fin n, (((s i : ℂ) - z)⁻¹ + (-(s i : ℂ) - z)⁻¹)‖ := norm_mul _ _
      _ ≤ (2 * (n : ℝ))⁻¹ * ((n : ℝ) * (2 * (z.im)⁻¹)) := by
          rw [hcoef]
          exact mul_le_mul_of_nonneg_left (hsum s) (le_of_lt (inv_pos.mpr (by linarith)))
      _ = (z.im)⁻¹ := by
          field_simp
  have hzsub : ∀ x : ℝ, ((x : ℂ) - z) ≠ 0 := by
    intro x hcon
    have him : (((x : ℂ) - z)).im = 0 := by rw [hcon]; simp
    simp at him
    linarith [hz, him]
  have hzsub' : ∀ x : ℝ, (-(x : ℂ) - z) ≠ 0 := by
    intro x hcon
    have him : (-(x : ℂ) - z).im = 0 := by rw [hcon]; simp
    simp at him
    linarith [hz, him]
  have hsqne : ∀ x : ℝ, ((x : ℂ)) ^ 2 - z ^ 2 ≠ 0 := by
    intro x hcon
    have hfac : ((x : ℂ)) ^ 2 - z ^ 2 = ((x : ℂ) - z) * ((x : ℂ) + z) := by ring
    rw [hfac] at hcon
    rcases mul_eq_zero.mp hcon with h' | h'
    · exact hzsub x h'
    · have him : ((x : ℂ) + z).im = 0 := by rw [h']; simp
      simp at him
      linarith [hz, him]
  have hper : ∀ x : ℝ,
      (((x : ℂ) - z)⁻¹ + (-(x : ℂ) - z)⁻¹) = (2 * z) * (((x : ℂ)) ^ 2 - z ^ 2)⁻¹ := by
    intro x
    have h1 : ((x : ℂ) - z) ≠ 0 := hzsub x
    have h2 : (-(x : ℂ) - z) ≠ 0 := hzsub' x
    have h3 : ((x : ℂ)) ^ 2 - z ^ 2 ≠ 0 := hsqne x
    field_simp
    ring


  have hsym : ∀ (s : Fin n → ℝ),
      symStieltjesSvals s z
        = ((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z) * ∑ i : Fin n, (((s i : ℂ)) ^ 2 - z ^ 2)⁻¹ := by
    intro s
    simp only [symStieltjesSvals]
    have hstep : (∑ i : Fin n, (((s i : ℂ) - z)⁻¹ + (-(s i : ℂ) - z)⁻¹))
        = ∑ i : Fin n, (2 * z) * (((s i : ℂ)) ^ 2 - z ^ 2)⁻¹ :=
      Finset.sum_congr rfl fun i _ => hper (s i)
    rw [hstep, ← Finset.mul_sum]
    ring
  have hSigmaBound : ∀ (s : Fin n → ℝ),
      ‖∑ i : Fin n, (((s i : ℂ)) ^ 2 - z ^ 2)⁻¹‖ * ((z.im) * ‖z‖) ≤ (n : ℝ) := by
    intro s
    have hs := hStieltjesBound s
    have hcoef : ‖(((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z))‖ = (2 * (n : ℝ))⁻¹ * (2 * ‖z‖) := by
      rw [norm_mul, norm_mul]
      have h1c : ‖((2 * (n : ℝ))⁻¹ : ℂ)‖ = (2 * (n : ℝ))⁻¹ := by
        rw [norm_inv]
        have hcast : ((2 : ℂ) * (((n : ℕ) : ℝ) : ℂ)) = (((2 : ℝ) * (n : ℝ) : ℝ) : ℂ) := by
          push_cast
          ring
        have hnf : ‖(((2 : ℝ) * (n : ℝ) : ℝ) : ℂ)‖ = |(2 : ℝ) * (n : ℝ)| :=
          RCLike.norm_ofReal _
        rw [hcast, hnf, abs_of_pos (by linarith : (0 : ℝ) < 2 * (n : ℝ))]
      have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h1c, h2c]
    rw [hsym s, norm_mul, hcoef] at hs
    have hzn : (0 : ℝ) < ‖z‖ := by
      have h := Complex.abs_im_le_norm z
      rw [abs_of_pos hz] at h
      linarith
    have step1 := mul_le_mul_of_nonneg_right hs (le_of_lt (mul_pos hnpos hz))
    have step3 : (2 * (n : ℝ))⁻¹ * (2 * ‖z‖)
        * ‖∑ i : Fin n, (((s i : ℂ)) ^ 2 - z ^ 2)⁻¹‖ * ((n : ℝ) * z.im)
        = ‖∑ i : Fin n, (((s i : ℂ)) ^ 2 - z ^ 2)⁻¹‖ * (z.im * ‖z‖) := by
      field_simp
      first | ring | skip
    have step2 : (z.im)⁻¹ * ((n : ℝ) * z.im) = (n : ℝ) := by field_simp
    rw [step3, step2] at step1
    exact step1
  have hStieltjesBoundA : ∀ ω : Ω,
      ‖symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z‖ ≤ (z.im)⁻¹ :=
    fun ω => hStieltjesBound _
  have hStieltjesBoundG : ∀ g : Matrix (Fin m) (Fin n) ℝ,
      ‖symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z‖ ≤
        (z.im)⁻¹ :=
    fun g => hStieltjesBound _
  have hDiffBound : ∀ (ω : Ω) (g : Matrix (Fin m) (Fin n) ℝ),
      ‖symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z
        - symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z‖
        ≤ 2 * (z.im)⁻¹ := by
    intro ω g
    calc ‖symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z
          - symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z‖
        ≤ ‖symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z‖
          + ‖symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z‖ :=
          norm_sub_le _ _
      _ ≤ (z.im)⁻¹ + (z.im)⁻¹ := add_le_add (hStieltjesBoundA ω) (hStieltjesBoundG g)
      _ = 2 * (z.im)⁻¹ := by ring
  have hzle : z.im ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rwa [abs_of_pos hz] at h
  have hznpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le hz hzle
  have hEmpos : (0 : ℝ) < (z.im ^ 4)⁻¹ := inv_pos.mpr (pow_pos hz 4)
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    unfold stdNormalMatrixMeasure
    infer_instance
  have hStdUniv : stdNormalMatrixMeasure m n Set.univ = 1 := measure_univ







  have hsplitA : (∫ ω, symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z ∂μ)
      = ((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z)
        * ∫ ω, (∑ i : Fin n,
            (((svals (maskedScaled p (Xi ω) (Mask ω)) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂μ := by
    have hpt : (fun ω => symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z)
        = (fun ω => ((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z)
            * (∑ i : Fin n,
              (((svals (maskedScaled p (Xi ω) (Mask ω)) i : ℂ)) ^ 2 - z ^ 2)⁻¹)) := by
      funext ω
      exact hsym (svals (maskedScaled p (Xi ω) (Mask ω)))
    rw [hpt, MeasureTheory.integral_const_mul]
  have hsplitG : (∫ g : Matrix (Fin m) (Fin n) ℝ,
        symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z
          ∂(stdNormalMatrixMeasure m n))
      = ((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z)
        * ∫ g : Matrix (Fin m) (Fin n) ℝ, (∑ i : Fin n,
            (((svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂(stdNormalMatrixMeasure m n) := by
    have hpt : (fun g : Matrix (Fin m) (Fin n) ℝ =>
          symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z)
        = (fun g : Matrix (Fin m) (Fin n) ℝ => ((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z)
            * (∑ i : Fin n,
              (((svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j) i : ℂ)) ^ 2 - z ^ 2)⁻¹)) := by
      funext g
      exact hsym (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j))
    rw [hpt]
    exact MeasureTheory.integral_const_mul (((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z)) _
  have hsvalsSq : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n),
      ((svals A i : ℂ)) ^ 2
        = (((max ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀
              (Fin.cast (Fintype.card_fin n).symm i)) 0) : ℝ) : ℂ) := by
    intro A i
    have h1 : ((svals A i : ℝ) : ℂ) ^ 2 = (((svals A i) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    simp only [svals]
    rw [Real.sq_sqrt']
  have hSigmaA : ∀ (A : Matrix (Fin m) (Fin n) ℝ),
      (∑ i : Fin n, (((svals A i : ℂ)) ^ 2 - z ^ 2)⁻¹)
        = ∑ i : Fin n,
            (((max ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀
              (Fin.cast (Fintype.card_fin n).symm i)) 0 : ℝ) : ℂ) - z ^ 2)⁻¹ := by
    intro A
    exact Finset.sum_congr rfl fun i _ => by rw [hsvalsSq A i]
  have hfunA : (fun ω => ∑ i : Fin n,
        (((svals (maskedScaled p (Xi ω) (Mask ω)) i : ℂ)) ^ 2 - z ^ 2)⁻¹)
      = (fun ω => ∑ i : Fin n,
          (((max ((Matrix.isHermitian_conjTranspose_mul_self
            (maskedScaled p (Xi ω) (Mask ω))).eigenvalues₀
            (Fin.cast (Fintype.card_fin n).symm i)) 0 : ℝ) : ℂ) - z ^ 2)⁻¹) := by
    funext ω
    exact hSigmaA _
  have hfunG : (fun g : Matrix (Fin m) (Fin n) ℝ => ∑ i : Fin n,
        (((svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j) i : ℂ)) ^ 2 - z ^ 2)⁻¹)
      = (fun g : Matrix (Fin m) (Fin n) ℝ => ∑ i : Fin n,
          (((max ((Matrix.isHermitian_conjTranspose_mul_self
            (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)).eigenvalues₀
            (Fin.cast (Fintype.card_fin n).symm i)) 0 : ℝ) : ℂ) - z ^ 2)⁻¹) := by
    funext g
    exact hSigmaA _
  have hEigDiff :
      ((∫ ω, (∑ i : Fin n,
          (((svals (maskedScaled p (Xi ω) (Mask ω)) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂μ)
        - ∫ g : Matrix (Fin m) (Fin n) ℝ, (∑ i : Fin n,
          (((svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂(stdNormalMatrixMeasure m n))
      = ((∫ ω, (∑ i : Fin n,
          (((max ((Matrix.isHermitian_conjTranspose_mul_self
            (maskedScaled p (Xi ω) (Mask ω))).eigenvalues₀
            (Fin.cast (Fintype.card_fin n).symm i)) 0 : ℝ) : ℂ) - z ^ 2)⁻¹) ∂μ)
        - ∫ g : Matrix (Fin m) (Fin n) ℝ, (∑ i : Fin n,
          (((max ((Matrix.isHermitian_conjTranspose_mul_self
            (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)).eigenvalues₀
            (Fin.cast (Fintype.card_fin n).symm i)) 0 : ℝ) : ℂ) - z ^ 2)⁻¹) ∂(stdNormalMatrixMeasure m n)) := by
    rw [hfunA, hfunG]



  have hdiff : (∫ ω, symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z ∂μ)
      - ∫ g : Matrix (Fin m) (Fin n) ℝ,
          symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z
          ∂(stdNormalMatrixMeasure m n)
      = ((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z)
        * ((∫ ω, (∑ i : Fin n,
              (((svals (maskedScaled p (Xi ω) (Mask ω)) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂μ)
          - ∫ g : Matrix (Fin m) (Fin n) ℝ, (∑ i : Fin n,
              (((svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂(stdNormalMatrixMeasure m n)) := by
    rw [hsplitA, hsplitG]
    ring
  have hconstNorm : ‖(((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z))‖
      = (2 * (n : ℝ))⁻¹ * (2 * ‖z‖) := by
    rw [norm_mul, norm_mul]
    have h1 : ‖((2 * (n : ℝ))⁻¹ : ℂ)‖ = (2 * (n : ℝ))⁻¹ := by
      rw [norm_inv]
      have hcast : ((2 : ℂ) * (((n : ℕ) : ℝ) : ℂ)) = (((2 : ℝ) * (n : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      have hnf : ‖(((2 : ℝ) * (n : ℝ) : ℝ) : ℂ)‖ = |(2 : ℝ) * (n : ℝ)| :=
        RCLike.norm_ofReal _
      rw [hcast, hnf, abs_of_pos (by linarith : (0 : ℝ) < 2 * (n : ℝ))]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h1, h2]
  have hc_ne : (((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z)) ≠ 0 := by
    intro h0
    have hzero : (0 : ℝ) = (2 * (n : ℝ))⁻¹ * (2 * ‖z‖) := by
      rw [h0] at hconstNorm
      simpa using hconstNorm
    have hpos : (0 : ℝ) < (2 * (n : ℝ))⁻¹ * (2 * ‖z‖) :=
      mul_pos (inv_pos.mpr (by linarith)) (by linarith)
    linarith
  have hsymInv : ∀ (s : Fin n → ℝ),
      (((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z))⁻¹ * symStieltjesSvals s z
        = ∑ i : Fin n, (((s i : ℂ)) ^ 2 - z ^ 2)⁻¹ := by
    intro s
    rw [hsym s, ← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul]
  have hcoefInv : ((2 * (n : ℝ))⁻¹ * (2 * ‖z‖))⁻¹ = (n : ℝ) / ‖z‖ := by
    have hzn : ‖z‖ ≠ 0 := ne_of_gt hznpos
    have h2n : (2 * (n : ℝ)) ≠ 0 := ne_of_gt (by linarith)
    field_simp
    first | ring | skip



  have hdiffNorm : ‖(∫ ω, symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z ∂μ)
      - ∫ g : Matrix (Fin m) (Fin n) ℝ,
          symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z
          ∂(stdNormalMatrixMeasure m n)‖
      = (2 * (n : ℝ))⁻¹ * (2 * ‖z‖)
        * ‖(∫ ω, (∑ i : Fin n,
              (((svals (maskedScaled p (Xi ω) (Mask ω)) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂μ)
          - ∫ g : Matrix (Fin m) (Fin n) ℝ, (∑ i : Fin n,
              (((svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂(stdNormalMatrixMeasure m n)‖ := by
    rw [hdiff, norm_mul, hconstNorm]
  have hdiffNormMul : ‖(∫ ω, (∑ i : Fin n,
        (((svals (maskedScaled p (Xi ω) (Mask ω)) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂μ)
      - ∫ g : Matrix (Fin m) (Fin n) ℝ, (∑ i : Fin n,
          (((svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j) i : ℂ)) ^ 2 - z ^ 2)⁻¹)
          ∂(stdNormalMatrixMeasure m n)‖ * ((2 * (n : ℝ))⁻¹ * (2 * ‖z‖))
      = ‖(∫ ω, symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z ∂μ)
        - ∫ g : Matrix (Fin m) (Fin n) ℝ,
            symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z
            ∂(stdNormalMatrixMeasure m n)‖ := by
    rw [hdiffNorm, mul_comm]

  have hCancel : ∀ (s s' : Fin n → ℝ),
      symStieltjesSvals s z - symStieltjesSvals s' z
        = ((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z)
          * ((∑ i : Fin n, (((s i : ℂ)) ^ 2 - z ^ 2)⁻¹)
            - ∑ i : Fin n, (((s' i : ℂ)) ^ 2 - z ^ 2)⁻¹) := by
    intro s s'
    rw [hsym s, hsym s']
    ring
  have hCancelNorm : ∀ (s s' : Fin n → ℝ),
      ‖symStieltjesSvals s z - symStieltjesSvals s' z‖
        = (2 * (n : ℝ))⁻¹ * (2 * ‖z‖)
          * ‖(∑ i : Fin n, (((s i : ℂ)) ^ 2 - z ^ 2)⁻¹)
            - ∑ i : Fin n, (((s' i : ℂ)) ^ 2 - z ^ 2)⁻¹‖ := by
    intro s s'
    rw [hCancel s s', norm_mul, hconstNorm]









  have hDictPt : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      (∑ i : Fin n, (((svals A i : ℂ)) ^ 2 - z ^ 2)⁻¹)
        = (((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z))⁻¹ *
          (- (((((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ) *
              ((((((m : ℝ) + (n : ℝ))⁻¹ : ℝ)) : ℂ) *
                ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
                    (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A
                      (Matrix.transpose A) (0 : Matrix (Fin n) (Fin n) ℝ)).map
                      Complex.ofReal)⁻¹).trace)
            + (((((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ) * z⁻¹) := by
    intro A
    rw [← hsymInv (svals A)]
    rw [statopia_math_node_1061731261_2101eec5 m n hn A z hz]

  have hDictS : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      (∑ i : Fin n, (((svals A i : ℂ)) ^ 2 - z ^ 2)⁻¹)
        = - (2 * z)⁻¹ *
            (((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A
                  (Matrix.transpose A) (0 : Matrix (Fin n) (Fin n) ℝ)).map
                  Complex.ofReal)⁻¹).trace
              - (((m : ℝ) - (n : ℝ) : ℝ) : ℂ) * z⁻¹) := by
    intro A
    have hd0 : ((m : ℝ) + (n : ℝ)) ≠ 0 := ne_of_gt (by linarith)
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have h2n0 : (2 * (n : ℝ)) ≠ 0 := ne_of_gt (by linarith)
    have hreal1 : ((2 * (n : ℝ)) : ℝ) * (((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ)) : ℝ) *
        (((m : ℝ) + (n : ℝ))⁻¹ : ℝ) = 1 := by
      field_simp
      first | ring | skip
    have hreal2 : ((2 * (n : ℝ)) : ℝ) * (((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ)) : ℝ)
        = ((m : ℝ) - (n : ℝ)) := by
      field_simp
      first | ring | skip
    have hA1 : ((((2 * (n : ℝ)) : ℝ) : ℂ)) *
        (((((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ) *
        (((((m : ℝ) + (n : ℝ))⁻¹ : ℝ)) : ℂ) = 1 := by
      have hcast : ((((2 * (n : ℝ)) : ℝ) : ℂ)) *
          (((((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ) *
          (((((m : ℝ) + (n : ℝ))⁻¹ : ℝ)) : ℂ)
          = (((((2 * (n : ℝ)) : ℝ) * ((((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) *
              ((((m : ℝ) + (n : ℝ))⁻¹ : ℝ))) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, hreal1]
      norm_num
    have hA2 : ((((2 * (n : ℝ)) : ℝ) : ℂ)) *
        (((((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ)
        = ((((m : ℝ) - (n : ℝ)) : ℝ) : ℂ) := by
      have hcast : ((((2 * (n : ℝ)) : ℝ) : ℂ)) *
          (((((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ)
          = (((((2 * (n : ℝ)) : ℝ) *
              ((((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ)) : ℝ))) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, hreal2]
    have hcinv : (((2 * (n : ℝ))⁻¹ : ℂ) * (2 * z))⁻¹
        = ((((2 * (n : ℝ)) : ℝ) : ℂ)) * (2 * z)⁻¹ := by
      rw [mul_inv_rev]
      have h2 : ((((2 * (n : ℝ))⁻¹ : ℂ)))⁻¹ = ((((2 * (n : ℝ)) : ℝ)) : ℂ) := by
        push_cast
        first | rw [inv_inv] | skip
      rw [h2, mul_comm]
    rw [hDictPt A]
    set Tr : ℂ := ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A
          (Matrix.transpose A) (0 : Matrix (Fin n) (Fin n) ℝ)).map
          Complex.ofReal)⁻¹).trace with hTr
    set M : ℂ := (((((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ) with hM
    set N : ℂ := (((((m : ℝ) + (n : ℝ))⁻¹ : ℝ)) : ℂ) with hN
    set K : ℂ := (((((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ)) : ℝ)) : ℂ) with hK
    set E : ℂ := ((((m : ℝ) - (n : ℝ)) : ℝ) : ℂ) with hEs
    rw [hcinv]
    have hMN : ((((2 * (n : ℝ)) : ℝ) : ℂ)) * M * N = 1 := by
      rw [hM, hN]
      exact hA1
    have hMK : ((((2 * (n : ℝ)) : ℝ) : ℂ)) * K = E := by
      rw [hK, hEs]
      exact hA2
    have hstep : ((((2 * (n : ℝ)) : ℝ) : ℂ)) * (-M * (N * Tr) + K * z⁻¹)
        = - (Tr - E * z⁻¹) := by
      have h1 : ((((2 * (n : ℝ)) : ℝ) : ℂ)) * (-M * (N * Tr) + K * z⁻¹)
          = - ((((((2 * (n : ℝ)) : ℝ) : ℂ)) * M) * N) * Tr
            + (((((2 * (n : ℝ)) : ℝ) : ℂ)) * K) * z⁻¹ := by
        ring
      rw [h1, hMN, hMK]
      ring
    calc ((((2 * (n : ℝ)) : ℝ) : ℂ) * (2 * z)⁻¹) * (-M * (N * Tr) + K * z⁻¹)
        = (2 * z)⁻¹ * (((((2 * (n : ℝ)) : ℝ) : ℂ)) * (-M * (N * Tr) + K * z⁻¹)) := by
          ring
      _ = (2 * z)⁻¹ * (- (Tr - E * z⁻¹)) := by rw [hstep]
      _ = - (2 * z)⁻¹ * (Tr - E * z⁻¹) := by ring


  have hIntA : (∫ ω, (∑ i : Fin n,
        (((svals (maskedScaled p (Xi ω) (Mask ω)) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂μ)
      = (- (2 * z)⁻¹) * ∫ ω,
          (((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (maskedScaled p (Xi ω) (Mask ω))
                (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
                (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace
            - (((m : ℝ) - (n : ℝ) : ℝ) : ℂ) * z⁻¹) ∂μ := by
    have hpt : (fun ω => ∑ i : Fin n,
          (((svals (maskedScaled p (Xi ω) (Mask ω)) i : ℂ)) ^ 2 - z ^ 2)⁻¹)
        = (fun ω => (- (2 * z)⁻¹) *
            (((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                  (maskedScaled p (Xi ω) (Mask ω))
                  (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
                  (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace
              - (((m : ℝ) - (n : ℝ) : ℝ) : ℂ) * z⁻¹)) := by
      funext ω
      simpa only [neg_mul] using hDictS (maskedScaled p (Xi ω) (Mask ω))
    rw [hpt, MeasureTheory.integral_const_mul]
  have hIntG : (∫ g : Matrix (Fin m) (Fin n) ℝ, (∑ i : Fin n,
        (((svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j) i : ℂ)) ^ 2 - z ^ 2)⁻¹)
        ∂(stdNormalMatrixMeasure m n))
      = (- (2 * z)⁻¹) * ∫ g : Matrix (Fin m) (Fin n) ℝ,
          (((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)
                (Matrix.transpose (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j))
                (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace
            - (((m : ℝ) - (n : ℝ) : ℝ) : ℂ) * z⁻¹) ∂(stdNormalMatrixMeasure m n) := by
    have hpt : (fun g : Matrix (Fin m) (Fin n) ℝ => ∑ i : Fin n,
          (((svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j) i : ℂ)) ^ 2 - z ^ 2)⁻¹)
        = (fun g : Matrix (Fin m) (Fin n) ℝ => (- (2 * z)⁻¹) *
            (((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                  (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)
                  (Matrix.transpose (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j))
                  (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace
              - (((m : ℝ) - (n : ℝ) : ℝ) : ℂ) * z⁻¹)) := by
      funext g
      simpa only [neg_mul] using hDictS (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)
    rw [hpt]
    exact MeasureTheory.integral_const_mul (- (2 * z)⁻¹) _

  have hshift : ∀ (F : Ω → ℂ)
      (G : Matrix (Fin m) (Fin n) ℝ → ℂ) (s : ℂ),
      Integrable F μ →
      Integrable G (stdNormalMatrixMeasure m n) →
      ((∫ ω, (F ω - s) ∂μ) - ∫ g, (G g - s) ∂(stdNormalMatrixMeasure m n))
        = (∫ ω, F ω ∂μ) - ∫ g, G g ∂(stdNormalMatrixMeasure m n) := by
    intro F G s hF hG
    have hFs : (∫ ω, (F ω - s) ∂μ) = (∫ ω, F ω ∂μ) - s := by
      have h := integral_sub hF (integrable_const (μ := μ) s)
      simpa using h
    have hGs : (∫ g, (G g - s) ∂(stdNormalMatrixMeasure m n))
        = (∫ g, G g ∂(stdNormalMatrixMeasure m n)) - s := by
      have h := integral_sub hG (integrable_const (μ := stdNormalMatrixMeasure m n) s)
      simpa using h
    rw [hFs, hGs]
    ring
  have hnormalized : ∀ (d : ℕ) (F : Ω → ℂ)
      (G : Matrix (Fin m) (Fin n) ℝ → ℂ),
      ((∫ ω, ((d : ℂ)⁻¹) * F ω ∂μ)
          - ∫ g, ((d : ℂ)⁻¹) * G g ∂(stdNormalMatrixMeasure m n))
        = ((d : ℂ)⁻¹)
          * ((∫ ω, F ω ∂μ) - ∫ g, G g ∂(stdNormalMatrixMeasure m n)) := by
    intro d F G
    have h1 : (∫ ω, ((d : ℂ)⁻¹) * F ω ∂μ) = ((d : ℂ)⁻¹) * ∫ ω, F ω ∂μ :=
      MeasureTheory.integral_const_mul ((d : ℂ)⁻¹) F
    have h2 : (∫ g, ((d : ℂ)⁻¹) * G g ∂(stdNormalMatrixMeasure m n))
        = ((d : ℂ)⁻¹) * ∫ g, G g ∂(stdNormalMatrixMeasure m n) :=
      MeasureTheory.integral_const_mul ((d : ℂ)⁻¹) G
    rw [h1, h2]
    ring


  have htraceReindex : ∀ (e : Fin m ⊕ Fin n ≃ Fin (m + n))
      (N : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ),
      Matrix.trace ((Matrix.reindex e e) N) = Matrix.trace N := by
    intro e N
    rw [Matrix.reindex_apply]
    have hcomp : (∑ a : Fin (m + n), N (e.symm a) (e.symm a)) = ∑ b, N b b :=
      Equiv.sum_comp e.symm (fun j => N j j)
    show (∑ a : Fin (m + n), (N.submatrix ⇑e.symm ⇑e.symm) a a) = ∑ b, N b b
    simpa [Matrix.submatrix_apply] using hcomp
  have hreindexResolvent : ∀ (e : Fin m ⊕ Fin n ≃ Fin (m + n))
      (N : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ),
      Matrix.trace ((z • (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
          - (Matrix.reindex e e) N)⁻¹)
        = Matrix.trace ((z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) - N)⁻¹) := by
    intro e N
    have h1 : (z • (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
          - (Matrix.reindex e e) N)
        = (Matrix.reindex e e)
            (z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) - N) := by
      rw [Matrix.reindex_apply, Matrix.reindex_apply]
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [Matrix.submatrix_apply, Matrix.one_apply]
      · have hne : e.symm a ≠ e.symm b := fun hc => hab (by
          have hh := congrArg (⇑e) hc
          simpa using hh)
        simp [Matrix.submatrix_apply, Matrix.one_apply, hab, hne]

    rw [h1, Matrix.inv_reindex]
    exact htraceReindex e _

  have hTrace : ‖(∫ ω,
        (((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (maskedScaled p (Xi ω) (Mask ω))
              (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace
          - (((m : ℝ) - (n : ℝ) : ℝ) : ℂ) * z⁻¹) ∂μ)
      - ∫ g : Matrix (Fin m) (Fin n) ℝ,
          (((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)
                (Matrix.transpose (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j))
                (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace
            - (((m : ℝ) - (n : ℝ) : ℝ) : ℂ) * z⁻¹) ∂(stdNormalMatrixMeasure m n)‖
      ≤ ((m : ℝ) + (n : ℝ))
        * (24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹) := by
    have hCore := hC μ m n hm hn p Kt hp hp1 hKt Xi Mask hXi_meas hXi_int hXi_sq_int
      hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val hMask_law hMask_indep hIndep z hz
    obtain ⟨-, hIntP, -, hIntQ, -⟩ :=
      statopia_math_node_2041753363_bb646534 m n hm hn p hp z hz μ Xi Mask hXi_meas hMask_meas
    have hcbridge : ((((m : ℝ) : ℂ)) + (((n : ℝ) : ℂ))) =
        (((((m : ℝ) + (n : ℝ)) : ℝ) : ℂ)) := by
      push_cast
      ring
    have hcc2 : ((((m : ℝ) + (n : ℝ)) : ℂ)) = (((m + n : ℕ)) : ℂ) := by
      push_cast
      ring
    have hcn : ‖(((((m : ℝ) + (n : ℝ)) : ℝ) : ℂ))⁻¹‖ = ((m : ℝ) + (n : ℝ))⁻¹ := by
      rw [norm_inv]
      have hnf : ‖(((((m : ℝ) + (n : ℝ)) : ℝ) : ℂ))‖ = |((m : ℝ) + (n : ℝ))| :=
        RCLike.norm_ofReal _
      rw [hnf, abs_of_pos (by linarith : (0 : ℝ) < (m : ℝ) + (n : ℝ))]
    have hcne : ((((m : ℝ) : ℂ)) + (((n : ℝ) : ℂ)))⁻¹ ≠ 0 := by
      rw [hcbridge]
      intro h0
      rw [h0] at hcn
      simp at hcn
      have hpos : (0 : ℝ) < ((m : ℝ) + (n : ℝ))⁻¹ := inv_pos.mpr hd0pos
      linarith
    have hcnN : ‖((((m + n : ℕ)) : ℂ))⁻¹‖ = ((m : ℝ) + (n : ℝ))⁻¹ := by
      rw [← hcc2, hcbridge]
      exact hcn

    have hIntF : Integrable (fun ω =>
        ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (maskedScaled p (Xi ω) (Mask ω))
              (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace) μ := by
      have h := hIntP.const_mul (((((m : ℝ) : ℂ)) + (((n : ℝ) : ℂ)))⁻¹)⁻¹
      simpa only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul] using h
    have hIntG : Integrable (fun g : Matrix (Fin m) (Fin n) ℝ =>
        ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)
              (Matrix.transpose (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)
        (stdNormalMatrixMeasure m n) := by
      have h := hIntQ.const_mul (((((m : ℝ) : ℂ)) + (((n : ℝ) : ℂ)))⁻¹)⁻¹
      simpa only [div_eq_inv_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcne,
        one_mul] using h
    refine le_trans (le_of_eq (congrArg (fun t : ℂ => ‖t‖)
      (hshift (fun ω =>
        ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (maskedScaled p (Xi ω) (Mask ω))
              (Matrix.transpose (maskedScaled p (Xi ω) (Mask ω)))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)
        (fun g =>
        ((((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) -
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)
              (Matrix.transpose (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j))
              (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace)
        ((((m : ℝ) - (n : ℝ) : ℝ) : ℂ) * z⁻¹) hIntF hIntG))) ?_
    have h := hCore
    have hrpow : Real.rpow ((m : ℝ) * p) (-(1 / 2 : ℝ)) = (Real.sqrt ((m : ℝ) * p))⁻¹ := by
      have hmp : (0 : ℝ) ≤ (m : ℝ) * p := le_of_lt (mul_pos hmpos hp)
      have hexp : (-(1 / 2 : ℝ)) = (-1) / 2 := by norm_num
      rw [hexp]
      have h1 : Real.rpow ((m : ℝ) * p) ((-1) / 2 : ℝ)
          = Real.rpow (Real.sqrt ((m : ℝ) * p)) (-1 : ℝ) :=
        Real.rpow_div_two_eq_sqrt (-1) hmp
      rw [h1]
      exact Real.rpow_neg_one _
    rw [hrpow] at h
    simp only [div_eq_inv_mul] at h
    rw [hcc2] at h
    rw [hnormalized] at h
    rw [norm_mul] at h
    rw [hcnN] at h

    have hmul_eq : ∀ x : ℝ, ((m : ℝ) + (n : ℝ)) * ((((m : ℝ) + (n : ℝ))⁻¹) * x) = x := by
      intro x
      rw [← mul_assoc, mul_inv_cancel₀ hd0ne, one_mul]
    have h2 := mul_le_mul_of_nonneg_left h (le_of_lt hd0pos)
    rw [hmul_eq] at h2
    refine le_trans h2 ?_
    have hstep : C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹
        ≤ 24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹ := by
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : C ≤ 24 * C)
            (pow_nonneg (le_of_lt hKt) 3)) hR) hE
    exact mul_le_mul_of_nonneg_left hstep (le_of_lt hd0pos)








  have hD : ‖(∫ ω, (∑ i : Fin n,
        (((svals (maskedScaled p (Xi ω) (Mask ω)) i : ℂ)) ^ 2 - z ^ 2)⁻¹) ∂μ)
      - ∫ g : Matrix (Fin m) (Fin n) ℝ, (∑ i : Fin n,
          (((svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j) i : ℂ)) ^ 2 - z ^ 2)⁻¹)
          ∂(stdNormalMatrixMeasure m n)‖
      ≤ ((m : ℝ) + (n : ℝ)) / (2 * ‖z‖)
        * (24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹) := by
    have hzet : ‖(- (2 * z)⁻¹)‖ = (2 * ‖z‖)⁻¹ := by
      rw [norm_neg, norm_inv, norm_mul]
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2]
    have hfac : ∀ (X Y : ℂ), (- (2 * z)⁻¹) * X - (- (2 * z)⁻¹) * Y
        = (- (2 * z)⁻¹) * (X - Y) := by
      intro X Y
      ring
    rw [hIntA, hIntG, hfac, norm_mul, hzet]
    have hnn : (0 : ℝ) ≤ (2 * ‖z‖)⁻¹ := inv_nonneg.mpr (by positivity)
    have hb := mul_le_mul_of_nonneg_left hTrace hnn
    refine le_trans hb (le_of_eq ?_)
    rw [div_eq_mul_inv]
    ring

  have hDclean := hD
  have hDeig : ‖(∫ ω, (∑ i : Fin n,
        (((max ((Matrix.isHermitian_conjTranspose_mul_self
          (maskedScaled p (Xi ω) (Mask ω))).eigenvalues₀
          (Fin.cast (Fintype.card_fin n).symm i)) 0 : ℝ) : ℂ) - z ^ 2)⁻¹) ∂μ)
      - ∫ g : Matrix (Fin m) (Fin n) ℝ, (∑ i : Fin n,
        (((max ((Matrix.isHermitian_conjTranspose_mul_self
          (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)).eigenvalues₀
          (Fin.cast (Fintype.card_fin n).symm i)) 0 : ℝ) : ℂ) - z ^ 2)⁻¹) ∂(stdNormalMatrixMeasure m n)‖
      ≤ ((m : ℝ) + (n : ℝ)) / (2 * ‖z‖)
        * (24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹) := by
    rw [← hEigDiff]
    exact hDclean
  have hcore : ‖(∫ ω, symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z ∂μ)
      - ∫ g : Matrix (Fin m) (Fin n) ℝ,
          symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z
          ∂(stdNormalMatrixMeasure m n)‖
      ≤ ((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ))
        * (24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹) := by
    have hcoefnn : (0 : ℝ) ≤ (2 * (n : ℝ))⁻¹ * (2 * ‖z‖) :=
      mul_nonneg (inv_nonneg.mpr (by linarith)) (by positivity)
    rw [hdiffNorm]
    have hmul := mul_le_mul_of_nonneg_left hD hcoefnn
    have hEq : (2 * (n : ℝ))⁻¹ * (2 * ‖z‖)
        * (((m : ℝ) + (n : ℝ)) / (2 * ‖z‖)
          * (24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹))
        = ((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ))
          * (24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹) := by
      have hzn : ‖z‖ ≠ 0 := ne_of_gt hznpos
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      field_simp
      first | ring | skip
    exact le_trans hmul (le_of_eq hEq)
  have hkey : ‖(∫ ω, symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z ∂μ)
      - ∫ g : Matrix (Fin m) (Fin n) ℝ,
          symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z
          ∂(stdNormalMatrixMeasure m n)‖
      ≤ 24 * C * Kt ^ 3 * ((1 + rhoMinus⁻¹) / 2)
        * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹ := by
    have h1 : ((m : ℝ) + (n : ℝ)) / (2 * (n : ℝ))
        * (24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹)
        ≤ ((1 + rhoMinus⁻¹) / 2)
        * (24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹) :=
      mul_le_mul_of_nonneg_right hfac hYnn
    have h2 : ((1 + rhoMinus⁻¹) / 2)
        * (24 * C * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹)
        = 24 * C * Kt ^ 3 * ((1 + rhoMinus⁻¹) / 2)
          * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹ := by
      ring
    exact le_trans (le_trans hcore h1) (le_of_eq h2)
  exact hnum _ hkey
  /- @proof-region region.target-node.session.bcf4a73b7deb2e67 end -/

end Statlib.Imported

