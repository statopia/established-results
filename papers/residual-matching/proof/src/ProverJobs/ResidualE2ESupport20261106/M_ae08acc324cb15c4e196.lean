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
theorem statopia_math_node_3491744900_7d9db115 : ∀ (Cbv CD Kt D0 alpha0 D : ℝ)
    (hCbv : 1 ≤ Cbv) (hD0 : 0 < D0) (hKt : 0 < Kt) (halpha0 : 15 < alpha0)
    (hD : 0 < D),
    ∃ M1 : ℕ, ∀ m : ℕ, M1 ≤ m →
      3 * Cbv *
        (Real.rpow (m : ℝ) (-(1 / 4)) * Real.rpow (Real.log (m : ℝ)) (3 / 4)
          + Real.rpow (m : ℝ) (-(1 / 2)) * Real.sqrt (max 1 ((D + 2) * Real.log (m : ℝ)))
          + Real.rpow (3 * (2 * CD + 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
                * Real.rpow (Real.log (m : ℝ)) (1 - alpha0 / 2)) (1 / 3)
              * Real.rpow (max 1 ((D + 2) * Real.log (m : ℝ))) (2 / 3)
          + 3 * (2 * CD + 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
                * Real.rpow (Real.log (m : ℝ)) (1 - alpha0 / 2)
              * max 1 ((D + 2) * Real.log (m : ℝ)))
        ≤ 1 * (Real.log (m : ℝ))⁻¹ := by
  /- @proof-region region.target-node.session.6a66cbfe8d1ea75c begin -/
  intro Cbv CD Kt D0 alpha0 D hCbv hD0 hKt halpha0 hD
  set P : ℝ := 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 with hP
  set Kc : ℝ := 3 * (2 * CD + P) with hKc
  set A : ℝ := D + 2 with hA
  set e : ℝ := 1 - alpha0 / 2 with he
  obtain ⟨K0, hK0⟩ : ∃ x : ℝ, x = |2 * CD| + P := ⟨_, rfl⟩
  obtain ⟨C3, hC3⟩ : ∃ x : ℝ, x = (3 * K0) ^ (1 / 3 : ℝ) * (2 * A) ^ (2 / 3 : ℝ) := ⟨_, rfl⟩
  obtain ⟨C4, hC4⟩ : ∃ x : ℝ, x = 2 + C3 + 6 * K0 * A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x : ℝ, x = 1000 + 128 * A + (3 * Cbv * C4) ^ 2 + A := ⟨_, rfl⟩
  refine ⟨⌈Real.exp B⌉₊ + 2, ?_⟩
  intro m hm
  set L : ℝ := Real.log (m : ℝ) with hL
  set tau : ℝ := max 1 (A * L) with htau
  have hm2 : 2 ≤ m := by omega
  have hmpos_nat : 0 < m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hLval : Real.log (m : ℝ) = L := by rw [hL]
  have hBL : B ≤ L := by
    have h1 : Real.exp B ≤ (⌈Real.exp B⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp B⌉₊ : ℝ) ≤ (m : ℝ) := by
      have h3 : ((⌈Real.exp B⌉₊ : ℝ) + 2) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h6 : Real.exp B ≤ (m : ℝ) := le_trans h1 h2
    have h7 : Real.exp L = (m : ℝ) := by rw [hL]; exact Real.exp_log hmpos
    have h8 : Real.exp B ≤ Real.exp L := by rw [h7]; exact h6
    exact Real.exp_le_exp.mp h8
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hK00 : 0 ≤ K0 := by rw [hK0]; positivity
  have hA2 : 2 < A := by rw [hA]; linarith
  have hA0 : 0 < A := by linarith
  have hC30 : 0 ≤ C3 := by rw [hC3]; positivity
  have hC40 : 0 < C4 := by
    have h1 : 0 ≤ K0 * A := mul_nonneg hK00 hA0.le
    rw [hC4]; nlinarith
  have hCbv0 : 0 < Cbv := by linarith
  have hKcabs : |Kc| ≤ 3 * K0 := by
    have htri : |2 * CD + P| ≤ |2 * CD| + P := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith [neg_abs_le (2 * CD)]
      · linarith [le_abs_self (2 * CD)]
    rw [hKc, hK0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul_of_nonneg_left htri (by norm_num)
  have hB1000 : 1000 ≤ B := by
    have h2 : (0 : ℝ) ≤ 128 * A := by linarith [hA0.le]
    have h3 : (0 : ℝ) ≤ (3 * Cbv * C4) ^ 2 := sq_nonneg _
    rw [hB]; linarith
  have hL1000 : 1000 ≤ L := le_trans hB1000 hBL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hAL1 : 1 ≤ A * L := by
    have h := mul_le_mul hA2.le hL1 (by norm_num : (0 : ℝ) ≤ 1) hA0.le
    linarith
  have h128A : 128 * A ≤ L := by
    have h := hBL
    rw [hB] at h
    have h3 : (0 : ℝ) ≤ (3 * Cbv * C4) ^ 2 := sq_nonneg _
    have h4 : (0 : ℝ) ≤ A := hA0.le
    linarith
  have hC4sq : (3 * Cbv * C4) ^ 2 ≤ L := by
    have h := hBL
    rw [hB] at h
    have h2 : (0 : ℝ) ≤ 128 * A := by linarith [hA0.le]
    have h4 : (0 : ℝ) ≤ A := hA0.le
    linarith
  have hC4le : 3 * Cbv * C4 ≤ Real.sqrt L := by
    have h0 : 0 ≤ 3 * Cbv * C4 := by positivity
    calc 3 * Cbv * C4 = Real.sqrt ((3 * Cbv * C4) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hC4sq
  have hlog12 : Real.log L ≤ L / 12 := by
    have hkey : L ≤ Real.exp (L / 12) := by
      have hsq : Real.exp (L / 12) = Real.exp (L / 24) ^ 2 := by
        have h := Real.exp_nat_mul (L / 24) 2
        rw [show ((2 : ℕ) : ℝ) * (L / 24) = L / 12 by ring] at h
        exact h
      have hone : L / 24 + 1 ≤ Real.exp (L / 24) := Real.add_one_le_exp _
      have hprod : (L / 24 + 1) * (L / 24 + 1) ≤ Real.exp (L / 24) * Real.exp (L / 24) :=
        mul_le_mul hone hone (by linarith only [hL1000]) (le_of_lt (Real.exp_pos _))
      have hpoly : L ≤ (L / 24 + 1) * (L / 24 + 1) := by nlinarith only [hL1000]
      have hsq2 : Real.exp (L / 24) * Real.exp (L / 24) = Real.exp (L / 24) ^ 2 := by ring
      rw [hsq, ← hsq2]
      linarith only [hprod, hpoly]
    exact (Real.log_le_iff_le_exp hLpos).mpr hkey
  have hlog6 : Real.log L ≤ L / 6 := by linarith only [hlog12, hL1000]
  have hm1 : Real.rpow (m : ℝ) (-(1 / 4)) = Real.exp (-(L / 4)) := by
    have h : Real.rpow (m : ℝ) (-(1 / 4)) = Real.exp (Real.log (m : ℝ) * (-(1 / 4))) :=
      Real.rpow_def_of_pos hmpos (-(1 / 4))
    rw [h, hLval]
    congr 1
    ring
  have hm3 : Real.rpow L (3 / 4) ≤ Real.exp (L / 8) := by
    have h : Real.rpow L (3 / 4) = Real.exp (Real.log L * (3 / 4)) :=
      Real.rpow_def_of_pos hLpos (3 / 4)
    rw [h]
    apply Real.exp_le_exp.mpr
    linarith only [hlog6]
  have hm4 : Real.rpow (m : ℝ) (-(1 / 4)) * Real.rpow L (3 / 4) ≤ Real.exp (-(L / 8)) := by
    have hstep : Real.rpow (m : ℝ) (-(1 / 4)) * Real.rpow L (3 / 4)
        ≤ Real.exp (-(L / 4)) * Real.exp (L / 8) :=
      mul_le_mul hm1.le hm3 (Real.rpow_nonneg hLpos.le _) (Real.exp_pos _).le
    have heq : Real.exp (-(L / 4)) * Real.exp (L / 8) = Real.exp (-(L / 8)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linarith only [hstep, heq]
  have hm5 : Real.exp (-(L / 8)) ≤ Real.rpow L (-(3 / 2)) := by
    have h : Real.rpow L (-(3 / 2)) = Real.exp (Real.log L * (-(3 / 2))) :=
      Real.rpow_def_of_pos hLpos (-(3 / 2))
    rw [h]
    apply Real.exp_le_exp.mpr
    linarith only [hlog12]
  have hterm1 : Real.rpow (m : ℝ) (-(1 / 4)) * Real.rpow L (3 / 4) ≤ Real.rpow L (-(3 / 2)) :=
    le_trans hm4 hm5
  have htau1 : 1 ≤ tau := by rw [htau]; exact le_max_left _ _
  have htaule : tau ≤ 2 * A * L := by
    rw [htau]
    apply max_le
    · nlinarith only [hAL1]
    · nlinarith only [hAL1]
  have hAL0 : 0 ≤ A * L := by linarith only [hAL1]
  have hsqrt_tau : Real.sqrt tau ≤ 2 * A * L := by
    rw [Real.sqrt_le_iff]
    refine ⟨?_, ?_⟩
    · nlinarith only [hA0, hLpos]
    · have h2 : 1 ≤ 2 * A * L := by nlinarith only [hAL1]
      nlinarith only [htaule, h2]
  have hm6 : Real.rpow (m : ℝ) (-(1 / 2)) = Real.exp (-(L / 2)) := by
    have h : Real.rpow (m : ℝ) (-(1 / 2)) = Real.exp (Real.log (m : ℝ) * (-(1 / 2))) :=
      Real.rpow_def_of_pos hmpos (-(1 / 2))
    rw [h, hLval]
    congr 1
    ring
  have hexp4 : 2 * A * L ≤ Real.exp (L / 4) := by
    have hsq : Real.exp (L / 4) = Real.exp (L / 8) ^ 2 := by
      have h := Real.exp_nat_mul (L / 8) 2
      rw [show ((2 : ℕ) : ℝ) * (L / 8) = L / 4 by ring] at h
      exact h
    have hone : L / 8 + 1 ≤ Real.exp (L / 8) := Real.add_one_le_exp _
    have hprod : (L / 8 + 1) * (L / 8 + 1) ≤ Real.exp (L / 8) * Real.exp (L / 8) :=
      mul_le_mul hone hone (by linarith only [hL1000]) (le_of_lt (Real.exp_pos _))
    have hpoly : L ^ 2 / 64 ≤ (L / 8 + 1) * (L / 8 + 1) := by nlinarith only [hL1000]
    have hsq2 : Real.exp (L / 8) * Real.exp (L / 8) = Real.exp (L / 8) ^ 2 := by ring
    have h2 : L ^ 2 / 64 ≤ Real.exp (L / 4) := by
      rw [hsq, ← hsq2]
      linarith only [hprod, hpoly]
    have h3 : 2 * A * L ≤ L ^ 2 / 64 := by nlinarith only [h128A, hLpos]
    linarith only [h2, h3]
  have hm7 : Real.rpow (m : ℝ) (-(1 / 2)) * Real.sqrt tau ≤ Real.exp (-(L / 4)) := by
    have hstep : Real.rpow (m : ℝ) (-(1 / 2)) * Real.sqrt tau
        ≤ Real.exp (-(L / 2)) * (2 * A * L) :=
      mul_le_mul hm6.le hsqrt_tau (Real.sqrt_nonneg tau) (Real.exp_pos _).le
    have hstep2 : Real.exp (-(L / 2)) * (2 * A * L)
        ≤ Real.exp (-(L / 2)) * Real.exp (L / 4) :=
      mul_le_mul_of_nonneg_left hexp4 (Real.exp_pos _).le
    have heq : Real.exp (-(L / 2)) * Real.exp (L / 4) = Real.exp (-(L / 4)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linarith only [hstep, hstep2, heq]
  have hm8 : Real.exp (-(L / 4)) ≤ Real.rpow L (-(3 / 2)) := by
    have h : Real.rpow L (-(3 / 2)) = Real.exp (Real.log L * (-(3 / 2))) :=
      Real.rpow_def_of_pos hLpos (-(3 / 2))
    rw [h]
    apply Real.exp_le_exp.mpr
    linarith only [hlog6]
  have hterm2 : Real.rpow (m : ℝ) (-(1 / 2)) * Real.sqrt tau ≤ Real.rpow L (-(3 / 2)) :=
    le_trans hm7 hm8
  have hLepos : 0 < Real.rpow L e := Real.rpow_pos_of_pos hLpos e
  have htau0 : 0 ≤ tau := le_trans zero_le_one htau1
  have habs_base : |Kc * Real.rpow L e| ≤ 3 * K0 * Real.rpow L e := by
    have h1 : |Kc * Real.rpow L e| = |Kc| * Real.rpow L e := by
      rw [abs_mul, abs_of_pos hLepos]
    have h2 : |Kc| * Real.rpow L e ≤ 3 * K0 * Real.rpow L e :=
      mul_le_mul_of_nonneg_right hKcabs hLepos.le
    linarith only [h1, h2]
  have hcbrt : Real.rpow (Kc * Real.rpow L e) (1 / 3)
      ≤ Real.rpow (3 * K0) (1 / 3) * Real.rpow L (e / 3) := by
    have h1 : Real.rpow (Kc * Real.rpow L e) (1 / 3)
        ≤ Real.rpow |Kc * Real.rpow L e| (1 / 3) :=
      le_trans (le_abs_self _) (Real.abs_rpow_le_abs_rpow _ _)
    have h2 : Real.rpow |Kc * Real.rpow L e| (1 / 3)
        ≤ Real.rpow (3 * K0 * Real.rpow L e) (1 / 3) :=
      Real.rpow_le_rpow (abs_nonneg _) habs_base (by norm_num)
    have h3 : Real.rpow (3 * K0 * Real.rpow L e) (1 / 3)
        = Real.rpow (3 * K0) (1 / 3) * Real.rpow L (e / 3) := by
      have hmr : Real.rpow (3 * K0 * Real.rpow L e) (1 / 3)
          = Real.rpow (3 * K0) (1 / 3) * Real.rpow (Real.rpow L e) (1 / 3) :=
        Real.mul_rpow (by linarith only [hK00] : (0 : ℝ) ≤ 3 * K0) hLepos.le
      rw [hmr]
      congr 1
      have hmul : Real.rpow (Real.rpow L e) (1 / 3) = Real.rpow L (e * (1 / 3)) :=
        (Real.rpow_mul hLpos.le e (1 / 3)).symm
      rw [hmul]
      rw [show e * (1 / 3) = e / 3 by ring]
    calc Real.rpow (Kc * Real.rpow L e) (1 / 3) ≤ Real.rpow |Kc * Real.rpow L e| (1 / 3) := h1
      _ ≤ Real.rpow (3 * K0 * Real.rpow L e) (1 / 3) := h2
      _ = Real.rpow (3 * K0) (1 / 3) * Real.rpow L (e / 3) := h3
  have htau_rpow : Real.rpow tau (2 / 3) ≤ Real.rpow (2 * A) (2 / 3) * Real.rpow L (2 / 3) := by
    have h1 : Real.rpow tau (2 / 3) ≤ Real.rpow (2 * A * L) (2 / 3) :=
      Real.rpow_le_rpow htau0 htaule (by norm_num)
    have h2 : Real.rpow (2 * A * L) (2 / 3)
        = Real.rpow (2 * A) (2 / 3) * Real.rpow L (2 / 3) :=
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * A) hLpos.le
    linarith only [h1, h2]
  have hterm3 : Real.rpow (Kc * Real.rpow L e) (1 / 3) * Real.rpow tau (2 / 3)
      ≤ C3 * Real.rpow L (-(3 / 2)) := by
    have hprod : Real.rpow (Kc * Real.rpow L e) (1 / 3) * Real.rpow tau (2 / 3)
        ≤ (Real.rpow (3 * K0) (1 / 3) * Real.rpow L (e / 3))
          * (Real.rpow (2 * A) (2 / 3) * Real.rpow L (2 / 3)) :=
      mul_le_mul hcbrt htau_rpow (Real.rpow_nonneg htau0 _)
        (mul_nonneg (Real.rpow_nonneg (by linarith only [hK00] : (0 : ℝ) ≤ 3 * K0) _)
          (Real.rpow_nonneg hLpos.le _))
    have hEq : (Real.rpow (3 * K0) (1 / 3) * Real.rpow L (e / 3))
          * (Real.rpow (2 * A) (2 / 3) * Real.rpow L (2 / 3))
        = C3 * (Real.rpow L (e / 3) * Real.rpow L (2 / 3)) := by
      have hC3' : C3 = Real.rpow (3 * K0) (1 / 3) * Real.rpow (2 * A) (2 / 3) := hC3
      rw [hC3']
      ring
    have hadd : Real.rpow L (e / 3) * Real.rpow L (2 / 3)
        = Real.rpow L (e / 3 + 2 / 3) :=
      (Real.rpow_add hLpos (e / 3) (2 / 3)).symm
    have hexp3 : e / 3 + 2 / 3 ≤ -(3 / 2) := by
      rw [he]
      linarith only [halpha0]
    have hmono : Real.rpow L (e / 3 + 2 / 3) ≤ Real.rpow L (-(3 / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 hexp3
    calc Real.rpow (Kc * Real.rpow L e) (1 / 3) * Real.rpow tau (2 / 3)
        ≤ (Real.rpow (3 * K0) (1 / 3) * Real.rpow L (e / 3))
          * (Real.rpow (2 * A) (2 / 3) * Real.rpow L (2 / 3)) := hprod
      _ = C3 * (Real.rpow L (e / 3) * Real.rpow L (2 / 3)) := hEq
      _ = C3 * Real.rpow L (e / 3 + 2 / 3) := by rw [hadd]
      _ ≤ C3 * Real.rpow L (-(3 / 2)) :=
        mul_le_mul_of_nonneg_left hmono hC30
  have hterm4 : Kc * Real.rpow L e * tau ≤ 6 * K0 * A * Real.rpow L (-(3 / 2)) := by
    have h1a : Kc * Real.rpow L e ≤ |Kc| * Real.rpow L e :=
      mul_le_mul_of_nonneg_right (le_abs_self Kc) hLepos.le
    have h1 : Kc * Real.rpow L e * tau ≤ |Kc| * Real.rpow L e * tau :=
      mul_le_mul_of_nonneg_right h1a htau0
    have h2a : |Kc| * Real.rpow L e ≤ 3 * K0 * Real.rpow L e :=
      mul_le_mul_of_nonneg_right hKcabs hLepos.le
    have h2 : |Kc| * Real.rpow L e * tau ≤ 3 * K0 * Real.rpow L e * tau :=
      mul_le_mul_of_nonneg_right h2a htau0
    have h3a : 0 ≤ 3 * K0 * Real.rpow L e :=
      mul_nonneg (by linarith only [hK00] : (0 : ℝ) ≤ 3 * K0) hLepos.le
    have h3 : 3 * K0 * Real.rpow L e * tau ≤ 3 * K0 * Real.rpow L e * (2 * A * L) :=
      mul_le_mul_of_nonneg_left htaule h3a
    have h4 : 3 * K0 * Real.rpow L e * (2 * A * L) = 6 * K0 * A * Real.rpow L (e + 1) := by
      have hrr : Real.rpow L e * L = Real.rpow L (e + 1) := by
        have h := (Real.rpow_add hLpos e 1).symm
        rw [Real.rpow_one] at h
        exact h
      calc 3 * K0 * Real.rpow L e * (2 * A * L) = 6 * K0 * A * (Real.rpow L e * L) := by ring
        _ = 6 * K0 * A * Real.rpow L (e + 1) := by rw [hrr]
    have hexp4' : e + 1 ≤ -(3 / 2) := by
      rw [he]
      linarith only [halpha0]
    have h5 : Real.rpow L (e + 1) ≤ Real.rpow L (-(3 / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 hexp4'
    have h6 : 6 * K0 * A * Real.rpow L (e + 1) ≤ 6 * K0 * A * Real.rpow L (-(3 / 2)) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    calc Kc * Real.rpow L e * tau ≤ |Kc| * Real.rpow L e * tau := h1
      _ ≤ 3 * K0 * Real.rpow L e * tau := h2
      _ ≤ 3 * K0 * Real.rpow L e * (2 * A * L) := h3
      _ = 6 * K0 * A * Real.rpow L (e + 1) := h4
      _ ≤ 6 * K0 * A * Real.rpow L (-(3 / 2)) := h6
  set S : ℝ := Real.rpow (m : ℝ) (-(1 / 4)) * Real.rpow L (3 / 4)
      + Real.rpow (m : ℝ) (-(1 / 2)) * Real.sqrt tau
      + Real.rpow (Kc * Real.rpow L e) (1 / 3) * Real.rpow tau (2 / 3)
      + Kc * Real.rpow L e * tau with hS
  have hsqrt_eq : Real.sqrt L = Real.rpow L (1 / 2) := Real.sqrt_eq_rpow L
  have hA1nonneg : 0 ≤ Real.rpow L (-(3 / 2)) := Real.rpow_nonneg hLpos.le _
  have hbr : S ≤ C4 * Real.rpow L (-(3 / 2)) := by
    have hs : S ≤ ((Real.rpow L (-(3 / 2)) + Real.rpow L (-(3 / 2)))
        + C3 * Real.rpow L (-(3 / 2))) + 6 * K0 * A * Real.rpow L (-(3 / 2)) := by
      rw [hS]
      exact add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) hterm4
    have heq : ((Real.rpow L (-(3 / 2)) + Real.rpow L (-(3 / 2)))
          + C3 * Real.rpow L (-(3 / 2))) + 6 * K0 * A * Real.rpow L (-(3 / 2))
        = C4 * Real.rpow L (-(3 / 2)) := by
      rw [hC4]
      ring
    exact le_trans hs heq.le
  have hstep : 3 * Cbv * S ≤ Real.sqrt L * Real.rpow L (-(3 / 2)) := by
    have h0 : 0 ≤ 3 * Cbv := by linarith only [hCbv0]
    have h1 : 3 * Cbv * S ≤ 3 * Cbv * (C4 * Real.rpow L (-(3 / 2))) :=
      mul_le_mul_of_nonneg_left hbr h0
    have h2 : 3 * Cbv * (C4 * Real.rpow L (-(3 / 2))) = 3 * Cbv * C4 * Real.rpow L (-(3 / 2)) := by
      ring
    have h3 : 3 * Cbv * C4 * Real.rpow L (-(3 / 2)) ≤ Real.sqrt L * Real.rpow L (-(3 / 2)) :=
      mul_le_mul_of_nonneg_right hC4le hA1nonneg
    exact le_trans (le_trans h1 h2.le) h3
  have hfin : Real.sqrt L * Real.rpow L (-(3 / 2)) = L⁻¹ := by
    have h4 : Real.sqrt L * Real.rpow L (-(3 / 2)) = Real.rpow L (1 / 2) * Real.rpow L (-(3 / 2)) := by
      rw [hsqrt_eq]
    have h5 : Real.rpow L (1 / 2) * Real.rpow L (-(3 / 2)) = Real.rpow L (1 / 2 + -(3 / 2)) :=
      (Real.rpow_add hLpos (1 / 2) (-(3 / 2))).symm
    have h6 : Real.rpow L (1 / 2 + -(3 / 2)) = Real.rpow L (-1) := by
      rw [show (1 : ℝ) / 2 + -(3 / 2) = -1 by norm_num]
    have h7 : Real.rpow L (-1) = L⁻¹ := Real.rpow_neg_one L
    exact h4.trans (h5.trans (h6.trans h7))
  calc 3 * Cbv * S ≤ Real.sqrt L * Real.rpow L (-(3 / 2)) := hstep
    _ = L⁻¹ := hfin
    _ = 1 * L⁻¹ := by rw [one_mul]
  /- @proof-region region.target-node.session.6a66cbfe8d1ea75c end -/

end Statlib.Imported

