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
theorem statopia_math_node_254483913_a2e212e7 : ∀ (D0 Kt alpha0 CL L E p : ℝ) (m n : ℕ)
    (b c : Fin m → Fin n → ℝ)
    (XT : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ)
    (hD0 : 0 < D0) (hKt : 0 < Kt) (halpha0 : 15 < alpha0) (hCL : 0 < CL)
    (hm : 3 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hL : 2 ≤ L)
    (hLK : L + Kt ≤ CL * (m : ℝ))
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
    (hE0 : 0 < E)
    (hEdec : E ≤ Real.rpow ((m : ℝ) * (n : ℝ)) (-(D0 + 12)))
    (hthr2 : (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E + 4 * (L + Kt) ^ 2 * E ^ 2 ≤ 1 / 2)
    (hcsq : ∀ (i : Fin m) (j : Fin n),
      |1 - (c i j) ^ 2| ≤
        (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E + 4 * (L + Kt) ^ 2 * E ^ 2)
    (hcpos : ∀ (i : Fin m) (j : Fin n), 0 < c i j)
    (hb : ∀ (i : Fin m) (j : Fin n), |b i j| ≤ 2 * (L + Kt) * E)
    (hXT : ∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
      XT x i j = (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j)
    (hthrM : 24 * (1 + Kt) * (1 + CL) ^ 3 * Real.rpow (m : ℝ) (-(D0 + 8)) ≤ 1)
    (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ (i : Fin m) (j : Fin n), M i j = 0 ∨ M i j = 1)
    (x : Matrix (Fin m) (Fin n) ℝ)
    (hx : ∀ (i : Fin m) (j : Fin n), |x i j| ≤ L),
      
      
      
      ‖(fun (i : Fin m) (j : Fin n) =>
          (maskedScaled p x M - maskedScaled p (XT x) M) i j)‖ ≤
        Real.rpow (n : ℝ) (-(D0 + 5)) := by
  /- @proof-region region.target-node.session.300c6df449b6ff3f begin -/
  intro D0 Kt alpha0 CL L E p m n b c XT hD0 hKt halpha0 hCL hm hn hnm hL hLK hp0 hp1 hsparse hE0 hEdec hthr2 hcsq hcpos hb hXT hthrM M hM x hx
  have hmR3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmR1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hmR0 : (0 : ℝ) ≤ (m : ℝ) := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hKtnn : (0 : ℝ) ≤ Kt := le_of_lt hKt
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hLKnn : (0 : ℝ) ≤ L + Kt := by linarith
  have hEnn : (0 : ℝ) ≤ E := le_of_lt hE0
  set C : ℝ := CL * (m : ℝ) with hC
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hC]
    linarith
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hLC : L ≤ C := by
    rw [hC]
    linarith
  have hLKC : L + Kt ≤ C := by
    rw [hC]
    exact hLK
  set S : ℝ := (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E + 4 * (L + Kt) ^ 2 * E ^ 2 with hSdef
  have hS_le_half : S ≤ 1 / 2 := by
    rw [hSdef]
    exact hthr2
  have hAp : (0 : ℝ) ≤ 2 * L ^ 2 + 4 * Kt * (L + Kt) := by
    have h1 : (0 : ℝ) ≤ 2 * L ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 4 * Kt * (L + Kt) := mul_nonneg (mul_nonneg (by norm_num) hKtnn) hLKnn
    linarith
  have hBp : (0 : ℝ) ≤ 4 * (L + Kt) ^ 2 := by positivity
  have hS_nonneg : (0 : ℝ) ≤ S := by
    rw [hSdef]
    exact add_nonneg (mul_nonneg hAp hEnn) (mul_nonneg hBp (sq_nonneg E))
  have hbase1 : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by
    have h := mul_le_mul hmR1 hnR1 (by norm_num : (0 : ℝ) ≤ 1) hmR0
    simpa using h
  have hE1 : E ≤ 1 := by
    refine le_trans hEdec ?_
    have h := Real.rpow_le_rpow_of_exponent_le hbase1 (show (-(D0 + 12) : ℝ) ≤ 0 by linarith)
    simpa using h
  have hEsq : E ^ 2 ≤ E := by
    have h : E * E ≤ E * 1 := mul_le_mul_of_nonneg_left hE1 hEnn
    simpa [pow_two] using h
  have hlog1 : (1 : ℝ) ≤ Real.log (m : ℝ) := by
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
      linarith [Real.exp_one_lt_three]
    have h4 : Real.log 3 ≤ Real.log (m : ℝ) := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)]
      rw [Real.exp_log hmpos]
      exact hmR3
    linarith
  have hpow1 : (1 : ℝ) ≤ Real.rpow (Real.log (m : ℝ)) alpha0 := by
    have h := Real.rpow_le_rpow_of_exponent_le hlog1 (show (0 : ℝ) ≤ alpha0 by linarith)
    simpa using h
  have hmp1 : (1 : ℝ) ≤ (m : ℝ) * p := le_trans hpow1 hsparse
  have hsq1 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) * p) := by
    rw [Real.one_le_sqrt]
    exact hmp1
  set rm : ℝ := Real.rpow (m : ℝ) (-(D0 + 12)) with hrm
  set rn : ℝ := Real.rpow (n : ℝ) (-(D0 + 12)) with hrn
  set rm8 : ℝ := Real.rpow (m : ℝ) (-(D0 + 8)) with hrm8
  set A : ℝ := 24 * (1 + Kt) * (1 + CL) ^ 3 with hA
  have hrm0 : (0 : ℝ) ≤ rm := by
    rw [hrm]
    exact Real.rpow_nonneg hmR0 _
  have hrn0 : (0 : ℝ) ≤ rn := by
    rw [hrn]
    exact Real.rpow_nonneg hnR0 _
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]
    have h1 : (0 : ℝ) ≤ 24 * (1 + Kt) := by linarith
    have h2 : (0 : ℝ) ≤ (1 + CL) ^ 3 := pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + CL) 3
    exact mul_nonneg h1 h2
  have hEdec' : E ≤ rm * rn := by
    rw [hrm, hrn]
    calc E ≤ Real.rpow ((m : ℝ) * (n : ℝ)) (-(D0 + 12)) := hEdec
      _ = Real.rpow (m : ℝ) (-(D0 + 12)) * Real.rpow (n : ℝ) (-(D0 + 12)) := Real.mul_rpow hmR0 hnR0
  have hthrM' : A * rm8 ≤ 1 := by
    rw [hA, hrm8]
    exact hthrM
  have hm3eq : (m : ℝ) ^ 3 = Real.rpow (m : ℝ) (3 : ℝ) := (Real.rpow_natCast (m : ℝ) 3).symm
  have hpow3 : (m : ℝ) ^ 3 * rm ≤ rm8 := by
    have hEq : (m : ℝ) ^ 3 * rm = Real.rpow (m : ℝ) ((3 : ℝ) + -(D0 + 12)) := by
      rw [hrm, hm3eq]
      exact (Real.rpow_add hmpos (3 : ℝ) (-(D0 + 12))).symm
    calc (m : ℝ) ^ 3 * rm = Real.rpow (m : ℝ) ((3 : ℝ) + -(D0 + 12)) := hEq
      _ ≤ Real.rpow (m : ℝ) (-(D0 + 8)) := Real.rpow_le_rpow_of_exponent_le hmR1 (by linarith)
      _ = rm8 := hrm8.symm
  have hKtC : Kt ≤ C := by linarith [hLKC, hLnn]
  have hS_le : S ≤ 10 * C ^ 2 * E := by
    rw [hSdef]
    have hL2 : L ^ 2 ≤ C ^ 2 := by
      have h := mul_le_mul hLC hLC hLnn hC0
      calc L ^ 2 = L * L := by rw [pow_two]
        _ ≤ C * C := h
        _ = C ^ 2 := by rw [pow_two]
    have hLK2 : (L + Kt) ^ 2 ≤ C ^ 2 := by
      have h := mul_le_mul hLKC hLKC hLKnn hC0
      calc (L + Kt) ^ 2 = (L + Kt) * (L + Kt) := by rw [pow_two]
        _ ≤ C * C := h
        _ = C ^ 2 := by rw [pow_two]
    have hKtLK : Kt * (L + Kt) ≤ C ^ 2 := by
      have h := mul_le_mul hKtC hLKC hLKnn hC0
      calc Kt * (L + Kt) ≤ C * C := h
        _ = C ^ 2 := by rw [pow_two]
    have hA' : 2 * L ^ 2 + 4 * Kt * (L + Kt) ≤ 6 * C ^ 2 := by linarith [hL2, hKtLK]
    have h1 : (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E ≤ 6 * C ^ 2 * E :=
      mul_le_mul_of_nonneg_right hA' hEnn
    have h2a : 4 * (L + Kt) ^ 2 ≤ 4 * C ^ 2 := by linarith [hLK2]
    have h2b : 4 * (L + Kt) ^ 2 * E ^ 2 ≤ 4 * C ^ 2 * E ^ 2 :=
      mul_le_mul_of_nonneg_right h2a (sq_nonneg E)
    have h2c : 4 * C ^ 2 * E ^ 2 ≤ 4 * C ^ 2 * E :=
      mul_le_mul_of_nonneg_left hEsq (by positivity)
    have h2d : 4 * C ^ 2 * E ≤ 10 * C ^ 2 * E := by
      have hce : (0 : ℝ) ≤ C ^ 2 * E := mul_nonneg (sq_nonneg C) hEnn
      have h : 4 * (C ^ 2 * E) ≤ 10 * (C ^ 2 * E) := by linarith [hce]
      calc 4 * C ^ 2 * E = 4 * (C ^ 2 * E) := by ring
        _ ≤ 10 * (C ^ 2 * E) := h
        _ = 10 * C ^ 2 * E := by ring
    linarith [h1, h2b, h2c, h2d]
  have hδ_le : 2 * L * S + 4 * (L + Kt) * E ≤ 24 * C ^ 3 * E := by
    have h1 : 2 * L * S ≤ 20 * C ^ 3 * E := by
      have h2L : (2 : ℝ) * L ≤ 2 * C := by linarith [hLC]
      have h3 : (2 * L) * S ≤ (2 * C) * S := mul_le_mul_of_nonneg_right h2L hS_nonneg
      have h4 : (2 * C) * S ≤ (2 * C) * (10 * C ^ 2 * E) :=
        mul_le_mul_of_nonneg_left hS_le (by linarith [hC0])
      have hid : (2 * C) * (10 * C ^ 2 * E) = 20 * C ^ 3 * E := by ring
      linarith [h3, h4, hid]
    have h4 : 4 * (L + Kt) * E ≤ 4 * C * E := by
      have h : (4 : ℝ) * (L + Kt) ≤ 4 * C := by linarith [hLKC]
      exact mul_le_mul_of_nonneg_right h hEnn
    have hpow : C ≤ C ^ 3 := by
      have h := Bound.pow_le_pow_right_of_le_one_or_one_le (a := C) (n := 1) (m := 3) (Or.inl ⟨hC1, by norm_num⟩)
      simpa using h
    have h6 : 4 * C * E ≤ 4 * C ^ 3 * E := by
      have h : (4 : ℝ) * C ≤ 4 * C ^ 3 := by linarith [hpow]
      exact mul_le_mul_of_nonneg_right h hEnn
    linarith [h1, h4, h6]
  have hCL2 : CL ^ 2 ≤ (1 + CL) ^ 2 := by
    have h1CL : CL ≤ 1 + CL := by linarith
    have h := mul_le_mul h1CL h1CL (le_of_lt hCL) (by linarith : (0 : ℝ) ≤ 1 + CL)
    calc CL ^ 2 = CL * CL := by rw [pow_two]
      _ ≤ (1 + CL) * (1 + CL) := h
      _ = (1 + CL) ^ 2 := by rw [pow_two]
  have hCL3a : CL ^ 3 ≤ (1 + CL) ^ 3 := by
    have h1CL : CL ≤ 1 + CL := by linarith
    calc CL ^ 3 = CL ^ 2 * CL := by ring
      _ ≤ (1 + CL) ^ 2 * (1 + CL) := mul_le_mul hCL2 h1CL (le_of_lt hCL) (sq_nonneg (1 + CL))
      _ = (1 + CL) ^ 3 := by ring
  have hCL3 : CL ^ 3 ≤ (1 + Kt) * (1 + CL) ^ 3 := by
    have h2 : (1 + CL) ^ 3 ≤ (1 + Kt) * (1 + CL) ^ 3 := by
      have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + Kt by linarith)
        (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + CL) 3)
      simpa using h
    linarith [hCL3a, h2]
  have hcoef : 24 * C ^ 3 ≤ A * (m : ℝ) ^ 3 := by
    have hmain : 24 * (CL * (m : ℝ)) ^ 3 ≤ 24 * (1 + Kt) * (1 + CL) ^ 3 * (m : ℝ) ^ 3 := by
      have hm3 : (CL * (m : ℝ)) ^ 3 = CL ^ 3 * (m : ℝ) ^ 3 := by ring
      have hprod : CL ^ 3 * (m : ℝ) ^ 3 ≤ ((1 + Kt) * (1 + CL) ^ 3) * (m : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hCL3 (pow_nonneg hmR0 3)
      calc 24 * (CL * (m : ℝ)) ^ 3 = 24 * (CL ^ 3 * (m : ℝ) ^ 3) := by rw [hm3]
        _ ≤ 24 * (((1 + Kt) * (1 + CL) ^ 3) * (m : ℝ) ^ 3) := by linarith [hprod]
        _ = 24 * (1 + Kt) * (1 + CL) ^ 3 * (m : ℝ) ^ 3 := by ring
    rw [hA, hC]
    exact hmain
  have hfinal : 24 * C ^ 3 * E ≤ Real.rpow (n : ℝ) (-(D0 + 5)) := by
    have hC3 : (0 : ℝ) ≤ 24 * C ^ 3 := by
      have h : (0 : ℝ) ≤ C ^ 3 := pow_nonneg hC0 3
      linarith
    have h1 : 24 * C ^ 3 * E ≤ 24 * C ^ 3 * (rm * rn) := mul_le_mul_of_nonneg_left hEdec' hC3
    have h2 : 24 * C ^ 3 * (rm * rn) ≤ A * (m : ℝ) ^ 3 * (rm * rn) := by
      apply mul_le_mul_of_nonneg_right hcoef
      exact mul_nonneg hrm0 hrn0
    have h3 : A * (m : ℝ) ^ 3 * (rm * rn) ≤ A * rm8 * rn := by
      have h6 : A * ((m : ℝ) ^ 3 * rm) ≤ A * rm8 := mul_le_mul_of_nonneg_left hpow3 hA0
      have h7 := mul_le_mul_of_nonneg_right h6 hrn0
      calc A * (m : ℝ) ^ 3 * (rm * rn) = A * ((m : ℝ) ^ 3 * rm) * rn := by ring
        _ ≤ A * rm8 * rn := h7
    have h4 : A * rm8 * rn ≤ rn := by
      calc A * rm8 * rn ≤ 1 * rn := mul_le_mul_of_nonneg_right hthrM' hrn0
        _ = rn := one_mul rn
    have h5 : rn ≤ Real.rpow (n : ℝ) (-(D0 + 5)) := by
      rw [hrn]
      exact Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)
    exact le_trans h1 (le_trans h2 (le_trans h3 (le_trans h4 h5)))
  have hrhs : (0 : ℝ) ≤ Real.rpow (n : ℝ) (-(D0 + 5)) := Real.rpow_nonneg hnR0 _
  rw [show ‖(fun (i : Fin m) (j : Fin n) =>
      (maskedScaled p x M - maskedScaled p (XT x) M) i j)‖
      = dist (fun (i : Fin m) (j : Fin n) =>
          (maskedScaled p x M - maskedScaled p (XT x) M) i j) 0 from by
    rw [dist_eq_norm, sub_zero]]
  rw [dist_pi_le_iff (f := fun (i : Fin m) (j : Fin n) =>
      (maskedScaled p x M - maskedScaled p (XT x) M) i j) (g := 0) hrhs]
  intro i
  show dist (fun j : Fin n => (maskedScaled p x M - maskedScaled p (XT x) M) i j) 0 ≤
    Real.rpow (n : ℝ) (-(D0 + 5))
  rw [dist_pi_le_iff (f := fun j : Fin n =>
      (maskedScaled p x M - maskedScaled p (XT x) M) i j) (g := 0) hrhs]
  intro j
  show dist ((maskedScaled p x M - maskedScaled p (XT x) M) i j) 0 ≤ Real.rpow (n : ℝ) (-(D0 + 5))
  rw [dist_eq_norm, sub_zero]
  have hc : 0 < c i j := hcpos i j
  have hcsqij : |1 - (c i j) ^ 2| ≤ S := by
    rw [hSdef]
    exact hcsq i j
  have hc2 : (1 / 2 : ℝ) ≤ (c i j) ^ 2 := by
    have h1 : (1 : ℝ) - S ≤ (c i j) ^ 2 := by
      have h := (abs_le.mp hcsqij).2
      linarith [h]
    linarith [h1, hS_le_half]
  have hcge : (1 / 2 : ℝ) ≤ c i j := by
    have h1 : Real.sqrt (1 / 2) ≤ c i j := by
      have h := Real.sqrt_le_sqrt hc2
      rwa [Real.sqrt_sq (le_of_lt hc)] at h
    have h2 : (1 / 2 : ℝ) ≤ Real.sqrt (1 / 2) := by
      have h := Real.sqrt_le_sqrt (show ((1 : ℝ) / 2) ^ 2 ≤ 1 / 2 by norm_num)
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    linarith [h1, h2]
  have hc1 : |c i j - 1| ≤ S := by
    have hc1pos : (0 : ℝ) < c i j + 1 := by linarith
    have h0 : |c i j - 1| * (c i j + 1) = |(c i j) ^ 2 - 1| := by
      rw [← abs_of_pos hc1pos, ← abs_mul, show (c i j - 1) * (c i j + 1) = (c i j) ^ 2 - 1 by ring]
    have h1 : |(c i j) ^ 2 - 1| = |1 - (c i j) ^ 2| := by
      rw [show (c i j) ^ 2 - 1 = -(1 - (c i j) ^ 2) by ring, abs_neg]
    have h2 : |c i j - 1| * (c i j + 1) ≤ S := by
      rw [h0, h1]
      exact hcsqij
    have h3 : |c i j - 1| * 1 ≤ |c i j - 1| * (c i j + 1) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      linarith
    linarith [h2, h3]
  have hXTij : XT x i j = (x i j - b i j) / c i j := by
    rw [hXT x i j, if_pos (hx i j), mul_one]
  have hceq : x i j - XT x i j = (x i j * (c i j - 1) + b i j) / c i j := by
    rw [hXTij]
    field_simp
    ring
  have hΔ : |x i j - XT x i j| ≤ 2 * L * S + 4 * (L + Kt) * E := by
    have hnum : |x i j * (c i j - 1) + b i j| ≤ L * S + 2 * (L + Kt) * E := by
      have h1 : |x i j * (c i j - 1)| ≤ L * S := by
        rw [abs_mul]
        exact mul_le_mul (hx i j) hc1 (abs_nonneg _) hLnn
      have h2 : |x i j * (c i j - 1) + b i j| ≤ |x i j * (c i j - 1)| + |b i j| :=
        abs_add_le (x i j * (c i j - 1)) (b i j)
      linarith [h1, h2, hb i j]
    have hnum_nn : (0 : ℝ) ≤ L * S + 2 * (L + Kt) * E := by
      have h1 : (0 : ℝ) ≤ L * S := mul_nonneg hLnn hS_nonneg
      have h2 : (0 : ℝ) ≤ 2 * (L + Kt) * E := mul_nonneg (mul_nonneg (by norm_num) hLKnn) hEnn
      linarith [h1, h2]
    have h2c : (1 : ℝ) ≤ 2 * c i j := by linarith [hcge]
    have hstep1 : |(x i j * (c i j - 1) + b i j) / c i j| ≤ (L * S + 2 * (L + Kt) * E) / c i j := by
      rw [abs_div, abs_of_pos hc]
      exact div_le_div_of_nonneg_right hnum (le_of_lt hc)
    have hstep2 : (L * S + 2 * (L + Kt) * E) / c i j ≤ 2 * L * S + 4 * (L + Kt) * E := by
      rw [div_le_iff₀ hc]
      have hA1 : L * S + 2 * (L + Kt) * E ≤ (L * S + 2 * (L + Kt) * E) * (2 * c i j) := by
        have h := mul_le_mul_of_nonneg_left h2c hnum_nn
        simpa using h
      have he : (L * S + 2 * (L + Kt) * E) * (2 * c i j) = (2 * L * S + 4 * (L + Kt) * E) * c i j := by ring
      linarith [hA1, he]
    rw [hceq]
    linarith [hstep1, hstep2]
  have hM1 : |M i j| ≤ 1 := by
    rcases hM i j with h | h <;> simp [h]
  have hentry : (maskedScaled p x M - maskedScaled p (XT x) M) i j = M i j * (x i j - XT x i j) / Real.sqrt ((m : ℝ) * p) := by
    show M i j * x i j / Real.sqrt ((m : ℝ) * p) - M i j * XT x i j / Real.sqrt ((m : ℝ) * p) = M i j * (x i j - XT x i j) / Real.sqrt ((m : ℝ) * p)
    ring
  have hspos : (0 : ℝ) < Real.sqrt ((m : ℝ) * p) := by linarith [hsq1]
  have hδnn : (0 : ℝ) ≤ 2 * L * S + 4 * (L + Kt) * E := by
    have h1 : (0 : ℝ) ≤ 2 * L * S := mul_nonneg (mul_nonneg (by norm_num) hLnn) hS_nonneg
    have h2 : (0 : ℝ) ≤ 4 * (L + Kt) * E := mul_nonneg (mul_nonneg (by norm_num) hLKnn) hEnn
    linarith [h1, h2]
  have hnum2 : |M i j * (x i j - XT x i j)| ≤ 2 * L * S + 4 * (L + Kt) * E := by
    rw [abs_mul]
    have h1 : |M i j| * |x i j - XT x i j| ≤ 1 * (2 * L * S + 4 * (L + Kt) * E) :=
      mul_le_mul hM1 hΔ (abs_nonneg _) (by norm_num)
    simpa using h1
  have hb1 : |(maskedScaled p x M - maskedScaled p (XT x) M) i j| ≤ (2 * L * S + 4 * (L + Kt) * E) / Real.sqrt ((m : ℝ) * p) := by
    rw [hentry, abs_div, abs_of_pos hspos]
    exact div_le_div_of_nonneg_right hnum2 (le_of_lt hspos)
  have hb2 : (2 * L * S + 4 * (L + Kt) * E) / Real.sqrt ((m : ℝ) * p) ≤ 2 * L * S + 4 * (L + Kt) * E := by
    rw [div_le_iff₀ hspos]
    have h : (2 * L * S + 4 * (L + Kt) * E) * 1 ≤ (2 * L * S + 4 * (L + Kt) * E) * Real.sqrt ((m : ℝ) * p) :=
      mul_le_mul_of_nonneg_left hsq1 hδnn
    linarith [h]
  have hb3 : 2 * L * S + 4 * (L + Kt) * E ≤ Real.rpow (n : ℝ) (-(D0 + 5)) := le_trans hδ_le hfinal
  exact le_trans hb1 (le_trans hb2 hb3)
  /- @proof-region region.target-node.session.300c6df449b6ff3f end -/

end Statlib.Imported

