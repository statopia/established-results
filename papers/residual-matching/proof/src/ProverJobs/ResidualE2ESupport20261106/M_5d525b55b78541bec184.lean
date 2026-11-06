import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_e61c1c594ceef591edfb
import ProverJobs.ResidualE2ESupport20261106.M_275039000c74a0fbe21e
import ProverJobs.ResidualE2ESupport20261106.M_85c4c52a0c79aeb67f28
import ProverJobs.ResidualE2ESupport20261106.M_703efae8fa3f87b78451
import ProverJobs.ResidualE2ESupport20261106.M_d90c4508c8207afb518a
import ProverJobs.ResidualE2ESupport20261106.M_00c5010fc90cd7d8d9f5
import ProverJobs.ResidualE2ESupport20261106.M_cb35079d62bdf2ae9f71

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
theorem statopia_math_node_69799842_f5d4fc65 : ∀ (D0 Kt alpha0 CD : ℝ)
    (hD0 : 0 < D0) (hKt : 0 < Kt) (halpha0 : 15 < alpha0)
    (hCD : Kt * (D0 + 12) ≤ CD),
    ∃ M0 : ℕ,
      ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → n ≤ m → M0 ≤ m →
        ∀ (p : ℝ), 0 < p → p ≤ 1 →
          Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p →
            ∀ (ν : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν],
              (∀ (i : Fin m) (j : Fin n), ∫ x, (x i j) ^ 2 ∂ν = 1) →
                (∀ (i : Fin m) (j : Fin n), ∫ x, x i j ∂ν = 0) →
                  (∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
                      ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|} ≤
                        ENNReal.ofReal (2 * Real.exp (-t / Kt))) →
                    ∀ (b c : Fin m → Fin n → ℝ)
                      (XT : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ),
                      (∀ (i : Fin m) (j : Fin n),
                          b i j = ∫ x, x i j * (if |x i j| ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 then (1 : ℝ) else 0) ∂ν) →
                        (∀ (i : Fin m) (j : Fin n),
                            c i j = Real.sqrt (∫ x, (x i j * (if |x i j| ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν)) →
                          (∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
                              XT x i j = (x i j * (if |x i j| ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 then (1 : ℝ) else 0) - b i j) / c i j) →
                            (∀ (i : Fin m) (j : Fin n), 0 < c i j) ∧
                              (∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
                                  |XT x i j| ≤ 3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)) ∧
                                (ν {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n), CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 < |x i j|} ≤
                                    ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10)))) ∧
                                  (∀ (M : Matrix (Fin m) (Fin n) ℝ),
                                      (∀ (i : Fin m) (j : Fin n), M i j = 0 ∨ M i j = 1) →
                                        ∀ (x : Matrix (Fin m) (Fin n) ℝ),
                                          (∀ (i : Fin m) (j : Fin n), |x i j| ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4) →
                                            ‖(fun (i : Fin m) (j : Fin n) =>
                                                maskedScaled p x M i j - maskedScaled p (XT x) M i j)‖ ≤ Real.rpow (n : ℝ) (-(D0 + 5))) := by
  /- @proof-region region.target-node.session.380dadf345e65dba begin -/
  intro D0 Kt alpha0 CD hD0 hKt halpha0 hCD
  have hCDpos : 0 < CD := by nlinarith [hCD, hKt, hD0]
  set C0 : ℝ := (10:ℝ)^6 * (Kt + 1)^4 * (D0 + 1)^4 * (alpha0 + 1)^4 with hC0
  have hC0ge2 : 2 ≤ C0 := by
    have h1 : (1:ℝ) ≤ (Kt + 1)^4 := one_le_pow₀ (by linarith)
    have h2 : (1:ℝ) ≤ (D0 + 1)^4 := one_le_pow₀ (by linarith)
    have h3 : (1:ℝ) ≤ (alpha0 + 1)^4 := one_le_pow₀ (by linarith)
    have h4 : (2:ℝ) ≤ (10:ℝ)^6 := by norm_num
    have h5 : (2:ℝ) ≤ (10:ℝ)^6 * (Kt + 1)^4 := by
      have hm := mul_le_mul h4 h1 (show (0:ℝ) ≤ 1 by norm_num)
        (show (0:ℝ) ≤ (10:ℝ)^6 by norm_num)
      simpa using hm
    have h6 : (2:ℝ) ≤ (10:ℝ)^6 * (Kt + 1)^4 * (D0 + 1)^4 := by
      have hb : (0:ℝ) ≤ (10:ℝ)^6 * (Kt + 1)^4 := by positivity
      have hm := mul_le_mul h5 h2 (show (0:ℝ) ≤ 1 by norm_num) hb
      simpa using hm
    have h7 : (2:ℝ) ≤ (10:ℝ)^6 * (Kt + 1)^4 * (D0 + 1)^4 * (alpha0 + 1)^4 := by
      have hb : (0:ℝ) ≤ (10:ℝ)^6 * (Kt + 1)^4 * (D0 + 1)^4 := by positivity
      have hm := mul_le_mul h6 h3 (show (0:ℝ) ≤ 1 by norm_num) hb
      simpa using hm
    rw [hC0]
    exact h7
  set D1 : ℝ := 2 * CD + C0 + Kt + 1 with hD1
  have hD1pos : 0 < D1 := by rw [hD1]; linarith
  set A : ℝ := 100 * (1 + Kt) * (1 + D1) ^ 2 with hA
  have hApos : 0 < A := by rw [hA]; positivity

  obtain ⟨M0, hM03, haux⟩ :=
    statopia_math_node_3923772922_929a3872 D0 Kt D1 A hD0 hKt
      (add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt hD1pos)) hA
  have hM0 : ∀ m : ℕ, M0 ≤ m → A * Real.rpow (m : ℝ) (-(D0 + 9)) ≤ 1 :=
    fun m h => (haux m h).1
  have hthrM : ∀ m : ℕ, M0 ≤ m →
      24 * (1 + Kt) * (1 + D1) ^ 3 * Real.rpow (m : ℝ) (-(D0 + 8)) ≤ 1 :=
    fun m h => (haux m h).2



  refine ⟨M0, ?_⟩

  intro m n hm hn hnm hMm p hp0 hp1 hsparse ν hν hvar hmean htail b c XT hb hc hXT
  set L : ℝ := CD * Real.log ((m : ℝ) * (n : ℝ)) + C0 with hL
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hmn1 : (1:ℝ) ≤ (m:ℝ) * (n : ℝ) := by
    have hm' := mul_le_mul hm1 hn1 (show (0:ℝ) ≤ 1 by norm_num)
      (show (0:ℝ) ≤ (m:ℝ) by linarith)
    simpa using hm'
  have hlog0 : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := Real.log_nonneg hmn1
  have hL2 : 2 ≤ L := by
    have hmul : 0 ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := mul_nonneg (le_of_lt hCDpos) hlog0
    rw [hL]
    linarith
  set E : ℝ := Real.exp (-L / Kt) with hEdef
  have hEpos : 0 < E := by rw [hEdef]; positivity
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hL2
  have hmom : ∀ (i : Fin m) (j : Fin n),
      |b i j| ≤ 2 * (L + Kt) * E ∧
        1 - (c i j) ^ 2 ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E + 4 * (L + Kt) ^ 2 * E ^ 2 :=
    fun i j =>
      statopia_math_node_2154310619_f2ebfa07 m n ν i j L Kt (b i j) (c i j) hKt hLpos
        (hmean i j) (hvar i j) (htail i j) (hb i j) (hc i j)
  have hmom1 : ∀ (i : Fin m) (j : Fin n), |b i j| ≤ 2 * (L + Kt) * E :=
    fun i j => (hmom i j).1
  have hmom2 : ∀ (i : Fin m) (j : Fin n),
      1 - (c i j) ^ 2 ≤ (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E + 4 * (L + Kt) ^ 2 * E ^ 2 :=
    fun i j => (hmom i j).2
  have hthr := statopia_math_node_3064412691_7282c3bb D0 Kt CD C0 D1 A L E m n
    hD0 hKt hCD hC0ge2 hm hn hnm hD1 hA hL hEdef (hM0 m hMm)
  have hthr1 : 2 * (L + Kt) * E ≤ 1 := hthr.1
  have hthr2 : (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E + 4 * (L + Kt) ^ 2 * E ^ 2 ≤ 1 / 2 := hthr.2





  have hb1 : ∀ (i : Fin m) (j : Fin n), |b i j| ≤ 1 := by
    intro i j
    exact le_trans (hmom1 i j) hthr1
  have hc2half : ∀ (i : Fin m) (j : Fin n), (1:ℝ) / 2 ≤ (c i j) ^ 2 := by
    intro i j
    have h2 : (1:ℝ) - (c i j) ^ 2 ≤ 1 / 2 := le_trans (hmom2 i j) hthr2
    have h3 : (1:ℝ) / 2 + 1 / 2 ≤ 1 / 2 + (c i j) ^ 2 := by
      have h := add_le_add_right h2 ((c i j) ^ 2)
      calc (1:ℝ) / 2 + 1 / 2 = (c i j) ^ 2 + (1 - (c i j) ^ 2) := by ring
        _ ≤ (c i j) ^ 2 + 1 / 2 := h
        _ = 1 / 2 + (c i j) ^ 2 := by ring
    exact le_of_add_le_add_left h3


  have hcnonneg : ∀ (i : Fin m) (j : Fin n), 0 ≤ c i j := by
    intro i j
    rw [hc i j]
    exact Real.sqrt_nonneg _
  have hcpos : ∀ (i : Fin m) (j : Fin n), 0 < c i j := by
    intro i j
    have h := hc2half i j
    have hnn := hcnonneg i j
    have hne : c i j ≠ 0 := by
      intro h0
      rw [h0] at h
      norm_num at h
    exact lt_of_le_of_ne hnn (Ne.symm hne)



  have hXTbound : ∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
      |XT x i j| ≤ 3 * L := by
    intro x i j
    have h1 : |x i j * (if |x i j| ≤ L then (1:ℝ) else 0)| ≤ L := by
      by_cases h : (|x i j| ≤ L)
      · rw [if_pos h, mul_one]; exact h
      · rw [if_neg h, mul_zero, abs_zero]; exact le_of_lt hLpos
    have hb3 : |x i j * (if |x i j| ≤ L then (1:ℝ) else 0) - b i j| ≤ L + 1 := by
      rw [sub_eq_add_neg]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_neg]
      exact add_le_add h1 (hb1 i j)
    have hc1 : (1:ℝ)/2 ≤ c i j := by
      rcases le_total ((1:ℝ)/2) (c i j) with h | h
      · exact h
      · exfalso
        have hcnn : (0:ℝ) ≤ c i j := le_of_lt (hcpos i j)
        have hs1 : c i j * c i j ≤ c i j * ((1:ℝ)/2) := mul_le_mul_of_nonneg_left h hcnn
        have hs2 : c i j * ((1:ℝ)/2) ≤ ((1:ℝ)/2) * ((1:ℝ)/2) :=
          mul_le_mul_of_nonneg_right h (by norm_num)
        have hsq : (c i j) ^ 2 ≤ 1/4 := by
          have e : (c i j) ^ 2 = c i j * c i j := by ring
          rw [e]
          refine le_trans hs1 (le_trans hs2 ?_)
          norm_num
        exact absurd (le_trans (hc2half i j) hsq) (by norm_num)
    have hhalf : (1:ℝ) ≤ L * ((1:ℝ)/2) := by
      have h := mul_le_mul_of_nonneg_right hL2 (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
      have e : (2:ℝ) * ((1:ℝ)/2) = 1 := by norm_num
      rwa [e] at h
    have h3L : (0:ℝ) ≤ 3 * L := mul_nonneg (by norm_num) (le_of_lt hLpos)
    have hA1 : L + 1 ≤ 3 * L * ((1:ℝ)/2) := by
      have h := add_le_add_left hhalf L
      have h' : L + 1 ≤ L + L * ((1:ℝ)/2) := by simpa only [add_comm] using h
      have he : L + L * ((1:ℝ)/2) = 3 * L * ((1:ℝ)/2) := by ring
      rw [he] at h'
      exact h'
    have hmid : L + 1 ≤ 3 * L * c i j :=
      le_trans hA1 (mul_le_mul_of_nonneg_left hc1 h3L)
    rw [hXT x i j, abs_div, abs_of_pos (hcpos i j)]
    exact (div_le_iff₀ (hcpos i j)).mpr (le_trans hb3 hmid)







  have htailun : ν {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n), L < |x i j|} ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10))) :=
    statopia_math_node_2053018745_c199926d D0 Kt CD C0 L E m n ν hD0 hKt hCD
      (le_trans (by norm_num : (0:ℝ) ≤ 2) hC0ge2) (le_trans hM03 hMm) hn hL hEdef hLpos htail
  have hgd := statopia_math_node_1768303233_f2c5ce27 D0 Kt CD C0 D1 L E m n
    hD0 hKt hCD (le_trans (by norm_num : (0:ℝ) ≤ 2) hC0ge2) (le_trans hM03 hMm) hn hnm hD1 hL hEdef
  have hLK : L + Kt ≤ D1 * (m : ℝ) := hgd.1
  have hEdec : E ≤ Real.rpow ((m : ℝ) * (n : ℝ)) (-(D0 + 12)) := hgd.2


  have htrans : ∀ (M : Matrix (Fin m) (Fin n) ℝ),
      (∀ (i : Fin m) (j : Fin n), M i j = 0 ∨ M i j = 1) →
        ∀ (x : Matrix (Fin m) (Fin n) ℝ),
          (∀ (i : Fin m) (j : Fin n), |x i j| ≤ L) →
            ‖(fun (i : Fin m) (j : Fin n) =>
                maskedScaled p x M i j - maskedScaled p (XT x) M i j)‖ ≤
              Real.rpow (n : ℝ) (-(D0 + 5)) := by
    have hcsq : ∀ (i : Fin m) (j : Fin n),
        |1 - (c i j) ^ 2| ≤
          (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E + 4 * (L + Kt) ^ 2 * E ^ 2 := by
      intro i j
      have hupper : (c i j) ^ 2 ≤ 1 :=
        statopia_math_node_1895661039_5283179a m n ν i j L (b i j) (c i j)
          (hvar i j) (hb i j) (hc i j)
      have hnn : (0:ℝ) ≤ 1 - (c i j) ^ 2 := sub_nonneg.mpr hupper
      rw [abs_of_nonneg hnn]
      exact hmom2 i j
    intro M hM x hx
    exact statopia_math_node_254483913_a2e212e7 D0 Kt alpha0 D1 L E p m n b c XT
      hD0 hKt halpha0 hD1pos (le_trans hM03 hMm) hn hnm hL2 hLK hp0 hp1 hsparse
      hEpos hEdec hthr2 hcsq hcpos hmom1 hXT (hthrM m hMm) M hM x hx
  exact ⟨hcpos, hXTbound, htailun, htrans⟩

  /- @proof-region region.target-node.session.380dadf345e65dba end -/

end Statlib.Imported

