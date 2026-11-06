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
theorem statopia_math_node_2053018745_c199926d : ∀ (D0 Kt CD C0 L E : ℝ) (m n : ℕ)
    (ν : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν]
    (hD0 : 0 < D0) (hKt : 0 < Kt) (hCD : Kt * (D0 + 12) ≤ CD)
    (hC0 : 0 ≤ C0) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) + C0)
    (hE : E = Real.exp (-L / Kt)) (hLpos : 0 < L)
    (htail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
      ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|} ≤
        ENNReal.ofReal (2 * Real.exp (-t / Kt))),
    ν {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n), L < |x i j|} ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 10))) := by
  /- @proof-region region.target-node.session.5a02943772a70618 begin -/
  intro D0 Kt CD C0 L E m n ν hprob hD0 hKt hCD hC0 hm hn hL hE hLpos htail
  have hmR : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hMpos : (0:ℝ) < (m:ℝ) := by linarith
  have hNpos : (0:ℝ) < (n:ℝ) := by linarith
  have hMN : (1:ℝ) ≤ (m:ℝ)*(n:ℝ) := by nlinarith
  have hMNpos : (0:ℝ) < (m:ℝ)*(n:ℝ) := by linarith
  have hlog : (0:ℝ) ≤ Real.log ((m:ℝ)*(n:ℝ)) := Real.log_nonneg hMN
  have hkey : Kt * (D0+12) * Real.log ((m:ℝ)*(n:ℝ)) ≤ CD * Real.log ((m:ℝ)*(n:ℝ)) + C0 := by
    have h1 : (Kt * (D0+12)) * Real.log ((m:ℝ)*(n:ℝ)) ≤ CD * Real.log ((m:ℝ)*(n:ℝ)) :=
      mul_le_mul_of_nonneg_right hCD hlog
    nlinarith
  have hLbound : (D0+12) * Real.log ((m:ℝ)*(n:ℝ)) ≤ L / Kt := by
    rw [hL, le_div_iff₀ hKt]
    nlinarith [hkey]
  have hLmult : ((D0+12) * Real.log ((m:ℝ)*(n:ℝ))) * Kt ≤ L :=
    (le_div_iff₀ hKt).mp hLbound
  have hEle : E ≤ ((m:ℝ)*(n:ℝ)) ^ (-(D0+12)) := by
    rw [hE, Real.rpow_def_of_pos hMNpos]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hKt]
    have h2 : Real.log ((m:ℝ)*(n:ℝ)) * (-(D0+12)) * Kt
        = -(((D0+12) * Real.log ((m:ℝ)*(n:ℝ))) * Kt) := by ring
    rw [h2]
    linarith [hLmult]
  have hrpow12 : ((m:ℝ)*(n:ℝ)) ^ (-(D0+11))
      = ((m:ℝ)*(n:ℝ)) * ((m:ℝ)*(n:ℝ)) ^ (-(D0+12)) := by
    have h := Real.rpow_add hMNpos (1:ℝ) (-(D0+12))
    rw [Real.rpow_one] at h
    have h2 : -(D0+11) = (1:ℝ) + -(D0+12) := by ring
    rw [h2]
    exact h
  have hstep1 : 2*(m:ℝ)*(n:ℝ)*E ≤ 2 * ((m:ℝ)*(n:ℝ)) ^ (-(D0+11)) := by
    have h2 : 2*(m:ℝ)*(n:ℝ)*E
        ≤ 2*(m:ℝ)*(n:ℝ) * ((m:ℝ)*(n:ℝ)) ^ (-(D0+12)) :=
      mul_le_mul_of_nonneg_left hEle (by positivity)
    calc 2*(m:ℝ)*(n:ℝ)*E
        ≤ 2*(m:ℝ)*(n:ℝ) * ((m:ℝ)*(n:ℝ)) ^ (-(D0+12)) := h2
      _ = 2 * ((m:ℝ)*(n:ℝ)) ^ (-(D0+11)) := by rw [hrpow12]; ring
  have hMle : (m:ℝ) ^ (-(D0+11)) ≤ (3:ℝ) ^ (-(D0+11)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hmR (by linarith)
  have hbase : (3:ℝ) ^ (-(D0+11)) ≤ (3:ℝ) ^ (-(1:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h13 : (3:ℝ) ^ (-(1:ℝ)) = 1/3 := by
    have hneg : (3:ℝ) ^ (-(1:ℝ)) = ((3:ℝ) ^ (1:ℝ))⁻¹ := Real.rpow_neg (by norm_num) 1
    have hone : (3:ℝ) ^ (1:ℝ) = (3:ℝ) := Real.rpow_one 3
    rw [hone] at hneg
    rw [hneg]
    norm_num
  have h2M : 2 * (m:ℝ) ^ (-(D0+11)) ≤ (n:ℝ) := by
    have h1 : (m:ℝ) ^ (-(D0+11)) ≤ 1/3 := le_trans hMle (le_trans hbase (le_of_eq h13))
    exact le_trans (mul_le_mul_of_nonneg_left h1 (by norm_num)) (le_trans (by norm_num) hnR)
  have hstep2 : 2 * ((m:ℝ)*(n:ℝ)) ^ (-(D0+11)) ≤ (n:ℝ) ^ (-(D0+10)) := by
    have hrp : ((m:ℝ)*(n:ℝ)) ^ (-(D0+11))
        = (m:ℝ) ^ (-(D0+11)) * (n:ℝ) ^ (-(D0+11)) :=
      Real.mul_rpow hMpos.le hNpos.le
    have hNk : (0:ℝ) ≤ (n:ℝ) ^ (-(D0+11)) := Real.rpow_nonneg hNpos.le _
    have h1 : 2 * ((m:ℝ)*(n:ℝ)) ^ (-(D0+11))
        ≤ (n:ℝ) * (n:ℝ) ^ (-(D0+11)) := by
      rw [hrp]
      calc 2 * ((m:ℝ) ^ (-(D0+11)) * (n:ℝ) ^ (-(D0+11)))
          = (2 * (m:ℝ) ^ (-(D0+11))) * (n:ℝ) ^ (-(D0+11)) := by ring
        _ ≤ (n:ℝ) * (n:ℝ) ^ (-(D0+11)) := mul_le_mul_of_nonneg_right h2M hNk
    have hgoal : (n:ℝ) ^ (-(D0+10)) = (n:ℝ) * (n:ℝ) ^ (-(D0+11)) := by
      have h := Real.rpow_add hNpos (1:ℝ) (-(D0+11))
      rw [Real.rpow_one] at h
      have h2 : -(D0+10) = (1:ℝ) + -(D0+11) := by ring
      rw [h2]
      exact h
    linarith [h1, hgoal]
  have hfinal : 2*(m:ℝ)*(n:ℝ)*E ≤ Real.rpow (n:ℝ) (-(D0+10)) := le_trans hstep1 hstep2
  have hsummand : ∀ (i : Fin m) (j : Fin n),
      ν {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|} ≤ ENNReal.ofReal (2*E) := by
    intro i j
    have h := htail i j L hLpos
    rwa [← hE] at h
  have hset : {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n), L < |x i j|}
      = ⋃ (i : Fin m) (j : Fin n), {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  have hunion : ν {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n), L < |x i j|}
      ≤ ∑ i : Fin m, ∑ j : Fin n, ENNReal.ofReal (2*E) := by
    rw [hset]
    calc ν (⋃ (i : Fin m) (j : Fin n), {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|})
        ≤ ∑' i : Fin m, ν (⋃ j : Fin n, {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}) :=
          measure_iUnion_le _
      _ = ∑ i : Fin m, ν (⋃ j : Fin n, {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|}) :=
          tsum_fintype _
      _ ≤ ∑ i : Fin m, ∑ j : Fin n, ν {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|} := by
          apply Finset.sum_le_sum
          intro i _
          calc ν (⋃ j : Fin n, {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|})
              ≤ ∑' j : Fin n, ν {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|} := measure_iUnion_le _
            _ = ∑ j : Fin n, ν {x : Matrix (Fin m) (Fin n) ℝ | L < |x i j|} := tsum_fintype _
      _ ≤ ∑ i : Fin m, ∑ j : Fin n, ENNReal.ofReal (2*E) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact hsummand i j
  have hsum_eq : ∀ (r : ℕ) (c : ENNReal), (∑ _ : Fin r, c) = (r : ENNReal) * c := by
    intro r c
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcast : ∀ (r : ℕ) (a : ℝ), (r : ENNReal) * ENNReal.ofReal a = ENNReal.ofReal ((r:ℝ) * a) := by
    intro r a
    rw [← ENNReal.ofReal_natCast r, ← ENNReal.ofReal_mul (by positivity)]
  have hsum_val : ∑ i : Fin m, ∑ j : Fin n, ENNReal.ofReal (2*E)
      = ENNReal.ofReal ((m:ℝ)*(n:ℝ)*(2*E)) := by
    rw [hsum_eq m]
    rw [hsum_eq n]
    rw [hcast n (2*E)]
    rw [hcast m ((n:ℝ)*(2*E))]
    congr 1
    ring
  have hofReal : ENNReal.ofReal ((m:ℝ)*(n:ℝ)*(2*E))
      ≤ ENNReal.ofReal (Real.rpow (n:ℝ) (-(D0+10))) := by
    apply ENNReal.ofReal_le_ofReal
    linarith [hfinal]
  calc ν {x : Matrix (Fin m) (Fin n) ℝ | ∃ (i : Fin m) (j : Fin n), L < |x i j|}
      ≤ ∑ i : Fin m, ∑ j : Fin n, ENNReal.ofReal (2*E) := hunion
    _ = ENNReal.ofReal ((m:ℝ)*(n:ℝ)*(2*E)) := hsum_val
    _ ≤ ENNReal.ofReal (Real.rpow (n:ℝ) (-(D0+10))) := hofReal
  /- @proof-region region.target-node.session.5a02943772a70618 end -/

end Statlib.Imported

