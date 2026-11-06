import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_cc349246c35e6c14af3f

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
theorem statopia_math_node_1590920294_08da72e6 : ∀ (Kt D0 alpha0 CD : ℝ) (hKt : 0 < Kt) (hD0 : 0 < D0) (halpha0 : 0 < alpha0)
    (hCD : Kt * (D0 + 12) ≤ CD)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (L : ℝ)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
      (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
    (ν : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure ν]
    (h_var : ∀ (i : Fin m) (j : Fin n), ∫ x, (x i j) ^ 2 ∂ν = 1)
    (h_mean : ∀ (i : Fin m) (j : Fin n), ∫ x, x i j ∂ν = 0)
    (h_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
      ν {x : Matrix (Fin m) (Fin n) ℝ | t < |x i j|} ≤
        ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (b c : Fin m → Fin n → ℝ)
    (XT : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ)
    (hb : ∀ (i : Fin m) (j : Fin n),
      b i j = ∫ x, x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) ∂ν)
    (hc : ∀ (i : Fin m) (j : Fin n),
      c i j = Real.sqrt
        (∫ x, (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b i j) ^ 2 ∂ν))
    (hXT : ∀ (x : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n),
      XT x i j = (x i j * (if |x i j| ≤ L then (1 : ℝ) else 0) - b i j) / c i j),
    ∀ (x : Matrix (Fin m) (Fin n) ℝ), (∀ (i : Fin m) (j : Fin n), |x i j| ≤ L) →
      ∀ (i : Fin m) (j : Fin n),
        |x i j - XT x i j| ≤
          64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
  /- @proof-region region.target-node.session.299060de44b3044c begin -/
  intro Kt D0 alpha0 CD hKt hD0 halpha0 hCD m n hm hn L hL ν hν h_var h_mean h_tail b c XT hb hc hXT z hz i j
  have hCDpos : 0 < CD := by
    have h1 : 0 < Kt * (D0 + 12) := mul_pos hKt (by linarith [hD0])
    linarith [hCD, h1]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by linarith
  have hmn : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by
    calc (1 : ℝ) ≤ (m : ℝ) := hm1
      _ = (m : ℝ) * 1 := (mul_one _).symm
      _ ≤ (m : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hn1 hm0
  have hlog : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := Real.log_nonneg hmn
  have hKt1 : 0 < Kt + 1 := by linarith
  have hD01 : 0 < D0 + 1 := by linarith
  have hal1 : 0 < alpha0 + 1 := by linarith
  have hTpos : (0 : ℝ) < (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 :=
    mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hKt1 4)) (pow_pos hD01 4)) (pow_pos hal1 4)
  have hLpos : 0 < L := by
    rw [hL]
    have h1 : 0 ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := mul_nonneg hCDpos.le hlog
    linarith [hTpos, h1]
  have key : ∀ t : ℝ, (0 : ℝ) < t → (1 : ℝ) ≤ (t + 1) ^ 4 := by
    intro t ht
    have h1 : (0 : ℝ) ≤ t * (t + 2) := mul_nonneg (le_of_lt ht) (by linarith)
    have h2 : (0 : ℝ) ≤ (t + 1) ^ 2 + 1 := by positivity
    have hprod : (0 : ℝ) ≤ (t * (t + 2)) * ((t + 1) ^ 2 + 1) := mul_nonneg h1 h2
    have he : (t + 1) ^ 4 = (t * (t + 2)) * ((t + 1) ^ 2 + 1) + 1 := by ring
    rw [he]
    linarith [hprod]
  have hT1 : (1 : ℝ) ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
    have h10 : (1 : ℝ) ≤ (10 : ℝ) ^ 6 := by norm_num
    have h10p : (0 : ℝ) ≤ (10 : ℝ) ^ 6 := by norm_num
    have hKp : (1 : ℝ) ≤ (Kt + 1) ^ 4 := key Kt hKt
    have hDp : (1 : ℝ) ≤ (D0 + 1) ^ 4 := key D0 hD0
    have hap : (1 : ℝ) ≤ (alpha0 + 1) ^ 4 := key alpha0 halpha0
    have hKp0 : (0 : ℝ) ≤ (Kt + 1) ^ 4 := (pow_pos hKt1 4).le
    have hDp0 : (0 : ℝ) ≤ (D0 + 1) ^ 4 := (pow_pos hD01 4).le
    have h1 : (1 : ℝ) ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 := by
      have := mul_le_mul h10 hKp (by norm_num : (0 : ℝ) ≤ 1) h10p
      simpa using this
    have h2 : (1 : ℝ) ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 := by
      have := mul_le_mul h1 hDp (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg h10p hKp0)
      simpa using this
    have h3 : (1 : ℝ) ≤ (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
      have := mul_le_mul h2 hap (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg (mul_nonneg h10p hKp0) hDp0)
      simpa using this
    exact h3
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    have h1 : 0 ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := mul_nonneg hCDpos.le hlog
    linarith [hT1, h1]
  haveI : IsProbabilityMeasure ν := hν
  obtain ⟨hb_bound, hc_ge, hc_le, hc_sq⟩ :=
    statopia_math_node_3352644490_9c3ad106 Kt D0 alpha0 CD hKt hD0 halpha0 hCD m n hm hn L hL ν h_var h_mean h_tail b c hb hc i j
  have hcpos : 0 < c i j := lt_of_lt_of_le (by norm_num) hc_ge
  have hcne : c i j ≠ 0 := hcpos.ne'
  have hexp_pos : 0 < Real.exp (-L / Kt) := Real.exp_pos _
  have hc1 : |c i j - 1| ≤ 2 * (1 - (c i j) ^ 2) := by
    have hne : (1 : ℝ) + c i j ≠ 0 := by linarith [hc_ge]
    have hnum2 : (0 : ℝ) ≤ 1 - (c i j) ^ 2 := by
      have h1 : (0 : ℝ) ≤ 1 - c i j := by linarith [hc_le]
      have h2 : (0 : ℝ) ≤ 1 + c i j := by linarith [hc_ge]
      have he : 1 - (c i j) ^ 2 = (1 - c i j) * (1 + c i j) := by ring
      rw [he]
      exact mul_nonneg h1 h2
    have hstep_a : |c i j - 1| = 1 - c i j := by
      rw [abs_sub_comm, abs_of_nonneg (show (0 : ℝ) ≤ 1 - c i j by linarith [hc_le])]
    have hfac : (1 - (c i j) ^ 2) / (1 + c i j) = 1 - c i j := by
      rw [div_eq_iff hne]; ring
    rw [hstep_a, ← hfac]
    have hden : (3 / 2 : ℝ) ≤ 1 + c i j := by linarith [hc_ge]
    have hcle : (1 - (c i j) ^ 2) / (1 + c i j) ≤ (1 - (c i j) ^ 2) / (3 / 2) :=
      div_le_div_of_nonneg_left hnum2 (by norm_num) hden
    have h2 : (1 - (c i j) ^ 2) / (3 / 2) ≤ 2 * (1 - (c i j) ^ 2) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 2)]
      linarith [hnum2]
    linarith [hcle, h2]
  have hif : z i j * (if |z i j| ≤ L then (1 : ℝ) else 0) = z i j := by
    rw [if_pos (hz i j), mul_one]
  have hXTij : XT z i j = (z i j - b i j) / c i j := by
    rw [hXT z i j, hif]
  have hcdiff : z i j - XT z i j = (z i j * (c i j - 1) + b i j) / c i j := by
    rw [hXTij, eq_div_iff hcne]
    field_simp
    ring
  have hnum3 : |z i j * (c i j - 1) + b i j| ≤ L * |c i j - 1| + |b i j| := by
    have h1 : |z i j * (c i j - 1)| ≤ L * |c i j - 1| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hz i j) (abs_nonneg _)
    calc |z i j * (c i j - 1) + b i j| ≤ |z i j * (c i j - 1)| + |b i j| := abs_add_le _ _
      _ ≤ L * |c i j - 1| + |b i j| := by linarith [h1]
  have hstep1 : |z i j - XT z i j| ≤ (L * |c i j - 1| + |b i j|) / c i j := by
    rw [hcdiff, abs_div, abs_of_pos hcpos, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum3 (inv_nonneg.mpr hcpos.le)
  have hLa : L * |c i j - 1| ≤ 16 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
    have h1 : L * |c i j - 1| ≤ L * (2 * (1 - (c i j) ^ 2)) :=
      mul_le_mul_of_nonneg_left hc1 hLpos.le
    have h3 : L * (2 * (1 - (c i j) ^ 2)) ≤
        L * (2 * (8 * (L + Kt) ^ 2 * Real.exp (-L / Kt))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc_sq (by norm_num)) hLpos.le
    refine le_trans h1 (le_trans h3 (le_of_eq ?_))
    ring
  have hLin : (L + Kt) ≤ L * (L + Kt) ^ 2 := by
    have hLKs : (0 : ℝ) ≤ L + Kt := by linarith [hLpos]
    have h1 : (1 : ℝ) ≤ L * (L + Kt) := by
      have := mul_le_mul hL1 (by linarith [hLpos] : (1 : ℝ) ≤ L + Kt) (by norm_num : (0 : ℝ) ≤ 1) (by linarith [hLpos] : (0 : ℝ) ≤ L)
      simpa using this
    have hstep : (1 : ℝ) * (L + Kt) ≤ (L * (L + Kt)) * (L + Kt) :=
      mul_le_mul_of_nonneg_right h1 hLKs
    have heq : (L * (L + Kt)) * (L + Kt) = L * (L + Kt) ^ 2 := by ring
    rw [heq] at hstep
    simpa using hstep
  have hbL : |b i j| ≤ 2 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
    have h2LK : 2 * (L + Kt) ≤ 2 * L * (L + Kt) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hLin (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * (L + Kt) ≤ 2 * (L * (L + Kt) ^ 2) := h
        _ = 2 * L * (L + Kt) ^ 2 := by ring
    calc |b i j| ≤ 2 * (L + Kt) * Real.exp (-L / Kt) := hb_bound
      _ ≤ 2 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) :=
          mul_le_mul_of_nonneg_right h2LK hexp_pos.le

  have hnumC : L * |c i j - 1| + |b i j| ≤ 18 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
    have hsum : L * |c i j - 1| + |b i j| ≤
        16 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) + 2 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) :=
      add_le_add hLa hbL
    refine le_trans hsum (le_of_eq ?_)
    ring
  have h_invc : (1 : ℝ) / c i j ≤ 2 := by
    rw [div_le_iff₀ hcpos]
    linarith [hc_ge]
  have h_invc_nonneg : (0 : ℝ) ≤ 1 / c i j := div_nonneg (by norm_num) hcpos.le
  have hbndpos : (0 : ℝ) ≤ 18 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hLpos.le) (sq_nonneg (L + Kt))) hexp_pos.le
  have hfinal1 : |z i j - XT z i j| ≤ 36 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
    calc |z i j - XT z i j| ≤ (L * |c i j - 1| + |b i j|) / c i j := hstep1
      _ = (L * |c i j - 1| + |b i j|) * (1 / c i j) := by rw [div_eq_mul_one_div]
      _ ≤ (18 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt)) * 2 :=
          mul_le_mul hnumC h_invc h_invc_nonneg hbndpos
      _ = 36 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by ring
  have hgrp : (0 : ℝ) ≤ L * (L + Kt) ^ 2 * Real.exp (-L / Kt) :=
    mul_nonneg (mul_nonneg hLpos.le (sq_nonneg (L + Kt))) hexp_pos.le
  have h36 : (36 : ℝ) ≤ 64 * (Kt + 1) := by linarith [hKt]
  calc |z i j - XT z i j| ≤ 36 * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := hfinal1
    _ = 36 * (L * (L + Kt) ^ 2 * Real.exp (-L / Kt)) := by ring
    _ ≤ (64 * (Kt + 1)) * (L * (L + Kt) ^ 2 * Real.exp (-L / Kt)) :=
        mul_le_mul_of_nonneg_right h36 hgrp
    _ = 64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by ring
  /- @proof-region region.target-node.session.299060de44b3044c end -/

end Statlib.Imported

#print axioms Statlib.Imported.statopia_math_node_1590920294_08da72e6

