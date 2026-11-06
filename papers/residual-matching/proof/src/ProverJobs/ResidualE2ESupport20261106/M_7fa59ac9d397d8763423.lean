import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_ad2660411b093d071ccc
import ProverJobs.ResidualE2ESupport20261106.M_75066f0e36ad2aaa1e21

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2587526204_66177347 : ∀ (m n : ℕ) (p sigma : ℝ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hsigma : 0 < sigma)
    (Om M0 Hm : Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ (i : Fin m) (j : Fin n), Om i j = 0 ∨ Om i j = 1)
    (lamHat : Fin n → ℝ) (w : Fin n → ℝ)
    (hw_nn : ∀ i : Fin n, 0 ≤ w i) (hw_sum : (∑ i : Fin n, w i) = 1)
    (C1 C3 C4 : ℝ) (hC1 : 0 < C1) (hC3 : 0 < C3) (hC4 : 0 < C4)
    (h1 : ∀ i : Fin n,
      |sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m : ℝ)) - lamHat i|
        ≤ C1 * Real.sqrt p * deltaM m)
    (h3 : ∀ i : Fin n,
      0 ≤ sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m : ℝ)) ∧
      sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m : ℝ)) ≤ C3 * Real.sqrt p)
    (h4 : |sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M0 / sigma - 1|
        ≤ C4 * deltaM m)
    (h4half : C4 * deltaM m ≤ 1 / 2),
    sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M0 ≠ 0 ∧
      loss hnm (indexSet n) p w lamHat (Yobs Om M0 Hm) Om M0
        ≤ ENNReal.ofReal ((2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * deltaM m ^ 2) := by
  /- @proof-region region.target-node.session.46f6cad63fb290fa begin -/
  intro m n p sigma _ hnm hp0 _ hsigma Om M0 Hm _ lamHat w hw_nn hw_sum C1 C3 C4 _ _ _ h1 h3 h4_scale h4_half
  set s := sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M0 with hs
  have hsle : |s / sigma - 1| ≤ C4 * deltaM m := by simpa only [hs] using h4_scale
  have hr : (1 : ℝ) / 2 ≤ s / sigma := by
    have h := (abs_le.mp hsle).1
    linarith
  have hspos : 0 < s := by
    have hmul : sigma * (s / sigma) = s := by field_simp
    have hpos : (0 : ℝ) < sigma * (s / sigma) := mul_pos hsigma (by linarith)
    linarith
  refine ⟨ne_of_gt hspos, ?_⟩
  set d := deltaM m with hd
  have h1' : ∀ i : Fin n,
      |sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m : ℝ)) - lamHat i| ≤ C1 * Real.sqrt p * d :=
    fun i => by simpa only [← hd] using h1 i
  have h3' : ∀ i : Fin n,
      0 ≤ sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m : ℝ)) ∧
        sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m : ℝ)) ≤ C3 * Real.sqrt p :=
    fun i => by simpa only [← hd] using h3 i
  have h4half : C4 * d ≤ 1 / 2 := by simpa only [← hd] using h4_half
  have hY : Yobs Om M0 Hm - maskOp Om M0 = maskOp Om Hm := by
    ext i j
    simp only [Yobs, maskOp, Matrix.sub_apply, Matrix.add_apply]
    ring
  have hscal : ∀ (M : Matrix (Fin m) (Fin n) ℝ) (c : ℝ), 0 ≤ c → ∀ i : Fin n,
      sv hnm (c • M) i = c * sv hnm M i := by
    intro M c hc i
    have hsc_l := statopia_math_node_3786437948_943d4007 m n M c
      (Fin.castLE (le_min hnm le_rfl) i)
    exact hsc_l.2.2.2.2.2.1 hnm i hc
  have hc_nn : (0 : ℝ) ≤ (Real.sqrt (m : ℝ) * s)⁻¹ := by
    by_cases hm : Real.sqrt (m : ℝ) = 0
    · rw [hm, zero_mul, inv_zero]
    · have hpos : 0 < Real.sqrt (m : ℝ) := lt_of_le_of_ne (Real.sqrt_nonneg (m : ℝ)) (Ne.symm hm)
      exact le_of_lt (inv_pos.mpr (mul_pos hpos hspos))
  have hkey : ∀ t : ℝ,
      (Real.sqrt (m : ℝ) * s)⁻¹ * t = (sigma / s) * (t / (sigma * Real.sqrt (m : ℝ))) := by
    intro t
    by_cases hm : Real.sqrt (m : ℝ) = 0
    · rw [hm]
      simp
    · field_simp
  have hα : |sigma / s - 1| ≤ 2 * C4 * d := by
    have hsle' : |s / sigma - 1| ≤ C4 * d := by simpa only [← hd] using hsle
    have hCd_nn : 0 ≤ C4 * d := le_trans (abs_nonneg (s / sigma - 1)) hsle'
    have hfac : sigma / s - 1 = (sigma - s) / s := by field_simp
    have hsdiff : |sigma - s| ≤ C4 * d * sigma := by
      have hfac2 : s - sigma = (s / sigma - 1) * sigma := by field_simp
      calc |sigma - s| = |s - sigma| := abs_sub_comm _ _
        _ = |(s / sigma - 1) * sigma| := by rw [hfac2]
        _ = |s / sigma - 1| * sigma := by rw [abs_mul, abs_of_pos hsigma]
        _ ≤ C4 * d * sigma := mul_le_mul_of_nonneg_right hsle' (le_of_lt hsigma)
    have hsge : sigma / 2 ≤ s := by
      have hmul : sigma * (s / sigma) = s := by field_simp
      rw [← hmul]
      calc sigma / 2 = sigma * (1 / 2) := by ring
        _ ≤ sigma * (s / sigma) := mul_le_mul_of_nonneg_left hr (le_of_lt hsigma)
    have hgoal2 : |sigma - s| ≤ s * (2 * C4 * d) := by
      have hstep : C4 * d * sigma ≤ C4 * d * (2 * s) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hCd_nn
      nlinarith [hsdiff, hstep]
    rw [hfac, abs_div, abs_of_pos hspos, div_eq_mul_inv]
    calc |sigma - s| * s⁻¹ ≤ (s * (2 * C4 * d)) * s⁻¹ :=
          mul_le_mul_of_nonneg_right hgoal2 (le_of_lt (inv_pos.mpr hspos))
      _ = 2 * C4 * d := by field_simp
  have hbound : ∀ i : Fin n,
      ((Real.sqrt (m : ℝ) * s)⁻¹ * sv hnm (maskOp Om Hm) i - lamHat i) ^ 2
        ≤ (2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * p * d ^ 2 := by
    intro i
    set th := sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m : ℝ)) with hth
    set Z := C1 * Real.sqrt p * d + 2 * C4 * d * (C3 * Real.sqrt p) with hZ
    have ha : |th - lamHat i| ≤ C1 * Real.sqrt p * d := by simpa only [hth] using h1' i
    have hθnn : 0 ≤ th := by simpa only [hth] using (h3' i).1
    have hθle : th ≤ C3 * Real.sqrt p := by simpa only [hth] using (h3' i).2
    have hkeyi : (Real.sqrt (m : ℝ) * s)⁻¹ * sv hnm (maskOp Om Hm) i = (sigma / s) * th := by
      rw [hth]
      exact hkey _
    have he : (Real.sqrt (m : ℝ) * s)⁻¹ * sv hnm (maskOp Om Hm) i - lamHat i
        = (th - lamHat i) + (sigma / s - 1) * th := by
      rw [hkeyi]
      ring
    have hb : |(sigma / s - 1) * th| ≤ 2 * C4 * d * (C3 * Real.sqrt p) := by
      rw [abs_mul, abs_of_nonneg hθnn]
      exact mul_le_mul hα hθle hθnn (le_trans (abs_nonneg _) hα)
    have hsum : |(th - lamHat i) + (sigma / s - 1) * th| ≤ Z := by
      rw [hZ]
      calc |(th - lamHat i) + (sigma / s - 1) * th|
          ≤ |th - lamHat i| + |(sigma / s - 1) * th| := abs_add_le _ _
        _ ≤ C1 * Real.sqrt p * d + 2 * C4 * d * (C3 * Real.sqrt p) := add_le_add ha hb
    have hsq : ((th - lamHat i) + (sigma / s - 1) * th) ^ 2 ≤ Z ^ 2 := by
      have hle1 := (abs_le.mp hsum).1
      have hle2 := (abs_le.mp hsum).2
      have hfac3 : 0 ≤ (Z - ((th - lamHat i) + (sigma / s - 1) * th)) *
          (Z + ((th - lamHat i) + (sigma / s - 1) * th)) :=
        mul_nonneg (by linarith only [hle1, hle2]) (by linarith only [hle1, hle2])
      nlinarith only [hfac3]
    have h2sq : Z ^ 2 ≤ 2 * (C1 * Real.sqrt p * d) ^ 2 + 2 * (2 * C4 * d * (C3 * Real.sqrt p)) ^ 2 := by
      rw [hZ]
      nlinarith only [sq_nonneg (C1 * Real.sqrt p * d - 2 * C4 * d * (C3 * Real.sqrt p))]
    have h3sq : 2 * (C1 * Real.sqrt p * d) ^ 2 + 2 * (2 * C4 * d * (C3 * Real.sqrt p)) ^ 2
        = (2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * p * d ^ 2 := by
      have hpsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (le_of_lt hp0)
      have e1 : 2 * (C1 * Real.sqrt p * d) ^ 2 = 2 * C1 ^ 2 * p * d ^ 2 := by
        have h : (C1 * Real.sqrt p * d) ^ 2 = C1 ^ 2 * (Real.sqrt p * Real.sqrt p) * d ^ 2 := by
          ring
        rw [h, hpsq]
        ring
      have e2 : 2 * (2 * C4 * d * (C3 * Real.sqrt p)) ^ 2 = 8 * C4 ^ 2 * d ^ 2 * C3 ^ 2 * p := by
        have h : (2 * C4 * d * (C3 * Real.sqrt p)) ^ 2
            = 4 * C4 ^ 2 * d ^ 2 * C3 ^ 2 * (Real.sqrt p * Real.sqrt p) := by ring
        rw [h, hpsq]
        ring
      rw [e1, e2]
      ring
    calc ((Real.sqrt (m : ℝ) * s)⁻¹ * sv hnm (maskOp Om Hm) i - lamHat i) ^ 2
        = ((th - lamHat i) + (sigma / s - 1) * th) ^ 2 := by rw [he]
      _ ≤ Z ^ 2 := hsq
      _ ≤ 2 * (C1 * Real.sqrt p * d) ^ 2 + 2 * (2 * C4 * d * (C3 * Real.sqrt p)) ^ 2 := h2sq
      _ = (2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * p * d ^ 2 := h3sq
  have hcrit : criterion hnm w lamHat ((Real.sqrt (m : ℝ) * s)⁻¹ • (Yobs Om M0 Hm - maskOp Om M0))
      ≤ (2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * p * d ^ 2 := by
    have hN : (Real.sqrt (m : ℝ) * s)⁻¹ • (Yobs Om M0 Hm - maskOp Om M0)
        = (Real.sqrt (m : ℝ) * s)⁻¹ • maskOp Om Hm := by rw [hY]
    rw [hN]
    simp only [criterion]
    calc ∑ i : Fin n, w i * (sv hnm ((Real.sqrt (m : ℝ) * s)⁻¹ • maskOp Om Hm) i - lamHat i) ^ 2
        = ∑ i : Fin n, w i * ((Real.sqrt (m : ℝ) * s)⁻¹ * sv hnm (maskOp Om Hm) i - lamHat i) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hscal (maskOp Om Hm) ((Real.sqrt (m : ℝ) * s)⁻¹) hc_nn i]
      _ ≤ ∑ i : Fin n, w i * ((2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * p * d ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact mul_le_mul_of_nonneg_left (hbound i) (hw_nn i)
      _ = (2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * p * d ^ 2 := by
          rw [← Finset.sum_mul, hw_sum, one_mul]
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hmain : p⁻¹ * criterion hnm w lamHat ((Real.sqrt (m : ℝ) * s)⁻¹ • (Yobs Om M0 Hm - maskOp Om M0))
      ≤ (2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * d ^ 2 := by
    have hpiv : (0 : ℝ) ≤ p⁻¹ := le_of_lt (inv_pos.mpr hp0)
    have hinv : p⁻¹ * p = 1 := inv_mul_cancel₀ hpne
    have heq : p⁻¹ * ((2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * p * d ^ 2)
        = (2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * d ^ 2 := by
      calc p⁻¹ * ((2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * p * d ^ 2)
          = (p⁻¹ * p) * ((2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * d ^ 2) := by ring
        _ = (2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * d ^ 2 := by rw [hinv, one_mul]
    calc p⁻¹ * criterion hnm w lamHat ((Real.sqrt (m : ℝ) * s)⁻¹ • (Yobs Om M0 Hm - maskOp Om M0))
        ≤ p⁻¹ * ((2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * p * d ^ 2) :=
          mul_le_mul_of_nonneg_left hcrit hpiv
      _ = (2 * C1 ^ 2 + 8 * C4 ^ 2 * C3 ^ 2) * d ^ 2 := heq
  have hloss : loss hnm (indexSet n) p w lamHat (Yobs Om M0 Hm) Om M0
      = ENNReal.ofReal (p⁻¹ * criterion hnm w lamHat
          ((Real.sqrt (m : ℝ) * s)⁻¹ • (Yobs Om M0 Hm - maskOp Om M0))) := by
    simp only [loss]
    rw [if_neg (by rw [← hs]; exact ne_of_gt hspos), hs]
  rw [hloss]
  exact ENNReal.ofReal_le_ofReal hmain
  /- @proof-region region.target-node.session.46f6cad63fb290fa end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_2587526204_66177347


