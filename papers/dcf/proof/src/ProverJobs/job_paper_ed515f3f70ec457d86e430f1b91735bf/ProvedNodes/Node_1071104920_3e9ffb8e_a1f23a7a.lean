import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_108072969_a1eba6a6_a4e28db2
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3288924075_b4e681f6_dff03e4b
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3323695585_5e8b63c6_53aad4aa

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf


open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1071104920_3e9ffb8e : ∀ (phi0 : ℝ → ℝ)
    (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1),
    ∃ Cbd : ℝ, 0 < Cbd ∧
      ∀ (p : ℕ) (hp : 0 < Real.log (p : ℝ)) (phi : ℝ) (hphi : 1 ≤ phi)
        (y : Fin p → ℝ) (j k : Fin p),
      (let beta : ℝ := phi * Real.log (p : ℝ)
       let kappa : (Fin p → ℝ) → ℝ := fun w =>
         phi0 (phi * (beta⁻¹ * Real.log (∑ j : Fin p, Real.exp (beta * (w j - y j)))))
       (∀ w : Fin p → ℝ,
         |(fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ))) w)
             (Pi.single k (1 : ℝ))| ≤ Cbd * beta ^ 2) ∧
       (Continuous fun w : Fin p → ℝ =>
         (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ kappa z) (Pi.single j (1 : ℝ))) w)
           (Pi.single k (1 : ℝ)))) := by
  /- @proof-region region.target-node.session.d3782a8c0d38ee9e begin -/
  intro phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  obtain ⟨M1, M2, hM1nn, hM2nn, hM1, hM2, hc1, hc2⟩ :=
    statopia_math_node_108072969_a1eba6a6 phi0 hphi0_cont hphi0_left hphi0_right
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨M2 / (Real.log 2) ^ 2 + 2 * M1 / Real.log 2 + 1, by positivity, ?_⟩
  intro p hp phi hphi y j k
  dsimp only
  obtain ⟨hformula, hcont⟩ :=
    statopia_math_node_3323695585_5e8b63c6 phi0 hphi0_cont hc1 hc2 p hp phi hphi y j k
  refine ⟨?_, ?_⟩
  · intro w
    have hphipos : 0 < phi := by linarith
    rw [hformula w]
    set Bt : ℝ := phi * Real.log (p : ℝ) with hBt
    set SS : ℝ := ∑ t : Fin p, Real.exp (Bt * (w t - y t)) with hSS
    set sj : ℝ := Real.exp (Bt * (w j - y j)) / SS with hsj
    set sk : ℝ := Real.exp (Bt * (w k - y k)) / SS with hsk
    have hBtpos : 0 < Bt := by rw [hBt]; exact mul_pos hphipos hp
    have hSSpos : 0 < SS := by
      rw [hSS]
      exact lt_of_lt_of_le (Real.exp_pos _)
        (Finset.single_le_sum (f := fun t : Fin p => Real.exp (Bt * (w t - y t)))
          (fun t _ => (Real.exp_pos _).le) (Finset.mem_univ j))
    have hsj0 : 0 ≤ sj := by rw [hsj]; exact div_nonneg (Real.exp_pos _).le hSSpos.le
    have hsk0 : 0 ≤ sk := by rw [hsk]; exact div_nonneg (Real.exp_pos _).le hSSpos.le
    have hsj1 : sj ≤ 1 := by
      rw [hsj]
      exact (div_le_one hSSpos).mpr (by
        rw [hSS]
        exact Finset.single_le_sum (f := fun t : Fin p => Real.exp (Bt * (w t - y t)))
          (fun t _ => (Real.exp_pos _).le) (Finset.mem_univ j))
    have hsk1 : sk ≤ 1 := by
      rw [hsk]
      exact (div_le_one hSSpos).mpr (by
        rw [hSS]
        exact Finset.single_le_sum (f := fun t : Fin p => Real.exp (Bt * (w t - y t)))
          (fun t _ => (Real.exp_pos _).le) (Finset.mem_univ k))
    have hdiff : |(if j = k then (1 : ℝ) else 0) * sj - sj * sk| ≤ 2 := by
      have hδ0 : 0 ≤ (if j = k then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have hδ1 : (if j = k then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have hx0 : 0 ≤ (if j = k then (1 : ℝ) else 0) * sj := mul_nonneg hδ0 hsj0
      have hx1 : (if j = k then (1 : ℝ) else 0) * sj ≤ 1 := by nlinarith
      have hy0 : 0 ≤ sj * sk := mul_nonneg hsj0 hsk0
      have hy1 : sj * sk ≤ 1 := by nlinarith
      rw [abs_le]
      constructor <;> linarith
    have hYnn : 0 ≤ phi * Bt := mul_nonneg hphipos.le hBtpos.le
    have h1 : |deriv (deriv phi0) (phi * (Bt⁻¹ * Real.log SS)) * (phi ^ 2 * (sj * sk))| ≤
        M2 * phi ^ 2 := by
      rw [abs_mul]
      have hX : |phi ^ 2 * (sj * sk)| ≤ phi ^ 2 := by
        have h0 : 0 ≤ phi ^ 2 * (sj * sk) := mul_nonneg (sq_nonneg phi) (mul_nonneg hsj0 hsk0)
        rw [abs_of_nonneg h0]
        calc phi ^ 2 * (sj * sk) ≤ phi ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg phi)
          _ = phi ^ 2 := by ring
      exact mul_le_mul (hM2 _) hX (abs_nonneg _) hM2nn
    have h2 : |deriv phi0 (phi * (Bt⁻¹ * Real.log SS)) * (phi * Bt) *
        ((if j = k then (1 : ℝ) else 0) * sj - sj * sk)| ≤ 2 * (M1 * (phi * Bt)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hYnn]
      calc (|deriv phi0 (phi * (Bt⁻¹ * Real.log SS))| * (phi * Bt)) *
            |(if j = k then (1 : ℝ) else 0) * sj - sj * sk|
          = (phi * Bt) * (|deriv phi0 (phi * (Bt⁻¹ * Real.log SS))| *
              |(if j = k then (1 : ℝ) else 0) * sj - sj * sk|) := by ring
        _ ≤ (phi * Bt) * (M1 * 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hYnn
            exact mul_le_mul (hM1 _) hdiff (abs_nonneg _) hM1nn
        _ = 2 * (M1 * (phi * Bt)) := by ring
    have hmain : M2 * phi ^ 2 + 2 * (M1 * (phi * Bt)) ≤
        (M2 / (Real.log 2) ^ 2 + 2 * M1 / Real.log 2 + 1) * Bt ^ 2 := by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        have hp1 : 1 < p := by
          by_contra hcon
          push_neg at hcon
          have hp0 : p = 0 ∨ p = 1 := by omega
          rcases hp0 with h0 | h0
          · rw [h0, Nat.cast_zero, Real.log_zero] at hp
            exact absurd hp (lt_irrefl 0)
          · rw [h0, Nat.cast_one, Real.log_one] at hp
            exact absurd hp (lt_irrefl 0)
        exact_mod_cast hp1
      have hlog_le : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hp2
      have hφℓ : phi * Real.log 2 ≤ Bt := by
        rw [hBt]
        exact mul_le_mul_of_nonneg_left hlog_le hphipos.le
      have hφℓnn : 0 ≤ phi * Real.log 2 := mul_nonneg hphipos.le hlog2.le
      have hsq : phi ^ 2 * (Real.log 2) ^ 2 ≤ Bt ^ 2 := by nlinarith [hφℓ, hφℓnn, hBtpos.le]
      have hlin : phi * Bt * Real.log 2 ≤ Bt ^ 2 := by nlinarith [hφℓ, hBtpos.le]
      have hA : M2 * phi ^ 2 * (Real.log 2) ^ 2 ≤ M2 * Bt ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hsq hM2nn
        calc M2 * phi ^ 2 * (Real.log 2) ^ 2 = M2 * (phi ^ 2 * (Real.log 2) ^ 2) := by ring
          _ ≤ M2 * Bt ^ 2 := h
      have hB0 : 0 ≤ 2 * M1 * Real.log 2 :=
        mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * M1) hlog2.le
      have hB : 2 * M1 * (phi * Bt) * (Real.log 2) ^ 2 ≤ 2 * M1 * Real.log 2 * Bt ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hlin hB0
        calc 2 * M1 * (phi * Bt) * (Real.log 2) ^ 2
            = 2 * M1 * Real.log 2 * (phi * Bt * Real.log 2) := by ring
          _ ≤ 2 * M1 * Real.log 2 * Bt ^ 2 := h
      have hkey : (M2 * phi ^ 2 + 2 * (M1 * (phi * Bt))) * (Real.log 2) ^ 2 ≤
          (M2 + 2 * M1 * Real.log 2 + (Real.log 2) ^ 2) * Bt ^ 2 := by
        have hC : 0 ≤ (Real.log 2) ^ 2 * Bt ^ 2 := by positivity
        linarith [hA, hB, hC]
      have hpos2 : (0 : ℝ) < (Real.log 2) ^ 2 := by positivity
      have hℓne : Real.log 2 ≠ 0 := ne_of_gt hlog2
      field_simp
      nlinarith [hkey, hlog2, hM1nn, hM2nn]
    have htri : |deriv (deriv phi0) (phi * (Bt⁻¹ * Real.log SS)) * (phi ^ 2 * (sj * sk)) +
        deriv phi0 (phi * (Bt⁻¹ * Real.log SS)) * (phi * Bt) *
          ((if j = k then (1 : ℝ) else 0) * sj - sj * sk)| ≤
        M2 * phi ^ 2 + 2 * (M1 * (phi * Bt)) := by
      calc |deriv (deriv phi0) (phi * (Bt⁻¹ * Real.log SS)) * (phi ^ 2 * (sj * sk)) +
            deriv phi0 (phi * (Bt⁻¹ * Real.log SS)) * (phi * Bt) *
              ((if j = k then (1 : ℝ) else 0) * sj - sj * sk)|
          ≤ |deriv (deriv phi0) (phi * (Bt⁻¹ * Real.log SS)) * (phi ^ 2 * (sj * sk))| +
            |deriv phi0 (phi * (Bt⁻¹ * Real.log SS)) * (phi * Bt) *
              ((if j = k then (1 : ℝ) else 0) * sj - sj * sk)| := abs_add_le _ _
        _ ≤ M2 * phi ^ 2 + 2 * (M1 * (phi * Bt)) := add_le_add h1 h2
    exact le_trans htri hmain
  · exact hcont
  /- @proof-region region.target-node.session.d3782a8c0d38ee9e end -/

end

end Statlib.Imported

