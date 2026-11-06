import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_b4f2420a5901dea2781f

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
theorem statopia_math_node_3877234010_7a806c4e : ∀ (m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (p sigma : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hsigma : 0 < sigma)
    (Om M0 Hm : Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ (i : Fin m) (j : Fin n), Om i j = 0 ∨ Om i j = 1)
    (lamHat : Fin n → ℝ)
    (C1 c2 : ℝ) (hC1 : 0 < C1) (hc2 : 0 < c2)
    (h1 : ∀ i : Fin n,
      |sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m : ℝ)) - lamHat i|
        ≤ C1 * Real.sqrt p * deltaM m)
    (h2 : c2 * (n : ℝ) * Real.sqrt p ≤ ∑ i ∈ indexSet n, lamHat i),
    (∀ M : Matrix (Fin m) (Fin n) ℝ,
      |sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M / sigma - 1|
        ≤ (C1 / c2) * deltaM m
          + (1 / c2) * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp Om (M - M0))
              / (sigma * Real.sqrt ((m : ℝ) * (n : ℝ) * p))) ∧
    (|sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M0 / sigma - 1|
        ≤ (C1 / c2) * deltaM m) ∧
    ((C1 / c2) * deltaM m ≤ 1 / 2 →
      sigma / 2 ≤ sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M0 ∧ 0 < sigma / 2) := by
  /- @proof-region region.target-node.session.0f59eee89b1e1f3c begin -/
  intro m n hn hnm p sigma hp0 hp1 hsigma Om M0 Hm hOm lamHat C1 c2 hC1 hc2 h1 h2
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnmR : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
  have hmpos : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hnpos hnmR
  have hm1 : (1:ℝ) ≤ (m:ℝ) := le_trans hn1 hnmR
  have hsqrtm_pos : (0:ℝ) < Real.sqrt (m:ℝ) := Real.sqrt_pos.2 hmpos
  have hsqrtp_pos : (0:ℝ) < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hδnn : (0:ℝ) ≤ deltaM m := by
    unfold deltaM
    exact inv_nonneg.2 (Real.log_nonneg hm1)
  have hSpos : (0:ℝ) < ∑ i ∈ indexSet n, lamHat i :=
    lt_of_lt_of_le (mul_pos (mul_pos hc2 hnpos) hsqrtp_pos) h2
  have hmain : ∀ M : Matrix (Fin m) (Fin n) ℝ,
      |sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M / sigma - 1|
        ≤ (C1 / c2) * deltaM m
          + (1 / c2) * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp Om (M - M0))
              / (sigma * Real.sqrt ((m : ℝ) * (n : ℝ) * p)) := by
    intro M
    have hFrnn : ∀ A : Matrix (Fin m) (Fin n) ℝ,
        (0:ℝ) ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm A := by
      intro A
      unfold Statlib.HighDim.MatrixAnalysis.frobeniusNorm
      positivity
    have hcardn : ((indexSet n).card : ℝ) ≤ (n:ℝ) := by
      have h : (indexSet n).card ≤ n := by
        simpa using Finset.card_le_univ (indexSet n)
      exact_mod_cast h
    have hY : Yobs Om M0 Hm - maskOp Om M = maskOp Om Hm - maskOp Om (M - M0) := by
      ext i j
      simp only [Yobs, maskOp, Matrix.sub_apply, Matrix.add_apply]
      ring
    have hdiff : maskOp Om Hm - (Yobs Om M0 Hm - maskOp Om M) = maskOp Om (M - M0) := by
      rw [hY]
      abel
    have hdep := statopia_math_node_2382536492_f7c626d4 m n hnm (maskOp Om Hm)
      (Yobs Om M0 Hm - maskOp Om M)
    have hdep3 : ∑ i ∈ indexSet n, |sv hnm (maskOp Om Hm) i - sv hnm (Yobs Om M0 Hm - maskOp Om M) i|
        ≤ Real.sqrt ((indexSet n).card : ℝ)
            * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp Om (M - M0)) := by
      have h := (hdep.2 (indexSet n)).2
      rwa [hdiff] at h
    have hFnn : (0:ℝ) ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp Om (M - M0)) :=
      hFrnn _
    have hdep3' : ∑ i ∈ indexSet n, |sv hnm (maskOp Om Hm) i - sv hnm (Yobs Om M0 Hm - maskOp Om M) i|
        ≤ Real.sqrt (n:ℝ) * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp Om (M - M0)) := by
      refine le_trans hdep3 ?_
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcardn) hFnn
    have hCnn : (0:ℝ) ≤ C1 * Real.sqrt p * deltaM m * (sigma * Real.sqrt (m:ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC1) (le_of_lt hsqrtp_pos)) hδnn)
        (le_of_lt (mul_pos hsigma hsqrtm_pos))
    have hterm : ∀ i ∈ indexSet n,
        |sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i|
          ≤ C1 * Real.sqrt p * deltaM m * (sigma * Real.sqrt (m:ℝ)) := by
      intro i _
      have hpos : (0:ℝ) < sigma * Real.sqrt (m:ℝ) := mul_pos hsigma hsqrtm_pos
      have heq : sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i
          = (sigma * Real.sqrt (m:ℝ))
              * (sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m:ℝ)) - lamHat i) := by
        field_simp
      rw [heq, abs_mul, abs_of_pos hpos]
      calc (sigma * Real.sqrt (m:ℝ))
            * |sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m:ℝ)) - lamHat i|
          ≤ (sigma * Real.sqrt (m:ℝ)) * (C1 * Real.sqrt p * deltaM m) :=
            mul_le_mul_of_nonneg_left (h1 i) (le_of_lt hpos)
        _ = C1 * Real.sqrt p * deltaM m * (sigma * Real.sqrt (m:ℝ)) := by ring
    have hsum3 : ∑ i ∈ indexSet n, |sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i|
        ≤ (n:ℝ) * (C1 * Real.sqrt p * deltaM m * (sigma * Real.sqrt (m:ℝ))) := by
      calc ∑ i ∈ indexSet n, |sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i|
          ≤ ∑ i ∈ indexSet n, (C1 * Real.sqrt p * deltaM m * (sigma * Real.sqrt (m:ℝ))) :=
            Finset.sum_le_sum hterm
        _ = ((indexSet n).card : ℝ)
              * (C1 * Real.sqrt p * deltaM m * (sigma * Real.sqrt (m:ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n:ℝ) * (C1 * Real.sqrt p * deltaM m * (sigma * Real.sqrt (m:ℝ))) :=
            mul_le_mul_of_nonneg_right hcardn hCnn
    have hsplit1 : (∑ i ∈ indexSet n, sv hnm (Yobs Om M0 Hm - maskOp Om M) i)
          - ∑ i ∈ indexSet n, sv hnm (maskOp Om Hm) i
        = ∑ i ∈ indexSet n,
            (sv hnm (Yobs Om M0 Hm - maskOp Om M) i - sv hnm (maskOp Om Hm) i) := by
      rw [Finset.sum_sub_distrib]
    have hsplit2 : sigma * Real.sqrt (m:ℝ) * (∑ i ∈ indexSet n, lamHat i)
        = ∑ i ∈ indexSet n, sigma * Real.sqrt (m:ℝ) * lamHat i := by
      rw [Finset.mul_sum]
    have hsplit3 : (∑ i ∈ indexSet n, sv hnm (maskOp Om Hm) i)
          - sigma * Real.sqrt (m:ℝ) * (∑ i ∈ indexSet n, lamHat i)
        = ∑ i ∈ indexSet n,
            (sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i) := by
      rw [hsplit2, Finset.sum_sub_distrib]
    have hsplit : (∑ i ∈ indexSet n, sv hnm (Yobs Om M0 Hm - maskOp Om M) i)
          - sigma * Real.sqrt (m:ℝ) * (∑ i ∈ indexSet n, lamHat i)
        = (∑ i ∈ indexSet n,
              (sv hnm (Yobs Om M0 Hm - maskOp Om M) i - sv hnm (maskOp Om Hm) i))
          + (∑ i ∈ indexSet n,
              (sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i)) := by
      rw [← hsplit1, ← hsplit3]
      ring
    have htri : |(∑ i ∈ indexSet n, sv hnm (Yobs Om M0 Hm - maskOp Om M) i)
          - sigma * Real.sqrt (m:ℝ) * (∑ i ∈ indexSet n, lamHat i)|
        ≤ ∑ i ∈ indexSet n, |sv hnm (maskOp Om Hm) i - sv hnm (Yobs Om M0 Hm - maskOp Om M) i|
          + ∑ i ∈ indexSet n, |sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i| := by
      rw [hsplit]
      have h1' : |∑ i ∈ indexSet n,
            (sv hnm (Yobs Om M0 Hm - maskOp Om M) i - sv hnm (maskOp Om Hm) i)|
          ≤ ∑ i ∈ indexSet n,
              |sv hnm (maskOp Om Hm) i - sv hnm (Yobs Om M0 Hm - maskOp Om M) i| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_sub_comm]
      have h2' : |∑ i ∈ indexSet n,
            (sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i)|
          ≤ ∑ i ∈ indexSet n,
              |sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i| :=
        Finset.abs_sum_le_sum_abs _ _
      have hstep : |(∑ i ∈ indexSet n,
              (sv hnm (Yobs Om M0 Hm - maskOp Om M) i - sv hnm (maskOp Om Hm) i))
            + (∑ i ∈ indexSet n,
              (sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i))|
          ≤ |∑ i ∈ indexSet n,
              (sv hnm (Yobs Om M0 Hm - maskOp Om M) i - sv hnm (maskOp Om Hm) i)|
            + |∑ i ∈ indexSet n,
              (sv hnm (maskOp Om Hm) i - sigma * Real.sqrt (m:ℝ) * lamHat i)| := by
        apply abs_add_le
      exact le_trans hstep (add_le_add h1' h2')
    have hNbound : |(∑ i ∈ indexSet n, sv hnm (Yobs Om M0 Hm - maskOp Om M) i)
          - sigma * Real.sqrt (m:ℝ) * (∑ i ∈ indexSet n, lamHat i)|
        ≤ Real.sqrt (n:ℝ) * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp Om (M - M0))
          + (n:ℝ) * (C1 * Real.sqrt p * deltaM m * (sigma * Real.sqrt (m:ℝ))) :=
      le_trans htri (add_le_add hdep3' hsum3)
    have hD : (0:ℝ) < sigma * Real.sqrt (m:ℝ) * (∑ i ∈ indexSet n, lamHat i) :=
      mul_pos (mul_pos hsigma hsqrtm_pos) hSpos
    have hsig : sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M / sigma - 1
        = ((∑ i ∈ indexSet n, sv hnm (Yobs Om M0 Hm - maskOp Om M) i)
            - sigma * Real.sqrt (m:ℝ) * (∑ i ∈ indexSet n, lamHat i))
          / (sigma * Real.sqrt (m:ℝ) * (∑ i ∈ indexSet n, lamHat i)) := by
      have hne1 : sigma ≠ 0 := ne_of_gt hsigma
      have hne2 : (∑ i ∈ indexSet n, lamHat i) ≠ 0 := ne_of_gt hSpos
      have hne3 : Real.sqrt (m:ℝ) ≠ 0 := ne_of_gt hsqrtm_pos
      unfold sigmaHat
      field_simp
    rw [hsig, abs_div, abs_of_pos hD]
    have hsqrtmnp : Real.sqrt ((m:ℝ) * (n:ℝ) * p)
        = Real.sqrt (m:ℝ) * Real.sqrt (n:ℝ) * Real.sqrt p := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (le_of_lt hmpos)]
    have hsqn : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := by
      rw [← Real.sqrt_mul (le_of_lt hnpos)]
      exact Real.sqrt_mul_self (le_of_lt hnpos)
    have hsqrtn_pos : (0:ℝ) < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hnpos
    have key : ∀ (A F sm sn sp Sr sig C1' c2' del : ℝ),
        0 < sm → 0 < sn → 0 < sp → 0 < sig → 0 < c2' → 0 < C1' → 0 ≤ F → 0 < Sr →
          0 ≤ del →
          c2' * (n:ℝ) * sp ≤ Sr →
          sn * sn = (n:ℝ) →
          |A - sig * sm * Sr| ≤ sn * F + (n:ℝ) * (C1' * sp * del * (sig * sm)) →
          |A - sig * sm * Sr| / (sig * sm * Sr)
            ≤ (C1' / c2') * del + 1 / c2' * F / (sig * (sm * sn * sp)) := by
      intro A F sm sn sp Sr sig C1' c2' del hsm hsn hsp hsig hc2' hC1' hF hSr hdel h2' hsn2 hbound
      have hone : (1 / c2') * c2' = 1 := by
        field_simp
      have hDen : 0 < sig * sm * Sr := mul_pos (mul_pos hsig hsm) hSr
      have hDen2 : 0 < sig * (sm * sn * sp) :=
        mul_pos hsig (mul_pos (mul_pos hsm hsn) hsp)
      have hstep1 : |A - sig * sm * Sr| / (sig * sm * Sr)
          ≤ (sn * F + (n:ℝ) * (C1' * sp * del * (sig * sm))) / (sig * sm * Sr) := by
        rw [div_le_div_iff₀ hDen hDen]
        exact mul_le_mul_of_nonneg_right hbound hDen.le
      have h3a : sn * F / (sig * sm * Sr) ≤ (1 / c2') * F / (sig * (sm * sn * sp)) := by
        rw [div_le_div_iff₀ hDen hDen2]
        have hA : F * (sig * sm) * (c2' * (n:ℝ) * sp) ≤ F * (sig * sm) * Sr :=
          mul_le_mul_of_nonneg_left h2' (mul_nonneg hF (le_of_lt (mul_pos hsig hsm)))
        have hB := mul_le_mul_of_nonneg_left hA (le_of_lt (div_pos one_pos hc2'))
        calc sn * F * (sig * (sm * sn * sp))
            = (1 / c2') * (F * (sig * sm) * (c2' * (n:ℝ) * sp)) := by
              calc sn * F * (sig * (sm * sn * sp)) = F * (sig * sm) * (sn * sn) * sp := by ring
                _ = F * (sig * sm) * (n:ℝ) * sp := by rw [hsn2]
                _ = (1 / c2') * (F * (sig * sm) * (c2' * (n:ℝ) * sp)) := by
                    have hne : c2' ≠ 0 := ne_of_gt hc2'
                    field_simp
          _ ≤ (1 / c2') * (F * (sig * sm) * Sr) := hB
          _ = ((1 / c2') * F) * (sig * sm * Sr) := by ring
      have h3b : (n:ℝ) * (C1' * sp * del * (sig * sm)) / (sig * sm * Sr)
          ≤ (C1' / c2') * del := by
        have hstep : (C1' / c2') * del = (C1' * del) / c2' := by
          rw [div_mul_eq_mul_div]
        rw [hstep, div_le_div_iff₀ hDen hc2']
        have hkk : (C1' * del) * (sig * sm) * (c2' * (n:ℝ) * sp)
            ≤ (C1' * del) * (sig * sm) * Sr :=
          mul_le_mul_of_nonneg_left h2'
            (mul_nonneg (mul_nonneg (le_of_lt hC1') hdel) (le_of_lt (mul_pos hsig hsm)))
        calc (n:ℝ) * (C1' * sp * del * (sig * sm)) * c2'
            = (C1' * del) * (sig * sm) * (c2' * (n:ℝ) * sp) := by ring
          _ ≤ (C1' * del) * (sig * sm) * Sr := hkk
          _ = (C1' * del) * (sig * sm * Sr) := by ring
      calc |A - sig * sm * Sr| / (sig * sm * Sr)
          ≤ (sn * F + (n:ℝ) * (C1' * sp * del * (sig * sm))) / (sig * sm * Sr) := hstep1
        _ = sn * F / (sig * sm * Sr)
              + (n:ℝ) * (C1' * sp * del * (sig * sm)) / (sig * sm * Sr) := add_div _ _ _
        _ ≤ (1 / c2') * F / (sig * (sm * sn * sp)) + (C1' / c2') * del := add_le_add h3a h3b
        _ = (C1' / c2') * del + 1 / c2' * F / (sig * (sm * sn * sp)) := by ring
    rw [hsqrtmnp]
    exact key (∑ i ∈ indexSet n, sv hnm (Yobs Om M0 Hm - maskOp Om M) i)
      (Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp Om (M - M0)))
      (Real.sqrt (m:ℝ)) (Real.sqrt (n:ℝ)) (Real.sqrt p)
      (∑ i ∈ indexSet n, lamHat i) sigma C1 c2 (deltaM m)
      hsqrtm_pos hsqrtn_pos hsqrtp_pos hsigma hc2 hC1 hFnn hSpos hδnn h2 hsqn hNbound
  have hF0 : Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp Om (M0 - M0)) = 0 := by
    simp [Statlib.HighDim.MatrixAnalysis.frobeniusNorm, maskOp]
  have hconj2 : |sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M0 / sigma - 1|
      ≤ (C1 / c2) * deltaM m := by
    have h0 := hmain M0
    rw [hF0] at h0
    simpa using h0
  refine ⟨hmain, hconj2, ?_⟩
  intro hC4
  have habs : |sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M0 / sigma - 1| ≤ 1 / 2 :=
    le_trans hconj2 hC4
  have hx := (abs_le.mp habs).1
  have hge : (1:ℝ) / 2 ≤ sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M0 / sigma := by
    linarith
  have hs : sigma / 2 ≤ sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M0 := by
    have h := (le_div_iff₀ hsigma).mp hge
    linarith
  have hhalf : (0:ℝ) < sigma / 2 := by linarith
  exact ⟨hs, hhalf⟩
  /- @proof-region region.target-node.session.0f59eee89b1e1f3c end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3877234010_7a806c4e


