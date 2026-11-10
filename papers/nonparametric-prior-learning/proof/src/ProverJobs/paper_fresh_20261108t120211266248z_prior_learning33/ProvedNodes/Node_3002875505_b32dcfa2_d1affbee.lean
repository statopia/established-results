import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3002875505_b32dcfa2 : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : Type*) (bH : HilbertBasis ι ℝ H) (mu : ι → ℝ)
    (hmu_pos : ∀ i : ι, 0 < mu i)
    (t : ℝ) (ht : 0 ≤ t) (a b : H),
    (HScaleNorm bH mu t (a + b)) ^ (1 / 2 : ℝ) ≤
      (HScaleNorm bH mu t a) ^ (1 / 2 : ℝ) +
        (HScaleNorm bH mu t b) ^ (1 / 2 : ℝ) := by
  /- @proof-region region.target-node.session.58fd722cc1ca1408 begin -/
  intro H _ _ _ ι bH mu hmu_pos t ht a b
  have key : ∀ (c u v : ι → ℝ), (∀ i, 0 ≤ c i) →
      (∑' i, ENNReal.ofReal (c i * (u i + v i) ^ 2)) ^ (1 / 2 : ℝ) ≤
        (∑' i, ENNReal.ofReal (c i * u i ^ 2)) ^ (1 / 2 : ℝ) +
          (∑' i, ENNReal.ofReal (c i * v i ^ 2)) ^ (1 / 2 : ℝ) := by
    intro c u v hc
    have hfin : ∀ s : Finset ι,
        (∑ i ∈ s, ENNReal.ofReal (c i * (u i + v i) ^ 2)) ^ (1 / 2 : ℝ) ≤
          (∑ i ∈ s, ENNReal.ofReal (c i * u i ^ 2)) ^ (1 / 2 : ℝ) +
            (∑ i ∈ s, ENNReal.ofReal (c i * v i ^ 2)) ^ (1 / 2 : ℝ) := by
      intro s
      set As : ℝ := ∑ i ∈ s, c i * u i ^ 2 with hAs
      set Bs : ℝ := ∑ i ∈ s, c i * v i ^ 2 with hBs
      set Cs : ℝ := ∑ i ∈ s, c i * (u i + v i) ^ 2 with hCs
      have hAu : ∀ i ∈ s, 0 ≤ c i * u i ^ 2 := fun i _ => mul_nonneg (hc i) (sq_nonneg (u i))
      have hAv : ∀ i ∈ s, 0 ≤ c i * v i ^ 2 := fun i _ => mul_nonneg (hc i) (sq_nonneg (v i))
      have hAw : ∀ i ∈ s, 0 ≤ c i * (u i + v i) ^ 2 :=
        fun i _ => mul_nonneg (hc i) (sq_nonneg (u i + v i))
      have hA0 : 0 ≤ As := by rw [hAs]; exact Finset.sum_nonneg hAu
      have hB0 : 0 ≤ Bs := by rw [hBs]; exact Finset.sum_nonneg hAv
      have hC0 : 0 ≤ Cs := by rw [hCs]; exact Finset.sum_nonneg hAw
      have hCeq : Cs = As + 2 * (∑ i ∈ s, c i * u i * v i) + Bs := by
        rw [hCs, hAs, hBs, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hCS : (∑ i ∈ s, c i * u i * v i) ≤ Real.sqrt As * Real.sqrt Bs := by
        have h := Finset.sum_mul_sq_le_sq_mul_sq s
          (fun i => Real.sqrt (c i) * u i) (fun i => Real.sqrt (c i) * v i)
        have e1 : (∑ i ∈ s, (Real.sqrt (c i) * u i) * (Real.sqrt (c i) * v i)) =
            ∑ i ∈ s, c i * u i * v i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hci : Real.sqrt (c i) * Real.sqrt (c i) = c i := Real.mul_self_sqrt (hc i)
          calc (Real.sqrt (c i) * u i) * (Real.sqrt (c i) * v i)
              = (Real.sqrt (c i) * Real.sqrt (c i)) * (u i * v i) := by ring
            _ = c i * u i * v i := by rw [hci]; ring
        have e2 : (∑ i ∈ s, (Real.sqrt (c i) * u i) ^ 2) = As := by
          rw [hAs]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_pow, Real.sq_sqrt (hc i)]
        have e3 : (∑ i ∈ s, (Real.sqrt (c i) * v i) ^ 2) = Bs := by
          rw [hBs]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_pow, Real.sq_sqrt (hc i)]
        rw [e1, e2, e3] at h
        have hprod : 0 ≤ Real.sqrt As * Real.sqrt Bs :=
          mul_nonneg (Real.sqrt_nonneg As) (Real.sqrt_nonneg Bs)
        rcases le_total 0 (∑ i ∈ s, c i * u i * v i) with h0 | h0
        · have h' : (∑ i ∈ s, c i * u i * v i) * (∑ i ∈ s, c i * u i * v i) ≤ As * Bs := by
            simpa [pow_two] using h
          have h2 : Real.sqrt ((∑ i ∈ s, c i * u i * v i) * (∑ i ∈ s, c i * u i * v i))
              = ∑ i ∈ s, c i * u i * v i := Real.sqrt_mul_self h0
          have h3 : Real.sqrt (As * Bs) = Real.sqrt As * Real.sqrt Bs := Real.sqrt_mul hA0 Bs
          calc (∑ i ∈ s, c i * u i * v i)
              = Real.sqrt ((∑ i ∈ s, c i * u i * v i) * (∑ i ∈ s, c i * u i * v i)) := h2.symm
            _ ≤ Real.sqrt (As * Bs) := Real.sqrt_le_sqrt h'
            _ = Real.sqrt As * Real.sqrt Bs := h3
        · linarith
      have hmink : Real.sqrt Cs ≤ Real.sqrt As + Real.sqrt Bs := by
        have hAB : 0 ≤ Real.sqrt As + Real.sqrt Bs :=
          add_nonneg (Real.sqrt_nonneg As) (Real.sqrt_nonneg Bs)
        have hmain : Cs ≤ (Real.sqrt As + Real.sqrt Bs) ^ 2 := by
          have hsq : (Real.sqrt As + Real.sqrt Bs) ^ 2 =
              As + 2 * (Real.sqrt As * Real.sqrt Bs) + Bs := by
            nlinarith [Real.mul_self_sqrt hA0, Real.mul_self_sqrt hB0]
          nlinarith [hCS, hCeq]
        calc Real.sqrt Cs ≤ Real.sqrt ((Real.sqrt As + Real.sqrt Bs) ^ 2) :=
              Real.sqrt_le_sqrt hmain
          _ = Real.sqrt As + Real.sqrt Bs := Real.sqrt_sq hAB
      have eA : (∑ i ∈ s, ENNReal.ofReal (c i * u i ^ 2)) = ENNReal.ofReal As := by
        rw [hAs, ENNReal.ofReal_sum_of_nonneg hAu]
      have eB : (∑ i ∈ s, ENNReal.ofReal (c i * v i ^ 2)) = ENNReal.ofReal Bs := by
        rw [hBs, ENNReal.ofReal_sum_of_nonneg hAv]
      have eC : (∑ i ∈ s, ENNReal.ofReal (c i * (u i + v i) ^ 2)) = ENNReal.ofReal Cs := by
        rw [hCs, ENNReal.ofReal_sum_of_nonneg hAw]
      rw [eA, eB, eC]
      have sA : (ENNReal.ofReal As) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt As) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num), ← Real.sqrt_eq_rpow]
      have sB : (ENNReal.ofReal Bs) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt Bs) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num), ← Real.sqrt_eq_rpow]
      have sC : (ENNReal.ofReal Cs) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt Cs) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hC0 (by norm_num), ← Real.sqrt_eq_rpow]
      rw [sA, sB, sC, ← ENNReal.ofReal_add (Real.sqrt_nonneg As) (Real.sqrt_nonneg Bs)]
      exact ENNReal.ofReal_le_ofReal hmink
    set K : ENNReal := (∑' i, ENNReal.ofReal (c i * u i ^ 2)) ^ (1 / 2 : ℝ) +
      (∑' i, ENNReal.ofReal (c i * v i ^ 2)) ^ (1 / 2 : ℝ) with hK
    have hpow : ∀ x : ENNReal, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
      intro x
      rw [← ENNReal.rpow_mul x (1 / 2 : ℝ) (2 : ℝ)]
      have h : (1 / 2 : ℝ) * 2 = 1 := by norm_num
      rw [h, ENNReal.rpow_one]
    have hKpow : (K ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = K := by
      rw [← ENNReal.rpow_mul K (2 : ℝ) (1 / 2 : ℝ)]
      have h : (2 : ℝ) * (1 / 2) = 1 := by norm_num
      rw [h, ENNReal.rpow_one]
    have hstep : ∀ s : Finset ι,
        (∑ i ∈ s, ENNReal.ofReal (c i * (u i + v i) ^ 2)) ≤ K ^ (2 : ℝ) := by
      intro s
      have h1 : (∑ i ∈ s, ENNReal.ofReal (c i * (u i + v i) ^ 2)) ^ (1 / 2 : ℝ) ≤ K := by
        have h2 : (∑ i ∈ s, ENNReal.ofReal (c i * u i ^ 2)) ^ (1 / 2 : ℝ) ≤
            (∑' i, ENNReal.ofReal (c i * u i ^ 2)) ^ (1 / 2 : ℝ) :=
          (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr
            (ENNReal.sum_le_tsum s)
        have h3 : (∑ i ∈ s, ENNReal.ofReal (c i * v i ^ 2)) ^ (1 / 2 : ℝ) ≤
            (∑' i, ENNReal.ofReal (c i * v i ^ 2)) ^ (1 / 2 : ℝ) :=
          (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr
            (ENNReal.sum_le_tsum s)
        calc (∑ i ∈ s, ENNReal.ofReal (c i * (u i + v i) ^ 2)) ^ (1 / 2 : ℝ)
            ≤ (∑ i ∈ s, ENNReal.ofReal (c i * u i ^ 2)) ^ (1 / 2 : ℝ) +
                (∑ i ∈ s, ENNReal.ofReal (c i * v i ^ 2)) ^ (1 / 2 : ℝ) := hfin s
          _ ≤ (∑' i, ENNReal.ofReal (c i * u i ^ 2)) ^ (1 / 2 : ℝ) +
                (∑' i, ENNReal.ofReal (c i * v i ^ 2)) ^ (1 / 2 : ℝ) := add_le_add h2 h3
          _ = K := hK.symm
      calc (∑ i ∈ s, ENNReal.ofReal (c i * (u i + v i) ^ 2))
          = ((∑ i ∈ s, ENNReal.ofReal (c i * (u i + v i) ^ 2)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
            (hpow _).symm
        _ ≤ K ^ (2 : ℝ) :=
            (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mpr h1
    have hCK : (∑' i, ENNReal.ofReal (c i * (u i + v i) ^ 2)) ≤ K ^ (2 : ℝ) := by
      rw [ENNReal.tsum_eq_iSup_sum]
      exact iSup_le hstep
    calc (∑' i, ENNReal.ofReal (c i * (u i + v i) ^ 2)) ^ (1 / 2 : ℝ)
        ≤ (K ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr hCK
      _ = K := hKpow
  have hc0 : ∀ i : ι, 0 ≤ Real.rpow (mu i) (-t) :=
    fun i => le_of_lt (Real.rpow_pos_of_pos (hmu_pos i) (-t))
  have hkey := key (fun i => Real.rpow (mu i) (-t))
    (fun i => inner ℝ (bH i) a) (fun i => inner ℝ (bH i) b) hc0
  simpa [HScaleNorm, inner_add_right] using hkey
  /- @proof-region region.target-node.session.58fd722cc1ca1408 end -/

end Statlib.Imported
end

