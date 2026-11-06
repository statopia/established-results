import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false in
theorem statopia_math_node_3997658605_d5d667e6 : ∀ (m n r : ℕ) (hn : 0 < n) (hnm : n ≤ m) (hr : 1 ≤ r)
    (p C_L K : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) (hC_L : 0 < C_L) (hK : 1 ≤ K)
    (Om M0 H Y M : Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ (i : Fin m) (j : Fin n), Om i j = 0 ∨ Om i j = 1)
    (hY : Y = obsMatrix Om M0 H)
    (w lamHat : Fin n → ℝ)
    (hw_nonneg : ∀ i : Fin n, 0 ≤ w i)
    (homega : 0 < w ⟨0, hn⟩)
    (hbulk : 0 < ∑ k ∈ bulkIdx n, lamHat k)
    (hlam1 : lamHat ⟨0, hn⟩ ≤ K * Real.sqrt p)
    (hloss : normLoss hnm p w lamHat Y Om M ≤ ((C_L * w ⟨0, hn⟩ : ℝ) : WithTop ℝ)),
    0 < sigmaHat hnm lamHat Y Om M ∧
      spectralNorm (Y - projMask Om M) ≤
        (K + Real.sqrt C_L) * sigmaHat hnm lamHat Y Om M * Real.sqrt ((m : ℝ) * p) := by
  /- @proof-region region.target-node.session.ea9ec9cd0bcd69e1 begin -/
  intro m n r hn hnm hr p C_L K hp_pos hp_le hC_L hK Om M0 H Y M hOm hY w lamHat
    hw_nonneg homega1 hbulk hlam1 hloss
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by
    have hm : 0 < m := lt_of_lt_of_le hn hnm
    exact_mod_cast hm
  have hne : Nonempty (Fin m) ∨ Nonempty (Fin n) := Or.inr ⟨⟨0, hn⟩⟩
  have hsv_nonneg : ∀ (E : Matrix (Fin m) (Fin n) ℝ) (k : Fin (min m n)),
      0 ≤ Statlib.HighDim.MatrixAnalysis.singularValues E k :=
    fun E k => (Statlib.HighDim.MatrixAnalysis.singular_value_properties E hne).2.1 k
  have hpsi_nonneg : ∀ (E : Matrix (Fin m) (Fin n) ℝ) (k : Fin n), 0 ≤ psi hnm E k :=
    fun E k => hsv_nonneg E (Fin.cast (Nat.min_eq_right hnm).symm k)
  have hsigma_ne : sigmaHat hnm lamHat Y Om M ≠ 0 := by
    intro h0
    simp only [normLoss, if_pos h0] at hloss
    exact WithTop.coe_ne_top (top_le_iff.mp hloss)
  have hloss_real : p⁻¹ * weightedLoss hnm w lamHat
      (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
      ≤ C_L * w ⟨0, hn⟩ := by
    simp only [normLoss, if_neg hsigma_ne] at hloss
    exact WithTop.coe_le_coe.mp hloss
  have hsigma_nonneg : 0 ≤ sigmaHat hnm lamHat Y Om M := by
    unfold sigmaHat
    exact div_nonneg
      (Finset.sum_nonneg (fun k _ => hpsi_nonneg (Y - projMask Om M) k))
      (mul_pos (Real.sqrt_pos.mpr hm_real_pos) hbulk).le
  have hsigma_pos : 0 < sigmaHat hnm lamHat Y Om M :=
    lt_of_le_of_ne hsigma_nonneg (Ne.symm hsigma_ne)
  have hsingle : w ⟨0, hn⟩ * (psi hnm
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
        ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2
      ≤ weightedLoss hnm w lamHat
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)) := by
    unfold weightedLoss
    exact Finset.single_le_sum
      (f := fun i => w i * (psi hnm
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
        i - lamHat i) ^ 2)
      (fun i _ => mul_nonneg (hw_nonneg i) (sq_nonneg _)) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
  have hW : weightedLoss hnm w lamHat
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
      ≤ p * (C_L * w ⟨0, hn⟩) := by
    have h := mul_le_mul_of_nonneg_left hloss_real hp_pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp_pos), one_mul] at h
  have hsquare : (psi hnm
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
        ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2 ≤ p * C_L := by
    have hW' : w ⟨0, hn⟩ * (psi hnm
          (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
          ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2 ≤ w ⟨0, hn⟩ * (p * C_L) := by
      calc w ⟨0, hn⟩ * (psi hnm
            (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
            ⟨0, hn⟩ - lamHat ⟨0, hn⟩) ^ 2
          ≤ weightedLoss hnm w lamHat (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)) := hsingle
        _ ≤ p * (C_L * w ⟨0, hn⟩) := hW
        _ = w ⟨0, hn⟩ * (p * C_L) := by ring
    nlinarith [hW', homega1]
  have hsqrt_bound : psi hnm
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
        ⟨0, hn⟩ ≤ (K + Real.sqrt C_L) * Real.sqrt p := by
    have habs : |psi hnm
          (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
          ⟨0, hn⟩ - lamHat ⟨0, hn⟩| ≤ Real.sqrt (p * C_L) := by
      have h2 := Real.sqrt_le_sqrt hsquare
      rwa [Real.sqrt_sq_eq_abs] at h2
    have hK : Real.sqrt (p * C_L) = Real.sqrt p * Real.sqrt C_L := Real.sqrt_mul hp_pos.le C_L
    calc psi hnm (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)) ⟨0, hn⟩
        ≤ lamHat ⟨0, hn⟩ + Real.sqrt (p * C_L) := by
          linarith [le_trans (le_abs_self _) habs]
      _ ≤ K * Real.sqrt p + Real.sqrt p * Real.sqrt C_L := by
          rw [hK]; linarith [hlam1]
      _ = (K + Real.sqrt C_L) * Real.sqrt p := by ring
  have hc_pos : 0 < Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M :=
    mul_pos (Real.sqrt_pos.mpr hm_real_pos) hsigma_pos
  have hmin_pos : 0 < min m n := by rw [Nat.min_eq_right hnm]; exact hn
  have hN_eq : (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
      = (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)⁻¹ • (Y - projMask Om M) := by
    ext i j
    simp [div_eq_mul_inv, mul_comm]
  have hpsi0 : psi hnm
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
        ⟨0, hn⟩
      = Statlib.HighDim.MatrixAnalysis.opNorm
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)) := by
    unfold psi
    rw [show Fin.cast (Nat.min_eq_right hnm).symm ⟨0, hn⟩ = ⟨0, hmin_pos⟩ from Fin.ext rfl]
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties _ hne).1 hmin_pos
  have hspec : spectralNorm (Y - projMask Om M)
      = Statlib.HighDim.MatrixAnalysis.opNorm (Y - projMask Om M) := by
    unfold spectralNorm
    rw [dif_pos hmin_pos]
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties _ hne).1 hmin_pos
  have hscale : Statlib.HighDim.MatrixAnalysis.opNorm
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
      = (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)⁻¹ *
        Statlib.HighDim.MatrixAnalysis.opNorm (Y - projMask Om M) := by
    rw [hN_eq]
    unfold Statlib.HighDim.MatrixAnalysis.opNorm
    rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc_pos)]
  have hpsiN : psi hnm
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
        ⟨0, hn⟩
      = spectralNorm (Y - projMask Om M) / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M) := by
    calc psi hnm (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)) ⟨0, hn⟩
        = Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)) := hpsi0
      _ = (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)⁻¹ * Statlib.HighDim.MatrixAnalysis.opNorm (Y - projMask Om M) := hscale
      _ = (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)⁻¹ * spectralNorm (Y - projMask Om M) := by
            rw [hspec]
      _ = spectralNorm (Y - projMask Om M) / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M) := by
            rw [div_eq_inv_mul]
  refine ⟨hsigma_pos, ?_⟩
  have hfinal : spectralNorm (Y - projMask Om M)
      = (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M) * psi hnm
        (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M))
        ⟨0, hn⟩ := by
    rw [hpsiN, div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc_pos), one_mul]
  calc spectralNorm (Y - projMask Om M)
      = (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M) * psi hnm (fun i j => (Y - projMask Om M) i j / (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M)) ⟨0, hn⟩ := hfinal
    _ ≤ (Real.sqrt (m : ℝ) * sigmaHat hnm lamHat Y Om M) * ((K + Real.sqrt C_L) * Real.sqrt p) :=
        mul_le_mul_of_nonneg_left hsqrt_bound (le_of_lt hc_pos)
    _ = (K + Real.sqrt C_L) * sigmaHat hnm lamHat Y Om M * Real.sqrt ((m : ℝ) * p) := by
        rw [Real.sqrt_mul hm_real_pos.le p]
        ring
  /- @proof-region region.target-node.session.ea9ec9cd0bcd69e1 end -/

end Statlib.Imported

