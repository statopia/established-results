import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548
import ProverJobs.ResidualE2EAssembly20261106.M_fdd291d964cdab2a1342

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
theorem statopia_math_node_488293955_708efb91 : ∀ (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (r : ℕ) (hr : 0 < r)
    (p Lambda mu : ℝ) (hp : 0 < p) (hLam : 0 ≤ Lambda) (hmu : 0 ≤ mu)
    (Om : Matrix (Fin m) (Fin n) ℝ)
    (hSchur : ∀ (kk : ℕ) (L : Matrix (Fin m) (Fin kk) ℝ) (R : Matrix (Fin n) (Fin kk) ℝ),
      spectralNorm (p⁻¹ • projMask Om (L * Matrix.transpose R) - L * Matrix.transpose R)
        ≤ Lambda * Real.sqrt (twoInfNormSq L) * Real.sqrt (twoInfNormSq R)),
    ∀ (kk : ℕ) (Uk : Matrix (Fin m) (Fin kk) ℝ) (Vk : Matrix (Fin n) (Fin kk) ℝ)
      (dk : Fin kk → ℝ),
      Matrix.transpose Uk * Uk = 1 →
      Matrix.transpose Vk * Vk = 1 →
      (∀ j : Fin kk, 0 < dk j) →
      (∀ i : Fin m, rowL2Sq Uk i ≤ mu * (r : ℝ) / (m : ℝ)) →
      (∀ j : Fin n, rowL2Sq Vk j ≤ mu * (r : ℝ) / (n : ℝ)) →
      spectralNorm (p⁻¹ • projMask Om (Uk * Matrix.diagonal dk * Matrix.transpose Vk)
          - Uk * Matrix.diagonal dk * Matrix.transpose Vk)
        ≤ Lambda * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))
            * spectralNorm (Uk * Matrix.diagonal dk * Matrix.transpose Vk) := by
  /- @proof-region region.target-node.session.4bba317206c3f128 begin -/
  intro m n hn hnm r hr p Lambda mu hp hLam hmu Om hSchur
  intro kk Uk Vk dk hUtU hVtV hdkpos hrowU hrowV
  set W : Matrix (Fin m) (Fin n) ℝ := Uk * Matrix.diagonal dk * Matrix.transpose Vk with hW
  set L : Matrix (Fin m) (Fin kk) ℝ := Uk * Matrix.diagonal (fun j => Real.sqrt (dk j)) with hL
  set R : Matrix (Fin n) (Fin kk) ℝ := Vk * Matrix.diagonal (fun j => Real.sqrt (dk j)) with hR
  have hLR : L * Matrix.transpose R = W := by
    rw [hL, hR, hW, Matrix.transpose_mul, Matrix.diagonal_transpose]
    have hdd : Matrix.diagonal (fun j => Real.sqrt (dk j)) * Matrix.diagonal (fun j => Real.sqrt (dk j))
        = Matrix.diagonal dk := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext j
      exact Real.mul_self_sqrt (le_of_lt (hdkpos j))
    calc (Uk * Matrix.diagonal (fun j => Real.sqrt (dk j))) * (Matrix.diagonal (fun j => Real.sqrt (dk j)) * Matrix.transpose Vk)
        = Uk * (Matrix.diagonal (fun j => Real.sqrt (dk j)) * (Matrix.diagonal (fun j => Real.sqrt (dk j)) * Matrix.transpose Vk)) := by
            rw [Matrix.mul_assoc]
      _ = Uk * ((Matrix.diagonal (fun j => Real.sqrt (dk j)) * Matrix.diagonal (fun j => Real.sqrt (dk j))) * Matrix.transpose Vk) := by
            rw [← Matrix.mul_assoc (Matrix.diagonal (fun j => Real.sqrt (dk j))) (Matrix.diagonal (fun j => Real.sqrt (dk j))) (Matrix.transpose Vk)]
      _ = Uk * (Matrix.diagonal dk * Matrix.transpose Vk) := by rw [hdd]
      _ = Uk * Matrix.diagonal dk * Matrix.transpose Vk := (Matrix.mul_assoc Uk (Matrix.diagonal dk) (Matrix.transpose Vk)).symm
  have hσ_nn : 0 ≤ spectralNorm W := by
    unfold spectralNorm
    split_ifs with h
    · unfold Statlib.HighDim.MatrixAnalysis.singularValues
      exact Real.sqrt_nonneg _
    · exact le_refl 0
  have hdk_le : ∀ j : Fin kk, dk j ≤ spectralNorm W := by
    have hmin : 0 < min m n := by rw [min_eq_right hnm]; exact hn
    intro j
    have h := statopia_math_node_3881171327_07a9338e m n kk Uk Vk dk hUtU hVtV hdkpos hmin j
    rw [← hW] at h
    exact h
  have hrowL : ∀ i : Fin m, rowL2Sq L i ≤ spectralNorm W * mu * (r : ℝ) / (m : ℝ) := by
    intro i
    have hcomp : rowL2Sq L i = ∑ j : Fin kk, (Uk i j)^2 * dk j := by
      unfold rowL2Sq
      rw [hL]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Matrix.mul_diagonal, Matrix.of_apply, mul_pow, Real.sq_sqrt (le_of_lt (hdkpos j))]
    rw [hcomp]
    calc ∑ j : Fin kk, (Uk i j)^2 * dk j
        ≤ spectralNorm W * ∑ j : Fin kk, (Uk i j)^2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum (fun j _ => ?_)
          rw [mul_comm (Uk i j ^ 2) (dk j)]
          exact mul_le_mul_of_nonneg_right (hdk_le j) (sq_nonneg (Uk i j))
      _ = spectralNorm W * rowL2Sq Uk i := rfl
      _ ≤ spectralNorm W * (mu * (r : ℝ) / (m : ℝ)) := mul_le_mul_of_nonneg_left (hrowU i) hσ_nn
      _ = spectralNorm W * mu * (r : ℝ) / (m : ℝ) := by ring_nf
  have hrowR : ∀ j : Fin n, rowL2Sq R j ≤ spectralNorm W * mu * (r : ℝ) / (n : ℝ) := by
    intro i
    have hcomp : rowL2Sq R i = ∑ k : Fin kk, (Vk i k)^2 * dk k := by
      unfold rowL2Sq
      rw [hR]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [Matrix.mul_diagonal, Matrix.of_apply, mul_pow, Real.sq_sqrt (le_of_lt (hdkpos k))]
    rw [hcomp]
    calc ∑ k : Fin kk, (Vk i k)^2 * dk k
        ≤ spectralNorm W * ∑ k : Fin kk, (Vk i k)^2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [mul_comm (Vk i k ^ 2) (dk k)]
          exact mul_le_mul_of_nonneg_right (hdk_le k) (sq_nonneg (Vk i k))
      _ = spectralNorm W * rowL2Sq Vk i := rfl
      _ ≤ spectralNorm W * (mu * (r : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_left (hrowV i) hσ_nn
      _ = spectralNorm W * mu * (r : ℝ) / (n : ℝ) := by ring_nf
  have htinfL : twoInfNormSq L ≤ spectralNorm W * mu * (r : ℝ) / (m : ℝ) := by
    unfold twoInfNormSq
    apply csSup_le
    · exact ⟨rowL2Sq L ⟨0, lt_of_lt_of_le hn hnm⟩, ⟨⟨0, lt_of_lt_of_le hn hnm⟩, rfl⟩⟩
    · rintro b ⟨i, hi⟩
      rw [← hi]
      exact hrowL i
  have htinfR : twoInfNormSq R ≤ spectralNorm W * mu * (r : ℝ) / (n : ℝ) := by
    unfold twoInfNormSq
    apply csSup_le
    · exact ⟨rowL2Sq R ⟨0, hn⟩, ⟨⟨0, hn⟩, rfl⟩⟩
    · rintro b ⟨i, hi⟩
      rw [← hi]
      exact hrowR i
  have hprod : Real.sqrt (twoInfNormSq L) * Real.sqrt (twoInfNormSq R)
      ≤ spectralNorm W * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) := by
    have hσmu : (0:ℝ) ≤ spectralNorm W * mu * (r : ℝ) :=
      mul_nonneg (mul_nonneg hσ_nn hmu) (by positivity)
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (lt_of_lt_of_le hn hnm)
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hXnn : 0 ≤ spectralNorm W * mu * (r : ℝ) / (m : ℝ) := div_nonneg hσmu (le_of_lt hm0)
    have hYnn : 0 ≤ spectralNorm W * mu * (r : ℝ) / (n : ℝ) := div_nonneg hσmu (le_of_lt hn0)
    have hZnn : 0 ≤ spectralNorm W * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) :=
      div_nonneg hσmu (Real.sqrt_nonneg _)
    have hprod2 : Real.sqrt (twoInfNormSq L) * Real.sqrt (twoInfNormSq R)
        ≤ Real.sqrt (spectralNorm W * mu * (r : ℝ) / (m : ℝ)) * Real.sqrt (spectralNorm W * mu * (r : ℝ) / (n : ℝ)) :=
      mul_le_mul (Real.sqrt_le_sqrt htinfL) (Real.sqrt_le_sqrt htinfR) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hXY : (spectralNorm W * mu * (r : ℝ) / (m : ℝ)) * (spectralNorm W * mu * (r : ℝ) / (n : ℝ))
        = (spectralNorm W * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)))^2 := by
      rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (m:ℝ) * (n:ℝ)), div_mul_div_comm, pow_two]
    have hkey : Real.sqrt (spectralNorm W * mu * (r : ℝ) / (m : ℝ)) * Real.sqrt (spectralNorm W * mu * (r : ℝ) / (n : ℝ))
        = spectralNorm W * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) := by
      calc Real.sqrt (spectralNorm W * mu * (r : ℝ) / (m : ℝ)) * Real.sqrt (spectralNorm W * mu * (r : ℝ) / (n : ℝ))
          = Real.sqrt ((spectralNorm W * mu * (r : ℝ) / (m : ℝ)) * (spectralNorm W * mu * (r : ℝ) / (n : ℝ))) :=
              (Real.sqrt_mul hXnn (spectralNorm W * mu * (r : ℝ) / (n : ℝ))).symm
        _ = Real.sqrt ((spectralNorm W * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)))^2) := by rw [hXY]
        _ = spectralNorm W * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) := Real.sqrt_sq hZnn
    exact le_trans hprod2 hkey.le
  have hstep : Lambda * Real.sqrt (twoInfNormSq L) * Real.sqrt (twoInfNormSq R)
      ≤ Lambda * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) * spectralNorm W := by
    have h := mul_le_mul_of_nonneg_left hprod hLam
    calc Lambda * Real.sqrt (twoInfNormSq L) * Real.sqrt (twoInfNormSq R)
        = Lambda * (Real.sqrt (twoInfNormSq L) * Real.sqrt (twoInfNormSq R)) := by ring
      _ ≤ Lambda * (spectralNorm W * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) := h
      _ = Lambda * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) * spectralNorm W := by ring_nf
  calc
    spectralNorm (p⁻¹ • projMask Om W - W)
        = spectralNorm (p⁻¹ • projMask Om (L * Matrix.transpose R) - L * Matrix.transpose R) := by
          rw [hLR]
    _ ≤ Lambda * Real.sqrt (twoInfNormSq L) * Real.sqrt (twoInfNormSq R) := hSchur kk L R
    _ ≤ Lambda * mu * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) * spectralNorm W := hstep
  /- @proof-region region.target-node.session.4bba317206c3f128 end -/

end Statlib.Imported

