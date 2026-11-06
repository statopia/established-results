import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SoftThresholdDenoisingHelpers
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548
import ProverJobs.ResidualE2EAssembly20261106.M_6e12677f17c847c6e6a8

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
theorem statopia_math_node_2550844442_8211841b : ∀ (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (r : ℕ) (hr : 0 < r)
    (p mu0 mu1 Lambda : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1)
    (hmu0 : 0 < mu0) (hmu0_le : mu0 ≤ mu1) (hLambda : 0 ≤ Lambda)
    (Om : Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ (i : Fin m) (j : Fin n), Om i j = 0 ∨ Om i j = 1)
    (hSchur : ∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
      spectralNorm (p⁻¹ • projMask Om (L * Matrix.transpose R) - L * Matrix.transpose R)
        ≤ Lambda * Real.sqrt (twoInfNormSq L) * Real.sqrt (twoInfNormSq R))
    (M0 : Matrix (Fin m) (Fin n) ℝ)
    (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ) (d0 : Fin r → ℝ)
    (hM0 : M0 = U0 * Matrix.diagonal d0 * Matrix.transpose V0)
    (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
    (hd0 : ∀ (i : Fin r), 0 < d0 i)
    (hlevU0 : ∀ (i : Fin m), rowL2Sq U0 i ≤ mu0 * (r : ℝ) / (m : ℝ))
    (hlevV0 : ∀ (j : Fin n), rowL2Sq V0 j ≤ mu0 * (r : ℝ) / (n : ℝ))
    (M : Matrix (Fin m) (Fin n) ℝ)
    (hMrank : Matrix.rank M ≤ r)
    (hMmem : M ∈ candidateSet r mu1)
    (k : ℕ) (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin k) ℝ) (d : Fin k → ℝ)
    (hk : k ≤ r)
    (hM : M = U * Matrix.diagonal d * Matrix.transpose V)
    (hU : Matrix.transpose U * U = 1) (hV : Matrix.transpose V * V = 1)
    (hd : ∀ (j : Fin k), 0 < d j)
    (hlevU : ∀ (i : Fin m), rowL2Sq U i ≤ mu1 * (r : ℝ) / (m : ℝ))
    (hlevV : ∀ (j : Fin n), rowL2Sq V j ≤ mu1 * (r : ℝ) / (n : ℝ)),
    spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0))
      ≤ 2 * (Lambda * max mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) *
          (spectralNorm M0 + spectralNorm (M - M0)) := by
  /- @proof-region region.target-node.session.1619022abb9416fe begin -/
  intro m n hn hnm r hr p mu0 mu1 Lambda hp_pos hp_le hmu0 hmu0_le hLambda
    Om hOm hSchur M0 U0 V0 d0 hM0 hU0 hV0 hd0 hlevU0 hlevV0 M hMrank hMmem
    k U V d hk hMfac hUtU hVtV hdpos hincU1 hincV1
  have hmin : 0 < min m n := by
    rw [min_eq_right hnm]; exact hn
  have hmpos : 0 < m := lt_of_lt_of_le hn hnm
  have hlin : p⁻¹ • projMask Om (M - M0) - (M - M0)
      = (p⁻¹ • projMask Om M - M) - (p⁻¹ • projMask Om M0 - M0) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, projMask, smul_eq_mul]
    ring
  rw [hlin]
  have hspec_nn : ∀ A : Matrix (Fin m) (Fin n) ℝ, 0 ≤ spectralNorm A := by
    intro A
    unfold spectralNorm
    rw [dif_pos hmin]
    exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties A
      (Or.inl ⟨⟨0, hmpos⟩⟩)).2.1 ⟨0, hmin⟩
  have hCnn : 0 ≤ Lambda * (max mu0 mu1) * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) := by
    have hmax : 0 < max mu0 mu1 := lt_of_lt_of_le hmu0 (le_max_left _ _)
    have hrnn : (0 : ℝ) ≤ (r : ℝ) := by positivity
    have hmn : (0 : ℝ) < (m : ℝ) * (n : ℝ) := by
      have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
      have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      positivity
    have hsqrt : 0 < Real.sqrt ((m : ℝ) * (n : ℝ)) := Real.sqrt_pos.mpr hmn
    exact div_nonneg (mul_nonneg (mul_nonneg hLambda (le_of_lt hmax)) hrnn) (le_of_lt hsqrt)
  have hsp : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      spectralNorm A = Statlib.HighDim.MatrixAnalysis.singularValues A ⟨0, hmin⟩ := by
    intro A
    unfold spectralNorm
    rw [dif_pos hmin]
  have hSNop : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      Statlib.HighDim.MatrixAnalysis.opNorm A = spectralNorm A := by
    intro A
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 A, hsp A]
    exact ((Statlib.HighDim.MatrixAnalysis.singular_value_properties A
      (Or.inl ⟨⟨0, hmpos⟩⟩)).1 hmin).symm
  have htri_gen : ∀ A B : Matrix (Fin m) (Fin n) ℝ,
      spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
    intro A B
    have hw := Statlib.HighDim.MatrixAnalysis.rectangular_singularValues_weyl_upper A B ⟨0, hmin⟩
    calc spectralNorm (A + B)
        = Statlib.HighDim.MatrixAnalysis.singularValues (A + B) ⟨0, hmin⟩ := hsp _
      _ ≤ Statlib.HighDim.MatrixAnalysis.singularValues A ⟨0, hmin⟩
            + Statlib.HighDim.MatrixAnalysis.opNorm B := hw
      _ = spectralNorm A + spectralNorm B := by rw [← hsp A, hSNop B]
  have hneg : ∀ Z : Matrix (Fin m) (Fin n) ℝ, spectralNorm (-Z) = spectralNorm Z := by
    intro Z
    rw [← hSNop (-Z), ← hSNop Z,
      Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 (-Z),
      Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 Z]
    rw [Matrix.l2_opNorm_def (-Z), Matrix.l2_opNorm_def Z]
    have hmap : (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (-Z)
        = -((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) Z) := by simp
    rw [hmap]
    exact ContinuousLinearMap.opNorm_neg _
  have htri : spectralNorm ((p⁻¹ • projMask Om M - M) - (p⁻¹ • projMask Om M0 - M0))
      ≤ spectralNorm (p⁻¹ • projMask Om M - M)
        + spectralNorm (p⁻¹ • projMask Om M0 - M0) := by
    calc spectralNorm ((p⁻¹ • projMask Om M - M) - (p⁻¹ • projMask Om M0 - M0))
        = spectralNorm ((p⁻¹ • projMask Om M - M) + -(p⁻¹ • projMask Om M0 - M0)) := by
          rw [sub_eq_add_neg]
      _ ≤ spectralNorm (p⁻¹ • projMask Om M - M)
            + spectralNorm (-(p⁻¹ • projMask Om M0 - M0)) := htri_gen _ _
      _ = spectralNorm (p⁻¹ • projMask Om M - M)
            + spectralNorm (p⁻¹ • projMask Om M0 - M0) := by
          rw [hneg (p⁻¹ • projMask Om M0 - M0)]
  have hboundM : spectralNorm (p⁻¹ • projMask Om M - M)
      ≤ Lambda * (max mu0 mu1) * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))
          * spectralNorm M := by
    have hrnn : (0 : ℝ) ≤ (r : ℝ) := by positivity
    have hmn : (0 : ℝ) < (m : ℝ) * (n : ℝ) := by
      have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
      have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      positivity
    have hsqrt : 0 < Real.sqrt ((m : ℝ) * (n : ℝ)) := Real.sqrt_pos.mpr hmn
    have hmu1nn : 0 ≤ mu1 := le_trans (le_of_lt hmu0) hmu0_le
    have hchildM : spectralNorm (p⁻¹ • projMask Om (U * Matrix.diagonal d * Matrix.transpose V)
          - U * Matrix.diagonal d * Matrix.transpose V)
        ≤ Lambda * mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))
            * spectralNorm (U * Matrix.diagonal d * Matrix.transpose V) :=
      statopia_math_node_488293955_708efb91 m n hn hnm r hr p Lambda mu1 hp_pos hLambda
        hmu1nn Om hSchur k U V d hUtU hVtV hdpos hincU1 hincV1
    have hchildM' : spectralNorm (p⁻¹ • projMask Om M - M)
        ≤ Lambda * mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) * spectralNorm M := by
      rw [hMfac]
      exact hchildM
    have hnum : Lambda * mu1 * (r : ℝ) ≤ Lambda * (max mu0 mu1) * (r : ℝ) := by
      have h1 : Lambda * mu1 ≤ Lambda * (max mu0 mu1) :=
        mul_le_mul_of_nonneg_left (le_max_right mu0 mu1) hLambda
      exact mul_le_mul_of_nonneg_right h1 hrnn
    have hKle : Lambda * mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))
        ≤ Lambda * (max mu0 mu1) * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (le_of_lt hsqrt))
    exact le_trans hchildM' (mul_le_mul_of_nonneg_right hKle (hspec_nn M))
  have hboundM0 : spectralNorm (p⁻¹ • projMask Om M0 - M0)
      ≤ Lambda * (max mu0 mu1) * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))
          * spectralNorm M0 := by
    have hrnn : (0 : ℝ) ≤ (r : ℝ) := by positivity
    have hmn : (0 : ℝ) < (m : ℝ) * (n : ℝ) := by
      have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
      have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      positivity
    have hsqrt : 0 < Real.sqrt ((m : ℝ) * (n : ℝ)) := Real.sqrt_pos.mpr hmn
    have hmu0nn : 0 ≤ mu0 := le_of_lt hmu0
    have hchildM0 : spectralNorm (p⁻¹ • projMask Om (U0 * Matrix.diagonal d0 * Matrix.transpose V0)
          - U0 * Matrix.diagonal d0 * Matrix.transpose V0)
        ≤ Lambda * mu0 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))
            * spectralNorm (U0 * Matrix.diagonal d0 * Matrix.transpose V0) :=
      statopia_math_node_488293955_708efb91 m n hn hnm r hr p Lambda mu0 hp_pos hLambda
        hmu0nn Om hSchur r U0 V0 d0 hU0 hV0 hd0 hlevU0 hlevV0
    have hchildM0' : spectralNorm (p⁻¹ • projMask Om M0 - M0)
        ≤ Lambda * mu0 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) * spectralNorm M0 := by
      rw [hM0]
      exact hchildM0
    have hnum : Lambda * mu0 * (r : ℝ) ≤ Lambda * (max mu0 mu1) * (r : ℝ) := by
      have h1 : Lambda * mu0 ≤ Lambda * (max mu0 mu1) :=
        mul_le_mul_of_nonneg_left (le_max_left mu0 mu1) hLambda
      exact mul_le_mul_of_nonneg_right h1 hrnn
    have hKle : Lambda * mu0 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))
        ≤ Lambda * (max mu0 mu1) * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (le_of_lt hsqrt))
    exact le_trans hchildM0' (mul_le_mul_of_nonneg_right hKle (hspec_nn M0))
  have hMnorm : spectralNorm M ≤ spectralNorm M0 + spectralNorm (M - M0) := by
    have h := htri_gen M0 (M - M0)
    rwa [show M0 + (M - M0) = M from by abel] at h
  calc spectralNorm ((p⁻¹ • projMask Om M - M) - (p⁻¹ • projMask Om M0 - M0))
      ≤ spectralNorm (p⁻¹ • projMask Om M - M)
          + spectralNorm (p⁻¹ • projMask Om M0 - M0) := htri
    _ ≤ Lambda * (max mu0 mu1) * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) * spectralNorm M
          + Lambda * (max mu0 mu1) * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))
              * spectralNorm M0 := add_le_add hboundM hboundM0
    _ = Lambda * (max mu0 mu1) * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))
          * (spectralNorm M + spectralNorm M0) := by rw [mul_add]
    _ ≤ Lambda * (max mu0 mu1) * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))
          * (2 * (spectralNorm M0 + spectralNorm (M - M0))) := by
        apply mul_le_mul_of_nonneg_left _ hCnn
        nlinarith [hMnorm, hspec_nn M0, hspec_nn (M - M0)]
    _ = 2 * (Lambda * (max mu0 mu1) * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)))
          * (spectralNorm M0 + spectralNorm (M - M0)) := by ring
  /- @proof-region region.target-node.session.1619022abb9416fe end -/

end Statlib.Imported

