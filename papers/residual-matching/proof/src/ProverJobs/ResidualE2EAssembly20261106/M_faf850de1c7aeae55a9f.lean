import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SoftThresholdDenoisingHelpers
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
theorem statopia_math_node_1461725421_1cd7d47b : ∀ (m n r : ℕ) (hn : 0 < n) (hnm : n ≤ m) (hr : 0 < r) (hrn : 12 * r ≤ n)
    (p sigma K c : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hsigma : 0 < sigma)
    (hK : 1 ≤ K) (hc : 0 < c)
    (Om H M0 M : Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ i j, Om i j = 0 ∨ Om i j = 1)
    (lamHat : Fin n → ℝ)
    (hrank : Matrix.rank (M - M0) ≤ 2 * r)
    (hnoise : spectralNorm (projMask Om H) ≤ K * sigma * Real.sqrt ((m : ℝ) * p))
    (hbulk : c * (n : ℝ) * Real.sqrt p ≤ ∑ i ∈ bulkIdx n, lamHat i),
    0 ≤ sigmaHat hnm lamHat (obsMatrix Om M0 H) Om M ∧
      sigmaHat hnm lamHat (obsMatrix Om M0 H) Om M * Real.sqrt ((m : ℝ) / p) ≤
        c⁻¹ * (K * sigma * Real.sqrt ((m : ℝ) / p) +
          spectralNorm ((p : ℝ)⁻¹ • projMask Om (M - M0) - (M - M0))) := by
  /- @proof-region region.target-node.session.78c6019db410f6f1 begin -/
  intro m n r hn hnm hr hrn p sigma K c hp hp_le hsigma hK hc Om H M0 M hOm lamHat hrank hnoise hbulk
  have hnn : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsval : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin (min m n)),
      0 ≤ Statlib.HighDim.MatrixAnalysis.singularValues A k := by
    intro A k
    exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties A (Or.inr hnn)).2.1 k
  have hLpos : 0 ≤ ∑ k ∈ bulkIdx n, lamHat k := by
    have hbase : 0 ≤ c * (n : ℝ) * Real.sqrt p :=
      mul_nonneg (mul_nonneg (le_of_lt hc) (by positivity)) (Real.sqrt_nonneg p)
    linarith [hbulk]
  constructor
  · unfold sigmaHat
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro k _
      simpa only [psi] using
        hsval (obsMatrix Om M0 H - projMask Om M)
          (Fin.cast (Nat.min_eq_right hnm).symm k)
    · exact mul_nonneg (Real.sqrt_nonneg (m : ℝ)) hLpos
  · have hminpos : 0 < min m n := by rw [Nat.min_eq_right hnm]; exact hn
    have hspecop : ∀ (A : Matrix (Fin m) (Fin n) ℝ),
        spectralNorm A = Statlib.HighDim.MatrixAnalysis.opNorm A := by
      intro A
      rw [spectralNorm, dif_pos hminpos,
        (Statlib.HighDim.MatrixAnalysis.singular_value_properties A (Or.inr hnn)).1 hminpos]
      rfl
    have hYdec : obsMatrix Om M0 H - projMask Om M
        = (-(p • (M - M0))) +
            (projMask Om H - p • (p⁻¹ • projMask Om (M - M0) - (M - M0))) := by
      have hpne : p ≠ 0 := ne_of_gt hp
      ext i j
      simp only [obsMatrix, projMask, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
        Matrix.smul_apply, smul_eq_mul]
      field_simp
      ring
    have hrankp : Matrix.rank (-(p • (M - M0))) ≤ 2 * r := by
      have heq : -(p • (M - M0)) = ((-p) • (1 : Matrix (Fin m) (Fin m) ℝ)) * (M - M0) := by
        rw [Matrix.smul_mul, Matrix.one_mul, neg_smul]
      rw [heq]
      exact le_trans (Matrix.rank_mul_le_right _ _) hrank
    have hEbound : Statlib.HighDim.MatrixAnalysis.opNorm
        (projMask Om H - p • (p⁻¹ • projMask Om (M - M0) - (M - M0)))
        ≤ K * sigma * Real.sqrt ((m : ℝ) * p) +
            p * spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0)) := by
      set Eo : Matrix (Fin m) (Fin n) ℝ := p⁻¹ • projMask Om (M - M0) - (M - M0)
      have htri : Statlib.HighDim.MatrixAnalysis.opNorm (projMask Om H - p • Eo)
          ≤ Statlib.HighDim.MatrixAnalysis.opNorm (projMask Om H) +
              Statlib.HighDim.MatrixAnalysis.opNorm (p • Eo) := by
        simp only [Statlib.HighDim.MatrixAnalysis.opNorm]
        rw [show LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (projMask Om H - p • Eo))
              = LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (projMask Om H))
                - LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (p • Eo)) from by
            rw [← map_sub, ← map_sub]]
        exact norm_sub_le _ _
      have h1 : Statlib.HighDim.MatrixAnalysis.opNorm (projMask Om H)
          = spectralNorm (projMask Om H) := (hspecop _).symm
      have h2 : Statlib.HighDim.MatrixAnalysis.opNorm (p • Eo) = p * spectralNorm Eo := by
        rw [hspecop Eo]
        simp only [Statlib.HighDim.MatrixAnalysis.opNorm]
        rw [show LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (p • Eo))
              = p • LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Eo) from by
            rw [← map_smul, ← map_smul]]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp]
      calc Statlib.HighDim.MatrixAnalysis.opNorm (projMask Om H - p • Eo)
          ≤ Statlib.HighDim.MatrixAnalysis.opNorm (projMask Om H) +
              Statlib.HighDim.MatrixAnalysis.opNorm (p • Eo) := htri
        _ = spectralNorm (projMask Om H) + p * spectralNorm Eo := by rw [h1, h2]
        _ ≤ K * sigma * Real.sqrt ((m : ℝ) * p) + p * spectralNorm Eo := by
              linarith [hnoise]
    have hidx : ∀ i ∈ bulkIdx n, 2 * r ≤ (i : ℕ) := by
      intro i hi
      simp only [bulkIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hge : 4 * r ≤ (n + 2) / 3 := by omega
      have h4 : 4 * r ≤ (i : ℕ) + 1 := le_trans hge hi.1
      omega
    have hper : ∀ i ∈ bulkIdx n,
        psi hnm (obsMatrix Om M0 H - projMask Om M) i
          ≤ K * sigma * Real.sqrt ((m : ℝ) * p) +
              p * spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0)) := by
      intro i hi
      have h_lt : (i : ℕ) < min m n := by
        rw [Nat.min_eq_right hnm]; exact i.isLt
      have hb := Statlib.HighDim.MatrixAnalysis.singularValues_tail_le_of_rank_add_opNorm_le
        (-(p • (M - M0)))
        (projMask Om H - p • (p⁻¹ • projMask Om (M - M0) - (M - M0)))
        hrankp hEbound (hidx i hi) h_lt
      have hpsi_eq : psi hnm (obsMatrix Om M0 H - projMask Om M) i
          = Statlib.HighDim.MatrixAnalysis.singularValues
              ((-(p • (M - M0))) + (projMask Om H - p • (p⁻¹ • projMask Om (M - M0) - (M - M0))))
              ⟨(i : ℕ), h_lt⟩ := by
        rw [hYdec]
        simp only [psi]
        exact congrArg _ (Fin.ext rfl)
      rw [hpsi_eq]
      exact hb
    have hSbound : (∑ k ∈ bulkIdx n, psi hnm (obsMatrix Om M0 H - projMask Om M) k)
        ≤ (n : ℝ) * (K * sigma * Real.sqrt ((m : ℝ) * p) +
            p * spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0))) := by
      have hbase : 0 ≤ K * sigma * Real.sqrt ((m : ℝ) * p) +
          p * spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0)) := by
        have h1 : 0 ≤ K * sigma * Real.sqrt ((m : ℝ) * p) :=
          mul_nonneg (mul_nonneg (le_trans zero_le_one hK) (le_of_lt hsigma)) (Real.sqrt_nonneg _)
        have h2 : 0 ≤ p * spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0)) := by
          apply mul_nonneg (le_of_lt hp)
          rw [hspecop _]
          exact Statlib.HighDim.MatrixAnalysis.opNorm_nonneg _
        linarith
      have hcard : ((bulkIdx n).card : ℝ) ≤ (n : ℝ) := by
        have h : (bulkIdx n).card ≤ n := by
          simpa using Finset.card_le_univ (bulkIdx n)
        exact_mod_cast h
      calc (∑ k ∈ bulkIdx n, psi hnm (obsMatrix Om M0 H - projMask Om M) k)
          ≤ ∑ k ∈ bulkIdx n, (K * sigma * Real.sqrt ((m : ℝ) * p) +
              p * spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0))) :=
            Finset.sum_le_sum hper
        _ = ((bulkIdx n).card : ℝ) * (K * sigma * Real.sqrt ((m : ℝ) * p) +
              p * spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n : ℝ) * (K * sigma * Real.sqrt ((m : ℝ) * p) +
              p * spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0))) :=
            mul_le_mul_of_nonneg_right hcard hbase
    have harith : (n : ℝ) * (K * sigma * Real.sqrt ((m : ℝ) * p) +
          p * spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0))) /
          (Real.sqrt (m : ℝ) * ∑ k ∈ bulkIdx n, lamHat k) * Real.sqrt ((m : ℝ) / p)
        ≤ c⁻¹ * (K * sigma * Real.sqrt ((m : ℝ) / p) +
            spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0))) := by
      have harith_gen : ∀ (Nm : ℝ), 0 ≤ Nm →
          (n : ℝ) * (K * sigma * Real.sqrt ((m : ℝ) * p) + p * Nm) /
              (Real.sqrt (m : ℝ) * ∑ k ∈ bulkIdx n, lamHat k) * Real.sqrt ((m : ℝ) / p)
            ≤ c⁻¹ * (K * sigma * Real.sqrt ((m : ℝ) / p) + Nm) := by
        intro Nm hNm
        have hm0 : (0:ℝ) < (m:ℝ) := by
          have h2 : 0 < m := lt_of_lt_of_le hn hnm
          exact_mod_cast h2
        have hs : 0 < Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr hm0
        have ht : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
        have hcne : c ≠ 0 := ne_of_gt hc
        have hsne : Real.sqrt (m:ℝ) ≠ 0 := ne_of_gt hs
        have htne : Real.sqrt p ≠ 0 := ne_of_gt ht
        have hLpos2 : 0 < ∑ k ∈ bulkIdx n, lamHat k := by
          have hbase : 0 < c * (n:ℝ) * Real.sqrt p := by
            have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
            exact mul_pos (mul_pos hc hn0) (Real.sqrt_pos.mpr hp)
          linarith [hbulk]
        have hLne : (∑ k ∈ bulkIdx n, lamHat k) ≠ 0 := ne_of_gt hLpos2
        have hsmLne : Real.sqrt (m:ℝ) * (∑ k ∈ bulkIdx n, lamHat k) ≠ 0 := mul_ne_zero hsne hLne
        have hKs : (0:ℝ) ≤ K * sigma := mul_nonneg (le_trans zero_le_one hK) (le_of_lt hsigma)
        have hspos : (0:ℝ) ≤ Real.sqrt p := le_of_lt ht
        have hmpos : (0:ℝ) ≤ Real.sqrt (m:ℝ) := le_of_lt hs
        have e1 : Real.sqrt ((m:ℝ)*p) = Real.sqrt (m:ℝ) * Real.sqrt p :=
          Real.sqrt_mul (le_of_lt hm0) p
        have e2 : Real.sqrt ((m:ℝ)/p) = Real.sqrt (m:ℝ) / Real.sqrt p := by
          have h1 : (m:ℝ)/p = (m:ℝ) * p⁻¹ := div_eq_mul_inv (m:ℝ) p
          rw [h1, Real.sqrt_mul (le_of_lt hm0) p⁻¹, Real.sqrt_inv, div_eq_mul_inv]
        rw [e1, e2]
        have hsqp : Real.sqrt p * Real.sqrt p = p := by nlinarith [Real.sq_sqrt (le_of_lt hp)]
        field_simp
        have hKmult : (K * sigma * Real.sqrt (m:ℝ)) * (c * ↑n * Real.sqrt p)
            ≤ (K * sigma * Real.sqrt (m:ℝ)) * (∑ k ∈ bulkIdx n, lamHat k) :=
          mul_le_mul_of_nonneg_left hbulk (mul_nonneg hKs hmpos)
        have hcp_eq : (c * ↑n * Real.sqrt p) * Real.sqrt p = c * ↑n * p := by
          rw [mul_assoc (c * ↑n) (Real.sqrt p) (Real.sqrt p), hsqp]
        have hNm2 : (c * ↑n * p) * Nm
            ≤ (∑ k ∈ bulkIdx n, lamHat k) * Real.sqrt p * Nm := by
          rw [← hcp_eq]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbulk hspos) hNm
        nlinarith [hKmult, hNm2]
      exact harith_gen (spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0)))
        (by rw [hspecop]; exact Statlib.HighDim.MatrixAnalysis.opNorm_nonneg _)
    unfold sigmaHat
    have hRpos : 0 < Real.sqrt (m : ℝ) * ∑ k ∈ bulkIdx n, lamHat k := by
      have hm0 : (0 : ℝ) < (m : ℝ) := by
        have : 0 < m := lt_of_lt_of_le hn hnm
        exact_mod_cast this
      have hsum : 0 < ∑ k ∈ bulkIdx n, lamHat k := by
        have hbase : 0 < c * (n : ℝ) * Real.sqrt p := by
          have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          exact mul_pos (mul_pos hc hn0) (Real.sqrt_pos.mpr hp)
        linarith [hbulk]
      exact mul_pos (Real.sqrt_pos.mpr hm0) hsum
    have hsqrtmp : 0 < Real.sqrt ((m : ℝ) / p) := by
      have hm0 : (0 : ℝ) < (m : ℝ) := by
        have : 0 < m := lt_of_lt_of_le hn hnm
        exact_mod_cast this
      exact Real.sqrt_pos.mpr (div_pos hm0 hp)
    have hstep : (∑ k ∈ bulkIdx n, psi hnm (obsMatrix Om M0 H - projMask Om M) k) /
          (Real.sqrt (m : ℝ) * ∑ k ∈ bulkIdx n, lamHat k) * Real.sqrt ((m : ℝ) / p)
        ≤ (n : ℝ) * (K * sigma * Real.sqrt ((m : ℝ) * p) +
            p * spectralNorm (p⁻¹ • projMask Om (M - M0) - (M - M0))) /
          (Real.sqrt (m : ℝ) * ∑ k ∈ bulkIdx n, lamHat k) * Real.sqrt ((m : ℝ) / p) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hsqrtmp)
      exact div_le_div_of_nonneg_right hSbound (le_of_lt hRpos)
    linarith [hstep, harith]
  /- @proof-region region.target-node.session.78c6019db410f6f1 end -/

end Statlib.Imported

