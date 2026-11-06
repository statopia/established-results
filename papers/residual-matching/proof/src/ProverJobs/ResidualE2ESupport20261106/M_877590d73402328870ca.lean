import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_515d9600226534ea5a92
import ProverJobs.ResidualE2ESupport20261106.M_50e7268f36fab0891165

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106

set_option maxHeartbeats 4000000
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
theorem statopia_math_node_1222515461_d927f311 : ∀ (alpha0 : ℝ) (halpha0 : 15 < alpha0) (rhoMin : ℝ) (hrhoMin : 0 < rhoMin),
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ m0 : ℕ,
      ∀ (m n r : ℕ) (p : ℝ) {Ωs : Type*} [MeasurableSpace Ωs]
        (μΩ : Measure Ωs) [IsProbabilityMeasure μΩ]
        (Om : Ωs → Matrix (Fin m) (Fin n) ℝ)
        (M0 : Matrix (Fin m) (Fin n) ℝ) (U0 : Matrix (Fin m) (Fin r) ℝ)
        (d0 : Fin r → ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ) (mu0 : ℝ),
        m0 ≤ m → 2 ≤ n → n ≤ m → 0 < p → p ≤ 1 →
        rhoMin ≤ rho m n → rho m n ≤ 1 →
        Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p →
        IsIncoherentSVD M0 U0 d0 V0 mu0 →
        IsBernoulliMask μΩ Om p →
        μΩ {ω : Ωs |
              (Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om ω))
                  ≤ C * Real.sqrt ((m : ℝ) / p)) ∧
                ∀ A B : Matrix (Fin m) (Fin n) ℝ,
                  inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
                    |matInner (TOmega (Om ω) U0 V0 A) B - p * matInner A B|
                      ≤ C * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                          * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                          * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B}
          ≥ ENNReal.ofReal (1 - c * ((n : ℝ) ^ 4)⁻¹) := by
  intro alpha0 halpha rhoMin hrhoMin
  have probe_row : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ),
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rowNorm A
        = rowSupNorm A := by
    intro m n A
    unfold _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rowNorm
    rfl
  have probe_inner : ∀ {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ),
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobInner A B
        = matInner A B := by
    intro m n A B
    unfold _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobInner
    rfl
  have probe_norm : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ),
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobNorm A
        = Statlib.HighDim.MatrixAnalysis.frobeniusNorm A := by
    intro m n A
    unfold _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobNorm
    rfl
  have probe_spec : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ),
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.specNorm A
        = Statlib.HighDim.MatrixAnalysis.opNorm A := by
    intro m n A
    unfold _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.specNorm
    rfl
  have probe_wmask : ∀ {m n : ℕ} (p : ℝ) (Om : Matrix (Fin m) (Fin n) ℝ),
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Wmask p Om
        = centeredMaskOp p Om := by
    intro m n p Om
    unfold _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Wmask
    rfl
  have probe_ge_spec : ∀ {m n r : ℕ} (p Λ θ : ℝ) (Om : Matrix (Fin m) (Fin n) ℝ)
      (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ),
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.GoodEvent p Λ θ Om U0 V0 →
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.specNorm
        (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Wmask p Om) ≤ Λ := by
    intro m n r p Λ θ Om U0 V0 h
    unfold _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.GoodEvent at h
    exact h.1
  have probe_spec' : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ),
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.specNorm A
        = Statlib.HighDim.MatrixAnalysis.opNorm A := probe_spec
  have probe_wmask' : ∀ {m n : ℕ} (p : ℝ) (Om : Matrix (Fin m) (Fin n) ℝ),
      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Wmask p Om
        = centeredMaskOp p Om := probe_wmask
  have hfrob : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ),
      Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
        = Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
    intro m n A
    unfold Statlib.HighDim.MatrixAnalysis.frobeniusNorm
    rfl


  obtain ⟨N0, Cs, CL, Cth, cD, hCs, hCL, hCth, hcD, hD⟩ :=
    _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.paper_45fc93d926fd4099b9973daee59eb529
      rhoMin hrhoMin alpha0 halpha
  have hm0 : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → N0 ≤ m ∧ 2 ≤ m ∧ 12 / Cs ≤ Real.log (m : ℝ) := by
    have hlog : Filter.Tendsto (fun m : ℕ => Real.log (m : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h1 : ∀ᶠ m : ℕ in Filter.atTop, N0 ≤ m ∧ 2 ≤ m :=
      (Filter.eventually_ge_atTop (max N0 2)).mono
        (fun m hm => ⟨le_trans (le_max_left _ _) hm, le_trans (le_max_right _ _) hm⟩)
    have h2 : ∀ᶠ m : ℕ in Filter.atTop, 12 / Cs ≤ Real.log (m : ℝ) :=
      hlog.eventually (Filter.eventually_ge_atTop (12 / Cs))
    have hall : ∀ᶠ m : ℕ in Filter.atTop, N0 ≤ m ∧ 2 ≤ m ∧ 12 / Cs ≤ Real.log (m : ℝ) := by
      filter_upwards [h1, h2] with m hm1 hm2 using ⟨hm1.1, hm1.2, hm2⟩
    exact Filter.eventually_atTop.mp hall
  obtain ⟨m0G, hm0G⟩ := hm0
  refine ⟨CL + Cth + 2 * Real.sqrt Cs + 1, cD, ?_, hcD, m0G, ?_⟩
  · have h1 : 0 ≤ Real.sqrt Cs := Real.sqrt_nonneg Cs
    linarith only [hCL, hCth, h1]
  · intro m n r p Ωs _ μΩ _ Om M0 U0 d0 V0 mu0 hm hn hnm hp0 hp1 hrho_lo hrho_hi hmp hM0 hmask
    obtain ⟨hM0eq, hM0pos, hU0, hV0, hrowU, hrowV⟩ := hM0
    have hrowU' : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rowNorm U0
        ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) := by
      rw [probe_row]
      exact hrowU
    have hrowV' : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rowNorm V0
        ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) := by
      rw [probe_row]
      exact hrowV
    have htan : ∀ A : Matrix (Fin m) (Fin n) ℝ, inTangentSpace U0 V0 A →
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.MemTangentRect U0 V0 A := by
      intro A hA
      refine ⟨(U0.transpose * A * (1 - V0 * V0.transpose)).transpose, A * V0, ?_⟩
      rw [Matrix.transpose_transpose]
      have hX : A * (1 - V0 * V0.transpose)
          = (U0 * U0.transpose) * (A * (1 - V0 * V0.transpose)) := by
        have h3 : (1 - U0 * U0.transpose) * (A * (1 - V0 * V0.transpose)) = 0 := by
          rw [← Matrix.mul_assoc]
          exact hA
        have h4 : A * (1 - V0 * V0.transpose)
            - (U0 * U0.transpose) * (A * (1 - V0 * V0.transpose)) = 0 := by
          simpa [Matrix.sub_mul] using h3
        exact sub_eq_zero.mp h4
      calc A = A * (1 - V0 * V0.transpose) + A * (V0 * V0.transpose) := by
              rw [Matrix.mul_sub, Matrix.mul_one]
              abel
          _ = (U0 * U0.transpose) * (A * (1 - V0 * V0.transpose))
                + A * (V0 * V0.transpose) := congrArg (fun Z => Z + A * (V0 * V0.transpose)) hX
          _ = U0 * (U0.transpose * A * (1 - V0 * V0.transpose))
                + (A * V0) * V0.transpose := by simp only [Matrix.mul_assoc]
    have hsum_sq : ∑ i : Fin m, ∑ j : Fin r, U0 i j ^ 2 = (r : ℝ) := by
      have h1 : ∑ j : Fin r, (U0.transpose * U0) j j = (r : ℝ) := by
        rw [hU0]
        simp
      calc ∑ i : Fin m, ∑ j : Fin r, U0 i j ^ 2
          = ∑ j : Fin r, ∑ i : Fin m, U0 i j ^ 2 := Finset.sum_comm
        _ = ∑ j : Fin r, (U0.transpose * U0) j j := by
              simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
        _ = (r : ℝ) := h1
    have hmu0 : ∀ (_ : 1 ≤ r), (1 : ℝ) ≤ mu0 := by
      intro hr1
      have hm2 : 2 ≤ m := (hm0G m hm).2.1
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hrpos : (0 : ℝ) < (r : ℝ) := by
        have h : 0 < r := by omega
        exact_mod_cast h
      have hrow : ∀ i : Fin m,
          ∑ j : Fin r, U0 i j ^ 2 ≤ (Real.sqrt (mu0 * (r : ℝ) / (m : ℝ))) ^ 2 := by
        intro i
        have hbdd : BddAbove (Set.range (fun i : Fin m => Real.sqrt (∑ j : Fin r, U0 i j ^ 2))) :=
          (Set.finite_range _).bddAbove
        have hle : Real.sqrt (∑ j : Fin r, U0 i j ^ 2) ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) :=
          le_trans (le_csSup hbdd (Set.mem_range_self i)) hrowU
        calc ∑ j : Fin r, U0 i j ^ 2 = (Real.sqrt (∑ j : Fin r, U0 i j ^ 2)) ^ 2 := by
              rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
          _ ≤ (Real.sqrt (mu0 * (r : ℝ) / (m : ℝ))) ^ 2 := by
              rw [pow_two, pow_two]
              exact mul_self_le_mul_self (Real.sqrt_nonneg _) hle
      have hbound : (r : ℝ) ≤ (m : ℝ) * (Real.sqrt (mu0 * (r : ℝ) / (m : ℝ))) ^ 2 := by
        have h3 : ∑ i : Fin m, ∑ j : Fin r, U0 i j ^ 2
            ≤ ∑ _i : Fin m, (Real.sqrt (mu0 * (r : ℝ) / (m : ℝ))) ^ 2 :=
          Finset.sum_le_sum (fun i _ => hrow i)
        rw [hsum_sq] at h3
        simpa [Finset.sum_const, nsmul_eq_mul] using h3
      by_cases hx : 0 ≤ mu0 * (r : ℝ) / (m : ℝ)
      · have h4 : (m : ℝ) * (mu0 * (r : ℝ) / (m : ℝ)) = mu0 * (r : ℝ) := by
          field_simp
        rw [Real.sq_sqrt hx, h4] at hbound
        have h5 : (r : ℝ) ≤ mu0 * (r : ℝ) := hbound
        have h7 : (r : ℝ) * (r : ℝ)⁻¹ ≤ mu0 * (r : ℝ) * (r : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right h5 (inv_pos.mpr hrpos).le
        simpa [mul_assoc, mul_inv_cancel₀ hrpos.ne'] using h7
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx)] at hbound
        have h6 : (r : ℝ) ≤ 0 := by simpa using hbound
        linarith
    have hkey : U0.transpose * M0 * V0 = Matrix.diagonal d0 := by
      simp only [hM0eq, Matrix.mul_assoc, hV0, Matrix.mul_one]
      rw [← Matrix.mul_assoc, hU0, Matrix.one_mul]
    have hcard : (Matrix.diagonal d0).rank = r := by
      rw [Matrix.rank_diagonal]
      have e : {i : Fin r // d0 i ≠ 0} ≃ Fin r :=
        { toFun := fun x => x.1
          invFun := fun i => ⟨i, ne_of_gt (hM0pos i)⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun i => rfl }
      rw [Fintype.card_congr e, Fintype.card_fin]
    have hrank : M0.rank = r := by
      have h1 : r ≤ M0.rank := by
        rw [← hcard, ← hkey]
        exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
      have h3 : M0.rank ≤ r := by
        have hU0rank : U0.rank ≤ r := by
          simpa using Matrix.rank_le_card_width U0
        calc M0.rank = (U0 * (Matrix.diagonal d0 * V0.transpose)).rank := by
                rw [hM0eq]
                simp only [Matrix.mul_assoc]
          _ ≤ U0.rank := Matrix.rank_mul_le_left _ _
          _ ≤ r := hU0rank
      omega
    have hTR : ∀ X Y : Matrix (Fin m) (Fin n) ℝ, matInner X Y = (X * Y.transpose).trace := by
      intro X Y
      simp [matInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    have hQ1 : (1 - U0 * U0.transpose).transpose = 1 - U0 * U0.transpose := by
      simp [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_one,
        Matrix.transpose_transpose]
    have hQ2 : (1 - V0 * V0.transpose).transpose = 1 - V0 * V0.transpose := by
      simp [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_one,
        Matrix.transpose_transpose]
    have hproj : ∀ (Om' : Matrix (Fin m) (Fin n) ℝ) (A B : Matrix (Fin m) (Fin n) ℝ),
        inTangentSpace U0 V0 B →
        matInner (TOmega Om' U0 V0 A) B = matInner (maskOp Om' A) B := by
      intro Om' A B hB
      have hsq : (1 - V0 * V0.transpose) * B.transpose * (1 - U0 * U0.transpose) = 0 := by
        have h := congrArg Matrix.transpose hB
        simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.transpose_transpose, hQ1, hQ2, Matrix.transpose_zero] at h
        simpa [Matrix.mul_assoc] using h
      have hzero : matInner ((1 - U0 * U0.transpose) * (maskOp Om' A)
          * (1 - V0 * V0.transpose)) B = 0 := by
        rw [hTR]
        set P : Matrix (Fin m) (Fin m) ℝ := 1 - U0 * U0.transpose with hP
        set Q : Matrix (Fin n) (Fin n) ℝ := 1 - V0 * V0.transpose with hQ
        set M' : Matrix (Fin m) (Fin n) ℝ := maskOp Om' A with hM'
        have hsq' : Q * B.transpose * P = 0 := by
          rw [hP, hQ]
          exact hsq
        have h1 : ((P * M' * Q) * B.transpose).trace
            = (B.transpose * (P * M' * Q)).trace :=
          Matrix.trace_mul_comm (A := P * M' * Q) (B := B.transpose)
        have e1 : (B.transpose * (P * M' * Q)).trace
            = ((B.transpose * P) * (M' * Q)).trace := by
          simp only [Matrix.mul_assoc]
        have h2 : ((B.transpose * P) * (M' * Q)).trace
            = ((M' * Q) * (B.transpose * P)).trace :=
          Matrix.trace_mul_comm (A := B.transpose * P) (B := M' * Q)
        have e2 : ((M' * Q) * (B.transpose * P)).trace
            = (M' * (Q * B.transpose * P)).trace := by
          simp only [Matrix.mul_assoc]
        rw [h1, e1, h2, e2]
        simp [hsq']
      have hsub : matInner ((maskOp Om' A) - (1 - U0 * U0.transpose) * (maskOp Om' A)
          * (1 - V0 * V0.transpose)) B
          = matInner (maskOp Om' A) B
            - matInner ((1 - U0 * U0.transpose) * (maskOp Om' A)
              * (1 - V0 * V0.transpose)) B := by
        simp [matInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
      show matInner ((maskOp Om' A) - (1 - U0 * U0.transpose) * (maskOp Om' A)
        * (1 - V0 * V0.transpose)) B = matInner (maskOp Om' A) B
      rw [hsub, hzero, sub_zero]
    have probe_ge_tan : ∀ {m n r : ℕ} (p Λ θ : ℝ) (Om : Matrix (Fin m) (Fin n) ℝ)
        (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ),
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.GoodEvent
            p Λ θ Om U0 V0 →
        ∀ A B : Matrix (Fin m) (Fin n) ℝ,
          _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.MemTangentRect U0 V0 A →
          _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.MemTangentRect U0 V0 B →
          |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobInner
              (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask p Om A) B|
            ≤ θ * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobNorm A
                * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobNorm B := by
      intro m n r p Λ θ Om U0 V0 h A B hA hB
      unfold _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.GoodEvent at h
      exact h.2.1 A B hA hB
    have htmask_eq : ∀ (p : ℝ) (Om' A : Matrix (Fin m) (Fin n) ℝ),
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask p Om' A
          = fun i j => (p⁻¹ * Om' i j - 1) * A i j := by
      intro p' Om' A
      unfold _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Wmask
      rfl
    have htanId : ∀ (Om' A B : Matrix (Fin m) (Fin n) ℝ), inTangentSpace U0 V0 B →
        matInner (TOmega Om' U0 V0 A) B - p * matInner A B
          = p * matInner (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask p Om' A) B := by
      intro Om' A B hB
      rw [hproj Om' A B hB, htmask_eq]
      have hpne : p ≠ 0 := ne_of_gt hp0
      have hpt : ∀ i j, (Om' i j * A i j) * B i j - p * (A i j * B i j)
          = p * ((p⁻¹ * Om' i j - 1) * A i j * B i j) := by
        intro i j
        field_simp
      calc matInner (maskOp Om' A) B - p * matInner A B
          = (∑ i, ∑ j, (Om' i j * A i j) * B i j) - p * (∑ i, ∑ j, A i j * B i j) := by
              simp [matInner, maskOp]
        _ = ∑ i, ∑ j, ((Om' i j * A i j) * B i j - p * (A i j * B i j)) := by
              simp only [Finset.mul_sum, Finset.sum_sub_distrib]
        _ = ∑ i, ∑ j, p * ((p⁻¹ * Om' i j - 1) * A i j * B i j) :=
              Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))
        _ = p * matInner (fun i j => (p⁻¹ * Om' i j - 1) * A i j) B := by
              simp only [matInner, Finset.mul_sum]
    have hGEtan : ∀ (Λ θ : ℝ) (Om' : Matrix (Fin m) (Fin n) ℝ),
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.GoodEvent
            p Λ θ Om' U0 V0 →
        ∀ A B : Matrix (Fin m) (Fin n) ℝ, inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
          |matInner (TOmega Om' U0 V0 A) B - p * matInner A B|
            ≤ θ * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B := by
      intro Λ θ Om' hGE A B hA hB
      have h1 : |matInner (TOmega Om' U0 V0 A) B - p * matInner A B|
          = p * |matInner (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask p Om' A) B| := by
        rw [htanId Om' A B hB, abs_mul, abs_of_pos hp0]
      rw [h1]
      have h3 : |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobInner
            (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask p Om' A) B|
          ≤ θ * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobNorm A
              * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobNorm B :=
        probe_ge_tan p Λ θ Om' U0 V0 hGE A B (htan A hA) (htan B hB)
      rw [probe_inner, probe_norm, probe_norm] at h3
      calc p * |matInner (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask p Om' A) B|
          = |matInner (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask p Om' A) B| * p :=
              mul_comm _ _
        _ ≤ |matInner (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask p Om' A) B| * 1 :=
              mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
        _ = |matInner (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask p Om' A) B| :=
              mul_one _
        _ ≤ θ * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
              * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B := h3
    have hCS2 : ∀ X Y : Matrix (Fin m) (Fin n) ℝ,
        ∑ i, ∑ j, X i j * Y i j
          ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm X
              * Statlib.HighDim.MatrixAnalysis.frobeniusNorm Y := by
      intro X Y
      have h1 : ∀ i : Fin m, ∑ j : Fin n, X i j * Y i j
          ≤ Real.sqrt (∑ j : Fin n, X i j ^ 2) * Real.sqrt (∑ j : Fin n, Y i j ^ 2) := by
        intro i
        have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n))
          (fun j => X i j) (fun j => Y i j)
        simpa using h
      have h2 : ∑ i : Fin m, Real.sqrt (∑ j : Fin n, X i j ^ 2)
            * Real.sqrt (∑ j : Fin n, Y i j ^ 2)
          ≤ Real.sqrt (∑ i : Fin m, (Real.sqrt (∑ j : Fin n, X i j ^ 2)) ^ 2)
              * Real.sqrt (∑ i : Fin m, (Real.sqrt (∑ j : Fin n, Y i j ^ 2)) ^ 2) := by
        have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m))
          (fun i => Real.sqrt (∑ j : Fin n, X i j ^ 2))
          (fun i => Real.sqrt (∑ j : Fin n, Y i j ^ 2))
        simpa using h
      have h3 : (∑ i : Fin m, (Real.sqrt (∑ j : Fin n, X i j ^ 2)) ^ 2)
          = ∑ i : Fin m, ∑ j : Fin n, X i j ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      have h4 : (∑ i : Fin m, (Real.sqrt (∑ j : Fin n, Y i j ^ 2)) ^ 2)
          = ∑ i : Fin m, ∑ j : Fin n, Y i j ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      calc ∑ i, ∑ j, X i j * Y i j
          ≤ ∑ i, Real.sqrt (∑ j : Fin n, X i j ^ 2) * Real.sqrt (∑ j : Fin n, Y i j ^ 2) :=
            Finset.sum_le_sum (fun i _ => h1 i)
        _ ≤ Real.sqrt (∑ i : Fin m, (Real.sqrt (∑ j : Fin n, X i j ^ 2)) ^ 2)
              * Real.sqrt (∑ i : Fin m, (Real.sqrt (∑ j : Fin n, Y i j ^ 2)) ^ 2) := h2
        _ = Real.sqrt (∑ i : Fin m, ∑ j : Fin n, X i j ^ 2)
              * Real.sqrt (∑ i : Fin m, ∑ j : Fin n, Y i j ^ 2) := by rw [h3, h4]
        _ = Statlib.HighDim.MatrixAnalysis.frobeniusNorm X
              * Statlib.HighDim.MatrixAnalysis.frobeniusNorm Y := by
              rw [hfrob X, hfrob Y]
    haveI hP2 : IsProbabilityMeasure (μΩ.prod μΩ) := inferInstance
    have hOm'_meas : ∀ i j, Measurable fun q : Ωs × Ωs => Om q.1 i j :=
      fun i j => (hmask.1 i j).comp measurable_fst
    have hOm'_one : ∀ i j, (μΩ.prod μΩ) {q : Ωs × Ωs | Om q.1 i j = 1} = ENNReal.ofReal p := by
      intro i j
      have hset : {q : Ωs × Ωs | Om q.1 i j = 1} = {s : Ωs | Om s i j = 1} ×ˢ Set.univ := by
        ext q
        simp
      rw [hset]
      have h1 : (μΩ.prod μΩ) ({s : Ωs | Om s i j = 1} ×ˢ Set.univ)
          = μΩ {s : Ωs | Om s i j = 1} * μΩ (Set.univ : Set Ωs) := by
        simp
      rw [h1, measure_univ, mul_one]
      exact hmask.2.2.1 i j
    have hOm_ind : ∀ i j, (fun s : Ωs => Om s i j)
        = {s : Ωs | Om s i j = 1}.indicator (fun _ => (1 : ℝ)) := by
      intro i j
      funext s
      rcases hmask.2.1 s i j with h | h
      · simp [h]
      · simp [h]
    have hOm_mean : ∀ i j, ∫ s : Ωs, Om s i j ∂μΩ = p := by
      intro i j
      have hmeas : MeasurableSet {s : Ωs | Om s i j = 1} :=
        (hmask.1 i j) (measurableSet_singleton (1 : ℝ))
      rw [hOm_ind i j, MeasureTheory.integral_indicator hmeas, MeasureTheory.setIntegral_const]
      simp only [MeasureTheory.Measure.real, hmask.2.2.1 i j, ENNReal.toReal_ofReal hp0.le,
        smul_eq_mul, mul_one]
    have hOm'_mean : ∀ i j, ∫ q : Ωs × Ωs, Om q.1 i j ∂(μΩ.prod μΩ) = p := by
      intro i j
      have h := MeasureTheory.integral_prod_mul (μ := μΩ) (ν := μΩ)
        (f := fun s : Ωs => Om s i j) (g := fun _ : Ωs => (1 : ℝ))
      simp only [mul_one] at h
      have hone : ∫ _y : Ωs, (1 : ℝ) ∂μΩ = 1 := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real]
      rw [h, hOm_mean i j, hone, mul_one]
    have htriv : ∀ (Om' A B : Matrix (Fin m) (Fin n) ℝ),
        (∀ i j, Om' i j = 0 ∨ Om' i j = 1) → inTangentSpace U0 V0 B →
        |matInner (TOmega Om' U0 V0 A) B - p * matInner A B|
          ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
            * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B := by
      intro Om' A B h01 hB
      have hsum : p * matInner (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask p Om' A) B
          = ∑ i, ∑ j, (Om' i j - p) * (A i j * B i j) := by
        rw [htmask_eq]
        simp only [matInner]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        field_simp
      rw [htanId Om' A B hB, hsum]
      have h1 : |∑ i, ∑ j, (Om' i j - p) * (A i j * B i j)|
          ≤ ∑ i, ∑ j, |A i j * B i j| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => ?_))
        have hle : |Om' i j - p| ≤ 1 := by
          rcases h01 i j with h | h
          · rw [h, abs_le]
            constructor <;> linarith
          · rw [h, abs_le]
            constructor <;> linarith
        rw [abs_mul]
        calc |Om' i j - p| * |A i j * B i j| ≤ 1 * |A i j * B i j| :=
              mul_le_mul_of_nonneg_right hle (abs_nonneg _)
          _ = |A i j * B i j| := one_mul _
      have h2 : ∑ i, ∑ j, |A i j * B i j|
          ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
            * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B := by
        have h := hCS2 (fun i j => |A i j|) (fun i j => |B i j|)
        have e1 : (∑ i, ∑ j, |A i j * B i j|) = ∑ i, ∑ j, |A i j| * |B i j| := by
          simp [abs_mul]
        have e2 : Statlib.HighDim.MatrixAnalysis.frobeniusNorm (fun i j => |A i j|)
            = Statlib.HighDim.MatrixAnalysis.frobeniusNorm A := by
          rw [hfrob, hfrob]
          congr 1
          simp [sq_abs]
        have e3 : Statlib.HighDim.MatrixAnalysis.frobeniusNorm (fun i j => |B i j|)
            = Statlib.HighDim.MatrixAnalysis.frobeniusNorm B := by
          rw [hfrob, hfrob]
          congr 1
          simp [sq_abs]
        simpa [e1, e2, e3] using h
      exact le_trans h1 h2
    have hempty : ¬ (12 * r > n ∧ Cs * mu0 * (r : ℝ) * Real.log (m : ℝ) ≤ (n : ℝ) * p) := by
      rintro ⟨h12, hloc⟩
      have hr1 : 1 ≤ r := by omega
      have hmu : 1 ≤ mu0 := hmu0 hr1
      have hlogpos : 0 < Real.log (m : ℝ) := by
        apply Real.log_pos
        exact_mod_cast (by omega : 1 < m)
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (by omega : 0 < n)
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := by
        have h : 0 ≤ r := by omega
        exact_mod_cast h
      have hrlt : (n : ℝ) / 12 < (r : ℝ) := by
        have h : (n : ℝ) < 12 * (r : ℝ) := by exact_mod_cast h12
        linarith
      have hlog12 : (12 : ℝ) / Cs ≤ Real.log (m : ℝ) := (hm0G m hm).2.2
      have hlt : Cs * ((n : ℝ) / 12) * Real.log (m : ℝ)
          < Cs * mu0 * (r : ℝ) * Real.log (m : ℝ) := by
        have ha : Cs * ((n : ℝ) / 12) < Cs * (r : ℝ) := mul_lt_mul_of_pos_left hrlt hCs
        have hCsle : Cs ≤ Cs * mu0 := by
          simpa using mul_le_mul_of_nonneg_left hmu hCs.le
        have hb : Cs * (r : ℝ) ≤ Cs * mu0 * (r : ℝ) :=
          mul_le_mul_of_nonneg_right hCsle hr0
        have h1 : Cs * ((n : ℝ) / 12) < Cs * mu0 * (r : ℝ) := lt_of_lt_of_le ha hb
        exact mul_lt_mul_of_pos_right h1 hlogpos
      have h2 : (n : ℝ) ≤ Cs * ((n : ℝ) / 12) * Real.log (m : ℝ) := by
        have h3 : Cs * ((n : ℝ) / 12) * ((12 : ℝ) / Cs) = (n : ℝ) := by
          field_simp
        have hnn : 0 ≤ Cs * ((n : ℝ) / 12) :=
          mul_nonneg hCs.le (div_nonneg hnpos.le (by norm_num))
        have h4 : Cs * ((n : ℝ) / 12) * ((12 : ℝ) / Cs)
            ≤ Cs * ((n : ℝ) / 12) * Real.log (m : ℝ) :=
          mul_le_mul_of_nonneg_left hlog12 hnn
        linarith
      have hnlt : (n : ℝ) < (n : ℝ) * p := by linarith
      have hnp : (n : ℝ) * 1 < (n : ℝ) * p := by
        rw [mul_one]
        exact hnlt
      have hnle : (n : ℝ) * p ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hp1 hnpos.le
      exact absurd (lt_of_lt_of_le hnp hnle) (lt_irrefl ((n : ℝ) * 1))
    have hfrob_nonneg : ∀ A : Matrix (Fin m) (Fin n) ℝ,
        0 ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm A := by
      intro A
      rw [hfrob A]
      exact Real.sqrt_nonneg _
    have hGEspec : ∀ (Λ θ : ℝ) (Om' : Matrix (Fin m) (Fin n) ℝ),
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.GoodEvent
            p Λ θ Om' U0 V0 →
        Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p Om') ≤ Λ := by
      intro Λ θ Om' hGE
      have h := probe_ge_spec p Λ θ Om' U0 V0 hGE
      rwa [probe_spec, probe_wmask] at h
    have hGE_target : ∀ (Λ θ C : ℝ) (Om' : Matrix (Fin m) (Fin n) ℝ),
        Λ ≤ C * Real.sqrt ((m : ℝ) / p) →
        θ ≤ C * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) →
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.GoodEvent
            p Λ θ Om' U0 V0 →
        (Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p Om')
            ≤ C * Real.sqrt ((m : ℝ) / p) ∧
          ∀ A B : Matrix (Fin m) (Fin n) ℝ, inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
            |matInner (TOmega Om' U0 V0 A) B - p * matInner A B|
              ≤ C * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                  * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                  * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B) := by
      intro Λ θ C Om' hΛ hθ hGE
      refine ⟨le_trans (hGEspec Λ θ Om' hGE) hΛ, ?_⟩
      intro A B hA hB
      have h1 := hGEtan Λ θ Om' hGE A B hA hB
      calc |matInner (TOmega Om' U0 V0 A) B - p * matInner A B|
          ≤ θ * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
              * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B := h1
        _ ≤ (C * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
              * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
              * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hθ (hfrob_nonneg A)) (hfrob_nonneg B)
    have hCL_le : CL * Real.sqrt ((m : ℝ) / p)
        ≤ (CL + Cth + 2 * Real.sqrt Cs + 1) * Real.sqrt ((m : ℝ) / p) := by
      have hs : 0 ≤ Real.sqrt Cs := Real.sqrt_nonneg Cs
      exact mul_le_mul_of_nonneg_right (by linarith only [hCth, hs]) (Real.sqrt_nonneg _)
    have hCth_le : Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
        ≤ (CL + Cth + 2 * Real.sqrt Cs + 1)
            * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) := by
      have hs : 0 ≤ Real.sqrt Cs := Real.sqrt_nonneg Cs
      exact mul_le_mul_of_nonneg_right (by linarith only [hCL, hs]) (Real.sqrt_nonneg _)
    have hEv : ∀ (Om' : Matrix (Fin m) (Fin n) ℝ),
        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.GoodEvent p
            (CL * Real.sqrt ((m : ℝ) / p))
            (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))) Om' U0 V0 →
        (Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p Om')
            ≤ (CL + Cth + 2 * Real.sqrt Cs + 1) * Real.sqrt ((m : ℝ) / p) ∧
          ∀ A B : Matrix (Fin m) (Fin n) ℝ, inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
            |matInner (TOmega Om' U0 V0 A) B - p * matInner A B|
              ≤ (CL + Cth + 2 * Real.sqrt Cs + 1)
                  * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                  * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                  * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B) :=
      fun Om' h => hGE_target (CL * Real.sqrt ((m : ℝ) / p))
        (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
        (CL + Cth + 2 * Real.sqrt Cs + 1) Om' hCL_le hCth_le h
    have hx4 : 0 ≤ cD * ((n : ℝ) ^ 4)⁻¹ := by
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      exact mul_nonneg hcD.le (inv_nonneg.mpr (pow_nonneg hn0.le 4))
    have hconv : ENNReal.ofReal (1 - cD * ((n : ℝ) ^ 4)⁻¹)
        ≤ 1 - ENNReal.ofReal (cD / ((n : ℝ) ^ 4)) := by
      rw [div_eq_mul_inv, ENNReal.ofReal_sub _ hx4, ENNReal.ofReal_one]

    have hOm'_01 : ∀ i j, ∀ᵐ q ∂(μΩ.prod μΩ),
        Om q.1 i j = 0 ∨ Om q.1 i j = 1 :=
      fun i j => Filter.Eventually.of_forall (fun q => hmask.2.1 q.1 i j)
    have hOm'_int : ∀ i j, Integrable (fun q : Ωs × Ωs => Om q.1 i j) (μΩ.prod μΩ) := by
      intro i j
      refine MeasureTheory.Integrable.of_bound (hOm'_meas i j).aestronglyMeasurable 1 ?_
      filter_upwards with q
      rcases hmask.2.1 q.1 i j with h | h <;> simp [h]
    have hOm'_indep :
        iIndepFun (fun (x : Fin m × Fin n) => fun q : Ωs × Ωs => Om q.1 x.1 x.2)
          (μΩ.prod μΩ) := by
      rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
      intro S sets hsets
      have hmask_i : μΩ (⋂ x ∈ S, (fun s : Ωs => Om s x.1 x.2) ⁻¹' sets x)
          = ∏ x ∈ S, μΩ ((fun s : Ωs => Om s x.1 x.2) ⁻¹' sets x) :=
        (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul).mp hmask.2.2.2
          (sets := sets) S hsets
      have hset : (⋂ x ∈ S, (fun q : Ωs × Ωs => Om q.1 x.1 x.2) ⁻¹' sets x)
          = (⋂ x ∈ S, (fun s : Ωs => Om s x.1 x.2) ⁻¹' sets x) ×ˢ Set.univ := by
        ext q
        simp [Set.mem_iInter, Set.mem_preimage]
      have hf : ∀ x ∈ S, (μΩ.prod μΩ) ((fun q : Ωs × Ωs => Om q.1 x.1 x.2) ⁻¹' sets x)
          = μΩ ((fun s : Ωs => Om s x.1 x.2) ⁻¹' sets x) := by
        intro x _
        have hx' : (fun q : Ωs × Ωs => Om q.1 x.1 x.2) ⁻¹' sets x
            = ((fun s : Ωs => Om s x.1 x.2) ⁻¹' sets x) ×ˢ Set.univ := by
          ext q
          simp [Set.mem_preimage]
        rw [hx', MeasureTheory.Measure.prod_prod, measure_univ, mul_one]
      rw [hset, MeasureTheory.Measure.prod_prod, measure_univ, mul_one, hmask_i]
      exact (Finset.prod_congr rfl hf).symm
    set E : Set Ωs := {ω | _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.GoodEvent p
        (CL * Real.sqrt ((m : ℝ) / p))
        (Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))) (Om ω) U0 V0} with hE
    have hProdmask : (μΩ.prod μΩ) (E ×ˢ Set.univ) = μΩ E := by
      rw [MeasureTheory.Measure.prod_prod, measure_univ, mul_one]
    have hEmeasure : 1 - ENNReal.ofReal (cD / ((n : ℝ) ^ 4)) ≤
        μΩ {ω | Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om ω))
              ≤ (CL + Cth + 2 * Real.sqrt Cs + 1) * Real.sqrt ((m : ℝ) / p) ∧
            ∀ A B : Matrix (Fin m) (Fin n) ℝ,
              inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
                |matInner (TOmega (Om ω) U0 V0 A) B - p * matInner A B|
                  ≤ (CL + Cth + 2 * Real.sqrt Cs + 1)
                      * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B} := by
      by_cases hp_lt : p < 1
      · have hp_sq_pos : 0 < p - p ^ 2 := by
          have h : 0 < p * (1 - p) := mul_pos hp0 (by linarith only [hp_lt])
          nlinarith only [h]
        have hone1 : ∫ _x : Ωs, (1 : ℝ) ∂μΩ = 1 := by
          rw [MeasureTheory.integral_const]
          simp [MeasureTheory.Measure.real]
        have hconstp : ∫ _q : Ωs × Ωs, p ∂(μΩ.prod μΩ) = p := by
          rw [MeasureTheory.integral_const]
          simp [MeasureTheory.Measure.real]
        have hsnd_mean : ∀ i j, ∫ q : Ωs × Ωs, Om q.2 i j ∂(μΩ.prod μΩ) = p := by
          intro i j
          have h := MeasureTheory.integral_prod_mul (μ := μΩ) (ν := μΩ)
            (f := fun _ : Ωs => (1 : ℝ)) (g := fun s : Ωs => Om s i j)
          simpa [hone1, hOm_mean i j] using h
        have hsnd_meas : ∀ i j, Measurable (fun q : Ωs × Ωs => Om q.2 i j) := by
          intro i j
          exact (hmask.1 i j).comp measurable_snd
        have hsnd_int : ∀ i j, Integrable (fun q : Ωs × Ωs => Om q.2 i j) (μΩ.prod μΩ) := by
          intro i j
          refine MeasureTheory.Integrable.of_bound (hsnd_meas i j).aestronglyMeasurable 1 ?_
          filter_upwards with q
          rcases hmask.2.1 q.2 i j with h | h <;> simp [h]
        have hH_meas : ∀ i j, Measurable (fun q : Ωs × Ωs => Om q.2 i j - p) := by
          intro i j
          exact (hsnd_meas i j).sub measurable_const
        have hH_int : ∀ i j, Integrable (fun q : Ωs × Ωs => Om q.2 i j - p) (μΩ.prod μΩ) := by
          intro i j
          exact (hsnd_int i j).sub (integrable_const p)
        have hH_mean : ∀ i j, ∫ q : Ωs × Ωs, (Om q.2 i j - p) ∂(μΩ.prod μΩ) = 0 := by
          intro i j
          rw [MeasureTheory.integral_sub (hsnd_int i j) (integrable_const p), hsnd_mean i j,
            hconstp]
          ring
        have hH_var : ∀ i j, ∫ q : Ωs × Ωs, (Om q.2 i j - p) ^ 2 ∂(μΩ.prod μΩ)
            = Real.sqrt (p - p ^ 2) ^ 2 := by
          intro i j
          rw [Real.sq_sqrt hp_sq_pos.le]
          have h1 : Integrable (fun q : Ωs × Ωs => (1 - 2 * p) * Om q.2 i j) (μΩ.prod μΩ) :=
            (hsnd_int i j).const_mul (1 - 2 * p)
          have h2 : Integrable (fun _ : Ωs × Ωs => p ^ 2) (μΩ.prod μΩ) := integrable_const _
          have hconst : ∫ _q : Ωs × Ωs, p ^ 2 ∂(μΩ.prod μΩ) = p ^ 2 := by
            rw [MeasureTheory.integral_const]
            simp [MeasureTheory.Measure.real]
          have hpt : ∀ q : Ωs × Ωs,
              (Om q.2 i j - p) ^ 2 = (1 - 2 * p) * Om q.2 i j + p ^ 2 := by
            intro q
            rcases hmask.2.1 q.2 i j with h | h <;> rw [h] <;> ring
          calc ∫ q : Ωs × Ωs, (Om q.2 i j - p) ^ 2 ∂(μΩ.prod μΩ)
              = ∫ q : Ωs × Ωs, ((1 - 2 * p) * Om q.2 i j + p ^ 2) ∂(μΩ.prod μΩ) := by
                simp only [hpt]
            _ = (∫ q : Ωs × Ωs, (1 - 2 * p) * Om q.2 i j ∂(μΩ.prod μΩ)) + p ^ 2 := by
                rw [MeasureTheory.integral_add h1 h2, hconst]
            _ = (1 - 2 * p) * (∫ q : Ωs × Ωs, Om q.2 i j ∂(μΩ.prod μΩ)) + p ^ 2 := by
                rw [MeasureTheory.integral_const_mul]
            _ = p - p ^ 2 := by
                rw [hsnd_mean i j]
                ring
        have hH_tail : ∃ KH, 0 < KH ∧ ∀ (i j) (t : ℝ), 0 ≤ t →
            (μΩ.prod μΩ) {q : Ωs × Ωs | t ≤ |Om q.2 i j - p|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t / KH))) := by
          refine ⟨2, by norm_num, ?_⟩
          intro i j t ht
          have hbound : ∀ q : Ωs × Ωs, |Om q.2 i j - p| ≤ 1 := by
            intro q
            rcases hmask.2.1 q.2 i j with h | h
            · rw [h, abs_le]
              constructor <;> linarith
            · rw [h, abs_le]
              constructor <;> linarith
          by_cases ht1 : t ≤ 1
          · have hle1 : (μΩ.prod μΩ) {q : Ωs × Ωs | t ≤ |Om q.2 i j - p|} ≤ 1 := by
              calc (μΩ.prod μΩ) {q : Ωs × Ωs | t ≤ |Om q.2 i j - p|}
                  ≤ (μΩ.prod μΩ) Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            refine le_trans hle1 ?_
            rw [← ENNReal.ofReal_one]
            refine ENNReal.ofReal_le_ofReal ?_
            have hexp : -(t / 2) + 1 ≤ Real.exp (-(t / 2)) := Real.add_one_le_exp _
            linarith
          · push_neg at ht1
            have hno : {q : Ωs × Ωs | t ≤ |Om q.2 i j - p|} = ∅ := by
              ext q
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
              linarith [hbound q]
            rw [hno, measure_empty]
            exact zero_le _
        have hOm2_indep :
            iIndepFun (fun (x : Fin m × Fin n) => fun q : Ωs × Ωs => Om q.2 x.1 x.2)
              (μΩ.prod μΩ) := by
          rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
          intro S sets hsets
          have hmask_i : μΩ (⋂ x ∈ S, (fun s : Ωs => Om s x.1 x.2) ⁻¹' sets x)
              = ∏ x ∈ S, μΩ ((fun s : Ωs => Om s x.1 x.2) ⁻¹' sets x) :=
            (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul).mp hmask.2.2.2
              (sets := sets) S hsets
          have hset : (⋂ x ∈ S, (fun q : Ωs × Ωs => Om q.2 x.1 x.2) ⁻¹' sets x)
              = Set.univ ×ˢ (⋂ x ∈ S, (fun s : Ωs => Om s x.1 x.2) ⁻¹' sets x) := by
            ext q
            simp [Set.mem_iInter, Set.mem_preimage]
          have hf : ∀ x ∈ S, (μΩ.prod μΩ) ((fun q : Ωs × Ωs => Om q.2 x.1 x.2) ⁻¹' sets x)
              = μΩ ((fun s : Ωs => Om s x.1 x.2) ⁻¹' sets x) := by
            intro x _
            have hx' : (fun q : Ωs × Ωs => Om q.2 x.1 x.2) ⁻¹' sets x
                = Set.univ ×ˢ ((fun s : Ωs => Om s x.1 x.2) ⁻¹' sets x) := by
              ext q
              simp [Set.mem_preimage]
            rw [hx', MeasureTheory.Measure.prod_prod, measure_univ, one_mul]
          rw [hset, MeasureTheory.Measure.prod_prod, measure_univ, one_mul, hmask_i]
          exact (Finset.prod_congr rfl hf).symm
        have hH_indep :
            iIndepFun (fun (x : Fin m × Fin n) => fun q : Ωs × Ωs => Om q.2 x.1 x.2 - p)
              (μΩ.prod μΩ) := by
          rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
          intro S sets hsets
          have hsets' : ∀ x ∈ S, MeasurableSet {a : ℝ | a - p ∈ sets x} :=
            fun x hx => (measurable_id.sub measurable_const) (hsets x hx)
          have hmain := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul).mp hOm2_indep
            (sets := fun x => {a : ℝ | a - p ∈ sets x}) S hsets'
          exact hmain
        have hOmH_indep :
            IndepFun (fun (q : Ωs × Ωs) (ij : Fin m × Fin n) => Om q.1 ij.1 ij.2)
              (fun (q : Ωs × Ωs) (ij : Fin m × Fin n) => Om q.2 ij.1 ij.2 - p)
              (μΩ.prod μΩ) := by
          rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
          intro s t hs ht
          have h1 : (fun (q : Ωs × Ωs) (ij : Fin m × Fin n) => Om q.1 ij.1 ij.2) ⁻¹' s
              = ((fun ω : Ωs => fun ij : Fin m × Fin n => Om ω ij.1 ij.2) ⁻¹' s)
                ×ˢ Set.univ := by
            ext q
            simp [Set.mem_preimage]
          have h2 : (fun (q : Ωs × Ωs) (ij : Fin m × Fin n) => Om q.2 ij.1 ij.2 - p) ⁻¹' t
              = Set.univ
                ×ˢ ((fun ω : Ωs => fun ij : Fin m × Fin n => Om ω ij.1 ij.2 - p) ⁻¹' t) := by
            ext q
            simp [Set.mem_preimage]
          have h3 : ((fun ω : Ωs => fun ij : Fin m × Fin n => Om ω ij.1 ij.2) ⁻¹' s) ×ˢ Set.univ
              ∩ (Set.univ
                ×ˢ ((fun ω : Ωs => fun ij : Fin m × Fin n => Om ω ij.1 ij.2 - p) ⁻¹' t))
              = ((fun ω : Ωs => fun ij : Fin m × Fin n => Om ω ij.1 ij.2) ⁻¹' s)
                ×ˢ ((fun ω : Ωs => fun ij : Fin m × Fin n => Om ω ij.1 ij.2 - p) ⁻¹' t) := by
            ext q
            simp [Set.mem_prod]
          rw [h1, h2, h3]
          simp only [MeasureTheory.Measure.prod_prod, measure_univ, mul_one, one_mul]
        by_cases hloc : Cs * mu0 * (r : ℝ) * Real.log (m : ℝ) ≤ (n : ℝ) * p
        · have hmpos : 0 < m := by
            have h2 : 2 ≤ m := (hm0G m hm).2.1
            omega
          have hnpos : 0 < n := by omega
          have hN0 : N0 ≤ m := (hm0G m hm).1
          have h12r : 12 * r ≤ n := by
            by_contra hcon
            exact hempty ⟨by omega, hloc⟩
          have hsigma_pos : 0 < Real.sqrt (p - p ^ 2) := Real.sqrt_pos.mpr hp_sq_pos
          have hDapp := hD m n r p mu0 (Real.sqrt (p - p ^ 2)) hmpos hnpos hN0 hnm hp0.le hp1
            hrho_lo hrho_hi hsigma_pos h12r hmp hloc M0 U0 V0 d0 hrank hU0 hV0 hM0pos hM0eq
            hrowU' hrowV' (Ωm := Ωs × Ωs) (μΩ.prod μΩ)
            (fun i j q => Om q.2 i j - p) (fun i j q => Om q.1 i j)
            hH_meas hH_int hH_indep hH_mean hH_var hH_tail
            hOm'_meas hOm'_indep hOm'_01 hOm'_one hOm'_int hOm'_mean hOmH_indep
          have hsubset : {q : Ωs × Ωs |
              _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.specNorm
                  (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Wmask
                    p (fun i j => Om q.1 i j))
                  ≤ CL * Real.sqrt ((m : ℝ) / p) ∧
                (∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
                  _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.specNorm
                      (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask
                        p (fun i j => Om q.1 i j) (L * R.transpose))
                    ≤ CL * Real.sqrt ((m : ℝ) / p)
                        * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rowNorm L
                        * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rowNorm R) ∧
                  (∀ A B : Matrix (Fin m) (Fin n) ℝ,
                    _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.MemTangentRect U0 V0 A →
                      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.MemTangentRect U0 V0 B →
                        |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobInner
                            (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask
                              p (fun i j => Om q.1 i j) A) B|
                          ≤ Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                              * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobNorm A
                              * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobNorm B) ∧
                    ∀ (k l : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
                      (C1 : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
                      |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobInner
                          (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask
                            p (fun i j => Om q.1 i j) (A * B.transpose)) (C1 * D.transpose)|
                        ≤ CL * Real.sqrt ((m : ℝ) / p)
                            * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.bFactor A C1
                            * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.bFactor B D}
              ⊆ E ×ˢ Set.univ := by
            intro q hq
            refine ⟨?_, Set.mem_univ _⟩
            exact ⟨hq.1, hq.2.2.1, hq.2.2.2, hq.2.1⟩
          have hDapp' : 1 - ENNReal.ofReal (cD / ((n : ℝ) ^ 4))
              ≤ (μΩ.prod μΩ) (E ×ˢ Set.univ) :=
            le_trans hDapp (measure_mono hsubset)
          rw [hProdmask] at hDapp'
          exact le_trans hDapp' (measure_mono (fun ω hω => hEv (Om ω) hω))
        · have hnp_pos : (0 : ℝ) < (n : ℝ) * p := by
            have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
            exact mul_pos hn0 hp0
          have hshape : Cs * (mu0 * (r : ℝ) * Real.log (m : ℝ))
              = Cs * mu0 * (r : ℝ) * Real.log (m : ℝ) := by ring
          have harg : Cs * (mu0 * (r : ℝ) * Real.log (m : ℝ)) / ((n : ℝ) * p)
              = Cs * (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) := by ring
          have hA : (1 : ℝ) ≤ Cs * (mu0 * (r : ℝ) * Real.log (m : ℝ)) / ((n : ℝ) * p) := by
            rw [one_le_div hnp_pos, hshape]
            exact (lt_of_not_ge hloc).le
          have hbase : (1 : ℝ) ≤ Real.sqrt Cs
              * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) := by
            have e : Real.sqrt Cs
                * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                = Real.sqrt (Cs * (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))) := by
              rw [Real.sqrt_mul hCs.le]
            rw [e, Real.one_le_sqrt, ← harg]
            exact hA
          have hsqrtC_le : Real.sqrt Cs ≤ CL + Cth + 2 * Real.sqrt Cs + 1 := by
            have h := Real.sqrt_nonneg Cs
            linarith only [h, hCL, hCth]
          have hkeyC : (1 : ℝ) ≤ (CL + Cth + 2 * Real.sqrt Cs + 1)
              * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) :=
            le_trans hbase (mul_le_mul_of_nonneg_right hsqrtC_le (Real.sqrt_nonneg _))
          have htan_all : ∀ (Om' : Matrix (Fin m) (Fin n) ℝ),
              (∀ i j, Om' i j = 0 ∨ Om' i j = 1) →
              ∀ A B : Matrix (Fin m) (Fin n) ℝ, inTangentSpace U0 V0 A →
                inTangentSpace U0 V0 B →
                |matInner (TOmega Om' U0 V0 A) B - p * matInner A B|
                  ≤ (CL + Cth + 2 * Real.sqrt Cs + 1)
                      * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B := by
            intro Om' h01 A B hA' hB'
            have h1 := htriv Om' A B h01 hB'
            have h2 : Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B
                ≤ ((CL + Cth + 2 * Real.sqrt Cs + 1)
                    * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
                  * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                  * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B := by
              have h3 : (1 : ℝ) * (Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                    * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B)
                  ≤ ((CL + Cth + 2 * Real.sqrt Cs + 1)
                      * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
                    * (Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B) :=
                mul_le_mul_of_nonneg_right hkeyC
                  (mul_nonneg (hfrob_nonneg A) (hfrob_nonneg B))
              calc Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                    * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B
                  = (1 : ℝ) * (Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B) := by rw [one_mul]
                _ ≤ ((CL + Cth + 2 * Real.sqrt Cs + 1)
                      * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
                    * (Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                      * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B) := h3
                _ = ((CL + Cth + 2 * Real.sqrt Cs + 1)
                      * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
                    * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                    * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B := by ring
            exact le_trans h1 h2
          have hspec : 1 - ENNReal.ofReal (cD / ((n : ℝ) ^ 4))
              ≤ μΩ {ω | Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om ω))
                    ≤ CL * Real.sqrt ((m : ℝ) / p)} := by
            have hmpos : 0 < m := by
              have h2 : 2 ≤ m := (hm0G m hm).2.1
              omega
            have hnpos : 0 < n := by omega
            have hN0 : N0 ≤ m := (hm0G m hm).1
            haveI hnem : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
            haveI hnen : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
            have hsupU : rowSupNorm (0 : Matrix (Fin m) (Fin 0) ℝ) ≤ 0 := by
              unfold rowSupNorm
              exact ciSup_le (fun i => by simp)
            have hsupV : rowSupNorm (0 : Matrix (Fin n) (Fin 0) ℝ) ≤ 0 := by
              unfold rowSupNorm
              exact ciSup_le (fun i => by simp)
            have hrowU0 : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rowNorm
                (0 : Matrix (Fin m) (Fin 0) ℝ) ≤ Real.sqrt (0 * ((0 : ℕ) : ℝ) / (m : ℝ)) := by
              rw [probe_row]
              refine le_trans hsupU ?_
              simp
            have hrowV0 : _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rowNorm
                (0 : Matrix (Fin n) (Fin 0) ℝ) ≤ Real.sqrt (0 * ((0 : ℕ) : ℝ) / (n : ℝ)) := by
              rw [probe_row]
              refine le_trans hsupV ?_
              simp
            have hD0 := hD m n 0 p 0 (Real.sqrt (p - p ^ 2)) hmpos hnpos hN0 hnm hp0.le hp1
              hrho_lo hrho_hi (Real.sqrt_pos.mpr hp_sq_pos) (by omega : 12 * 0 ≤ n) hmp
              (by
                have h1 : (0 : ℝ) ≤ (n : ℝ) * p := hnp_pos.le
                have h2 : Cs * (0 : ℝ) * ((0 : ℕ) : ℝ) * Real.log (m : ℝ) = 0 := by simp
                rw [h2]
                exact h1)
              (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin m) (Fin 0) ℝ)
              (0 : Matrix (Fin n) (Fin 0) ℝ) (0 : Fin 0 → ℝ) Matrix.rank_zero
              (by ext i j; exact i.elim0) (by ext i j; exact i.elim0) (fun i => i.elim0)
              (by ext i j; simp) hrowU0 hrowV0
              (Ωm := Ωs × Ωs) (μΩ.prod μΩ)
              (fun i j q => Om q.2 i j - p) (fun i j q => Om q.1 i j)
              hH_meas hH_int hH_indep hH_mean hH_var hH_tail
              hOm'_meas hOm'_indep hOm'_01 hOm'_one hOm'_int hOm'_mean hOmH_indep
            have hsub0 : {q : Ωs × Ωs |
                _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.specNorm
                    (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Wmask
                      p (fun i j => Om q.1 i j))
                    ≤ CL * Real.sqrt ((m : ℝ) / p) ∧
                  (∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
                    _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.specNorm
                        (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask
                          p (fun i j => Om q.1 i j) (L * R.transpose))
                      ≤ CL * Real.sqrt ((m : ℝ) / p)
                          * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rowNorm L
                          * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.rowNorm R) ∧
                    (∀ A B : Matrix (Fin m) (Fin n) ℝ,
                      _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.MemTangentRect
                          (0 : Matrix (Fin m) (Fin 0) ℝ) (0 : Matrix (Fin n) (Fin 0) ℝ) A →
                        _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.MemTangentRect
                          (0 : Matrix (Fin m) (Fin 0) ℝ) (0 : Matrix (Fin n) (Fin 0) ℝ) B →
                          |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobInner
                              (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask
                                p (fun i j => Om q.1 i j) A) B|
                            ≤ Cth * Real.sqrt (0 * ((0 : ℕ) : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                                * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobNorm A
                                * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobNorm B) ∧
                      ∀ (k l : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
                        (C1 : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
                        |_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.frobInner
                            (_root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.Tmask
                              p (fun i j => Om q.1 i j) (A * B.transpose)) (C1 * D.transpose)|
                          ≤ CL * Real.sqrt ((m : ℝ) / p)
                              * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.bFactor A C1
                              * _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.bFactor B D}
                ⊆ {q : Ωs × Ωs | Statlib.HighDim.MatrixAnalysis.opNorm
                      (centeredMaskOp p (fun i j => Om q.1 i j))
                    ≤ CL * Real.sqrt ((m : ℝ) / p)} := by
              intro q hq
              have h := hq.1
              rwa [probe_spec, probe_wmask] at h
            have hprod0 : (μΩ.prod μΩ) {q : Ωs × Ωs | Statlib.HighDim.MatrixAnalysis.opNorm
                  (centeredMaskOp p (fun i j => Om q.1 i j))
                  ≤ CL * Real.sqrt ((m : ℝ) / p)}
                = μΩ {ω | Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om ω))
                      ≤ CL * Real.sqrt ((m : ℝ) / p)} := by
              have hset : {q : Ωs × Ωs | Statlib.HighDim.MatrixAnalysis.opNorm
                    (centeredMaskOp p (fun i j => Om q.1 i j))
                    ≤ CL * Real.sqrt ((m : ℝ) / p)}
                  = {ω : Ωs | Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om ω))
                        ≤ CL * Real.sqrt ((m : ℝ) / p)} ×ˢ Set.univ := by
                ext q
                simp
              rw [hset, MeasureTheory.Measure.prod_prod, measure_univ, mul_one]
            exact le_trans hD0 (le_trans (measure_mono hsub0) (le_of_eq hprod0))
          have hsub : {ω | Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om ω))
                  ≤ CL * Real.sqrt ((m : ℝ) / p)}
              ⊆ {ω | Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om ω))
                    ≤ (CL + Cth + 2 * Real.sqrt Cs + 1) * Real.sqrt ((m : ℝ) / p) ∧
                  ∀ A B : Matrix (Fin m) (Fin n) ℝ,
                    inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
                      |matInner (TOmega (Om ω) U0 V0 A) B - p * matInner A B|
                        ≤ (CL + Cth + 2 * Real.sqrt Cs + 1)
                            * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                            * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                            * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B} := by
            intro ω hω
            exact ⟨le_trans hω hCL_le,
              fun A B hA' hB' => htan_all (Om ω) (fun i j => hmask.2.1 ω i j) A B hA' hB'⟩
          exact le_trans hspec (measure_mono hsub)
      · have hp_eq : p = 1 := le_antisymm hp1 (le_of_not_gt hp_lt)
        have hC0 : (0 : ℝ) ≤ CL + Cth + 2 * Real.sqrt Cs + 1 := by
          have h := Real.sqrt_nonneg Cs
          linarith only [hCL, hCth, h]
        have hzero : ∀ (i : Fin m) (j : Fin n), μΩ {ω : Ωs | ¬ (Om ω i j = 1)} = 0 := by
          intro i j
          have hmeas : MeasurableSet {ω : Ωs | Om ω i j = 1} :=
            (hmask.1 i j) (measurableSet_singleton (1 : ℝ))
          have hms : μΩ {ω : Ωs | Om ω i j = 1} = 1 := by
            rw [hmask.2.2.1 i j, hp_eq, ENNReal.ofReal_one]
          have hne : μΩ {ω : Ωs | Om ω i j = 1} ≠ ⊤ := by
            rw [hms]
            exact ENNReal.one_ne_top
          have hc : μΩ ({ω : Ωs | Om ω i j = 1}ᶜ) = 0 := by
            rw [MeasureTheory.measure_compl hmeas hne, hms, measure_univ, tsub_self]
          exact hc
        have hop0 : Statlib.HighDim.MatrixAnalysis.opNorm (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
          unfold Statlib.HighDim.MatrixAnalysis.opNorm
          simp
        have hspec1 : ∀ (ω : Ωs), (∀ (i : Fin m) (j : Fin n), Om ω i j = 1) →
            Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om ω))
              ≤ (CL + Cth + 2 * Real.sqrt Cs + 1) * Real.sqrt ((m : ℝ) / p) := by
          intro ω hω
          have hmat : (Om ω) = fun _ _ => (1 : ℝ) := by
            ext i j
            exact hω i j
          have hc0 : centeredMaskOp p (Om ω) = 0 := by
            rw [hmat, hp_eq]
            ext i j
            simp [centeredMaskOp]
          rw [hc0, hop0]
          exact mul_nonneg hC0 (Real.sqrt_nonneg _)
        have htan1 : ∀ (ω : Ωs), (∀ (i : Fin m) (j : Fin n), Om ω i j = 1) →
            ∀ A B : Matrix (Fin m) (Fin n) ℝ, inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
              |matInner (TOmega (Om ω) U0 V0 A) B - p * matInner A B|
                ≤ (CL + Cth + 2 * Real.sqrt Cs + 1)
                    * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                    * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                    * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B := by
          intro ω hω A B hA hB
          have hmat : (Om ω) = fun _ _ => (1 : ℝ) := by
            ext i j
            exact hω i j
          have hmask1 : maskOp (Om ω) A = A := by
            rw [hmat]
            ext i j
            simp [maskOp]
          have hproj1 : projTangent U0 V0 A = A := by
            unfold projTangent
            rw [hA]
            simp
          have hTO : TOmega (Om ω) U0 V0 A = A := by
            unfold TOmega
            rw [hmask1, hproj1]
          rw [hTO, hp_eq]
          have hz : matInner A B - (1 : ℝ) * matInner A B = 0 := by ring
          rw [hz, abs_zero]
          exact mul_nonneg
            (mul_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _)) (hfrob_nonneg A))
            (hfrob_nonneg B)
        have hnull : μΩ ({ω : Ωs | ∀ (i : Fin m) (j : Fin n), Om ω i j = 1}ᶜ) = 0 := by
          have hset : ({ω : Ωs | ∀ (i : Fin m) (j : Fin n), Om ω i j = 1})ᶜ
              = ⋃ (i : Fin m) (j : Fin n), {ω : Ωs | ¬ (Om ω i j = 1)} := by
            ext ω
            simp
          rw [hset]
          exact MeasureTheory.measure_iUnion_null
            (fun i => MeasureTheory.measure_iUnion_null (fun j => hzero i j))
        have hone : (1 : ENNReal) ≤ μΩ {ω : Ωs | ∀ (i : Fin m) (j : Fin n), Om ω i j = 1} := by
          have hsetT : {ω : Ωs | ∀ (i : Fin m) (j : Fin n), Om ω i j = 1}
              = ⋂ (i : Fin m) (j : Fin n), {ω : Ωs | Om ω i j = 1} := by
            ext ω
            simp
          have hTmeas : MeasurableSet {ω : Ωs | ∀ (i : Fin m) (j : Fin n), Om ω i j = 1} := by
            rw [hsetT]
            exact MeasurableSet.iInter (fun i => MeasurableSet.iInter
              (fun j => show MeasurableSet {ω : Ωs | Om ω i j = 1} from
                (hmask.1 i j) (measurableSet_singleton (1 : ℝ))))
          have hne : μΩ {ω : Ωs | ∀ (i : Fin m) (j : Fin n), Om ω i j = 1} ≠ ⊤ :=
            measure_ne_top _ _
          have hc := MeasureTheory.measure_compl hTmeas hne
          rw [hnull, measure_univ] at hc
          exact tsub_eq_zero_iff_le.mp hc.symm
        exact le_trans (le_trans tsub_le_self hone)
          (measure_mono (fun ω hω => ⟨hspec1 ω hω, fun A B hA hB => htan1 ω hω A B hA hB⟩))
    exact le_trans hconv hEmeasure

end Statlib.Imported

end


#print axioms ResidualLoss20261106.Statlib.Imported.statopia_math_node_1222515461_d927f311

