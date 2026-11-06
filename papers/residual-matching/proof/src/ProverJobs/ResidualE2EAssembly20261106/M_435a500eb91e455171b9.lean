import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48
import ProverJobs.ResidualE2EAssembly20261106.M_9b31866eda2beab96fcd

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported
open scoped Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3691428624_182dbd31 : ∀ (m n r : ℕ) (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (sig0 : Fin r → ℝ) (mu0 mu1 CM : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (hm : 0 < m) (hn : 0 < n) (hr : 1 ≤ r) (hCM : 1 ≤ CM)
    (hmu : mu0 ≤ mu1) (hmu0 : 0 ≤ mu0)
    (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
    (hanti : Antitone sig0) (hsmin : 0 < SMin sig0)
    (hlevU : twoInfNorm U0 ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)))
    (hlevV : twoInfNorm V0 ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)))
    (hM : InLowRankClass r mu1 M) (hspec : spectralNorm M ≤ CM * SMax sig0),
    ∃ (X0 X : Matrix (Fin m) (Fin r) ℝ) (Y0 Y : Matrix (Fin n) (Fin r) ℝ),
      X0 = U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)) ∧
      Y0 = V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)) ∧
      X0 * Matrix.transpose Y0 = U0 * Matrix.diagonal sig0 * Matrix.transpose V0 ∧
      X * Matrix.transpose Y = M ∧
      spectralNorm X0 ≤ Real.sqrt (SMax sig0) ∧
      spectralNorm Y0 ≤ Real.sqrt (SMax sig0) ∧
      twoInfNorm X0 ≤
        Real.sqrt (SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) ∧
      twoInfNorm Y0 ≤
        Real.sqrt (SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) ∧
      twoInfNorm X ≤
        Real.sqrt (CM * SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) ∧
      twoInfNorm Y ≤
        Real.sqrt (CM * SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) ∧
      frobSq (X - X0) + frobSq (Y - Y0) ≤
        2 * frobSq (X * Matrix.transpose Y - X0 * Matrix.transpose Y0) /
          ((Real.sqrt 2 - 1) * SMin sig0) := by
  /- @proof-region region.target-node.session.bf74740d2e4b28bc begin -/
  intro m n r U0 V0 sig0 mu0 mu1 CM M hm hn hr hCM hmu hmu0 hU0 hV0 hanti hsmin hlevU hlevV hM hspec
  have hbar : mu0 ≤ barMuOf mu0 mu1 := le_max_left mu0 mu1
  have hbar0 : 0 ≤ barMuOf mu0 mu1 := le_trans hmu0 hbar
  have hsigpos : ∀ t : Fin r, 0 < sig0 t := by
    intro t
    haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
    have hbdd : BddBelow (Set.range sig0) := (Set.finite_range sig0).bddBelow
    have h1 : SMin sig0 ≤ sig0 t := ciInf_le hbdd t
    linarith
  have hsig0 : ∀ t : Fin r, 0 ≤ sig0 t := fun t => le_of_lt (hsigpos t)
  let X0 : Matrix (Fin m) (Fin r) ℝ := U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t))
  let Y0 : Matrix (Fin n) (Fin r) ℝ := V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t))
  have hdT : Matrix.transpose (Matrix.diagonal (fun t : Fin r => Real.sqrt (sig0 t)))
      = Matrix.diagonal (fun t : Fin r => Real.sqrt (sig0 t)) := by
    ext i j
    by_cases h : i = j
    · rw [h]
      simp [Matrix.diagonal_apply, Matrix.transpose_apply]
    · simp [Matrix.diagonal_apply, Matrix.transpose_apply, h, Ne.symm h]
  have hdd : Matrix.diagonal (fun t : Fin r => Real.sqrt (sig0 t)) *
      Matrix.diagonal (fun t : Fin r => Real.sqrt (sig0 t)) = Matrix.diagonal sig0 := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext t
    exact Real.mul_self_sqrt (hsig0 t)
  have hX0Y0 : X0 * Matrix.transpose Y0 = U0 * Matrix.diagonal sig0 * Matrix.transpose V0 := by
    show U0 * Matrix.diagonal (fun t : Fin r => Real.sqrt (sig0 t)) *
        Matrix.transpose (V0 * Matrix.diagonal (fun t : Fin r => Real.sqrt (sig0 t)))
      = U0 * Matrix.diagonal sig0 * Matrix.transpose V0
    rw [Matrix.transpose_mul, hdT]
    simp only [Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc, hdd]
  have hspecX0 : spectralNorm X0 ≤ Real.sqrt (SMax sig0) := by
    let Dv : Matrix (Fin r) (Fin r) ℝ := Matrix.diagonal (fun t => Real.sqrt (sig0 t))
    have hconj : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ),
        A.conjTranspose = Matrix.transpose A := by
      intro a b A
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    have hSMaxnn : 0 ≤ SMax sig0 :=
      le_trans (le_of_lt (hsigpos (⟨0, by omega⟩ : Fin r)))
        (le_ciSup ((Set.finite_range sig0).bddAbove) (⟨0, by omega⟩ : Fin r))
    have hD : ‖Dv‖ ≤ Real.sqrt (SMax sig0) := by
      have hD' : ‖Matrix.diagonal (fun t : Fin r => Real.sqrt (sig0 t))‖
          ≤ Real.sqrt (SMax sig0) := by
        rw [Matrix.l2_opNorm_diagonal]
        rw [pi_norm_le_iff_of_nonneg (x := fun t : Fin r => Real.sqrt (sig0 t))
          (Real.sqrt_nonneg (SMax sig0))]
        intro t
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (le_ciSup ((Set.finite_range sig0).bddAbove) t)
      exact hD'
    have hkey : (U0 * Dv).conjTranspose * (U0 * Dv) = Dv.conjTranspose * Dv := by
      have hc1 : (U0 * Dv).conjTranspose = Matrix.transpose (U0 * Dv) := hconj (U0 * Dv)
      have hc2 : Dv.conjTranspose = Matrix.transpose Dv := hconj Dv
      rw [hc1, hc2, Matrix.transpose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (Matrix.transpose U0) U0 Dv, hU0, Matrix.one_mul]
    have hstep : ‖U0 * Dv‖ * ‖U0 * Dv‖ ≤ SMax sig0 := by
      have h1 : ‖U0 * Dv‖ * ‖U0 * Dv‖ = ‖Dv‖ * ‖Dv‖ := by
        rw [← Matrix.l2_opNorm_conjTranspose_mul_self (U0 * Dv), hkey,
          Matrix.l2_opNorm_conjTranspose_mul_self]
      rw [h1]
      calc ‖Dv‖ * ‖Dv‖ ≤ Real.sqrt (SMax sig0) * Real.sqrt (SMax sig0) :=
            mul_le_mul hD hD (norm_nonneg _) (Real.sqrt_nonneg _)
        _ = SMax sig0 := Real.mul_self_sqrt hSMaxnn
    show Statlib.HighDim.MatrixAnalysis.opNorm X0 ≤ Real.sqrt (SMax sig0)
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    show ‖U0 * Dv‖ ≤ Real.sqrt (SMax sig0)
    calc ‖U0 * Dv‖ = Real.sqrt (‖U0 * Dv‖ * ‖U0 * Dv‖) :=
          (Real.sqrt_mul_self (norm_nonneg _)).symm
      _ ≤ Real.sqrt (SMax sig0) := Real.sqrt_le_sqrt hstep
  have hspecY0 : spectralNorm Y0 ≤ Real.sqrt (SMax sig0) := by
    let Ev : Matrix (Fin r) (Fin r) ℝ := Matrix.diagonal (fun t => Real.sqrt (sig0 t))
    have hconj : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ),
        A.conjTranspose = Matrix.transpose A := by
      intro a b A
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    have hSMaxnn : 0 ≤ SMax sig0 :=
      le_trans (le_of_lt (hsigpos (⟨0, by omega⟩ : Fin r)))
        (le_ciSup ((Set.finite_range sig0).bddAbove) (⟨0, by omega⟩ : Fin r))
    have hD : ‖Ev‖ ≤ Real.sqrt (SMax sig0) := by
      have hD' : ‖Matrix.diagonal (fun t : Fin r => Real.sqrt (sig0 t))‖
          ≤ Real.sqrt (SMax sig0) := by
        rw [Matrix.l2_opNorm_diagonal]
        rw [pi_norm_le_iff_of_nonneg (x := fun t : Fin r => Real.sqrt (sig0 t))
          (Real.sqrt_nonneg (SMax sig0))]
        intro t
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (le_ciSup ((Set.finite_range sig0).bddAbove) t)
      exact hD'
    have hkey : (V0 * Ev).conjTranspose * (V0 * Ev) = Ev.conjTranspose * Ev := by
      have hc1 : (V0 * Ev).conjTranspose = Matrix.transpose (V0 * Ev) := hconj (V0 * Ev)
      have hc2 : Ev.conjTranspose = Matrix.transpose Ev := hconj Ev
      rw [hc1, hc2, Matrix.transpose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (Matrix.transpose V0) V0 Ev, hV0, Matrix.one_mul]
    have hstep : ‖V0 * Ev‖ * ‖V0 * Ev‖ ≤ SMax sig0 := by
      have h1 : ‖V0 * Ev‖ * ‖V0 * Ev‖ = ‖Ev‖ * ‖Ev‖ := by
        rw [← Matrix.l2_opNorm_conjTranspose_mul_self (V0 * Ev), hkey,
          Matrix.l2_opNorm_conjTranspose_mul_self]
      rw [h1]
      calc ‖Ev‖ * ‖Ev‖ ≤ Real.sqrt (SMax sig0) * Real.sqrt (SMax sig0) :=
            mul_le_mul hD hD (norm_nonneg _) (Real.sqrt_nonneg _)
        _ = SMax sig0 := Real.mul_self_sqrt hSMaxnn
    show Statlib.HighDim.MatrixAnalysis.opNorm Y0 ≤ Real.sqrt (SMax sig0)
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    show ‖V0 * Ev‖ ≤ Real.sqrt (SMax sig0)
    calc ‖V0 * Ev‖ = Real.sqrt (‖V0 * Ev‖ * ‖V0 * Ev‖) :=
          (Real.sqrt_mul_self (norm_nonneg _)).symm
      _ ≤ Real.sqrt (SMax sig0) := Real.sqrt_le_sqrt hstep
  have h2X0 : twoInfNorm X0 ≤
      Real.sqrt (SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) := by
    have hSMaxnn : 0 ≤ SMax sig0 :=
      le_trans (le_of_lt (hsigpos (⟨0, by omega⟩ : Fin r)))
        (le_ciSup ((Set.finite_range sig0).bddAbove) (⟨0, by omega⟩ : Fin r))
    have hU0nn : 0 ≤ twoInfNorm U0 :=
      le_trans (Real.sqrt_nonneg _)
        (le_ciSup ((Set.finite_range (fun i : Fin m => Real.sqrt (∑ j : Fin r, U0 i j ^ 2))).bddAbove)
          (⟨0, hm⟩ : Fin m))
    have hsqrtrow : ∀ i : Fin m,
        Real.sqrt (∑ j : Fin r, X0 i j ^ 2) ≤
          Real.sqrt (SMax sig0) * Real.sqrt (∑ j : Fin r, U0 i j ^ 2) := by
      intro i
      have hentry : ∀ j : Fin r, X0 i j = U0 i j * Real.sqrt (sig0 j) := by
        intro j
        show (U0 * Matrix.diagonal (fun t : Fin r => Real.sqrt (sig0 t))) i j
          = U0 i j * Real.sqrt (sig0 j)
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single j (by
          intro b _ hb
          simp [Matrix.diagonal_apply, hb]) (by
          intro hj
          exact absurd (Finset.mem_univ j) hj)]
        simp [Matrix.diagonal_apply]
      have hsum : ∑ j : Fin r, X0 i j ^ 2 = ∑ j : Fin r, U0 i j ^ 2 * sig0 j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hentry j, mul_pow, Real.sq_sqrt (hsig0 j)]
      rw [hsum]
      calc Real.sqrt (∑ j : Fin r, U0 i j ^ 2 * sig0 j)
          ≤ Real.sqrt (SMax sig0 * ∑ j : Fin r, U0 i j ^ 2) := by
            apply Real.sqrt_le_sqrt
            have h1 : ∑ j : Fin r, U0 i j ^ 2 * sig0 j
                ≤ ∑ j : Fin r, U0 i j ^ 2 * SMax sig0 := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_left
                (le_ciSup ((Set.finite_range sig0).bddAbove) j) (sq_nonneg _)
            calc ∑ j : Fin r, U0 i j ^ 2 * sig0 j
                ≤ ∑ j : Fin r, U0 i j ^ 2 * SMax sig0 := h1
              _ = SMax sig0 * ∑ j : Fin r, U0 i j ^ 2 := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl (fun j _ => by ring)
        _ = Real.sqrt (SMax sig0) * Real.sqrt (∑ j : Fin r, U0 i j ^ 2) :=
            Real.sqrt_mul hSMaxnn _
    have hone : (⨆ i : Fin m, Real.sqrt (∑ j : Fin r, X0 i j ^ 2)) ≤
        Real.sqrt (SMax sig0) * twoInfNorm U0 := by
      refine Real.iSup_le (fun i => ?_) (mul_nonneg (Real.sqrt_nonneg _) hU0nn)
      calc Real.sqrt (∑ j : Fin r, X0 i j ^ 2)
          ≤ Real.sqrt (SMax sig0) * Real.sqrt (∑ j : Fin r, U0 i j ^ 2) := hsqrtrow i
        _ ≤ Real.sqrt (SMax sig0) * twoInfNorm U0 :=
            mul_le_mul_of_nonneg_left
              (le_ciSup ((Set.finite_range
                (fun i : Fin m => Real.sqrt (∑ j : Fin r, U0 i j ^ 2))).bddAbove) i)
              (Real.sqrt_nonneg _)
    have hsqrtmono : Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) ≤
        Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) := by
      apply Real.sqrt_le_sqrt
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbar (Nat.cast_nonneg r))
        (inv_nonneg.mpr (Nat.cast_nonneg m))
    show (⨆ i : Fin m, Real.sqrt (∑ j : Fin r, X0 i j ^ 2)) ≤
      Real.sqrt (SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ))
    calc (⨆ i : Fin m, Real.sqrt (∑ j : Fin r, X0 i j ^ 2))
        ≤ Real.sqrt (SMax sig0) * twoInfNorm U0 := hone
      _ ≤ Real.sqrt (SMax sig0) * Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hlevU (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrtmono (Real.sqrt_nonneg _)
  have h2Y0 : twoInfNorm Y0 ≤
      Real.sqrt (SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) := by
    have hSMaxnn : 0 ≤ SMax sig0 :=
      le_trans (le_of_lt (hsigpos (⟨0, by omega⟩ : Fin r)))
        (le_ciSup ((Set.finite_range sig0).bddAbove) (⟨0, by omega⟩ : Fin r))
    have hV0nn : 0 ≤ twoInfNorm V0 :=
      le_trans (Real.sqrt_nonneg _)
        (le_ciSup ((Set.finite_range (fun i : Fin n => Real.sqrt (∑ j : Fin r, V0 i j ^ 2))).bddAbove)
          (⟨0, hn⟩ : Fin n))
    have hsqrtrow : ∀ i : Fin n,
        Real.sqrt (∑ j : Fin r, Y0 i j ^ 2) ≤
          Real.sqrt (SMax sig0) * Real.sqrt (∑ j : Fin r, V0 i j ^ 2) := by
      intro i
      have hentry : ∀ j : Fin r, Y0 i j = V0 i j * Real.sqrt (sig0 j) := by
        intro j
        show (V0 * Matrix.diagonal (fun t : Fin r => Real.sqrt (sig0 t))) i j
          = V0 i j * Real.sqrt (sig0 j)
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single j (by
          intro b _ hb
          simp [Matrix.diagonal_apply, hb]) (by
          intro hj
          exact absurd (Finset.mem_univ j) hj)]
        simp [Matrix.diagonal_apply]
      have hsum : ∑ j : Fin r, Y0 i j ^ 2 = ∑ j : Fin r, V0 i j ^ 2 * sig0 j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hentry j, mul_pow, Real.sq_sqrt (hsig0 j)]
      rw [hsum]
      calc Real.sqrt (∑ j : Fin r, V0 i j ^ 2 * sig0 j)
          ≤ Real.sqrt (SMax sig0 * ∑ j : Fin r, V0 i j ^ 2) := by
            apply Real.sqrt_le_sqrt
            have h1 : ∑ j : Fin r, V0 i j ^ 2 * sig0 j
                ≤ ∑ j : Fin r, V0 i j ^ 2 * SMax sig0 := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_left
                (le_ciSup ((Set.finite_range sig0).bddAbove) j) (sq_nonneg _)
            calc ∑ j : Fin r, V0 i j ^ 2 * sig0 j
                ≤ ∑ j : Fin r, V0 i j ^ 2 * SMax sig0 := h1
              _ = SMax sig0 * ∑ j : Fin r, V0 i j ^ 2 := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl (fun j _ => by ring)
        _ = Real.sqrt (SMax sig0) * Real.sqrt (∑ j : Fin r, V0 i j ^ 2) :=
            Real.sqrt_mul hSMaxnn _
    have hone : (⨆ i : Fin n, Real.sqrt (∑ j : Fin r, Y0 i j ^ 2)) ≤
        Real.sqrt (SMax sig0) * twoInfNorm V0 := by
      refine Real.iSup_le (fun i => ?_) (mul_nonneg (Real.sqrt_nonneg _) hV0nn)
      calc Real.sqrt (∑ j : Fin r, Y0 i j ^ 2)
          ≤ Real.sqrt (SMax sig0) * Real.sqrt (∑ j : Fin r, V0 i j ^ 2) := hsqrtrow i
        _ ≤ Real.sqrt (SMax sig0) * twoInfNorm V0 :=
            mul_le_mul_of_nonneg_left
              (le_ciSup ((Set.finite_range
                (fun i : Fin n => Real.sqrt (∑ j : Fin r, V0 i j ^ 2))).bddAbove) i)
              (Real.sqrt_nonneg _)
    have hsqrtmono : Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) ≤
        Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) := by
      apply Real.sqrt_le_sqrt
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbar (Nat.cast_nonneg r))
        (inv_nonneg.mpr (Nat.cast_nonneg n))
    show (⨆ i : Fin n, Real.sqrt (∑ j : Fin r, Y0 i j ^ 2)) ≤
      Real.sqrt (SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ))
    calc (⨆ i : Fin n, Real.sqrt (∑ j : Fin r, Y0 i j ^ 2))
        ≤ Real.sqrt (SMax sig0) * twoInfNorm V0 := hone
      _ ≤ Real.sqrt (SMax sig0) * Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlevV (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrtmono (Real.sqrt_nonneg _)
  have hmid : ∃ (X : Matrix (Fin m) (Fin r) ℝ) (Y : Matrix (Fin n) (Fin r) ℝ),
      X * Matrix.transpose Y = M ∧
      twoInfNorm X ≤
        Real.sqrt (CM * SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) ∧
      twoInfNorm Y ≤
        Real.sqrt (CM * SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) ∧
      frobSq (X - X0) + frobSq (Y - Y0) ≤
        2 * frobSq (X * Matrix.transpose Y - X0 * Matrix.transpose Y0) /
          ((Real.sqrt 2 - 1) * SMin sig0) := by
    exact statopia_math_node_2464956088_5e15ab10 m n r U0 V0 sig0 mu0 mu1 CM M
      hm hn hr hCM hmu hmu0 hU0 hV0 hanti hsmin hM hspec
  obtain ⟨X, Y, hXY, h2X, h2Y, hfin⟩ := hmid
  exact ⟨X0, X, Y0, Y, rfl, rfl, hX0Y0, hXY, hspecX0, hspecY0, h2X0, h2Y0, h2X, h2Y, hfin⟩
  /- @proof-region region.target-node.session.bf74740d2e4b28bc end -/

end

end Statlib.Imported

