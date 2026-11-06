import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported
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
theorem statopia_math_node_913401766_3b0eb21b : ∀ (m n r : ℕ) (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (sig0 : Fin r → ℝ) (mu0 mu1 CM : ℝ)
    (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
    (hsmin : 0 < SMin sig0),
    ∃ X : Matrix (Fin m) (Fin r) ℝ, ∃ Y : Matrix (Fin n) (Fin r) ℝ,
      X * Matrix.transpose Y = 0 ∧
      twoInfNorm X ≤
        Real.sqrt (CM * SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) ∧
      twoInfNorm Y ≤
        Real.sqrt (CM * SMax sig0) * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) ∧
      frobSq (X - U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t))) +
          frobSq (Y - V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t))) ≤
        2 * frobSq (X * Matrix.transpose Y -
            (U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t))) *
              Matrix.transpose (V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)))) /
          ((Real.sqrt 2 - 1) * SMin sig0) := by
  /- @proof-region region.target-node.session.24713f039226f341 begin -/
  intro m n r U0 V0 sig0 mu0 mu1 CM hU0 hV0 hsmin
  set D : Matrix (Fin r) (Fin r) ℝ := Matrix.diagonal (fun t => Real.sqrt (sig0 t)) with hD
  set X0 : Matrix (Fin m) (Fin r) ℝ := U0 * D with hX0def
  set Y0 : Matrix (Fin n) (Fin r) ℝ := V0 * D with hY0def
  have hbdd : BddBelow (Set.range sig0) := by
    refine ⟨-∑ u : Fin r, |sig0 u|, ?_⟩
    rintro x ⟨t, rfl⟩
    have h1 : |sig0 t| ≤ ∑ u : Fin r, |sig0 u| :=
      Finset.single_le_sum (fun u _ => abs_nonneg (sig0 u)) (Finset.mem_univ t)
    have h2 : -|sig0 t| ≤ sig0 t := neg_abs_le (sig0 t)
    linarith
  have hsle : ∀ t : Fin r, SMin sig0 ≤ sig0 t := fun t => ciInf_le hbdd t
  have hσ : ∀ t : Fin r, 0 ≤ sig0 t := fun t => le_trans (le_of_lt hsmin) (hsle t)
  have hfrob : ∀ {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ),
      frobSq A = (Matrix.transpose A * A).trace := by
    intro p q A
    simp only [frobSq, pow_two]
    rw [show (Matrix.transpose A * A).trace = ∑ i : Fin q, ∑ k : Fin p, A k i * A k i by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]]
    rw [Finset.sum_comm]
  have hDtrans : Matrix.transpose D = D := by
    rw [hD]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, Matrix.transpose_apply, h, eq_comm]
  have hDmul : D * D = Matrix.diagonal sig0 := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1
    funext t
    exact Real.mul_self_sqrt (hσ t)
  have hX0Xt : Matrix.transpose X0 * X0 = Matrix.diagonal sig0 := by
    rw [hX0def, Matrix.transpose_mul, hDtrans]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.transpose U0) U0 D, hU0, Matrix.one_mul]
    exact hDmul
  have hX0val : frobSq X0 = ∑ t : Fin r, sig0 t := by
    rw [hfrob, hX0Xt, Matrix.trace_diagonal]
  have hY0Xt : Matrix.transpose Y0 * Y0 = Matrix.diagonal sig0 := by
    rw [hY0def, Matrix.transpose_mul, hDtrans]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.transpose V0) V0 D, hV0, Matrix.one_mul]
    exact hDmul
  have hY0val : frobSq Y0 = ∑ t : Fin r, sig0 t := by
    rw [hfrob, hY0Xt, Matrix.trace_diagonal]
  have hneg : ∀ {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ), frobSq (-A) = frobSq A := by
    intro p q A
    simp only [frobSq, Matrix.neg_apply]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have hXYval : frobSq (X0 * Matrix.transpose Y0) = ∑ t : Fin r, sig0 t ^ 2 := by
    rw [hfrob]
    have h1 : Matrix.transpose (X0 * Matrix.transpose Y0) * (X0 * Matrix.transpose Y0)
        = Y0 * Matrix.diagonal sig0 * Matrix.transpose Y0 := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [← Matrix.mul_assoc (Y0 * Matrix.transpose X0) X0 (Matrix.transpose Y0)]
      rw [Matrix.mul_assoc Y0 (Matrix.transpose X0) X0, hX0Xt]
    rw [h1]
    have h2 : (Y0 * Matrix.diagonal sig0 * Matrix.transpose Y0).trace
        = (Matrix.diagonal sig0 * Matrix.diagonal sig0).trace := by
      rw [Matrix.trace_mul_comm (Y0 * Matrix.diagonal sig0) (Matrix.transpose Y0)]
      rw [← Matrix.mul_assoc (Matrix.transpose Y0) Y0 (Matrix.diagonal sig0), hY0Xt]
    rw [h2, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [pow_two]
  have hL : frobSq ((0 : Matrix (Fin m) (Fin r) ℝ) - X0) +
      frobSq ((0 : Matrix (Fin n) (Fin r) ℝ) - Y0) = 2 * ∑ t : Fin r, sig0 t := by
    have e1 : frobSq ((0 : Matrix (Fin m) (Fin r) ℝ) - X0) = frobSq X0 := by
      rw [zero_sub, hneg]
    have e2 : frobSq ((0 : Matrix (Fin n) (Fin r) ℝ) - Y0) = frobSq Y0 := by
      rw [zero_sub, hneg]
    rw [e1, e2, hX0val, hY0val]
    ring
  have hR : frobSq (-(X0 * Matrix.transpose Y0)) = ∑ t : Fin r, sig0 t ^ 2 := by
    rw [hneg, hXYval]
  have hterm : ∀ t : Fin r, sig0 t ≤ sig0 t ^ 2 / SMin sig0 := by
    intro t
    have h1 : SMin sig0 ≤ sig0 t := hsle t
    have h0 : 0 ≤ sig0 t := hσ t
    rw [le_div_iff₀ hsmin]
    calc sig0 t * SMin sig0 ≤ sig0 t * sig0 t := mul_le_mul_of_nonneg_left h1 h0
      _ = sig0 t ^ 2 := by rw [pow_two]
  have hsum : ∑ t : Fin r, sig0 t ≤ ∑ t : Fin r, sig0 t ^ 2 / SMin sig0 :=
    Finset.sum_le_sum (fun t _ => hterm t)
  rw [← Finset.sum_div] at hsum
  have hX2nn : 0 ≤ ∑ t : Fin r, sig0 t ^ 2 := Finset.sum_nonneg (fun t _ => sq_nonneg (sig0 t))
  have hspos : 0 < Real.sqrt 2 - 1 := by
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  have hspos2 : Real.sqrt 2 - 1 ≤ 1 := by
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  have hden : 0 < (Real.sqrt 2 - 1) * SMin sig0 := mul_pos hspos hsmin
  have hdenle : (Real.sqrt 2 - 1) * SMin sig0 ≤ SMin sig0 := by
    have h := mul_le_mul_of_nonneg_right hspos2 (le_of_lt hsmin)
    simpa using h
  have hmain : 2 * (∑ t : Fin r, sig0 t) ≤
      2 * (∑ t : Fin r, sig0 t ^ 2) / ((Real.sqrt 2 - 1) * SMin sig0) := by
    have step1 : 2 * (∑ t : Fin r, sig0 t) ≤
        2 * ((∑ t : Fin r, sig0 t ^ 2) / SMin sig0) := by linarith
    have step3 : 2 * ((∑ t : Fin r, sig0 t ^ 2) / SMin sig0) ≤
        2 * (∑ t : Fin r, sig0 t ^ 2) / ((Real.sqrt 2 - 1) * SMin sig0) := by
      have h := div_le_div_of_nonneg_left (by linarith : (0:ℝ) ≤ 2 * (∑ t : Fin r, sig0 t ^ 2))
        hden hdenle
      calc 2 * ((∑ t : Fin r, sig0 t ^ 2) / SMin sig0)
          = 2 * (∑ t : Fin r, sig0 t ^ 2) / SMin sig0 := by ring
        _ ≤ 2 * (∑ t : Fin r, sig0 t ^ 2) / ((Real.sqrt 2 - 1) * SMin sig0) := h
    linarith
  have hnormm : twoInfNorm (0 : Matrix (Fin m) (Fin r) ℝ) = 0 := by
    simp [twoInfNorm, Real.iSup_const_zero]
  have hnorms : twoInfNorm (0 : Matrix (Fin n) (Fin r) ℝ) = 0 := by
    simp [twoInfNorm, Real.iSup_const_zero]
  refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
  · simp
  · rw [hnormm]; positivity
  · rw [hnorms]; positivity
  · have hz : (0 : Matrix (Fin m) (Fin r) ℝ) * Matrix.transpose (0 : Matrix (Fin n) (Fin r) ℝ) = 0 := by
      simp
    rw [hz, hL, zero_sub, hR]; exact hmain
  /- @proof-region region.target-node.session.24713f039226f341 end -/

end

end Statlib.Imported

