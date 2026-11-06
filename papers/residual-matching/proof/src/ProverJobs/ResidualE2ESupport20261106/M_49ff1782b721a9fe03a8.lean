import Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_fc77e5f7bde342f28b24

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2776670489_0aa5642a : ∀ (m n : ℕ) (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ)
    (z : ℂ) (hz : 0 < z.im),
    (((z : ℂ) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) -
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)⁻¹).trace
                    = - (∑ i : Fin n, (((svals A i : ℂ) - z)⁻¹ + (-(svals A i : ℂ) - z)⁻¹))
                      + (((m : ℂ) - (n : ℂ)) * z⁻¹) := by
  /- @proof-region region.target-node.session.4efc392d19187a33 begin -/
  intro m n hn A z hz
  set A' : Matrix (Fin m) (Fin n) ℂ := A.map Complex.ofReal with hA'
  set B : Matrix (Fin n) (Fin m) ℂ := A'.transpose with hB
  set F : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) A' B
      (0 : Matrix (Fin n) (Fin n) ℂ) with hF
  have hXeq :
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal = F := by
    rw [hF]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hA', hB, Matrix.map_apply]
  rw [hXeq]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simpa using hz
  have hzimm : z.im ≠ 0 := ne_of_gt hz
  have hBconj : A'.conjTranspose = B := by
    rw [hB]
    ext i j
    simp [hA', Matrix.conjTranspose_apply, Complex.conj_ofReal]
  have hFherm : F.IsHermitian := by
    rw [hF]
    refine Matrix.IsHermitian.fromBlocks ?_ hBconj ?_
    · show (0 : Matrix (Fin m) (Fin m) ℂ).conjTranspose = 0
      simp
    · show (0 : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 0
      simp
  set w : ℂ := z * z with hw
  set P : Matrix (Fin m) (Fin m) ℂ := w • 1 - A' * B with hP
  set Q : Matrix (Fin n) (Fin n) ℂ := w • 1 - B * A' with hQ
  have hu1 : IsUnit (z • 1 - F) := by
    have h := Matrix.IsHermitian.isUnit_sub_smul_one F hFherm z hzimm
    simpa [neg_sub] using h.neg
  have hu2 : IsUnit (z • 1 + F) := by
    have h := Matrix.IsHermitian.isUnit_sub_smul_one (-F) hFherm.neg z hzimm
    simpa using h.neg
  have hprod : (z • 1 - F) * (z • 1 + F) = w • 1 - F * F := by
    have hzF : (z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) * F = z • F := by
      rw [Algebra.smul_mul_assoc, one_mul]
    have hFz : F * (z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) = z • F := by
      rw [Algebra.mul_smul_comm, mul_one]
    have hzz : (z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) *
        (z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) = w • 1 := by
      rw [Algebra.smul_mul_assoc, one_mul, smul_smul, ← hw]
    have hexp : ∀ a b : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ,
        (a - b) * (a + b) = a * a + a * b - b * a - b * b := fun a b => by
      noncomm_ring
    have hcancel : ∀ x y t : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ,
        x + y - y - t = x - t := fun x y t => by
      noncomm_ring
    rw [hexp (z • 1) F, hzz, hzF, hFz, hcancel (w • 1) (z • F) (F * F)]
  have hmul_blocks : ∀ (X1 : Matrix (Fin m) (Fin m) ℂ) (Y1 : Matrix (Fin m) (Fin n) ℂ)
      (Z1 : Matrix (Fin n) (Fin m) ℂ) (W1 : Matrix (Fin n) (Fin n) ℂ)
      (X2 : Matrix (Fin m) (Fin m) ℂ) (Y2 : Matrix (Fin m) (Fin n) ℂ)
      (Z2 : Matrix (Fin n) (Fin m) ℂ) (W2 : Matrix (Fin n) (Fin n) ℂ),
      Matrix.fromBlocks X1 Y1 Z1 W1 * Matrix.fromBlocks X2 Y2 Z2 W2 =
        Matrix.fromBlocks (X1 * X2 + Y1 * Z2) (X1 * Y2 + Y1 * W2)
          (Z1 * X2 + W1 * Z2) (Z1 * Y2 + W1 * W2) := by
    intro X1 Y1 Z1 W1 X2 Y2 Z2 W2
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type]
  have hone_blocks : (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) =
      Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  have htr_blocks : ∀ (X1 : Matrix (Fin m) (Fin m) ℂ) (Y1 : Matrix (Fin m) (Fin n) ℂ)
      (Z1 : Matrix (Fin n) (Fin m) ℂ) (W1 : Matrix (Fin n) (Fin n) ℂ),
      (Matrix.fromBlocks X1 Y1 Z1 W1).trace = X1.trace + W1.trace := by
    intro X1 Y1 Z1 W1
    simp [Matrix.trace, Matrix.diag, Matrix.fromBlocks, Fintype.sum_sum_type]
  have hinv_mul_det : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ),
      IsUnit X.det → X * X⁻¹ = 1 := by
    intro ι _ _ X h
    exact Matrix.mul_nonsing_inv X h
  have hunit_det : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ),
      IsUnit X ↔ IsUnit X.det := by
    intro ι _ _ X
    exact Matrix.isUnit_iff_isUnit_det X
  have hinv_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℂ),
      X * Y = 1 → X⁻¹ = Y := by
    intro ι _ _ X Y h
    exact Matrix.inv_eq_right_inv h
  have hFF : F * F = Matrix.fromBlocks (A' * B) (0 : Matrix (Fin m) (Fin n) ℂ)
      (0 : Matrix (Fin n) (Fin m) ℂ) (B * A') := by
    rw [hF, hmul_blocks]
    simp
  have hW : w • 1 - F * F = Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin n) ℂ)
      (0 : Matrix (Fin n) (Fin m) ℂ) Q := by
    rw [hFF, hP, hQ]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.one_apply, smul_eq_mul]
  have hWunit : IsUnit (w • 1 - F * F) := by
    rw [← hprod]
    exact hu1.mul hu2
  have hWdet : IsUnit (w • 1 - F * F).det := (hunit_det (w • 1 - F * F)).mp hWunit
  have hdetPQ : IsUnit (P.det * Q.det) := by
    rw [hW, Matrix.det_fromBlocks_zero₂₁] at hWdet
    exact hWdet
  have hPunit : IsUnit P :=
    (hunit_det P).mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hdetPQ.ne_zero).1)
  have hQunit : IsUnit Q :=
    (hunit_det Q).mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hdetPQ.ne_zero).2)
  have hPP : P * P⁻¹ = 1 := hinv_mul_det P ((hunit_det P).mp hPunit)
  have hQQ : Q * Q⁻¹ = 1 := hinv_mul_det Q ((hunit_det Q).mp hQunit)
  have hWinv : (w • 1 - F * F)⁻¹ = Matrix.fromBlocks P⁻¹ (0 : Matrix (Fin m) (Fin n) ℂ)
      (0 : Matrix (Fin n) (Fin m) ℂ) Q⁻¹ := by
    apply hinv_eq
    rw [hW, hmul_blocks, hone_blocks, hPP, hQQ]
    simp
  have htrW : ((w • 1 - F * F)⁻¹).trace = (P⁻¹).trace + (Q⁻¹).trace := by
    rw [hWinv, htr_blocks]
  have hzW : (z • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) * (w • 1 - F * F)⁻¹
      = z • (w • 1 - F * F)⁻¹ := by
    rw [Algebra.smul_mul_assoc, one_mul]
  have hFW : (F * (w • 1 - F * F)⁻¹).trace = 0 := by
    rw [hWinv, hF, hmul_blocks, htr_blocks]
    simp [Matrix.trace]
  have hinv : (z • 1 - F)⁻¹ = (z • 1 + F) * (w • 1 - F * F)⁻¹ := by
    apply hinv_eq
    rw [← mul_assoc, hprod]
    exact hinv_mul_det (w • 1 - F * F) hWdet
  have htr : ((z • 1 - F)⁻¹).trace = z * ((P⁻¹).trace + (Q⁻¹).trace) := by
    rw [hinv, add_mul, Matrix.trace_add, hzW, Matrix.trace_smul, hFW, htrW, smul_eq_mul,
      add_zero]
  have hPQ : (P⁻¹).trace = (Q⁻¹).trace + ((m : ℂ) - (n : ℂ)) * w⁻¹ := by
    have hwne : w ≠ 0 := by
      rw [hw]
      exact mul_ne_zero hz0 hz0
    have hsm1 : (w • (1 : Matrix (Fin m) (Fin m) ℂ)) * A' = w • A' := by
      ext i j
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, smul_eq_mul,
          if_pos rfl, mul_one]
      · intro k _ hk
        rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, if_neg (Ne.symm hk), mul_zero,
          zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hsm2 : A' * (w • (1 : Matrix (Fin n) (Fin n) ℂ)) = w • A' := by
      ext i j
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, smul_eq_mul,
          if_pos rfl, mul_one, mul_comm (A' i j) w]
      · intro k _ hk
        rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, if_neg hk, mul_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have hPA : P * A' = A' * Q := by
      rw [hP, hQ, Matrix.sub_mul, Matrix.mul_sub, hsm2, hsm1, Matrix.mul_assoc]
    have hkey : P * (A' * Q⁻¹ * B) = A' * B := by
      have e4 : (A' * Q) * Q⁻¹ = A' * (Q * Q⁻¹) := by rw [Matrix.mul_assoc]
      calc P * (A' * Q⁻¹ * B)
          = (P * (A' * Q⁻¹)) * B := by rw [← Matrix.mul_assoc]
        _ = ((P * A') * Q⁻¹) * B := by rw [← Matrix.mul_assoc]
        _ = ((A' * Q) * Q⁻¹) * B := by rw [hPA]
        _ = (A' * (Q * Q⁻¹)) * B := by rw [e4]
        _ = A' * B := by rw [hQQ, Matrix.mul_one]
    have hWood : P⁻¹ = w⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ) + w⁻¹ • (A' * Q⁻¹ * B) := by
      apply hinv_eq
      rw [mul_add, Algebra.mul_smul_comm, Algebra.mul_smul_comm, mul_one, hkey, ← smul_add, hP,
        sub_add_cancel, smul_smul, inv_mul_cancel₀ hwne, one_smul]
    have htrA : (P⁻¹).trace = (m : ℂ) * w⁻¹ + w⁻¹ * ((A' * Q⁻¹ * B).trace) := by
      rw [hWood, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
        Fintype.card_fin]
      simp only [smul_eq_mul]
      ring
    have hBA : B * A' = w • 1 - Q := by
      rw [hQ]
      abel
    have htrB : (A' * Q⁻¹ * B).trace = w * (Q⁻¹).trace - (n : ℂ) := by
      rw [Matrix.trace_mul_comm (A' * Q⁻¹) B, ← Matrix.mul_assoc, hBA, Matrix.sub_mul,
        Algebra.smul_mul_assoc, one_mul, hQQ, sub_eq_add_neg, Matrix.trace_add, Matrix.trace_neg,
        Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
      simp only [smul_eq_mul]
      ring
    rw [htrA, htrB]
    field_simp
    ring
  have hQspec : (Q⁻¹).trace = ∑ i : Fin n, (w - ((svals A i : ℝ) : ℂ) ^ 2)⁻¹ := by
    have hwnz : ∀ s : ℝ, w - (s : ℂ) ^ 2 ≠ 0 := by
      intro s h
      have hsz : (s : ℂ) - z ≠ 0 := by
        intro hs
        have hz' : z = (s : ℂ) := (sub_eq_zero.mp hs).symm
        rw [hz'] at hz
        simp at hz
      have hmsz : -(s : ℂ) - z ≠ 0 := by
        intro hs
        have hz' : z = -(s : ℂ) := (sub_eq_zero.mp hs).symm
        rw [hz'] at hz
        simp at hz
      have hfac : z * z - (s : ℂ) ^ 2 = (z - (s : ℂ)) * (z + (s : ℂ)) := by ring
      rw [hw] at h
      rw [hfac] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact hsz (by linear_combination -h')
      · exact hmsz (by linear_combination -h')
    rw [hQ, hB, hA']
    exact statopia_math_node_1439674200_188c062d m n A w (fun i => hwnz (svals A i))
  have hterm : ∀ i : Fin n,
      2 * z * (w - ((svals A i : ℝ) : ℂ) ^ 2)⁻¹ =
        -(((svals A i : ℂ) - z)⁻¹ + (-(svals A i : ℂ) - z)⁻¹) := by
    have hsz : ∀ s : ℝ, (s : ℂ) - z ≠ 0 := by
      intro s h
      have hz' : z = (s : ℂ) := (sub_eq_zero.mp h).symm
      rw [hz'] at hz
      simp at hz
    have hmsz : ∀ s : ℝ, -(s : ℂ) - z ≠ 0 := by
      intro s h
      have hz' : z = -(s : ℂ) := (sub_eq_zero.mp h).symm
      rw [hz'] at hz
      simp at hz
    have hws : ∀ s : ℝ, z ^ 2 - (s : ℂ) ^ 2 ≠ 0 := by
      intro s h
      have hfac : z ^ 2 - (s : ℂ) ^ 2 = (z - (s : ℂ)) * (z + (s : ℂ)) := by ring
      rw [hfac] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact hsz s (by linear_combination -h')
      · exact hmsz s (by linear_combination -h')
    intro i
    have h1 : z ^ 2 - ((svals A i : ℝ) : ℂ) ^ 2 ≠ 0 := hws (svals A i)
    have h2 : ((svals A i : ℝ) : ℂ) - z ≠ 0 := hsz (svals A i)
    have h3 : -((svals A i : ℝ) : ℂ) - z ≠ 0 := hmsz (svals A i)
    rw [hw, ← pow_two z]
    field_simp
    ring
  have hfinal : ((z • 1 - F)⁻¹).trace =
      -(∑ i : Fin n, (((svals A i : ℂ) - z)⁻¹ + (-(svals A i : ℂ) - z)⁻¹)) +
        (((m : ℂ) - (n : ℂ)) * z⁻¹) := by
    have h1 : ((z • 1 - F)⁻¹).trace =
        z * (2 * (∑ i : Fin n, (w - ((svals A i : ℝ) : ℂ) ^ 2)⁻¹)) +
          ((m : ℂ) - (n : ℂ)) * z⁻¹ := by
      rw [htr, hPQ, hQspec, hw]
      have hz2 : z * z ≠ 0 := mul_ne_zero hz0 hz0
      field_simp
      ring
    have h2 : z * (2 * (∑ i : Fin n, (w - ((svals A i : ℝ) : ℂ) ^ 2)⁻¹))
        = ∑ i : Fin n, 2 * z * (w - ((svals A i : ℝ) : ℂ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have h3 : (∑ i : Fin n, 2 * z * (w - ((svals A i : ℝ) : ℂ) ^ 2)⁻¹)
        = -(∑ i : Fin n, (((svals A i : ℂ) - z)⁻¹ + (-(svals A i : ℂ) - z)⁻¹)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    rw [h1, h2, h3]
  exact hfinal
  /- @proof-region region.target-node.session.4efc392d19187a33 end -/

end Statlib.Imported

