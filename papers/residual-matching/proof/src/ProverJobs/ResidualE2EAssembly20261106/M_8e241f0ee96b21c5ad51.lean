import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48
import ProverJobs.ResidualE2EAssembly20261106.M_c281c6201a3dcffd9ac0
import ProverJobs.ResidualE2EAssembly20261106.M_b1ee8c2b77462de73480
import ProverJobs.ResidualE2EAssembly20261106.M_5eacf8ccb7ff44b13edc

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
theorem statopia_math_node_1997987195_42842367 : ∀ (m n r : ℕ) (hm : 0 < m) (hn : 0 < n) (hr : 1 ≤ r) (hrn : r ≤ n) (hrm : r ≤ m)
    (sig0 : Fin r → ℝ) (hsig_anti : Antitone sig0) (hsig_pos : 0 < SMin sig0)
    (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (M0 : Matrix (Fin m) (Fin n) ℝ)
    (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
    (hM0 : M0 = U0 * Matrix.diagonal sig0 * Matrix.transpose V0)
    (mu0 mu1 mubar : ℝ)
    (hmu0 : mu0 ≤ mubar) (hmu1 : mu1 ≤ mubar) (hmubar : 0 ≤ mubar)
    (hincU : twoInfNorm U0 ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)))
    (hincV : twoInfNorm V0 ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)))
    (CM : ℝ) (hCM : 1 ≤ CM)
    (M : Matrix (Fin m) (Fin n) ℝ) (hMclass : InLowRankClass r mu1 M)
    (hMnorm : spectralNorm M ≤ CM * SMax sig0),
    ∃ (X0 : Matrix (Fin m) (Fin r) ℝ) (Y0 : Matrix (Fin n) (Fin r) ℝ)
      (X : Matrix (Fin m) (Fin r) ℝ) (Y : Matrix (Fin n) (Fin r) ℝ),
      (X0 = U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)) ∧
        Y0 = V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t))) ∧
      (M0 = X0 * Matrix.transpose Y0 ∧
        Matrix.transpose X0 * X0 = Matrix.diagonal sig0 ∧
        Matrix.transpose Y0 * Y0 = Matrix.diagonal sig0) ∧
      (spectralNorm X0 = Real.sqrt (SMax sig0) ∧
        spectralNorm Y0 = Real.sqrt (SMax sig0)) ∧
      (twoInfNorm X0 ≤ Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) ∧
        twoInfNorm Y0 ≤ Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))) ∧
      (let F0 : Matrix (Fin (m + n)) (Fin r) ℝ := Fin.append (fun a => X0 a) (fun b => Y0 b);
        Matrix.transpose F0 * F0 = (2 : ℝ) • Matrix.diagonal sig0) ∧
      (M = X * Matrix.transpose Y ∧
        Matrix.transpose X * X = Matrix.transpose Y * Y ∧
        spectralNorm X = Real.sqrt (spectralNorm M) ∧
        spectralNorm Y = Real.sqrt (spectralNorm M)) ∧
      (twoInfNorm X ≤ Real.sqrt (CM * SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) ∧
        twoInfNorm Y ≤ Real.sqrt (CM * SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))) := by
  /- @proof-region region.target-node.session.f6efb897db5381d3 begin -/
  classical
  intro m n r hm hn hr hrn hnm sig0 hsig_anti hsig_pos U0 V0 M0 hU0 hV0 hM0
    mu0 mu1 mubar hmu0 hmu1 hmubar hincU hincV CM hCM M hMclass hMnorm
  set Dc : Matrix (Fin r) (Fin r) ℝ := Matrix.diagonal (fun t => Real.sqrt (sig0 t)) with hDc
  set X0c : Matrix (Fin m) (Fin r) ℝ := U0 * Dc with hX0c
  set Y0c : Matrix (Fin n) (Fin r) ℝ := V0 * Dc with hY0c
  set F0c : Matrix (Fin (m + n)) (Fin r) ℝ :=
    fun i t => Fin.append (m := m) (n := n) (fun a => X0c a t) (fun b => Y0c b t) i with hF0c
  have h1 : X0c = U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)) := by rw [hX0c, hDc]
  have h2 : Y0c = V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)) := by rw [hY0c, hDc]
  have hSigNonneg : ∀ t : Fin r, 0 ≤ sig0 t := by
    intro t
    have hle : SMin sig0 ≤ sig0 t := by
      have hbdd : BddBelow (Set.range sig0) := by
        refine ⟨sig0 ⟨r - 1, by omega⟩, ?_⟩
        intro b hb
        obtain ⟨i, rfl⟩ := hb
        exact hsig_anti (by
          rw [Fin.le_def]
          show i.val ≤ r - 1
          have := i.isLt
          omega)
      exact ciInf_le hbdd t
    linarith
  have hDcT : Matrix.transpose Dc = Dc := by
    rw [hDc, Matrix.diagonal_transpose]
  have hDcSq : Dc * Dc = Matrix.diagonal sig0 := by
    rw [hDc, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => Real.sqrt (sig0 i) * Real.sqrt (sig0 i)) = sig0 from
      funext (fun t => Real.mul_self_sqrt (hSigNonneg t))]
  have h3 : M0 = X0c * Matrix.transpose Y0c := by
    rw [hM0, hX0c, hY0c, Matrix.transpose_mul, hDcT]
    calc U0 * Matrix.diagonal sig0 * Matrix.transpose V0
        = U0 * (Matrix.diagonal sig0 * Matrix.transpose V0) := by rw [Matrix.mul_assoc]
      _ = U0 * ((Dc * Dc) * Matrix.transpose V0) := by rw [← hDcSq]
      _ = U0 * (Dc * (Dc * Matrix.transpose V0)) := by rw [Matrix.mul_assoc]
      _ = (U0 * Dc) * (Dc * Matrix.transpose V0) := by rw [← Matrix.mul_assoc]
  have h4 : Matrix.transpose X0c * X0c = Matrix.diagonal sig0 := by
    rw [hX0c, Matrix.transpose_mul, hDcT]
    rw [Matrix.mul_assoc Dc (Matrix.transpose U0) (U0 * Dc)]
    rw [(Matrix.mul_assoc (Matrix.transpose U0) U0 Dc).symm]
    rw [hU0, Matrix.one_mul, hDcSq]
  have h5 : Matrix.transpose Y0c * Y0c = Matrix.diagonal sig0 := by
    rw [hY0c, Matrix.transpose_mul, hDcT]
    rw [Matrix.mul_assoc Dc (Matrix.transpose V0) (V0 * Dc)]
    rw [(Matrix.mul_assoc (Matrix.transpose V0) V0 Dc).symm]
    rw [hV0, Matrix.one_mul, hDcSq]
  have h6 : spectralNorm X0c = Real.sqrt (SMax sig0) := by
    rw [h1]
    exact statopia_math_node_183065247_d0f01c1a m r hr sig0 hSigNonneg U0 hU0
  have h7 : spectralNorm Y0c = Real.sqrt (SMax sig0) := by
    rw [h2]
    exact statopia_math_node_183065247_d0f01c1a n r hr sig0 hSigNonneg V0 hV0
  have h8 : twoInfNorm X0c ≤ Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) := by
    rw [h1]
    exact statopia_math_node_1308708277_bfca1bc0 m r hm hr sig0 hSigNonneg U0 mu0 mubar hmu0 hmubar hincU
  have h9 : twoInfNorm Y0c ≤ Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)) := by
    rw [h2]
    exact statopia_math_node_1308708277_bfca1bc0 n r hn hr sig0 hSigNonneg V0 mu0 mubar hmu0 hmubar hincV
  have h10 : ∀ (i : Fin (m + n)) (t : Fin r),
      F0c i t = Fin.append (m := m) (n := n) (fun a => X0c a t) (fun b => Y0c b t) i := by
    intro i t
    rw [hF0c]
  have h11 : Matrix.transpose F0c * F0c = Matrix.diagonal (fun t => 2 * sig0 t) := by
    ext s t
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    rw [Fin.sum_univ_add]
    have e4 : (∑ a : Fin m, X0c a s * X0c a t) = Matrix.diagonal sig0 s t := by
      have hh : (Matrix.transpose X0c * X0c) s t = ∑ a : Fin m, X0c a s * X0c a t := by
        rw [Matrix.mul_apply]
        simp only [Matrix.transpose_apply]
      rw [← hh, h4]
    have e5 : (∑ b : Fin n, Y0c b s * Y0c b t) = Matrix.diagonal sig0 s t := by
      have hh : (Matrix.transpose Y0c * Y0c) s t = ∑ b : Fin n, Y0c b s * Y0c b t := by
        rw [Matrix.mul_apply]
        simp only [Matrix.transpose_apply]
      rw [← hh, h5]
    simp only [hF0c, Fin.append_left, Fin.append_right]
    rw [e4, e5]
    simp only [Matrix.diagonal_apply]
    split_ifs with hst
    · ring
    · ring
  have combine : ∀ (X : Matrix (Fin m) (Fin r) ℝ) (Y : Matrix (Fin n) (Fin r) ℝ),
      (M = X * Matrix.transpose Y) → (Matrix.transpose X * X = Matrix.transpose Y * Y) →
      (spectralNorm X = Real.sqrt (spectralNorm M)) →
      (spectralNorm Y = Real.sqrt (spectralNorm M)) →
      (twoInfNorm X ≤ Real.sqrt (CM * SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ))) →
      (twoInfNorm Y ≤ Real.sqrt (CM * SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))) →
      ∃ (X0 : Matrix (Fin m) (Fin r) ℝ) (Y0 : Matrix (Fin n) (Fin r) ℝ)
        (X : Matrix (Fin m) (Fin r) ℝ) (Y : Matrix (Fin n) (Fin r) ℝ)
        (F0 : Matrix (Fin (m + n)) (Fin r) ℝ),
        X0 = U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)) ∧
        Y0 = V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)) ∧
        M0 = X0 * Matrix.transpose Y0 ∧
        Matrix.transpose X0 * X0 = Matrix.diagonal sig0 ∧
        Matrix.transpose Y0 * Y0 = Matrix.diagonal sig0 ∧
        spectralNorm X0 = Real.sqrt (SMax sig0) ∧
        spectralNorm Y0 = Real.sqrt (SMax sig0) ∧
        twoInfNorm X0 ≤ Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) ∧
        twoInfNorm Y0 ≤ Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)) ∧
        (∀ (i : Fin (m + n)) (t : Fin r),
          F0 i t = Fin.append (m := m) (n := n) (fun a => X0 a t) (fun b => Y0 b t) i) ∧
        Matrix.transpose F0 * F0 = Matrix.diagonal (fun t => 2 * sig0 t) ∧
        M = X * Matrix.transpose Y ∧
        Matrix.transpose X * X = Matrix.transpose Y * Y ∧
        spectralNorm X = Real.sqrt (spectralNorm M) ∧
        spectralNorm Y = Real.sqrt (spectralNorm M) ∧
        twoInfNorm X ≤ Real.sqrt (CM * SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) ∧
        twoInfNorm Y ≤ Real.sqrt (CM * SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)) := by
    intro X Y hXY hbal hspecX hspecY hbx hby
    exact ⟨X0c, Y0c, X, Y, F0c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      hXY, hbal, hspecX, hspecY, hbx, hby⟩
  obtain ⟨Xm, Ym, hXY, hbal, hspecX, hspecY, hbx, hby⟩ :=
    statopia_math_node_290215883_e35c90a8 m n r hm hn hr sig0 hSigNonneg mu1 mubar hmu1
      hmubar CM hCM M hMclass hMnorm
  set G : Matrix (Fin (m + n)) (Fin r) ℝ := Fin.append (fun a => X0c a) (fun b => Y0c b) with hG
  have hdiag_smul : Matrix.diagonal (fun t => 2 * sig0 t) = (2 : ℝ) • Matrix.diagonal sig0 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  have hG11 : Matrix.transpose G * G = Matrix.diagonal (fun t => 2 * sig0 t) := by
    ext s t
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    rw [Fin.sum_univ_add]
    have e4 : (∑ a : Fin m, X0c a s * X0c a t) = Matrix.diagonal sig0 s t := by
      have hh : (Matrix.transpose X0c * X0c) s t = ∑ a : Fin m, X0c a s * X0c a t := by
        rw [Matrix.mul_apply]
        simp only [Matrix.transpose_apply]
      rw [← hh, h4]
    have e5 : (∑ b : Fin n, Y0c b s * Y0c b t) = Matrix.diagonal sig0 s t := by
      have hh : (Matrix.transpose Y0c * Y0c) s t = ∑ b : Fin n, Y0c b s * Y0c b t := by
        rw [Matrix.mul_apply]
        simp only [Matrix.transpose_apply]
      rw [← hh, h5]
    simp only [hG, Fin.append_left, Fin.append_right]
    rw [e4, e5]
    simp only [Matrix.diagonal_apply]
    split_ifs with hst
    · ring
    · ring
  refine ⟨X0c, Y0c, Xm, Ym, ⟨rfl, rfl⟩, ⟨h3, h4, h5⟩, ⟨h6, h7⟩, ⟨h8, h9⟩, ?_,
    ⟨hXY, hbal, hspecX, hspecY⟩, ⟨hbx, hby⟩⟩
  show Matrix.transpose G * G = (2 : ℝ) • Matrix.diagonal sig0
  rw [hG11, hdiag_smul]
  /- @proof-region region.target-node.session.f6efb897db5381d3 end -/

end

end Statlib.Imported

