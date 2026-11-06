import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48
import ProverJobs.ResidualE2EAssembly20261106.M_8e241f0ee96b21c5ad51
import ProverJobs.ResidualE2EAssembly20261106.M_c84a1f6d480e7cbc1162
import ProverJobs.ResidualE2EAssembly20261106.M_5d1852be792d69517477
import ProverJobs.ResidualE2EAssembly20261106.M_64ffdbd3bb52e4d66abf
import ProverJobs.ResidualE2EAssembly20261106.M_a06de3dfe0f3e485ea7c

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
theorem statopia_math_node_3113149870_e08e141b : ∀ (m n r : ℕ) (hm : 0 < m) (hn : 0 < n) (hr : 1 ≤ r)
    (hrn : r ≤ n) (hnm : n ≤ m) (hrm : r ≤ m)
    (p : ℝ) (hp : 0 < p)
    (Om : Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ (i : Fin m) (j : Fin n), Om i j = 0 ∨ Om i j = 1)
    (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
    (sig0 : Fin r → ℝ) (hsig_anti : Antitone sig0) (hsig_pos : 0 < SMin sig0)
    (Lambda theta : ℝ) (hLambda : 0 ≤ Lambda) (htheta : 0 ≤ theta)
    (hMask : MaskEvent Lambda theta p Om (tangentSpace U0 V0))
    (mubar : ℝ) (hmubar : 0 ≤ mubar)
    (CM : ℝ) (hCM : 1 ≤ CM)
    (X0 X : Matrix (Fin m) (Fin r) ℝ) (Y0 Y : Matrix (Fin n) (Fin r) ℝ)
    (hX0 : X0 = U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)))
    (hY0 : Y0 = V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)))
    (hX0Y0 : X0 * Matrix.transpose Y0 = U0 * Matrix.diagonal sig0 * Matrix.transpose V0)
    (hspecX0 : spectralNorm X0 ≤ Real.sqrt (SMax sig0))
    (hspecY0 : spectralNorm Y0 ≤ Real.sqrt (SMax sig0))
    (hrowX0 : twoInfNorm X0 ≤
      Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)))
    (hrowY0 : twoInfNorm Y0 ≤
      Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)))
    (hrowX : twoInfNorm X ≤
      Real.sqrt (CM * SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)))
    (hrowY : twoInfNorm Y ≤
      Real.sqrt (CM * SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)))
    (hdist : frobSq (X - X0) + frobSq (Y - Y0) ≤
      2 * frobSq (X * Matrix.transpose Y - X0 * Matrix.transpose Y0) /
        ((Real.sqrt 2 - 1) * SMin sig0)),
    |p⁻¹ * frobSq (projMask Om (X * Matrix.transpose Y - X0 * Matrix.transpose Y0)) -
        frobSq (X * Matrix.transpose Y - X0 * Matrix.transpose Y0)|
      ≤ (12 / (Real.sqrt 2 - 1)) * kappaOf sig0 *
          (theta + (1 + CM) * Lambda *
            Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) *
            Real.sqrt (mubar * (r : ℝ) / (n : ℝ))) *
        frobSq (X * Matrix.transpose Y - X0 * Matrix.transpose Y0) := by
  /- @proof-region region.target-node.session.2b1540737ec29de7 begin -/
  intro m n r hm hn hr hrn hnm hrm p hp Om hOm U0 V0 hU0 hV0
    sig0 hsig_anti hsig_pos Lambda theta hLambda htheta hMask mubar hmubar CM hCM
    X0 X Y0 Y hX0 hY0 hX0Y0 hspecX0 hspecY0 hrowX0 hrowY0 hrowX hrowY hdist
  set EX : Matrix (Fin m) (Fin r) ℝ := X - X0 with hEX
  set EY : Matrix (Fin n) (Fin r) ℝ := Y - Y0 with hEY
  set DeltaT : Matrix (Fin m) (Fin n) ℝ :=
    X0 * Matrix.transpose EY + EX * Matrix.transpose Y0 with hDeltaT
  set DeltaQ : Matrix (Fin m) (Fin n) ℝ := EX * Matrix.transpose EY with hDeltaQ
  set Delta : Matrix (Fin m) (Fin n) ℝ :=
    X * Matrix.transpose Y - X0 * Matrix.transpose Y0 with hDelta
  have hDelta_split : Delta = DeltaT + DeltaQ := by
    rw [hDelta, hDeltaT, hDeltaQ, hEX, hEY, Matrix.transpose_sub]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hId := (statopia_math_node_3302904835_67c2c5f7 m n hm hn p (ne_of_gt hp) Om hOm).2.2 Delta
  rw [hId]
  have hIT_add_l : ∀ (A A' B : Matrix (Fin m) (Fin n) ℝ),
      innerTrace (A + A') B = innerTrace A B + innerTrace A' B := by
    intro A A' B
    simp only [innerTrace, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  have hIT_add_r : ∀ (A B B' : Matrix (Fin m) (Fin n) ℝ),
      innerTrace A (B + B') = innerTrace A B + innerTrace A B' := by
    intro A B B'
    simp only [innerTrace, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  have hPM_add : ∀ A A' : Matrix (Fin m) (Fin n) ℝ,
      projMask Om (A + A') = projMask Om A + projMask Om A' := by
    intro A A'
    ext i j
    simp [projMask, Matrix.add_apply, mul_add]
  have hTOm_add : ∀ A A' : Matrix (Fin m) (Fin n) ℝ,
      TOm p Om (A + A') = TOm p Om A + TOm p Om A' := by
    intro A A'
    simp only [TOm, hPM_add, smul_add]
    abel
  have hsymm : ∀ A B : Matrix (Fin m) (Fin n) ℝ, innerTrace A B = innerTrace B A :=
    fun A B => (statopia_math_node_3302904835_67c2c5f7 m n hm hn p (ne_of_gt hp) Om hOm).1 A B
  have hself : ∀ A B : Matrix (Fin m) (Fin n) ℝ,
      innerTrace (TOm p Om A) B = innerTrace A (TOm p Om B) :=
    fun A B => (statopia_math_node_3302904835_67c2c5f7 m n hm hn p (ne_of_gt hp) Om hOm).2.1 A B
  have hQexp :
      innerTrace (TOm p Om Delta) Delta
        = innerTrace (TOm p Om DeltaT) DeltaT
          + 2 * (innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ
                 + innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ)
          + innerTrace (TOm p Om DeltaQ) DeltaQ := by
    have hcross : innerTrace (TOm p Om DeltaQ) DeltaT
        = innerTrace (TOm p Om DeltaT) DeltaQ :=
      (hself DeltaQ DeltaT).trans (hsymm DeltaQ (TOm p Om DeltaT))
    have hsplit : innerTrace (TOm p Om DeltaT) DeltaQ
        = innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ
          + innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ := by
      rw [hDeltaT, hTOm_add, hIT_add_l]
    simp only [hDelta_split, hTOm_add, hIT_add_l, hIT_add_r]
    rw [hcross]
    simp only [hsplit]
    ring
  rw [hQexp]
  have hDeltaT_mem : DeltaT ∈ tangentSpace U0 V0 := by
    have hmem : DeltaT =
        U0 * Matrix.transpose (EY * Matrix.diagonal (fun t => Real.sqrt (sig0 t)))
          + (EX * Matrix.diagonal (fun t => Real.sqrt (sig0 t))) * Matrix.transpose V0 := by
      rw [hDeltaT, hX0, hY0]
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [hmem]
    apply Submodule.subset_span
    exact ⟨EY * Matrix.diagonal (fun t => Real.sqrt (sig0 t)),
      EX * Matrix.diagonal (fun t => Real.sqrt (sig0 t)), rfl⟩
  have hSchur :=
    (statopia_math_node_4099765160_cf18766e m n p Om Lambda theta (tangentSpace U0 V0) hLambda hMask).2
  have hTT : |innerTrace (TOm p Om DeltaT) DeltaT| ≤ theta * frob DeltaT ^ 2 := by
    have h := hMask.2.2.2 DeltaT hDeltaT_mem
    rwa [hsymm DeltaT (TOm p Om DeltaT)] at h
  have hTQ0 : |innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ|
      ≤ Lambda * twoInfNorm X0 * twoInfNorm EY * frob EX * frob EY := by
    rw [hDeltaQ, hsymm (TOm p Om (X0 * Matrix.transpose EY)) (EX * Matrix.transpose EY)]
    exact hSchur r r X0 EY EX EY
  have hTQ1 : |innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ|
      ≤ Lambda * twoInfNorm EX * twoInfNorm Y0 * frob EX * frob EY := by
    rw [hDeltaQ, hsymm (TOm p Om (EX * Matrix.transpose Y0)) (EX * Matrix.transpose EY)]
    exact hSchur r r EX Y0 EX EY
  have hQQ : |innerTrace (TOm p Om DeltaQ) DeltaQ|
      ≤ Lambda * twoInfNorm EX * twoInfNorm EY * frob EX * frob EY := by
    rw [hDeltaQ, hsymm (TOm p Om (EX * Matrix.transpose EY)) (EX * Matrix.transpose EY)]
    exact hSchur r r EX EY EX EY
  have frobSq_nonneg : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ), 0 ≤ frobSq A := by
    intro a b A
    simp only [frobSq]
    refine Finset.sum_nonneg (fun i _ => ?_)
    refine Finset.sum_nonneg (fun j _ => ?_)
    positivity
  have frob_sq : frob DeltaT ^ 2 = frobSq DeltaT := by
    rw [frob, Real.sq_sqrt (frobSq_nonneg DeltaT)]
  have hEXEY : frob EX * frob EY ≤ frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0) := by
    have hprod : frob EX * frob EY = Real.sqrt (frobSq EX * frobSq EY) := by
      unfold frob
      exact (Real.sqrt_mul (frobSq_nonneg EX) (frobSq EY)).symm
    rw [hprod]
    calc Real.sqrt (frobSq EX * frobSq EY)
        ≤ (frobSq EX + frobSq EY) / 2 := by
          have h1 : frobSq EX * frobSq EY ≤ ((frobSq EX + frobSq EY) / 2) ^ 2 := by
            nlinarith [sq_nonneg (frobSq EX - frobSq EY)]
          have h2 := Real.sqrt_le_sqrt h1
          rwa [Real.sqrt_sq (div_nonneg (by linarith [frobSq_nonneg EX, frobSq_nonneg EY])
            (by norm_num : (0:ℝ) ≤ 2))] at h2
      _ ≤ frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0) := by
          calc (frobSq EX + frobSq EY) / 2
              = (frobSq EX + frobSq EY) * (1/2) := by ring
            _ ≤ (2 * frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0)) * (1/2) :=
                mul_le_mul_of_nonneg_right hdist (by norm_num : (0:ℝ) ≤ 1/2)
            _ = frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0) := by ring
  have hSmax_nonneg : 0 ≤ SMax sig0 := by
    have hbdd : BddAbove (Set.range sig0) := (Set.finite_range sig0).bddAbove
    have hbddl : BddBelow (Set.range sig0) := (Set.finite_range sig0).bddBelow
    have h1 : SMin sig0 ≤ sig0 ⟨0, by omega⟩ := ciInf_le hbddl ⟨0, by omega⟩
    have h2 : sig0 ⟨0, by omega⟩ ≤ SMax sig0 := le_ciSup hbdd ⟨0, by omega⟩
    have h3 : 0 < sig0 ⟨0, by omega⟩ := lt_of_lt_of_le hsig_pos h1
    linarith
  have hSmax_sqrt_sq : Real.sqrt (SMax sig0) * Real.sqrt (SMax sig0) = SMax sig0 := by
    rw [← pow_two, Real.sq_sqrt hSmax_nonneg]
  have hCM_nonneg : 0 ≤ CM := le_trans (by norm_num) hCM
  have hCM_sqrt_sq : Real.sqrt CM * Real.sqrt CM = CM := by
    rw [← pow_two, Real.sq_sqrt hCM_nonneg]

  have twoInfNorm_sub_le : ∀ {a b : ℕ} (ha : 0 < a) (A B : Matrix (Fin a) (Fin b) ℝ),
      twoInfNorm (A - B) ≤ twoInfNorm A + twoInfNorm B := by
    intro a b ha A B
    have hbddA : BddAbove (Set.range (fun i : Fin a => Real.sqrt (∑ j, A i j ^ 2))) :=
      (Set.finite_range _).bddAbove
    have hbddB : BddAbove (Set.range (fun i : Fin a => Real.sqrt (∑ j, B i j ^ 2))) :=
      (Set.finite_range _).bddAbove
    have hAnonneg : 0 ≤ twoInfNorm A :=
      le_trans (Real.sqrt_nonneg _) (le_ciSup hbddA ⟨0, ha⟩)
    have hBnonneg : 0 ≤ twoInfNorm B :=
      le_trans (Real.sqrt_nonneg _) (le_ciSup hbddB ⟨0, ha⟩)
    have hrow_norm : ∀ (M : Matrix (Fin a) (Fin b) ℝ) (k : Fin a),
        ‖(EuclideanSpace.equiv (Fin b) ℝ).symm (fun j => M k j)‖
          = Real.sqrt (∑ j, M k j ^ 2) := by
      intro M k
      have hof : ((EuclideanSpace.equiv (Fin b) ℝ).symm (fun j => M k j)).ofLp = (fun j => M k j) :=
        rfl
      rw [← Real.sqrt_sq (norm_nonneg _), Statlib.HighDim.MatrixAnalysis.col_norm_sq]
      simp only [hof]
    refine Real.iSup_le (fun i => ?_) (add_nonneg hAnonneg hBnonneg)
    have hrowA : Real.sqrt (∑ j, A i j ^ 2) ≤ twoInfNorm A := le_ciSup hbddA i
    have hrowB : Real.sqrt (∑ j, B i j ^ 2) ≤ twoInfNorm B := le_ciSup hbddB i
    have hsub : (EuclideanSpace.equiv (Fin b) ℝ).symm (fun j => (A - B) i j)
        = (EuclideanSpace.equiv (Fin b) ℝ).symm (fun j => A i j)
          - (EuclideanSpace.equiv (Fin b) ℝ).symm (fun j => B i j) := by
      rw [show (fun j => (A - B) i j) = (fun j => A i j) - (fun j => B i j) from by
        ext j; simp [Matrix.sub_apply]]
      exact map_sub _ _ _
    have htri : Real.sqrt (∑ j, (A - B) i j ^ 2)
        ≤ Real.sqrt (∑ j, A i j ^ 2) + Real.sqrt (∑ j, B i j ^ 2) := by
      rw [← hrow_norm (A - B) i, ← hrow_norm A i, ← hrow_norm B i, hsub]
      exact norm_sub_le _ _
    linarith [htri, hrowA, hrowB]
  have hDeltaTsq : frobSq DeltaT ≤
      4 * (SMax sig0 / SMin sig0) * frobSq Delta / (Real.sqrt 2 - 1) := by
    have frobSq_transpose : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ),
        frobSq (Matrix.transpose M) = frobSq M := by
      intro a b M
      simp only [frobSq, Matrix.transpose_apply]
      exact Finset.sum_comm
    have frobSq_add_two : ∀ (P Q : Matrix (Fin m) (Fin n) ℝ),
        frobSq (P + Q) ≤ 2 * (frobSq P + frobSq Q) := by
      intro P Q
      have hper : ∀ (a b : ℝ), (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
        intro a b; nlinarith only [sq_nonneg (a - b)]
      simp only [frobSq]
      calc ∑ i, ∑ j, ((P + Q) i j) ^ 2
          ≤ ∑ i, ∑ j, 2 * (P i j ^ 2 + Q i j ^ 2) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hper (P i j) (Q i j)))
        _ = 2 * (∑ i, ∑ j, P i j ^ 2 + ∑ i, ∑ j, Q i j ^ 2) := by
            have inner : ∀ (i : Fin m), (∑ j, 2 * (P i j ^ 2 + Q i j ^ 2))
                = 2 * (∑ j, P i j ^ 2 + ∑ j, Q i j ^ 2) := by
              intro i
              rw [← Finset.mul_sum, Finset.sum_add_distrib]
            simp only [inner]
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have hspecX0_sq : spectralNorm X0 ^ 2 ≤ SMax sig0 := by
      have hnn : 0 ≤ spectralNorm X0 := Statlib.HighDim.MatrixAnalysis.opNorm_nonneg X0
      have hsnn : 0 ≤ Real.sqrt (SMax sig0) := Real.sqrt_nonneg _
      have h1 : spectralNorm X0 * spectralNorm X0 ≤ Real.sqrt (SMax sig0) * spectralNorm X0 :=
        mul_le_mul_of_nonneg_right hspecX0 hnn
      have h2 : Real.sqrt (SMax sig0) * spectralNorm X0 ≤ Real.sqrt (SMax sig0) * Real.sqrt (SMax sig0) :=
        mul_le_mul_of_nonneg_left hspecX0 hsnn
      have h3 := le_trans h1 h2
      rw [hSmax_sqrt_sq] at h3
      rw [← pow_two] at h3
      exact h3
    have hspecY0_sq : spectralNorm Y0 ^ 2 ≤ SMax sig0 := by
      have hnn : 0 ≤ spectralNorm Y0 := Statlib.HighDim.MatrixAnalysis.opNorm_nonneg Y0
      have hsnn : 0 ≤ Real.sqrt (SMax sig0) := Real.sqrt_nonneg _
      have h1 : spectralNorm Y0 * spectralNorm Y0 ≤ Real.sqrt (SMax sig0) * spectralNorm Y0 :=
        mul_le_mul_of_nonneg_right hspecY0 hnn
      have h2 : Real.sqrt (SMax sig0) * spectralNorm Y0 ≤ Real.sqrt (SMax sig0) * Real.sqrt (SMax sig0) :=
        mul_le_mul_of_nonneg_left hspecY0 hsnn
      have h3 := le_trans h1 h2
      rw [hSmax_sqrt_sq] at h3
      rw [← pow_two] at h3
      exact h3
    have hfrobX0EY : frobSq (X0 * Matrix.transpose EY) ≤ SMax sig0 * frobSq EY :=
      le_trans (statopia_math_node_2004537962_c9e99f7f m n r X0 EY)
        (mul_le_mul_of_nonneg_right hspecX0_sq (frobSq_nonneg EY))
    have hfrobEXY0 : frobSq (EX * Matrix.transpose Y0) ≤ SMax sig0 * frobSq EX := by
      have hchild := statopia_math_node_2004537962_c9e99f7f n m r Y0 EX
      have htrans : frobSq (EX * Matrix.transpose Y0) = frobSq (Y0 * Matrix.transpose EX) := by
        rw [show EX * Matrix.transpose Y0 = Matrix.transpose (Y0 * Matrix.transpose EX) from by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose]]
        exact frobSq_transpose (Y0 * Matrix.transpose EX)
      rw [htrans]
      exact le_trans hchild (mul_le_mul_of_nonneg_right hspecY0_sq (frobSq_nonneg EX))
    have hcombine : frobSq DeltaT ≤ 2 * (SMax sig0 * frobSq EY + SMax sig0 * frobSq EX) := by
      rw [hDeltaT]
      refine le_trans (frobSq_add_two (X0 * Matrix.transpose EY) (EX * Matrix.transpose Y0)) ?_
      exact mul_le_mul_of_nonneg_left (add_le_add hfrobX0EY hfrobEXY0) (by norm_num : (0:ℝ) ≤ 2)
    have hdist' : frobSq EX + frobSq EY ≤
        2 * frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0) := by
      rw [hEX, hEY, hDelta]
      exact hdist
    calc frobSq DeltaT
        ≤ 2 * (SMax sig0 * frobSq EY + SMax sig0 * frobSq EX) := hcombine
      _ = 2 * SMax sig0 * (frobSq EX + frobSq EY) := by ring
      _ ≤ 2 * SMax sig0 * (2 * frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0)) :=
          mul_le_mul_of_nonneg_left hdist' (by linarith only [hSmax_nonneg])
      _ = 4 * (SMax sig0 / SMin sig0) * frobSq Delta / (Real.sqrt 2 - 1) := by
          rw [div_eq_mul_inv, mul_inv_rev]
          ring
  have hrowEX : twoInfNorm EX ≤
      (1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ))) := by
    have h := twoInfNorm_sub_le hm X X0
    rw [← hEX] at h
    have hbL : Real.sqrt (CM * SMax sig0) = Real.sqrt CM * Real.sqrt (SMax sig0) :=
      Real.sqrt_mul (le_trans (by norm_num) hCM) (SMax sig0)
    refine le_trans h ?_
    calc twoInfNorm X + twoInfNorm X0
        ≤ Real.sqrt (CM * SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ))
          + Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) :=
          add_le_add hrowX hrowX0
      _ = (1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ))) := by
          rw [hbL]; ring
  have hrowEY : twoInfNorm EY ≤
      (1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))) := by
    have h := twoInfNorm_sub_le hn Y Y0
    rw [← hEY] at h
    have hbR : Real.sqrt (CM * SMax sig0) = Real.sqrt CM * Real.sqrt (SMax sig0) :=
      Real.sqrt_mul (le_trans (by norm_num) hCM) (SMax sig0)
    refine le_trans h ?_
    calc twoInfNorm Y + twoInfNorm Y0
        ≤ Real.sqrt (CM * SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))
          + Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)) :=
          add_le_add hrowY hrowY0
      _ = (1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))) := by
          rw [hbR]; ring
  have hTTterm : theta * frob DeltaT ^ 2
      ≤ 4 * (SMax sig0 / SMin sig0) * theta * frobSq Delta / (Real.sqrt 2 - 1) := by
    rw [frob_sq]
    calc theta * frobSq DeltaT
        ≤ theta * (4 * (SMax sig0 / SMin sig0) * frobSq Delta / (Real.sqrt 2 - 1)) :=
          mul_le_mul_of_nonneg_left hDeltaTsq htheta
      _ = 4 * (SMax sig0 / SMin sig0) * theta * frobSq Delta / (Real.sqrt 2 - 1) := by ring
  have hAbs : |(innerTrace (TOm p Om DeltaT) DeltaT
        + 2 * (innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ
               + innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ))
        + innerTrace (TOm p Om DeltaQ) DeltaQ|
      ≤ |innerTrace (TOm p Om DeltaT) DeltaT|
        + 2 * (|innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ|
               + |innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ|)
        + |innerTrace (TOm p Om DeltaQ) DeltaQ| := by
    have h1 := abs_add_le
      (innerTrace (TOm p Om DeltaT) DeltaT + 2 * (innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ + innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ))
      (innerTrace (TOm p Om DeltaQ) DeltaQ)
    have h2 := abs_add_le (innerTrace (TOm p Om DeltaT) DeltaT)
      (2 * (innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ + innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ))
    have h3 : |2 * (innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ + innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ)| = 2 * |innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ + innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h4 := abs_add_le (innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ) (innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ)
    linarith [h1, h2, h3, h4]
  have hstep1 : |innerTrace (TOm p Om DeltaT) DeltaT
        + 2 * (innerTrace (TOm p Om (X0 * Matrix.transpose EY)) DeltaQ
               + innerTrace (TOm p Om (EX * Matrix.transpose Y0)) DeltaQ)
        + innerTrace (TOm p Om DeltaQ) DeltaQ|
      ≤ theta * frob DeltaT ^ 2
        + 2 * (Lambda * twoInfNorm X0 * twoInfNorm EY * frob EX * frob EY
               + Lambda * twoInfNorm EX * twoInfNorm Y0 * frob EX * frob EY)
      + Lambda * twoInfNorm EX * twoInfNorm EY * frob EX * frob EY := by
    refine le_trans hAbs ?_
    linarith [hTT, hTQ0, hTQ1, hQQ]
  refine le_trans hstep1 ?_
  have twoInfNorm_nonneg : ∀ {a b : ℕ} (ha : 0 < a) (A : Matrix (Fin a) (Fin b) ℝ),
      0 ≤ twoInfNorm A := by
    intro a b ha A
    have hbdd : BddAbove (Set.range (fun i : Fin a => Real.sqrt (∑ j, A i j ^ 2))) :=
      (Set.finite_range _).bddAbove
    have h := le_ciSup hbdd (⟨0, ha⟩ : Fin a)
    exact le_trans (Real.sqrt_nonneg _) h
  have hB0 : Lambda * twoInfNorm X0 * twoInfNorm EY * frob EX * frob EY
      ≤ Lambda * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)))
          * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))))
          * (frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0)) := by
    have htEYnn : 0 ≤ twoInfNorm EY := twoInfNorm_nonneg hn EY
    have hfnn : 0 ≤ frob EX * frob EY :=
      mul_nonneg (Real.sqrt_nonneg (frobSq EX)) (Real.sqrt_nonneg (frobSq EY))
    rw [show Lambda * twoInfNorm X0 * twoInfNorm EY * frob EX * frob EY
        = (Lambda * twoInfNorm X0 * twoInfNorm EY) * (frob EX * frob EY) from by ring]
    refine mul_le_mul ?_ hEXEY hfnn ?_
    · have hinner : Lambda * twoInfNorm X0 * twoInfNorm EY
          ≤ Lambda * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)))
              * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)))) := by
        rw [show Lambda * twoInfNorm X0 * twoInfNorm EY
            = (Lambda * twoInfNorm X0) * twoInfNorm EY from by ring]
        refine mul_le_mul ?_ hrowEY htEYnn ?_
        · exact mul_le_mul_of_nonneg_left hrowX0 hLambda
        · positivity
      exact hinner
    · positivity
  have hB1 : Lambda * twoInfNorm EX * twoInfNorm Y0 * frob EX * frob EY
      ≤ Lambda * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ))))
          * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)))
          * (frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0)) := by
    have htY0nn : 0 ≤ twoInfNorm Y0 := twoInfNorm_nonneg hn Y0
    have hfnn : 0 ≤ frob EX * frob EY :=
      mul_nonneg (Real.sqrt_nonneg (frobSq EX)) (Real.sqrt_nonneg (frobSq EY))
    rw [show Lambda * twoInfNorm EX * twoInfNorm Y0 * frob EX * frob EY
        = (Lambda * twoInfNorm EX * twoInfNorm Y0) * (frob EX * frob EY) from by ring]
    refine mul_le_mul ?_ hEXEY hfnn ?_
    · have hinner : Lambda * twoInfNorm EX * twoInfNorm Y0
          ≤ Lambda * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ))))
              * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))) := by
        rw [show Lambda * twoInfNorm EX * twoInfNorm Y0
            = (Lambda * twoInfNorm EX) * twoInfNorm Y0 from by ring]
        refine mul_le_mul ?_ hrowY0 htY0nn ?_
        · exact mul_le_mul_of_nonneg_left hrowEX hLambda
        · positivity
      exact hinner
    · positivity
  have hB2 : Lambda * twoInfNorm EX * twoInfNorm EY * frob EX * frob EY
      ≤ Lambda * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ))))
          * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))))
          * (frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0)) := by
    have htEYnn : 0 ≤ twoInfNorm EY := twoInfNorm_nonneg hn EY
    have hfnn : 0 ≤ frob EX * frob EY :=
      mul_nonneg (Real.sqrt_nonneg (frobSq EX)) (Real.sqrt_nonneg (frobSq EY))
    rw [show Lambda * twoInfNorm EX * twoInfNorm EY * frob EX * frob EY
        = (Lambda * twoInfNorm EX * twoInfNorm EY) * (frob EX * frob EY) from by ring]
    refine mul_le_mul ?_ hEXEY hfnn ?_
    · have hinner : Lambda * twoInfNorm EX * twoInfNorm EY
          ≤ Lambda * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ))))
              * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)))) := by
        rw [show Lambda * twoInfNorm EX * twoInfNorm EY
            = (Lambda * twoInfNorm EX) * twoInfNorm EY from by ring]
        refine mul_le_mul ?_ hrowEY htEYnn ?_
        · exact mul_le_mul_of_nonneg_left hrowEX hLambda
        · positivity
      exact hinner
    · positivity

  have hBsum :
      4 * (SMax sig0 / SMin sig0) * theta * frobSq Delta / (Real.sqrt 2 - 1)
        + 2 * ((Lambda * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)))
              * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))))
              * (frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0)))
            + (Lambda * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ))))
              * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ)))
              * (frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0))))
        + Lambda * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (m : ℝ))))
            * ((1 + Real.sqrt CM) * (Real.sqrt (SMax sig0) * Real.sqrt (mubar * (r : ℝ) / (n : ℝ))))
            * (frobSq Delta / ((Real.sqrt 2 - 1) * SMin sig0))
      ≤ (12 / (Real.sqrt 2 - 1)) * (SMax sig0 / SMin sig0) *
          (theta + (1 + CM) * Lambda * Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) *
            Real.sqrt (mubar * (r : ℝ) / (n : ℝ))) *
          frobSq Delta := by
    set rS : ℝ := Real.sqrt (SMax sig0) with hrSdef
    set u : ℝ := Real.sqrt CM with hudef
    set bL : ℝ := Real.sqrt (mubar * (r : ℝ) / (m : ℝ)) with hbLdef
    set bR : ℝ := Real.sqrt (mubar * (r : ℝ) / (n : ℝ)) with hbRdef
    have hrSsq : rS * rS = SMax sig0 := by rw [hrSdef]; exact hSmax_sqrt_sq
    have husq : u * u = CM := by rw [hudef]; exact hCM_sqrt_sq
    have hBt : Lambda * (rS * bL) * ((1 + u) * (rS * bR))
        = Lambda * ((1 + u) * (SMax sig0 * (bL * bR))) := by
      rw [show Lambda * (rS * bL) * ((1 + u) * (rS * bR))
          = Lambda * (rS * rS) * (bL * bR) * (1 + u) from by ring, hrSsq]
      ring
    have hCt : Lambda * ((1 + u) * (rS * bL)) * (rS * bR)
        = Lambda * ((1 + u) * (SMax sig0 * (bL * bR))) := by
      rw [show Lambda * ((1 + u) * (rS * bL)) * (rS * bR)
          = Lambda * (rS * rS) * (bL * bR) * (1 + u) from by ring, hrSsq]
      ring
    have hDt : Lambda * ((1 + u) * (rS * bL)) * ((1 + u) * (rS * bR))
        = Lambda * ((1 + u) * ((1 + u) * (SMax sig0 * (bL * bR)))) := by
      rw [show Lambda * ((1 + u) * (rS * bL)) * ((1 + u) * (rS * bR))
          = Lambda * (rS * rS) * (bL * bR) * ((1 + u) * (1 + u)) from by ring, hrSsq]
      ring
    rw [hBt, hCt, hDt, ← husq]
    have hbLnn : 0 ≤ bL := by rw [hbLdef]; exact Real.sqrt_nonneg _
    have hbRnn : 0 ≤ bR := by rw [hbRdef]; exact Real.sqrt_nonneg _
    have hLR : 0 ≤ Lambda * bL * bR := mul_nonneg (mul_nonneg hLambda hbLnn) hbRnn
    have hβpos : 0 < Real.sqrt 2 - 1 := sub_pos.mpr Real.one_lt_sqrt_two
    have hK : 0 ≤ SMax sig0 * (SMin sig0)⁻¹ * frobSq Delta * (Real.sqrt 2 - 1)⁻¹ := by
      have h1 : 0 ≤ (SMin sig0)⁻¹ := inv_nonneg.mpr (le_of_lt hsig_pos)
      have h2 : 0 ≤ (Real.sqrt 2 - 1)⁻¹ := inv_nonneg.mpr (le_of_lt hβpos)
      exact mul_nonneg (mul_nonneg (mul_nonneg hSmax_nonneg h1) (frobSq_nonneg Delta)) h2
    have hscalar : 4 * theta + (5 + 6 * u + u * u) * Lambda * bL * bR
        ≤ 12 * (theta + (1 + u * u) * Lambda * bL * bR) := by
      have hquad : 0 ≤ 7 - 6 * u + 11 * (u * u) := by nlinarith only [sq_nonneg (11 * u - 3)]
      have hprod : 0 ≤ (7 - 6 * u + 11 * (u * u)) * (Lambda * bL * bR) := mul_nonneg hquad hLR
      linarith only [hprod, htheta]
    refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_left hscalar hK) (le_of_eq ?_))
    · simp only [div_eq_mul_inv, mul_inv_rev]; ring
    · simp only [div_eq_mul_inv, mul_inv_rev]; ring
  have hk : kappaOf sig0 = SMax sig0 / SMin sig0 := rfl
  rw [hk]
  linarith only [hBsum, hB0, hB1, hB2, hTTterm]
  /- @proof-region region.target-node.session.2b1540737ec29de7 end -/

end

end Statlib.Imported

