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
theorem statopia_math_node_2454385512_63790049 : ∀ (r : ℕ) (sig0 : Fin r → ℝ) (m n : ℕ)
    (p CM mu0 mu1 : ℝ) (hr : 1 ≤ r) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (hCM : 1 ≤ CM) (hlog : 0 ≤ Real.log (m : ℝ)) (hkappa : 0 ≤ kappaOf sig0)
    (hbarMu : 0 ≤ barMuOf mu0 mu1)
    (hnp : npCondition (16 * (max 1 (12 / (Real.sqrt 2 - 1))) ^ 4 * (1 + CM) ^ 2)
      mu0 mu1 sig0 p m n),
    agMain (max 1 (12 / (Real.sqrt 2 - 1))) mu0 mu1 sig0 CM
      (LambdaOf (max 1 (12 / (Real.sqrt 2 - 1))) m p)
      (thetaOf (max 1 (12 / (Real.sqrt 2 - 1))) mu0 r m n p) m n ≤ 1 / 2 := by
  /- @proof-region region.target-node.session.79a21d8984e2ff71 begin -/
  intro r sig0 m n p CM mu0 mu1 hr hm hn hp hCM hlog hkappa hbarMu hnp
  set C : ℝ := max 1 (12 / (Real.sqrt 2 - 1))
  set κ : ℝ := kappaOf sig0
  set mbar : ℝ := barMuOf mu0 mu1
  let S : ℝ := mbar * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)
  let T : ℝ := mbar * (r : ℝ) / Real.sqrt ((n : ℝ) * p)
  have hSdef : S = mbar * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p) := rfl
  have hTdef : T = mbar * (r : ℝ) / Real.sqrt ((n : ℝ) * p) := rfl
  have hC1 : (1 : ℝ) ≤ C := le_max_left 1 (12 / (Real.sqrt 2 - 1))
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have h1CM : (0 : ℝ) < 1 + CM := by linarith
  have hKP : (0 : ℝ) < 16 * C ^ 4 * (1 + CM) ^ 2 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hCpos 4)) (pow_pos h1CM 2)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hnp_pos : (0 : ℝ) < (n : ℝ) * p := mul_pos hnR hp
  have hmn_pos : (0 : ℝ) < (m : ℝ) * (n : ℝ) := mul_pos hmR hnR
  have hS0 : (0 : ℝ) ≤ S := by
    rw [hSdef]
    exact div_nonneg (mul_nonneg (mul_nonneg hbarMu hr0) hlog) hnp_pos.le
  have hT0 : (0 : ℝ) ≤ T := by
    rw [hTdef]
    exact div_nonneg (mul_nonneg hbarMu hr0) (Real.sqrt_nonneg _)
  have hpne : p ≠ 0 := ne_of_gt hp
  have hmnne : Real.sqrt ((m : ℝ) * (n : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hmn_pos)
  have hnpne : Real.sqrt ((n : ℝ) * p) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnp_pos)
  have hs1 : Real.sqrt ((m : ℝ) / p) * Real.sqrt ((n : ℝ) * p) = Real.sqrt ((m : ℝ) * (n : ℝ)) := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ (m : ℝ) / p by positivity)]
    congr 1
    rw [div_mul_eq_mul_div, div_eq_iff hpne]
    ring
  have hratio : Real.sqrt ((m : ℝ) / p) / Real.sqrt ((m : ℝ) * (n : ℝ)) = 1 / Real.sqrt ((n : ℝ) * p) := by
    rw [eq_div_iff hnpne]
    have h1 : Real.sqrt ((m : ℝ) / p) / Real.sqrt ((m : ℝ) * (n : ℝ)) * Real.sqrt ((n : ℝ) * p)
        = Real.sqrt ((m : ℝ) / p) * Real.sqrt ((n : ℝ) * p) / Real.sqrt ((m : ℝ) * (n : ℝ)) := by ring
    rw [h1, hs1, div_self hmnne]
  have hZ : LambdaOf C m p * (mbar * (r : ℝ)) / Real.sqrt ((m : ℝ) * (n : ℝ)) = C * T := by
    rw [hTdef]
    simp only [LambdaOf]
    calc C * Real.sqrt ((m : ℝ) / p) * (mbar * (r : ℝ)) / Real.sqrt ((m : ℝ) * (n : ℝ))
        = C * (mbar * (r : ℝ)) * (Real.sqrt ((m : ℝ) / p) / Real.sqrt ((m : ℝ) * (n : ℝ))) := by ring
      _ = C * (mbar * (r : ℝ)) * (1 / Real.sqrt ((n : ℝ) * p)) := by rw [hratio]
      _ = C * (mbar * (r : ℝ) / Real.sqrt ((n : ℝ) * p)) := by ring
  have hθ : thetaOf C mu0 r m n p ≤ C * Real.sqrt S := by
    rw [hSdef]
    simp only [thetaOf]
    refine mul_le_mul_of_nonneg_left ?_ hCpos.le
    refine Real.sqrt_le_sqrt ?_
    have hnum : mu0 * (r : ℝ) * Real.log (m : ℝ) ≤ mbar * (r : ℝ) * Real.log (m : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left mu0 mu1) hr0) hlog
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hnp_pos.le)
  have hstep : C * κ * (thetaOf C mu0 r m n p + (1 + CM) * LambdaOf C m p * (mbar * (r : ℝ)) / Real.sqrt ((m : ℝ) * (n : ℝ)))
      ≤ C * κ * (C * Real.sqrt S + (1 + CM) * (C * T)) := by
    have hκC : (0 : ℝ) ≤ C * κ := mul_nonneg hCpos.le hkappa
    refine mul_le_mul_of_nonneg_left ?_ hκC
    have hZ2 : (1 + CM) * LambdaOf C m p * (mbar * (r : ℝ)) / Real.sqrt ((m : ℝ) * (n : ℝ)) = (1 + CM) * (C * T) := by
      have h3 : (1 + CM) * LambdaOf C m p * (mbar * (r : ℝ)) / Real.sqrt ((m : ℝ) * (n : ℝ))
          = (1 + CM) * (LambdaOf C m p * (mbar * (r : ℝ)) / Real.sqrt ((m : ℝ) * (n : ℝ))) := by ring
      rw [h3, hZ]
    linarith [hθ, hZ2]
  have hstep2 : C * κ * (C * Real.sqrt S + (1 + CM) * (C * T))
      ≤ C ^ 2 * (1 + CM) * κ * (Real.sqrt S + T) := by
    have hCM0 : (0 : ℝ) ≤ CM := by linarith
    have h1 : (0 : ℝ) ≤ C ^ 2 * κ * Real.sqrt S * CM :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C) hkappa) (Real.sqrt_nonneg S)) hCM0
    have hdiff : C ^ 2 * (1 + CM) * κ * (Real.sqrt S + T) - C * κ * (C * Real.sqrt S + (1 + CM) * (C * T))
        = C ^ 2 * κ * Real.sqrt S * CM := by ring
    linarith [h1, hdiff]
  have hTeq : T ^ 2 = mbar ^ 2 * (r : ℝ) ^ 2 / ((n : ℝ) * p) := by
    rw [hTdef, div_pow, Real.sq_sqrt hnp_pos.le]
    ring
  have hSeqq : S + T ^ 2 = (mbar * (r : ℝ) * Real.log (m : ℝ) + mbar ^ 2 * (r : ℝ) ^ 2) / ((n : ℝ) * p) := by
    rw [hSdef, hTeq, add_div]
  have hST : κ ^ 2 * (S + T ^ 2) ≤ 1 / (16 * C ^ 4 * (1 + CM) ^ 2) := by
    have hA : κ ^ 2 * (S + T ^ 2)
        = κ ^ 2 * (mbar * (r : ℝ) * Real.log (m : ℝ) + mbar ^ 2 * (r : ℝ) ^ 2) / ((n : ℝ) * p) := by
      rw [hSeqq, ← mul_div_assoc]
    rw [hA, div_le_iff₀ hnp_pos]
    rw [show (1 / (16 * C ^ 4 * (1 + CM) ^ 2)) * ((n : ℝ) * p)
        = ((n : ℝ) * p) / (16 * C ^ 4 * (1 + CM) ^ 2) by ring]
    rw [le_div_iff₀ hKP]
    have hnp' : 16 * C ^ 4 * (1 + CM) ^ 2 * κ ^ 2 * (mbar * (r : ℝ) * Real.log (m : ℝ) + mbar ^ 2 * (r : ℝ) ^ 2) ≤ (n : ℝ) * p := by
      have h := hnp
      simp only [npCondition] at h
      exact h
    have hcomm : κ ^ 2 * (mbar * (r : ℝ) * Real.log (m : ℝ) + mbar ^ 2 * (r : ℝ) ^ 2) * (16 * C ^ 4 * (1 + CM) ^ 2)
        = 16 * C ^ 4 * (1 + CM) ^ 2 * κ ^ 2 * (mbar * (r : ℝ) * Real.log (m : ℝ) + mbar ^ 2 * (r : ℝ) ^ 2) := by ring
    linarith [hnp', hcomm]
  have hsplit : κ ^ 2 * (S + T ^ 2) = κ ^ 2 * S + κ ^ 2 * T ^ 2 := by ring
  have hκ2S : κ ^ 2 * S ≤ 1 / (16 * C ^ 4 * (1 + CM) ^ 2) := by
    have h2 : (0 : ℝ) ≤ κ ^ 2 * T ^ 2 := mul_nonneg (sq_nonneg κ) (sq_nonneg T)
    linarith [hST, hsplit, h2]
  have hκ2T : κ ^ 2 * T ^ 2 ≤ 1 / (16 * C ^ 4 * (1 + CM) ^ 2) := by
    have h2 : (0 : ℝ) ≤ κ ^ 2 * S := mul_nonneg (sq_nonneg κ) hS0
    linarith [hST, hsplit, h2]
  have hkS : κ * Real.sqrt S ≤ Real.sqrt (1 / (16 * C ^ 4 * (1 + CM) ^ 2)) := by
    calc κ * Real.sqrt S = Real.sqrt (κ ^ 2) * Real.sqrt S := by rw [Real.sqrt_sq hkappa]
      _ = Real.sqrt (κ ^ 2 * S) := by rw [Real.sqrt_mul (sq_nonneg κ)]
      _ ≤ Real.sqrt (1 / (16 * C ^ 4 * (1 + CM) ^ 2)) := Real.sqrt_le_sqrt hκ2S
  have hkT : κ * T ≤ Real.sqrt (1 / (16 * C ^ 4 * (1 + CM) ^ 2)) := by
    calc κ * T = Real.sqrt (κ ^ 2) * Real.sqrt (T ^ 2) := by rw [Real.sqrt_sq hkappa, Real.sqrt_sq hT0]
      _ = Real.sqrt (κ ^ 2 * T ^ 2) := by rw [Real.sqrt_mul (sq_nonneg κ)]
      _ ≤ Real.sqrt (1 / (16 * C ^ 4 * (1 + CM) ^ 2)) := Real.sqrt_le_sqrt hκ2T
  have hsum2 : κ * Real.sqrt S + κ * T ≤ 2 * Real.sqrt (1 / (16 * C ^ 4 * (1 + CM) ^ 2)) := by
    linarith [hkS, hkT]
  have hfin1 : C ^ 2 * (1 + CM) * (κ * Real.sqrt S + κ * T)
      ≤ C ^ 2 * (1 + CM) * (2 * Real.sqrt (1 / (16 * C ^ 4 * (1 + CM) ^ 2))) := by
    have h0 : (0 : ℝ) ≤ C ^ 2 * (1 + CM) := mul_nonneg (sq_nonneg C) h1CM.le
    exact mul_le_mul_of_nonneg_left hsum2 h0
  have hfin2 : C ^ 2 * (1 + CM) * (2 * Real.sqrt (1 / (16 * C ^ 4 * (1 + CM) ^ 2))) = 1 / 2 := by
    have hsq : 1 / (16 * C ^ 4 * (1 + CM) ^ 2) = (1 / (4 * C ^ 2 * (1 + CM))) ^ 2 := by
      field_simp
      ring
    rw [hsq, Real.sqrt_sq (show (0 : ℝ) ≤ 1 / (4 * C ^ 2 * (1 + CM)) by positivity)]
    field_simp
    ring
  have hfin3 : C ^ 2 * (1 + CM) * κ * (Real.sqrt S + T) ≤ 1 / 2 := by
    have hdist : C ^ 2 * (1 + CM) * κ * (Real.sqrt S + T)
        = C ^ 2 * (1 + CM) * (κ * Real.sqrt S + κ * T) := by ring
    linarith [hdist, hfin1, hfin2]
  have hag1 : agMain C mu0 mu1 sig0 CM (LambdaOf C m p) (thetaOf C mu0 r m n p) m n
      = C * κ * (thetaOf C mu0 r m n p + (1 + CM) * LambdaOf C m p * mbar * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) := rfl
  have hag2 : C * κ * (thetaOf C mu0 r m n p + (1 + CM) * LambdaOf C m p * mbar * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)))
      = C * κ * (thetaOf C mu0 r m n p + (1 + CM) * LambdaOf C m p * (mbar * (r : ℝ)) / Real.sqrt ((m : ℝ) * (n : ℝ))) := by ring
  rw [hag1, hag2]
  exact le_trans hstep (le_trans hstep2 hfin3)
  /- @proof-region region.target-node.session.79a21d8984e2ff71 end -/

end

end Statlib.Imported

