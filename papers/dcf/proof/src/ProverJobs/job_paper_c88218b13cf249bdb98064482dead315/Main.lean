import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.ExternalNodes.Node_de79d78c6a944a25a489
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.ProvedNodes
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base

namespace PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315

noncomputable section
universe u
open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

theorem paper_c88218b13cf249bdb98064482dead315
    (b : ℝ) (hb : 0 < b) :
    ∃ Kstar : ℝ, 0 < Kstar ∧
      ∀ (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 2 ≤ p)

        (δ : ℕ → ℕ → ℝ) (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
        (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω),
        IsProbabilityMeasure μ →
        ∀ (μX μY : Fin p → ℝ)
          (X : Fin n → Ω → (Fin p → ℝ)) (Y : Fin m → Ω → (Fin p → ℝ))
          (F : Fin n → Ω → (Fin p → ℝ)) (G : Fin m → Ω → (Fin p → ℝ)),
        
        (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) →
        (∀ i, Measurable (F i)) → (∀ i, Measurable (G i)) →
        
        iIndepFun (allVec X Y F G) μ →
        
        (∀ i j, ∫ ω, X i ω j ∂μ = μX j) →
        (∀ i j, ∫ ω, Y i ω j ∂μ = μY j) →
        
        
        (∀ i j, Integrable (fun ω => X i ω j) μ) →
        (∀ i j, Integrable (fun ω => Y i ω j) μ) →
        (∀ i j, Integrable (fun ω => F i ω j) μ) →
        (∀ i j, Integrable (fun ω => G i ω j) μ) →
        
        (∀ i j, Integrable (fun ω => |X i ω j - μX j| ^ 3) μ) →
        (∀ i j, Integrable (fun ω => |Y i ω j - μY j| ^ 3) μ) →
        (∀ i j, Integrable (fun ω => |F i ω j - μX j| ^ 3) μ) →
        (∀ i j, Integrable (fun ω => |G i ω j - μY j| ^ 3) μ) →
        
        (∀ i j k, Integrable (fun ω => (X i ω j - μX j) * (X i ω k - μX k)) μ) →
        (∀ i j k, Integrable (fun ω => (Y i ω j - μY j) * (Y i ω k - μY k)) μ) →
        (∀ i j k, Integrable (fun ω => (F i ω j - μX j) * (F i ω k - μX k)) μ) →
        (∀ i j k, Integrable (fun ω => (G i ω j - μY j) * (G i ω k - μY k)) μ) →
        
        (∀ i, IsGaussian (μ.map (F i))) →
        (∀ i j, ∫ ω, F i ω j ∂μ = μX j) →
        (∀ i, ∀ j k, ∫ ω, (F i ω j - μX j) * (F i ω k - μX k) ∂μ
              = ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂μ) →
        
        (∀ i, IsGaussian (μ.map (G i))) →
        (∀ i j, ∫ ω, G i ω j ∂μ = μY j) →
        (∀ i, ∀ j k, ∫ ω, (G i ω j - μY j) * (G i ω k - μY k) ∂μ
              = ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂μ) →
        
        (∀ j, Integrable (fun ω => (partXY X Y μX μY (δ n m) ω j) ^ 2) μ) →
        (b ≤ ⨅ j : Fin p, ∫ ω, (partXY X Y μX μY (δ n m) ω j) ^ 2 ∂μ) →
        
        rhoStar μ X Y F G μX μY (δ n m) ≤
          Kstar *
            ((Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
                (phi1 * Lstat μ X μX * rhoStar μ X Y F G μX μY (δ n m)
                  + Lstat μ X μX * Real.sqrt (Real.log (p : ℝ))
                  + phi1 * MstatN μ X F μX phi1)
              + (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
                  |δ n m| ^ 3 *
                (phi2 * Lstat μ Y μY * rhoStar μ X Y F G μX μY (δ n m)
                  + Lstat μ Y μY * Real.sqrt (Real.log (p : ℝ))
                  + phi2 * MstatM μ Y G μY phi2 (δ n m))
              + (min phi1 phi2)⁻¹ * Real.sqrt (Real.log (p : ℝ)))
:= by
  /- @proof-region region.root.fc5c94850870 begin -/
  obtain ⟨Cb, hCbpos, hCb⟩ :=
    @_root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.paper_ed515f3f70ec457d86e430f1b91735bf.{u} b hb
  
  
  refine ⟨max 3 (8 * Cb), ?_, ?_⟩
  
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · intro n m p hn hm hp δ phi1 phi2 hphi1 hphi2 Ω inst μ hμ μX μY X Y F G
      hXm hYm hFm hGm hindep hXmean hYmean hXint hYint hFint hGint
      hX3 hY3 hF3 hG3 hXprod hYprod hFprod hGprod
      hFgauss hFmean hFcov hGgauss hGmean hGcov hXY2 hinf
    set rho : ℝ := rhoStar μ X Y F G μX μY (δ n m) with hrhodef
    set B : ℝ :=
      ((Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
          (phi1 * Lstat μ X μX * rho
            + Lstat μ X μX * Real.sqrt (Real.log (p : ℝ))
            + phi1 * MstatN μ X F μX phi1)
        + (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
            |δ n m| ^ 3 *
          (phi2 * Lstat μ Y μY * rho
            + Lstat μ Y μY * Real.sqrt (Real.log (p : ℝ))
            + phi2 * MstatM μ Y G μY phi2 (δ n m))
        + (min phi1 phi2)⁻¹ * Real.sqrt (Real.log (p : ℝ))) with hBdef
    have hρ0 : 0 ≤ rho := by
      rw [hrhodef]
      apply Real.sSup_nonneg
      intro x hx
      obtain ⟨v, -, rfl⟩ := hx
      apply Real.sSup_nonneg
      intro a ha
      obtain ⟨A, -, rfl⟩ := ha
      exact abs_nonneg _
    have hρ1 : rho ≤ 1 := by
      haveI : IsProbabilityMeasure μ := hμ
      rw [hrhodef]
      refine csSup_le ⟨_, ⟨0, by simp, rfl⟩⟩ ?_
      intro x hx
      obtain ⟨v, -, rfl⟩ := hx
      refine csSup_le ⟨_, ⟨hyperRect p (fun _ => (0 : EReal)) (fun _ => (0 : EReal)),
        ⟨fun _ => (0 : EReal), fun _ => (0 : EReal), fun _ => le_refl _, rfl⟩, rfl⟩⟩ ?_
      intro y hy
      obtain ⟨A, -, rfl⟩ := hy
      have hb1 : (0:ℝ) ≤ (μ {ω : Ω | (fun j : Fin p =>
            Real.sqrt v * partXY X Y μX μY (δ n m) ω j
              + Real.sqrt (1 - v) * partFG F G μX μY (δ n m) ω j) ∈ A}).toReal := by
        rw [← MeasureTheory.measureReal_def]
        exact MeasureTheory.measureReal_nonneg
      have hb2 : (μ {ω : Ω | (fun j : Fin p =>
            Real.sqrt v * partXY X Y μX μY (δ n m) ω j
              + Real.sqrt (1 - v) * partFG F G μX μY (δ n m) ω j) ∈ A}).toReal ≤ 1 := by
        rw [← MeasureTheory.measureReal_def]
        exact MeasureTheory.measureReal_le_one
      have hb3 : (0:ℝ) ≤ (μ {ω : Ω | partFG F G μX μY (δ n m) ω ∈ A}).toReal := by
        rw [← MeasureTheory.measureReal_def]
        exact MeasureTheory.measureReal_nonneg
      have hb4 : (μ {ω : Ω | partFG F G μX μY (δ n m) ω ∈ A}).toReal ≤ 1 := by
        rw [← MeasureTheory.measureReal_def]
        exact MeasureTheory.measureReal_le_one
      rw [abs_le]
      constructor <;> linarith
  
    have hLx : 0 ≤ Lstat μ X μX := by
      have hp0 : 0 < p := by omega
      have hbd : BddAbove (Set.range (fun j : Fin p =>
          (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, |X i ω j - μX j| ^ 3 ∂μ)) :=
        (Set.finite_range _).bddAbove
      have h0 : (0:ℝ) ≤ (n : ℝ)⁻¹ * ∑ i : Fin n,
          ∫ ω, |X i ω (⟨0, hp0⟩ : Fin p) - μX (⟨0, hp0⟩ : Fin p)| ^ 3 ∂μ := by
        refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg ?_)
        intro i _
        exact MeasureTheory.integral_nonneg (fun ω =>
          pow_nonneg (abs_nonneg (X i ω (⟨0, hp0⟩ : Fin p) - μX (⟨0, hp0⟩ : Fin p))) 3)
      have hle := le_ciSup hbd (⟨0, hp0⟩ : Fin p)
      rw [Lstat]
      linarith
    have hLy : 0 ≤ Lstat μ Y μY := by
      have hp0 : 0 < p := by omega
      have hbd : BddAbove (Set.range (fun j : Fin p =>
          (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, |Y i ω j - μY j| ^ 3 ∂μ)) :=
        (Set.finite_range _).bddAbove
      have h0 : (0:ℝ) ≤ (m : ℝ)⁻¹ * ∑ i : Fin m,
          ∫ ω, |Y i ω (⟨0, hp0⟩ : Fin p) - μY (⟨0, hp0⟩ : Fin p)| ^ 3 ∂μ := by
        refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg m)) (Finset.sum_nonneg ?_)
        intro i _
        exact MeasureTheory.integral_nonneg (fun ω =>
          pow_nonneg (abs_nonneg (Y i ω (⟨0, hp0⟩ : Fin p) - μY (⟨0, hp0⟩ : Fin p))) 3)
  
      have hle := le_ciSup hbd (⟨0, hp0⟩ : Fin p)
      rw [Lstat]
      linarith
  
    have hmaxnn : ∀ (z c : Fin p → ℝ), 0 ≤ maxCoord z c := by
      intro z c
      have hp0 : 0 < p := by omega
      have hbd : BddAbove (Set.range (fun j : Fin p => |z j - c j|)) :=
        (Set.finite_range _).bddAbove
      have hle := le_ciSup hbd (⟨0, hp0⟩ : Fin p)
      have h0 : (0:ℝ) ≤ |z (⟨0, hp0⟩ : Fin p) - c (⟨0, hp0⟩ : Fin p)| := abs_nonneg _
      rw [maxCoord]
      linarith
    have htrunn : ∀ (Z : Ω → (Fin p → ℝ)) (c : Fin p → ℝ) (lev : ℝ),
        0 ≤ truncThird μ Z c lev := by
      intro Z c lev
      rw [truncThird]
      apply MeasureTheory.integral_nonneg
      intro ω
      change (0:ℝ) ≤ (if lev < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0)
      by_cases h : lev < maxCoord (Z ω) c
      · rw [if_pos h]
        exact pow_nonneg (hmaxnn (Z ω) c) 3
      · rw [if_neg h]
    have hMnn : ∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)) (c : Fin p → ℝ) (lev : ℝ),
        0 ≤ Mstat μ Z c lev := by
      intro k Z c lev
      rw [Mstat]
      refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg k)) (Finset.sum_nonneg ?_)
      intro i _
      exact htrunn (Z i) c lev
    have hMx : 0 ≤ MstatN μ X F μX phi1 := by
      rw [MstatN]
      exact add_nonneg (hMnn n X μX _) (hMnn n F μX _)
    have hMy : 0 ≤ MstatM μ Y G μY phi2 (δ n m) := by
      rw [MstatM]
      by_cases hd : (δ n m) = 0
      · rw [if_pos hd]
      · rw [if_neg hd]
        exact add_nonneg (hMnn m Y μY _) (hMnn m G μY _)
  
  
    have hsp : 0 ≤ Real.sqrt (Real.log (p : ℝ)) := Real.sqrt_nonneg _
    have hφ1 : (0:ℝ) ≤ phi1 := le_trans zero_le_one hphi1
    have hφ2 : (0:ℝ) ≤ phi2 := le_trans zero_le_one hphi2
    have hXin : 0 ≤ phi1 * Lstat μ X μX * rho
        + Lstat μ X μX * Real.sqrt (Real.log (p : ℝ))
        + phi1 * MstatN μ X F μX phi1 := by
      have h1 : 0 ≤ phi1 * Lstat μ X μX * rho := mul_nonneg (mul_nonneg hφ1 hLx) hρ0
      have h2 : 0 ≤ Lstat μ X μX * Real.sqrt (Real.log (p : ℝ)) := mul_nonneg hLx hsp
      have h3 : 0 ≤ phi1 * MstatN μ X F μX phi1 := mul_nonneg hφ1 hMx
      linarith
    have hYin : 0 ≤ phi2 * Lstat μ Y μY * rho
        + Lstat μ Y μY * Real.sqrt (Real.log (p : ℝ))
        + phi2 * MstatM μ Y G μY phi2 (δ n m) := by
      have h1 : 0 ≤ phi2 * Lstat μ Y μY * rho := mul_nonneg (mul_nonneg hφ2 hLy) hρ0
      have h2 : 0 ≤ Lstat μ Y μY * Real.sqrt (Real.log (p : ℝ)) := mul_nonneg hLy hsp
      have h3 : 0 ≤ phi2 * MstatM μ Y G μY phi2 (δ n m) := mul_nonneg hφ2 hMy
      linarith
    have hXt : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ * phi1 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
        (phi1 * Lstat μ X μX * rho + Lstat μ X μX * Real.sqrt (Real.log (p : ℝ))
          + phi1 * MstatN μ X F μX phi1) := by
      have h1 : (0:ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      have h2 : (0:ℝ) ≤ phi1 ^ 2 := sq_nonneg _
      have h3 : (0:ℝ) ≤ (Real.log (p : ℝ)) ^ 2 := sq_nonneg _
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) hXin
    have hYt : 0 ≤ (Real.sqrt (m : ℝ))⁻¹ * phi2 ^ 2 * (Real.log (p : ℝ)) ^ 2 *
        |δ n m| ^ 3 *
        (phi2 * Lstat μ Y μY * rho + Lstat μ Y μY * Real.sqrt (Real.log (p : ℝ))
          + phi2 * MstatM μ Y G μY phi2 (δ n m)) := by
      have h1 : (0:ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      have h2 : (0:ℝ) ≤ phi2 ^ 2 := sq_nonneg _
      have h3 : (0:ℝ) ≤ (Real.log (p : ℝ)) ^ 2 := sq_nonneg _
      have h4 : (0:ℝ) ≤ |δ n m| ^ 3 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) hYin
    have hminpos : 0 < min phi1 phi2 := lt_min (by linarith) (by linarith)
    have hminv : 0 ≤ (min phi1 phi2)⁻¹ := inv_nonneg.2 (le_of_lt hminpos)
    have hC : 0 ≤ (min phi1 phi2)⁻¹ * Real.sqrt (Real.log (p : ℝ)) :=
      mul_nonneg hminv hsp
    have hBnonneg : 0 ≤ B := by
      rw [hBdef]
      linarith [hXt, hYt, hC]
    by_cases hcase : min phi1 phi2 < 2
    · have hhalf : (1:ℝ)/2 ≤ (min phi1 phi2)⁻¹ := by
        have hcancel : min phi1 phi2 * (min phi1 phi2)⁻¹ = 1 :=
          mul_inv_cancel₀ (ne_of_gt hminpos)
        nlinarith [hminpos, le_of_lt hcase, hcancel]
      have hlog : (4:ℝ)/9 ≤ Real.log (p : ℝ) := by
        have h2 : (2:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
        have hlog2 : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) h2
        have h93 : (4:ℝ)/9 < Real.log 2 := by linarith [Real.log_two_gt_d9]
        linarith
      have hsqrt : (2:ℝ)/3 ≤ Real.sqrt (Real.log (p : ℝ)) := by
        have h1 : Real.sqrt ((4:ℝ)/9) ≤ Real.sqrt (Real.log (p : ℝ)) :=
          Real.sqrt_le_sqrt hlog
        have h2 : Real.sqrt ((4:ℝ)/9) = (2:ℝ)/3 := by
          rw [show (4:ℝ)/9 = ((2:ℝ)/3)^2 by norm_num, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2/3)]
        linarith
      have hfin : (1:ℝ)/3 ≤ (min phi1 phi2)⁻¹ * Real.sqrt (Real.log (p : ℝ)) := by
        have hmul := mul_le_mul hhalf hsqrt (by norm_num : (0:ℝ) ≤ 2/3) hminv
        linarith
      have hB1 : (1:ℝ)/3 ≤ B := by
        rw [hBdef]
        linarith [hXt, hYt, hfin]
      have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
      have hK : (3:ℝ) ≤ max 3 (8 * Cb) := le_max_left _ _
      have hmul2 : 3 * B ≤ max 3 (8 * Cb) * B :=
        mul_le_mul_of_nonneg_right hK hB0
      linarith [hρ1, hB1]
  
    · have hK2 : 2 * Real.sqrt 2 * Cb ≤ max 3 (2 * Real.sqrt 2 * Cb) := le_max_right _ _
      have hCbnonneg : 0 ≤ 2 * Real.sqrt 2 * Cb :=
        mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) (le_of_lt hCbpos)
      have hpR : (2:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hDpos : 0 < p + p := by omega
      have hlog2le : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hpR
      have hlog2p : Real.log ((p + p : ℕ) : ℝ) = Real.log 2 + Real.log (p : ℝ) := by
        rw [show ((p + p : ℕ) : ℝ) = 2 * (p : ℝ) by push_cast; ring]
        exact Real.log_mul (by norm_num) (by linarith)
      have hlogDpos : 0 < Real.log ((p + p : ℕ) : ℝ) := by
        rw [hlog2p]
        have h1 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
        linarith
      have hlogDle : Real.log ((p + p : ℕ) : ℝ) ≤ 2 * Real.log (p : ℝ) := by
        rw [hlog2p]
        linarith
      have hXcm : ∀ (i : Fin n) (j : Fin p), Measurable (fun ω => X i ω j) :=
        fun i j => (measurable_pi_apply j).comp (hXm i)
      have hFcm : ∀ (i : Fin n) (j : Fin p), Measurable (fun ω => F i ω j) :=
        fun i j => (measurable_pi_apply j).comp (hFm i)
      have hYcm : ∀ (i : Fin m) (j : Fin p), Measurable (fun ω => Y i ω j) :=
        fun i j => (measurable_pi_apply j).comp (hYm i)
      have hGcm : ∀ (i : Fin m) (j : Fin p), Measurable (fun ω => G i ω j) :=
        fun i j => (measurable_pi_apply j).comp (hGm i)
      haveI : IsProbabilityMeasure μ := hμ
      let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
        if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
        else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩
      have hD1 : 1 ≤ p + p := by omega
      have hcmp := statopia_math_node_2954776716_6ed88160 n m p hn hm hp Ω μ μX μY (δ n m)
        X F Y G hX3 hF3 hY3 hG3 hXcm hFcm hYcm hGcm
      obtain ⟨-, -, -, hLxT, hLyT, -, -, hNT, hMT⟩ := hcmp
      have hext : ∀ (ω : Ω) (j : Fin (p + p)),
          PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.combVec
              n m (δ n m) (T μX) (T μY) (fun i => (T ∘ X i) ω) (fun i => (T ∘ Y i) ω) j
            = partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) (δ n m) ω j := by
        intro ω j
        simp only [
          PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.combVec,
          PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.normSum,
          partXY, normSum]
      have hD := statopia_math_node_1676181909_80e1dfab n m p (by omega) (by omega) (by omega)
        Ω μ μX μY (δ n m) X Y F G hXm hYm hFm hGm hindep hXmean hYmean hXint hYint hFint hGint
        hX3 hY3 hF3 hG3 hXprod hYprod hFprod hGprod hFgauss hFmean hFcov hGgauss hGmean hGcov
      obtain ⟨hXmD, hYmD, hFmD, hGmD, hindepD, hmeX, hmeF, hmeY, hmeG,
        hiX, hiY, hiF, hiG, h3XD, h3YD, h3FD, h3GD, hprX, hprY, hprF, hprG,
        hgF, hgG, hcvF, hcvG⟩ := hD
      have hXcmD : ∀ (i : Fin n) (j : Fin (p + p)), Measurable (fun ω => (T ∘ X i) ω j) :=
        fun i j => (measurable_pi_apply j).comp (hXmD i)
      have hFcmD : ∀ (i : Fin n) (j : Fin (p + p)), Measurable (fun ω => (T ∘ F i) ω j) :=
        fun i j => (measurable_pi_apply j).comp (hFmD i)
      have hYcmD : ∀ (i : Fin m) (j : Fin (p + p)), Measurable (fun ω => (T ∘ Y i) ω j) :=
        fun i j => (measurable_pi_apply j).comp (hYmD i)
      have hGcmD : ∀ (i : Fin m) (j : Fin (p + p)), Measurable (fun ω => (T ∘ G i) ω j) :=
        fun i j => (measurable_pi_apply j).comp (hGmD i)
      have hmlp0 := statopia_math_node_2670649085_3064904c μ
        (fun ω => (T ∘ X (⟨0, hn⟩ : Fin n)) ω (⟨0, hDpos⟩ : Fin (p + p)))
        (hXcmD ⟨0, hn⟩ ⟨0, hDpos⟩) (hiX ⟨0, hn⟩ ⟨0, hDpos⟩)
        (T μX ⟨0, hDpos⟩) (h3XD ⟨0, hn⟩ ⟨0, hDpos⟩)
      have hmlpAll := hmlp0.2.2 n m (p + p) (T μX) (T μY)
        (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i)
        hXcmD hYcmD hFcmD hGcmD hiX hiY hiF hiG h3XD h3YD h3FD h3GD
      obtain ⟨hmlpX, hmlpY, hmlpF, hmlpG⟩ := hmlpAll
      have hJF : ∀ i : Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)),
          PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.jointFam
              (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i) i
            = allVec (fun i => T ∘ X i) (fun i => T ∘ Y i)
                (fun i => T ∘ F i) (fun i => T ∘ G i) i := by
        intro i
        match i with
        | Sum.inl a => rfl
        | Sum.inr (Sum.inl b) => rfl
        | Sum.inr (Sum.inr (Sum.inl c)) => rfl
        | Sum.inr (Sum.inr (Sum.inr e)) => rfl
      have hindepJ : iIndepFun
          (PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.jointFam
            (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i)) μ :=
        (statopia_math_node_1150318497_1ef0c7ba hDpos hn hm Ω μ
          (fun i => T ∘ X i) (fun i => T ∘ F i) (fun i => T ∘ Y i) (fun i => T ∘ G i)
          (Equiv.refl _)
          (PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.jointFam
            (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i))
          hJF).mp hindepD
      have hCG_F := statopia_math_node_1420745056_d05a4859 (p + p) n hDpos hn Ω μ (T μX)
        (fun i => T ∘ X i) (fun i => T ∘ F i) hFmD hgF hmeF hcvF hprX hprF
      have hCG_G := statopia_math_node_1420745056_d05a4859 (p + p) m hDpos hm Ω μ (T μY)
        (fun i => T ∘ Y i) (fun i => T ∘ G i) hGmD hgG hmeG hcvG hprY hprG
      have hDcond := statopia_math_node_1799359223_1d14dae9 p (by omega) n hn m hm Ω μ μX μY (δ n m)
        X Y b hXY2 hinf
  
      obtain ⟨hXY2D, hinfD, -⟩ := hDcond
      have hcint : ∀ j : Fin (p + p), Integrable (fun ω =>
          (PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.combVec
              n m (δ n m) (T μX) (T μY) (fun i => (T ∘ X i) ω) (fun i => (T ∘ Y i) ω) j) ^ 2) μ := by
        intro j
        simpa only [hext] using hXY2D j
      have hclb : ∀ j : Fin (p + p), b ≤ ∫ ω,
          (PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.combVec
              n m (δ n m) (T μX) (T μY) (fun i => (T ∘ X i) ω) (fun i => (T ∘ Y i) ω) j) ^ 2 ∂μ := by
        intro j
        have hbdd : BddBelow (Set.range (fun j : Fin (p + p) =>
            ∫ ω, (partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY)
              (δ n m) ω j) ^ 2 ∂μ)) :=
          ⟨0, fun x hx => by
            obtain ⟨k, rfl⟩ := hx
            exact MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)⟩
        have hle := ciInf_le hbdd j
        simp only [hext]
        exact le_trans hinfD hle
      have hextFG : ∀ (ω : Ω) (j : Fin (p + p)),
          PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.combVec
              n m (δ n m) (T μX) (T μY) (fun i => (T ∘ F i) ω) (fun i => (T ∘ G i) ω) j
            = partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) (δ n m) ω j := by
        intro ω j
        simp only [
          PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.combVec,
          PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.normSum,
          partFG, normSum]
      have hdictX := statopia_math_node_3719264890_eca90103 (p + p) n m hDpos hn hm (δ n m) (T μX) (T μY)
        Ω μ (fun i => T ∘ X i) (fun i => T ∘ F i) (fun i => T ∘ Y i) (fun i => T ∘ G i)
      obtain ⟨-, -, hdictX3⟩ := hdictX
      have hdictY := statopia_math_node_3719264890_eca90103 (p + p) m m hDpos hm hm (δ n m) (T μY) (T μY)
        Ω μ (fun i => T ∘ Y i) (fun i => T ∘ G i) (fun i => T ∘ Y i) (fun i => T ∘ G i)
      obtain ⟨-, -, hdictY3⟩ := hdictY
      have hphi1h : (1:ℝ) ≤ phi1 / 2 := by
        have h2 : (2:ℝ) ≤ phi1 := le_trans (not_lt.mp hcase) (min_le_left _ _)
        linarith
      have hphi2h : (1:ℝ) ≤ phi2 / 2 := by
        have h2 : (2:ℝ) ≤ phi2 := le_trans (not_lt.mp hcase) (min_le_right _ _)
        linarith
      have hLX : PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.LX
          μ n (T μX) (fun i => T ∘ X i) = Lstat μ X μX :=
        ((hdictX3 (phi1 / 2) hphi1h).1).trans hLxT
      have hLY : PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.LY
          μ m (T μY) (fun i => T ∘ Y i) = Lstat μ Y μY :=
        ((hdictY3 (phi2 / 2) hphi2h).1).trans hLyT
      have hMn_le : PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.Mn
          μ n (T μX) (fun i => T ∘ X i) (fun i => T ∘ F i) (phi1 / 2)
          ≤ MstatN μ X F μX phi1 :=
        le_trans (hdictX3 (phi1 / 2) hphi1h).2.1.le (hNT phi1 hphi1)
      have hMs_le : PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.Mstar
          μ m (δ n m) (T μY) (fun i => T ∘ Y i) (fun i => T ∘ G i) (phi2 / 2)
          ≤ MstatM μ Y G μY phi2 (δ n m) := by
        by_cases hd : (δ n m) = 0
        · have h1 : PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.Mstar
              μ m (δ n m) (T μY) (fun i => T ∘ Y i) (fun i => T ∘ G i) (phi2 / 2) = 0 := by
            rw [hd]
            simp
          rw [h1]
          exact hMy
        · have hkey := (hdictX3 (phi2 / 2) hphi2h).2.2
          rw [if_neg hd] at hkey
          refine le_trans ?_ (hMT phi2 hphi2)
          simpa only [
            PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.Mstar,
            PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.MY,
            PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.MG,
            if_neg hd] using hkey.le
  
  
  
      have hEng := hCb Ω μ n m (p + p) δ (T μX) (T μY)
        (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i)
        (phi1 / 2) (phi2 / 2) hn hm hDpos hlogDpos
        hXmD hYmD hFmD hGmD hindepJ hmlpX hmlpY h3XD h3YD h3FD h3GD
        hmeX hmeY hCG_F hCG_G hcint hclb
        (by
          have h2 : (2:ℝ) ≤ phi1 := le_trans (not_lt.mp hcase) (min_le_left _ _)
          linarith)
        (by
          have h2 : (2:ℝ) ≤ phi2 := le_trans (not_lt.mp hcase) (min_le_right _ _)
          linarith)
      have hbr := statopia_math_node_1702548930_dc235873 n m p (by omega) (by omega) (by omega)
        Ω μ μX μY (δ n m) X F Y G hXm hYm hFm hGm
      have hbdd1 : ∀ (s t : Set Ω), |(μ s).toReal - (μ t).toReal| ≤ 1 := by
        intro s t
        have h1 : (0:ℝ) ≤ (μ s).toReal := by
          rw [← MeasureTheory.measureReal_def]
          exact MeasureTheory.measureReal_nonneg
        have h2 : (μ s).toReal ≤ 1 := by
          rw [← MeasureTheory.measureReal_def]
          exact MeasureTheory.measureReal_le_one
        have h3 : (0:ℝ) ≤ (μ t).toReal := by
          rw [← MeasureTheory.measureReal_def]
          exact MeasureTheory.measureReal_nonneg
        have h4 : (μ t).toReal ≤ 1 := by
          rw [← MeasureTheory.measureReal_def]
          exact MeasureTheory.measureReal_le_one
        rw [abs_le]
        constructor <;> linarith
  
  
  
  
  
  
  
  
  
      let GG : ℝ → (Fin (p + p) → ℝ) → ℝ := fun v y =>
        |(μ {ω : Ω | (fun j : Fin (p + p) =>
              Real.sqrt v * partXY (fun i => T ∘ X i) (fun i => T ∘ Y i) (T μX) (T μY) (δ n m) ω j
                + Real.sqrt (1 - v) *
                  partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) (δ n m) ω j) ≤ y}).toReal
          - (μ {ω : Ω | partFG (fun i => T ∘ F i) (fun i => T ∘ G i) (T μX) (T μY) (δ n m) ω ≤ y}).toReal|
      have hbdIn : ∀ v : ℝ, BddAbove (Set.range (GG v)) := fun v =>
        ⟨1, fun x hx => by
          obtain ⟨y, rfl⟩ := hx
          exact hbdd1 _ _⟩
      have hbdOut : BddAbove (Set.range (fun v : Set.Icc (0:ℝ) 1 =>
          (⨆ y : Fin (p + p) → ℝ, GG (v:ℝ) y))) :=
        ⟨1, fun x hx => by
          obtain ⟨v, rfl⟩ := hx
          exact Real.iSup_le (fun y => hbdd1 _ _) (by norm_num)⟩
      have hnn : 0 ≤ (⨆ v : Set.Icc (0:ℝ) 1, ⨆ y : Fin (p + p) → ℝ, GG (v:ℝ) y) :=
        le_trans (abs_nonneg _)
          (le_trans (le_ciSup (hbdIn (0:ℝ)) (fun _ => (0:ℝ)))
            (le_ciSup hbdOut ⟨0, by constructor <;> norm_num⟩))
      have hlogp0 : (0:ℝ) ≤ Real.log (p : ℝ) :=
        le_trans (le_of_lt (by linarith [Real.log_two_gt_d9] : (0:ℝ) < Real.log 2)) hlog2le
  
  
      have hA : rho ≤ PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.rho
          μ n m (p + p) (δ n m) (T μX) (T μY)
          (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i) := by
        rw [hrhodef, ← hbr]
        rw [PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.rho]
        simp only [hext, hextFG]
        refine Real.iSup_le (fun v => ?_) hnn
        refine Real.iSup_le (fun hv => ?_) hnn
        refine Real.iSup_le (fun y => ?_) hnn
        exact le_trans (le_ciSup (hbdIn v) y) (le_ciSup hbdOut ⟨v, hv⟩)
      have hρE0 : 0 ≤ PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.rho
          μ n m (p + p) (δ n m) (T μX) (T μY)
          (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i) :=
        le_trans hρ0 hA
      have hbdProp : ∀ v : ℝ, BddAbove (Set.range (fun _ : v ∈ Set.Icc (0:ℝ) 1 =>
          (⨆ y : Fin (p + p) → ℝ, GG v y))) := by
        intro v
        exact ⟨_, fun x hx => by obtain ⟨i, rfl⟩ := hx; exact le_refl _⟩
      have hbdOut2 : BddAbove (Set.range (fun v : ℝ =>
          (⨆ _ : v ∈ Set.Icc (0:ℝ) 1, ⨆ y : Fin (p + p) → ℝ, GG v y))) :=
        ⟨1, fun x hx => by
          obtain ⟨v, rfl⟩ := hx
          exact Real.iSup_le (fun hv => Real.iSup_le (fun y => hbdd1 _ _) (by norm_num))
            (by norm_num)⟩
      have hnn2 : 0 ≤ (⨆ v : ℝ, ⨆ _ : v ∈ Set.Icc (0:ℝ) 1,
          ⨆ y : Fin (p + p) → ℝ, GG v y) :=
        le_trans (abs_nonneg _)
          (le_trans (le_ciSup (hbdIn 0) (fun _ => (0:ℝ)))
            (le_trans (le_ciSup (hbdProp 0) (by constructor <;> norm_num))
              (le_ciSup hbdOut2 0)))
      have hrev : PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.rho
          μ n m (p + p) (δ n m) (T μX) (T μY)
          (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i)
          ≤ rho := by
        rw [hrhodef, ← hbr]
        rw [PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.rho]
        simp only [hext, hextFG]
        refine Real.iSup_le (fun v => ?_) hnn2
        refine Real.iSup_le (fun y => ?_) hnn2
        exact le_trans (le_ciSup (hbdIn (v:ℝ)) y)
          (le_trans (le_ciSup (hbdProp (v:ℝ)) v.property) (le_ciSup hbdOut2 (v:ℝ)))
  
  
  
      have hρle : rho ≤ 8 * Cb * B := by
        have h2 : PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.rho
            μ n m (p + p) (δ n m) (T μX) (T μY)
            (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i)
            ≤ 8 * Cb * B := by
          rw [hBdef]
          exact statopia_math_node_4109406159_630b7066 Cb
            (Real.sqrt (n : ℝ))⁻¹ (Real.sqrt (m : ℝ))⁻¹ (|δ n m| ^ 3)
  
            (PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.rho
              μ n m (p + p) (δ n m) (T μX) (T μY)
              (fun i => T ∘ X i) (fun i => T ∘ Y i) (fun i => T ∘ F i) (fun i => T ∘ G i))
            rho phi1 phi2
            (PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.LX
              μ n (T μX) (fun i => T ∘ X i))
            (PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.LY
              μ m (T μY) (fun i => T ∘ Y i))
            (PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.Mn
              μ n (T μX) (fun i => T ∘ X i) (fun i => T ∘ F i) (phi1 / 2))
            (PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported.Mstar
              μ m (δ n m) (T μY) (fun i => T ∘ Y i) (fun i => T ∘ G i) (phi2 / 2))
            (Lstat μ X μX) (Lstat μ Y μY) (MstatN μ X F μX phi1)
            (MstatM μ Y G μY phi2 (δ n m))
            (Real.log ((p + p : ℕ) : ℝ)) (Real.log (p : ℝ))
            hCbpos (inv_nonneg.2 (Real.sqrt_nonneg _)) (inv_nonneg.2 (Real.sqrt_nonneg _))
            (by positivity) hρE0 hρ0 hrev
            (le_of_eq hLX) (le_of_eq hLY) hMn_le hMs_le
            hLx hLy hMx hMy
            (by linarith) (by linarith)
            hlogp0 hlogDpos hlogDle hEng
        exact le_trans hA h2
  
  
      have hmul : 8 * Cb * B ≤ max 3 (8 * Cb) * B :=
        mul_le_mul_of_nonneg_right (le_max_right (3:ℝ) (8 * Cb)) hBnonneg
      linarith [hρle, hmul]
  /- @proof-region region.root.fc5c94850870 end -/

end Statlib.Imported

end

-- Paper root revision 92f11ca6-d24b-4c93-947e-9f07945fd04b

