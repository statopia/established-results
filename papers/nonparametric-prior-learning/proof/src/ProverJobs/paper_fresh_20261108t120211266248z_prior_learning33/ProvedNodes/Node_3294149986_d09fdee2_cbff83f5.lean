import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_628101960_eb0c6fc8_752efdfd

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3294149986_d09fdee2 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (iotaH : Type*) [Preorder iotaH] (bH : HilbertBasis iotaH ℝ H) (mu : iotaH → ℝ)
    (hmu_pos : ∀ i : iotaH, 0 < mu i)
    (C1 : H →L[ℝ] H) (hC1_eigen : ∀ i : iotaH, C1 (bH i) = mu i • bH i)
    (Gamma : H →L[ℝ] H) (hGamma_pos : Gamma.IsPositive)
    (hGamma_inj : ∀ v : H, Gamma v = 0 → v = 0)
    (Gammah : H →ₗ[ℝ] H)
    (hGammah_symm : ∀ v w : H, inner ℝ (Gammah v) w = inner ℝ v (Gammah w))
    (hGammah_pos : ∀ v : H, 0 ≤ inner ℝ v (Gammah v))
    (hGammah_sq : ∀ v : H, Gammah (Gammah v) = Gamma v)
    (Gammaih : H → H) (hGammaih_left : ∀ v : H, Gammaih (Gammah v) = v)
    (LG : X → U → H)
    (s0 s1 s st alpha : ℝ)
    (hs0_nonneg : 0 ≤ s0) (hs0_lt : s0 < 1)
    (hs1_nonneg : 0 ≤ s1) (hs1_lt : s1 < 1)
    (hs1_lt_s : s1 < s) (hs_le : s ≤ 1)
    (hs0_lt_st : s0 < st) (hst_le : st ≤ 1) (halpha : 0 ≤ alpha)
    (C1c : ℝ) (hC1c : 0 < C1c)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ r : ℝ, 0 ≤ M1 r)
    (hA1 : (¬ FiniteDimensional ℝ H) → ∀ (w : H) (rhoReal : ℝ),
      HScale bH mu (alpha - s) w →
        ((Int.floor (alpha - s1 - 1) : ℤ) : ℝ) ≤ rhoReal → rhoReal < alpha - s1 →
          HScale bH mu (-st) (Gammaih w) ∧
            (HScaleNorm bH mu (-st) (Gammaih w)) ^ (1 / 2 : ℝ) ≤
              ENNReal.ofReal C1c * (HScaleNorm bH mu (alpha - s) w) ^ (1 / 2 : ℝ))
    (hA2 : ∀ (x : X) (u : U), UScale e lam (1 - st) u →
      (HScaleNorm bH mu st (Gammaih (LG x u))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))), ∃ (mubar : ℝ), 1 ≤ mubar ∧ ∃ (kappa : ℝ), 0 ≤ kappa ∧
        (∀ (x : X) (y : H) (u : U), HScale bH mu (alpha - s) y → UScale e lam (1 - st) u →
          Phi Gammaih LG u x y ≥
            -(kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) *
              M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))) ∧
        (∀ (x : X) (y : H) (u : U), HScale bH mu (alpha - s) y → UScale e lam (1 - st) u →
          Phi Gammaih LG u x y ≤
            (1 / 2 : ℝ) * (mubar ^ st) *
                (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 +
              kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
  /- @proof-region region.target-node.session.e7e832e3e500f6c6 begin -/
  intro U hU hU' H hH hH' X hX hX' e lam hlam_pos iotaH hiotaH bH mu hmu_pos C1
    hC1_eigen Gamma hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq
    Gammaih hGammaih_left LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg hs1_lt
    hs1_lt_s hs_le hs0_lt_st hst_le halpha C1c hC1c M1 hM1_mono hM1_nonneg hA1 hA2
  classical
  have hPair : ∀ a b : H, HScaleNorm bH mu (-st) a < ⊤ → HScaleNorm bH mu st b < ⊤ →
      ENNReal.ofReal |inner ℝ a b| ≤
        (HScaleNorm bH mu (-st) a) ^ (1 / 2 : ℝ) * (HScaleNorm bH mu st b) ^ (1 / 2 : ℝ) := by
    intro a b ha hb
    have hane : HScaleNorm bH mu (-st) a ≠ ⊤ := ne_of_lt ha
    have hbne : HScaleNorm bH mu st b ≠ ⊤ := ne_of_lt hb
    have hxnn : ∀ i : iotaH, (0 : ℝ) ≤ mu i ^ st * (inner ℝ (bH i) a) ^ 2 :=
      fun i => mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu_pos i) st)) (by positivity)
    have hynn : ∀ i : iotaH, (0 : ℝ) ≤ mu i ^ (-st) * (inner ℝ (bH i) b) ^ 2 :=
      fun i => mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (hmu_pos i) (-st))) (by positivity)
    have hXeq : HScaleNorm bH mu (-st) a =
        ∑' i : iotaH, ENNReal.ofReal (mu i ^ st * (inner ℝ (bH i) a) ^ 2) := by
      simp only [HScaleNorm]
      apply tsum_congr
      intro i
      simp only [neg_neg]
      rfl
    have hYeq : HScaleNorm bH mu st b =
        ∑' i : iotaH, ENNReal.ofReal (mu i ^ (-st) * (inner ℝ (bH i) b) ^ 2) := by
      simp only [HScaleNorm]
      apply tsum_congr
      intro i
      rfl
    have hXsum : ∀ s : Finset iotaH,
        (∑ i ∈ s, ENNReal.ofReal (mu i ^ st * (inner ℝ (bH i) a) ^ 2)) =
          ENNReal.ofReal (∑ i ∈ s, mu i ^ st * (inner ℝ (bH i) a) ^ 2) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s his ih =>
          rw [Finset.sum_insert his, Finset.sum_insert his,
            ENNReal.ofReal_add (hxnn i) (Finset.sum_nonneg (fun j _ => hxnn j)), ih]
    have hYsum : ∀ s : Finset iotaH,
        (∑ i ∈ s, ENNReal.ofReal (mu i ^ (-st) * (inner ℝ (bH i) b) ^ 2)) =
          ENNReal.ofReal (∑ i ∈ s, mu i ^ (-st) * (inner ℝ (bH i) b) ^ 2) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s his ih =>
          rw [Finset.sum_insert his, Finset.sum_insert his,
            ENNReal.ofReal_add (hynn i) (Finset.sum_nonneg (fun j _ => hynn j)), ih]
    have hAs : ∀ s : Finset iotaH,
        (∑ i ∈ s, mu i ^ st * (inner ℝ (bH i) a) ^ 2) ≤
          (HScaleNorm bH mu (-st) a).toReal := by
      intro s
      have h1 : (∑ i ∈ s, ENNReal.ofReal (mu i ^ st * (inner ℝ (bH i) a) ^ 2)) ≤
          HScaleNorm bH mu (-st) a := by
        rw [hXeq]
        exact ENNReal.sum_le_tsum s
      have h2 : (ENNReal.ofReal (∑ i ∈ s, mu i ^ st * (inner ℝ (bH i) a) ^ 2)).toReal ≤
          (HScaleNorm bH mu (-st) a).toReal :=
        ENNReal.toReal_mono hane (by rw [← hXsum s]; exact h1)
      rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun j _ => hxnn j))] at h2
    have hBs : ∀ s : Finset iotaH,
        (∑ i ∈ s, mu i ^ (-st) * (inner ℝ (bH i) b) ^ 2) ≤
          (HScaleNorm bH mu st b).toReal := by
      intro s
      have h1 : (∑ i ∈ s, ENNReal.ofReal (mu i ^ (-st) * (inner ℝ (bH i) b) ^ 2)) ≤
          HScaleNorm bH mu st b := by
        rw [hYeq]
        exact ENNReal.sum_le_tsum s
      have h2 : (ENNReal.ofReal (∑ i ∈ s, mu i ^ (-st) * (inner ℝ (bH i) b) ^ 2)).toReal ≤
          (HScaleNorm bH mu st b).toReal :=
        ENNReal.toReal_mono hbne (by rw [← hYsum s]; exact h1)
      rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun j _ => hynn j))] at h2
    have hcs : ∀ s : Finset iotaH,
        (∑ i ∈ s, inner ℝ (bH i) a * inner ℝ (bH i) b) ^ 2 ≤
          (∑ i ∈ s, mu i ^ st * (inner ℝ (bH i) a) ^ 2) *
            (∑ i ∈ s, mu i ^ (-st) * (inner ℝ (bH i) b) ^ 2) := by
      intro s
      have h := Finset.sum_mul_sq_le_sq_mul_sq s
        (fun i => Real.sqrt (mu i ^ st) * inner ℝ (bH i) a)
        (fun i => Real.sqrt (mu i ^ (-st)) * inner ℝ (bH i) b)
      have hA : ∀ i : iotaH, (Real.sqrt (mu i ^ st) * inner ℝ (bH i) a) *
          (Real.sqrt (mu i ^ (-st)) * inner ℝ (bH i) b) =
          inner ℝ (bH i) a * inner ℝ (bH i) b := by
        intro i
        have hp : mu i ^ st * mu i ^ (-st) = 1 := by
          have hx0 : (0 : ℝ) ≤ mu i := le_of_lt (hmu_pos i)
          have hy0 : (0 : ℝ) ≤ (mu i)⁻¹ := inv_nonneg.2 hx0
          rw [Real.rpow_neg_eq_inv_rpow, ← Real.mul_rpow hx0 hy0,
            mul_inv_cancel₀ (ne_of_gt (hmu_pos i)), Real.one_rpow]
        have h1 : Real.sqrt (mu i ^ st) * Real.sqrt (mu i ^ (-st)) = 1 := by
          rw [← Real.sqrt_mul (le_of_lt (Real.rpow_pos_of_pos (hmu_pos i) st)), hp,
            Real.sqrt_one]
        calc (Real.sqrt (mu i ^ st) * inner ℝ (bH i) a) *
              (Real.sqrt (mu i ^ (-st)) * inner ℝ (bH i) b)
            = (Real.sqrt (mu i ^ st) * Real.sqrt (mu i ^ (-st))) *
                (inner ℝ (bH i) a * inner ℝ (bH i) b) := by ring
          _ = inner ℝ (bH i) a * inner ℝ (bH i) b := by rw [h1, one_mul]
      have hB : ∀ i : iotaH, (Real.sqrt (mu i ^ st) * inner ℝ (bH i) a) ^ 2 =
          mu i ^ st * (inner ℝ (bH i) a) ^ 2 := by
        intro i
        rw [mul_pow, Real.sq_sqrt (le_of_lt (Real.rpow_pos_of_pos (hmu_pos i) st))]
      have hC : ∀ i : iotaH, (Real.sqrt (mu i ^ (-st)) * inner ℝ (bH i) b) ^ 2 =
          mu i ^ (-st) * (inner ℝ (bH i) b) ^ 2 := by
        intro i
        rw [mul_pow, Real.sq_sqrt (le_of_lt (Real.rpow_pos_of_pos (hmu_pos i) (-st)))]
      rw [Finset.sum_congr rfl (fun i _ => hA i), Finset.sum_congr rfl (fun i _ => hB i),
        Finset.sum_congr rfl (fun i _ => hC i)] at h
      exact h
    have hc : ∀ s : Finset iotaH,
        |∑ i ∈ s, inner ℝ (bH i) a * inner ℝ (bH i) b| ≤
          Real.sqrt ((HScaleNorm bH mu (-st) a).toReal) *
            Real.sqrt ((HScaleNorm bH mu st b).toReal) := by
      intro s
      have hsq_le : (∑ i ∈ s, inner ℝ (bH i) a * inner ℝ (bH i) b) ^ 2 ≤
          (HScaleNorm bH mu (-st) a).toReal * (HScaleNorm bH mu st b).toReal := by
        have h1 := mul_le_mul (hAs s) (hBs s) (Finset.sum_nonneg (fun j _ => hynn j))
          (le_trans (Finset.sum_nonneg (fun j _ => hxnn j)) (hAs s))
        linarith [hcs s, h1]
      calc |∑ i ∈ s, inner ℝ (bH i) a * inner ℝ (bH i) b|
          = Real.sqrt ((∑ i ∈ s, inner ℝ (bH i) a * inner ℝ (bH i) b) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt ((HScaleNorm bH mu (-st) a).toReal * (HScaleNorm bH mu st b).toReal) :=
            Real.sqrt_le_sqrt hsq_le
        _ = Real.sqrt ((HScaleNorm bH mu (-st) a).toReal) *
              Real.sqrt ((HScaleNorm bH mu st b).toReal) :=
            Real.sqrt_mul (by positivity) _
    have htend : Tendsto (fun s : Finset iotaH =>
        ∑ i ∈ s, inner ℝ (bH i) a * inner ℝ (bH i) b) atTop (𝓝 (inner ℝ a b)) := by
      simpa [real_inner_comm] using HilbertBasis.hasSum_inner_mul_inner bH a b
    have hmain : |inner ℝ a b| ≤ Real.sqrt ((HScaleNorm bH mu (-st) a).toReal) *
        Real.sqrt ((HScaleNorm bH mu st b).toReal) := by
      have h1 : inner ℝ a b ≤ Real.sqrt ((HScaleNorm bH mu (-st) a).toReal) *
          Real.sqrt ((HScaleNorm bH mu st b).toReal) :=
        le_of_tendsto' htend (fun s => le_trans (le_abs_self _) (hc s))
      have h2 : -inner ℝ a b ≤ Real.sqrt ((HScaleNorm bH mu (-st) a).toReal) *
          Real.sqrt ((HScaleNorm bH mu st b).toReal) :=
        le_of_tendsto' htend.neg
          (fun s => le_trans (by linarith [neg_abs_le (∑ i ∈ s, inner ℝ (bH i) a * inner ℝ (bH i) b)]) (hc s))
      by_cases hpos : 0 ≤ inner ℝ a b
      · rwa [abs_of_nonneg hpos]
      · rw [abs_of_neg (not_le.mp hpos)]
        exact h2
    have hXh : (HScaleNorm bH mu (-st) a) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ne_of_lt ((ENNReal.rpow_lt_top_iff_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)).2 ha)
    have hYh : (HScaleNorm bH mu st b) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ne_of_lt ((ENNReal.rpow_lt_top_iff_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)).2 hb)
    rw [← ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hXh hYh),
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    exact hmain
  have hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : X) (y : H) (u : U),
      HScale bH mu (alpha - s) y → UScale e lam (1 - st) u →
      |inner ℝ (Gammaih y) (Gammaih (LG x u))| ≤
        K * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) *
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
    by_cases hfd : FiniteDimensional ℝ H
    · haveI : FiniteDimensional ℝ H := hfd
      have hGammah_inj : ∀ v : H, Gammah v = 0 → v = 0 := by
        intro v hv
        have h1 : Gamma v = 0 := by
          rw [← hGammah_sq, hv]
          exact map_zero Gammah
        exact hGamma_inj v h1
      have hstp : 0 < st := lt_of_le_of_lt hs0_nonneg hs0_lt_st
      obtain ⟨Kf, hKf0, hKfb⟩ :=
        statopia_math_node_628101960_eb0c6fc8 H iotaH bH mu hmu_pos (alpha - s) st hstp
          Gammah hGammah_inj Gammaih hGammaih_left
      refine ⟨Kf, hKf0, ?_⟩
      intro x y u hy hu
      have hXtop : HScaleNorm bH mu (alpha - s) y < ⊤ := hy
      have hXh : (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ) ≠ ⊤ :=
        ne_of_lt ((ENNReal.rpow_lt_top_iff_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)).2 hXtop)
      have hcomb : ENNReal.ofReal |inner ℝ (Gammaih y) (Gammaih (LG x u))| ≤
          (ENNReal.ofReal Kf * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
            ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
        have hp := hKfb y (Gammaih (LG x u))
        have hstep2 : (ENNReal.ofReal Kf * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
            (HScaleNorm bH mu st (Gammaih (LG x u))) ^ (1 / 2 : ℝ) ≤
            (ENNReal.ofReal Kf * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
              ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) :=
          mul_le_mul_left' (hA2 x u hu) _
        exact le_trans hp hstep2
      have hMu0 : (0 : ℝ) ≤ M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := hM1_nonneg _
      have hne1 : (ENNReal.ofReal Kf * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hXh) ENNReal.ofReal_ne_top
      have h1 := ENNReal.toReal_mono hne1 hcomb
      have e2 : ((ENNReal.ofReal Kf * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))).toReal =
          (Kf * ((HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)).toReal) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
        simp only [ENNReal.toReal_mul]
        rw [ENNReal.toReal_ofReal hKf0, ENNReal.toReal_ofReal hMu0]
      have hreal : |inner ℝ (Gammaih y) (Gammaih (LG x u))| ≤
          (Kf * ((HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)).toReal) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
        calc |inner ℝ (Gammaih y) (Gammaih (LG x u))|
            = (ENNReal.ofReal |inner ℝ (Gammaih y) (Gammaih (LG x u))|).toReal :=
              (ENNReal.toReal_ofReal (abs_nonneg _)).symm
          _ ≤ ((ENNReal.ofReal Kf * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
                ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))).toReal := h1
          _ = (Kf * ((HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)).toReal) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := e2
      have hdist : ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) =
          ((HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)).toReal := by
        rw [HScaleDist, sub_zero]
      rw [hdist]
      exact hreal
    · refine ⟨C1c, le_of_lt hC1c, ?_⟩
      intro x y u hy hu
      obtain ⟨hfin1, hbound1⟩ := hA1 hfd y (alpha - s1 - 1) hy (Int.floor_le _) (by linarith)
      have hXtop : HScaleNorm bH mu (alpha - s) y < ⊤ := hy
      have hXh : (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ) ≠ ⊤ :=
        ne_of_lt ((ENNReal.rpow_lt_top_iff_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)).2 hXtop)
      have hfin2 : HScaleNorm bH mu st (Gammaih (LG x u)) < ⊤ := by
        have h1 : (HScaleNorm bH mu st (Gammaih (LG x u))) ^ (1 / 2 : ℝ) ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hA2 x u hu)
        exact (ENNReal.rpow_lt_top_iff_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)).1
          (lt_top_iff_ne_top.2 h1)
      have hpair := hPair (Gammaih y) (Gammaih (LG x u)) hfin1 hfin2
      have hcomb : ENNReal.ofReal |inner ℝ (Gammaih y) (Gammaih (LG x u))| ≤
          (ENNReal.ofReal C1c * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
            ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
        have hstep1 : (HScaleNorm bH mu (-st) (Gammaih y)) ^ (1 / 2 : ℝ) *
            (HScaleNorm bH mu st (Gammaih (LG x u))) ^ (1 / 2 : ℝ) ≤
            (ENNReal.ofReal C1c * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
              (HScaleNorm bH mu st (Gammaih (LG x u))) ^ (1 / 2 : ℝ) :=
          mul_le_mul_right' hbound1 _
        have hstep2 : (ENNReal.ofReal C1c * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
            (HScaleNorm bH mu st (Gammaih (LG x u))) ^ (1 / 2 : ℝ) ≤
            (ENNReal.ofReal C1c * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
              ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) :=
          mul_le_mul_left' (hA2 x u hu) _
        exact le_trans hpair (le_trans hstep1 hstep2)
      have hMu0 : (0 : ℝ) ≤ M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := hM1_nonneg _
      have hne1 : (ENNReal.ofReal C1c * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hXh) ENNReal.ofReal_ne_top
      have h1 := ENNReal.toReal_mono hne1 hcomb
      have e2 : ((ENNReal.ofReal C1c * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))).toReal =
          (C1c * ((HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)).toReal) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
        simp only [ENNReal.toReal_mul]
        rw [ENNReal.toReal_ofReal (le_of_lt hC1c), ENNReal.toReal_ofReal hMu0]
      have hreal : |inner ℝ (Gammaih y) (Gammaih (LG x u))| ≤
          (C1c * ((HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)).toReal) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
        calc |inner ℝ (Gammaih y) (Gammaih (LG x u))|
            = (ENNReal.ofReal |inner ℝ (Gammaih y) (Gammaih (LG x u))|).toReal :=
              (ENNReal.toReal_ofReal (abs_nonneg _)).symm
          _ ≤ ((ENNReal.ofReal C1c * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)) *
                ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))).toReal := h1
          _ = (C1c * ((HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)).toReal) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := e2
      have hdist : ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) =
          ((HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ)).toReal := by
        rw [HScaleDist, sub_zero]
      rw [hdist]
      exact hreal
  obtain ⟨K, hK0, hKb⟩ := hK
  have hParseval : ∀ v : H, HScaleNorm bH mu 0 v = ENNReal.ofReal (‖v‖ ^ 2) := by
    intro v
    have hsum : Summable (fun i : iotaH => (inner ℝ (bH i) v) ^ 2) := by
      refine (HilbertBasis.summable_inner_mul_inner bH v v).congr (fun i => ?_)
      rw [sq, real_inner_comm]
    have htsum : (∑' i : iotaH, (inner ℝ (bH i) v) ^ 2) = ‖v‖ ^ 2 := by
      have hcongr : (∑' i : iotaH, (inner ℝ (bH i) v) ^ 2)
          = ∑' i : iotaH, inner ℝ v (bH i) * inner ℝ (bH i) v := by
        apply tsum_congr
        intro i
        rw [sq, real_inner_comm]
      rw [hcongr, HilbertBasis.tsum_inner_mul_inner bH v v, real_inner_self_eq_norm_sq]
    have hrpow : ∀ i : iotaH, Real.rpow (mu i) (-(0 : ℝ)) = 1 := fun i =>
      show (mu i) ^ (-(0 : ℝ)) = 1 from by simp
    have hstep : ∀ i : iotaH,
        ENNReal.ofReal (Real.rpow (mu i) (-(0 : ℝ)) * (inner ℝ (bH i) v) ^ 2)
          = ENNReal.ofReal ((inner ℝ (bH i) v) ^ 2) := by
      intro i
      rw [hrpow i, one_mul]
    simp only [HScaleNorm]
    rw [tsum_congr hstep, ← ENNReal.ofReal_tsum_of_nonneg
      (f := fun i : iotaH => (inner ℝ (bH i) v) ^ 2) (fun i => by positivity) hsum, htsum]
  have hmubar_pos : 0 < max 1 ‖C1‖ := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖C1‖)
  have hst_pos : 0 < st := lt_of_le_of_lt hs0_nonneg hs0_lt_st
  have hmu_le : ∀ i : iotaH, mu i ≤ max 1 ‖C1‖ := by
    intro i
    have hnorm : ‖bH i‖ = 1 := bH.orthonormal.1 i
    have hinner : inner ℝ (bH i) (bH i) = 1 := by
      rw [real_inner_self_eq_norm_sq, hnorm]
      norm_num
    have heq : mu i = inner ℝ (bH i) (C1 (bH i)) := by
      rw [hC1_eigen i, inner_smul_right, hinner, mul_one]
    have hcs : |inner ℝ (bH i) (C1 (bH i))| ≤ ‖bH i‖ * ‖C1 (bH i)‖ :=
      abs_real_inner_le_norm (bH i) (C1 (bH i))
    have hop : ‖C1 (bH i)‖ ≤ ‖C1‖ * ‖bH i‖ := C1.le_opNorm (bH i)
    have hle : mu i ≤ ‖C1‖ := by
      rw [heq]
      calc inner ℝ (bH i) (C1 (bH i)) ≤ |inner ℝ (bH i) (C1 (bH i))| := le_abs_self _
        _ ≤ ‖bH i‖ * ‖C1 (bH i)‖ := hcs
        _ = ‖C1 (bH i)‖ := by rw [hnorm, one_mul]
        _ ≤ ‖C1‖ * ‖bH i‖ := hop
        _ = ‖C1‖ := by rw [hnorm, mul_one]
    exact le_trans hle (le_max_right 1 ‖C1‖)
  have hVgen : ∀ (v : H) (M : ℝ), 0 ≤ M →
      (HScaleNorm bH mu st v) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal M →
      ‖v‖ ^ 2 ≤ (max 1 ‖C1‖) ^ st * M ^ 2 := by
    intro v M hM0 hM
    have hterm : ∀ i : iotaH,
        ENNReal.ofReal ((max 1 ‖C1‖) ^ (-st) * (inner ℝ (bH i) v) ^ 2)
          ≤ ENNReal.ofReal (Real.rpow (mu i) (-st) * (inner ℝ (bH i) v) ^ 2) := by
      intro i
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
      exact Real.rpow_le_rpow_of_nonpos (hmu_pos i) (hmu_le i) (neg_nonpos.mpr hst_pos.le)
    have hc : (0 : ℝ) ≤ (max 1 ‖C1‖) ^ (-st) :=
      le_of_lt (Real.rpow_pos_of_pos hmubar_pos (-st))
    have hW : ENNReal.ofReal ((max 1 ‖C1‖) ^ (-st)) * ENNReal.ofReal (‖v‖ ^ 2) ≤
        HScaleNorm bH mu st v := by
      have hP0 : ENNReal.ofReal (‖v‖ ^ 2) =
          ∑' i : iotaH, ENNReal.ofReal ((inner ℝ (bH i) v) ^ 2) := by
        rw [← hParseval v]
        have hrpow : ∀ i : iotaH, Real.rpow (mu i) (-(0 : ℝ)) = 1 := fun i =>
          show (mu i) ^ (-(0 : ℝ)) = 1 from by simp
        have hstep' : ∀ i : iotaH,
            ENNReal.ofReal (Real.rpow (mu i) (-(0 : ℝ)) * (inner ℝ (bH i) v) ^ 2)
              = ENNReal.ofReal ((inner ℝ (bH i) v) ^ 2) := by
          intro i
          rw [hrpow i, one_mul]
        simp only [HScaleNorm]
        rw [tsum_congr hstep']
      have hstep : ENNReal.ofReal ((max 1 ‖C1‖) ^ (-st)) * ENNReal.ofReal (‖v‖ ^ 2)
          = ∑' i : iotaH, ENNReal.ofReal ((max 1 ‖C1‖) ^ (-st) * (inner ℝ (bH i) v) ^ 2) := by
        rw [hP0, ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro i
        rw [ENNReal.ofReal_mul hc]
      rw [hstep]
      exact ENNReal.tsum_le_tsum hterm
    have hMtop : ENNReal.ofReal M ≠ ⊤ := ENNReal.ofReal_ne_top
    have hfin : HScaleNorm bH mu st v ≠ ⊤ := by
      have h1 : (HScaleNorm bH mu st v) ^ (1 / 2 : ℝ) ≠ ⊤ := ne_top_of_le_ne_top hMtop hM
      exact ((ENNReal.rpow_lt_top_iff_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)).1
        (lt_top_iff_ne_top.2 h1)).ne
    have hm : (HScaleNorm bH mu st v).toReal ^ (1 / 2 : ℝ) ≤ M := by
      rw [ENNReal.toReal_rpow]
      calc ((HScaleNorm bH mu st v) ^ (1 / 2 : ℝ)).toReal
          ≤ (ENNReal.ofReal M).toReal := ENNReal.toReal_mono hMtop hM
        _ = M := ENNReal.toReal_ofReal hM0
    have hxx : (HScaleNorm bH mu st v).toReal ^ (1 / 2 : ℝ) *
        ((HScaleNorm bH mu st v).toReal ^ (1 / 2 : ℝ)) = (HScaleNorm bH mu st v).toReal := by
      rw [← sq, ← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt (by positivity)
    have hsq2 : (HScaleNorm bH mu st v).toReal ≤ M * M := by
      have h := mul_self_le_mul_self
        (a := (HScaleNorm bH mu st v).toReal ^ (1 / 2 : ℝ)) (b := M)
        (Real.rpow_nonneg (x := (HScaleNorm bH mu st v).toReal) (by positivity) (1 / 2)) hm
      rwa [hxx] at h
    have hS : HScaleNorm bH mu st v ≤ ENNReal.ofReal (M * M) := by
      rw [← ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ M * M)]
      exact hsq2
    have hreal : (max 1 ‖C1‖) ^ (-st) * ‖v‖ ^ 2 ≤ M * M := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (le_trans hW hS)
      rw [ENNReal.toReal_ofReal_mul ((max 1 ‖C1‖) ^ (-st)) (ENNReal.ofReal (‖v‖ ^ 2)) hc,
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ‖v‖ ^ 2),
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ M * M)] at h
      exact h
    have hprod : (max 1 ‖C1‖) ^ st * (max 1 ‖C1‖) ^ (-st) = 1 := by
      have hx0 : (0 : ℝ) ≤ max 1 ‖C1‖ := le_of_lt hmubar_pos
      have hy0 : (0 : ℝ) ≤ (max 1 ‖C1‖)⁻¹ := inv_nonneg.2 hx0
      have hne : max 1 ‖C1‖ ≠ 0 := ne_of_gt hmubar_pos
      rw [Real.rpow_neg_eq_inv_rpow, ← Real.mul_rpow hx0 hy0, mul_inv_cancel₀ hne,
        Real.one_rpow]
    have hpos : (0 : ℝ) < (max 1 ‖C1‖) ^ st := Real.rpow_pos_of_pos hmubar_pos st
    have hgoal : ‖v‖ ^ 2 ≤ (max 1 ‖C1‖) ^ st * (M * M) := by
      have h1 : (max 1 ‖C1‖) ^ st * ((max 1 ‖C1‖) ^ (-st) * ‖v‖ ^ 2) ≤
          (max 1 ‖C1‖) ^ st * (M * M) :=
        mul_le_mul_of_nonneg_left hreal (le_of_lt hpos)
      calc ‖v‖ ^ 2 = (max 1 ‖C1‖) ^ st * ((max 1 ‖C1‖) ^ (-st) * ‖v‖ ^ 2) := by
            rw [← mul_assoc, hprod, one_mul]
        _ ≤ (max 1 ‖C1‖) ^ st * (M * M) := h1
    calc ‖v‖ ^ 2 ≤ (max 1 ‖C1‖) ^ st * (M * M) := hgoal
      _ = (max 1 ‖C1‖) ^ st * M ^ 2 := by rw [sq]
  have hV : ∀ (x : X) (u : U), UScale e lam (1 - st) u →
      ‖Gammaih (LG x u)‖ ^ 2 ≤
        (max 1 ‖C1‖) ^ st *
          (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 := by
    intro x u hu
    exact hVgen (Gammaih (LG x u)) (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))
      (hM1_nonneg _) (hA2 x u hu)
  refine ⟨max 1 ‖C1‖, le_max_left _ _, K, hK0, ?_, ?_⟩
  · intro x y u hy hu
    have h1 := hKb x y u hy hu
    have h2 := neg_abs_le (inner ℝ (Gammaih y) (Gammaih (LG x u)))
    have h4 := le_abs_self (inner ℝ (Gammaih y) (Gammaih (LG x u)))
    have h3 : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖Gammaih (LG x u)‖ ^ 2 := by positivity
    simp only [Phi]
    nlinarith [h1, h2, h3, h4]
  · intro x y u hy hu
    have h1 := hKb x y u hy hu
    have h2 := neg_abs_le (inner ℝ (Gammaih y) (Gammaih (LG x u)))
    have h4 := le_abs_self (inner ℝ (Gammaih y) (Gammaih (LG x u)))
    have h3 := hV x u hu
    simp only [Phi]
    nlinarith [h1, h2, h3, h4]
  /- @proof-region region.target-node.session.e7e832e3e500f6c6 end -/

end Statlib.Imported
end

