import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2688295946_9f415b7c_0ae0088e
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3037409400_ac6c94eb_d1e4dbc8
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
theorem statopia_math_node_1558896730_aca48620 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
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
        ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
    (hHsub : ∀ w : H, HScale bH mu (alpha - s) w → ∃ a : H, Gammah a = w)
    (hLG_all_range : ∀ (x : X) (u : U), UScale e lam (1 - st) u →
      ∃ w : H, Gammah w = LG x u), ∃ (mubar : ℝ) (kappa : ℝ), 1 ≤ mubar ∧ 0 ≤ kappa ∧
        ∀ (x x' : X) (y y' : H) (u : U),
          HScale bH mu (alpha - s) y → HScale bH mu (alpha - s) y' →
          UScale e lam (1 - st) u →
          |Phi Gammaih LG u x y - Phi Gammaih LG u x y'| ≤
              kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y y') *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) ∧
          |Phi Gammaih LG u x y - Phi Gammaih LG u x' y| ≤
              (Real.rpow mubar st * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) +
                  kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0)) *
                ENNReal.toReal (HScaleDist bH mu st (Gammaih (LG x u - LG x' u)) 0) ∧
          ENNReal.toReal (HScaleDist bH mu st (Gammaih (LG x u - LG x' u)) 0) ≤
            2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
  /- @proof-region region.target-node.session.986adaef310a2e59 begin -/
  classical
  intro U _ _ H _ _ X _ _ e lam hlam_pos iotaH _ bH mu hmu_pos C1 hC1_eigen Gamma hGamma_pos
    hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left LG
    s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg hs1_lt hs1_lt_s hs_le hs0_lt_st hst_le
    halpha C1c hC1c M1 hM1_mono hM1_nonneg hA1 hA2 hHsub hLG_all_range
  have hGammah_inj : ∀ v : H, Gammah v = 0 → v = 0 := by
    intro v hv
    exact hGamma_inj v (by rw [← hGammah_sq, hv, map_zero])
  have htoolA := statopia_math_node_3037409400_ac6c94eb bH mu hmu_pos (alpha - s)
  have htoolS := statopia_math_node_3037409400_ac6c94eb bH mu hmu_pos st
  have hsub_as : ∀ z z' : H, HScaleNorm bH mu (alpha - s) z < ⊤ →
      HScaleNorm bH mu (alpha - s) z' < ⊤ → HScaleNorm bH mu (alpha - s) (z - z') < ⊤ :=
    htoolA.2.1
  have hsub_st : ∀ z z' : H, HScaleNorm bH mu st z < ⊤ →
      HScaleNorm bH mu st z' < ⊤ → HScaleNorm bH mu st (z - z') < ⊤ := htoolS.2.1
  have hpair : ∀ p q : H, HScaleNorm bH mu (-st) p < ⊤ → HScaleNorm bH mu st q < ⊤ →
      |inner ℝ p q| ≤ (HScaleNorm bH mu (-st) p).toReal ^ (1 / 2 : ℝ) *
        (HScaleNorm bH mu st q).toReal ^ (1 / 2 : ℝ) := htoolS.2.2.1
  have htri : ∀ p q : H, HScaleNorm bH mu st p < ⊤ → HScaleNorm bH mu st q < ⊤ →
      (HScaleDist bH mu st (p - q) 0).toReal ≤
        (HScaleDist bH mu st p 0).toReal + (HScaleDist bH mu st q 0).toReal := htoolS.2.2.2
  have hC1bound := statopia_math_node_2688295946_9f415b7c H iotaH bH mu hmu_pos C1 hC1_eigen
  have hnorm_le : ∀ (t : ℝ), 0 ≤ t → ∀ z : H, HScaleNorm bH mu t z < ⊤ →
      ‖z‖ ≤ Real.rpow (max 1 ‖C1‖) (t / 2) * (HScaleDist bH mu t z 0).toReal := hC1bound.2.2
  have hfinK : ∃ K : ℝ, 0 ≤ K ∧ (FiniteDimensional ℝ H → ∀ z v : H,
      HScaleNorm bH mu (alpha - s) z < ⊤ → HScaleNorm bH mu st v < ⊤ →
      |inner ℝ (Gammaih z) v| ≤
        K * ((HScaleDist bH mu (alpha - s) z 0).toReal * (HScaleDist bH mu st v 0).toReal)) := by
    by_cases hfd : FiniteDimensional ℝ H
    · haveI : FiniteDimensional ℝ H := hfd
      obtain ⟨K, hK0, hK⟩ := statopia_math_node_628101960_eb0c6fc8 (H := H) (ι := iotaH)
        bH mu hmu_pos (T := alpha - s) (st := st) (by linarith) Gammah hGammah_inj Gammaih
        hGammaih_left
      refine ⟨K, hK0, fun _ z v hz hv => ?_⟩
      have hne1 : (HScaleNorm bH mu (alpha - s) z) ^ (1 / 2 : ℝ) ≠ ⊤ :=
        ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < (1/2:ℝ))).mpr hz).ne
      have hne2 : (HScaleNorm bH mu st v) ^ (1 / 2 : ℝ) ≠ ⊤ :=
        ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < (1/2:ℝ))).mpr hv).ne
      have hne : ENNReal.ofReal K * (HScaleNorm bH mu (alpha - s) z) ^ (1 / 2 : ℝ) *
          (HScaleNorm bH mu st v) ^ (1 / 2 : ℝ) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne1) hne2
      have hb := ENNReal.toReal_mono hne (hK z v)
      simp only [HScaleDist, sub_zero, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal hK0, ENNReal.toReal_ofReal (abs_nonneg _)] at hb ⊢
      simpa only [mul_assoc] using hb
    · exact ⟨0, le_refl 0, fun h' => absurd h' hfd⟩
  obtain ⟨Kfin, hKfin0, hKfin⟩ := hfinK
  refine ⟨max 1 ‖C1‖, max C1c Kfin, le_max_left 1 ‖C1‖,
    le_trans (le_of_lt hC1c) (le_max_left C1c Kfin), ?_⟩
  intro x x' y y' u hy hy' hu
  have hA2v : (HScaleNorm bH mu st (Gammaih (LG x u))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := hA2 x u hu
  have hA2v' : (HScaleNorm bH mu st (Gammaih (LG x' u))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := hA2 x' u hu
  have hfinv : HScaleNorm bH mu st (Gammaih (LG x u)) < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < (1/2:ℝ))).mp
      (lt_of_le_of_lt hA2v ENNReal.ofReal_lt_top)
  have hfinv' : HScaleNorm bH mu st (Gammaih (LG x' u)) < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < (1/2:ℝ))).mp
      (lt_of_le_of_lt hA2v' ENNReal.ofReal_lt_top)
  obtain ⟨w, hw⟩ := hLG_all_range x u hu
  obtain ⟨w', hw'⟩ := hLG_all_range x' u hu
  have hv : Gammaih (LG x u) = w := by rw [← hw, hGammaih_left]
  have hv' : Gammaih (LG x' u) = w' := by rw [← hw', hGammaih_left]
  have hVsplit : Gammaih (LG x u - LG x' u) = Gammaih (LG x u) - Gammaih (LG x' u) := by
    have hs : Gammah (w - w') = LG x u - LG x' u := by rw [map_sub, hw, hw']
    rw [← hs, hGammaih_left, hv, hv']
  refine ⟨?_, ?_, ?_⟩
  · have hY : Gammaih (y - y') = Gammaih y - Gammaih y' := by
      obtain ⟨a, ha⟩ := hHsub y hy
      obtain ⟨a', ha'⟩ := hHsub y' hy'
      have hs : Gammah (a - a') = y - y' := by rw [map_sub, ha, ha']
      have h1 : Gammaih y = a := by rw [← ha, hGammaih_left]
      have h2 : Gammaih y' = a' := by rw [← ha', hGammaih_left]
      rw [← hs, hGammaih_left, h1, h2]
    have hPhiA : Phi Gammaih LG u x y - Phi Gammaih LG u x y' =
        -inner ℝ (Gammaih (y - y')) (Gammaih (LG x u)) := by
      simp only [Phi]
      rw [hY, inner_sub_left]
      ring
    have hsymA : (HScaleDist bH mu (alpha - s) y y').toReal =
        (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) := by
      rw [HScaleDist, ← ENNReal.toReal_rpow]
    have hfinA : HScaleNorm bH mu (alpha - s) (y - y') < ⊤ := hsub_as y y' hy hy'
    have hBv : (HScaleNorm bH mu st (Gammaih (LG x u))).toReal ^ (1 / 2 : ℝ) ≤
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      have h := ENNReal.toReal_mono (ENNReal.ofReal_lt_top).ne hA2v
      simp only [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (hM1_nonneg _)] at h
      exact h
    have hX : (0 : ℝ) ≤ (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hM : (0 : ℝ) ≤ M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := hM1_nonneg _
    have hkey : |inner ℝ (Gammaih (y - y')) (Gammaih (LG x u))| ≤
        max C1c Kfin * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      by_cases hfd : FiniteDimensional ℝ H
      · have hK := hKfin hfd (y - y') (Gammaih (LG x u)) hfinA hfinv
        have hD : (HScaleDist bH mu (alpha - s) (y - y') 0).toReal =
            (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) := by
          rw [HScaleDist, sub_zero, ← ENNReal.toReal_rpow]
        have hDv : (HScaleDist bH mu st (Gammaih (LG x u)) 0).toReal =
            (HScaleNorm bH mu st (Gammaih (LG x u))).toReal ^ (1 / 2 : ℝ) := by
          rw [HScaleDist, sub_zero, ← ENNReal.toReal_rpow]
        rw [hD, hDv] at hK
        calc |inner ℝ (Gammaih (y - y')) (Gammaih (LG x u))|
            ≤ Kfin * ((HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
                (HScaleNorm bH mu st (Gammaih (LG x u))).toReal ^ (1 / 2 : ℝ)) := hK
          _ ≤ Kfin * ((HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBv hX) hKfin0
          _ ≤ max C1c Kfin * ((HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) :=
              mul_le_mul_of_nonneg_right (le_max_right C1c Kfin) (mul_nonneg hX hM)
          _ = max C1c Kfin * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by ring
      · obtain ⟨hA1fin, hA1le⟩ := hA1 hfd (y - y')
          ((Int.floor (alpha - s1 - 1) : ℤ) : ℝ) hfinA le_rfl
          (by have h := Int.floor_le (alpha - s1 - 1); linarith)
        have hle : (HScaleNorm bH mu (-st) (Gammaih (y - y'))).toReal ^ (1 / 2 : ℝ) ≤
            C1c * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) := by
          have hne : ENNReal.ofReal C1c *
              (HScaleNorm bH mu (alpha - s) (y - y')) ^ (1 / 2 : ℝ) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < (1/2:ℝ))).mpr hfinA).ne
          have h := ENNReal.toReal_mono hne hA1le
          simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
            ENNReal.toReal_ofReal (le_of_lt hC1c)] at h
          exact h
        have hp := hpair (Gammaih (y - y')) (Gammaih (LG x u)) hA1fin hfinv
        have hstep : (HScaleNorm bH mu (-st) (Gammaih (y - y'))).toReal ^ (1 / 2 : ℝ) *
              (HScaleNorm bH mu st (Gammaih (LG x u))).toReal ^ (1 / 2 : ℝ) ≤
            C1c * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
              M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
          have h1 : (HScaleNorm bH mu (-st) (Gammaih (y - y'))).toReal ^ (1 / 2 : ℝ) *
                (HScaleNorm bH mu st (Gammaih (LG x u))).toReal ^ (1 / 2 : ℝ) ≤
              (C1c * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ)) *
                (HScaleNorm bH mu st (Gammaih (LG x u))).toReal ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          have h2 : (C1c * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ)) *
                (HScaleNorm bH mu st (Gammaih (LG x u))).toReal ^ (1 / 2 : ℝ) ≤
              (C1c * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ)) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
            mul_le_mul_of_nonneg_left hBv (mul_nonneg (le_of_lt hC1c) hX)
          calc (HScaleNorm bH mu (-st) (Gammaih (y - y'))).toReal ^ (1 / 2 : ℝ) *
                (HScaleNorm bH mu st (Gammaih (LG x u))).toReal ^ (1 / 2 : ℝ)
              ≤ (C1c * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ)) *
                (HScaleNorm bH mu st (Gammaih (LG x u))).toReal ^ (1 / 2 : ℝ) := h1
            _ ≤ (C1c * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ)) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := h2
            _ = C1c * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by ring
        calc |inner ℝ (Gammaih (y - y')) (Gammaih (LG x u))|
            ≤ (HScaleNorm bH mu (-st) (Gammaih (y - y'))).toReal ^ (1 / 2 : ℝ) *
                (HScaleNorm bH mu st (Gammaih (LG x u))).toReal ^ (1 / 2 : ℝ) := hp
          _ ≤ C1c * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := hstep
          _ ≤ max C1c Kfin * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
              have hlt : (0 : ℝ) ≤
                  (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
                    M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := mul_nonneg hX hM
              nlinarith [hlt, le_max_left C1c Kfin]
    calc |Phi Gammaih LG u x y - Phi Gammaih LG u x y'|
        = |inner ℝ (Gammaih (y - y')) (Gammaih (LG x u))| := by rw [hPhiA, abs_neg]
      _ ≤ max C1c Kfin * (HScaleNorm bH mu (alpha - s) (y - y')).toReal ^ (1 / 2 : ℝ) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := hkey
      _ = max C1c Kfin * ENNReal.toReal (HScaleDist bH mu (alpha - s) y y') *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by rw [hsymA]
  · set X : ℝ := (HScaleDist bH mu st (Gammaih (LG x u - LG x' u)) 0).toReal with hXdef
    set Y : ℝ := (HScaleDist bH mu (alpha - s) y 0).toReal with hYdef
    have hst0 : 0 ≤ st := by linarith
    have hmb1 : (1 : ℝ) ≤ max 1 ‖C1‖ := le_max_left 1 ‖C1‖
    have hmbpos : (0 : ℝ) < max 1 ‖C1‖ := lt_of_lt_of_le zero_lt_one hmb1
    have hRhalf0 : (0 : ℝ) ≤ Real.rpow (max 1 ‖C1‖) (st / 2) :=
      Real.rpow_nonneg (le_of_lt hmbpos) _
    have hX0 : (0 : ℝ) ≤ X := by rw [hXdef]; exact ENNReal.toReal_nonneg
    have hY0 : (0 : ℝ) ≤ Y := by rw [hYdef]; exact ENNReal.toReal_nonneg
    have hXeq : (HScaleNorm bH mu st (Gammaih (LG x u - LG x' u))).toReal ^ (1 / 2 : ℝ) = X := by
      rw [hXdef, HScaleDist, sub_zero, ← ENNReal.toReal_rpow]
    have hYeq : (HScaleNorm bH mu (alpha - s) y).toReal ^ (1 / 2 : ℝ) = Y := by
      rw [hYdef, HScaleDist, sub_zero, ← ENNReal.toReal_rpow]
    have hfinV : HScaleNorm bH mu st (Gammaih (LG x u - LG x' u)) < ⊤ := by
      rw [hVsplit]
      exact hsub_st _ _ hfinv hfinv'
    have hbdv : (HScaleDist bH mu st (Gammaih (LG x u)) 0).toReal ≤
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      have h := ENNReal.toReal_mono (ENNReal.ofReal_lt_top).ne hA2v
      simp only [HScaleDist, sub_zero, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal (hM1_nonneg _)] at h ⊢
      exact h
    have hbdv' : (HScaleDist bH mu st (Gammaih (LG x' u)) 0).toReal ≤
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      have h := ENNReal.toReal_mono (ENNReal.ofReal_lt_top).ne hA2v'
      simp only [HScaleDist, sub_zero, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal (hM1_nonneg _)] at h ⊢
      exact h
    have hnv : ‖Gammaih (LG x u)‖ ≤ Real.rpow (max 1 ‖C1‖) (st / 2) *
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
      le_trans (hnorm_le st hst0 _ hfinv) (mul_le_mul_of_nonneg_left hbdv hRhalf0)
    have hnv' : ‖Gammaih (LG x' u)‖ ≤ Real.rpow (max 1 ‖C1‖) (st / 2) *
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) :=
      le_trans (hnorm_le st hst0 _ hfinv') (mul_le_mul_of_nonneg_left hbdv' hRhalf0)
    have hnV : ‖Gammaih (LG x u - LG x' u)‖ ≤ Real.rpow (max 1 ‖C1‖) (st / 2) * X := by
      have h := hnorm_le st hst0 (Gammaih (LG x u - LG x' u)) hfinV
      rw [← hXdef] at h
      exact h
    have hsum0 : (0 : ℝ) ≤ ‖Gammaih (LG x u)‖ + ‖Gammaih (LG x' u)‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hfac : ‖Gammaih (LG x u)‖ ^ 2 - ‖Gammaih (LG x' u)‖ ^ 2 =
        (‖Gammaih (LG x u)‖ - ‖Gammaih (LG x' u)‖) *
          (‖Gammaih (LG x u)‖ + ‖Gammaih (LG x' u)‖) := by ring
    have hbase : |‖Gammaih (LG x u)‖ - ‖Gammaih (LG x' u)‖| ≤
        ‖Gammaih (LG x u - LG x' u)‖ := by
      have h := abs_norm_sub_norm_le (Gammaih (LG x u)) (Gammaih (LG x' u))
      rwa [← hVsplit] at h
    have hrpow : Real.rpow (max 1 ‖C1‖) (st / 2) * Real.rpow (max 1 ‖C1‖) (st / 2) =
        Real.rpow (max 1 ‖C1‖) st := by
      have h := Real.rpow_add hmbpos (st / 2) (st / 2)
      rw [show st / 2 + st / 2 = st by ring] at h
      exact h.symm
    have hstep1 : |(1 / 2 : ℝ) * (‖Gammaih (LG x u)‖ ^ 2 - ‖Gammaih (LG x' u)‖ ^ 2)| ≤
        Real.rpow (max 1 ‖C1‖) st * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) * X := by
      have hsq : |‖Gammaih (LG x u)‖ ^ 2 - ‖Gammaih (LG x' u)‖ ^ 2| ≤
          ‖Gammaih (LG x u - LG x' u)‖ *
            (‖Gammaih (LG x u)‖ + ‖Gammaih (LG x' u)‖) := by
        rw [hfac, abs_mul, abs_of_nonneg hsum0]
        exact mul_le_mul_of_nonneg_right hbase hsum0
      have hprod : ‖Gammaih (LG x u - LG x' u)‖ *
            (‖Gammaih (LG x u)‖ + ‖Gammaih (LG x' u)‖) ≤
          (Real.rpow (max 1 ‖C1‖) (st / 2) * X) *
            (Real.rpow (max 1 ‖C1‖) (st / 2) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) +
              Real.rpow (max 1 ‖C1‖) (st / 2) *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) :=
        mul_le_mul hnV (add_le_add hnv hnv') hsum0 (mul_nonneg hRhalf0 hX0)
      have hchain : |‖Gammaih (LG x u)‖ ^ 2 - ‖Gammaih (LG x' u)‖ ^ 2| ≤
          2 * Real.rpow (max 1 ‖C1‖) st *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) * X := by
        calc |‖Gammaih (LG x u)‖ ^ 2 - ‖Gammaih (LG x' u)‖ ^ 2|
            ≤ ‖Gammaih (LG x u - LG x' u)‖ *
                (‖Gammaih (LG x u)‖ + ‖Gammaih (LG x' u)‖) := hsq
          _ ≤ (Real.rpow (max 1 ‖C1‖) (st / 2) * X) *
                (Real.rpow (max 1 ‖C1‖) (st / 2) *
                    M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) +
                  Real.rpow (max 1 ‖C1‖) (st / 2) *
                    M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := hprod
          _ = 2 * Real.rpow (max 1 ‖C1‖) st *
                M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) * X := by
              rw [← hrpow]; ring
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]
      have h := mul_le_mul_of_nonneg_left hchain (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
      linarith
    have hstep2 : |inner ℝ (Gammaih y) (Gammaih (LG x u - LG x' u))| ≤
        max C1c Kfin * Y * X := by
      by_cases hfd : FiniteDimensional ℝ H
      · have hK := hKfin hfd y (Gammaih (LG x u - LG x' u)) hy hfinV
        have hK' : |inner ℝ (Gammaih y) (Gammaih (LG x u - LG x' u))| ≤ Kfin * (Y * X) := by
          rw [hYdef, hXdef]
          exact hK
        calc |inner ℝ (Gammaih y) (Gammaih (LG x u - LG x' u))| ≤ Kfin * (Y * X) := hK'
          _ ≤ max C1c Kfin * (Y * X) :=
              mul_le_mul_of_nonneg_right (le_max_right C1c Kfin) (mul_nonneg hY0 hX0)
          _ = max C1c Kfin * Y * X := by ring
      · obtain ⟨hA1fin, hA1le⟩ := hA1 hfd y ((Int.floor (alpha - s1 - 1) : ℤ) : ℝ) hy le_rfl
          (by have h := Int.floor_le (alpha - s1 - 1); linarith)
        have hleY : (HScaleNorm bH mu (-st) (Gammaih y)).toReal ^ (1 / 2 : ℝ) ≤ C1c * Y := by
          have hne : ENNReal.ofReal C1c * (HScaleNorm bH mu (alpha - s) y) ^ (1 / 2 : ℝ) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < (1/2:ℝ))).mpr hy).ne
          have h := ENNReal.toReal_mono hne hA1le
          simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
            ENNReal.toReal_ofReal (le_of_lt hC1c)] at h
          rw [hYeq] at h
          exact h
        have hp : |inner ℝ (Gammaih y) (Gammaih (LG x u - LG x' u))| ≤
            (HScaleNorm bH mu (-st) (Gammaih y)).toReal ^ (1 / 2 : ℝ) * X := by
          rw [← hXeq]
          exact hpair (Gammaih y) (Gammaih (LG x u - LG x' u)) hA1fin hfinV
        calc |inner ℝ (Gammaih y) (Gammaih (LG x u - LG x' u))|
            ≤ (HScaleNorm bH mu (-st) (Gammaih y)).toReal ^ (1 / 2 : ℝ) * X := hp
          _ ≤ (C1c * Y) * X := mul_le_mul_of_nonneg_right hleY hX0
          _ ≤ max C1c Kfin * Y * X := by
              have h1 : C1c * Y ≤ max C1c Kfin * Y :=
                mul_le_mul_of_nonneg_right (le_max_left C1c Kfin) hY0
              have h3 := mul_le_mul_of_nonneg_right h1 hX0
              linarith
    have hPhiB : Phi Gammaih LG u x y - Phi Gammaih LG u x' y =
        (1 / 2 : ℝ) * (‖Gammaih (LG x u)‖ ^ 2 - ‖Gammaih (LG x' u)‖ ^ 2) -
          inner ℝ (Gammaih y) (Gammaih (LG x u - LG x' u)) := by
      simp only [Phi, hVsplit]
      rw [inner_sub_right]
      ring
    have habs : |Phi Gammaih LG u x y - Phi Gammaih LG u x' y| ≤
        |(1 / 2 : ℝ) * (‖Gammaih (LG x u)‖ ^ 2 - ‖Gammaih (LG x' u)‖ ^ 2)| +
          |inner ℝ (Gammaih y) (Gammaih (LG x u - LG x' u))| := by
      rw [hPhiB]
      have h := abs_add_le ((1 / 2 : ℝ) * (‖Gammaih (LG x u)‖ ^ 2 - ‖Gammaih (LG x' u)‖ ^ 2))
        (-inner ℝ (Gammaih y) (Gammaih (LG x u - LG x' u)))
      simpa only [abs_neg, sub_eq_add_neg] using h
    calc |Phi Gammaih LG u x y - Phi Gammaih LG u x' y|
        ≤ |(1 / 2 : ℝ) * (‖Gammaih (LG x u)‖ ^ 2 - ‖Gammaih (LG x' u)‖ ^ 2)| +
            |inner ℝ (Gammaih y) (Gammaih (LG x u - LG x' u))| := habs
      _ ≤ Real.rpow (max 1 ‖C1‖) st * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) * X +
            max C1c Kfin * Y * X := add_le_add hstep1 hstep2
      _ = (Real.rpow (max 1 ‖C1‖) st * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) +
            max C1c Kfin * Y) * X := by ring
  · have hbd1 : (HScaleDist bH mu st (Gammaih (LG x u)) 0).toReal ≤
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      have h := ENNReal.toReal_mono (ENNReal.ofReal_lt_top).ne hA2v
      simp only [HScaleDist, sub_zero, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal (hM1_nonneg _)] at h ⊢
      exact h
    have hbd2 : (HScaleDist bH mu st (Gammaih (LG x' u)) 0).toReal ≤
        M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      have h := ENNReal.toReal_mono (ENNReal.ofReal_lt_top).ne hA2v'
      simp only [HScaleDist, sub_zero, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal (hM1_nonneg _)] at h ⊢
      exact h
    have htri' := htri (Gammaih (LG x u)) (Gammaih (LG x' u)) hfinv hfinv'
    rw [← hVsplit] at htri'
    linarith
  /- @proof-region region.target-node.session.986adaef310a2e59 end -/

end Statlib.Imported
end

