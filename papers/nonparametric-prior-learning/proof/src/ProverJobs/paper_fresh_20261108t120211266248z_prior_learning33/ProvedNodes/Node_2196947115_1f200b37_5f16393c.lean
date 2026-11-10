import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

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
theorem statopia_math_node_2196947115_1f200b37 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Type*)
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (iotaH : Type*) [Preorder iotaH] (bH : HilbertBasis iotaH ℝ H) (mu : iotaH → ℝ)
    (Gammaih : H → H) (LG : X → U → H) (s st alpha : ℝ)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ t : ℝ, 0 ≤ M1 t)
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (mubar : ℝ) (hmubar : 1 ≤ mubar)
    (h6 : ∀ (x x' : X) (y y' : H), HScale bH mu (alpha - s) y → HScale bH mu (alpha - s) y' →
      ∀ u : U, UScale e lam (1 - st) u →
      |Phi Gammaih LG u x y - Phi Gammaih LG u x y'| ≤
        kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y y') *
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))
    (h7 : ∀ (x x' : X) (y y' : H), HScale bH mu (alpha - s) y → HScale bH mu (alpha - s) y' →
      ∀ u : U, UScale e lam (1 - st) u →
      |Phi Gammaih LG u x y - Phi Gammaih LG u x' y| ≤
        (Real.rpow mubar st * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) +
          kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0)) *
          ENNReal.toReal (HScaleDist bH mu st (Gammaih (LG x u - LG x' u)) 0))
    (h8 : ∀ (x x' : X) (y y' : H), HScale bH mu (alpha - s) y → HScale bH mu (alpha - s) y' →
      ∀ u : U, UScale e lam (1 - st) u →
      ENNReal.toReal (HScaleDist bH mu st (Gammaih (LG x u - LG x' u)) 0) ≤
        2 * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))
    (beta : ℝ) (hbeta : 0 < beta) (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r)
    (delta1 : ℝ) (hdelta1 : 0 < delta1)
    (Q : Measure U) [IsProbabilityMeasure Q]
    (hQ_scale : Q (UScale e lam (1 - st)) = 1)
    (D Dp : Fin m → X × H)
    (hD : ∀ j : Fin m, HScale bH mu (alpha - s) (D j).2)
    (hDp : ∀ j : Fin m, HScale bH mu (alpha - s) (Dp j).2)
    (hD_rad : ∀ j : Fin m, HScaleDist bH mu (alpha - s) (D j).2 0 ≤ ENNReal.ofReal r)
    (hDp_rad : ∀ j : Fin m, HScaleDist bH mu (alpha - s) (Dp j).2 0 ≤ ENNReal.ofReal r)
    (hEt_int : Integrable (fun u : U => ((UScale e lam (1 - st)).indicator
      (fun v : U => Real.exp (4 * delta1 *
        (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u) Q)
    (hDm : AEMeasurable
      (fun u : U => Real.exp (-(beta / (m : ℝ)) * potSum Gammaih LG D u)) Q)
    (hDmp : AEMeasurable
      (fun u : U => Real.exp (-(beta / (m : ℝ)) * potSum Gammaih LG Dp u)) Q),
    Integrable (fun u : U =>
      |(beta / (m : ℝ)) * potSum Gammaih LG D u -
          (beta / (m : ℝ)) * potSum Gammaih LG Dp u| *
        ((UScale e lam (1 - st)).indicator
          (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)) Q ∧
    Integrable (fun u : U =>
      ((beta / (m : ℝ)) * potSum Gammaih LG D u -
          (beta / (m : ℝ)) * potSum Gammaih LG Dp u) ^ 2 *
        ((UScale e lam (1 - st)).indicator
          (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u)) Q := by
  /- @proof-region region.target-node.session.401dc01bc2d5bc2b begin -/
  intro U _ _ _ H _ _ X e lam iotaH _ bH mu Gammaih LG s st alpha M1 hM1_mono hM1_nonneg kappa hkappa mubar hmubar h6 h7 h8 beta hbeta m hm r hr delta1 hdelta1 Q _ hQ_scale D Dp hD hDp hD_rad hDp_rad hEt_int hDm hDmp
  have hEff_meas : AEMeasurable (fun u : U => (UScale e lam (1 - st)).indicator (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) + delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u) Q := by
    have hE4_ae : AEMeasurable (fun u : U => (UScale e lam (1 - st)).indicator (fun v : U => Real.exp (4 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u) Q :=
      hEt_int.aestronglyMeasurable.aemeasurable
    have hsq1 : AEMeasurable (fun u : U => Real.sqrt ((UScale e lam (1 - st)).indicator (fun v : U => Real.exp (4 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u)) Q :=
      Real.continuous_sqrt.measurable.comp_aemeasurable hE4_ae
    have hsq2 : AEMeasurable (fun u : U => Real.sqrt (Real.sqrt ((UScale e lam (1 - st)).indicator (fun v : U => Real.exp (4 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u))) Q :=
      Real.continuous_sqrt.measurable.comp_aemeasurable hsq1
    have hF_ae : AEMeasurable (fun u : U => Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * Real.sqrt (Real.sqrt ((UScale e lam (1 - st)).indicator (fun v : U => Real.exp (4 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u))) Q :=
      aemeasurable_const.mul hsq2
    have hEff_eq : (fun u : U => (UScale e lam (1 - st)).indicator (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) + delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u) = (fun u : U => Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * Real.sqrt (Real.sqrt ((UScale e lam (1 - st)).indicator (fun v : U => Real.exp (4 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u))) := by
      funext u
      by_cases hu : u ∈ UScale e lam (1 - st)
      · simp only [Set.indicator, if_pos hu]
        set tu : ℝ := M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) with htu
        have hexp4 : Real.exp (4 * delta1 * tu ^ 2) = (Real.exp (2 * delta1 * tu ^ 2)) ^ 2 := by
          rw [show 4 * delta1 * tu ^ 2 = 2 * delta1 * tu ^ 2 + 2 * delta1 * tu ^ 2 from by ring, Real.exp_add]; ring
        have hsqrt1 : Real.sqrt (Real.exp (4 * delta1 * tu ^ 2)) = Real.exp (2 * delta1 * tu ^ 2) := by
          rw [hexp4, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
        have hexp2 : Real.exp (2 * delta1 * tu ^ 2) = (Real.exp (delta1 * tu ^ 2)) ^ 2 := by
          rw [show 2 * delta1 * tu ^ 2 = delta1 * tu ^ 2 + delta1 * tu ^ 2 from by ring, Real.exp_add]; ring
        have hsqrt2 : Real.sqrt (Real.exp (2 * delta1 * tu ^ 2)) = Real.exp (delta1 * tu ^ 2) := by
          rw [hexp2, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [hsqrt1, hsqrt2, ← Real.exp_add]
        rw [show (1 : ℝ) * ((beta * kappa * r) ^ 2 / (4 * delta1) + delta1 * tu ^ 2) = (beta * kappa * r) ^ 2 / (4 * delta1) + delta1 * tu ^ 2 from by ring]
      · simp only [Set.indicator, if_neg hu]
        simp
    rw [hEff_eq]
    exact hF_ae
  have hPsiD_meas : AEMeasurable (fun u : U => (beta / (m : ℝ)) * potSum Gammaih LG D u) Q := by
    have hlog : AEMeasurable (fun u : U => Real.log (Real.exp (-(beta / (m : ℝ)) * potSum Gammaih LG D u))) Q :=
      Real.measurable_log.comp_aemeasurable hDm
    have hneg : AEMeasurable (fun u : U => -((beta / (m : ℝ)) * potSum Gammaih LG D u)) Q := by
      simpa only [Function.comp_apply, Real.log_exp, neg_mul] using hlog
    simpa only [neg_neg] using hneg.neg
  have hPsiDp_meas : AEMeasurable (fun u : U => (beta / (m : ℝ)) * potSum Gammaih LG Dp u) Q := by
    have hlog : AEMeasurable (fun u : U => Real.log (Real.exp (-(beta / (m : ℝ)) * potSum Gammaih LG Dp u))) Q :=
      Real.measurable_log.comp_aemeasurable hDmp
    have hneg : AEMeasurable (fun u : U => -((beta / (m : ℝ)) * potSum Gammaih LG Dp u)) Q := by
      simpa only [Function.comp_apply, Real.log_exp, neg_mul] using hlog
    simpa only [neg_neg] using hneg.neg
  have hPsi_bound : ∀ u : U, UScale e lam (1 - st) u →
      |(beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u|
        ≤ beta * (2 * kappa * r * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) +
            2 * (Real.rpow mubar st) * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
    intro u hu
    set tu : ℝ := M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) with htu
    have htu_nn : 0 ≤ tu := by rw [htu]; exact hM1_nonneg _
    have hHScale0 : HScale bH mu (alpha - s) (0 : H) := show HScaleNorm bH mu (alpha - s) (0 : H) < ⊤ from by simp [HScaleNorm]
    have hdist00 : ENNReal.toReal (HScaleDist bH mu (alpha - s) (0 : H) 0) = 0 := by simp [HScaleDist, HScaleNorm]
    have hc_nn : 0 ≤ Real.rpow mubar st := Real.rpow_nonneg (by linarith) st
    have hperj : ∀ j : Fin m,
        |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (Dp j).1 (Dp j).2| ≤ 2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2 := by
      intro j
      have hrad : ENNReal.toReal (HScaleDist bH mu (alpha - s) (D j).2 0) ≤ r := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hD_rad j)
        rwa [ENNReal.toReal_ofReal hr] at h
      have hradp : ENNReal.toReal (HScaleDist bH mu (alpha - s) (Dp j).2 0) ≤ r := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hDp_rad j)
        rwa [ENNReal.toReal_ofReal hr] at h
      have h1j : |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0| ≤ kappa * r * tu := by
        have h6j := h6 (D j).1 (Dp j).1 (D j).2 0 (hD j) hHScale0 u hu
        rw [← htu] at h6j
        calc |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0|
            ≤ kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) (D j).2 0) * tu := h6j
          _ ≤ kappa * r * tu := by
              apply mul_le_mul_of_nonneg_right _ htu_nn
              exact mul_le_mul_of_nonneg_left hrad hkappa
      have h3j : |Phi Gammaih LG u (Dp j).1 0 - Phi Gammaih LG u (Dp j).1 (Dp j).2| ≤ kappa * r * tu := by
        have h6j := h6 (Dp j).1 (Dp j).1 (Dp j).2 0 (hDp j) hHScale0 u hu
        rw [← htu] at h6j
        calc |Phi Gammaih LG u (Dp j).1 0 - Phi Gammaih LG u (Dp j).1 (Dp j).2|
            = |Phi Gammaih LG u (Dp j).1 (Dp j).2 - Phi Gammaih LG u (Dp j).1 0| := abs_sub_comm _ _
          _ ≤ kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) (Dp j).2 0) * tu := h6j
          _ ≤ kappa * r * tu := by
              apply mul_le_mul_of_nonneg_right _ htu_nn
              exact mul_le_mul_of_nonneg_left hradp hkappa
      have h2j : |Phi Gammaih LG u (D j).1 0 - Phi Gammaih LG u (Dp j).1 0| ≤ 2 * (Real.rpow mubar st) * tu ^ 2 := by
        have h7j := h7 (D j).1 (Dp j).1 0 0 hHScale0 hHScale0 u hu
        rw [← htu, hdist00] at h7j
        have h8j := h8 (D j).1 (Dp j).1 0 0 hHScale0 hHScale0 u hu
        rw [← htu] at h8j
        have hc_nn_tu : 0 ≤ Real.rpow mubar st * tu := mul_nonneg hc_nn htu_nn
        have hkey : (Real.rpow mubar st * tu + kappa * 0) * ENNReal.toReal (HScaleDist bH mu st (Gammaih (LG (D j).1 u - LG (Dp j).1 u)) 0) ≤ 2 * (Real.rpow mubar st) * tu ^ 2 := by
          have hcoef : Real.rpow mubar st * tu + kappa * 0 = Real.rpow mubar st * tu := by ring
          rw [hcoef]
          calc Real.rpow mubar st * tu * ENNReal.toReal (HScaleDist bH mu st (Gammaih (LG (D j).1 u - LG (Dp j).1 u)) 0)
              ≤ Real.rpow mubar st * tu * (2 * tu) := mul_le_mul_of_nonneg_left h8j hc_nn_tu
            _ = 2 * (Real.rpow mubar st) * tu ^ 2 := by ring
        calc |Phi Gammaih LG u (D j).1 0 - Phi Gammaih LG u (Dp j).1 0|
            ≤ (Real.rpow mubar st * tu + kappa * 0) * ENNReal.toReal (HScaleDist bH mu st (Gammaih (LG (D j).1 u - LG (Dp j).1 u)) 0) := h7j
          _ ≤ 2 * (Real.rpow mubar st) * tu ^ 2 := hkey
      have htri : |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (Dp j).1 (Dp j).2| ≤
          |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0| +
          |Phi Gammaih LG u (D j).1 0 - Phi Gammaih LG u (Dp j).1 0| +
          |Phi Gammaih LG u (Dp j).1 0 - Phi Gammaih LG u (Dp j).1 (Dp j).2| := by
        have e : Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (Dp j).1 (Dp j).2
            = (Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0)
              + (Phi Gammaih LG u (D j).1 0 - Phi Gammaih LG u (Dp j).1 0)
              + (Phi Gammaih LG u (Dp j).1 0 - Phi Gammaih LG u (Dp j).1 (Dp j).2) := by ring
        rw [e]
        calc |(Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0)
                + (Phi Gammaih LG u (D j).1 0 - Phi Gammaih LG u (Dp j).1 0)
                + (Phi Gammaih LG u (Dp j).1 0 - Phi Gammaih LG u (Dp j).1 (Dp j).2)|
            ≤ |(Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0)
                + (Phi Gammaih LG u (D j).1 0 - Phi Gammaih LG u (Dp j).1 0)|
              + |Phi Gammaih LG u (Dp j).1 0 - Phi Gammaih LG u (Dp j).1 (Dp j).2| := abs_add_le _ _
          _ ≤ (|Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0|
                + |Phi Gammaih LG u (D j).1 0 - Phi Gammaih LG u (Dp j).1 0|)
              + |Phi Gammaih LG u (Dp j).1 0 - Phi Gammaih LG u (Dp j).1 (Dp j).2| := by
                have habs := abs_add_le (Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0) (Phi Gammaih LG u (D j).1 0 - Phi Gammaih LG u (Dp j).1 0)
                linarith [habs]
          _ = |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0| +
              |Phi Gammaih LG u (D j).1 0 - Phi Gammaih LG u (Dp j).1 0| +
              |Phi Gammaih LG u (Dp j).1 0 - Phi Gammaih LG u (Dp j).1 (Dp j).2| := by ring
      calc |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (Dp j).1 (Dp j).2|
          ≤ |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (D j).1 0| +
              |Phi Gammaih LG u (D j).1 0 - Phi Gammaih LG u (Dp j).1 0| +
              |Phi Gammaih LG u (Dp j).1 0 - Phi Gammaih LG u (Dp j).1 (Dp j).2| := htri
        _ ≤ kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2 + kappa * r * tu := add_le_add (add_le_add h1j h2j) h3j
        _ = 2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2 := by ring
    have hsum_eq : potSum Gammaih LG D u - potSum Gammaih LG Dp u = ∑ j : Fin m, (Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (Dp j).1 (Dp j).2) := by
      simp only [potSum, Finset.sum_sub_distrib]
    have hsum_abs : |potSum Gammaih LG D u - potSum Gammaih LG Dp u| ≤ ∑ j : Fin m, |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (Dp j).1 (Dp j).2| := by
      rw [hsum_eq]
      exact Finset.abs_sum_le_sum_abs _ _
    have hsum_bound : (∑ j : Fin m, |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (Dp j).1 (Dp j).2|) ≤ ∑ _j : Fin m, (2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2) :=
      Finset.sum_le_sum (fun j _ => hperj j)
    have hsum_const : (∑ _j : Fin m, (2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2)) = m * (2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [nsmul_eq_mul]
    have hbetam : 0 ≤ beta / (m : ℝ) := by positivity
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have hPsi_eq : (beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u = (beta / (m : ℝ)) * (potSum Gammaih LG D u - potSum Gammaih LG Dp u) := by ring
    calc |(beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u|
        = (beta / (m : ℝ)) * |potSum Gammaih LG D u - potSum Gammaih LG Dp u| := by
            rw [hPsi_eq, abs_mul, abs_of_nonneg hbetam]
      _ ≤ (beta / (m : ℝ)) * (m * (2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hbetam
            calc |potSum Gammaih LG D u - potSum Gammaih LG Dp u|
                ≤ ∑ j : Fin m, |Phi Gammaih LG u (D j).1 (D j).2 - Phi Gammaih LG u (Dp j).1 (Dp j).2| := hsum_abs
              _ ≤ ∑ _j : Fin m, (2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2) := hsum_bound
              _ = m * (2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2) := hsum_const
      _ = beta * (2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2) := by
            rw [← mul_assoc, div_mul_cancel₀ beta hm0]
  have hpoly : ∀ t : ℝ, 2 * kappa * r * t + 2 * (Real.rpow mubar st) * t ^ 2 ≤
      (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp (delta1 * t ^ 2) := by
    intro t
    have hexp1 : (1 : ℝ) ≤ Real.exp (delta1 * t ^ 2) := by
      have h := Real.add_one_le_exp (delta1 * t ^ 2)
      have h0 : (0 : ℝ) ≤ delta1 * t ^ 2 := by positivity
      linarith
    have hexpge : delta1 * t ^ 2 ≤ Real.exp (delta1 * t ^ 2) := by
      have h := Real.add_one_le_exp (delta1 * t ^ 2); linarith
    have hδinv : (0 : ℝ) ≤ 1 / delta1 := by positivity
    have h1δ : (1 / delta1) * (delta1 * t ^ 2) = t ^ 2 := by
      rw [one_div, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hdelta1), one_mul]
    have ht2 : t ^ 2 ≤ (1 / delta1) * Real.exp (delta1 * t ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hexpge hδinv
      rwa [h1δ] at h
    have ht_sq : t ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
    have ht1 : t ≤ (1 + 1 / delta1) * Real.exp (delta1 * t ^ 2) := by
      calc t ≤ 1 + t ^ 2 := ht_sq
        _ ≤ 1 + (1 / delta1) * Real.exp (delta1 * t ^ 2) := by linarith
        _ ≤ Real.exp (delta1 * t ^ 2) + (1 / delta1) * Real.exp (delta1 * t ^ 2) := by linarith
        _ = (1 + 1 / delta1) * Real.exp (delta1 * t ^ 2) := by ring
    have hkr : (0 : ℝ) ≤ 2 * kappa * r := by positivity
    have hc : (0 : ℝ) ≤ 2 * (Real.rpow mubar st) := by
      have hrp : (0 : ℝ) ≤ Real.rpow mubar st := Real.rpow_nonneg (by linarith) st
      linarith
    have h1 := mul_le_mul_of_nonneg_left ht1 hkr
    have h2 := mul_le_mul_of_nonneg_left ht2 hc
    calc 2 * kappa * r * t + 2 * (Real.rpow mubar st) * t ^ 2
        ≤ 2 * kappa * r * ((1 + 1 / delta1) * Real.exp (delta1 * t ^ 2)) + 2 * (Real.rpow mubar st) * ((1 / delta1) * Real.exp (delta1 * t ^ 2)) := add_le_add h1 h2
      _ = (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp (delta1 * t ^ 2) := by ring
  have hbound1 : ∀ u : U,
      ‖(|(beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u| *
        ((UScale e lam (1 - st)).indicator (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) + delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u))‖
      ≤ (beta * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1))) *
        ((UScale e lam (1 - st)).indicator (fun v : U => Real.exp (4 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u) := by
    intro u
    by_cases hu : UScale e lam (1 - st) u
    · have hmem : u ∈ UScale e lam (1 - st) := hu
      simp only [Set.indicator, if_pos hmem]
      set tu : ℝ := M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) with htu
      have hPsi := hPsi_bound u hu
      rw [← htu] at hPsi
      have hpolyu := hpoly tu
      have hPsi' : |(beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u|
          ≤ beta * ((2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp (delta1 * tu ^ 2)) := by
        calc |(beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u|
            ≤ beta * (2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2) := hPsi
          _ ≤ beta * ((2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp (delta1 * tu ^ 2)) :=
              mul_le_mul_of_nonneg_left hpolyu hbeta.le
      have hDc_nn : (0 : ℝ) ≤ 2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1 := by
        have hc_nn : (0 : ℝ) ≤ Real.rpow mubar st := Real.rpow_nonneg (by linarith) st
        have h1 : (0 : ℝ) ≤ 2 * kappa * r := by positivity
        have h2 : (0 : ℝ) ≤ 2 * (Real.rpow mubar st) := by linarith
        have hnum : (0 : ℝ) ≤ 2 * kappa * r + 2 * (Real.rpow mubar st) := by linarith
        have hdiv : (0 : ℝ) ≤ (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1 := div_nonneg hnum hdelta1.le
        linarith
      have hC_nn : (0 : ℝ) ≤ beta * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) :=
        mul_nonneg (mul_nonneg hbeta.le hDc_nn) (Real.exp_pos _).le
      rw [Real.norm_of_nonneg (by positivity)]
      rw [show (1 : ℝ) * ((beta * kappa * r) ^ 2 / (4 * delta1) + delta1 * tu ^ 2) = (beta * kappa * r) ^ 2 / (4 * delta1) + delta1 * tu ^ 2 from by ring, Real.exp_add]
      have hdt_nn : (0 : ℝ) ≤ delta1 * tu ^ 2 := mul_nonneg hdelta1.le (sq_nonneg tu)
      have hexsq : Real.exp (delta1 * tu ^ 2) * Real.exp (delta1 * tu ^ 2) = Real.exp (2 * delta1 * tu ^ 2) := by
        rw [← Real.exp_add, show delta1 * tu ^ 2 + delta1 * tu ^ 2 = 2 * delta1 * tu ^ 2 from by ring]
      have hmono : Real.exp (2 * delta1 * tu ^ 2) ≤ Real.exp (4 * delta1 * tu ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hdt_nn]
      calc |(beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u| * (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * Real.exp (delta1 * tu ^ 2))
          ≤ (beta * ((2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp (delta1 * tu ^ 2))) * (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * Real.exp (delta1 * tu ^ 2)) :=
              mul_le_mul_of_nonneg_right hPsi' (by positivity)
        _ = beta * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * (Real.exp (delta1 * tu ^ 2) * Real.exp (delta1 * tu ^ 2)) := by ring
        _ = beta * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * Real.exp (2 * delta1 * tu ^ 2) := by rw [hexsq]
        _ ≤ beta * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * Real.exp (4 * delta1 * tu ^ 2) :=
              mul_le_mul_of_nonneg_left hmono hC_nn
        _ = (beta * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1))) * Real.exp (4 * delta1 * tu ^ 2) := by ring
    · have hmem : u ∉ UScale e lam (1 - st) := hu
      simp only [Set.indicator, if_neg hmem]
      simp
  have hbound2 : ∀ u : U,
      ‖(((beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u) ^ 2 *
        ((UScale e lam (1 - st)).indicator (fun v : U => Real.exp (1 * ((beta * kappa * r) ^ 2 / (4 * delta1) + delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2))) u))‖
      ≤ (beta ^ 2 * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) ^ 2 * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1))) *
        ((UScale e lam (1 - st)).indicator (fun v : U => Real.exp (4 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u) := by
    intro u
    by_cases hu : UScale e lam (1 - st) u
    · have hmem : u ∈ UScale e lam (1 - st) := hu
      simp only [Set.indicator, if_pos hmem]
      set tu : ℝ := M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) with htu
      have hPsi := hPsi_bound u hu
      rw [← htu] at hPsi
      have hpolyu := hpoly tu
      have hDc_nn : (0 : ℝ) ≤ 2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1 := by
        have hc_nn : (0 : ℝ) ≤ Real.rpow mubar st := Real.rpow_nonneg (by linarith) st
        have h1 : (0 : ℝ) ≤ 2 * kappa * r := by positivity
        have h2 : (0 : ℝ) ≤ 2 * (Real.rpow mubar st) := by linarith
        have hnum : (0 : ℝ) ≤ 2 * kappa * r + 2 * (Real.rpow mubar st) := by linarith
        have hdiv : (0 : ℝ) ≤ (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1 := div_nonneg hnum hdelta1.le
        linarith
      have hA_nn : (0 : ℝ) ≤ beta * ((2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp (delta1 * tu ^ 2)) :=
        mul_nonneg hbeta.le (mul_nonneg hDc_nn (Real.exp_pos _).le)
      have hPsi2 : ((beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u) ^ 2
          ≤ (beta * ((2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp (delta1 * tu ^ 2))) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hA_nn]
        calc |(beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u|
            ≤ beta * (2 * kappa * r * tu + 2 * (Real.rpow mubar st) * tu ^ 2) := hPsi
          _ ≤ beta * ((2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp (delta1 * tu ^ 2)) :=
              mul_le_mul_of_nonneg_left hpolyu hbeta.le
      have hC2_nn : (0 : ℝ) ≤ beta ^ 2 * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) ^ 2 * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) := by positivity
      rw [Real.norm_of_nonneg (by positivity)]
      rw [show (1 : ℝ) * ((beta * kappa * r) ^ 2 / (4 * delta1) + delta1 * tu ^ 2) = (beta * kappa * r) ^ 2 / (4 * delta1) + delta1 * tu ^ 2 from by ring, Real.exp_add]
      have hdt_nn : (0 : ℝ) ≤ delta1 * tu ^ 2 := mul_nonneg hdelta1.le (sq_nonneg tu)
      have hexsq : Real.exp (delta1 * tu ^ 2) * Real.exp (delta1 * tu ^ 2) = Real.exp (2 * delta1 * tu ^ 2) := by
        rw [← Real.exp_add, show delta1 * tu ^ 2 + delta1 * tu ^ 2 = 2 * delta1 * tu ^ 2 from by ring]
      have hexsq2 : Real.exp (2 * delta1 * tu ^ 2) * Real.exp (delta1 * tu ^ 2) = Real.exp (3 * delta1 * tu ^ 2) := by
        rw [← Real.exp_add, show 2 * delta1 * tu ^ 2 + delta1 * tu ^ 2 = 3 * delta1 * tu ^ 2 from by ring]
      have hmono3 : Real.exp (3 * delta1 * tu ^ 2) ≤ Real.exp (4 * delta1 * tu ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hdt_nn]
      calc ((beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u) ^ 2 * (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * Real.exp (delta1 * tu ^ 2))
          ≤ (beta * ((2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp (delta1 * tu ^ 2))) ^ 2 * (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * Real.exp (delta1 * tu ^ 2)) :=
              mul_le_mul_of_nonneg_right hPsi2 (by positivity)
        _ = beta ^ 2 * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) ^ 2 * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * ((Real.exp (delta1 * tu ^ 2) * Real.exp (delta1 * tu ^ 2)) * Real.exp (delta1 * tu ^ 2)) := by ring
        _ = beta ^ 2 * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) ^ 2 * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * (Real.exp (2 * delta1 * tu ^ 2) * Real.exp (delta1 * tu ^ 2)) := by rw [hexsq]
        _ = beta ^ 2 * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) ^ 2 * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * Real.exp (3 * delta1 * tu ^ 2) := by rw [hexsq2]
        _ ≤ beta ^ 2 * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) ^ 2 * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)) * Real.exp (4 * delta1 * tu ^ 2) :=
              mul_le_mul_of_nonneg_left hmono3 hC2_nn
        _ = (beta ^ 2 * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) ^ 2 * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1))) * Real.exp (4 * delta1 * tu ^ 2) := by ring
    · have hmem : u ∉ UScale e lam (1 - st) := hu
      simp only [Set.indicator, if_neg hmem]
      simp
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' (g := fun u => (beta * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1))) * ((UScale e lam (1 - st)).indicator (fun v : U => Real.exp (4 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u)) ?_ ?_ ?_
    · simpa only [smul_eq_mul] using hEt_int.const_mul (beta * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)))
    · exact (hPsiD_meas.sub hPsiDp_meas).abs.aestronglyMeasurable.mul hEff_meas.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hbound1
  · refine Integrable.mono' (g := fun u => (beta ^ 2 * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) ^ 2 * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1))) * ((UScale e lam (1 - st)).indicator (fun v : U => Real.exp (4 * delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) v 0))) ^ 2)) u)) ?_ ?_ ?_
    · simpa only [smul_eq_mul] using hEt_int.const_mul (beta ^ 2 * (2 * kappa * r + (2 * kappa * r + 2 * (Real.rpow mubar st)) / delta1) ^ 2 * Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1)))
    · have hsq : AEMeasurable (fun u : U => ((beta / (m : ℝ)) * potSum Gammaih LG D u - (beta / (m : ℝ)) * potSum Gammaih LG Dp u) ^ 2) Q := by
        have h := (hPsiD_meas.sub hPsiDp_meas).mul (hPsiD_meas.sub hPsiDp_meas)
        simpa only [pow_two] using h
      exact (AEMeasurable.aestronglyMeasurable hsq).mul hEff_meas.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hbound2
  /- @proof-region region.target-node.session.401dc01bc2d5bc2b end -/

end Statlib.Imported
end

