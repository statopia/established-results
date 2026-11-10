import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3091194290_4509a8b7_27a85c1e
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3551296407_58969dcf_1b749c74
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3916768571_a9930ecf_948a7b8d

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
theorem statopia_math_node_4147388267_4d56357b : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Type*)
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (iotaH : Type*) [Preorder iotaH] (bH : HilbertBasis iotaH ℝ H) (mu : iotaH → ℝ)
    (Gammaih : H → H) (LG : X → U → H)
    (s st alpha : ℝ)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ t : ℝ, 0 ≤ M1 t)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hPhi_lower : ∀ (x : X) (y : H) (u : U), HScale bH mu (alpha - s) y →
      UScale e lam (1 - st) u →
      Phi Gammaih LG u x y ≥
        - (kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
    (beta : ℝ) (hbeta : 0 < beta) (m : ℕ) (hm : 0 < m)
    (Q : Measure U) [IsProbabilityMeasure Q]
    (hQ_scale : Q (UScale e lam (1 - st)) = 1)
    (delta_up : ℝ) (hdelta_up_pos : 0 < delta_up)
    (hdelta_up_int : ∀ delta : ℝ, 0 ≤ delta → delta < delta_up →
      Integrable ((UScale e lam (1 - st)).indicator
        (fun u : U =>
          Real.exp (delta * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) Q)
    (delta1 : ℝ) (hdelta1_pos : 0 < delta1) (hdelta1_lt : 8 * delta1 < delta_up)
    (r : ℝ) (hr : 0 ≤ r)
    (D : Fin m → X × H)
    (hD : ∀ j : Fin m,
      (HScaleNorm bH mu (alpha - s) (D j).2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal r)
    (hdens_meas : AEMeasurable (fun u : U => temperedDens beta m Gammaih LG D u) Q),
    (∀ u : U, UScale e lam (1 - st) u →
      potSum Gammaih LG D u ≥
        - ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ∧
      temperedDens beta m Gammaih LG D u ≤
        Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∧
    (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂Q) ≠ ⊤ ∧
    (∫⁻ u : U, ENNReal.ofReal
      (Real.exp (-(2 * beta / (m : ℝ)) * potSum Gammaih LG D u)) ∂Q) < ⊤ ∧
    (∫⁻ u : U, ENNReal.ofReal
      (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
        delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∂Q) < ⊤ ∧
    (∫⁻ u : U, ENNReal.ofReal
      (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
        delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∂Q) ≠ ⊤ := by
  /- @proof-region region.target-node.session.600020df0d7a2673 begin -/
  intro U hU1 hU2 hU3 H hH1 hH2 X e lam iotaH hIotaH bH mu Gammaih LG s st alpha
  intro M1 hM1_mono hM1_nonneg kappa hkappa hPhi_lower beta hbeta m hm Q hQprob hQ_scale
  intro delta_up hdelta_up_pos hdelta_up delta1 hdelta1_pos hdelta1 r hr D hD hDens_meas
  classical
  have hQuniv : Q Set.univ = 1 := measure_univ
  have hdelta1_lt : delta1 < delta_up := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hd1ne : delta1 ≠ 0 := ne_of_gt hdelta1_pos
  have h4ne : (4 * delta1) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 4 * delta1)
  have hind0 : Integrable ((UScale e lam (1 - st)).indicator (fun _ : U => (1 : ℝ))) Q := by
    have h := hdelta_up 0 (le_refl 0) hdelta_up_pos
    simpa using h
  have hAEm : AEMeasurable ((UScale e lam (1 - st)).indicator (fun _ : U => (1 : ℝ))) Q :=
    hind0.1.aemeasurable
  obtain ⟨g, hg_meas, hg_ae⟩ := hAEm
  have hg_ne : MeasurableSet {u : U | g u ≠ 0} := by
    show MeasurableSet (g ⁻¹' ({0} : Set ℝ)ᶜ)
    exact hg_meas (measurableSet_singleton 0).compl
  have h_st : (UScale e lam (1 - st)) =ᵐ[Q] {u : U | g u ≠ 0} := by
    filter_upwards [hg_ae] with u hu
    show (u ∈ UScale e lam (1 - st)) = (g u ≠ 0)
    rw [Set.indicator_apply] at hu
    by_cases h : u ∈ UScale e lam (1 - st)
    · rw [if_pos h] at hu
      exact propext ⟨fun _ => by rw [← hu]; exact one_ne_zero, fun _ => h⟩
    · rw [if_neg h] at hu
      exact propext ⟨fun hh => absurd hh h, fun hne => absurd (by rw [← hu]) hne⟩
  have hQt : Q {u : U | g u ≠ 0} = 1 := by
    rw [← measure_congr h_st]
    exact hQ_scale
  have htc : Q {u : U | g u ≠ 0}ᶜ = 0 := by
    rw [measure_compl hg_ne (by rw [hQt]; exact ENNReal.one_ne_top), hQt, hQuniv]
    simp
  have hae_mem : ∀ᵐ u ∂Q, u ∈ {u : U | g u ≠ 0} := by
    rw [MeasureTheory.ae_iff]
    show Q {u : U | g u ≠ 0}ᶜ = 0
    exact htc
  have hscale_ae : ∀ᵐ u ∂Q, u ∈ UScale e lam (1 - st) := by
    filter_upwards [hae_mem, h_st] with u hu hst
    exact Eq.mpr hst hu
  have hDist_le : ∀ j : Fin m,
      ENNReal.toReal (HScaleDist bH mu (alpha - s) (D j).2 0) ≤ r := by
    intro j
    have hD' : HScaleDist bH mu (alpha - s) (D j).2 0 ≤ ENNReal.ofReal r := by
      calc HScaleDist bH mu (alpha - s) (D j).2 0
          = (HScaleNorm bH mu (alpha - s) (D j).2) ^ (1 / 2 : ℝ) := by
            simp only [HScaleDist, sub_zero]
        _ ≤ ENNReal.ofReal r := hD j
    exact ENNReal.toReal_le_of_le_ofReal hr hD'
  have hHScale : ∀ j : Fin m, HScale bH mu (alpha - s) (D j).2 := by
    intro j
    have htop : ENNReal.ofReal r < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top
    have h₁ : (HScaleNorm bH mu (alpha - s) (D j).2) ^ (1 / 2 : ℝ) < (⊤ : ℝ≥0∞) :=
      lt_of_le_of_lt (hD j) htop
    change HScaleNorm bH mu (alpha - s) (D j).2 < (⊤ : ℝ≥0∞)
    by_contra hc
    rw [not_lt] at hc
    have htop2 : HScaleNorm bH mu (alpha - s) (D j).2 = ⊤ := le_antisymm le_top hc
    rw [htop2, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h₁
    exact absurd h₁ (lt_irrefl (⊤ : ℝ≥0∞))
  have hind1 : Integrable ((UScale e lam (1 - st)).indicator
      (fun u : U => Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) Q :=
    hdelta_up delta1 hdelta1_pos.le hdelta1_lt
  have hF_lin : (∫⁻ u : U, ENNReal.ofReal
      (Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∂Q) < ⊤ := by
    have hcongr : (fun u : U => ENNReal.ofReal
        (Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)))
        =ᵐ[Q] (fun u : U => ENNReal.ofReal
          (((UScale e lam (1 - st)).indicator
            (fun u : U => Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) u)) := by
      filter_upwards [hscale_ae] with u hu
      rw [Set.indicator_apply, if_pos hu]
    have hnn : (0 : U → ℝ) ≤ᶠ[ae Q]
        ((UScale e lam (1 - st)).indicator
          (fun u : U => Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) :=
      Filter.Eventually.of_forall (fun u => by
        rw [Pi.zero_apply, Set.indicator_apply]
        split_ifs with h
        · exact (Real.exp_pos _).le
        · exact le_refl 0)
    rw [lintegral_congr_ae hcongr, ← ofReal_integral_eq_lintegral_ofReal hind1 hnn]
    exact ENNReal.ofReal_lt_top
  have hexp_lin : ∀ A : ℝ, (∫⁻ u : U, ENNReal.ofReal
      (Real.exp (A + delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∂Q) < ⊤ := by
    intro A
    have hG : Integrable (fun u : U => Real.exp A *
        ((UScale e lam (1 - st)).indicator
          (fun u : U => Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) u) Q :=
      hind1.const_mul (Real.exp A)
    have hcongr : (fun u : U => ENNReal.ofReal (Real.exp A *
          ((UScale e lam (1 - st)).indicator
            (fun u : U => Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) u))
        =ᵐ[Q] (fun u : U => ENNReal.ofReal
          (Real.exp (A + delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) := by
      filter_upwards [hscale_ae] with u hu
      rw [Set.indicator_apply, if_pos hu, Real.exp_add]
    have hnn : (0 : U → ℝ) ≤ᶠ[ae Q] (fun u : U => Real.exp A *
        ((UScale e lam (1 - st)).indicator
          (fun u : U => Real.exp (delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2))) u) :=
      Filter.Eventually.of_forall (fun u => by
        refine mul_nonneg (Real.exp_pos A).le ?_
        rw [Set.indicator_apply]
        split_ifs with h
        · exact (Real.exp_pos _).le
        · exact le_refl 0)
    rw [← lintegral_congr_ae hcongr, ← ofReal_integral_eq_lintegral_ofReal hG hnn]
    exact ENNReal.ofReal_lt_top
  have hquad : ∀ A x : ℝ, A * x ≤ A ^ 2 / (4 * delta1) + delta1 * x ^ 2 := by
    intro A x
    have h4 : (0 : ℝ) < 4 * delta1 := by linarith
    have hkey : A * x * (4 * delta1) ≤ A ^ 2 + 4 * delta1 ^ 2 * x ^ 2 := by
      nlinarith [sq_nonneg (A - 2 * delta1 * x)]
    have heq : A ^ 2 / (4 * delta1) + delta1 * x ^ 2
        = (A ^ 2 + 4 * delta1 ^ 2 * x ^ 2) / (4 * delta1) := by
      field_simp
    rw [heq, le_div_iff₀ h4]
    linarith
  have ha1 : ∀ u : U, UScale e lam (1 - st) u →
      potSum Gammaih LG D u ≥
        - ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
    intro u hu
    have hsum_le : (∑ j : Fin m,
        -(kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
        ≤ potSum Gammaih LG D u := by
      simp only [potSum]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hb := hPhi_lower (D j).1 (D j).2 u (hHScale j) hu
      have hstep : kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) (D j).2 0) *
          M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))
          ≤ kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
        refine mul_le_mul_of_nonneg_right ?_ (hM1_nonneg _)
        exact mul_le_mul_of_nonneg_left (hDist_le j) hkappa
      linarith
    have hcard : (∑ _j : Fin m,
        -(kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
        = - ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    linarith
  have ha2 : ∀ u : U, UScale e lam (1 - st) u →
      temperedDens beta m Gammaih LG D u ≤
        Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2) := by
    intro u hu
    have hp := ha1 u hu
    have hcpos : 0 < beta / (m : ℝ) := div_pos hbeta hmpos
    have hstep : -(beta / (m : ℝ)) * potSum Gammaih LG D u
        ≤ beta * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
      have h1 : -(beta / (m : ℝ)) * potSum Gammaih LG D u
          ≤ -(beta / (m : ℝ)) *
            (- ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))) :=
        mul_le_mul_of_nonpos_left hp (by linarith : -(beta / (m : ℝ)) ≤ 0)
      have h2 : -(beta / (m : ℝ)) *
            (- ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
          = beta * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
        field_simp
      rwa [h2] at h1
    have hq := hquad (beta * kappa * r) (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))
    show Real.exp (-(beta / (m : ℝ)) * potSum Gammaih LG D u) ≤
      Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
        delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)
    exact Real.exp_le_exp.mpr (le_trans hstep hq)
  have hN_lin : (∫⁻ u : U, ENNReal.ofReal
      (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
        delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∂Q) < ⊤ :=
    hexp_lin ((beta * kappa * r) ^ 2 / (4 * delta1))
  have hdens_lin : (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂Q) ≠ ⊤ := by
    have hle : (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂Q)
        ≤ ∫⁻ u : U, ENNReal.ofReal
          (Real.exp ((beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∂Q := by
      refine lintegral_mono_ae ?_
      filter_upwards [hscale_ae] with u hu
      exact ENNReal.ofReal_le_ofReal (ha2 u hu)
    exact ne_of_lt (lt_of_le_of_lt hle hN_lin)
  have hsq_lin : (∫⁻ u : U, ENNReal.ofReal
      (Real.exp (-(2 * beta / (m : ℝ)) * potSum Gammaih LG D u)) ∂Q) < ⊤ := by
    have hA2 : (2 * beta * kappa * r) ^ 2 / (4 * delta1) = (beta * kappa * r) ^ 2 / delta1 := by
      field_simp
      ring
    have hle : (∫⁻ u : U, ENNReal.ofReal
        (Real.exp (-(2 * beta / (m : ℝ)) * potSum Gammaih LG D u)) ∂Q)
        ≤ ∫⁻ u : U, ENNReal.ofReal
          (Real.exp ((2 * beta * kappa * r) ^ 2 / (4 * delta1) +
            delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∂Q := by
      refine lintegral_mono_ae ?_
      filter_upwards [hscale_ae] with u hu
      refine ENNReal.ofReal_le_ofReal ?_
      have hp := ha1 u hu
      have hstep : -(2 * beta / (m : ℝ)) * potSum Gammaih LG D u
          ≤ 2 * beta * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
        have h1 : -(2 * beta / (m : ℝ)) * potSum Gammaih LG D u
            ≤ -(2 * beta / (m : ℝ)) *
              (- ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))) :=
          mul_le_mul_of_nonpos_left hp (by
            have h2b : (0 : ℝ) < 2 * beta / (m : ℝ) := div_pos (by linarith) hmpos
            linarith)
        have h2 : -(2 * beta / (m : ℝ)) *
              (- ((m : ℝ) * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
            = 2 * beta * kappa * r * M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)) := by
          field_simp
        rwa [h2] at h1
      have hq := hquad (2 * beta * kappa * r) (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))
      exact Real.exp_le_exp.mpr (le_trans hstep hq)
    have hfin : (∫⁻ u : U, ENNReal.ofReal
        (Real.exp ((2 * beta * kappa * r) ^ 2 / (4 * delta1) +
          delta1 * (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2)) ∂Q) < ⊤ := by
      rw [hA2]
      exact hexp_lin ((beta * kappa * r) ^ 2 / delta1)
    exact lt_of_le_of_lt hle hfin
  refine ⟨fun u hu => ⟨ha1 u hu, ha2 u hu⟩, hdens_lin, hsq_lin, hN_lin, ne_of_lt hN_lin⟩
  /- @proof-region region.target-node.session.600020df0d7a2673 end -/

end Statlib.Imported
end

