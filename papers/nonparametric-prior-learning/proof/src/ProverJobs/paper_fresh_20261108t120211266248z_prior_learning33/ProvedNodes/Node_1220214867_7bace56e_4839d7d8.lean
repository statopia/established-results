import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3091194290_4509a8b7_27a85c1e
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3551296407_58969dcf_1b749c74
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3916768571_a9930ecf_948a7b8d
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_4147388267_4d56357b_aae526a8

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
theorem statopia_math_node_1220214867_7bace56e : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Type*)
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (iotaH : Type*) [Preorder iotaH] (bH : HilbertBasis iotaH ℝ H) (mu : iotaH → ℝ)
    (Gammaih : H → H) (LG : X → U → H)
    (s st alpha : ℝ)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ t : ℝ, 0 ≤ M1 t)
    (mubar kappa : ℝ) (hmubar : 1 ≤ mubar) (hkappa : 0 ≤ kappa)
    (hPhi_lower : ∀ (x : X) (y : H) (u : U), HScale bH mu (alpha - s) y →
      UScale e lam (1 - st) u →
      Phi Gammaih LG u x y ≥
        - (kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
    (hPhi_upper : ∀ (x : X) (y : H) (u : U), HScale bH mu (alpha - s) y →
      UScale e lam (1 - st) u →
      Phi Gammaih LG u x y ≤
        (1 / 2 : ℝ) * (mubar ^ st) *
            (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))) ^ 2 +
          kappa * ENNReal.toReal (HScaleDist bH mu (alpha - s) y 0) *
            M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0)))
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
    (∀ u : U, 0 < temperedDens beta m Gammaih LG D u) ∧
      Integrable (fun u : U => temperedDens beta m Gammaih LG D u) Q ∧
      0 < Zm beta m Gammaih LG Q D ∧
      ENNReal.ofReal (Zm beta m Gammaih LG Q D) =
        ∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂Q ∧
      Qpost beta m Gammaih LG Q D =
        Q.withDensity
          (fun u : U =>
            ENNReal.ofReal ((Zm beta m Gammaih LG Q D)⁻¹ * temperedDens beta m Gammaih LG D u)) ∧
      MeasureTheory.Measure.AbsolutelyContinuous (Qpost beta m Gammaih LG Q D) Q ∧
      (∀ᵐ u ∂Q,
        (Qpost beta m Gammaih LG Q D).rnDeriv Q u =
          ENNReal.ofReal ((Zm beta m Gammaih LG Q D)⁻¹ * temperedDens beta m Gammaih LG D u)) := by
  /- @proof-region region.target-node.session.3332898b1da43037 begin -/
  intro U _ _ _ H _ _ X e lam iotaH _ bH mu Gammaih LG s st alpha M1 hM1_mono hM1_nonneg
    mubar kappa hmubar hkappa hPhi_lower hPhi_upper beta hbeta m hm Q _ hQ_scale delta_up
    hdelta_up_pos hdelta_up delta1 hdelta1_pos hdelta1 r hr D hD hDens_meas
  have hkey := statopia_math_node_4147388267_4d56357b
    (U := U) (H := H) (X := X) (e := e) (lam := lam) (iotaH := iotaH) (bH := bH) (mu := mu)
    (Gammaih := Gammaih) (LG := LG) (s := s) (st := st) (alpha := alpha)
    (M1 := M1) (hM1_mono := hM1_mono) (hM1_nonneg := hM1_nonneg) (kappa := kappa)
    (hkappa := hkappa) (hPhi_lower := hPhi_lower) (beta := beta) (hbeta := hbeta) (m := m)
    (hm := hm) (Q := Q) (hQ_scale := hQ_scale) (delta_up := delta_up)
    (hdelta_up_pos := hdelta_up_pos) (hdelta_up_int := hdelta_up) (delta1 := delta1)
    (hdelta1_pos := hdelta1_pos) (hdelta1_lt := hdelta1) (r := r) (hr := hr) (D := D)
    (hD := hD) (hdens_meas := hDens_meas)
  have hdens_ae : ∀ᵐ u ∂Q, (0 : ℝ) ≤ temperedDens beta m Gammaih LG D u :=
    Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le)
  have hlin_ne_top :
      (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂Q) ≠ ⊤ :=
    hkey.2.1
  have hInt : Integrable (fun u : U => temperedDens beta m Gammaih LG D u) Q :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hDens_meas.aestronglyMeasurable
      hdens_ae).1 hlin_ne_top
  have hofReal_int : ENNReal.ofReal (Zm beta m Gammaih LG Q D) =
      ∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂Q :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hdens_ae
  let gD : U → ℝ := hDens_meas.mk
  have hgD_meas : Measurable gD := hDens_meas.measurable_mk
  have hgD_ae : (fun u : U => temperedDens beta m Gammaih LG D u) =ᵐ[Q] gD :=
    hDens_meas.ae_eq_mk
  have hlin_pos : 0 < ∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂Q := by
    have hgD_pos : ∀ᵐ u ∂Q, 0 < gD u := by
      filter_upwards [hgD_ae] with u hu
      rw [← hu]
      exact Real.exp_pos _
    have hsupp : Q (Function.support (fun u : U => ENNReal.ofReal (gD u))) = 1 := by
      have hset : Function.support (fun u : U => ENNReal.ofReal (gD u)) =ᵐ[Q] Set.univ := by
        filter_upwards [hgD_pos] with u hu
        exact propext ⟨fun _ => trivial, fun _ => ne_of_gt ((ENNReal.ofReal_pos).mpr hu)⟩
      rw [MeasureTheory.measure_congr hset, measure_univ]
    have hcongr : (∫⁻ u : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D u) ∂Q)
        = ∫⁻ u : U, ENNReal.ofReal (gD u) ∂Q := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards [hgD_ae] with u hu
      rw [hu]
    rw [hcongr, MeasureTheory.lintegral_pos_iff_support hgD_meas.ennreal_ofReal, hsupp]
    exact zero_lt_one
  have hZpos : 0 < Zm beta m Gammaih LG Q D := by
    have hpos : 0 < ENNReal.ofReal (Zm beta m Gammaih LG Q D) := by
      rw [hofReal_int]
      exact hlin_pos
    exact (ENNReal.ofReal_pos).1 hpos
  have hpost : Qpost beta m Gammaih LG Q D =
      Q.withDensity (fun u : U => ENNReal.ofReal ((Zm beta m Gammaih LG Q D)⁻¹ *
        temperedDens beta m Gammaih LG D u)) := by
    show Q.withDensity (fun u : U => ENNReal.ofReal (temperedDens beta m Gammaih LG D u) /
        (∫⁻ v : U, ENNReal.ofReal (temperedDens beta m Gammaih LG D v) ∂Q)) =
      Q.withDensity (fun u : U => ENNReal.ofReal ((Zm beta m Gammaih LG Q D)⁻¹ *
        temperedDens beta m Gammaih LG D u))
    congr 1
    funext u
    rw [hofReal_int.symm, ← ENNReal.ofReal_div_of_pos hZpos]
    congr 1
    rw [div_eq_inv_mul]
  have hd_meas : Measurable (fun u : U =>
      ENNReal.ofReal ((Zm beta m Gammaih LG Q D)⁻¹ * gD u)) :=
    (measurable_const.mul hgD_meas).ennreal_ofReal
  have h_ae : (fun u : U => ENNReal.ofReal ((Zm beta m Gammaih LG Q D)⁻¹ *
        temperedDens beta m Gammaih LG D u)) =ᵐ[Q]
      (fun u : U => ENNReal.ofReal ((Zm beta m Gammaih LG Q D)⁻¹ * gD u)) := by
    filter_upwards [hgD_ae] with u hu
    rw [hu]
  have hEq : Q.withDensity (fun u : U => ENNReal.ofReal ((Zm beta m Gammaih LG Q D)⁻¹ *
        temperedDens beta m Gammaih LG D u)) =
      Q.withDensity (fun u : U => ENNReal.ofReal ((Zm beta m Gammaih LG Q D)⁻¹ * gD u)) :=
    MeasureTheory.withDensity_congr_ae h_ae
  refine ⟨fun u => Real.exp_pos _, hInt, hZpos, hofReal_int, hpost, ?_, ?_⟩
  · rw [hpost]
    exact MeasureTheory.withDensity_absolutelyContinuous Q _
  · rw [hpost, hEq]
    exact (MeasureTheory.Measure.rnDeriv_withDensity Q hd_meas).trans h_ae.symm
  /- @proof-region region.target-node.session.3332898b1da43037 end -/

end Statlib.Imported
end

