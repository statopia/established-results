import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2540716848_7ce5841c_f4134c6f
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3082865640_d48798c3_6cb1bf8c
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_457006637_708d8d08_c9bb53bc

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
theorem statopia_math_node_3916768571_a9930ecf : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Type*) [TopologicalSpace X]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (Γ : H →L[ℝ] H) (hΓ_pos : Γ.IsPositive) (hΓ_inj : ∀ v : H, Γ v = 0 → v = 0)
    (Γh : H →ₗ[ℝ] H)
    (hΓh_symm : ∀ v w : H, inner ℝ (Γh v) w = inner ℝ v (Γh w))
    (hΓh_pos : ∀ v : H, 0 ≤ inner ℝ v (Γh v))
    (hΓh_sq : ∀ v : H, Γh (Γh v) = Γ v)
    (Γih : H → H) (hΓih_left : ∀ v : H, Γih (Γh v) = v)
    (ιH : Type*) [Preorder ιH] (bH : HilbertBasis ιH ℝ H) (mu : ιH → ℝ)
    (hmu_pos : ∀ i : ιH, 0 < mu i) (hmu_anti : Antitone mu)
    (C1 : H →L[ℝ] H) (hC1_pos : C1.IsPositive) (hC1_inj : ∀ v : H, C1 v = 0 → v = 0)
    (hC1_eigen : ∀ i : ιH, C1 (bH i) = mu i • bH i)
    (LG : X → U → H)
    (s0 s1 s st α : ℝ)
    (hs0_nonneg : 0 ≤ s0) (hs0_lt : s0 < 1)
    (hs1_nonneg : 0 ≤ s1) (hs1_lt : s1 < 1)
    (hs_gt : s1 < s) (hs_le : s ≤ 1)
    (hst_gt : s0 < st) (hst_le : st ≤ 1) (hα : 0 ≤ α)
    (C1c C2c : ℝ) (hC1c : 0 < C1c) (hC2c : 0 < C2c)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ r : ℝ, 0 ≤ M1 r)
    (M2 : ℝ → ℝ → ℝ) (hM2_nonneg : ∀ r1 r2 : ℝ, 0 ≤ M2 r1 r2)
    (hM2_mono_fst : ∀ r2 : ℝ, Monotone (fun r : ℝ => M2 r r2))
    (hM2_mono_snd : ∀ r1 : ℝ, Monotone (fun r : ℝ => M2 r1 r))
    (hA1 : (¬ FiniteDimensional ℝ H) → ∀ (w : H) (ρ : ℝ),
      HScale bH mu (α - s) w → ((Int.floor (α - s1 - 1) : ℤ) : ℝ) ≤ ρ → ρ < α - s1 →
      HScale bH mu (-st) (Γih w) ∧ HScale bH mu st (Γh w) ∧ HScale bH mu (ρ - α) w ∧
      (HScaleNorm bH mu (-st) (Γih w)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C1c * (HScaleNorm bH mu (α - s) w) ^ (1 / 2 : ℝ) ∧
      (HScaleNorm bH mu st (Γh w)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C2c * (HScaleNorm bH mu (ρ - α) w) ^ (1 / 2 : ℝ))
    (hA2 : ∀ (x : X) (u : U), UScale e lam (1 - st) u →
      (HScaleNorm bH mu st (Γih (LG x u))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
    (hA3 : ∀ (x : X) (u1 u2 : U), UScale e lam (1 - st) u1 → UScale e lam (1 - st) u2 →
      UScale e lam (1 - st) (u1 - u2) →
      (HScaleNorm bH mu st (Γih (LG x u1 - LG x u2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M2 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0))
          (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) *
          UScaleDist e lam (1 - st) (u1 - u2) 0)
    (hA4 : ∀ (x' : X) (u : U), UScale e lam (1 - st) u →
      Tendsto (fun x : X => (HScaleNorm bH mu st (Γih (LG x u - LG x' u))) ^ (1 / 2 : ℝ))
        (𝓝 x') (𝓝 0))
    (hLG_all_range : ∀ (x : X) (u : U), UScale e lam (1 - st) u → ∃ w : H, Γh w = LG x u)
    (β : ℝ) (hβ : 0 < β) (m : ℕ) (hm : 0 < m),
    (∀ (x : X) (y : H) (u0 : U), UScale e lam (1 - st) u0 →
      ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ u : U, UScale e lam (1 - st) u →
          UScaleDist e lam (1 - st) u u0 ≤ ENNReal.ofReal delta →
          |Phi Γih LG u x y - Phi Γih LG u0 x y| ≤
            C * (UScaleDist e lam (1 - st) u u0).toReal) ∧
    (MeasurableSpace.generateFrom
        {T : Set {u : U // UScale e lam (1 - st) u} |
          ∃ u0 : U, UScale e lam (1 - st) u0 ∧ ∃ eps : ℝ, 0 < eps ∧
            T = {v : {u : U // UScale e lam (1 - st) u} |
                  UScaleDist e lam (1 - st) (v : U) u0 < ENNReal.ofReal eps}} =
      MeasurableSpace.comap (Subtype.val : {u : U // UScale e lam (1 - st) u} → U)
        (borel U)) ∧
    (∀ (D : Fin m → X × H) (x : X) (y : H) (Q : Measure U),
      Q (UScale e lam (1 - st)) = 1 → Q ((UScale e lam (1 - st))ᶜ) = 0 →
      AEMeasurable (fun u : U => Phi Γih LG u x y) Q ∧
      AEMeasurable (fun u : U => potSum Γih LG D u) Q ∧
      AEMeasurable (fun u : U => temperedDens β m Γih LG D u) Q) := by
  /- @proof-region region.target-node.session.bc72ede090d6262c begin -/
  intro U _ _ _ _ H _ _ X _ e lam hlam_pos hlam_anti Gamma hGamma_pos hGamma_inj Gammah hGammah_symm hGammah_pos hGammah_sq Gammaih hGammaih_left ιH _ bH mu hmu_pos hmu_anti C1 hC1_pos hC1_inj hC1_eigen LG s0 s1 s st alpha hs0_nonneg hs0_lt hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg hM2_mono_fst hM2_mono_snd hA1 hA2 hA3 hA4 hLG_all_range beta hbeta m hm
  have hNormMeas : ∀ t : ℝ, Measurable fun u : U => UScaleNorm e lam t u := by
    intro t
    refine Measurable.ennreal_tsum fun k => ?_
    have hc : Continuous fun u : U => inner ℝ (e k) u :=
      continuous_inner.comp (continuous_const.prodMk continuous_id)
    have hc2 : Continuous fun u : U => (inner ℝ (e k) u) ^ 2 := hc.pow 2
    have hK : Continuous fun _ : U => Real.rpow (lam k) (-t) := continuous_const
    have hc3 : Continuous fun u : U => Real.rpow (lam k) (-t) * (inner ℝ (e k) u) ^ 2 :=
      hK.mul hc2
    exact hc3.measurable.ennreal_ofReal
  have hGammah_inj : ∀ v : H, Gammah v = 0 → v = 0 := by
    intro v hv
    refine hGamma_inj v ?_
    rw [← hGammah_sq v, hv, LinearMap.map_zero]
  have hGammaIH_sub : ∀ a b : H,
      Gammaih (Gammah a - Gammah b) = Gammaih (Gammah a) - Gammaih (Gammah b) := by
    intro a b
    rw [← map_sub, hGammaih_left, hGammaih_left, hGammaih_left]
  have hmu_bdd : ∃ Cb : ℝ, 0 < Cb ∧ ∀ i : ιH, mu i ≤ Cb := by
    refine ⟨max 1 ‖C1‖, lt_of_lt_of_le one_pos (le_max_left _ _), fun i => ?_⟩
    have h1 : ‖mu i • bH i‖ = mu i := by
      rw [norm_smul, (HilbertBasis.orthonormal bH).norm_eq_one i, mul_one, Real.norm_eq_abs,
        abs_of_pos (hmu_pos i)]
    have h2 : mu i ≤ ‖C1‖ := by
      calc mu i = ‖mu i • bH i‖ := h1.symm
        _ = ‖C1 (bH i)‖ := by rw [hC1_eigen i]
        _ ≤ ‖C1‖ * ‖bH i‖ := C1.le_opNorm (bH i)
        _ = ‖C1‖ := by rw [(HilbertBasis.orthonormal bH).norm_eq_one i, mul_one]
    exact le_trans h2 (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · exact statopia_math_node_457006637_708d8d08 (U := U) (H := H) (X := X) e lam hlam_pos
      hlam_anti Gammah Gammaih hGammaih_left (ιH := ιH) bH mu hmu_pos hmu_anti hmu_bdd
      s1 s st alpha hs1_nonneg hs1_lt hs_gt hs_le (by linarith : (0 : ℝ) < st) hst_le halpha
      C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg hM2_mono_fst hM2_mono_snd LG
      hA1 hA2 hA3 hA4 hLG_all_range
  · exact statopia_math_node_2540716848_7ce5841c (U := U) e lam hlam_pos hlam_anti (1 - st)
      (by linarith)
  · intro D x y Q hQ hQae
    have hS : MeasurableSet (UScale e lam (1 - st)) :=
      measurableSet_lt (hNormMeas (1 - st)) measurable_const
    have hPhi : ∀ (x : X) (y : H), AEMeasurable (fun u : U => Phi Gammaih LG u x y) Q := by
      intro x y
      exact statopia_math_node_3082865640_d48798c3 (U := U) (H := H) (X := X) e lam hlam_pos
        hlam_anti Gammaih LG st hst_le
        (statopia_math_node_457006637_708d8d08 (U := U) (H := H) (X := X) e lam hlam_pos
          hlam_anti Gammah Gammaih hGammaih_left (ιH := ιH) bH mu hmu_pos hmu_anti hmu_bdd
          s1 s st alpha hs1_nonneg hs1_lt hs_gt hs_le (by linarith : (0 : ℝ) < st) hst_le
          halpha C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg hM2_mono_fst
          hM2_mono_snd LG hA1 hA2 hA3 hA4 hLG_all_range)
        (statopia_math_node_2540716848_7ce5841c (U := U) e lam hlam_pos hlam_anti (1 - st)
          (by linarith))
        x y Q hQ hQae
    have hPot : AEMeasurable (fun u : U => potSum Gammaih LG D u) Q := by
      have hsum : AEMeasurable
          (∑ j : Fin m, fun u : U => Phi Gammaih LG u (D j).1 (D j).2) Q :=
        Finset.aemeasurable_sum Finset.univ fun j _ => hPhi (D j).1 (D j).2
      convert hsum using 1
      ext u
      simp [potSum, Finset.sum_apply]
    have hTem : AEMeasurable (fun u : U => temperedDens beta m Gammaih LG D u) Q := by
      have h1 : AEMeasurable
          (fun u : U => -(beta / (m : ℝ)) * potSum Gammaih LG D u) Q :=
        hPot.const_mul _
      have h2 : AEMeasurable
          (fun u : U => Real.exp (-(beta / (m : ℝ)) * potSum Gammaih LG D u)) Q :=
        Real.continuous_exp.measurable.comp_aemeasurable h1
      exact h2
    exact ⟨hPhi x y, hPot, hTem⟩
  /- @proof-region region.target-node.session.bc72ede090d6262c end -/

end Statlib.Imported
end

