import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_1317275614_2c6ca56c_5aedae4f
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_1407967003_c453b7c7_b1a7c2b7
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_2313301504_0c50d598_9ec72f4b
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_3689113668_206332b7_5a5b546b
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_79440718_8647c8d9_38e2d9f6




open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_2532196350_d96cfaed : ∀ {Theta U : Type*} [MeasurableSpace Theta] [MeasurableSpace U]
    (n : ℕ) (hn : 0 < n)
    [MeasurableSpace.CountableOrCountablyGenerated Theta (Fin n → U)]
    (Qpost HP : ProbabilityMeasure Theta)
    (kap lam : Fin n → Theta → Measure U)
    (hkap_prob : ∀ (i : Fin n) (theta : Theta), IsProbabilityMeasure (kap i theta))
    (hlam_prob : ∀ (i : Fin n) (theta : Theta), IsProbabilityMeasure (lam i theta))
    (hkap_meas : ∀ i : Fin n, Measurable fun theta : Theta => kap i theta)
    (hlam_meas : ∀ i : Fin n, Measurable fun theta : Theta => lam i theta)
    (hKL_meas : ∀ i : Fin n, Measurable fun theta : Theta =>
      InformationTheory.klDiv (kap i theta) (lam i theta)),
    InformationTheory.klDiv
        ((Qpost : Measure Theta).bind fun theta =>
          Measure.map (fun u : Fin n → U => (theta, u))
            (Measure.pi fun i : Fin n => kap i theta))
        ((HP : Measure Theta).bind fun theta =>
          Measure.map (fun u : Fin n → U => (theta, u))
            (Measure.pi fun i : Fin n => lam i theta))
      = InformationTheory.klDiv (Qpost : Measure Theta) (HP : Measure Theta)
        + ∫⁻ theta, InformationTheory.klDiv (Measure.pi fun i : Fin n => kap i theta)
            (Measure.pi fun i : Fin n => lam i theta) ∂(Qpost : Measure Theta) := by
  /- @proof-region region.target-node.session.a8316b0fa1630dd8 begin -/
  intro Θ U _ _ n hn _ Qpost HP kap lam hkap_prob hlam_prob hkap_meas hlam_meas hKL_meas
  have hklFun_eq : ∀ x : ℝ, 0 < x → InformationTheory.klFun x = x * Real.log x + 1 - x := by
    intro x _
    simp [InformationTheory.klFun]
  have hklFun_mul : ∀ f g : ℝ, 0 < f → 0 < g →
      InformationTheory.klFun (f * g)
        = g * InformationTheory.klFun f + f * InformationTheory.klFun g + (1 - f) * (1 - g) := by
    intro f g hf hg
    rw [hklFun_eq (f * g) (mul_pos hf hg), hklFun_eq f hf, hklFun_eq g hg,
      Real.log_mul (ne_of_gt hf) (ne_of_gt hg)]
    ring
  have hklFun_eq' : ∀ x : ℝ, InformationTheory.klFun x = x * Real.log x + 1 - x := by
    intro x
    simp [InformationTheory.klFun]
  have hklFun_mul' : ∀ f g : ℝ, 0 ≤ f → 0 ≤ g →
      InformationTheory.klFun (f * g)
        = g * InformationTheory.klFun f + f * InformationTheory.klFun g + (1 - f) * (1 - g) := by
    intro f g hf hg
    rcases eq_or_lt_of_le hf with hf0 | hfpos
    · subst hf0
      simp only [zero_mul]
      rw [hklFun_eq' 0]
      ring
    rcases eq_or_lt_of_le hg with hg0 | hgpos
    · subst hg0
      simp only [mul_zero]
      rw [hklFun_eq' 0]
      ring
    · rw [hklFun_eq' (f * g), hklFun_eq' f, hklFun_eq' g,
        Real.log_mul (ne_of_gt hfpos) (ne_of_gt hgpos)]
      ring
  have hklFun_nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ InformationTheory.klFun x := by
    intro x hx
    rcases hx.eq_or_lt with h0 | hpos
    · subst h0
      simp [InformationTheory.klFun]
    · have h1 : Real.log x⁻¹ ≤ x⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_inv] at h1
      have h2 : 1 - x⁻¹ ≤ Real.log x := by linarith
      have h3 : x * (1 - x⁻¹) ≤ x * Real.log x :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt hpos)
      have h4 : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
      rw [hklFun_eq x hpos]
      nlinarith
  have hK_meas : Measurable fun θ : Θ => Measure.pi fun i : Fin n => kap i θ :=
    statopia_math_node_79440718_8647c8d9 n kap hkap_prob hkap_meas
  have hL_meas : Measurable fun θ : Θ => Measure.pi fun i : Fin n => lam i θ :=
    statopia_math_node_79440718_8647c8d9 n lam hlam_prob hlam_meas
  let Kk : Kernel Θ (Fin n → U) := Kernel.mk (fun θ => Measure.pi fun i : Fin n => kap i θ) hK_meas
  let Lk : Kernel Θ (Fin n → U) := Kernel.mk (fun θ => Measure.pi fun i : Fin n => lam i θ) hL_meas
  haveI hKmrk : IsMarkovKernel Kk :=
    ⟨fun θ => show IsProbabilityMeasure (Measure.pi fun i : Fin n => kap i θ) from inferInstance⟩
  haveI hLmrk : IsMarkovKernel Lk :=
    ⟨fun θ => show IsProbabilityMeasure (Measure.pi fun i : Fin n => lam i θ) from inferInstance⟩
  haveI hKfin : IsFiniteKernel Kk := inferInstance
  haveI hLfin : IsFiniteKernel Lk := inferInstance
  have hν : (Qpost : Measure Θ).bind (fun θ =>
        Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n => kap i θ))
      = (Qpost : Measure Θ) ⊗ₘ Kk := by
    have hfun : (fun θ => Measure.map (fun u : Fin n → U => (θ, u))
          (Measure.pi fun i : Fin n => kap i θ)) = ⇑(Kernel.id ×ₖ Kk) := by
      funext θ
      simp only [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod, Kk]
      rfl
    rw [Measure.compProd_eq_comp_prod, hfun]
  have hμ : (HP : Measure Θ).bind (fun θ =>
        Measure.map (fun u : Fin n → U => (θ, u)) (Measure.pi fun i : Fin n => lam i θ))
      = (HP : Measure Θ) ⊗ₘ Lk := by
    have hfun : (fun θ => Measure.map (fun u : Fin n → U => (θ, u))
          (Measure.pi fun i : Fin n => lam i θ)) = ⇑(Kernel.id ×ₖ Lk) := by
      funext θ
      simp only [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod, Lk]
      rfl
    rw [Measure.compProd_eq_comp_prod, hfun]
  have hbridge : InformationTheory.klDiv ((Qpost : Measure Θ) ⊗ₘ Kk) ((HP : Measure Θ) ⊗ₘ Lk)
      = InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ)
        + ∫⁻ θ, InformationTheory.klDiv (Kk θ) (Lk θ) ∂(Qpost : Measure Θ) := by
    by_cases hQ : (Qpost : Measure Θ) ≪ (HP : Measure Θ) ∧ ∀ᵐ θ ∂(Qpost : Measure Θ), Kk θ ≪ Lk θ
    · obtain ⟨hQ1, hQ2⟩ := hQ
      haveI hsig : SigmaFinite ((HP : Measure Θ) ⊗ₘ Lk) := by
        rw [Measure.compProd_eq_comp_prod]
        infer_instance
      have hdens := statopia_math_node_2313301504_0c50d598 (Qpost : Measure Θ) (HP : Measure Θ)
        Kk Lk hQ1 hQ2
      have hwith := statopia_math_node_3689113668_206332b7 (Qpost : Measure Θ) Kk Lk hQ2
      have hAC : (Qpost : Measure Θ) ⊗ₘ Kk ≪ (HP : Measure Θ) ⊗ₘ Lk :=
        Measure.AbsolutelyContinuous.compProd_of_compProd (κ := Kk) (η := Lk) hQ1 hwith.2
      have hmass : ∀ᵐ θ ∂(Qpost : Measure Θ),
          ∫⁻ u, (Kernel.rnDeriv Kk Lk) θ u ∂(Lk θ) = 1 := by
        filter_upwards [hQ2] with θ hθ
        have hm_eq : (Kernel.rnDeriv Kk Lk) θ =ᵐ[Lk θ] Measure.rnDeriv (Kk θ) (Lk θ) :=
          Kernel.rnDeriv_eq_rnDeriv_measure (κ := Kk) (η := Lk) (a := θ)
        have hwd' : (Lk θ).withDensity (Measure.rnDeriv (Kk θ) (Lk θ)) = Kk θ :=
          Measure.withDensity_rnDeriv_eq (Kk θ) (Lk θ) hθ
        have hmeas : Measurable (Measure.rnDeriv (Kk θ) (Lk θ)) :=
          (Measure.haveLebesgueDecomposition_spec (Kk θ) (Lk θ)).1
        have hmul := MeasureTheory.lintegral_withDensity_eq_lintegral_mul (Lk θ) hmeas
          (g := fun _ => (1 : ℝ≥0∞)) measurable_const
        rw [hwd', lintegral_const, one_mul] at hmul
        simp only [Pi.mul_apply, mul_one] at hmul
        rw [lintegral_congr_ae hm_eq, ← hmul]
        simp
      have hQmass :
          ∫⁻ θ, Measure.rnDeriv (Qpost : Measure Θ) (HP : Measure Θ) θ ∂(HP : Measure Θ) = 1 := by
        have hwd : (HP : Measure Θ).withDensity
            (Measure.rnDeriv (Qpost : Measure Θ) (HP : Measure Θ)) = (Qpost : Measure Θ) :=
          Measure.withDensity_rnDeriv_eq (Qpost : Measure Θ) (HP : Measure Θ) hQ1
        have hmeas : Measurable (Measure.rnDeriv (Qpost : Measure Θ) (HP : Measure Θ)) :=
          (Measure.haveLebesgueDecomposition_spec (Qpost : Measure Θ) (HP : Measure Θ)).1
        have hmul := MeasureTheory.lintegral_withDensity_eq_lintegral_mul (HP : Measure Θ) hmeas
          (g := fun _ => (1 : ℝ≥0∞)) measurable_const
        rw [hwd, lintegral_const, one_mul] at hmul
        simp only [Pi.mul_apply, mul_one] at hmul
        rw [← hmul]
        simp
      have hKl : ∀ᵐ θ ∂(Qpost : Measure Θ), InformationTheory.klDiv (Kk θ) (Lk θ)
          = ∫⁻ u, ENNReal.ofReal
              (InformationTheory.klFun (((Kernel.rnDeriv Kk Lk) θ u).toReal)) ∂(Lk θ) := by
        filter_upwards [hQ2] with θ hθ
        rw [InformationTheory.klDiv_eq_lintegral_klFun, if_pos hθ]
        refine lintegral_congr_ae ?_
        filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := Kk) (η := Lk) (a := θ)] with u hu
        rw [hu]
      have hQkl : InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ)
          = ∫⁻ θ, ENNReal.ofReal (InformationTheory.klFun
              ((Measure.rnDeriv (Qpost : Measure Θ) (HP : Measure Θ) θ).toReal))
            ∂(HP : Measure Θ) := by
        rw [InformationTheory.klDiv_eq_lintegral_klFun, if_pos hQ1]
      have hLden : InformationTheory.klDiv ((Qpost : Measure Θ) ⊗ₘ Kk) ((HP : Measure Θ) ⊗ₘ Lk)
          = ∫⁻ p, ENNReal.ofReal (InformationTheory.klFun
              ((Measure.rnDeriv (Qpost : Measure Θ) (HP : Measure Θ) p.1
                * (Kernel.rnDeriv Kk Lk) p.1 p.2).toReal)) ∂((HP : Measure Θ) ⊗ₘ Lk) := by
        rw [InformationTheory.klDiv_eq_lintegral_klFun, if_pos hAC]
        refine lintegral_congr_ae ?_
        filter_upwards [hdens] with p hp
        rw [hp]
      have harith :
          ∫⁻ p, ENNReal.ofReal (InformationTheory.klFun
              ((Measure.rnDeriv (Qpost : Measure Θ) (HP : Measure Θ) p.1
                * (Kernel.rnDeriv Kk Lk) p.1 p.2).toReal)) ∂((HP : Measure Θ) ⊗ₘ Lk)
            = ∫⁻ θ, ENNReal.ofReal (InformationTheory.klFun
                ((Measure.rnDeriv (Qpost : Measure Θ) (HP : Measure Θ) θ).toReal))
                ∂(HP : Measure Θ)
              + ∫⁻ θ, (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun
                  (((Kernel.rnDeriv Kk Lk) θ u).toReal)) ∂(Lk θ)) ∂(Qpost : Measure Θ) := by
        exact statopia_math_node_1317275614_2c6ca56c Qpost HP Kk Lk hQ1 hQ2
      rw [hLden, hQkl, lintegral_congr_ae hKl]
      exact harith
    · obtain ⟨h1, h2⟩ := statopia_math_node_1407967003_c453b7c7 Qpost HP Kk Lk hQ
      exact h1.trans h2.symm
  rw [hν, hμ]
  exact hbridge
  /- @proof-region region.target-node.session.a8316b0fa1630dd8 end -/

end
end Statlib.Imported
