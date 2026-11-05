import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_1154493248_d468b8c9_f8a9fe6a
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
theorem statopia_math_node_1317275614_2c6ca56c : ∀ {Theta U : Type*} [MeasurableSpace Theta] [MeasurableSpace U]
    [MeasurableSpace.CountableOrCountablyGenerated Theta U]
    (Q HP : ProbabilityMeasure Theta) (K L : Kernel Theta U)
    [IsMarkovKernel K] [IsMarkovKernel L]
    (hac : (Q : Measure Theta) ≪ (HP : Measure Theta))
    (hfib : ∀ᵐ theta ∂(Q : Measure Theta), (K theta : Measure U) ≪ (L theta : Measure U)),
    ∫⁻ p : Theta × U, ENNReal.ofReal (InformationTheory.klFun
        (((Measure.rnDeriv (Q : Measure Theta) (HP : Measure Theta)) p.1
          * (Kernel.rnDeriv K L) p.1 p.2).toReal)) ∂((HP : Measure Theta) ⊗ₘ L)
      = ∫⁻ theta, ENNReal.ofReal (InformationTheory.klFun
          (((Measure.rnDeriv (Q : Measure Theta) (HP : Measure Theta)) theta).toReal))
          ∂(HP : Measure Theta)
        + ∫⁻ theta, (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun
            (((Kernel.rnDeriv K L) theta u).toReal)) ∂(L theta))
          ∂(Q : Measure Theta) := by
  /- @proof-region region.target-node.session.03280c64cf7a556f begin -/
  intro Theta U _ _ _ Q HP K L _ _ hac hfib
  have hFub : ∫⁻ p : Theta × U, ENNReal.ofReal (InformationTheory.klFun
        (((Measure.rnDeriv (Q : Measure Theta) (HP : Measure Theta)) p.1
          * (Kernel.rnDeriv K L) p.1 p.2).toReal)) ∂((HP : Measure Theta) ⊗ₘ L)
      = ∫⁻ theta, ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun
          (((Measure.rnDeriv (Q : Measure Theta) (HP : Measure Theta)) theta
            * (Kernel.rnDeriv K L) theta u).toReal)) ∂(L theta) ∂(HP : Measure Theta) :=
    Measure.lintegral_compProd (by measurability)
  rw [hFub]
  set f : Theta → ENNReal := Measure.rnDeriv (Q : Measure Theta) (HP : Measure Theta) with hfdef
  set g : Theta → U → ENNReal := Kernel.rnDeriv K L with hgdef
  haveI hleb : (Q : Measure Theta).HaveLebesgueDecomposition (HP : Measure Theta) :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hfmeas : Measurable f := by
    rw [hfdef]
    exact (Measure.haveLebesgueDecomposition_spec (Q : Measure Theta) (HP : Measure Theta)).1
  have hQeq : (HP : Measure Theta).withDensity f = (Q : Measure Theta) := by
    rw [hfdef]
    exact Measure.withDensity_rnDeriv_eq (Q : Measure Theta) (HP : Measure Theta) hac
  have hfint : ∫⁻ θ, f θ ∂(HP : Measure Theta) = 1 := by
    have h := MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul (μ := (HP : Measure Theta))
      (f := f) (g := fun _ => (1 : ENNReal)) hfmeas measurable_const (s := Set.univ) MeasurableSet.univ
    rw [hQeq] at h
    simpa using h.symm
  have hftop : ∀ᵐ θ ∂(HP : Measure Theta), f θ < ⊤ := by
    have hS : MeasurableSet {θ : Theta | f θ = ⊤} := hfmeas (measurableSet_singleton ⊤)
    have hind : ∫⁻ θ, (Set.indicator {θ : Theta | f θ = ⊤} (fun _ => (1 : ENNReal))) θ
          ∂(HP : Measure Theta) = (HP : Measure Theta) {θ : Theta | f θ = ⊤} := by
      rw [MeasureTheory.lintegral_indicator hS, MeasureTheory.lintegral_one]
      simp [Measure.restrict_apply, hS]
    have hpt : ∀ θ, ⊤ * (Set.indicator {θ : Theta | f θ = ⊤} (fun _ => (1 : ENNReal))) θ ≤ f θ := by
      intro θ
      by_cases h : f θ = ⊤
      · rw [Set.indicator_of_mem (show θ ∈ {θ : Theta | f θ = ⊤} from h)]
        simp [h]
      · rw [Set.indicator_of_notMem (show θ ∉ {θ : Theta | f θ = ⊤} from h)]
        simp
    have hbound : ⊤ * (HP : Measure Theta) {θ : Theta | f θ = ⊤} ≤ 1 := by
      calc ⊤ * (HP : Measure Theta) {θ : Theta | f θ = ⊤}
          = ∫⁻ θ, ⊤ * (Set.indicator {θ : Theta | f θ = ⊤} (fun _ => (1 : ENNReal))) θ
              ∂(HP : Measure Theta) := by
            rw [← hind, ← MeasureTheory.lintegral_const_mul]
            exact measurable_const.indicator hS
        _ ≤ ∫⁻ θ, f θ ∂(HP : Measure Theta) := MeasureTheory.lintegral_mono hpt
        _ = 1 := hfint
    have hzero : ∫⁻ θ, (Set.indicator {θ : Theta | f θ = ⊤} (fun _ => (1 : ENNReal))) θ
          ∂(HP : Measure Theta) = 0 := by
      rw [hind]
      by_contra hne
      have htop : (⊤ : ENNReal) * (HP : Measure Theta) {θ : Theta | f θ = ⊤} = ⊤ := by
        rw [ENNReal.top_mul]
        simp [hne]
      rw [htop] at hbound
      exact absurd hbound (by simp)
    have hae : ∀ᵐ θ ∂(HP : Measure Theta),
        (Set.indicator {θ : Theta | f θ = ⊤} (fun _ => (1 : ENNReal))) θ = 0 :=
      (MeasureTheory.lintegral_eq_zero_iff'
        (measurable_const.indicator hS).aemeasurable).mp hzero
    filter_upwards [hae] with θ hθ
    rw [lt_top_iff_ne_top]
    intro hcon
    have : (Set.indicator {θ : Theta | f θ = ⊤} (fun _ => (1 : ENNReal))) θ = 1 :=
      Set.indicator_of_mem (show θ ∈ {θ : Theta | f θ = ⊤} from hcon) _
    rw [this] at hθ
    exact one_ne_zero hθ
  have hgmeas : Measurable (Function.uncurry g) := by
    rw [hgdef]
    exact Kernel.measurable_rnDeriv K L
  have hgmass : ∀ᵐ θ ∂(Q : Measure Theta), ∫⁻ u, g θ u ∂(L θ) = 1 := by
    filter_upwards [hfib] with θ hθ
    have hwith : (L.withDensity g) θ = K θ := by
      rw [hgdef]
      exact Kernel.withDensity_rnDeriv_eq hθ
    have hlint : ∫⁻ u, (1 : ENNReal) ∂(L.withDensity g) θ = ∫⁻ u, g θ u * (1 : ENNReal) ∂(L θ) :=
      Kernel.lintegral_withDensity L hgmeas θ measurable_const
    rw [hwith, MeasureTheory.lintegral_one, measure_univ] at hlint
    simpa using hlint.symm
  have hAmeas : Measurable fun θ => ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((g θ u).toReal)) ∂(L θ) :=
    Measurable.lintegral_kernel_prod_right (κ := L) (by measurability)
  have hcm : ∫⁻ θ, (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((g θ u).toReal)) ∂(L θ)) ∂(Q : Measure Theta)
      = ∫⁻ θ, f θ * (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((g θ u).toReal)) ∂(L θ)) ∂(HP : Measure Theta) := by
    have h := MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul (μ := (HP : Measure Theta))
      (f := f) (g := fun θ => ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((g θ u).toReal)) ∂(L θ))
      hfmeas hAmeas (s := Set.univ) MeasurableSet.univ
    rw [hQeq] at h
    simpa using h
  have hfib_eq : ∀ᵐ θ ∂(HP : Measure Theta),
      ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((f θ * g θ u).toReal)) ∂(L θ)
        = ENNReal.ofReal (InformationTheory.klFun ((f θ).toReal))
          + f θ * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((g θ u).toReal)) ∂(L θ) := by
    have hgslice : ∀ θ : Theta, Measurable fun u => g θ u := by
      intro θ
      have hpair : Measurable fun u : U => (θ, u) := by measurability
      exact hgmeas.comp hpair
    set phi : Theta → ENNReal :=
      fun θ => ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((f θ * g θ u).toReal)) ∂(L θ) with hphidef
    set psi : Theta → ENNReal :=
      fun θ => ENNReal.ofReal (InformationTheory.klFun ((f θ).toReal))
        + f θ * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((g θ u).toReal)) ∂(L θ) with hpsidef
    have hphimeas : Measurable phi := by
      rw [hphidef]
      exact Measurable.lintegral_kernel_prod_right (κ := L) (by measurability)
    have hpsimeas : Measurable psi := by
      rw [hpsidef]
      have hmY' : Measurable fun θ => ENNReal.ofReal (InformationTheory.klFun ((f θ).toReal)) := by
        measurability
      exact hmY'.add (hfmeas.mul hAmeas)
    have hQae : phi =ᶠ[ae (Q : Measure Theta)] psi := by
      have hftopQ : ∀ᵐ θ ∂(Q : Measure Theta), f θ < ⊤ := hftop.filter_mono hac.ae_le
      filter_upwards [hgmass, hftopQ] with θ hmass htop
      exact statopia_math_node_1154493248_d468b8c9 (L θ) (fun u => g θ u) (hgslice θ) hmass
        (f θ) (ne_of_lt htop)
    set G : Theta → ENNReal := fun θ => (phi θ - psi θ) ⊔ (psi θ - phi θ) with hGdef
    have hGmeas : Measurable G := by
      rw [hGdef]
      exact (hphimeas.sub hpsimeas).sup (hpsimeas.sub hphimeas)
    have hGae : G =ᶠ[ae (Q : Measure Theta)] 0 := by
      filter_upwards [hQae] with θ hθ
      rw [hGdef]
      simp [hθ]
    have hG0 : ∫⁻ θ, G θ ∂(Q : Measure Theta) = 0 := by
      rw [MeasureTheory.lintegral_congr_ae hGae]
      simp
    have hchange : ∫⁻ θ, G θ ∂(Q : Measure Theta) = ∫⁻ θ, f θ * G θ ∂(HP : Measure Theta) := by
      have h := MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul (μ := (HP : Measure Theta))
        (f := f) (g := G) hfmeas hGmeas (s := Set.univ) MeasurableSet.univ
      rw [hQeq] at h
      simpa using h
    have hprod : (fun θ => f θ * G θ) =ᶠ[ae (HP : Measure Theta)] 0 :=
      (MeasureTheory.lintegral_eq_zero_iff' (hfmeas.mul hGmeas).aemeasurable).mp (by
        rw [← hchange]
        exact hG0)
    filter_upwards [hprod] with θ hθ
    by_cases hf0 : f θ = 0
    · have hZ : ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((f θ * g θ u).toReal)) ∂(L θ)
          = ENNReal.ofReal (InformationTheory.klFun 0) := by
        have hfun : (fun u => ENNReal.ofReal (InformationTheory.klFun ((f θ * g θ u).toReal)))
            = fun _ => ENNReal.ofReal (InformationTheory.klFun 0) := by
          funext u
          simp [hf0]
        rw [hfun]
        simp
      rw [hZ, hf0]
      simp
    · have hGθ : G θ = 0 := by
        rcases mul_eq_zero.mp hθ with h | h
        · exact absurd h hf0
        · exact h
      have h1 : phi θ - psi θ = 0 := by
        refine le_antisymm ?_ (zero_le _)
        rw [← hGθ]
        exact le_sup_left
      have h2 : psi θ - phi θ = 0 := by
        refine le_antisymm ?_ (zero_le _)
        rw [← hGθ]
        exact le_sup_right
      show phi θ = psi θ
      exact le_antisymm (tsub_eq_zero_iff_le.mp h1) (tsub_eq_zero_iff_le.mp h2)
  have hmY : Measurable fun θ => ENNReal.ofReal (InformationTheory.klFun ((f θ).toReal)) := by
    measurability
  have hstep1 : ∫⁻ θ, (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((f θ * g θ u).toReal)) ∂(L θ)) ∂(HP : Measure Theta)
      = ∫⁻ θ, (ENNReal.ofReal (InformationTheory.klFun ((f θ).toReal))
          + f θ * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((g θ u).toReal)) ∂(L θ)) ∂(HP : Measure Theta) :=
    MeasureTheory.lintegral_congr_ae hfib_eq
  have hstep2 : ∫⁻ θ, (ENNReal.ofReal (InformationTheory.klFun ((f θ).toReal))
        + f θ * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((g θ u).toReal)) ∂(L θ)) ∂(HP : Measure Theta)
      = ∫⁻ θ, ENNReal.ofReal (InformationTheory.klFun ((f θ).toReal)) ∂(HP : Measure Theta)
        + ∫⁻ θ, f θ * (∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((g θ u).toReal)) ∂(L θ)) ∂(HP : Measure Theta) :=
    MeasureTheory.lintegral_add_left hmY
      (fun θ => f θ * ∫⁻ u, ENNReal.ofReal (InformationTheory.klFun ((g θ u).toReal)) ∂(L θ))
  rw [hstep1, hstep2, hcm]
  /- @proof-region region.target-node.session.03280c64cf7a556f end -/

end
end Statlib.Imported
