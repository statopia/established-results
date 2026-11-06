import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1972792747_7490ef34 : ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (X Y : ι → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i)) (hY_meas : ∀ i, Measurable (Y i))
    (hX_indep : iIndepFun X μ) (hY_indep : iIndepFun Y μ)
    (hIndep : IndepFun (fun ω (i : ι) => X i ω) (fun ω (i : ι) => Y i ω) μ),
    iIndepFun (fun (i : ι) (ω : Ω) => (X i ω, Y i ω)) μ := by
  /- @proof-region region.target-node.session.aee9b98f4096afbe begin -/
  classical
  intro Ω instΩ μ instμ ι instι X Y hX_meas hY_meas hX_indep hY_indep hIndep
  have hF_meas : Measurable (fun ω (i : ι) => X i ω) := measurable_pi_iff.2 hX_meas
  have hG_meas : Measurable (fun ω (i : ι) => Y i ω) := measurable_pi_iff.2 hY_meas
  have hXmap : Measure.map (fun ω (i : ι) => X i ω) μ = Measure.pi (fun i => Measure.map (X i) μ) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX_meas i).aemeasurable)).1 hX_indep
  have hYmap : Measure.map (fun ω (i : ι) => Y i ω) μ = Measure.pi (fun i => Measure.map (Y i) μ) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY_meas i).aemeasurable)).1 hY_indep
  have hXYmap : Measure.map (fun ω => ((fun i => X i ω), (fun i => Y i ω))) μ
      = (Measure.pi (fun i => Measure.map (X i) μ)).prod
          (Measure.pi (fun i => Measure.map (Y i) μ)) := by
    rw [← hXmap, ← hYmap]
    exact (indepFun_iff_map_prod_eq_prod_map_map hF_meas.aemeasurable hG_meas.aemeasurable).1 hIndep
  have hpair_marg : ∀ i, Measure.map (fun ω => (X i ω, Y i ω)) μ
      = (Measure.map (X i) μ).prod (Measure.map (Y i) μ) := by
    intro i
    exact (indepFun_iff_map_prod_eq_prod_map_map (hX_meas i).aemeasurable
      (hY_meas i).aemeasurable).1 (hIndep.comp (measurable_pi_apply i) (measurable_pi_apply i))
  have hprobX : ∀ i, IsProbabilityMeasure (Measure.map (X i) μ) :=
    fun i => MeasureTheory.Measure.isProbabilityMeasure_map (hX_meas i).aemeasurable
  have hprobY : ∀ i, IsProbabilityMeasure (Measure.map (Y i) μ) :=
    fun i => MeasureTheory.Measure.isProbabilityMeasure_map (hY_meas i).aemeasurable
  have hkey : ∀ (ρ τ : ι → Measure ℝ), (∀ i, IsProbabilityMeasure (ρ i)) →
      (∀ i, IsProbabilityMeasure (τ i)) →
      Measure.map (fun p : (ι → ℝ) × (ι → ℝ) => fun i => (p.1 i, p.2 i))
        ((Measure.pi ρ).prod (Measure.pi τ)) = Measure.pi (fun i => (ρ i).prod (τ i)) := by
    intro ρ τ hρ hτ
    haveI : ∀ i, IsProbabilityMeasure (ρ i) := hρ
    haveI : ∀ i, IsProbabilityMeasure (ρ i) := hρ
    haveI : ∀ i, IsProbabilityMeasure (τ i) := hτ
    have hsρ : ∀ i, SigmaFinite (ρ i) := fun i => inferInstance
    haveI : ∀ i, SigmaFinite (ρ i) := hsρ
    have hsτ : ∀ i, SigmaFinite (τ i) := fun i => inferInstance
    haveI : ∀ i, SigmaFinite (τ i) := hsτ
    haveI hσ : ∀ p : ι ⊕ ι, SigmaFinite (Sum.elim ρ τ p) := by
      intro p
      cases p with
      | inl i => exact hsρ i
      | inr i => exact hsτ i
    have he : ∀ g : ι ⊕ ι → ℝ,
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ)) g
          = (fun i => g (Sum.inl i), fun i => g (Sum.inr i)) := by
      intro g
      rfl
    have hmp : (Measure.pi ρ).prod (Measure.pi τ)
        = Measure.map (⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ)))
            (Measure.pi (Sum.elim ρ τ)) := by
      have h := measurePreserving_sumPiEquivProdPi (Sum.elim ρ τ)
      simpa using h.map_eq.symm
    have hΘ_meas : Measurable (fun q : ι → ℝ × ℝ => fun p : ι ⊕ ι =>
        Sum.elim (fun i => (q i).1) (fun i => (q i).2) p) := by
      rw [measurable_pi_iff]
      intro p
      cases p with
      | inl i => exact measurable_fst.comp (measurable_pi_apply i)
      | inr i => exact measurable_snd.comp (measurable_pi_apply i)
    haveI : ∀ i, SigmaFinite ((ρ i).prod (τ i)) := fun i => inferInstance
    have hA : Measure.pi (Sum.elim ρ τ)
        = Measure.map (fun q : ι → ℝ × ℝ => fun p : ι ⊕ ι =>
            Sum.elim (fun i => (q i).1) (fun i => (q i).2) p)
          (Measure.pi (fun i => (ρ i).prod (τ i))) := by
      refine Measure.pi_eq (fun t ht => ?_)
      have hbox : MeasurableSet (Set.univ.pi t) := MeasurableSet.univ_pi ht
      rw [Measure.map_apply hΘ_meas hbox]
      have hpre : (fun q : ι → ℝ × ℝ => fun p : ι ⊕ ι =>
          Sum.elim (fun i => (q i).1) (fun i => (q i).2) p) ⁻¹' (Set.univ.pi t)
          = Set.univ.pi (fun i => t (Sum.inl i) ×ˢ t (Sum.inr i)) := by
        ext q
        rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_univ_pi]
        constructor
        · intro h i
          exact ⟨h (Sum.inl i), h (Sum.inr i)⟩
        · intro h p
          cases p with
          | inl i => exact (h i).1
          | inr i => exact (h i).2
      rw [hpre, Measure.pi_pi]
      have h1 : ∀ i : ι, ((ρ i).prod (τ i)) (t (Sum.inl i) ×ˢ t (Sum.inr i))
          = (ρ i) (t (Sum.inl i)) * (τ i) (t (Sum.inr i)) := by
        intro i
        rw [Measure.prod_prod]
      rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_mul_distrib,
        Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
    have hΨ_meas : Measurable (fun p : (ι → ℝ) × (ι → ℝ) =>
        fun i => (p.1 i, p.2 i)) := by
      measurability
    have hψ_meas : Measurable (fun g : ι ⊕ ι → ℝ =>
        ((fun i => g (Sum.inl i)), (fun i => g (Sum.inr i)))) := by
      have ha : Measurable (fun g : ι ⊕ ι → ℝ => fun i => g (Sum.inl i)) := by
        rw [measurable_pi_iff]
        intro i
        exact measurable_pi_apply (Sum.inl i)
      have hb : Measurable (fun g : ι ⊕ ι → ℝ => fun i => g (Sum.inr i)) := by
        rw [measurable_pi_iff]
        intro i
        exact measurable_pi_apply (Sum.inr i)
      measurability
    have hψ_meas2 : Measurable (fun g : ι ⊕ ι → ℝ =>
        fun i => (g (Sum.inl i), g (Sum.inr i))) := by
      rw [measurable_pi_iff]
      intro i
      have h1 : Measurable (fun g : ι ⊕ ι → ℝ => g (Sum.inl i)) :=
        measurable_pi_apply (Sum.inl i)
      have h2 : Measurable (fun g : ι ⊕ ι → ℝ => g (Sum.inr i)) :=
        measurable_pi_apply (Sum.inr i)
      measurability
    have he_meas : Measurable (⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ))) := by
      have hEq : ⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ))
          = fun g : ι ⊕ ι → ℝ => ((fun i => g (Sum.inl i)), (fun i => g (Sum.inr i))) :=
        funext he
      rw [hEq]
      exact hψ_meas
    have hψe : (fun p : (ι → ℝ) × (ι → ℝ) => fun i => (p.1 i, p.2 i))
        ∘ (⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ)))
        = fun g : ι ⊕ ι → ℝ => fun i => (g (Sum.inl i), g (Sum.inr i)) := by
      funext g i
      simp only [Function.comp_apply, he g]
    have hψΘ : (fun g : ι ⊕ ι → ℝ => fun i => (g (Sum.inl i), g (Sum.inr i)))
        ∘ (fun q : ι → ℝ × ℝ => fun p : ι ⊕ ι =>
            Sum.elim (fun i => (q i).1) (fun i => (q i).2) p)
        = id := by
      funext q i
      simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
      exact Prod.ext rfl rfl
    rw [hmp]
    rw [Measure.map_map hΨ_meas he_meas]
    rw [hψe]
    rw [hA]
    rw [Measure.map_map hψ_meas2 hΘ_meas]
    rw [hψΘ, Measure.map_id]
  have hmain : Measure.map (fun ω (i : ι) => (X i ω, Y i ω)) μ
      = Measure.pi (fun i => (Measure.map (X i) μ).prod (Measure.map (Y i) μ)) := by
    have hFG_meas : Measurable (fun ω => ((fun i => X i ω), (fun i => Y i ω))) := by
      measurability
    have hφ_meas : Measurable (fun p : (ι → ℝ) × (ι → ℝ) => fun i => (p.1 i, p.2 i)) := by
      measurability
    have hfac : (fun ω (i : ι) => (X i ω, Y i ω))
        = (fun p : (ι → ℝ) × (ι → ℝ) => fun i => (p.1 i, p.2 i))
          ∘ (fun ω => ((fun i => X i ω), (fun i => Y i ω))) := rfl
    rw [hfac, ← Measure.map_map hφ_meas hFG_meas, hXYmap]
    exact hkey _ _ hprobX hprobY
  refine (iIndepFun_iff_map_fun_eq_pi_map (fun i => ?_)).2 ?_
  · have h1 := hX_meas i
    have h2 := hY_meas i
    measurability
  · have hfin : (fun i => Measure.map (fun ω => (X i ω, Y i ω)) μ)
        = (fun i => (Measure.map (X i) μ).prod (Measure.map (Y i) μ)) := funext hpair_marg
    rw [hfin, hmain]

  /- @proof-region region.target-node.session.aee9b98f4096afbe end -/

end Statlib.Imported

