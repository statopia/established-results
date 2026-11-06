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
theorem statopia_math_node_1948823760_a64561a6 : ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {κ : Type*} [Fintype κ] {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : κ → Ω → α) (g : κ → Ω → β)
    (hf_indep : iIndepFun f μ) (hg_indep : iIndepFun g μ)
    (hfg_indep : ProbabilityTheory.IndepFun (fun ω (i : κ) => f i ω)
      (fun ω (i : κ) => g i ω) μ)
    (hf_meas : ∀ i : κ, AEMeasurable (f i) μ)
    (hg_meas : ∀ i : κ, AEMeasurable (g i) μ),
    iIndepFun (fun (i : κ) (ω : Ω) => (f i ω, g i ω)) μ := by
  /- @proof-region region.target-node.session.491a91c6769ab759 begin -/
  classical
  intro Ω instΩ μ instμ κ instκ α β instα instβ f g hf_indep hg_indep hfg_indep hf_meas hg_meas
  have hP : ∀ i : κ, AEMeasurable (fun ω : Ω => (f i ω, g i ω)) μ :=
    fun i => (hf_meas i).prodMk (hg_meas i)
  refine (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hP).mpr ?_
  have hindep_i : ∀ i : κ, ProbabilityTheory.IndepFun (f i) (g i) μ := by
    intro i
    have h := hfg_indep.comp (measurable_pi_apply i) (measurable_pi_apply i)
    simpa using h
  have hν : ∀ i : κ, Measure.map (fun ω : Ω => (f i ω, g i ω)) μ
      = (Measure.map (f i) μ).prod (Measure.map (g i) μ) := by
    intro i
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map (hf_meas i) (hg_meas i)).mp
      (hindep_i i)
  let R : Set (Set (α × β)) :=
    {t | ∃ a : Set α, ∃ b : Set β, MeasurableSet a ∧ MeasurableSet b ∧ t = a ×ˢ b}
  have hgen : MeasurableSpace.generateFrom R = (inferInstance : MeasurableSpace (α × β)) := by
    have hbaseα : (inferInstance : MeasurableSpace α)
        = MeasurableSpace.generateFrom {t : Set α | MeasurableSet t} := by
      refine le_antisymm ?_ (MeasurableSpace.generateFrom_le (fun t ht => ht))
      intro t ht
      exact MeasurableSpace.measurableSet_generateFrom ht
    have hbaseβ : (inferInstance : MeasurableSpace β)
        = MeasurableSpace.generateFrom {t : Set β | MeasurableSet t} := by
      refine le_antisymm ?_ (MeasurableSpace.generateFrom_le (fun t ht => ht))
      intro t ht
      exact MeasurableSpace.measurableSet_generateFrom ht
    refine le_antisymm ?_ ?_
    · refine MeasurableSpace.generateFrom_le ?_
      rintro t ⟨a, b, ha, hb, rfl⟩
      exact ha.prod hb
    · have h1 : MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace α)
          ≤ MeasurableSpace.generateFrom R := by
        rw [hbaseα, MeasurableSpace.comap_generateFrom]
        refine MeasurableSpace.generateFrom_mono ?_
        rintro t ⟨s, hs, rfl⟩
        exact ⟨s, Set.univ, hs, MeasurableSet.univ, by ext p; simp⟩
      have h2 : MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace β)
          ≤ MeasurableSpace.generateFrom R := by
        rw [hbaseβ, MeasurableSpace.comap_generateFrom]
        refine MeasurableSpace.generateFrom_mono ?_
        rintro t ⟨s, hs, rfl⟩
        exact ⟨Set.univ, s, MeasurableSet.univ, hs, by ext p; simp⟩
      exact sup_le h1 h2
  have hpiR : IsPiSystem R := by
    intro t1 ht1 t2 ht2 hne
    obtain ⟨a1, b1, ha1, hb1, h1⟩ := ht1
    obtain ⟨a2, b2, ha2, hb2, h2⟩ := ht2
    refine ⟨a1 ∩ a2, b1 ∩ b2, ha1.inter ha2, hb1.inter hb2, ?_⟩
    rw [h1, h2]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_prod, and_assoc, and_left_comm]
  have hfss : ∀ i : κ, (Measure.map (fun ω : Ω => (f i ω, g i ω)) μ).FiniteSpanningSetsIn R := by
    intro i
    refine ⟨fun (_ : ℕ) => Set.univ, ?_, ?_, ?_⟩
    · intro j
      exact ⟨Set.univ, Set.univ, MeasurableSet.univ, MeasurableSet.univ, by ext p; simp⟩
    · intro j
      simp
    · ext p
      simp only [Set.mem_iUnion, Set.mem_univ]
      exact ⟨fun _ => trivial, fun _ => ⟨0, trivial⟩⟩
  have hbox : ∀ s : κ → Set (α × β), (∀ i, s i ∈ R) →
      Measure.map (fun ω (i : κ) => (f i ω, g i ω)) μ (Set.univ.pi s)
        = ∏ i, (Measure.map (fun ω : Ω => (f i ω, g i ω)) μ) (s i) := by
    intro s hs
    have hs' : ∀ i : κ, ∃ a : Set α, ∃ b : Set β,
        MeasurableSet a ∧ MeasurableSet b ∧ s i = a ×ˢ b := fun i => hs i
    choose a b hab using hs'
    have ha : ∀ i : κ, MeasurableSet (a i) := fun i => (hab i).1
    have hb : ∀ i : κ, MeasurableSet (b i) := fun i => (hab i).2.1
    have hsab : ∀ i : κ, s i = a i ×ˢ b i := fun i => (hab i).2.2
    have hP' : ∀ i : κ, ∃ G : Ω → α × β,
        Measurable G ∧ (fun ω => (f i ω, g i ω)) =ᵐ[μ] G := fun i => hP i
    choose F hFm hFae using hP'
    have hPairM : Measurable (fun ω (i : κ) => F i ω) := measurable_pi_iff.mpr hFm
    have hPairAe : (fun ω (i : κ) => (f i ω, g i ω)) =ᵐ[μ] fun ω (i : κ) => F i ω := by
      filter_upwards [Filter.eventually_all.mpr hFae] with ω hω
      funext i
      exact hω i
    have hmapbox : ∀ C : Set (κ → α × β), MeasurableSet C →
        (Measure.map (fun ω (i : κ) => (f i ω, g i ω)) μ) C
          = μ ((fun ω (i : κ) => (f i ω, g i ω)) ⁻¹' C) := by
      intro C hC
      rw [Measure.map_congr hPairAe, Measure.map_apply hPairM hC]
      refine measure_congr ?_
      filter_upwards [Filter.eventually_all.mpr hFae] with ω hω
      have hfun : (fun i => (f i ω, g i ω)) = fun i => F i ω := funext hω
      change ((fun i => F i ω) ∈ C) = ((fun i => (f i ω, g i ω)) ∈ C)
      rw [hfun]
    have hmapf : ∀ i : κ, (Measure.map (f i) μ) (a i) = μ (f i ⁻¹' a i) := by
      intro i
      obtain ⟨f', hf'm, hf'ae⟩ := hf_meas i
      rw [Measure.map_congr hf'ae, Measure.map_apply hf'm (ha i)]
      refine measure_congr ?_
      filter_upwards [hf'ae] with ω hω
      change (f' ω ∈ a i) = (f i ω ∈ a i)
      rw [hω]
    have hmapg : ∀ i : κ, (Measure.map (g i) μ) (b i) = μ (g i ⁻¹' b i) := by
      intro i
      obtain ⟨g', hg'm, hg'ae⟩ := hg_meas i
      rw [Measure.map_congr hg'ae, Measure.map_apply hg'm (hb i)]
      refine measure_congr ?_
      filter_upwards [hg'ae] with ω hω
      change (g' ω ∈ b i) = (g i ω ∈ b i)
      rw [hω]
    have hset : (fun ω (i : κ) => (f i ω, g i ω)) ⁻¹' (Set.univ.pi (fun i => a i ×ˢ b i))
        = ⋂ i, (f i ⁻¹' a i ∩ g i ⁻¹' b i) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter, Set.mem_inter_iff,
        Set.mem_prod]
    have hset2 : (⋂ i, (f i ⁻¹' a i ∩ g i ⁻¹' b i))
        = (⋂ i, f i ⁻¹' a i) ∩ (⋂ i, g i ⁻¹' b i) := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩,
        fun h i => ⟨h.1 i, h.2 i⟩⟩
    have hpreA : (fun ω (i : κ) => f i ω) ⁻¹' (Set.univ.pi a) = ⋂ i, f i ⁻¹' a i := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    have hpreB : (fun ω (i : κ) => g i ω) ⁻¹' (Set.univ.pi b) = ⋂ i, g i ⁻¹' b i := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    have hcross : μ ((⋂ i, f i ⁻¹' a i) ∩ (⋂ i, g i ⁻¹' b i))
        = μ (⋂ i, f i ⁻¹' a i) * μ (⋂ i, g i ⁻¹' b i) := by
      have h := (ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.mp hfg_indep
        (Set.univ.pi a) (Set.univ.pi b) (MeasurableSet.univ_pi ha) (MeasurableSet.univ_pi hb))
      rw [hpreA, hpreB] at h
      exact h
    have hfprod : μ (⋂ i, f i ⁻¹' a i) = ∏ i, μ (f i ⁻¹' a i) := by
      have h := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hf_indep)
        Finset.univ (sets := a) (fun i _ => ha i)
      simpa using h
    have hgprod : μ (⋂ i, g i ⁻¹' b i) = ∏ i, μ (g i ⁻¹' b i) := by
      have h := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hg_indep)
        Finset.univ (sets := b) (fun i _ => hb i)
      simpa using h
    have hR : ∏ i, (Measure.map (fun ω : Ω => (f i ω, g i ω)) μ) (s i)
        = ∏ i, (μ (f i ⁻¹' a i) * μ (g i ⁻¹' b i)) := by
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [hsab i, hν i, Measure.prod_prod, hmapf i, hmapg i]
    have hL : (Measure.map (fun ω (i : κ) => (f i ω, g i ω)) μ) (Set.univ.pi s)
        = (∏ i, μ (f i ⁻¹' a i)) * ∏ i, μ (g i ⁻¹' b i) := by
      have h1 : Set.univ.pi s = Set.univ.pi (fun i => a i ×ˢ b i) := by
        rw [show s = (fun i => a i ×ˢ b i) from funext hsab]
      rw [h1, hmapbox _ (MeasurableSet.univ_pi (fun i => (ha i).prod (hb i))),
        hset, hset2, hcross, hfprod, hgprod]
    rw [hL, hR, Finset.prod_mul_distrib]
  exact (Measure.pi_eq_generateFrom
    (μ := fun i : κ => Measure.map (fun ω : Ω => (f i ω, g i ω)) μ)
    (C := fun _ : κ => R) (fun _ => hgen) (fun _ => hpiR) hfss hbox).symm
  /- @proof-region region.target-node.session.491a91c6769ab759 end -/

end Statlib.Imported

