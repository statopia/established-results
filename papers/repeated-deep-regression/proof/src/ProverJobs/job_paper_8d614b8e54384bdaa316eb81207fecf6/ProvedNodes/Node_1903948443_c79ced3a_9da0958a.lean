import Statlib.StatFoundation.Vocabulary.EmpiricalProcess
import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base

namespace PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open _root_.PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
noncomputable section
set_option maxHeartbeats 1000000

set_option autoImplicit false in
theorem statopia_math_node_1903948443_c79ced3a : ∀ (p : ℕ) (hp : 0 < p)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α]
    (ε : Fin p → Ω → ℝ) (Z : Fin p → Ω → α)
    (h_eps_meas : ∀ k, Measurable (ε k))
    (h_eps_law : ∀ k, Measure.map (ε k) μ = rademacherLaw)
    (h_eps_indep : iIndepFun ε μ)
    (h_Z_meas : ∀ k, Measurable (Z k))
    (h_indep : IndepFun (fun ω => fun k => ε k ω) (fun ω => fun k => Z k ω) μ)
    (Phi : (Fin p → ℝ) → (Fin p → α) → ℝ)
    (hPhi_meas : Measurable (fun q : (Fin p → ℝ) × (Fin p → α) => Phi q.1 q.2))
    (C : ℝ) (hPhi_bound : ∀ (s : Fin p → ℝ) (x : Fin p → α), |Phi s x| ≤ C),
    ∫ ω, ((Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
        ∑ s : Fin p → Bool,
          Phi (fun k => if s k = true then (1 : ℝ) else -1) (fun k => Z k ω)) ∂μ
      = ∫ ω, Phi (fun k => ε k ω) (fun k => Z k ω) ∂μ := by
  /- @proof-region region.target-node.session.d6ba91062416e335 begin -/
  intro p hp Ω _ μ _ α _ ε Z hε_meas hε_law hε_indep hZ_meas h_indep Φ hΦ_meas C hC
  have hsign_meas : Measurable (Statlib.StatFoundation.Vocabulary.rademacherSign : Bool → ℝ) := by
    show Measurable (fun b : Bool => if b = true then (1 : ℝ) else -1)
    have h : (fun b : Bool => if b = true then (1 : ℝ) else -1)
        = fun b => if b ∈ ({true} : Set Bool) then (1 : ℝ) else -1 := by
      funext b
      simp [Set.mem_singleton_iff]
    rw [h]
    exact Measurable.ite (measurableSet_singleton true) measurable_const measurable_const
  have hεv_meas : Measurable (fun ω : Ω => fun k => ε k ω) := measurable_pi_iff.2 hε_meas
  have hZv_meas : Measurable (fun ω : Ω => fun k => Z k ω) := measurable_pi_iff.2 hZ_meas
  have hS_meas :
      Measurable (fun t : Fin p → Bool => fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) := by
    refine measurable_pi_iff.2 (fun k => ?_)
    exact hsign_meas.comp ((measurable_pi_iff.mp measurable_id) k)
  haveI hAprob : IsProbabilityMeasure (Measure.map (fun ω : Ω => fun k => ε k ω) μ) :=
    Measure.isProbabilityMeasure_map hεv_meas.aemeasurable
  haveI hBprob : IsProbabilityMeasure (Measure.map (fun ω : Ω => fun k => Z k ω) μ) :=
    Measure.isProbabilityMeasure_map hZv_meas.aemeasurable
  have hpair_meas : Measurable (fun q : (Fin p → α) × (Fin p → ℝ) => (q.2, q.1)) :=
    measurable_snd.prod measurable_fst
  have hΦ'_meas : Measurable (fun q : (Fin p → α) × (Fin p → ℝ) => Φ q.2 q.1) :=
    hΦ_meas.comp hpair_meas
  have hpZ_meas : ∀ s : Fin p → ℝ,
      Measurable (fun ω : Ω => (s, fun k => Z k ω)) := by
    intro s
    refine Measurable.prod (f := fun ω : Ω => (s, fun k => Z k ω)) ?_ ?_
    · simpa using (measurable_const : Measurable fun _ : Ω => s)
    · simpa using hZv_meas
  have hxZ_meas : ∀ s : Fin p → ℝ,
      Measurable (fun x : Fin p → α => (s, x)) := by
    intro s
    refine Measurable.prod (f := fun x : Fin p → α => (s, x)) ?_ ?_
    · simpa using (measurable_const : Measurable fun _ : Fin p → α => s)
    · simpa using (measurable_id : Measurable fun x : Fin p → α => x)
  have hIntμ : ∀ s : Fin p → ℝ, Integrable (fun ω : Ω => Φ s (fun k => Z k ω)) μ := by
    intro s
    refine Integrable.of_bound ?_ C ?_
    · exact (hΦ_meas.comp (hpZ_meas s)).aestronglyMeasurable
    · filter_upwards with ω
      simpa [Real.norm_eq_abs] using hC s (fun k => Z k ω)
  have hIntB : ∀ s : Fin p → ℝ,
      Integrable (fun x : Fin p → α => Φ s x) (Measure.map (fun ω : Ω => fun k => Z k ω) μ) := by
    intro s
    refine Integrable.of_bound ?_ C ?_
    · exact (hΦ_meas.comp (hxZ_meas s)).aestronglyMeasurable
    · filter_upwards with x
      simpa [Real.norm_eq_abs] using hC s x
  have hL : ∫ ω, ((Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
        ∑ s : Fin p → Bool,
          Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (s k)) (fun k => Z k ω)) ∂μ
      = (Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
        ∑ s : Fin p → Bool,
          ∫ ω, Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (s k)) (fun k => Z k ω) ∂μ := by
    rw [integral_const_mul]
    exact congrArg (fun z => (Fintype.card (Fin p → Bool) : ℝ)⁻¹ * z)
      (integral_finset_sum Finset.univ
        (fun s _ => hIntμ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (s k))))
  have hE : ∀ s : Fin p → Bool,
        ∫ ω, Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (s k)) (fun k => Z k ω) ∂μ
      = ∫ x, Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (s k)) x ∂(Measure.map (fun ω : Ω => fun k => Z k ω) μ) := by
    intro s
    exact (integral_map hZv_meas.aemeasurable
      ((hΦ_meas.comp (hxZ_meas (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (s k)))).aestronglyMeasurable)).symm
  have hradem_prob : IsProbabilityMeasure rademacherLaw := by
    have h := Measure.isProbabilityMeasure_map (μ := μ) (f := ε ⟨0, hp⟩) (hε_meas ⟨0, hp⟩).aemeasurable
    rw [hε_law ⟨0, hp⟩] at h
    exact h
  haveI := hradem_prob
  have hdirac_pre : ∀ (b : Bool) (s : Set ℝ),
      (Measure.dirac b : Measure Bool) (Statlib.StatFoundation.Vocabulary.rademacherSign ⁻¹' s)
        = (Measure.dirac (Statlib.StatFoundation.Vocabulary.rademacherSign b) : Measure ℝ) s := by
    intro b s
    rw [Measure.dirac_apply, Measure.dirac_apply]
    by_cases h : Statlib.StatFoundation.Vocabulary.rademacherSign b ∈ s <;> simp [Set.indicator, h]
  have hνB_val : ∀ s : Set ℝ,
      ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false))
          (Statlib.StatFoundation.Vocabulary.rademacherSign ⁻¹' s) = rademacherLaw s := by
    intro s
    have h1 : Statlib.StatFoundation.Vocabulary.rademacherSign true = (1 : ℝ) := by
      simp [Statlib.StatFoundation.Vocabulary.rademacherSign]
    have h2 : Statlib.StatFoundation.Vocabulary.rademacherSign false = (-1 : ℝ) := by
      simp [Statlib.StatFoundation.Vocabulary.rademacherSign]
    have hL : ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false))
        (Statlib.StatFoundation.Vocabulary.rademacherSign ⁻¹' s)
        = (2 : ℝ≥0∞)⁻¹ • ((Measure.dirac (1 : ℝ) : Measure ℝ) s + (Measure.dirac (-1 : ℝ) : Measure ℝ) s) := by
      rw [Measure.smul_apply, Measure.add_apply, hdirac_pre true s, hdirac_pre false s, h1, h2]
    have hR : rademacherLaw s
        = (2 : ℝ≥0∞)⁻¹ • ((Measure.dirac (1 : ℝ) : Measure ℝ) s + (Measure.dirac (-1 : ℝ) : Measure ℝ) s) := by
      have h3 : rademacherLaw
          = (2 : ℝ≥0∞)⁻¹ • ((Measure.dirac (-1 : ℝ) : Measure ℝ) + Measure.dirac 1) := rfl
      rw [h3, Measure.smul_apply, Measure.add_apply, add_comm]
    rw [hL, hR]
  have hνB_univ : ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)) Set.univ = 1 := by
    simpa using (hνB_val Set.univ).trans
      (MeasureTheory.IsProbabilityMeasure.measure_univ (μ := rademacherLaw))
  haveI hνBfin : IsFiniteMeasure ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)) := by
    refine ⟨?_⟩
    rw [hνB_univ]
    exact ENNReal.one_lt_top
  have hA_pi : Measure.map (fun ω : Ω => fun k => ε k ω) μ = Measure.pi (fun _ : Fin p => rademacherLaw) := by
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (μ := μ) (f := ε)
      (fun k => (hε_meas k).aemeasurable)).mp hε_indep
    simpa only [hε_law] using h
  have hA_map : Measure.pi (fun _ : Fin p => rademacherLaw)
      = Measure.map (fun t : Fin p → Bool => fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k))
          (Measure.pi (fun _ : Fin p => ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)))) := by
    refine Measure.pi_eq (μ := fun _ : Fin p => rademacherLaw) (fun u hu => ?_)
    rw [Measure.map_apply hS_meas (MeasurableSet.univ_pi hu)]
    have hpre : (fun t : Fin p → Bool => fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) ⁻¹' (Set.univ.pi u)
        = Set.univ.pi (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign ⁻¹' (u k)) := by
      ext t
      simp [Set.mem_univ_pi]
    rw [hpre, Measure.pi_pi]
    exact Finset.prod_congr rfl (fun k _ => hνB_val (u k))
  have hνB_single : ∀ b : Bool,
      ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)) {b} = (2 : ℝ≥0∞)⁻¹ := by
    intro b
    rw [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply, Measure.dirac_apply]
    cases b <;> simp
  have hmass : ∀ t : Fin p → Bool,
      (Measure.pi (fun _ : Fin p => ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)))) {t}
        = ((2 : ℝ≥0∞)⁻¹) ^ p := by
    intro t
    have hsingle : ({t} : Set (Fin p → Bool)) = Set.univ.pi (fun k => ({t k} : Set Bool)) := by
      ext s
      simp [Set.mem_univ_pi, funext_iff]
    rw [hsingle, Measure.pi_pi]
    have hfac : ∀ k : Fin p,
        ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)) {t k} = (2 : ℝ≥0∞)⁻¹ :=
      fun k => hνB_single (t k)
    simp only [hfac, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcval : (((2 : ℝ≥0∞)⁻¹) ^ p).toReal = (Fintype.card (Fin p → Bool) : ℝ)⁻¹ := by
    have hcard : ((Fintype.card (Fin p → Bool) : ℕ) : ℝ) = (2 : ℝ) ^ p := by
      rw [Fintype.card_fun]
      simp
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv, hcard, inv_pow]
    norm_num
  have hmass_real : ∀ t : Fin p → Bool,
      (Measure.pi (fun _ : Fin p => ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)))).real {t}
        = (Fintype.card (Fin p → Bool) : ℝ)⁻¹ := by
    intro t
    simp only [Measure.real, hmass t, hcval]
  have hinner : ∀ x : Fin p → α,
        ∫ s : Fin p → ℝ, Φ s x ∂(Measure.map (fun ω : Ω => fun k => ε k ω) μ)
      = (Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
        ∑ t : Fin p → Bool, Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) x := by
    intro x
    have hxs_meas : Measurable (fun s : Fin p → ℝ => (s, x)) := by
      refine Measurable.prod (f := fun s : Fin p → ℝ => (s, x)) ?_ ?_
      · simpa using (measurable_id : Measurable fun s : Fin p → ℝ => s)
      · simpa using (measurable_const : Measurable fun _ : Fin p → ℝ => x)
    have hΦx_meas : Measurable (fun s : Fin p → ℝ => Φ s x) := hΦ_meas.comp hxs_meas
    haveI hνqfin : IsFiniteMeasure (Measure.pi (fun _ : Fin p => ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)))) := by
      refine ⟨?_⟩
      rw [Measure.pi_univ]
      have h1 : ∀ _ : Fin p,
          ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)) Set.univ = 1 :=
        fun _ => hνB_univ
      simp [h1]
    have hIntν : Integrable (fun t : Fin p → Bool => Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) x)
        (Measure.pi (fun _ : Fin p => ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)))) := by
      refine Integrable.of_bound ?_ C ?_
      · exact (hΦx_meas.comp hS_meas).aestronglyMeasurable
      · filter_upwards with t
        simpa [Real.norm_eq_abs] using
          hC (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) x
    calc ∫ s : Fin p → ℝ, Φ s x ∂(Measure.map (fun ω : Ω => fun k => ε k ω) μ)
        = ∫ s : Fin p → ℝ, Φ s x ∂(Measure.pi (fun _ : Fin p => rademacherLaw)) := by rw [hA_pi]
      _ = ∫ s : Fin p → ℝ, Φ s x ∂(Measure.map
            (fun t : Fin p → Bool => fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k))
            (Measure.pi (fun _ : Fin p => ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false))))) := by
            rw [hA_map]
      _ = ∫ t : Fin p → Bool, Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) x
            ∂(Measure.pi (fun _ : Fin p => ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)))) :=
            integral_map hS_meas.aemeasurable hΦx_meas.aestronglyMeasurable
      _ = ∑ t : Fin p → Bool,
            (Measure.pi (fun _ : Fin p => ((2 : ℝ≥0∞)⁻¹ • ((Measure.dirac true : Measure Bool) + Measure.dirac false)))).real {t} •
              Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) x :=
            integral_fintype _ hIntν
      _ = ∑ t : Fin p → Bool, (Fintype.card (Fin p → Bool) : ℝ)⁻¹ •
              Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) x := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [hmass_real t]
      _ = (Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
            ∑ t : Fin p → Bool, Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) x := by
            rw [← Finset.smul_sum, smul_eq_mul]
  have hstepD : ∫ x, ((Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
          ∑ t : Fin p → Bool,
            Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) x) ∂(Measure.map (fun ω : Ω => fun k => Z k ω) μ)
      = (Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
          ∑ t : Fin p → Bool,
            ∫ x, Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) x ∂(Measure.map (fun ω : Ω => fun k => Z k ω) μ) := by
    rw [integral_const_mul]
    exact congrArg (fun z => (Fintype.card (Fin p → Bool) : ℝ)⁻¹ * z)
      (integral_finset_sum Finset.univ
        (fun t _ => hIntB (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k))))
  have hjoint : Measure.map (fun ω : Ω => ((fun k => Z k ω), (fun k => ε k ω))) μ
      = (Measure.map (fun ω : Ω => fun k => Z k ω) μ).prod (Measure.map (fun ω : Ω => fun k => ε k ω) μ) :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hZv_meas.aemeasurable
      hεv_meas.aemeasurable).mp h_indep.symm
  have hpairZA_meas : Measurable (fun ω : Ω => ((fun k => Z k ω), (fun k => ε k ω))) :=
    hZv_meas.prod hεv_meas
  have hstepA : ∫ ω, Φ (fun k => ε k ω) (fun k => Z k ω) ∂μ
      = ∫ q : (Fin p → α) × (Fin p → ℝ), Φ q.2 q.1 ∂((Measure.map (fun ω : Ω => fun k => Z k ω) μ).prod (Measure.map (fun ω : Ω => fun k => ε k ω) μ)) := by
    rw [← hjoint]
    exact (integral_map hpairZA_meas.aemeasurable hΦ'_meas.aestronglyMeasurable).symm
  have hstepB : ∫ q : (Fin p → α) × (Fin p → ℝ), Φ q.2 q.1 ∂((Measure.map (fun ω : Ω => fun k => Z k ω) μ).prod (Measure.map (fun ω : Ω => fun k => ε k ω) μ))
      = ∫ x, ∫ s : Fin p → ℝ, Φ s x ∂(Measure.map (fun ω : Ω => fun k => ε k ω) μ) ∂(Measure.map (fun ω : Ω => fun k => Z k ω) μ) := by
    refine integral_prod (fun q : (Fin p → α) × (Fin p → ℝ) => Φ q.2 q.1) ?_
    refine Integrable.of_bound hΦ'_meas.aestronglyMeasurable C ?_
    filter_upwards with q
    simpa [Real.norm_eq_abs] using hC q.2 q.1
  calc ∫ ω, ((Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
          ∑ s : Fin p → Bool,
            Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (s k)) (fun k => Z k ω)) ∂μ
      = (Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
          ∑ s : Fin p → Bool,
            ∫ ω, Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (s k)) (fun k => Z k ω) ∂μ := hL
    _ = (Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
          ∑ s : Fin p → Bool,
            ∫ x, Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (s k)) x ∂(Measure.map (fun ω : Ω => fun k => Z k ω) μ) := by
          simp only [hE]
    _ = ∫ x, ((Fintype.card (Fin p → Bool) : ℝ)⁻¹ *
          ∑ t : Fin p → Bool,
            Φ (fun k => Statlib.StatFoundation.Vocabulary.rademacherSign (t k)) x) ∂(Measure.map (fun ω : Ω => fun k => Z k ω) μ) := hstepD.symm
    _ = ∫ x, ∫ s : Fin p → ℝ, Φ s x ∂(Measure.map (fun ω : Ω => fun k => ε k ω) μ) ∂(Measure.map (fun ω : Ω => fun k => Z k ω) μ) := by
          simp only [hinner]
    _ = ∫ q : (Fin p → α) × (Fin p → ℝ), Φ q.2 q.1 ∂((Measure.map (fun ω : Ω => fun k => Z k ω) μ).prod (Measure.map (fun ω : Ω => fun k => ε k ω) μ)) := hstepB.symm
    _ = ∫ ω, Φ (fun k => ε k ω) (fun k => Z k ω) ∂μ := hstepA.symm
  /- @proof-region region.target-node.session.d6ba91062416e335 end -/

end

end Statlib.Imported

