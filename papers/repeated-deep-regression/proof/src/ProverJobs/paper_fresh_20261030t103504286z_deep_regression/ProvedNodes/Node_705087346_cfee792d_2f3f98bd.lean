import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Lean
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Vocabulary
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Base
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ProvedNodes.Node_1194647586_08143ca6_5fc8e5eb
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ProvedNodes.Node_2933192278_9a0e3317_3c979d9d
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ProvedNodes.Node_4168644478_42c29445_54dc375b
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ExternalNodes.Node_31d1bfda1f2c4bccb0b1

namespace PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression


open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_705087346_cfee792d : ∃ c38 c39 : ℝ, 0 < c38 ∧ 0 < c39 ∧
      ∀ (d : ℕ) (hd : 0 < d) (ΩS : Type*) [MeasurableSpace ΩS] (mu : Measure ΩS)
        [IsProbabilityMeasure mu] (Ω : Set (Fin d → ℝ)) (hΩ_meas : MeasurableSet Ω)
        (hΩ_sub : Ω ⊆ Set.Icc (0 : Fin d → ℝ) 1) (PX : Measure Ω) [IsProbabilityMeasure PX]
        (hPX_ac : PX ≪ Measure.comap (fun x : Ω => (x : Fin d → ℝ))
          (volume : Measure (Fin d → ℝ))) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
        (X : Fin n × Fin m → ΩS → Ω) (Z : Fin n → ΩS → Ω → ℝ) (eps sig : Fin n × Fin m → ΩS → ℝ)
        (F : Set (Ω → ℝ)) (fcirc : Ω → ℝ) (fhat : ΩS → Ω → ℝ) (B1 B2 B3 rstar : ℝ)
        (phi : ℝ → ℝ) (f0 : Ω → ℝ),
        (∀ ij : Fin n × Fin m, Measurable (X ij)) →
        iIndepFun X mu →
        (∀ ij ij' : Fin n × Fin m, IdentDistrib (X ij) (X ij') mu mu) →
        (∀ ij : Fin n × Fin m, Measure.map (X ij) mu = PX) →
        (∀ i : Fin n, Measurable fun p : ΩS × Ω => Z i p.1 p.2) →
        iIndepFun Z mu →
        (∀ i i' : Fin n, IdentDistrib (Z i) (Z i') mu mu) →
        (∀ (i : Fin n) (j : Fin m), ∀ᵐ ω ∂mu, fcirc (X (i, j) ω) =
          mu[fun ω => Z i ω (X (i, j) ω) |
            MeasurableSpace.comap (X (i, j)) (inferInstance : MeasurableSpace Ω)] ω) →
        (Function.swap X ⟂ᵢ[mu] Function.swap Z) →
        (∀ ij : Fin n × Fin m, Measurable (eps ij)) →
        iIndepFun eps mu →
        (Function.swap eps ⟂ᵢ[mu] fun ω => (Function.swap X ω, Function.swap Z ω)) →
        (∀ ij : Fin n × Fin m, Integrable (eps ij) mu) →
        (∀ ij : Fin n × Fin m, ∫ ω, eps ij ω ∂mu = 0) →
        (∀ (i : Fin n) (j : Fin m),
          Integrable (fun ω => stochPart Z fcirc i ω (X (i, j) ω) * fcirc (X (i, j) ω)) mu) →
        (∀ (i : Fin n) (j : Fin m),
          ∫ ω, stochPart Z fcirc i ω (X (i, j) ω) * fcirc (X (i, j) ω) ∂mu = 0) →
        (∀ (i : Fin n) (ω : ΩS), Continuous fun z : Ω => Z i ω z - f0 z) →
        (∀ ij : Fin n × Fin m, Measurable (sig ij)) →
        iIndepFun sig mu →
        (∀ ij : Fin n × Fin m,
          mu {ω | sig ij ω = 1} = 1 / 2 ∧ mu {ω | sig ij ω = -1} = 1 / 2) →
        (Function.swap sig ⟂ᵢ[mu] fun ω =>
          (Function.swap X ω, Function.swap Z ω, Function.swap eps ω)) →
        Measurable fhat →
        (∀ᵐ ω ∂mu, fhat ω ∈ F ∧ ∀ f ∈ F,
          empRisk X (response Z eps X fcirc) (fhat ω) ω ≤
            empRisk X (response Z eps X fcirc) f ω) →
        Measurable fcirc →
        (∀ f ∈ F, Measurable f) →
        AEMeasurable (fun p : ΩS × Ω => fhat p.1 p.2) (mu.prod PX) →
        AEMeasurable (fun ω => l2Err PX fcirc (fhat ω)) mu →
        0 < B1 →
        1 ≤ B1 →
        (∀ x : Ω, |fcirc x| ≤ B1) →
        (∀ f ∈ F, ∀ x : Ω, |f x| ≤ B1) →
        0 < B2 →
        (∀ (i : Fin n) (j : Fin m),
          ∫⁻ ω, ENNReal.ofReal (Real.exp (|stochPart Z fcirc i ω (X (i, j) ω)| / B2)) ∂mu
            ≤ 1) →
        0 < B3 →
        (∀ (i : Fin n) (j : Fin m),
          ∫⁻ ω, ENNReal.ofReal (Real.exp (|eps (i, j) ω| / B3)) ∂mu ≤ 1) →
        0 < rstar →
        (∀ r ∈ Set.Ici rstar, 0 ≤ phi r / Real.sqrt r) →
        AntitoneOn (fun r => phi r / Real.sqrt r) (Set.Ici rstar) →
        phi rstar ≤ rstar →
        (∀ r ∈ Set.Ici rstar, radSup mu PX F fcirc sig X r ≤ ENNReal.ofReal (phi r)) →
        (∀ i : Fin n, ∀ᵐ x ∂PX, Integrable (fun ω => Z i ω x) mu) →
        (∀ i : Fin n, ∀ᵐ x ∂PX, f0 x = ∫ ω, Z i ω x ∂mu) →
        Measurable f0 →
        (∀ x : Ω, |f0 x| ≤ B1) →
        (∀ᵐ x ∂PX, f0 x = fcirc x) →
        StarConvex ℝ f0 F →
        (∃ F0 : Set (Ω → ℝ), F0.Countable ∧ F0 ⊆ F ∧
          ∀ f ∈ F, ∃ u : ℕ → (Ω → ℝ), (∀ k : ℕ, u k ∈ F0) ∧
            ∀ x : Ω, Filter.Tendsto (fun k => u k x) Filter.atTop (𝓝 (f x))) →
        ∀ t : ℝ, 0 < t →
          rstar ≤ 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) →
          mu {ω : ΩS |
              |(l2Err PX fcirc (fhat ω)).toReal -
                  (1 / ((n : ℝ) * (m : ℝ))) *
                    ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2| >
                (1 / 2) * (l2Err PX fcirc (fhat ω)).toReal +
                  c38 * B1 ^ 2 * rstar +
                  c39 * B1 ^ 2 * (t + 1) / ((n : ℝ) * (m : ℝ))} ≤
            ENNReal.ofReal (Real.exp (-t)) := by
  /- @proof-region region.target-node.session.873e41438271e67e begin -/
  obtain ⟨c38, c39, hc38, hc39, htail⟩ :=
    PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.paper_8d614b8e54384bdaa316eb81207fecf6
  refine ⟨c38, c39, hc38, hc39, ?_⟩
  intro d hd ΩS hΩSinst mu hmuinst Ω hΩ_meas hΩ_sub PX hPXinst hPX_ac n m hn hm
    X Z eps sig F fcirc fhat B1 B2 B3 rstar phi f0
  intro hX_meas hX_indep hX_idd hX_law hZ_meas hZ_indep hZ_idd hcond hZX_indep
    heps_meas heps_indep heps_indep2 heps_int heps_mean
    hstoch_int hstoch_mean hU_cont hsig_meas hsig_indep hsig_val hsig_indep2
    hfhat_meas hERM hfcirc_meas hF_meas hfhat_aemeas hl2_aemeas
    hB1_pos hB1_ge hfcirc_bound hF_bound hB2_pos hU_tail hB3_pos heps_tail
    hrstar_pos hphi_nonneg hphi_antitone hphi_fix hphi_dom
    hZ_int hf0_mean hf0_meas hf0_bound hf0_eq_fcirc hF_starconvex hF_sep
  intro t ht hreg
  have hsig_pm : ∀ p : Fin n × Fin m, ∀ᵐ ω ∂mu, sig p ω = 1 ∨ sig p ω = -1 := by
    intro p
    have hA : MeasurableSet {ω : ΩS | sig p ω = 1} := hsig_meas p (measurableSet_singleton 1)
    have hB : MeasurableSet {ω : ΩS | sig p ω = -1} := hsig_meas p (measurableSet_singleton (-1))
    have hdisj : Disjoint {ω : ΩS | sig p ω = 1} {ω : ΩS | sig p ω = -1} := by
      rw [Set.disjoint_left]
      intro ω h1 h2
      simp only [Set.mem_setOf_eq] at h1 h2
      linarith
    have hunion : mu ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1}) = 1 := by
      rw [MeasureTheory.measure_union hdisj hB, (hsig_val p).1, (hsig_val p).2]
      have h2 : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      rw [two_mul] at h2
      simpa [one_div] using h2
    have hcompl : mu ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})ᶜ = 0 := by
      rw [MeasureTheory.measure_compl (hA.union hB)
          (by rw [hunion]; exact ENNReal.one_ne_top), hunion, MeasureTheory.measure_univ]
      simp
    have hmem : {ω : ΩS | sig p ω = 1 ∨ sig p ω = -1} ∈ ae mu := by
      rw [MeasureTheory.mem_ae_iff]
      simpa only [Set.compl_setOf, Set.compl_union, Set.mem_inter_iff, not_or] using hcompl
    exact hmem
  have hsig_law : ∀ p : Fin n × Fin m,
      Measure.map (sig p) mu =
        PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.rademacherLaw := by
    intro p
    classical
    have hA : MeasurableSet {ω : ΩS | sig p ω = 1} := hsig_meas p (measurableSet_singleton 1)
    have hB : MeasurableSet {ω : ΩS | sig p ω = -1} := hsig_meas p (measurableSet_singleton (-1))
    have hdisj : Disjoint {ω : ΩS | sig p ω = 1} {ω : ΩS | sig p ω = -1} := by
      rw [Set.disjoint_left]
      intro ω h1 h2
      simp only [Set.mem_setOf_eq] at h1 h2
      linarith
    have hunion : mu ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1}) = 1 := by
      rw [MeasureTheory.measure_union hdisj hB, (hsig_val p).1, (hsig_val p).2]
      have h2 : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      rw [two_mul] at h2
      simpa [one_div] using h2
    have hcompl : mu ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})ᶜ = 0 := by
      rw [MeasureTheory.measure_compl (hA.union hB)
          (by rw [hunion]; exact ENNReal.one_ne_top), hunion, MeasureTheory.measure_univ]
      simp
    ext s hs
    rw [MeasureTheory.Measure.map_apply (hsig_meas p) hs,
      PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.rademacherLaw,
      MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.add_apply,
      MeasureTheory.Measure.dirac_apply, MeasureTheory.Measure.dirac_apply, smul_eq_mul]
    have htu : mu (sig p ⁻¹' s)
        = mu (sig p ⁻¹' s ∩ ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})) := by
      refine le_antisymm ?_ (MeasureTheory.measure_mono Set.inter_subset_left)
      have hsub : sig p ⁻¹' s ⊆
          (sig p ⁻¹' s ∩ ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})) ∪
            ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})ᶜ := by
        intro ω hω
        by_cases h : sig p ω = 1 ∨ sig p ω = -1
        · exact Or.inl ⟨hω, h⟩
        · exact Or.inr (by simpa only [Set.mem_compl_iff, Set.mem_setOf_eq] using h)
      calc mu (sig p ⁻¹' s)
          ≤ mu ((sig p ⁻¹' s ∩ ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})) ∪
              ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})ᶜ) :=
            MeasureTheory.measure_mono hsub
        _ ≤ mu (sig p ⁻¹' s ∩ ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})) +
              mu ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})ᶜ :=
            MeasureTheory.measure_union_le _ _
        _ = mu (sig p ⁻¹' s ∩ ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})) := by
            rw [hcompl, add_zero]
    have hsplit : sig p ⁻¹' s ∩ ({ω : ΩS | sig p ω = 1} ∪ {ω : ΩS | sig p ω = -1})
        = ({ω : ΩS | sig p ω = 1} ∩ sig p ⁻¹' s) ∪ ({ω : ΩS | sig p ω = -1} ∩ sig p ⁻¹' s) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage]
      tauto
    have hdisj2 : Disjoint ({ω : ΩS | sig p ω = 1} ∩ sig p ⁻¹' s)
        ({ω : ΩS | sig p ω = -1} ∩ sig p ⁻¹' s) := by
      rw [Set.disjoint_left]
      intro ω h1 h2
      have h1' : sig p ω = 1 := h1.1
      have h2' : sig p ω = -1 := h2.1
      linarith
    have hAt : mu ({ω : ΩS | sig p ω = 1} ∩ sig p ⁻¹' s)
        = if (1 : ℝ) ∈ s then (2 : ENNReal)⁻¹ else 0 := by
      by_cases h1 : (1 : ℝ) ∈ s
      · rw [if_pos h1]
        have heq : {ω : ΩS | sig p ω = 1} ∩ sig p ⁻¹' s = {ω : ΩS | sig p ω = 1} := by
          ext ω
          constructor
          · intro h; exact h.1
          · intro h
            have hh : sig p ω = 1 := h
            refine ⟨h, ?_⟩
            show sig p ω ∈ s
            rw [hh]
            exact h1
        rw [heq]
        simpa [one_div] using (hsig_val p).1
      · rw [if_neg h1]
        have heq : {ω : ΩS | sig p ω = 1} ∩ sig p ⁻¹' s = ∅ := by
          ext ω
          constructor
          · intro h
            have hh : sig p ω = 1 := h.1
            have h2' : sig p ω ∈ s := h.2
            rw [hh] at h2'
            exact h1 h2'
          · intro h
            exact absurd h (by simp)
        rw [heq, MeasureTheory.measure_empty]
    have hBt : mu ({ω : ΩS | sig p ω = -1} ∩ sig p ⁻¹' s)
        = if (-1 : ℝ) ∈ s then (2 : ENNReal)⁻¹ else 0 := by
      by_cases h2 : (-1 : ℝ) ∈ s
      · rw [if_pos h2]
        have heq : {ω : ΩS | sig p ω = -1} ∩ sig p ⁻¹' s = {ω : ΩS | sig p ω = -1} := by
          ext ω
          constructor
          · intro h; exact h.1
          · intro h
            have hh : sig p ω = -1 := h
            refine ⟨h, ?_⟩
            show sig p ω ∈ s
            rw [hh]
            exact h2
        rw [heq]
        simpa [one_div] using (hsig_val p).2
      · rw [if_neg h2]
        have heq : {ω : ΩS | sig p ω = -1} ∩ sig p ⁻¹' s = ∅ := by
          ext ω
          constructor
          · intro h
            have hh : sig p ω = -1 := h.1
            have h2' : sig p ω ∈ s := h.2
            rw [hh] at h2'
            exact h2 h2'
          · intro h
            exact absurd h (by simp)
        rw [heq, MeasureTheory.measure_empty]
    rw [htu, hsplit, MeasureTheory.measure_union hdisj2 (hB.inter (hs.preimage (hsig_meas p))),
      hAt, hBt]
    by_cases h1 : (1 : ℝ) ∈ s
    · by_cases h2 : (-1 : ℝ) ∈ s
      · rw [if_pos h1, if_pos h2, Set.indicator_of_mem h2, Set.indicator_of_mem h1]
        rw [mul_add]
        simp
      · rw [if_pos h1, if_neg h2, Set.indicator_of_notMem h2, Set.indicator_of_mem h1]
        rw [mul_add]
        simp
    · by_cases h2 : (-1 : ℝ) ∈ s
      · rw [if_neg h1, if_pos h2, Set.indicator_of_mem h2, Set.indicator_of_notMem h1]
        rw [mul_add]
        simp
      · rw [if_neg h1, if_neg h2, Set.indicator_of_notMem h2, Set.indicator_of_notMem h1]
        rw [mul_add]
        simp
  have hpair : ∀ (g : ΩS → Ω), Measurable g → Measurable (fun ω : ΩS => (ω, g ω)) := by
    intro g hg
    exact measurable_id.prod hg
  have pZ_meas : ∀ i : Fin n, Measurable (Z i) := by
    intro i
    rw [measurable_pi_iff]
    intro x
    exact (hZ_meas i).comp (hpair (fun _ => x) measurable_const)
  have pU_cont : ∀ i : Fin n, ∀ᵐ ω ∂mu, ∀ᵐ x ∂PX,
      ContinuousAt
        (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.deviations
          Z f0 ω i) x := by
    intro i
    filter_upwards with ω
    filter_upwards with x
    exact (hU_cont i ω).continuousAt
  have pF_int : ∀ f ∈ F, Integrable (fun x => (f x - f0 x) ^ 2) PX := by
    intro f hf
    have hinner : Measurable (fun x : Ω => f x - f0 x) := (hF_meas f hf).sub hf0_meas
    have hsq : Measurable (fun x : Ω => (f x - f0 x) ^ 2) := by
      simpa [pow_two] using hinner.mul hinner
    refine MeasureTheory.Integrable.of_bound hsq.aestronglyMeasurable ((2 * B1) ^ 2)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : |f x - f0 x| ≤ 2 * B1 := by
      have h2 : |f x - f0 x| ≤ |f x| + |f0 x| := by
        simpa using abs_add_le (f x) (-f0 x)
      have h3 := hF_bound f hf x
      have h4 := hf0_bound x
      linarith
    have h5 : (f x - f0 x) ^ 2 ≤ (2 * B1) ^ 2 := by
      have hb : 0 ≤ 2 * B1 := by linarith
      have hle := abs_le.mp h1
      nlinarith [hle.1, hle.2, hb]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h5
  have pfhat_int : ∀ᵐ ω ∂mu, Integrable (fun x => (fhat ω x - f0 x) ^ 2) PX := by
    filter_upwards [hERM] with ω hω
    exact pF_int (fhat ω) hω.1
  have hnR : (0 : ℝ) < (↑n : ℝ) := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < (↑m : ℝ) := Nat.cast_pos.mpr hm
  have hζ : ∀ p : Fin n × Fin m, AEMeasurable (fun ω => Z p.1 ω (X p ω)) mu := by
    intro p
    exact ((hZ_meas p.1).comp (hpair (X p) (hX_meas p))).aemeasurable
  have pdev_int : ∀ p : Fin n × Fin m,
      Integrable (fun ω =>
        Real.exp (|PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.deviations
          Z f0 ω p.1 (X p ω) / B2|)) mu := by
    intro p
    exact (statopia_math_node_4168644478_42c29445 ΩS (Ω : Type) mu PX (X p) (hX_meas p) (hX_law p)
      (fun ω x => Z p.1 ω x) f0 fcirc (hζ p) hf0_meas hf0_eq_fcirc B2 hB2_pos
      (hU_tail p.1 p.2)).1
  have pdev_tail : ∀ p : Fin n × Fin m,
      ∫ ω, Real.exp (|PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.deviations
          Z f0 ω p.1 (X p ω) / B2|) ∂mu ≤ 1 := by
    intro p
    exact (statopia_math_node_4168644478_42c29445 ΩS (Ω : Type) mu PX (X p) (hX_meas p) (hX_law p)
      (fun ω x => Z p.1 ω x) f0 fcirc (hζ p) hf0_meas hf0_eq_fcirc B2 hB2_pos
      (hU_tail p.1 p.2)).2
  have hpeps_lint : ∀ p : Fin n × Fin m,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (|eps p ω / B3|)) ∂mu ≤ 1 := by
    intro p
    have hfun : (fun ω => ENNReal.ofReal (Real.exp (|eps p ω / B3|)))
        = fun ω => ENNReal.ofReal (Real.exp (|eps p ω| / B3)) := by
      funext ω
      rw [abs_div, abs_of_pos hB3_pos]
    rw [hfun]
    exact heps_tail p.1 p.2
  have peps_int : ∀ p : Fin n × Fin m,
      Integrable (fun ω => Real.exp (|eps p ω / B3|)) mu := by
    intro p
    have hmeas : AEStronglyMeasurable (fun ω => Real.exp (|eps p ω / B3|)) mu := by
      have hm : Measurable (fun ω => Real.exp (|eps p ω / B3|)) :=
        Real.continuous_exp.measurable.comp (((heps_meas p).div_const B3).abs)
      exact hm.aestronglyMeasurable
    have hpos : 0 ≤ᵐ[mu] (fun ω => Real.exp (|eps p ω / B3|)) :=
      Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hpos).mp
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hpeps_lint p))
  have peps_tail' : ∀ p : Fin n × Fin m,
      ∫ ω, Real.exp (|eps p ω / B3|) ∂mu ≤ 1 := by
    intro p
    have hpos : 0 ≤ᵐ[mu] (fun ω => Real.exp (|eps p ω / B3|)) :=
      Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
    rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
      hpos (peps_int p)]
    exact le_trans (ENNReal.toReal_mono ENNReal.one_ne_top (hpeps_lint p))
      (le_of_eq ENNReal.toReal_one)
  have pRad_int : ∀ (r : ℝ) (Fs : Finset (Ω → ℝ)),
      ↑Fs ⊆ PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.localizedClass
        F PX f0 r →
      Integrable (fun ω =>
        PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.rademacherFiniteSup
          (fun i j => X (i, j)) f0 (fun i j => sig (i, j)) ω Fs) mu := by
    intro r Fs hFs
    classical
    simp only [PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.rademacherFiniteSup,
      PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.localizedClass,
      Set.mem_setOf_eq] at hFs ⊢
    let R : (Ω → ℝ) → ΩS → ℝ := fun f ω => ((n : ℝ) * (m : ℝ))⁻¹ *
      ∑ i : Fin n, ∑ j : Fin m, sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))
    show Integrable (fun ω => sSup ((fun f => |R f ω|) '' ↑Fs)) mu
    have hFmem : ∀ f ∈ Fs, f ∈ F := fun f hf => (hFs (by simpa using hf)).1
    have hterm : ∀ f ∈ F, Measurable (fun ω => ∑ i : Fin n, ∑ j : Fin m,
        sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))) := by
      intro f hf
      have hpair' : ∀ p : Fin n × Fin m, Measurable
          (fun ω => sig p ω * (f (X p ω) - f0 (X p ω))) := by
        intro p
        exact (hsig_meas p).mul (((hF_meas f hf).comp (hX_meas p)).sub (hf0_meas.comp (hX_meas p)))
      have hall : ∀ s : Finset (Fin n × Fin m),
          Measurable (fun ω => s.sum (fun p => sig p ω * (f (X p ω) - f0 (X p ω)))) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using measurable_const (a := (0 : ℝ))
        | insert a s ha ih =>
            have hstep : (fun ω => (insert a s).sum (fun p => sig p ω * (f (X p ω) - f0 (X p ω))))
                = fun ω => sig a ω * (f (X a ω) - f0 (X a ω)) +
                    s.sum (fun p => sig p ω * (f (X p ω) - f0 (X p ω))) := by
              funext ω
              exact Finset.sum_insert ha
            rw [hstep]
            exact (hpair' a).add ih
      have hcurried : (fun ω => Finset.univ.sum (fun p : Fin n × Fin m =>
            sig p ω * (f (X p ω) - f0 (X p ω))))
          = fun ω => ∑ i : Fin n, ∑ j : Fin m,
              sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω)) := by
        funext ω
        rw [← Finset.univ_product_univ, Finset.sum_product]
      rw [← hcurried]
      exact hall Finset.univ
    have hval : ∀ f ∈ Fs, Measurable (fun ω => |R f ω|) := by
      intro f hf
      have h1 : Measurable (fun ω => R f ω) := by
        show Measurable (fun ω : ΩS => ((n : ℝ) * (m : ℝ))⁻¹ *
          ∑ i : Fin n, ∑ j : Fin m, sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω)))
        exact measurable_const.mul (hterm f (hFmem f hf))
      exact h1.abs
    have hsig_all : ∀ᵐ ω ∂mu, ∀ p : Fin n × Fin m, sig p ω = 1 ∨ sig p ω = -1 := by
      have hset : {ω : ΩS | ¬ ∀ p : Fin n × Fin m, (sig p ω = 1 ∨ sig p ω = -1)}
          = ⋃ p : Fin n × Fin m, {ω : ΩS | ¬ (sig p ω = 1 ∨ sig p ω = -1)} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall]
      have hzero : mu {ω : ΩS | ¬ ∀ p : Fin n × Fin m, (sig p ω = 1 ∨ sig p ω = -1)} = 0 := by
        rw [hset]
        exact MeasureTheory.measure_iUnion_null_iff.mpr (fun p => by
          have hp := MeasureTheory.mem_ae_iff.mp (hsig_pm p)
          simpa only [Set.compl_setOf] using hp)
      have hmem : {ω : ΩS | ∀ p : Fin n × Fin m, (sig p ω = 1 ∨ sig p ω = -1)} ∈ ae mu := by
        rw [MeasureTheory.mem_ae_iff]
        simpa only [Set.compl_setOf] using hzero
      exact hmem
    have hcoe_empty : ¬ Fs.Nonempty → ((↑Fs : Set (Ω → ℝ))) = ∅ := by
      intro hne
      ext f
      simp only [Set.mem_empty_iff_false, iff_false, Finset.mem_coe]
      intro hf
      exact hne ⟨f, hf⟩
    have himg : ∀ ω : ΩS, ((fun f => |R f ω|) '' ↑Fs) = Set.range (fun f : ↥Fs => |R f.1 ω|) := by
      intro ω
      ext y
      constructor
      · rintro ⟨f, hf, rfl⟩
        exact ⟨⟨f, hf⟩, rfl⟩
      · rintro ⟨f, rfl⟩
        exact ⟨f.1, f.2, rfl⟩
    have hbdd : ∀ ω : ΩS, BddAbove ((fun f => |R f ω|) '' ↑Fs) := by
      intro ω
      let g : ↥Fs → ℝ := fun f => abs (R f.1 ω)
      have hg : ((fun f => |R f ω|) '' ↑Fs) = Set.range g := himg ω
      rw [hg]
      exact Finite.bddAbove_range g
    have hcmp : ∀ (hne : Fs.Nonempty),
        (fun ω : ΩS => sSup ((fun f => |R f ω|) '' ↑Fs)) = Fs.sup' hne (fun f ω => |R f ω|) := by
      intro hne
      refine le_antisymm ?_ ?_
      · intro ω
        refine Real.sSup_le ?_ ?_
        · rintro y ⟨f, hf, rfl⟩
          exact (Finset.le_sup' (fun f ω' => |R f ω'|) hf) ω
        · obtain ⟨f₀, hf₀⟩ := hne
          exact le_trans (abs_nonneg (R f₀ ω)) ((Finset.le_sup' (fun f ω' => |R f ω'|) hf₀) ω)
      · refine (Finset.sup'_le_iff hne (fun f ω' => |R f ω'|)).mpr ?_
        intro b hb ω
        have hmem : |R b ω| ∈ ((fun f => |R f ω|) '' ↑Fs) := ⟨b, hb, rfl⟩
        have hub : ∀ y ∈ ((fun f => |R f ω|) '' ↑Fs),
            y ≤ sSup ((fun f => |R f ω|) '' ↑Fs) :=
          (Real.isLUB_sSup ⟨_, hmem⟩ (hbdd ω)).1
        exact hub _ hmem
    have hAESM : AEStronglyMeasurable (fun ω => sSup ((fun f => |R f ω|) '' ↑Fs)) mu := by
      by_cases hne : Fs.Nonempty
      · rw [hcmp hne]
        exact (Finset.measurable_sup' hne (fun f hf => hval f hf)).aestronglyMeasurable
      · have hempty := hcoe_empty hne
        have hz : (fun ω : ΩS => sSup ((fun f => |R f ω|) '' ↑Fs)) = fun _ => (0 : ℝ) := by
          funext ω
          rw [hempty, Set.image_empty, Real.sSup_empty]
        rw [hz]
        exact measurable_const.aestronglyMeasurable
    have hbound : ∀ᵐ ω ∂mu, ‖sSup ((fun f => |R f ω|) '' ↑Fs)‖ ≤ 2 * B1 := by
      by_cases hne : Fs.Nonempty
      · filter_upwards [hsig_all] with ω hsig
        have hper : ∀ f ∈ Fs, |R f ω| ≤ 2 * B1 := by
          intro f hf
          show |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
              sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))| ≤ 2 * B1
          have hb1 : ∀ p : Fin n × Fin m, |f (X p ω) - f0 (X p ω)| ≤ 2 * B1 := by
            intro p
            have h1 : |f (X p ω) - f0 (X p ω)| ≤ |f (X p ω)| + |f0 (X p ω)| := by
              simpa using abs_add_le (f (X p ω)) (-f0 (X p ω))
            have h2 := hF_bound f (hFmem f hf) (X p ω)
            have h3 := hf0_bound (X p ω)
            linarith
          have hsig1 : ∀ p : Fin n × Fin m, |sig p ω| = 1 := by
            intro p
            rcases hsig p with h | h
            · rw [h]; norm_num
            · rw [h]; norm_num
          have hterm : ∀ p : Fin n × Fin m, |sig p ω * (f (X p ω) - f0 (X p ω))| ≤ 2 * B1 := by
            intro p
            rw [abs_mul, hsig1 p, one_mul]
            exact hb1 p
          have hsum_const_fin : ∀ (k : ℕ) (c : ℝ), ∑ _x : Fin k, c = (k : ℝ) * c := by
            intro k c
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hinner : ∀ i : Fin n,
              |∑ j : Fin m, sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))|
                ≤ (m : ℝ) * (2 * B1) := by
            intro i
            refine le_trans (Finset.abs_sum_le_sum_abs (fun j : Fin m =>
              sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))) Finset.univ) ?_
            refine le_trans (Finset.sum_le_sum (fun j _ => hterm (i, j))) ?_
            exact le_of_eq (hsum_const_fin m (2 * B1))
          have hsum : |∑ i : Fin n, ∑ j : Fin m,
              sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))|
              ≤ (n : ℝ) * ((m : ℝ) * (2 * B1)) := by
            refine le_trans (Finset.abs_sum_le_sum_abs (fun i : Fin n =>
              ∑ j : Fin m, sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))) Finset.univ) ?_
            refine le_trans (Finset.sum_le_sum (fun i _ => hinner i)) ?_
            exact le_of_eq (hsum_const_fin n ((m : ℝ) * (2 * B1)))
          have hpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := mul_pos hnR hmR
          rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
          calc ((n : ℝ) * (m : ℝ))⁻¹ * |∑ i : Fin n, ∑ j : Fin m,
                sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))|
              ≤ ((n : ℝ) * (m : ℝ))⁻¹ * ((n : ℝ) * ((m : ℝ) * (2 * B1))) :=
                mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hpos))
            _ = 2 * B1 := by
                have hne0 : ((n : ℝ) * (m : ℝ)) ≠ 0 := ne_of_gt hpos
                field_simp
        have hmemle : ∀ y ∈ ((fun f => |R f ω|) '' ↑Fs), y ≤ 2 * B1 := by
          rintro y ⟨f, hf, rfl⟩
          exact hper f hf
        have hbdd : BddAbove ((fun f => |R f ω|) '' ↑Fs) := ⟨2 * B1, hmemle⟩
        have hnn : 0 ≤ sSup ((fun f => |R f ω|) '' ↑Fs) := by
          obtain ⟨f₀, hf₀⟩ := hne
          have hmem : |R f₀ ω| ∈ ((fun f => |R f ω|) '' ↑Fs) := ⟨f₀, hf₀, rfl⟩
          have hub : ∀ y ∈ ((fun f => |R f ω|) '' ↑Fs),
              y ≤ sSup ((fun f => |R f ω|) '' ↑Fs) :=
            (Real.isLUB_sSup ⟨_, hmem⟩ hbdd).1
          exact le_trans (abs_nonneg _) (hub _ hmem)
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        exact Real.sSup_le hmemle (by linarith [hB1_pos])
      · have hempty := hcoe_empty hne
        filter_upwards with ω
        rw [hempty, Set.image_empty, Real.sSup_empty, Real.norm_eq_abs, abs_zero]
        linarith [hB1_pos]
    exact MeasureTheory.Integrable.of_bound hAESM (2 * B1) hbound
  have pERM : ∀ᵐ ω ∂mu, fhat ω ∈ F ∧ ∀ f ∈ F,
      PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.lsqCriterion
          (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.responses
            Z (fun i j => X (i, j)) (fun i j => eps (i, j)))
          (fun i j => X (i, j)) ω (fhat ω) ≤
        PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.lsqCriterion
          (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.responses
            Z (fun i j => X (i, j)) (fun i j => eps (i, j)))
          (fun i j => X (i, j)) ω f := by
    filter_upwards [hERM] with ω hω
    refine ⟨hω.1, fun f hf => ?_⟩
    have hconv : ∀ g : Ω → ℝ,
        PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.lsqCriterion
            (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.responses
              Z (fun i j => X (i, j)) (fun i j => eps (i, j)))
            (fun i j => X (i, j)) ω g
          = empRisk X (response Z eps X fcirc) g ω := by
      intro g
      simp only [PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.lsqCriterion,
        PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.responses,
        empRisk, response, stochPart]
      rw [one_div,
        show (∑ x : Fin n × Fin m,
            (fcirc (X x ω) + (Z x.1 ω (X x ω) - fcirc (X x ω)) + eps x ω - g (X x ω)) ^ 2)
          = ∑ i : Fin n, ∑ j : Fin m,
            (fcirc (X (i, j) ω) + (Z i ω (X (i, j) ω) - fcirc (X (i, j) ω)) + eps (i, j) ω -
              g (X (i, j) ω)) ^ 2 from by
            rw [← Finset.univ_product_univ, Finset.sum_product]]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hconv (fhat ω), hconv f]
    exact hω.2 f hf
  have pfix :
      PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.IsRademacherFixedPoint
        F PX f0 (fun i j => X (i, j)) (fun i j => sig (i, j)) mu phi rstar := by
    refine ⟨hrstar_pos, ⟨hphi_nonneg, hphi_antitone⟩, hphi_fix, ?_⟩
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le hrstar_pos hr
    have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
    have hphinn : 0 ≤ phi r := by
      have hdiv := hphi_nonneg r hr
      have hmul : 0 ≤ (phi r / Real.sqrt r) * Real.sqrt r := mul_nonneg hdiv (le_of_lt hsq)
      have heq : (phi r / Real.sqrt r) * Real.sqrt r = phi r := by
        have hne : Real.sqrt r ≠ 0 := ne_of_gt hsq
        field_simp
      rwa [heq] at hmul
    refine Real.sSup_le ?_ hphinn
    intro v hv
    obtain ⟨Fs, hFs, rfl⟩ := hv
    refine le_trans (b := (radSup mu PX F fcirc sig X r).toReal) ?_ ?_
    · have hRad_ne_top : radSup mu PX F fcirc sig X r ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hphi_dom r hr)
      have hnonneg : 0 ≤ᵐ[mu] (fun ω =>
          PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.rademacherFiniteSup
            (fun i j => X (i, j)) f0 (fun i j => sig (i, j)) ω Fs) := by
        classical
        let R : (Ω → ℝ) → ΩS → ℝ := fun f ω => ((n : ℝ) * (m : ℝ))⁻¹ *
          ∑ i : Fin n, ∑ j : Fin m, sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))
        have h0 : ∀ ω : ΩS, 0 ≤ sSup ((fun f => |R f ω|) '' ↑Fs) := by
          intro ω
          by_cases hne : Fs.Nonempty
          · obtain ⟨f₀, hf₀⟩ := hne
            have hmem : |R f₀ ω| ∈ ((fun f => |R f ω|) '' ↑Fs) := ⟨f₀, hf₀, rfl⟩
            have himg : ((fun f => |R f ω|) '' ↑Fs) = Set.range (fun f : ↥Fs => |R f.1 ω|) := by
              ext y
              constructor
              · rintro ⟨f, hf, rfl⟩
                exact ⟨⟨f, hf⟩, rfl⟩
              · rintro ⟨f, rfl⟩
                exact ⟨f.1, f.2, rfl⟩
            have hbdd : BddAbove ((fun f => |R f ω|) '' ↑Fs) := by
              let g : ↥Fs → ℝ := fun f => abs (R f.1 ω)
              have hg : ((fun f => |R f ω|) '' ↑Fs) = Set.range g := himg
              rw [hg]
              exact Finite.bddAbove_range g
            have hub : ∀ y ∈ ((fun f => |R f ω|) '' ↑Fs),
                y ≤ sSup ((fun f => |R f ω|) '' ↑Fs) :=
              (Real.isLUB_sSup ⟨_, hmem⟩ hbdd).1
            exact le_trans (abs_nonneg (R f₀ ω)) (hub _ hmem)
          · have hempty : ((↑Fs : Set (Ω → ℝ))) = ∅ := by
              ext f
              simp only [Set.mem_empty_iff_false, iff_false, Finset.mem_coe]
              intro hf
              exact hne ⟨f, hf⟩
            rw [hempty, Set.image_empty, Real.sSup_empty]
        show 0 ≤ᵐ[mu] (fun ω : ΩS => sSup ((fun f => |R f ω|) '' ↑Fs))
        exact Filter.Eventually.of_forall h0
      rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
        hnonneg (pRad_int r Fs hFs)]
      refine ENNReal.toReal_mono hRad_ne_top ?_
      classical
      have hFs2 := hFs
      simp only [PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.localizedClass,
        Set.mem_setOf_eq] at hFs2
      have hloc : ∀ f ∈ Fs, f ∈ localized PX F fcirc r := by
        intro f hf
        have hmem := hFs2 (by simpa using hf)
        have hFmem2 : f ∈ F := hmem.1
        have hpred2 : (∫ x, (f x - f0 x) ^ 2 ∂PX) ≤ r := hmem.2
        have hcongr2 : (fun x : Ω => (f x - f0 x) ^ 2) =ᵐ[PX]
            (fun x : Ω => (f x - fcirc x) ^ 2) := by
          filter_upwards [hf0_eq_fcirc] with x hx
          rw [hx]
        have hint2 : Integrable (fun x : Ω => (f x - fcirc x) ^ 2) PX :=
          (pF_int f hFmem2).congr hcongr2
        have hof : ENNReal.ofReal (∫ x, (f x - fcirc x) ^ 2 ∂PX) = l2Err PX fcirc f :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint2
            (Filter.Eventually.of_forall fun x => sq_nonneg (f x - fcirc x))
        have hle2 : (∫ x, (f x - fcirc x) ^ 2 ∂PX) ≤ r := by
          rw [← MeasureTheory.integral_congr_ae hcongr2]
          exact hpred2
        refine ⟨hFmem2, ?_⟩
        rw [← hof]
        exact ENNReal.ofReal_le_ofReal hle2
      let s : Finset {f : Ω → ℝ // f ∈ localized PX F fcirc r} :=
        Fs.attach.image (fun x => (⟨x.1, hloc x.1 x.2⟩ : {f : Ω → ℝ // f ∈ localized PX F fcirc r}))
      have hle_iSup : ∫⁻ ω, ENNReal.ofReal
            (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.rademacherFiniteSup
              (fun i j => X (i, j)) f0 (fun i j => sig (i, j)) ω Fs) ∂mu ≤
          ∫⁻ ω, (⨆ g ∈ (s : Set {f : Ω → ℝ // f ∈ localized PX F fcirc r}),
            radProc sig X fcirc g.1 ω) ∂mu := by
        have hae : ∀ᵐ ω ∂mu, ∀ p : Fin n × Fin m, f0 (X p ω) = fcirc (X p ω) := by
          have hN : ∀ p : Fin n × Fin m, mu {ω : ΩS | f0 (X p ω) ≠ fcirc (X p ω)} = 0 := by
            intro p
            have hms : MeasurableSet {x : Ω | f0 x ≠ fcirc x} := by
              have h0 : MeasurableSet ({0} : Set ℝ)ᶜ := (measurableSet_singleton 0).compl
              have hp : MeasurableSet ((fun x : Ω => f0 x - fcirc x) ⁻¹' ({0} : Set ℝ)ᶜ) :=
                h0.preimage (hf0_meas.sub hfcirc_meas)
              have hEqSet : ((fun x : Ω => f0 x - fcirc x) ⁻¹' ({0} : Set ℝ)ᶜ)
                  = {x : Ω | f0 x ≠ fcirc x} := by
                ext x
                simp [sub_ne_zero]
              rw [hEqSet] at hp
              exact hp
            have hpre : {ω : ΩS | f0 (X p ω) ≠ fcirc (X p ω)} = X p ⁻¹' {x : Ω | f0 x ≠ fcirc x} := rfl
            rw [hpre, ← MeasureTheory.Measure.map_apply (hX_meas p) hms, hX_law p]
            have hzero := MeasureTheory.mem_ae_iff.mp hf0_eq_fcirc
            simpa only [Set.compl_setOf] using hzero
          have hN' : mu {ω : ΩS | ¬ ∀ p : Fin n × Fin m, f0 (X p ω) = fcirc (X p ω)} = 0 := by
            have hset : {ω : ΩS | ¬ ∀ p : Fin n × Fin m, f0 (X p ω) = fcirc (X p ω)}
                = ⋃ p : Fin n × Fin m, {ω : ΩS | f0 (X p ω) ≠ fcirc (X p ω)} := by
              ext ω
              simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall, ne_eq]
            rw [hset]
            exact MeasureTheory.measure_iUnion_null_iff.mpr hN
          have hmem : {ω : ΩS | ∀ p : Fin n × Fin m, f0 (X p ω) = fcirc (X p ω)} ∈ ae mu := by
            rw [MeasureTheory.mem_ae_iff]
            simpa only [Set.compl_setOf] using hN'
          exact hmem
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [hae] with ω hgood
        let R : (Ω → ℝ) → ΩS → ℝ := fun f ω => ((n : ℝ) * (m : ℝ))⁻¹ *
          ∑ i : Fin n, ∑ j : Fin m, sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))
        show ENNReal.ofReal (sSup ((fun f => |R f ω|) '' ↑Fs)) ≤
          ⨆ g ∈ (s : Set {f : Ω → ℝ // f ∈ localized PX F fcirc r}), radProc sig X fcirc g.1 ω
        have hfin : (⨆ g ∈ (s : Set {f : Ω → ℝ // f ∈ localized PX F fcirc r}),
            radProc sig X fcirc g.1 ω) ≠ ⊤ := by
          have hbfin : (⨆ g ∈ (s : Set {f : Ω → ℝ // f ∈ localized PX F fcirc r}),
              radProc sig X fcirc g.1 ω)
              ≤ ENNReal.ofReal ((1 / ((n : ℝ) * (m : ℝ))) *
                ∑ p : Fin n × Fin m, |sig p ω| * (2 * B1)) := by
            refine iSup_le (fun g => iSup_le (fun hg => ?_))
            have hgF : g.1 ∈ F := by
              have hgl := g.2
              simp only [localized, Set.mem_setOf_eq] at hgl
              exact hgl.1
            show ENNReal.ofReal |(1 / ((n : ℝ) * (m : ℝ))) * ∑ p : Fin n × Fin m,
                sig p ω * (g.1 (X p ω) - fcirc (X p ω))|
              ≤ ENNReal.ofReal ((1 / ((n : ℝ) * (m : ℝ))) *
                ∑ p : Fin n × Fin m, |sig p ω| * (2 * B1))
            refine ENNReal.ofReal_le_ofReal ?_
            have hc : (0 : ℝ) ≤ 1 / ((n : ℝ) * (m : ℝ)) := by positivity
            have hcpos : (0 : ℝ) < 1 / ((n : ℝ) * (m : ℝ)) := by positivity
            have hb : ∀ p : Fin n × Fin m, |g.1 (X p ω) - fcirc (X p ω)| ≤ 2 * B1 := by
              intro p
              have h1 : |g.1 (X p ω) - fcirc (X p ω)| ≤ |g.1 (X p ω)| + |fcirc (X p ω)| := by
                simpa using abs_add_le (g.1 (X p ω)) (-fcirc (X p ω))
              have h2 := hF_bound g.1 hgF (X p ω)
              have h3 := hfcirc_bound (X p ω)
              linarith
            rw [abs_mul, abs_of_pos hcpos]
            refine mul_le_mul_of_nonneg_left ?_ hc
            refine le_trans (Finset.abs_sum_le_sum_abs (fun p : Fin n × Fin m =>
              sig p ω * (g.1 (X p ω) - fcirc (X p ω))) Finset.univ) ?_
            refine Finset.sum_le_sum (fun p _ => ?_)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hb p) (abs_nonneg _)
          exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbfin
        have hle : sSup ((fun f => |R f ω|) '' ↑Fs) ≤
            (⨆ g ∈ (s : Set {f : Ω → ℝ // f ∈ localized PX F fcirc r}),
              radProc sig X fcirc g.1 ω).toReal := by
          refine Real.sSup_le ?_ (by positivity)
          rintro y ⟨f, hf, rfl⟩
          have hgs : (⟨f, hloc f hf⟩ : {f : Ω → ℝ // f ∈ localized PX F fcirc r}) ∈ s := by
            refine Finset.mem_image.mpr ⟨⟨f, hf⟩, Finset.mem_attach Fs ⟨f, hf⟩, rfl⟩
          have hsumEq : (∑ i : Fin n, ∑ j : Fin m,
                sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω)))
              = ∑ i : Fin n, ∑ j : Fin m,
                sig (i, j) ω * (f (X (i, j) ω) - fcirc (X (i, j) ω)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hgood (i, j)]
          have hprod : (∑ p : Fin n × Fin m, sig p ω * (f (X p ω) - fcirc (X p ω)))
              = ∑ i : Fin n, ∑ j : Fin m,
                sig (i, j) ω * (f (X (i, j) ω) - fcirc (X (i, j) ω)) := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
          have hvalR : ((n : ℝ) * (m : ℝ))⁻¹ *
                ∑ i : Fin n, ∑ j : Fin m, sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))
              = (1 / ((n : ℝ) * (m : ℝ))) *
                ∑ p : Fin n × Fin m, sig p ω * (f (X p ω) - fcirc (X p ω)) := by
            rw [one_div, hsumEq, hprod]
          have hval2 : (radProc sig X fcirc
                (⟨f, hloc f hf⟩ : {f : Ω → ℝ // f ∈ localized PX F fcirc r}).1 ω).toReal
              = |R f ω| := by
            show (ENNReal.ofReal |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                sig ij ω * (f (X ij ω) - fcirc (X ij ω))|).toReal
              = |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
                sig (i, j) ω * (f (X (i, j) ω) - f0 (X (i, j) ω))|
            rw [ENNReal.toReal_ofReal (abs_nonneg _), hvalR]
          have h1 : radProc sig X fcirc
                (⟨f, hloc f hf⟩ : {f : Ω → ℝ // f ∈ localized PX F fcirc r}).1 ω
              ≤ ⨆ g ∈ (s : Set {f : Ω → ℝ // f ∈ localized PX F fcirc r}),
                  radProc sig X fcirc g.1 ω :=
            le_trans
              (le_iSup (fun (_ : (⟨f, hloc f hf⟩ : {f : Ω → ℝ // f ∈ localized PX F fcirc r})
                  ∈ (s : Set {f : Ω → ℝ // f ∈ localized PX F fcirc r})) =>
                  radProc sig X fcirc
                    (⟨f, hloc f hf⟩ : {f : Ω → ℝ // f ∈ localized PX F fcirc r}).1 ω) hgs)
              (le_iSup (fun g => ⨆ (_ : g ∈ (s : Set {f : Ω → ℝ // f ∈ localized PX F fcirc r})),
                  radProc sig X fcirc g.1 ω)
                (⟨f, hloc f hf⟩ : {f : Ω → ℝ // f ∈ localized PX F fcirc r}))
          have h2 := ENNReal.toReal_mono hfin h1
          rw [hval2] at h2
          exact h2
        refine le_trans (ENNReal.ofReal_le_ofReal hle) (le_of_eq (ENNReal.ofReal_toReal hfin))
      refine le_trans hle_iSup ?_
      simp only [radSup]
      exact le_iSup (fun s' : Finset {f : Ω → ℝ // f ∈ localized PX F fcirc r} =>
        ∫⁻ ω, (⨆ g ∈ (s' : Set {f : Ω → ℝ // f ∈ localized PX F fcirc r}),
          radProc sig X fcirc g.1 ω) ∂mu) s
    · exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hphi_dom r hr))
        (le_of_eq (ENNReal.toReal_ofReal hphinn))
  have hmain := htail d hd Ω hΩ_sub PX hPXinst hPX_ac n m hn hm ΩS mu hmuinst
    f0 F fhat Z (fun i j => X (i, j)) (fun i j => eps (i, j)) (fun i j => sig (i, j)) B1 B2 B3
    hB1_pos (le_of_lt hB2_pos) (ne_of_gt hB2_pos) (le_of_lt hB3_pos) (ne_of_gt hB3_pos)
    phi rstar t
    pZ_meas hZ_idd hZ_indep hX_meas hX_law hX_indep hZX_indep heps_meas heps_indep
    hsig_meas hsig_law hsig_indep hsig_indep2 hZ_int hf0_mean hf0_bound hF_bound hf0_meas
    hF_meas pF_int hF_starconvex pfhat_int hfhat_aemeas pU_cont pdev_int pdev_tail
    peps_int peps_tail' pRad_int pERM pfix
  have hkey := hmain hreg hF_sep
  have hkey' : mu {ω : ΩS |
        |(l2Err PX fcirc (fhat ω)).toReal -
            (1 / ((n : ℝ) * (m : ℝ))) *
              ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2| >
          (1 / 2) * (l2Err PX fcirc (fhat ω)).toReal +
            c38 * B1 ^ 2 * rstar +
            c39 * B1 ^ 2 * (t + 1) / ((n : ℝ) * (m : ℝ))} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
    classical
    have hN : ∀ p : Fin n × Fin m, mu {ω : ΩS | f0 (X p ω) ≠ fcirc (X p ω)} = 0 := by
      intro p
      have hms : MeasurableSet {x : Ω | f0 x ≠ fcirc x} := by
        have h0 : MeasurableSet ({0} : Set ℝ)ᶜ := (measurableSet_singleton 0).compl
        have hp : MeasurableSet ((fun x : Ω => f0 x - fcirc x) ⁻¹' ({0} : Set ℝ)ᶜ) :=
          h0.preimage (hf0_meas.sub hfcirc_meas)
        have hEqSet : ((fun x : Ω => f0 x - fcirc x) ⁻¹' ({0} : Set ℝ)ᶜ)
            = {x : Ω | f0 x ≠ fcirc x} := by
          ext x
          simp [sub_ne_zero]
        rw [hEqSet] at hp
        exact hp
      have hpre : {ω : ΩS | f0 (X p ω) ≠ fcirc (X p ω)} = X p ⁻¹' {x : Ω | f0 x ≠ fcirc x} := rfl
      rw [hpre, ← MeasureTheory.Measure.map_apply (hX_meas p) hms, hX_law p]
      have hzero := MeasureTheory.mem_ae_iff.mp hf0_eq_fcirc
      simpa only [Set.compl_setOf] using hzero
    have hN' : mu {ω : ΩS | ¬ ∀ p : Fin n × Fin m, f0 (X p ω) = fcirc (X p ω)} = 0 := by
      have hset : {ω : ΩS | ¬ ∀ p : Fin n × Fin m, f0 (X p ω) = fcirc (X p ω)}
          = ⋃ p : Fin n × Fin m, {ω : ΩS | f0 (X p ω) ≠ fcirc (X p ω)} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall, ne_eq]
      rw [hset]
      exact MeasureTheory.measure_iUnion_null_iff.mpr hN
    have hae : ∀ᵐ ω ∂mu, ∀ p : Fin n × Fin m, f0 (X p ω) = fcirc (X p ω) := by
      have hmem : {ω : ΩS | ∀ p : Fin n × Fin m, f0 (X p ω) = fcirc (X p ω)} ∈ ae mu := by
        rw [MeasureTheory.mem_ae_iff]
        simpa only [Set.compl_setOf] using hN'
      exact hmem
    have hEq : ∀ᵐ ω ∂mu,
        PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.predError
            PX f0 (fhat ω) = (l2Err PX fcirc (fhat ω)).toReal ∧
          PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.empSqDisc
              (fun i j => X (i, j)) f0 ω (fhat ω)
            = (1 / ((n : ℝ) * (m : ℝ))) *
                ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2 := by
      filter_upwards [hae, pfhat_int] with ω hgood hint
      refine ⟨?_, ?_⟩
      · show (∫ x, (fhat ω x - f0 x) ^ 2 ∂PX) = (l2Err PX fcirc (fhat ω)).toReal
        have hcaseq : (fun x : Ω => (fhat ω x - f0 x) ^ 2)
            =ᵐ[PX] (fun x : Ω => (fhat ω x - fcirc x) ^ 2) := by
          filter_upwards [hf0_eq_fcirc] with x hx
          rw [hx]
        have hint2 : Integrable (fun x : Ω => (fhat ω x - fcirc x) ^ 2) PX := hint.congr hcaseq
        have hnn : (0 : ℝ) ≤ ∫ x, (fhat ω x - fcirc x) ^ 2 ∂PX :=
          integral_nonneg fun x => sq_nonneg _
        have hof : ENNReal.ofReal (∫ x, (fhat ω x - fcirc x) ^ 2 ∂PX) = l2Err PX fcirc (fhat ω) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint2
            (Filter.Eventually.of_forall fun x => sq_nonneg (fhat ω x - fcirc x))
        calc (∫ x, (fhat ω x - f0 x) ^ 2 ∂PX)
            = ∫ x, (fhat ω x - fcirc x) ^ 2 ∂PX := MeasureTheory.integral_congr_ae hcaseq
          _ = (ENNReal.ofReal (∫ x, (fhat ω x - fcirc x) ^ 2 ∂PX)).toReal :=
              (ENNReal.toReal_ofReal hnn).symm
          _ = (l2Err PX fcirc (fhat ω)).toReal := by rw [hof]
      · show ((n : ℝ) * (m : ℝ))⁻¹ *
            ∑ i : Fin n, ∑ j : Fin m, (fhat ω (X (i, j) ω) - f0 (X (i, j) ω)) ^ 2
          = (1 / ((n : ℝ) * (m : ℝ))) *
              ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2
        rw [one_div]
        congr 1
        rw [← Finset.univ_product_univ, Finset.sum_product]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hgood (i, j)]
    have hEqnull : mu {ω : ΩS | ¬ (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.predError
            PX f0 (fhat ω) = (l2Err PX fcirc (fhat ω)).toReal ∧
          PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.empSqDisc
              (fun i j => X (i, j)) f0 ω (fhat ω)
            = (1 / ((n : ℝ) * (m : ℝ))) *
                ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2)} = 0 := by
      have hh := MeasureTheory.mem_ae_iff.mp hEq
      simpa only [Set.compl_setOf] using hh
    have hsub : {ω : ΩS |
        |(l2Err PX fcirc (fhat ω)).toReal -
            (1 / ((n : ℝ) * (m : ℝ))) *
              ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2| >
          (1 / 2) * (l2Err PX fcirc (fhat ω)).toReal +
            c38 * B1 ^ 2 * rstar +
            c39 * B1 ^ 2 * (t + 1) / ((n : ℝ) * (m : ℝ))} ⊆
        (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.lemmaS2Event
            PX f0 (fun i j => X (i, j)) fhat B1 rstar t c38 c39)ᶜ ∪
          {ω : ΩS | ¬ (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.predError
              PX f0 (fhat ω) = (l2Err PX fcirc (fhat ω)).toReal ∧
            PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.empSqDisc
                (fun i j => X (i, j)) f0 ω (fhat ω)
              = (1 / ((n : ℝ) * (m : ℝ))) *
                  ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2)} := by
      intro ω hω
      by_cases hE : PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.predError
              PX f0 (fhat ω) = (l2Err PX fcirc (fhat ω)).toReal ∧
            PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.empSqDisc
                (fun i j => X (i, j)) f0 ω (fhat ω)
              = (1 / ((n : ℝ) * (m : ℝ))) *
                  ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2
      · left
        obtain ⟨hA, hB⟩ := hE
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le,
          PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.lemmaS2Event]
        rw [hA, hB]
        exact hω
      · right
        exact hE
    calc mu {ω : ΩS |
        |(l2Err PX fcirc (fhat ω)).toReal -
            (1 / ((n : ℝ) * (m : ℝ))) *
              ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2| >
          (1 / 2) * (l2Err PX fcirc (fhat ω)).toReal +
            c38 * B1 ^ 2 * rstar +
            c39 * B1 ^ 2 * (t + 1) / ((n : ℝ) * (m : ℝ))}
        ≤ mu ((PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.lemmaS2Event
            PX f0 (fun i j => X (i, j)) fhat B1 rstar t c38 c39)ᶜ ∪
          {ω : ΩS | ¬ (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.predError
              PX f0 (fhat ω) = (l2Err PX fcirc (fhat ω)).toReal ∧
            PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.empSqDisc
                (fun i j => X (i, j)) f0 ω (fhat ω)
              = (1 / ((n : ℝ) * (m : ℝ))) *
                  ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2)}) :=
          MeasureTheory.measure_mono hsub
      _ ≤ mu (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.lemmaS2Event
            PX f0 (fun i j => X (i, j)) fhat B1 rstar t c38 c39)ᶜ +
          mu {ω : ΩS | ¬ (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.predError
              PX f0 (fhat ω) = (l2Err PX fcirc (fhat ω)).toReal ∧
            PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.empSqDisc
                (fun i j => X (i, j)) f0 ω (fhat ω)
              = (1 / ((n : ℝ) * (m : ℝ))) *
                  ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2)} :=
          MeasureTheory.measure_union_le _ _
      _ = mu (PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported.lemmaS2Event
            PX f0 (fun i j => X (i, j)) fhat B1 rstar t c38 c39)ᶜ := by
          rw [hEqnull, add_zero]
      _ ≤ ENNReal.ofReal (Real.exp (-t)) := hkey
  exact hkey'
  /- @proof-region region.target-node.session.873e41438271e67e end -/

end Statlib.Imported
end

