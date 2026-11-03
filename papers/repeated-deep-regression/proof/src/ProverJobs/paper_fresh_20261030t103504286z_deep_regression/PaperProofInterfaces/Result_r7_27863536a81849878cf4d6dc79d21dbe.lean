import Lean
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ExternalNodes.Node_31d1bfda1f2c4bccb0b1
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Vocabulary
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ProvedNodes
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Base

namespace PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression

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

theorem Theorem_2_1_first_main_theorem_thm_thm1_non_asymptotic_prediction_error_bound_for_repeated_measurements_regression :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ (d : ℕ) (hd : 0 < d) (ΩS : Type*) [MeasurableSpace ΩS] (mu : Measure ΩS)

      [IsProbabilityMeasure mu] (Ω : Set (Fin d → ℝ)) (hΩ_meas : MeasurableSet Ω)
      (hΩ_sub : Ω ⊆ Set.Icc (0 : Fin d → ℝ) 1) (PX : Measure Ω) [IsProbabilityMeasure PX]
      (hPX_ac : PX ≪ Measure.comap (fun x : Ω => (x : Fin d → ℝ))
        (volume : Measure (Fin d → ℝ))) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
      (X : Fin n × Fin m → ΩS → Ω) (Z : Fin n → ΩS → Ω → ℝ) (eps sig : Fin n × Fin m → ΩS → ℝ)
      (F : Set (Ω → ℝ)) (fcirc : Ω → ℝ) (fhat : ΩS → Ω → ℝ) (B1 B2 B3 rstar : ℝ)
      (phi : ℝ → ℝ) (f0 : Ω → ℝ),

      
      (hX_meas : ∀ ij : Fin n × Fin m, Measurable (X ij)) →
      (hX_indep : iIndepFun X mu) →
      (hX_ident : ∀ ij ij' : Fin n × Fin m, IdentDistrib (X ij) (X ij') mu mu) →
      (hX_law : ∀ ij : Fin n × Fin m, Measure.map (X ij) mu = PX) →
      
      
      
      
      (hZ_meas : ∀ i : Fin n, Measurable (fun p : ΩS × Ω => Z i p.1 p.2)) →
      (hZ_indep : iIndepFun Z mu) →
      (hZ_ident : ∀ i i' : Fin n, IdentDistrib (Z i) (Z i') mu mu) →
      
      (hfcirc_cond : ∀ (i : Fin n) (j : Fin m),
        ∀ᵐ ω ∂mu, fcirc (X (i, j) ω) =
          mu[fun ω => Z i ω (X (i, j) ω) |
              MeasurableSpace.comap (X (i, j)) (inferInstance : MeasurableSpace Ω)] ω) →
      
      (hXZ_indep : IndepFun (Function.swap X) (Function.swap Z) mu) →
      
      (hEps_meas : ∀ ij : Fin n × Fin m, Measurable (eps ij)) →
      (hEps_indep : iIndepFun eps mu) →
      (hEps_data_indep : IndepFun (Function.swap eps)
        (fun ω : ΩS => (Function.swap X ω, Function.swap Z ω)) mu) →
      (hEps_int : ∀ ij : Fin n × Fin m, Integrable (eps ij) mu) →
      (hEps_mean : ∀ ij : Fin n × Fin m, ∫ ω, eps ij ω ∂mu = 0) →
      
      (hU_int : ∀ (i : Fin n) (j : Fin m),
        Integrable (fun ω => stochPart Z fcirc i ω (X (i, j) ω) * fcirc (X (i, j) ω)) mu) →
      (hU_center : ∀ (i : Fin n) (j : Fin m),
        ∫ ω, stochPart Z fcirc i ω (X (i, j) ω) * fcirc (X (i, j) ω) ∂mu = 0) →
      
      
      
      
      (hU_cont : ∀ (i : Fin n) (ω : ΩS), Continuous (fun z : Ω => Z i ω z - f0 z)) →
      
      (hSig_meas : ∀ ij : Fin n × Fin m, Measurable (sig ij)) →
      (hSig_indep : iIndepFun sig mu) →
      (hSig_val : ∀ ij : Fin n × Fin m,
        mu {ω | sig ij ω = 1} = 1 / 2 ∧ mu {ω | sig ij ω = -1} = 1 / 2) →
      (hSig_data_indep : IndepFun (Function.swap sig)
        (fun ω : ΩS => (Function.swap X ω, (Function.swap Z ω, Function.swap eps ω))) mu) →
      
      
      (hFhat_meas : Measurable fhat) →
      (hFhat_argmin : ∀ᵐ ω ∂mu, fhat ω ∈ F ∧
        ∀ f ∈ F, empRisk X (response Z eps X fcirc) (fhat ω) ω ≤
          empRisk X (response Z eps X fcirc) f ω) →
      
      
      
      
      (hfcirc_meas : Measurable fcirc) →
      (hF_meas : ∀ f ∈ F, Measurable f) →
      (hFhat_joint : AEMeasurable (fun p : ΩS × Ω => fhat p.1 p.2) (mu.prod PX)) →
      (hFhat_risk_meas : AEMeasurable (fun ω => l2Err PX fcirc (fhat ω)) mu) →
      
      (hB1_pos : 0 < B1) →

      
      
      
      
      
      
      (hB1_ge_one : 1 ≤ B1) →

      (hfcirc_bound : ∀ x : Ω, |fcirc x| ≤ B1) →
      (hF_bound : ∀ f ∈ F, ∀ x : Ω, |f x| ≤ B1) →
      
      
      
      (hB2_pos : 0 < B2) →
      (hU_exp : ∀ (i : Fin n) (j : Fin m),
        ∫⁻ ω, ENNReal.ofReal (Real.exp (|stochPart Z fcirc i ω (X (i, j) ω)| / B2)) ∂mu ≤ 1) →
      (hB3_pos : 0 < B3) →
      (hEps_exp : ∀ (i : Fin n) (j : Fin m),
        ∫⁻ ω, ENNReal.ofReal (Real.exp (|eps (i, j) ω| / B3)) ∂mu ≤ 1) →

      
      (hrstar_pos : 0 < rstar) →
      (hphi_nonneg : ∀ r ∈ Set.Ici rstar, 0 ≤ phi r / Real.sqrt r) →
      (hphi_antitone : AntitoneOn (fun r => phi r / Real.sqrt r) (Set.Ici rstar)) →
      (hphi_fix : phi rstar ≤ rstar) →
      (hphi_dom : ∀ r ∈ Set.Ici rstar,
        radSup mu PX F fcirc sig X r ≤ ENNReal.ofReal (phi r)) →
      
      
      
      (hZ_int : ∀ i : Fin n, ∀ᵐ x ∂PX, Integrable (fun ω => Z i ω x) mu) →
      (hf0_def : ∀ i : Fin n, ∀ᵐ x ∂PX, f0 x = ∫ (ω : ΩS), Z i ω x ∂mu) →
      (hf0_meas : Measurable f0) →
      (hf0_bound : ∀ x : Ω, |f0 x| ≤ B1) →
      (hf0_eq_fcirc : ∀ᵐ x ∂PX, f0 x = fcirc x) →
      
      (hF_star : StarConvex ℝ f0 F) →
      
      
      
      
      (hF_sep : ∃ F0 : Set (Ω → ℝ), F0.Countable ∧ F0 ⊆ F ∧
        ∀ f ∈ F, ∃ u : ℕ → (Ω → ℝ),
          (∀ k : ℕ, u k ∈ F0) ∧
            ∀ x : Ω, Filter.Tendsto (fun k : ℕ => u k x) Filter.atTop (nhds (f x))) →


      
      predErr mu PX fcirc fhat ≤
        ENNReal.ofReal
          (c1 * ((infRisk PX F fcirc).toReal + (B1 ^ 2 + B2 ^ 2) / (n : ℝ)
            + (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)))
:= by
  /- @proof-region region.root.66f203f90346 begin -/
  obtain ⟨c38, c39, hc38_pos, hc39_pos, htail⟩ := statopia_math_node_705087346_cfee792d
  refine ⟨2 + 2 * c38 + 12 * c39, by linarith [hc38_pos.le, hc39_pos.le], ?_⟩
  intro d hd ΩS _ mu _ Ω hΩ_meas hΩ_sub PX _ hPX_ac n m hn hm
    X Z eps sig F fcirc fhat B1 B2 B3 rstar phi f0
  intro hX_meas hX_indep hX_ident hX_law hZ_meas hZ_indep hZ_ident hfcirc_cond
    hXZ_indep hEps_meas hEps_indep hEps_data_indep hEps_int hEps_mean hU_int hU_center
    hU_cont hSig_meas hSig_indep hSig_val hSig_data_indep hFhat_meas hFhat_argmin
    hfcirc_meas hF_meas hFhat_joint hFhat_risk_meas hB1_pos hB1_ge_one
    hfcirc_bound hF_bound hB2_pos hU_exp hB3_pos hEps_exp
    hrstar_pos hphi_nonneg hphi_antitone hphi_fix hphi_dom
    hZ_int hf0_def hf0_meas hf0_bound hf0_eq_fcirc hF_star hF_sep
  have hnR : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn.le
  have hmem : ∀ᵐ ω ∂mu, fhat ω ∈ F :=
    hFhat_argmin.mono fun ω h => h.1
  have hbdd : ∀ f ∈ F, l2Err PX fcirc f ≤ ENNReal.ofReal (4 * B1 ^ 2) := by
    intro f hf
    have hstep : ∫⁻ x, ENNReal.ofReal ((f x - fcirc x) ^ 2) ∂PX
        ≤ ∫⁻ (_ : Ω), ENNReal.ofReal (4 * B1 ^ 2) ∂PX := by
      refine lintegral_mono fun x => ?_
      apply ENNReal.ofReal_le_ofReal
      have ha := abs_le.1 (hF_bound f hf x)
      have hb := abs_le.1 (hfcirc_bound x)
      have h1 : |f x - fcirc x| ≤ 2 * B1 := by
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
      nlinarith [(abs_le.1 h1).1, (abs_le.1 h1).2]
    have hconst : ∫⁻ (_ : Ω), ENNReal.ofReal (4 * B1 ^ 2) ∂PX
        = ENNReal.ofReal (4 * B1 ^ 2) := by
      rw [lintegral_const, measure_univ, mul_one]
    calc l2Err PX fcirc f = ∫⁻ x, ENNReal.ofReal ((f x - fcirc x) ^ 2) ∂PX := rfl
      _ ≤ ∫⁻ (_ : Ω), ENNReal.ofReal (4 * B1 ^ 2) ∂PX := hstep
      _ = ENNReal.ofReal (4 * B1 ^ 2) := hconst
  have hne : ∀ f ∈ F, l2Err PX fcirc f ≠ ⊤ := fun f hf =>
    (lt_of_le_of_lt (hbdd f hf) ENNReal.ofReal_lt_top).ne
  have hAbound : ∀ᵐ ω ∂mu, (l2Err PX fcirc (fhat ω)).toReal ≤ 4 * B1 ^ 2 :=
    hmem.mono fun ω hω => by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbdd (fhat ω) hω)
      rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hA_meas : AEMeasurable (fun ω => (l2Err PX fcirc (fhat ω)).toReal) mu :=
    ENNReal.measurable_toReal.comp_aemeasurable hFhat_risk_meas
  have hAint : Integrable (fun ω => (l2Err PX fcirc (fhat ω)).toReal) mu := by
    refine Integrable.of_bound hA_meas.aestronglyMeasurable (4 * B1 ^ 2) ?_
    filter_upwards [hAbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hω
  have hAeq : ∀ᵐ ω ∂mu,
      ENNReal.ofReal ((l2Err PX fcirc (fhat ω)).toReal) = l2Err PX fcirc (fhat ω) :=
    hmem.mono fun ω hω => ENNReal.ofReal_toReal (hne (fhat ω) hω)
  have hZ_meas' : ∀ i : Fin n, Measurable (Z i) :=
    fun i => measurable_pi_iff.mpr fun x =>
      (hZ_meas i).comp (measurable_prodMk_right (y := x))
  have hU_cont_ax : ∀ (i : Fin n), ∀ᵐ ω ∂mu, ∀ᵐ (x : Ω) ∂PX,
      ContinuousAt (fun z : Ω => Z i ω z - f0 z) x := by
    intro i
    exact Filter.Eventually.of_forall fun ω =>
      Filter.Eventually.of_forall fun x => (hU_cont i ω).continuousAt
  have hF_int : ∀ f ∈ F, Integrable (fun x : Ω => (f x - f0 x) ^ 2) PX := by
    intro f hf
    have hm : Measurable fun x : Ω => (f x - f0 x) ^ 2 := by
      have h1 : Measurable fun x : Ω => f x - f0 x := (hF_meas f hf).sub hf0_meas
      simpa [pow_two] using h1.mul h1
    refine Integrable.of_bound hm.aestronglyMeasurable (4 * B1 ^ 2) ?_
    filter_upwards with x
    have ha := abs_le.1 (hF_bound f hf x)
    have hb := abs_le.1 (hf0_bound x)
    have h1 : |f x - f0 x| ≤ 2 * B1 := by
      rw [abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    have h2 := abs_le.1 h1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x - f0 x))]
    nlinarith [h2.1, h2.2]
  have hfhat_int : ∀ᵐ ω ∂mu, Integrable (fun x : Ω => (fhat ω x - f0 x) ^ 2) PX := by
    filter_upwards [hmem] with ω hω
    have hm : Measurable fun x : Ω => (fhat ω x - f0 x) ^ 2 := by
      have h1 : Measurable fun x : Ω => fhat ω x - f0 x :=
        (hF_meas (fhat ω) hω).sub hf0_meas
      simpa [pow_two] using h1.mul h1
    refine Integrable.of_bound hm.aestronglyMeasurable (4 * B1 ^ 2) ?_
    filter_upwards with x
    have ha := abs_le.1 (hF_bound (fhat ω) hω x)
    have hb := abs_le.1 (hf0_bound x)
    have h1 : |fhat ω x - f0 x| ≤ 2 * B1 := by
      rw [abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    have h2 := abs_le.1 h1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (fhat ω x - f0 x))]
    nlinarith [h2.1, h2.2]
  have h_min : ∀ᵐ ω ∂mu, ∀ f ∈ F,
      (1 / ((n : ℝ) * (m : ℝ))) *
          ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2
        ≤ (1 / ((n : ℝ) * (m : ℝ))) *
          ∑ ij : Fin n × Fin m, (f (X ij ω) - fcirc (X ij ω)) ^ 2 := by
    have hcoll : ∀ᵐ ω ∂mu, ∀ ij : Fin n × Fin m, response Z eps X fcirc ij ω = fcirc (X ij ω) := by
      have h := statopia_math_node_1928020627_7c479ed8 mu n m hn hm X hX_meas Z hZ_meas
        fcirc hfcirc_meas eps hEps_meas B2 B3 hB2_pos hB3_pos
        (fun ij => hU_exp ij.1 ij.2) (fun ij => hEps_exp ij.1 ij.2)
      exact h.mono fun ω hω => hω.2
    filter_upwards [hcoll, hFhat_argmin] with ω hc ha f hf
    have hcollapse : ∀ g : Ω → ℝ, empRisk X (response Z eps X fcirc) g ω
        = (1 / ((n : ℝ) * (m : ℝ))) *
          ∑ ij : Fin n × Fin m, (g (X ij ω) - fcirc (X ij ω)) ^ 2 := by
      intro g
      rw [empRisk]
      congr 1
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, j⟩ -
      rw [hc (i, j)]
      ring
    have harg := ha.2 f hf
    rw [hcollapse (fhat ω), hcollapse f] at harg
    exact harg
  have hdev : ∀ t : ℝ, 0 < t →
      rstar ≤ 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) →
      mu {ω : ΩS |
          |(l2Err PX fcirc (fhat ω)).toReal
              - (1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                  (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2|
            > (1 / 2) * (l2Err PX fcirc (fhat ω)).toReal + c38 * B1 ^ 2 * rstar
              + c39 * B1 ^ 2 * (t + 1) / ((n : ℝ) * (m : ℝ))}
        ≤ ENNReal.ofReal (Real.exp (-t)) := by
    intro t ht hreg
    exact htail d hd ΩS mu Ω hΩ_meas hΩ_sub PX hPX_ac n m hn hm X Z eps sig F fcirc fhat
      B1 B2 B3 rstar phi f0 hX_meas hX_indep hX_ident hX_law hZ_meas hZ_indep hZ_ident
      hfcirc_cond hXZ_indep hEps_meas hEps_indep hEps_data_indep hEps_int hEps_mean
      hU_int hU_center hU_cont hSig_meas hSig_indep hSig_val hSig_data_indep hFhat_meas
      hFhat_argmin hfcirc_meas hF_meas hFhat_joint hFhat_risk_meas hB1_pos hB1_ge_one
      hfcirc_bound hF_bound hB2_pos hU_exp hB3_pos hEps_exp hrstar_pos hphi_nonneg
      hphi_antitone hphi_fix
      hphi_dom hZ_int hf0_def hf0_meas hf0_bound hf0_eq_fcirc hF_star hF_sep t ht hreg
  have hpred : ∀ f ∈ F,
      (∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
        ≤ 2 * (l2Err PX fcirc f).toReal
          + max rstar (2 * c38 * B1 ^ 2 * rstar)
          + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := by
    intro f hf
    exact statopia_math_node_1164508671_4013cd2b (mu := mu) (PX := PX)
      (hn := hn) (hm := hm) (n := n) (m := m) (X := X) (hX_meas := hX_meas)
      (hX_law := hX_law) (B1 := B1) (rstar := rstar) (c38 := c38) (c39 := c39)
      (hB1 := hB1_pos) (hrstar := hrstar_pos) (hc38 := hc38_pos)
      (hc39 := hc39_pos) (fcirc := fcirc) (hfcirc_meas := hfcirc_meas)
      (hfcirc_bound := hfcirc_bound) (F := F) (hF_meas := hF_meas)
      (hF_bound := hF_bound) (fhat := fhat) (hmem := hmem) (hA_meas := hA_meas)
      (hmin := h_min) (hdev := hdev) f hf
  have hFne : ∃ f : Ω → ℝ, f ∈ F := by
    by_contra hcon
    push_neg at hcon
    have hfalse : ∀ᵐ ω ∂mu, False := hmem.mono fun ω hω => hcon (fhat ω) hω
    have h0 : mu Set.univ = 0 := by
      simpa using (MeasureTheory.ae_iff.1 hfalse)
    rw [measure_univ] at h0
    exact one_ne_zero h0
  obtain ⟨f₀, hf₀⟩ := hFne
  haveI : Nonempty {f : Ω → ℝ // f ∈ F} := ⟨⟨f₀, hf₀⟩⟩
  have hIne : infRisk PX F fcirc ≠ ⊤ :=
    (lt_of_le_of_lt (le_trans
      (iInf_le (f := fun f : {f : Ω → ℝ // f ∈ F} => l2Err PX fcirc f.1) ⟨f₀, hf₀⟩)
      (hbdd f₀ hf₀)) ENNReal.ofReal_lt_top).ne
  have key :
      (∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
        ≤ 2 * (infRisk PX F fcirc).toReal + (max rstar (2 * c38 * B1 ^ 2 * rstar)
            + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ))) := by
    have hreal : ∀ f : {f : Ω → ℝ // f ∈ F},
        ((∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
          - (max rstar (2 * c38 * B1 ^ 2 * rstar)
              + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)))) / 2
          ≤ (l2Err PX fcirc f.1).toReal := by
      intro f
      have h : (∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
          ≤ 2 * (l2Err PX fcirc f.1).toReal
            + max rstar (2 * c38 * B1 ^ 2 * rstar)
            + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)) := hpred f.1 f.2
      linarith
    have hc : ((∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
          - (max rstar (2 * c38 * B1 ^ 2 * rstar)
              + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)))) / 2
        ≤ (infRisk PX F fcirc).toReal := by
      have hmax : (max (((∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
            - (max rstar (2 * c38 * B1 ^ 2 * rstar)
                + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)))) / 2) 0)
          ≤ (infRisk PX F fcirc).toReal := by
        have h1 : ENNReal.ofReal (max (((∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
              - (max rstar (2 * c38 * B1 ^ 2 * rstar)
                  + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)))) / 2) 0)
            ≤ infRisk PX F fcirc := by
          have h2 : ENNReal.ofReal (max (((∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
              - (max rstar (2 * c38 * B1 ^ 2 * rstar)
                  + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ)))) / 2) 0)
              ≤ ⨅ (f : {f : Ω → ℝ // f ∈ F}), l2Err PX fcirc f.1 :=
            le_iInf fun f =>
              le_trans (ENNReal.ofReal_le_ofReal (max_le (hreal f) ENNReal.toReal_nonneg))
                ENNReal.ofReal_toReal_le
          exact h2
        have h3 := ENNReal.toReal_mono hIne h1
        rwa [ENNReal.toReal_ofReal (le_max_right _ 0)] at h3
      exact le_trans (le_max_left _ 0) hmax
    linarith
  have hinv : (0 : ℝ) ≤ 1 / ((n : ℝ) * (m : ℝ)) := by positivity
  have hR0 : 0 ≤ rstar + 1 / ((n : ℝ) * (m : ℝ)) := by linarith [hrstar_pos.le, hinv]
  have hI0 : 0 ≤ (infRisk PX F fcirc).toReal := ENNReal.toReal_nonneg
  have hc1nonneg : (0 : ℝ) ≤ 2 + 2 * c38 + 12 * c39 := by
    linarith [hc38_pos.le, hc39_pos.le]
  have hB1T : B1 ^ 2 ≤ B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
      + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2 := by
    have h1 : 0 ≤ B2 ^ 2 * (Real.log (n : ℝ)) ^ 2 := by positivity
    have h2 : 0 ≤ B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2 := by positivity
    linarith
  have hTnn : (0 : ℝ) ≤ B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
      + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2 := by
    have h1 : (0 : ℝ) ≤ B1 ^ 2 := by positivity
    have h2 : 0 ≤ B2 ^ 2 * (Real.log (n : ℝ)) ^ 2 := by positivity
    have h3 : 0 ≤ B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2 := by positivity
    linarith
  have hT1 : (1 : ℝ) ≤ B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
      + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2 := by
    have hBsq1 : (1 : ℝ) ≤ B1 ^ 2 := by nlinarith [sq_nonneg (B1 - 1), hB1_ge_one]
    have h2 : 0 ≤ B2 ^ 2 * (Real.log (n : ℝ)) ^ 2 := by positivity
    have h3 : 0 ≤ B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2 := by positivity
    linarith
  have hA1 : 2 * (infRisk PX F fcirc).toReal
      ≤ (2 + 2 * c38 + 12 * c39) * (infRisk PX F fcirc).toReal := by
    nlinarith [hI0, hc38_pos.le, hc39_pos.le]
  have hK : max rstar (2 * c38 * B1 ^ 2 * rstar)
        + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ))
      ≤ (2 + 2 * c38 + 12 * c39)
        * ((rstar + 1 / ((n : ℝ) * (m : ℝ)))
          * (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) := by
    have hX0 : (0 : ℝ) ≤ (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
        (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
          + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2) := mul_nonneg hR0 hTnn
    have hbase : rstar ≤ (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
        (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
          + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2) := by
      have h1 : rstar ≤ rstar + 1 / ((n : ℝ) * (m : ℝ)) := by linarith [hinv]
      have h2 := mul_le_mul h1 hT1 (zero_le_one : (0 : ℝ) ≤ 1) hR0
      simpa using h2
    have hsqr : B1 ^ 2 * rstar ≤ (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
        (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
          + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2) := by
      have h1 : B1 ^ 2 * rstar ≤ (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
          + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2) * rstar :=
        mul_le_mul_of_nonneg_right hB1T hrstar_pos.le
      have h2 : (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
          + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2) * rstar
          ≤ (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)
            * (rstar + 1 / ((n : ℝ) * (m : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hTnn
        linarith [hinv]
      calc B1 ^ 2 * rstar ≤ (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)
            * (rstar + 1 / ((n : ℝ) * (m : ℝ))) := le_trans h1 h2
        _ = (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
            (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2) := by ring
    have hAx : max rstar (2 * c38 * B1 ^ 2 * rstar)
        ≤ max 1 (2 * c38) * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
          (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) := by
      have hM1 : (1 : ℝ) ≤ max 1 (2 * c38) := le_max_left _ _
      have hM0 : (0 : ℝ) ≤ max 1 (2 * c38) := le_trans zero_le_one hM1
      have h2c38 : (0 : ℝ) ≤ 2 * c38 := by linarith [hc38_pos.le]
      apply max_le
      · simpa using mul_le_mul hM1 hbase hrstar_pos.le hM0
      · have h2c38le : 2 * c38 ≤ max 1 (2 * c38) := le_max_right _ _
        calc 2 * c38 * B1 ^ 2 * rstar = 2 * c38 * (B1 ^ 2 * rstar) := by ring
          _ ≤ 2 * c38 * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) :=
              mul_le_mul_of_nonneg_left hsqr h2c38
          _ ≤ max 1 (2 * c38) * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) :=
              mul_le_mul_of_nonneg_right h2c38le hX0
    have hMle : max 1 (2 * c38) ≤ 2 + 2 * c38 := by
      apply max_le <;> linarith [hc38_pos.le]
    have hKA : max rstar (2 * c38 * B1 ^ 2 * rstar)
        ≤ (2 + 2 * c38) * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
          (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) :=
      le_trans hAx (mul_le_mul_of_nonneg_right hMle hX0)
    have hKB : 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ))
        ≤ 4 * c39 * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
          (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) := by
      have h2c39 : (0 : ℝ) ≤ 4 * c39 := by linarith [hc39_pos.le]
      have hprod : B1 ^ 2 * (1 / ((n : ℝ) * (m : ℝ)))
          ≤ (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
            (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2) := by
        have h1 : B1 ^ 2 * (1 / ((n : ℝ) * (m : ℝ)))
            ≤ (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)
              * (1 / ((n : ℝ) * (m : ℝ))) :=
          mul_le_mul_of_nonneg_right hB1T hinv
        have h2 : (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)
            * (1 / ((n : ℝ) * (m : ℝ)))
            ≤ (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)
              * (rstar + 1 / ((n : ℝ) * (m : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hTnn
          linarith [hrstar_pos.le]
        calc B1 ^ 2 * (1 / ((n : ℝ) * (m : ℝ)))
            ≤ (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)
              * (rstar + 1 / ((n : ℝ) * (m : ℝ))) := le_trans h1 h2
          _ = (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2) := by ring
      calc 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ))
          = 4 * c39 * (B1 ^ 2 * (1 / ((n : ℝ) * (m : ℝ)))) := by ring
        _ ≤ 4 * c39 * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) :=
              mul_le_mul_of_nonneg_left hprod h2c39
    have hsum : max rstar (2 * c38 * B1 ^ 2 * rstar)
          + 4 * c39 * B1 ^ 2 / ((n : ℝ) * (m : ℝ))
        ≤ (2 + 2 * c38) * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
            (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2))
          + 4 * c39 * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
            (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) := add_le_add hKA hKB
    have hfac : (2 + 2 * c38) * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
          (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2))
        + 4 * c39 * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
          (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2))
        = (2 + 2 * c38 + 4 * c39) * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
          (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) := by ring
    have hmono : (2 + 2 * c38 + 4 * c39) * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
          (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2))
        ≤ (2 + 2 * c38 + 12 * c39) * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
          (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
            + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) :=
      mul_le_mul_of_nonneg_right (by linarith [hc39_pos.le]) hX0
    linarith [hsum, hfac, hmono]
  have hkey' :
      (∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
        ≤ (2 + 2 * c38 + 12 * c39) * (infRisk PX F fcirc).toReal
          + (2 + 2 * c38 + 12 * c39) * ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
            (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) := by
    linarith [key, hA1, hK]
  have hslack : 0 ≤ (B1 ^ 2 + B2 ^ 2) / (n : ℝ) := div_nonneg (by positivity) hnR
  have hfinal : (∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
      ≤ (2 + 2 * c38 + 12 * c39) *
          ((infRisk PX F fcirc).toReal + (B1 ^ 2 + B2 ^ 2) / (n : ℝ)
            + (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) := by
    have h3 : (infRisk PX F fcirc).toReal
          + (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
            (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)
        ≤ (infRisk PX F fcirc).toReal + (B1 ^ 2 + B2 ^ 2) / (n : ℝ)
          + (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
            (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
              + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2) := by
      linarith [hslack]
    have h4 : (2 + 2 * c38 + 12 * c39) * (infRisk PX F fcirc).toReal
          + (2 + 2 * c38 + 12 * c39) *
            ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2))
        = (2 + 2 * c38 + 12 * c39) *
          ((infRisk PX F fcirc).toReal
            + (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) := by ring
    calc (∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
        ≤ (2 + 2 * c38 + 12 * c39) * (infRisk PX F fcirc).toReal
          + (2 + 2 * c38 + 12 * c39) *
            ((rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) := hkey'
      _ = (2 + 2 * c38 + 12 * c39) *
          ((infRisk PX F fcirc).toReal
            + (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) := h4
      _ ≤ (2 + 2 * c38 + 12 * c39) *
          ((infRisk PX F fcirc).toReal + (B1 ^ 2 + B2 ^ 2) / (n : ℝ)
            + (rstar + 1 / ((n : ℝ) * (m : ℝ))) *
              (B1 ^ 2 + B2 ^ 2 * (Real.log (n : ℝ)) ^ 2
                + B3 ^ 2 * (Real.log ((n : ℝ) * (m : ℝ))) ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 hc1nonneg
  have hpredEq : predErr mu PX fcirc fhat
      = ENNReal.ofReal (∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu) := by
    show (∫⁻ ω, l2Err PX fcirc (fhat ω) ∂mu) = ENNReal.ofReal (∫ ω, (l2Err PX fcirc (fhat ω)).toReal ∂mu)
    rw [← lintegral_congr_ae hAeq]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hAint
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
  rw [hpredEq]
  exact ENNReal.ofReal_le_ofReal hfinal
  /- @proof-region region.root.66f203f90346 end -/

end Statlib.Imported

-- Paper root revision 41256e8e-e229-475b-af66-3ae9fd59b7d3

