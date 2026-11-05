import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_1098378036_6924b604_7bda4bcf
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_35798353_6c7e7779_b4361b5f
import ProverJobs.jobea4701a9720de21f681f2da3.ExternalNodes.Node_a26b2b509ee15a62f52b


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
theorem statopia_math_node_4000542074_30367f47 : ∀ {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (mu nu : ProbabilityMeasure Ω)
    (zeta : ℝ) (hzeta : 0 < zeta)
    (phi : Ω → ℝ) (hphi : Measurable phi)
    (hExp : Integrable (fun x : Ω => Real.exp (zeta * phi x)) (mu : Measure Ω)),
    ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (phi x) ∂(nu : Measure Ω))
      ≤ (((zeta)⁻¹ : ℝ) : EReal)
          * (ENNReal.toEReal (InformationTheory.klDiv (nu : Measure Ω) (mu : Measure Ω))
              + ((Real.log (∫ x, Real.exp (zeta * phi x) ∂(mu : Measure Ω)) : ℝ) : EReal))
        + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(phi x)) ∂(nu : Measure Ω)) := by
  /- @proof-region region.target-node.session.f33eb3fadf0e17a6 begin -/
  classical
  intro Ω _ _ _ _ μ ν ζ hζ φ hφ hExp
  set kd : ENNReal := InformationTheory.klDiv (ν : Measure Ω) (μ : Measure Ω) with hkd
  set lr : ℝ := Real.log (∫ x, Real.exp (ζ * φ x) ∂(μ : Measure Ω)) with hlr

  have hbound : ∀ (g : Ω → ℝ), Measurable g → (∃ C : ℝ, ∀ x : Ω, |g x| ≤ C) →
      ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω))
        ≤ ((ζ⁻¹ : ℝ) : EReal)
            * (ENNReal.toEReal kd + (Real.log (∫ x, Real.exp (ζ * g x) ∂(μ : Measure Ω)) : EReal))
          + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(g x)) ∂(ν : Measure Ω)) := by
    intro g hg hgb
    obtain ⟨C, hC⟩ := hgb
    have hh : Measurable (fun x : Ω => ζ * g x) := by measurability
    have hhb : ∀ x : Ω, |ζ * g x| ≤ |ζ| * C :=
      fun x => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg ζ)
    have hc := statopia_math_node_35798353_6c7e7779 Ω μ ν (fun x => ζ * g x) hh (|ζ| * C) hhb

    have hgpos : Integrable (fun x : Ω => max (g x) 0) (ν : Measure Ω) :=
      MeasureTheory.Integrable.of_bound (by measurability) C (by
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), max_le_iff]
        exact ⟨(abs_le.mp (hC x)).2, le_trans (abs_nonneg (g x)) (hC x)⟩)
    have hgneg : Integrable (fun x : Ω => max (-(g x)) 0) (ν : Measure Ω) :=
      MeasureTheory.Integrable.of_bound (by measurability) C (by
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), max_le_iff]
        exact ⟨by linarith [(abs_le.mp (hC x)).1], le_trans (abs_nonneg (g x)) (hC x)⟩)
    have htP : (∫⁻ x, ENNReal.ofReal (max (g x) 0) ∂(ν : Measure Ω)).toReal
        = ∫ x, max (g x) 0 ∂(ν : Measure Ω) :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
        (Filter.Eventually.of_forall (fun x => le_max_right (g x) 0)) hgpos
    have htN : (∫⁻ x, ENNReal.ofReal (max (-(g x)) 0) ∂(ν : Measure Ω)).toReal
        = ∫ x, max (-(g x)) 0 ∂(ν : Measure Ω) :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
        (Filter.Eventually.of_forall (fun x => le_max_right (-(g x)) 0)) hgneg
    have hcong : (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω))
        = (∫⁻ x, ENNReal.ofReal (max (g x) 0) ∂(ν : Measure Ω)) := by
      apply MeasureTheory.lintegral_congr
      intro x
      rcases le_total 0 (g x) with h | h
      · have hmax : max (g x) 0 = g x :=
          le_antisymm (max_le (le_refl (g x)) h) (le_max_left (g x) 0)
        rw [hmax]
      · have hmax : max (g x) 0 = 0 :=
          le_antisymm (max_le h (le_refl 0)) (le_max_right (g x) 0)
        rw [hmax, ENNReal.ofReal_of_nonpos h]
        simp
    have hcongN : (∫⁻ x, ENNReal.ofReal (-(g x)) ∂(ν : Measure Ω))
        = (∫⁻ x, ENNReal.ofReal (max (-(g x)) 0) ∂(ν : Measure Ω)) := by
      apply MeasureTheory.lintegral_congr
      intro x
      rcases le_total 0 (-(g x)) with h | h
      · have hmax : max (-(g x)) 0 = -(g x) :=
          le_antisymm (max_le (le_refl (-(g x))) h) (le_max_left (-(g x)) 0)
        rw [hmax]
      · have hmax : max (-(g x)) 0 = 0 :=
          le_antisymm (max_le h (le_refl 0)) (le_max_right (-(g x)) 0)
        rw [hmax, ENNReal.ofReal_of_nonpos h]
        simp
    have hsplit : (∫ x, g x ∂(ν : Measure Ω))
        = (∫ x, max (g x) 0 ∂(ν : Measure Ω)) - (∫ x, max (-(g x)) 0 ∂(ν : Measure Ω)) := by
      rw [← MeasureTheory.integral_sub hgpos hgneg]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rcases le_total 0 (g x) with h | h
      · have h1 : max (g x) 0 = g x := le_antisymm (max_le (le_refl (g x)) h) (le_max_left (g x) 0)
        have h2 : max (-(g x)) 0 = 0 :=
          le_antisymm (max_le (by linarith) (le_refl 0)) (le_max_right (-(g x)) 0)
        rw [h1, h2]; ring
      · have h1 : max (g x) 0 = 0 := le_antisymm (max_le h (le_refl 0)) (le_max_right (g x) 0)
        have h2 : max (-(g x)) 0 = -(g x) :=
          le_antisymm (max_le (le_refl (-(g x))) (by linarith)) (le_max_left (-(g x)) 0)
        rw [h1, h2]; ring
    have htPall : (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω)).toReal
        = ∫ x, max (g x) 0 ∂(ν : Measure Ω) := by rw [hcong, htP]
    have htNall : (∫⁻ x, ENNReal.ofReal (-(g x)) ∂(ν : Measure Ω)).toReal
        = ∫ x, max (-(g x)) 0 ∂(ν : Measure Ω) := by rw [hcongN, htN]
    have hcoe : ∀ (x : NNReal), ENNReal.toEReal (↑x : ENNReal) = ((x : ℝ) : EReal) := by
      intro x
      norm_cast
    have hbr : ∀ (a : ENNReal), a ≠ ⊤ → ENNReal.toEReal a = ((a.toReal : ℝ) : EReal) := by
      intro a ha
      have hRN : a.toReal = ((a.toNNReal : NNReal) : ℝ) := by
        conv_lhs => rw [← ENNReal.coe_toNNReal ha]
        exact ENNReal.coe_toReal a.toNNReal
      rw [hRN]
      conv_lhs => rw [← ENNReal.coe_toNNReal ha]
      exact hcoe a.toNNReal
    have hAne : (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω)) ≠ ⊤ := by
      have hle : (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω)) ≤ ENNReal.ofReal C := by
        calc (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω))
            ≤ ∫⁻ x, ENNReal.ofReal C ∂(ν : Measure Ω) :=
              MeasureTheory.lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (abs_le.mp (hC x)).2)
          _ = ENNReal.ofReal C := by rw [MeasureTheory.lintegral_const]; simp
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    have hBne : (∫⁻ x, ENNReal.ofReal (-(g x)) ∂(ν : Measure Ω)) ≠ ⊤ := by
      have hle : (∫⁻ x, ENNReal.ofReal (-(g x)) ∂(ν : Measure Ω)) ≤ ENNReal.ofReal C := by
        calc (∫⁻ x, ENNReal.ofReal (-(g x)) ∂(ν : Measure Ω))
            ≤ ∫⁻ x, ENNReal.ofReal C ∂(ν : Measure Ω) :=
              MeasureTheory.lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp (hC x)).1]))
          _ = ENNReal.ofReal C := by rw [MeasureTheory.lintegral_const]; simp
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    have hA : ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω))
        = ((∫ x, max (g x) 0 ∂(ν : Measure Ω) : ℝ) : EReal) := by
      rw [hbr _ hAne, htPall]
    have hB : ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(g x)) ∂(ν : Measure Ω))
        = ((∫ x, max (-(g x)) 0 ∂(ν : Measure Ω) : ℝ) : EReal) := by
      rw [hbr _ hBne, htNall]
    rw [hA, hB]
    rw [show (∫ x, (fun x : Ω => ζ * g x) x ∂(ν : Measure Ω)) = ζ * (∫ x, g x ∂(ν : Measure Ω)) from MeasureTheory.integral_const_mul ζ g] at hc
    rw [EReal.coe_mul] at hc
    have hpos : (0 : EReal) ≤ ((ζ⁻¹ : ℝ) : EReal) := by
      exact_mod_cast (le_of_lt (inv_pos.mpr hζ))
    have hmul := mul_le_mul_of_nonneg_left hc hpos
    have hsimp : ((ζ⁻¹ : ℝ) : EReal) * (((ζ : ℝ) : EReal) * ((∫ x, g x ∂(ν : Measure Ω) : ℝ) : EReal))
        = ((∫ x, g x ∂(ν : Measure Ω) : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_mul,
        show ζ⁻¹ * (ζ * (∫ x, g x ∂(ν : Measure Ω))) = (∫ x, g x ∂(ν : Measure Ω)) from by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hζ), one_mul]]
    rw [hsimp] at hmul
    have hsum : ((∫ x, max (g x) 0 ∂(ν : Measure Ω) : ℝ) : EReal)
        = ((∫ x, g x ∂(ν : Measure Ω) : ℝ) : EReal) + ((∫ x, max (-(g x)) 0 ∂(ν : Measure Ω) : ℝ) : EReal) := by
      rw [show (∫ x, max (g x) 0 ∂(ν : Measure Ω)) = (∫ x, g x ∂(ν : Measure Ω)) + (∫ x, max (-(g x)) 0 ∂(ν : Measure Ω)) from by linarith [hsplit]]
      rw [EReal.coe_add]
    calc ((∫ x, max (g x) 0 ∂(ν : Measure Ω) : ℝ) : EReal)
        = ((∫ x, g x ∂(ν : Measure Ω) : ℝ) : EReal) + ((∫ x, max (-(g x)) 0 ∂(ν : Measure Ω) : ℝ) : EReal) := hsum
      _ ≤ ((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + ((Real.log (∫ x, Real.exp (ζ * g x) ∂(μ : Measure Ω))) : EReal)) + ((∫ x, max (-(g x)) 0 ∂(ν : Measure Ω) : ℝ) : EReal) := add_le_add hmul (le_refl _)
  have hmain :
      ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (φ x) ∂(ν : Measure Ω))
        ≤ ((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (lr : EReal))
          + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω)) := by
    have key : ∀ n : ℕ,
        ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (min (max (φ x) (-(n:ℝ))) (n:ℝ)) ∂(ν : Measure Ω))
          ≤ ((ζ⁻¹ : ℝ) : EReal)
              * (ENNReal.toEReal kd + (Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω)) : EReal))
            + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)) := by
      intro n
      have hmeas : Measurable (fun x : Ω => min (max (φ x) (-(n:ℝ))) (n:ℝ)) := by measurability
      have hbd : ∃ C : ℝ, ∀ x : Ω, |min (max (φ x) (-(n:ℝ))) (n:ℝ)| ≤ C := by
        refine ⟨(n:ℝ), fun x => ?_⟩
        have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
        rw [abs_le]
        exact ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩
      exact hbound (fun x => min (max (φ x) (-(n:ℝ))) (n:ℝ)) hmeas hbd
    by_cases hktop : kd = ⊤
    · rw [hktop]
      have hpos : (0 : EReal) < ((ζ⁻¹ : ℝ) : EReal) := by
        have h : (0 : ℝ) < ζ⁻¹ := inv_pos.mpr hζ
        exact_mod_cast h
      have htop : ((ζ⁻¹ : ℝ) : EReal) * ⊤ = ⊤ := EReal.mul_top_of_pos hpos
      simp [htop]
    · have hL : Filter.Tendsto
          (fun n : ℕ => ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (min (max (φ x) (-(n:ℝ))) (n:ℝ)) ∂(ν : Measure Ω)))
          Filter.atTop (nhds (ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (φ x) ∂(ν : Measure Ω)))) :=
        statopia_math_node_1098378036_6924b604 Ω ν φ hφ
      have hR : Filter.Tendsto
          (fun n : ℕ => ((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω)) : EReal)) + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)))
          Filter.atTop (nhds (((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (lr : EReal)) + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω)))) := by
        have hcoetend : ∀ (u : ℕ → ℝ) (a : ℝ), Filter.Tendsto u Filter.atTop (nhds a) →
            Filter.Tendsto (fun n => (u n : EReal)) Filter.atTop (nhds (a : EReal)) := by
          intro u a hu
          rw [tendsto_order]
          refine ⟨fun b hb => ?_, fun b hb => ?_⟩
          · by_cases hbot : b = ⊥
            · rw [hbot]; exact Filter.Eventually.of_forall (fun n => EReal.bot_lt_coe (u n))
            · have htop : b ≠ ⊤ := fun h => by rw [h] at hb; exact absurd hb (not_lt.mpr le_top)
              lift b to ℝ using ⟨htop, hbot⟩
              have hba : b < a := by exact_mod_cast hb
              filter_upwards [hu.eventually (Ioi_mem_nhds hba)] with n hn
              exact_mod_cast hn
          · by_cases htop : b = ⊤
            · rw [htop]; exact Filter.Eventually.of_forall (fun n => EReal.coe_lt_top (u n))
            · have hbot : b ≠ ⊥ := fun h => by rw [h] at hb; exact absurd hb (not_lt.mpr bot_le)
              lift b to ℝ using ⟨htop, hbot⟩
              have hba : a < b := by exact_mod_cast hb
              filter_upwards [hu.eventually (Iio_mem_nhds hba)] with n hn
              exact_mod_cast hn
        have hclamp_pt : ∀ x : Ω, Filter.Tendsto (fun n : ℕ => min (max (φ x) (-(n:ℝ))) (n:ℝ)) Filter.atTop (nhds (φ x)) := by
          intro x
          have hev : (fun n : ℕ => min (max (φ x) (-(n:ℝ))) (n:ℝ)) =ᶠ[Filter.atTop] (fun _ => φ x) := by
            obtain ⟨N, hN⟩ := exists_nat_ge (|φ x|)
            filter_upwards [Filter.eventually_ge_atTop N] with n hn
            have hn' : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
            have hg1 : -(n:ℝ) ≤ φ x := by linarith [(abs_le.mp hN).1]
            have hg2 : φ x ≤ (n:ℝ) := by linarith [(abs_le.mp hN).2]
            have e1 : max (φ x) (-(n:ℝ)) = φ x := le_antisymm (max_le (le_refl _) hg1) (le_max_left _ _)
            rw [e1]; exact le_antisymm (min_le_left _ _) (le_min (le_refl _) hg2)
          exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
        have hexp_pt : ∀ x : Ω, Filter.Tendsto (fun n : ℕ => Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ)))) Filter.atTop (nhds (Real.exp (ζ * φ x))) :=
          fun x => (Real.continuous_exp.tendsto (ζ * φ x)).comp ((hclamp_pt x).const_mul ζ)
        have hDCT : Filter.Tendsto (fun n : ℕ => ∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω)) Filter.atTop (nhds (∫ x, Real.exp (ζ * φ x) ∂(μ : Measure Ω))) := by
          apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun x : Ω => Real.exp (ζ * φ x) + 1)
          · filter_upwards with n
            have hm : Measurable (fun x : Ω => min (max (φ x) (-(n:ℝ))) (n:ℝ)) := (hφ.max measurable_const).min measurable_const
            exact (Real.measurable_exp.comp (measurable_const.mul hm)).aestronglyMeasurable
          · filter_upwards with n; filter_upwards with x
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            by_cases hx : -(n:ℝ) ≤ φ x
            · have h1 : max (φ x) (-(n:ℝ)) = φ x := le_antisymm (max_le (le_refl _) hx) (le_max_left _ _)
              have hle : min (max (φ x) (-(n:ℝ))) (n:ℝ) ≤ φ x := by rw [h1]; exact min_le_left _ _
              calc Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ)))
                  ≤ Real.exp (ζ * φ x) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle (le_of_lt hζ))
                _ ≤ Real.exp (ζ * φ x) + 1 := le_add_of_nonneg_right zero_le_one
            · push_neg at hx
              have h1 : max (φ x) (-(n:ℝ)) = -(n:ℝ) := le_antisymm (max_le (le_of_lt hx) (le_refl _)) (le_max_right _ _)
              have heq : min (max (φ x) (-(n:ℝ))) (n:ℝ) = -(n:ℝ) := by
                rw [h1]
                have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
                exact min_eq_left (by linarith)
              rw [heq]
              have hexp : Real.exp (ζ * -(n:ℝ)) ≤ 1 := by
                rw [← Real.exp_zero, show ζ * -(n:ℝ) = -(ζ * (n:ℝ)) from mul_neg ζ (n:ℝ)]
                exact Real.exp_le_exp.mpr (neg_nonpos.mpr (by positivity))
              linarith [Real.exp_pos (ζ * φ x), hexp]
          · exact hExp.add (integrable_const (1:ℝ))
          · filter_upwards with x; exact hexp_pt x
        have hP : (∫ x, Real.exp (ζ * φ x) ∂(μ : Measure Ω)) ≠ 0 := by
          have hnn : 0 ≤ᶠ[ae (μ : Measure Ω)] (fun x => Real.exp (ζ * φ x)) :=
            Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
          have hmeas : Measurable (fun x : Ω => ENNReal.ofReal (Real.exp (ζ * φ x))) :=
            (Real.measurable_exp.comp (measurable_const.mul hφ)).ennreal_ofReal
          have hsupp : 0 < (μ : Measure Ω) (Function.support (fun x : Ω => ENNReal.ofReal (Real.exp (ζ * φ x)))) := by
            rw [show Function.support (fun x : Ω => ENNReal.ofReal (Real.exp (ζ * φ x))) = Set.univ from by
              ext x
              simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
              exact (ENNReal.ofReal_pos.mpr (Real.exp_pos (ζ * φ x))).ne']
            rw [MeasureTheory.measure_univ]
            exact zero_lt_one
          have hlin : 0 < (∫⁻ x, ENNReal.ofReal (Real.exp (ζ * φ x)) ∂(μ : Measure Ω)) :=
            (MeasureTheory.lintegral_pos_iff_support hmeas).mpr hsupp
          have hfin : (∫⁻ x, ENNReal.ofReal (Real.exp (ζ * φ x)) ∂(μ : Measure Ω)) ≠ ⊤ := by
            have hlt : (∫⁻ x, ‖Real.exp (ζ * φ x)‖ₑ ∂(μ : Measure Ω)) < ⊤ := hExp.2
            rw [show (∫⁻ x, ENNReal.ofReal (Real.exp (ζ * φ x)) ∂(μ : Measure Ω))
                = ∫⁻ x, ‖Real.exp (ζ * φ x)‖ₑ ∂(μ : Measure Ω) from by
              apply MeasureTheory.lintegral_congr
              intro x
              exact (Real.enorm_eq_ofReal (Real.exp_pos _).le).symm]
            exact ne_of_lt hlt
          rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg hnn hExp]
          exact ne_of_gt (ENNReal.toReal_pos hlin.ne' hfin)
        have hlogt : Filter.Tendsto
            (fun n : ℕ => Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω)))
            Filter.atTop (nhds lr) := by
          have h := (Real.continuousAt_log hP).tendsto.comp hDCT
          simpa [hlr] using h
        have hcoe : ∀ (x : NNReal), ENNReal.toEReal (↑x : ENNReal) = ((x : ℝ) : EReal) := by
          intro x; norm_cast
        have hbr : ∀ (a : ENNReal), a ≠ ⊤ → ENNReal.toEReal a = ((a.toReal : ℝ) : EReal) := by
          intro a ha
          have hRN : a.toReal = ((a.toNNReal : NNReal) : ℝ) := by
            conv_lhs => rw [← ENNReal.coe_toNNReal ha]
            exact ENNReal.coe_toReal a.toNNReal
          rw [hRN]
          conv_lhs => rw [← ENNReal.coe_toNNReal ha]
          exact hcoe a.toNNReal
        have hu : Filter.Tendsto
            (fun n : ℕ => ζ⁻¹ * (kd.toReal + Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω))))
            Filter.atTop (nhds (ζ⁻¹ * (kd.toReal + lr))) := by
          have h1 : Filter.Tendsto (fun n : ℕ => kd.toReal + Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω))) Filter.atTop (nhds (kd.toReal + lr)) :=
            Filter.Tendsto.const_add kd.toReal hlogt
          exact Filter.Tendsto.const_mul ζ⁻¹ h1
        have hA : Filter.Tendsto
            (fun n : ℕ => ((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω)) : EReal)))
            Filter.atTop (nhds (((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (lr : EReal)))) := by
          have hfuneq : (fun n : ℕ => ((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω)) : EReal)))
              = (fun n : ℕ => (((ζ⁻¹ * (kd.toReal + Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω)))) : ℝ) : EReal)) := by
            funext n
            rw [hbr kd hktop, ← EReal.coe_add, ← EReal.coe_mul]
          rw [hfuneq]
          rw [show (((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (lr : EReal))) = (((ζ⁻¹ * (kd.toReal + lr)) : ℝ) : EReal) from by
            rw [hbr kd hktop, ← EReal.coe_add, ← EReal.coe_mul]]
          exact hcoetend (fun n : ℕ => ζ⁻¹ * (kd.toReal + Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω)))) (ζ⁻¹ * (kd.toReal + lr)) hu
        have hB : Filter.Tendsto
            (fun n : ℕ => ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)))
            Filter.atTop (nhds (ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω)))) := by
          have hchild := statopia_math_node_1098378036_6924b604 Ω ν (fun x => -(φ x)) hφ.neg
          have hfun : (fun n : ℕ => ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)))
              = (fun n : ℕ => ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (min (max (-(φ x)) (-(n:ℝ))) (n:ℝ)) ∂(ν : Measure Ω))) := by
            funext n
            apply congrArg ENNReal.toEReal
            apply MeasureTheory.lintegral_congr
            intro x
            rw [show -(min (max (φ x) (-(n:ℝ))) (n:ℝ)) = min (max (-(φ x)) (-(n:ℝ))) (n:ℝ) from by
              have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
              by_cases h1 : φ x ≤ -(n:ℝ)
              · rw [max_eq_right h1, min_eq_left (by linarith), max_eq_left (by linarith), min_eq_right (by linarith)]; ring
              · by_cases h2 : (n:ℝ) ≤ φ x
                · rw [max_eq_left (by linarith), min_eq_right h2, max_eq_right (by linarith), min_eq_left (by linarith)]
                · push_neg at h1 h2
                  rw [max_eq_left (by linarith), min_eq_left (le_of_lt h2), max_eq_left (by linarith), min_eq_left (by linarith)]]
          rw [hfun]
          exact hchild
        have hclamp_ub : ∀ (n : ℕ) (x : Ω), -(min (max (φ x) (-(n:ℝ))) (n:ℝ)) ≤ (n:ℝ) := by
          intro n x
          have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
          have h1 : -(n:ℝ) ≤ min (max (φ x) (-(n:ℝ))) (n:ℝ) := le_min (le_max_right _ _) (by linarith)
          linarith
        have hlint_ne : ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)) ≠ ⊤ := by
          intro n
          have hle : (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)) ≤ ENNReal.ofReal (n:ℝ) := by
            calc (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω))
                ≤ ∫⁻ x, ENNReal.ofReal (n:ℝ) ∂(ν : Measure Ω) :=
                  MeasureTheory.lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hclamp_ub n x))
              _ = ENNReal.ofReal (n:ℝ) := by rw [MeasureTheory.lintegral_const]; simp
          exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
        have hfun_eq : (fun n : ℕ => ((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω)) : EReal)) + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)))
            = (fun n : ℕ => (((ζ⁻¹ * (kd.toReal + Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω)))) + (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)).toReal : ℝ) : EReal)) := by
          funext n
          rw [hbr kd hktop, hbr _ (hlint_ne n), ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add]
        rw [hfun_eq]
        by_cases htopL : (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω)) = ⊤
        · have hTtop : (((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (lr : EReal)) + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω))) = ⊤ := by
            rw [show ((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (lr : EReal)) = ((ζ⁻¹ * (kd.toReal + lr) : ℝ) : EReal) from by
              rw [hbr kd hktop, ← EReal.coe_add, ← EReal.coe_mul]]
            rw [htopL, show ENNReal.toEReal (⊤ : ENNReal) = ⊤ from by simp [ENNReal.toEReal]]
            exact EReal.coe_add_top (ζ⁻¹ * (kd.toReal + lr))
          rw [hTtop]
          have hconv : Filter.Tendsto (fun n : ℕ => (↑((∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)).toReal) : EReal)) Filter.atTop (nhds ⊤) := by
            have e1 : (fun n : ℕ => ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω))) = (fun n : ℕ => (↑((∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)).toReal) : EReal)) := by
              funext n; exact hbr _ (hlint_ne n)
            have h := hB
            rw [e1] at h
            rwa [show ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω)) = ⊤ from by rw [htopL, show ENNReal.toEReal (⊤ : ENNReal) = ⊤ from by simp [ENNReal.toEReal]]] at h
          have hconv' := hconv
          rw [tendsto_order] at hconv'
          rw [tendsto_order]
          refine ⟨fun b hb => ?_, fun b hb => ?_⟩
          · by_cases hbot : b = ⊥
            · rw [hbot]; exact Filter.Eventually.of_forall (fun n => EReal.bot_lt_coe _)
            · have htp : b ≠ ⊤ := fun h => by rw [h] at hb; exact absurd hb (not_lt.mpr le_top)
              lift b to ℝ using ⟨htp, hbot⟩
              have hbv : ∀ᶠ (n : ℕ) in Filter.atTop, b - (ζ⁻¹ * (kd.toReal + lr) - 1) < (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)).toReal := by
                have h1 := hconv'.1 (↑(b - (ζ⁻¹ * (kd.toReal + lr) - 1)) : EReal) (EReal.coe_lt_top _)
                filter_upwards [h1] with n hn
                exact_mod_cast hn
              have huv : ∀ᶠ (n : ℕ) in Filter.atTop, ζ⁻¹ * (kd.toReal + lr) - 1 < ζ⁻¹ * (kd.toReal + Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω))) :=
                hu.eventually (Ioi_mem_nhds (show ζ⁻¹ * (kd.toReal + lr) - 1 < ζ⁻¹ * (kd.toReal + lr) from by linarith))
              filter_upwards [hbv, huv] with n h1 h2
              have hbw : b < ζ⁻¹ * (kd.toReal + Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω))) + (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)).toReal := by linarith
              exact_mod_cast hbw
          · exact absurd hb (not_lt.mpr le_top)
        · rw [show (((ζ⁻¹ : ℝ) : EReal) * (ENNReal.toEReal kd + (lr : EReal)) + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω)))
              = (((ζ⁻¹ * (kd.toReal + lr) + (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω)).toReal) : ℝ) : EReal) from by
            rw [hbr kd hktop, hbr _ htopL, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add]]
          have hB'' : Filter.Tendsto (fun n : ℕ => (↑((∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)).toReal) : EReal)) Filter.atTop (nhds (↑((∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω)).toReal) : EReal)) := by
            have e1 : (fun n : ℕ => ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω))) = (fun n : ℕ => (↑((∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)).toReal) : EReal)) := by
              funext n; exact hbr _ (hlint_ne n)
            have h := hB
            rw [e1] at h
            rwa [hbr _ htopL] at h
          have hbn : Filter.Tendsto (fun n : ℕ => (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)).toReal) Filter.atTop (nhds ((∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω)).toReal)) := by
            have ho := hB''
            rw [tendsto_order] at ho
            rw [tendsto_order]
            refine ⟨fun c hc => ?_, fun c hc => ?_⟩
            · filter_upwards [ho.1 (↑c) (by exact_mod_cast hc)] with n hn
              exact_mod_cast hn
            · filter_upwards [ho.2 (↑c) (by exact_mod_cast hc)] with n hn
              exact_mod_cast hn
          exact hcoetend (fun n : ℕ => ζ⁻¹ * (kd.toReal + Real.log (∫ x, Real.exp (ζ * (min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(μ : Measure Ω))) + (∫⁻ x, ENNReal.ofReal (-(min (max (φ x) (-(n:ℝ))) (n:ℝ))) ∂(ν : Measure Ω)).toReal) (ζ⁻¹ * (kd.toReal + lr) + (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(ν : Measure Ω)).toReal) (hu.add hbn)
      exact le_of_tendsto_of_tendsto' hL hR key
  exact hmain
  /- @proof-region region.target-node.session.f33eb3fadf0e17a6 end -/

end
end Statlib.Imported
