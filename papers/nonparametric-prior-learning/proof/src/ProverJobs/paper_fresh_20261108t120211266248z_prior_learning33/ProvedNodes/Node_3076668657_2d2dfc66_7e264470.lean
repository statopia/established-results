import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1218121120_7255afae_cddb3a58

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
theorem statopia_math_node_3076668657_2d2dfc66 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc_pos : ∀ k : ℕ, 0 < c k)
    (mu nu : Measure U) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (m_mu m_nu : U)
    (hmap_mu : ∀ n : ℕ,
      MeasureTheory.Measure.map (fun u : U => fun i : Fin n => inner ℝ (e i) u) mu
        = MeasureTheory.Measure.pi
            (fun i : Fin n =>
              ProbabilityTheory.gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩))
    (hsigma2 : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2))
    (hlim : ∀ᵐ u ∂mu, ∃ L : ℝ,
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu)) atTop (𝓝 L))
    (hcyl : ∀ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C →
      nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C)
        = ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
            ENNReal.ofReal
              (Real.exp
                ((∑ k ∈ Finset.range n,
                    (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
                  - (∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)
                      / 2)) ∂mu), nu = mu.withDensity (fun u : U =>
      ENNReal.ofReal
        (Real.exp
          ((Filter.limsup
              (fun n : ℕ => ∑ k ∈ Finset.range n,
                (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
              Filter.atTop)
            - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2))) := by
  /- @proof-region region.target-node.session.a2498d564cb3e5bf begin -/
  classical
  intro U _ _ _ _ _ _ e c hc_pos mu nu _ _ m_mu m_nu hmap_mu hsigma2 hlim hcyl
  let P : (n : ℕ) → U → (Fin n → ℝ) := fun n u i => inner ℝ (e i) u
  let b : ℕ → ℝ := fun k => inner ℝ (e k) (m_nu - m_mu)
  let a : ℕ → ℝ := fun k => (c k)⁻¹ * b k
  let X : ℕ → U → ℝ := fun k u => inner ℝ (e k) (u - m_mu)
  let Sn : ℕ → U → ℝ := fun n u => ∑ k ∈ Finset.range n, a k * X k u
  let s2n : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, (c k)⁻¹ * (b k) ^ 2
  let s2 : ℝ := ∑' k : ℕ, (c k)⁻¹ * (b k) ^ 2
  let fn : ℕ → U → ℝ := fun n u => Real.exp (Sn n u - s2n n / 2)
  let f : U → ℝ := fun u => Real.exp (limsup (fun n => Sn n u) atTop - s2 / 2)
  have hfn_pos : ∀ (n : ℕ) (u : U), 0 < fn n u := fun n u => Real.exp_pos _
  have hcyl' : ∀ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C →
      nu (P n ⁻¹' C) = ∫⁻ u in (P n ⁻¹' C), ENNReal.ofReal (fn n u) ∂mu :=
    fun n C hC => hcyl n C hC
  have hInt1 : ∀ n : ℕ, ∫⁻ u, ENNReal.ofReal (fn n u) ∂mu = 1 := by
    intro n
    simpa using (hcyl' n Set.univ MeasurableSet.univ).symm
  have hs2 : Tendsto s2n atTop (𝓝 s2) := hsigma2.hasSum.tendsto_sum_nat
  have hSn_cont : ∀ n : ℕ, Continuous (Sn n) := by
    intro n
    refine continuous_finset_sum _ ?_
    intro k _
    exact continuous_const.mul (continuous_const.inner (continuous_id.sub continuous_const))
  have hfn_cont : ∀ n : ℕ, Continuous (fn n) := by
    intro n
    exact Real.continuous_exp.comp ((hSn_cont n).sub continuous_const)
  have hfn_meas : ∀ n : ℕ, Measurable (fun u : U => ENNReal.ofReal (fn n u)) := by
    intro n
    exact (hfn_cont n).measurable.ennreal_ofReal
  have hconv : ∀ᵐ u ∂mu, Tendsto (fun n : ℕ => fn n u) atTop (𝓝 (f u)) := by
    filter_upwards [hlim] with u hu
    obtain ⟨L, hL⟩ := hu
    have hlimsup : limsup (fun n => Sn n u) atTop = L := hL.limsup_eq
    have h1 : Tendsto (fun n => Sn n u - s2n n / 2) atTop (𝓝 (L - s2 / 2)) :=
      hL.sub (hs2.div_const 2)
    have h3 : Tendsto (fun n => Real.exp (Sn n u - s2n n / 2)) atTop
        (𝓝 (Real.exp (limsup (fun n => Sn n u) atTop - s2 / 2))) := by
      have h4 := (Real.continuous_exp.tendsto (L - s2 / 2)).comp h1
      rwa [← hlimsup] at h4
    exact h3
  have hkey : nu = mu.withDensity (fun u => ENNReal.ofReal (f u)) := by
    have hpoint : ∀ (n : ℕ) (u : U), (fn n u) ^ 2
        = ∏ i : Fin n,
            Real.exp (2 * a i * (inner ℝ (e i) u - inner ℝ (e i) m_mu)
              - (c i)⁻¹ * (b i) ^ 2) := by
      intro n u
      have hA : (fn n u) ^ 2 = Real.exp (2 * Sn n u - s2n n) := by
        rw [show fn n u = Real.exp (Sn n u - s2n n / 2) from rfl, sq, ← Real.exp_add]
        congr 1
        ring
      have harg : 2 * Sn n u - s2n n
          = ∑ i : Fin n,
              (2 * a i * (inner ℝ (e i) u - inner ℝ (e i) m_mu) - (c i)⁻¹ * (b i) ^ 2) := by
        rw [Fin.sum_univ_eq_sum_range
          (fun k : ℕ => 2 * a k * (inner ℝ (e k) u - inner ℝ (e k) m_mu)
            - (c k)⁻¹ * (b k) ^ 2) n]
        simp only [Sn, s2n]
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [← inner_sub_right]
        ring
      rw [hA, harg, Real.exp_sum]
    let gfac : (n : ℕ) → (i : Fin n) → ℝ → ℝ :=
      fun n i y => Real.exp (2 * a i * (y - inner ℝ (e i) m_mu) - (c i)⁻¹ * (b i) ^ 2)
    have hPmeas : ∀ n : ℕ, Measurable (P n) := by
      intro n
      have hcont : Continuous (P n) := by
        refine continuous_pi ?_
        intro i
        exact continuous_const.inner continuous_id
      exact hcont.measurable
    have hgfac_cont : ∀ (n : ℕ) (i : Fin n), Continuous (gfac n i) := by
      intro n i
      exact Real.continuous_exp.comp
        ((continuous_const.mul (continuous_id.sub continuous_const)).sub continuous_const)
    have hFsm : ∀ n : ℕ,
        StronglyMeasurable fun y : (Fin n → ℝ) => ∏ i : Fin n, gfac n i (y i) := by
      intro n
      have hcont : Continuous fun y : (Fin n → ℝ) => ∏ i : Fin n, gfac n i (y i) := by
        apply continuous_finset_prod
        intro i _
        exact (hgfac_cont n i).comp (continuous_apply i)
      exact hcont.stronglyMeasurable
    have hfac : ∀ (n : ℕ) (i : Fin n),
        ∫ y, gfac n i y ∂(gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩)
          = Real.exp ((c i)⁻¹ * (b i) ^ 2) := by
      intro n i
      have hcoe : ((⟨c i, le_of_lt (hc_pos i)⟩ : NNReal) : ℝ) = c i := rfl
      have hmgf : ∀ t : ℝ,
          ∫ y, Real.exp (t * y) ∂(gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩)
            = Real.exp (inner ℝ (e i) m_mu * t + c i * t ^ 2 / 2) := by
        intro t
        have hmgf_eq : ProbabilityTheory.mgf id
            (gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩)
            = fun t => Real.exp (inner ℝ (e i) m_mu * t
                + (⟨c i, le_of_lt (hc_pos i)⟩ : NNReal) * t ^ 2 / 2) :=
          ProbabilityTheory.mgf_id_gaussianReal
        have h := congrFun hmgf_eq t
        simpa [ProbabilityTheory.mgf, hcoe] using h
      have hsplit : ∀ y : ℝ,
          Real.exp (2 * a i * (y - inner ℝ (e i) m_mu) - (c i)⁻¹ * (b i) ^ 2)
            = Real.exp (-((2 * a i) * inner ℝ (e i) m_mu) - (c i)⁻¹ * (b i) ^ 2)
              * Real.exp ((2 * a i) * y) := by
        intro y
        rw [← Real.exp_add]
        congr 1
        ring
      calc ∫ y, gfac n i y ∂(gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩)
          = ∫ y, Real.exp (-((2 * a i) * inner ℝ (e i) m_mu) - (c i)⁻¹ * (b i) ^ 2)
              * Real.exp ((2 * a i) * y)
              ∂(gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩) :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit)
        _ = Real.exp (-((2 * a i) * inner ℝ (e i) m_mu) - (c i)⁻¹ * (b i) ^ 2)
              * ∫ y, Real.exp ((2 * a i) * y)
                  ∂(gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩) :=
            MeasureTheory.integral_const_mul _ _
        _ = Real.exp ((c i)⁻¹ * (b i) ^ 2) := by
            rw [hmgf (2 * a i), ← Real.exp_add]
            congr 1
            have hc : c i ≠ 0 := ne_of_gt (hc_pos i)
            simp only [a]
            field_simp
            ring
    have hL2real : ∀ n : ℕ, ∫ u, (fn n u) ^ 2 ∂mu = Real.exp (s2n n) := by
      intro n
      calc ∫ u, (fn n u) ^ 2 ∂mu
          = ∫ u, (∏ i : Fin n, gfac n i ((P n u) i)) ∂mu :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => hpoint n u)
        _ = ∫ y, (∏ i : Fin n, gfac n i (y i)) ∂(Measure.map (P n) mu) :=
            (MeasureTheory.integral_map_of_stronglyMeasurable (hPmeas n) (hFsm n)).symm
        _ = ∫ y, (∏ i : Fin n, gfac n i (y i))
              ∂(Measure.pi (fun i : Fin n =>
                gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩)) := by
            rw [hmap_mu n]
        _ = ∏ i : Fin n,
              ∫ y, gfac n i y ∂(gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩) :=
            MeasureTheory.integral_fin_nat_prod_eq_prod
              (μ := fun i : Fin n => gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩)
              (f := fun i => gfac n i)
        _ = ∏ i : Fin n, Real.exp ((c i)⁻¹ * (b i) ^ 2) :=
            Finset.prod_congr rfl fun i _ => hfac n i
        _ = Real.exp (s2n n) := by
            rw [← Real.exp_sum]
            congr 1
            rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (c k)⁻¹ * (b k) ^ 2) n]
    have hterm_nonneg : ∀ k : ℕ, 0 ≤ (c k)⁻¹ * (b k) ^ 2 :=
      fun k => mul_nonneg (inv_nonneg.2 (le_of_lt (hc_pos k))) (sq_nonneg _)
    have hint2 : ∀ n : ℕ, Integrable (fun u => (fn n u) ^ 2) mu := by
      intro n
      by_contra h
      have h0 : ∫ u, (fn n u) ^ 2 ∂mu = 0 := MeasureTheory.integral_undef h
      rw [hL2real n] at h0
      exact Real.exp_ne_zero _ h0
    have hL2 : ∀ n : ℕ,
        ∫⁻ u, (ENNReal.ofReal (fn n u)) ^ 2 ∂mu = ENNReal.ofReal (Real.exp (s2n n)) := by
      intro n
      have h1 : ENNReal.ofReal (∫ u, (fn n u) ^ 2 ∂mu)
          = ∫⁻ u, ENNReal.ofReal ((fn n u) ^ 2) ∂mu :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint2 n)
          (Filter.Eventually.of_forall fun u => sq_nonneg (fn n u))
      rw [hL2real n] at h1
      rw [h1]
      exact lintegral_congr fun u => (ENNReal.ofReal_pow (le_of_lt (hfn_pos n u)) 2).symm
    have hs2n_le : ∀ n : ℕ, s2n n ≤ s2 := by
      intro n
      have h := hsigma2.sum_le_tsum (Finset.range n) (fun i _ => hterm_nonneg i)
      simpa [s2n, s2] using h
    have hL2le : ∀ n : ℕ,
        ∫⁻ u, (ENNReal.ofReal (fn n u)) ^ 2 ∂mu ≤ ENNReal.ofReal (Real.exp s2) := by
      intro n
      rw [hL2 n]
      exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt (Real.exp_pos s2))).mpr
        (Real.exp_le_exp.mpr (hs2n_le n))
    have hnest : ∀ (n m : ℕ) (hnm : n ≤ m) (C : Set (Fin n → ℝ)),
        P n ⁻¹' C = P m ⁻¹' ((fun y : Fin m → ℝ => fun i : Fin n =>
          y ⟨i, lt_of_lt_of_le i.isLt hnm⟩) ⁻¹' C) := by
      intro n m hnm C
      rfl
    have hcyl_m : ∀ (n m : ℕ) (hnm : n ≤ m) (C : Set (Fin n → ℝ)), MeasurableSet C →
        ∫⁻ u in (P n ⁻¹' C), ENNReal.ofReal (fn m u) ∂mu = nu (P n ⁻¹' C) := by
      intro n m hnm C hC
      have hΦ : Measurable fun y : Fin m → ℝ => fun i : Fin n =>
          y ⟨i, lt_of_lt_of_le i.isLt hnm⟩ := by
        refine (continuous_pi ?_).measurable
        intro i
        exact continuous_apply (⟨i, lt_of_lt_of_le i.isLt hnm⟩ : Fin m)
      have key := hcyl m ((fun y : Fin m → ℝ => fun i : Fin n =>
          y ⟨i, lt_of_lt_of_le i.isLt hnm⟩) ⁻¹' C) (hC.preimage hΦ)
      rw [hnest n m hnm C]
      exact key.symm
    have hgmin_cont : ∀ (n M : ℕ), Continuous fun u : U => min (fn n u) (M:ℝ) :=
      fun n M => (hfn_cont n).min continuous_const
    have hgmin_int : ∀ (n M : ℕ), Integrable (fun u : U => min (fn n u) (M:ℝ)) mu := by
      intro n M
      refine (MeasureTheory.integrable_const (M:ℝ)).mono'
        (((hgmin_cont n M).stronglyMeasurable).aestronglyMeasurable) ?_
      filter_upwards with u
      have h1 : (0:ℝ) ≤ min (fn n u) (M:ℝ) := le_min (hfn_pos n u).le (Nat.cast_nonneg M)
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact min_le_right _ _
    have hminf_aesm : ∀ M : ℕ, AEStronglyMeasurable (fun u : U => min (f u) (M:ℝ)) mu := by
      intro M
      exact aestronglyMeasurable_of_tendsto_ae (μ := mu) (ι := ℕ)
        (f := fun n (u : U) => min (fn n u) (M:ℝ))
        (g := fun u : U => min (f u) (M:ℝ)) atTop
        (fun n => ((hgmin_cont n M).stronglyMeasurable).aestronglyMeasurable)
        (by
          filter_upwards [hconv] with u hu
          exact hu.min tendsto_const_nhds)
    have hminf_int : ∀ M : ℕ, Integrable (fun u : U => min (f u) (M:ℝ)) mu := by
      intro M
      refine (MeasureTheory.integrable_const (M:ℝ)).mono' (hminf_aesm M) ?_
      filter_upwards with u
      have h1 : (0:ℝ) ≤ min (f u) (M:ℝ) := le_min (Real.exp_pos _).le (Nat.cast_nonneg M)
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact min_le_right _ _
    have hconv_min : ∀ M : ℕ,
        ENNReal.ofReal (∫ u, min (f u) (M:ℝ) ∂mu)
          = ∫⁻ u, ENNReal.ofReal (min (f u) (M:ℝ)) ∂mu := by
      intro M
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hminf_int M)
        (Filter.Eventually.of_forall fun u => le_min (Real.exp_pos _).le (Nat.cast_nonneg M))
    have hfn_int : ∀ n : ℕ, Integrable (fn n) mu := by
      intro n
      have hb : Integrable (fun u : U => (fn n u) ^ 2 + 1) mu :=
        (hint2 n).add (MeasureTheory.integrable_const (1:ℝ))
      refine hb.mono' (((hfn_cont n).stronglyMeasurable).aestronglyMeasurable) ?_
      filter_upwards with u
      have hp : (0:ℝ) < fn n u := hfn_pos n u
      have hle : fn n u ≤ (fn n u) ^ 2 + 1 := by nlinarith [sq_nonneg (fn n u - 1)]
      rw [Real.norm_eq_abs, abs_of_pos hp]
      exact hle
    have hInt1R : ∀ n : ℕ, ∫ u, fn n u ∂mu = 1 := by
      intro n
      have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfn_int n)
        (Filter.Eventually.of_forall fun u => (hfn_pos n u).le)
      rw [hInt1 n] at h
      have hnn : (0:ℝ) ≤ ∫ u, fn n u ∂mu := integral_nonneg fun u => (hfn_pos n u).le
      exact (ENNReal.ofReal_eq_ofReal_iff hnn zero_le_one).mp (by simpa using h)
    have hf_aesm : AEStronglyMeasurable f mu :=
      aestronglyMeasurable_of_tendsto_ae (μ := mu) (ι := ℕ) (f := fn) (g := f) atTop
        (fun n => ((hfn_cont n).stronglyMeasurable).aestronglyMeasurable) hconv
    have hdeficit : ∀ (n M : ℕ), 1 ≤ M →
        ∫ u, (fn n u - min (fn n u) (M:ℝ)) ∂mu ≤ Real.exp s2 * (M:ℝ)⁻¹ := by
      intro n M hM
      have hMpos : (0:ℝ) < (M:ℝ) := by
        have h1 : (0:ℕ) < M := lt_of_lt_of_le Nat.zero_lt_one hM
        exact_mod_cast h1
      have hle : ∫ u, (fn n u - min (fn n u) (M:ℝ)) ∂mu
          ≤ ∫ u, (fn n u) ^ 2 * (M:ℝ)⁻¹ ∂mu := by
        refine integral_mono ((hfn_int n).sub (hgmin_int n M)) ((hint2 n).mul_const _) ?_
        intro u
        dsimp only
        have hp : (0:ℝ) < fn n u := hfn_pos n u
        rcases le_total (fn n u) (M:ℝ) with hc | hc
        · rw [min_eq_left hc, sub_self]
          exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hMpos.le)
        · rw [min_eq_right hc, ← sub_nonneg]
          have hfac : (fn n u) ^ 2 * (M:ℝ)⁻¹ - (fn n u - (M:ℝ))
              = ((fn n u - (M:ℝ)) ^ 2 + fn n u * (M:ℝ)) * (M:ℝ)⁻¹ := by
            have hcne : (M:ℝ) ≠ 0 := ne_of_gt hMpos
            field_simp
            ring
          rw [hfac]
          exact mul_nonneg (by positivity) (inv_nonneg.mpr hMpos.le)
      have h2 : ∫ u, (fn n u) ^ 2 * (M:ℝ)⁻¹ ∂mu = Real.exp (s2n n) * (M:ℝ)⁻¹ := by
        rw [MeasureTheory.integral_mul_const, hL2real n]
      rw [h2] at hle
      refine hle.trans ?_
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hs2n_le n))
        (inv_nonneg.mpr hMpos.le)
    have hdc : ∀ M : ℕ, Tendsto (fun n : ℕ => ∫ u, min (fn n u) (M:ℝ) ∂mu) atTop
        (𝓝 (∫ u, min (f u) (M:ℝ) ∂mu)) := by
      intro M
      refine MeasureTheory.tendsto_integral_of_dominated_convergence (μ := mu)
        (F := fun n (u : U) => min (fn n u) (M:ℝ))
        (f := fun u : U => min (f u) (M:ℝ)) (fun _ : U => (M:ℝ)) ?_ ?_ ?_ ?_
      · exact fun n => ((hgmin_cont n M).stronglyMeasurable).aestronglyMeasurable
      · exact MeasureTheory.integrable_const (M:ℝ)
      · intro n
        filter_upwards with u
        have h1 : (0:ℝ) ≤ min (fn n u) (M:ℝ) := le_min (hfn_pos n u).le (Nat.cast_nonneg M)
        rw [Real.norm_eq_abs, abs_of_nonneg h1]
        exact min_le_right _ _
      · filter_upwards [hconv] with u hu
        exact hu.min tendsto_const_nhds
    have hub : ∀ M : ℕ, ∫ u, min (f u) (M:ℝ) ∂mu ≤ 1 := by
      intro M
      have hstep : ∀ n : ℕ, ∫ u, min (fn n u) (M:ℝ) ∂mu ≤ 1 := by
        intro n
        calc ∫ u, min (fn n u) (M:ℝ) ∂mu ≤ ∫ u, fn n u ∂mu :=
              integral_mono (hgmin_int n M) (hfn_int n) (fun u => min_le_left _ _)
          _ = 1 := hInt1R n
      by_contra hcon
      push_neg at hcon
      have hmem : Set.Ioi (1:ℝ) ∈ 𝓝 (∫ u, min (f u) (M:ℝ) ∂mu) :=
        isOpen_Ioi.mem_nhds hcon
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((hdc M).eventually hmem)
      exact absurd (hN N le_rfl) (not_lt.mpr (hstep N))
    have hlb : ∀ M : ℕ, 1 ≤ M →
        1 - Real.exp s2 * (M:ℝ)⁻¹ ≤ ∫ u, min (f u) (M:ℝ) ∂mu := by
      intro M hM
      have hstep : ∀ n : ℕ,
          1 - Real.exp s2 * (M:ℝ)⁻¹ ≤ ∫ u, min (fn n u) (M:ℝ) ∂mu := by
        intro n
        have hsub : ∫ u, (fn n u - min (fn n u) (M:ℝ)) ∂mu
            = ∫ u, fn n u ∂mu - ∫ u, min (fn n u) (M:ℝ) ∂mu :=
          MeasureTheory.integral_sub (hfn_int n) (hgmin_int n M)
        have hd := hdeficit n M hM
        rw [hsub, hInt1R n] at hd
        linarith
      by_contra hcon
      push_neg at hcon
      have hmem : Set.Iio (1 - Real.exp s2 * (M:ℝ)⁻¹) ∈ 𝓝 (∫ u, min (f u) (M:ℝ) ∂mu) :=
        isOpen_Iio.mem_nhds hcon
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((hdc M).eventually hmem)
      exact absurd (hN N le_rfl) (not_lt.mpr (hstep N))






    have hf_meas : Measurable f := by
      have h1 : Measurable fun u : U => limsup (fun n => Sn n u) atTop :=
        Measurable.limsup (fun n => (hSn_cont n).measurable)
      exact Real.continuous_exp.measurable.comp (h1.sub measurable_const)
    have hMmeas : ∀ M : ℕ, Measurable (fun u : U => ENNReal.ofReal (min (f u) (M:ℝ))) := by
      intro M
      exact ENNReal.measurable_ofReal.comp (hf_meas.min measurable_const)
    have hmono : Monotone (fun M : ℕ => fun u : U => ENNReal.ofReal (min (f u) (M:ℝ))) := by
      intro M N hMN u
      exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hMN))
    have hMCT : ∫⁻ u, (⨆ M : ℕ, ENNReal.ofReal (min (f u) (M:ℝ))) ∂mu
        = ⨆ M : ℕ, ∫⁻ u, ENNReal.ofReal (min (f u) (M:ℝ)) ∂mu :=
      MeasureTheory.lintegral_iSup hMmeas hmono
    have hsup : ∀ u : U,
        (⨆ M : ℕ, ENNReal.ofReal (min (f u) (M:ℝ))) = ENNReal.ofReal (f u) := by
      intro u
      refine le_antisymm (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
      obtain ⟨K, hK⟩ := exists_nat_gt (f u)
      calc ENNReal.ofReal (f u) = ENNReal.ofReal (min (f u) (K:ℝ)) := by rw [min_eq_left hK.le]
        _ ≤ ⨆ M : ℕ, ENNReal.ofReal (min (f u) (M:ℝ)) :=
          le_iSup (fun M : ℕ => ENNReal.ofReal (min (f u) (M:ℝ))) K
    have hIntf : ∫⁻ u, ENNReal.ofReal (f u) ∂mu = 1 := by
      set bs : ENNReal := ⨆ M : ℕ, ENNReal.ofReal (∫ u, min (f u) (M:ℝ) ∂mu) with hbs
      have heq : ∫⁻ u, ENNReal.ofReal (f u) ∂mu = bs := by
        rw [hbs, ← iSup_congr (fun M => (hconv_min M).symm), ← hMCT]
        exact lintegral_congr fun u => (hsup u).symm
      have hbs_le : bs ≤ 1 := by
        rw [hbs]
        refine iSup_le fun M => ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hub M)
      have hbs_ne : bs ≠ ⊤ := by
        intro h
        rw [h, top_le_iff] at hbs_le
        exact absurd hbs_le (ne_of_lt ENNReal.one_lt_top)
      have hlow : ∀ M : ℕ, 1 ≤ M → 1 - Real.exp s2 * (M:ℝ)⁻¹ ≤ bs.toReal := by
        intro M hM
        have h1 : ENNReal.ofReal (∫ u, min (f u) (M:ℝ) ∂mu) ≤ bs := by
          rw [hbs]
          exact le_iSup (fun M : ℕ => ENNReal.ofReal (∫ u, min (f u) (M:ℝ) ∂mu)) M
        have h2 : ∫ u, min (f u) (M:ℝ) ∂mu ≤ bs.toReal :=
          (ENNReal.ofReal_le_iff_le_toReal hbs_ne).mp h1
        linarith [hlb M hM]
      have hone : (1:ℝ) ≤ bs.toReal := by
        by_contra hc
        push_neg at hc
        have hδ : (0:ℝ) < 1 - bs.toReal := by linarith
        obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp s2 / (1 - bs.toReal))
        have hdiv : Real.exp s2 / (1 - bs.toReal) * (1 - bs.toReal) = Real.exp s2 := by
          field_simp
        have hKpos_nat : (0:ℕ) < max K 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right K 1)
        have hKpos : (0:ℝ) < ((max K 1 : ℕ) : ℝ) := by exact_mod_cast hKpos_nat
        have h2 : Real.exp s2 / (1 - bs.toReal) < ((max K 1 : ℕ) : ℝ) :=
          lt_of_lt_of_le hK (Nat.cast_le.mpr (le_max_left K 1))
        have hKlt : Real.exp s2 < ((max K 1 : ℕ) : ℝ) * (1 - bs.toReal) := by
          have h3 := mul_lt_mul_of_pos_right h2 hδ
          rwa [hdiv] at h3
        have hsmall : Real.exp s2 * ((max K 1 : ℕ) : ℝ)⁻¹ < 1 - bs.toReal := by
          have h4 := mul_lt_mul_of_pos_right hKlt (inv_pos.mpr hKpos)
          refine h4.trans_eq ?_
          have hne : ((max K 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hKpos
          field_simp
        have hcontra := hlow (max K 1) (le_max_right K 1)
        linarith
      have hbs_ge : (1:ENNReal) ≤ bs := by
        rw [show (1:ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
        exact ENNReal.ofReal_le_of_le_toReal hone
      rw [heq]
      exact le_antisymm hbs_le hbs_ge
    have hcylρ : ∀ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C →
        nu (P n ⁻¹' C) = ∫⁻ u in (P n ⁻¹' C), ENNReal.ofReal (f u) ∂mu := by
      intro n C hC
      set A : Set U := P n ⁻¹' C with hA
      have hAmeas : MeasurableSet A := hC.preimage (hPmeas n)
      have hint : ∀ m : ℕ, n ≤ m →
          ∫⁻ u in A, ENNReal.ofReal (fn m u) ∂mu = nu A := by
        intro m hnm
        exact hcyl_m n m hnm C hC
      have arch : ∀ (c d : ℝ), (∀ M : ℕ, 1 ≤ M → c - Real.exp s2 * (M:ℝ)⁻¹ ≤ d) → c ≤ d := by
        intro c d h
        by_contra hc
        push_neg at hc
        have hδ : (0:ℝ) < c - d := by linarith
        obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp s2 / (c - d))
        have hdiv : Real.exp s2 / (c - d) * (c - d) = Real.exp s2 := by field_simp
        have hKpos_nat : (0:ℕ) < max K 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right K 1)
        have hKpos : (0:ℝ) < ((max K 1 : ℕ) : ℝ) := by exact_mod_cast hKpos_nat
        have h2 : Real.exp s2 / (c - d) < ((max K 1 : ℕ) : ℝ) :=
          lt_of_lt_of_le hK (Nat.cast_le.mpr (le_max_left K 1))
        have hKlt : Real.exp s2 < ((max K 1 : ℕ) : ℝ) * (c - d) := by
          have h3 := mul_lt_mul_of_pos_right h2 hδ
          rwa [hdiv] at h3
        have hsmall : Real.exp s2 * ((max K 1 : ℕ) : ℝ)⁻¹ < c - d := by
          have h4 := mul_lt_mul_of_pos_right hKlt (inv_pos.mpr hKpos)
          refine h4.trans_eq ?_
          have hne : ((max K 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hKpos
          field_simp
        have hcontra := h (max K 1) (le_max_right K 1)
        linarith
      have hAint : ∀ m : ℕ, n ≤ m → ∫ u in A, fn m u ∂mu = (nu A).toReal := by
        intro m hnm
        have hI : Integrable (fn m) (mu.restrict A) :=
          (hfn_int m).mono_measure Measure.restrict_le_self
        have h1 : ENNReal.ofReal (∫ u, fn m u ∂(mu.restrict A))
            = ∫⁻ u, ENNReal.ofReal (fn m u) ∂(mu.restrict A) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI
            (Filter.Eventually.of_forall fun u => (hfn_pos m u).le)
        have h2 : ∫⁻ u, ENNReal.ofReal (fn m u) ∂(mu.restrict A) = nu A := hint m hnm
        rw [h2] at h1
        have h3 : (ENNReal.ofReal (∫ u, fn m u ∂(mu.restrict A))).toReal = (nu A).toReal := by
          rw [h1]
        rwa [ENNReal.toReal_ofReal (integral_nonneg fun u => (hfn_pos m u).le)] at h3
      have hcmA : ∀ M : ℕ, ENNReal.ofReal (∫ u in A, min (f u) (M:ℝ) ∂mu)
          = ∫⁻ u in A, ENNReal.ofReal (min (f u) (M:ℝ)) ∂mu := by
        intro M
        have hI : Integrable (fun u => min (f u) (M:ℝ)) (mu.restrict A) :=
          (hminf_int M).mono_measure Measure.restrict_le_self
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI
          (Filter.Eventually.of_forall fun u => le_min (Real.exp_pos _).le (Nat.cast_nonneg M))
      have hdcA : ∀ M : ℕ, Tendsto (fun m : ℕ => ∫ u in A, min (fn m u) (M:ℝ) ∂mu) atTop
          (𝓝 (∫ u in A, min (f u) (M:ℝ) ∂mu)) := by
        intro M
        refine MeasureTheory.tendsto_integral_of_dominated_convergence (μ := mu.restrict A)
          (F := fun m (u : U) => min (fn m u) (M:ℝ))
          (f := fun u : U => min (f u) (M:ℝ)) (fun _ : U => (M:ℝ)) ?_ ?_ ?_ ?_
        · exact fun m => ((hgmin_cont m M).stronglyMeasurable).aestronglyMeasurable
        · exact MeasureTheory.integrable_const (M:ℝ)
        · intro m
          filter_upwards with u
          have h1 : (0:ℝ) ≤ min (fn m u) (M:ℝ) := le_min (hfn_pos m u).le (Nat.cast_nonneg M)
          rw [Real.norm_eq_abs, abs_of_nonneg h1]
          exact min_le_right _ _
        · filter_upwards [hconv.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)]
            with u hu
          exact hu.min tendsto_const_nhds
      have hubA : ∀ M : ℕ, ∫ u in A, min (f u) (M:ℝ) ∂mu ≤ (nu A).toReal := by
        intro M
        have hstep : ∀ m : ℕ, n ≤ m →
            ∫ u in A, min (fn m u) (M:ℝ) ∂mu ≤ (nu A).toReal := by
          intro m hnm
          calc ∫ u in A, min (fn m u) (M:ℝ) ∂mu ≤ ∫ u in A, fn m u ∂mu :=
                integral_mono ((hgmin_int m M).mono_measure Measure.restrict_le_self)
                  ((hfn_int m).mono_measure Measure.restrict_le_self) (fun u => min_le_left _ _)
            _ = (nu A).toReal := hAint m hnm
        by_contra hcon
        push_neg at hcon
        have hmem : Set.Ioi ((nu A).toReal) ∈ 𝓝 (∫ u in A, min (f u) (M:ℝ) ∂mu) :=
          isOpen_Ioi.mem_nhds hcon
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((hdcA M).eventually hmem)
        exact absurd (hN (max N n) (le_max_left N n))
          (not_lt.mpr (hstep (max N n) (le_max_right N n)))
      have hdefA : ∀ (m M : ℕ), 1 ≤ M →
          ∫ u in A, (fn m u - min (fn m u) (M:ℝ)) ∂mu ≤ Real.exp s2 * (M:ℝ)⁻¹ := by
        intro m M hM
        have hMpos : (0:ℝ) < (M:ℝ) := by
          have h1 : (0:ℕ) < M := lt_of_lt_of_le Nat.zero_lt_one hM
          exact_mod_cast h1
        have hpt : ∀ u : U, A.indicator (fun u : U => fn m u - min (fn m u) (M:ℝ)) u
            ≤ (fn m u) ^ 2 * (M:ℝ)⁻¹ := by
          intro u
          by_cases hu : u ∈ A
          · rw [Set.indicator_of_mem hu]
            rcases le_total (fn m u) (M:ℝ) with hc | hc
            · rw [min_eq_left hc, sub_self]
              exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hMpos.le)
            · rw [min_eq_right hc, ← sub_nonneg]
              have hfac : (fn m u) ^ 2 * (M:ℝ)⁻¹ - (fn m u - (M:ℝ))
                  = ((fn m u - (M:ℝ)) ^ 2 + fn m u * (M:ℝ)) * (M:ℝ)⁻¹ := by
                have hcne : (M:ℝ) ≠ 0 := ne_of_gt hMpos
                field_simp
                ring
              rw [hfac]
              exact mul_nonneg (by positivity) (inv_nonneg.mpr hMpos.le)
          · have hzero : A.indicator (fun u : U => fn m u - min (fn m u) (M:ℝ)) u = 0 := by
              simp only [Set.indicator, hu, if_false]
            rw [hzero]
            exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hMpos.le)
        have hI : Integrable (A.indicator (fun u : U => fn m u - min (fn m u) (M:ℝ))) mu :=
          ((hfn_int m).sub (hgmin_int m M)).indicator hAmeas
        have hmono := integral_mono hI ((hint2 m).mul_const _) hpt
        rw [MeasureTheory.integral_indicator hAmeas] at hmono
        have h2 : ∫ u, (fn m u) ^ 2 * (M:ℝ)⁻¹ ∂mu = Real.exp (s2n m) * (M:ℝ)⁻¹ := by
          rw [MeasureTheory.integral_mul_const, hL2real m]
        rw [h2] at hmono
        exact hmono.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hs2n_le m))
          (inv_nonneg.mpr hMpos.le))
      have hlbA : ∀ M : ℕ, 1 ≤ M →
          (nu A).toReal - Real.exp s2 * (M:ℝ)⁻¹ ≤ ∫ u in A, min (f u) (M:ℝ) ∂mu := by
        intro M hM
        have hstep : ∀ m : ℕ, n ≤ m →
            (nu A).toReal - Real.exp s2 * (M:ℝ)⁻¹ ≤ ∫ u in A, min (fn m u) (M:ℝ) ∂mu := by
          intro m hnm
          have hsub : ∫ u in A, (fn m u - min (fn m u) (M:ℝ)) ∂mu
              = ∫ u in A, fn m u ∂mu - ∫ u in A, min (fn m u) (M:ℝ) ∂mu :=
            MeasureTheory.integral_sub ((hfn_int m).mono_measure Measure.restrict_le_self)
              ((hgmin_int m M).mono_measure Measure.restrict_le_self)
          have hd := hdefA m M hM
          rw [hsub, hAint m hnm] at hd
          linarith
        by_contra hcon
        push_neg at hcon
        have hmem : Set.Iio ((nu A).toReal - Real.exp s2 * (M:ℝ)⁻¹)
            ∈ 𝓝 (∫ u in A, min (f u) (M:ℝ) ∂mu) :=
          isOpen_Iio.mem_nhds hcon
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((hdcA M).eventually hmem)
        exact absurd (hN (max N n) (le_max_left N n))
          (not_lt.mpr (hstep (max N n) (le_max_right N n)))
      have hMCTA : ∫⁻ u, (⨆ M : ℕ, ENNReal.ofReal (min (f u) (M:ℝ))) ∂(mu.restrict A)
          = ⨆ M : ℕ, ∫⁻ u, ENNReal.ofReal (min (f u) (M:ℝ)) ∂(mu.restrict A) :=
        MeasureTheory.lintegral_iSup hMmeas hmono
      have heqA : ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu
          = ⨆ M : ℕ, ENNReal.ofReal (∫ u in A, min (f u) (M:ℝ) ∂mu) := by
        have step1 : ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu
            = ∫⁻ u, (⨆ M : ℕ, ENNReal.ofReal (min (f u) (M:ℝ))) ∂(mu.restrict A) :=
          lintegral_congr fun u => (hsup u).symm
        rw [step1, hMCTA]
        exact (iSup_congr fun M => hcmA M).symm
      have hAle : ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu ≤ nu A := by
        rw [heqA]
        refine iSup_le fun M => ?_
        rw [← ENNReal.ofReal_toReal (measure_ne_top nu A)]
        exact ENNReal.ofReal_le_ofReal (hubA M)
      have hAne : ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu ≠ ⊤ := by
        intro h
        rw [h, top_le_iff] at hAle
        exact measure_ne_top nu A hAle
      have hlowA : ∀ M : ℕ, 1 ≤ M →
          (nu A).toReal - Real.exp s2 * (M:ℝ)⁻¹
            ≤ (∫⁻ u in A, ENNReal.ofReal (f u) ∂mu).toReal := by
        intro M hM
        have h1 : ENNReal.ofReal (∫ u in A, min (f u) (M:ℝ) ∂mu)
            ≤ ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu := by
          rw [hcmA M]
          exact lintegral_mono fun u => ENNReal.ofReal_le_ofReal (min_le_left _ _)
        have h2 : ∫ u in A, min (f u) (M:ℝ) ∂mu
            ≤ (∫⁻ u in A, ENNReal.ofReal (f u) ∂mu).toReal :=
          (ENNReal.ofReal_le_iff_le_toReal hAne).mp h1
        linarith [hlbA M hM]
      have hAge : nu A ≤ ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top nu A)]
        exact ENNReal.ofReal_le_of_le_toReal (arch (nu A).toReal _ hlowA)
      exact le_antisymm hAge hAle
    have hall : ∀ A : Set U, MeasurableSet A →
        nu A = ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu := by
      set Cset : Set (Set U) :=
        {A : Set U | ∃ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C ∧ A = P n ⁻¹' C} with hCset
      have hpi : IsPiSystem Cset := by
        intro s hs t ht
        rw [hCset] at hs ht
        obtain ⟨m, C₁, hC₁, rfl⟩ := hs
        obtain ⟨n, C₂, hC₂, rfl⟩ := ht
        rcases le_total m n with hmn | hnm
        · have hΦ : Measurable fun y : Fin n → ℝ => fun i : Fin m =>
              y ⟨i, lt_of_lt_of_le i.isLt hmn⟩ := by
            refine (continuous_pi ?_).measurable
            intro i
            exact continuous_apply (⟨i, lt_of_lt_of_le i.isLt hmn⟩ : Fin n)
          intro _
          rw [hCset]
          exact ⟨n, ((fun y : Fin n → ℝ => fun i : Fin m =>
              y ⟨i, lt_of_lt_of_le i.isLt hmn⟩) ⁻¹' C₁) ∩ C₂,
            (hC₁.preimage hΦ).inter hC₂, by
              rw [hnest m n hmn C₁, ← Set.preimage_inter]⟩
        · have hΦ : Measurable fun y : Fin m → ℝ => fun i : Fin n =>
              y ⟨i, lt_of_lt_of_le i.isLt hnm⟩ := by
            refine (continuous_pi ?_).measurable
            intro i
            exact continuous_apply (⟨i, lt_of_lt_of_le i.isLt hnm⟩ : Fin m)
          intro _
          rw [hCset]
          exact ⟨m, C₁ ∩ ((fun y : Fin m → ℝ => fun i : Fin n =>
              y ⟨i, lt_of_lt_of_le i.isLt hnm⟩) ⁻¹' C₂),
            hC₁.inter (hC₂.preimage hΦ), by
              rw [hnest n m hnm C₂, ← Set.preimage_inter]⟩
      have hmem_univ : (Set.univ : Set U) ∈ Cset := by
        rw [hCset]
        exact ⟨0, Set.univ, MeasurableSet.univ, by simp⟩
      have hagree : ∀ s ∈ Cset,
          nu s = (mu.withDensity (fun u : U => ENNReal.ofReal (f u))) s := by
        intro s hs
        rw [hCset] at hs
        obtain ⟨n, C, hC, rfl⟩ := hs
        rw [hcylρ n C hC, MeasureTheory.withDensity_apply _ (hC.preimage (hPmeas n))]
      have hgen_le : MeasurableSpace.generateFrom Cset ≤ ‹MeasurableSpace U› := by
        refine MeasurableSpace.generateFrom_le ?_
        intro t ht
        rw [hCset] at ht
        obtain ⟨n, C, hC, rfl⟩ := ht
        exact hC.preimage (hPmeas n)
      have hgen : ‹MeasurableSpace U› = MeasurableSpace.generateFrom Cset :=
        statopia_math_node_1218121120_7255afae U e
      intro A hA
      have hmeq : nu = mu.withDensity (fun u : U => ENNReal.ofReal (f u)) :=
        MeasureTheory.Measure.ext_of_generateFrom_of_iUnion (μ := nu)
          (ν := mu.withDensity fun u : U => ENNReal.ofReal (f u))
          Cset (fun _ : ℕ => (Set.univ : Set U)) hgen hpi (by ext x; simp)
          (fun _ => hmem_univ) (fun _ => measure_ne_top nu Set.univ) hagree
      rw [hmeq, MeasureTheory.withDensity_apply _ hA]
    ext A hA
    rw [hall A hA, MeasureTheory.withDensity_apply _ hA]
  exact hkey
  /- @proof-region region.target-node.session.a2498d564cb3e5bf end -/

end Statlib.Imported
end

