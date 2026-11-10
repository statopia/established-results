import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

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
theorem statopia_math_node_784943557_45aa83b0 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc : ∀ k : ℕ, 0 < c k)
    (μ : Measure U) [IsProbabilityMeasure μ]
    (hmu_gauss : ProbabilityTheory.IsGaussian μ)
    (mUM : U)
    (hmean_mu : ∀ v : U, ∫ u, inner ℝ v u ∂μ = inner ℝ v mUM)
    (hcov_mu : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) * (inner ℝ (e l) u - inner ℝ (e l) mUM) ∂μ
        = if k = l then c k else 0)
    (hint1_mu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2_mu : ∀ v w : U,
      Integrable (fun u : U =>
        (inner ℝ v u - inner ℝ v mUM) * (inner ℝ w u - inner ℝ w mUM)) μ),
    Measure.map (fun u : U => fun k : ℕ => inner ℝ (e k) (u - mUM)) μ
      = Measure.infinitePi (fun k : ℕ => gaussianReal 0 (Real.toNNReal (c k))) := by
  /- @proof-region region.target-node.session.ae43bc3dcf4d3457 begin -/
  intro U _ _ _ _ _ _ e c hc μ _ hmu_gauss mUM hmean_mu hcov_mu hint1_mu hint2_mu
  haveI : ProbabilityTheory.IsGaussian μ := hmu_gauss
  have hreal : ∀ a b : ℝ, inner ℝ a b = a * b := fun a b => by simp [mul_comm]
  have hcontT : ∀ v : U, Continuous fun u : U => inner ℝ v (u - mUM) := fun v => by
    have h1 : Continuous fun u : U => inner ℝ v u := continuous_const.inner continuous_id
    have h2 : Continuous fun u : U => inner ℝ v u - inner ℝ v mUM :=
      h1.sub (continuous_const : Continuous fun _ : U => inner ℝ v mUM)
    simpa only [inner_sub_right] using h2
  have hmarg : ∀ s : Finset ℕ,
      Measure.map (fun u : U => fun i : s => inner ℝ (e i) (u - mUM)) μ
        = Measure.pi (fun i : s => gaussianReal 0 (Real.toNNReal (c i))) := by
    intro s
    have htoLp : Measurable (WithLp.toLp 2 : (s → ℝ) → EuclideanSpace ℝ s) :=
      WithLp.measurable_toLp 2 (s → ℝ)
    have hofLp : Measurable (WithLp.ofLp : EuclideanSpace ℝ s → (s → ℝ)) :=
      WithLp.measurable_ofLp 2 (s → ℝ)
    have hΦrow : Measurable (fun u : U => fun i : s => inner ℝ (e i) (u - mUM)) :=
      measurable_pi_iff.mpr (fun i => (hcontT (e i)).measurable)
    have hΦ : Measurable (fun u : U =>
        (WithLp.toLp 2 (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) :=
      htoLp.comp hΦrow
    have hE : Measure.map (fun u : U =>
          (WithLp.toLp 2 (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) μ
        = Measure.map (WithLp.toLp 2)
            (Measure.pi (fun i : s => gaussianReal 0 (Real.toNNReal (c i)))) := by
      refine Measure.ext_of_charFun (funext fun t => ?_)
      set T : U := ∑ i : s, (t.ofLp i) • e i with hTdef
      have hg : Continuous fun x : EuclideanSpace ℝ s => inner ℝ x t :=
        continuous_id.inner continuous_const
      have hfm : AEStronglyMeasurable
          (fun x : EuclideanSpace ℝ s => Complex.exp (↑(inner ℝ x t) * Complex.I))
          (Measure.map (fun u : U =>
            (WithLp.toLp 2 (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) μ) := by
        have hci : Continuous fun x : EuclideanSpace ℝ s => (↑(inner ℝ x t) : ℂ) * Complex.I :=
          (Complex.continuous_ofReal.comp hg).mul continuous_const
        exact (Complex.continuous_exp.comp hci).measurable.aestronglyMeasurable
      have hpt : ∀ u : U, inner ℝ ((WithLp.toLp 2
            (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) t
          = inner ℝ T u - inner ℝ T mUM := by
        intro u
        have h1 : inner ℝ ((WithLp.toLp 2
              (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) t
            = ∑ i : s, (t.ofLp i) * inner ℝ (e i) (u - mUM) := by
          rw [PiLp.inner_apply]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hreal]
          ring
        have h2 : inner ℝ T (u - mUM) = ∑ i : s, (t.ofLp i) * inner ℝ (e i) (u - mUM) := by
          rw [hTdef, sum_inner]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [real_inner_smul_left]
        rw [h1, ← h2, inner_sub_right]
      have hint : ∀ u : U, Complex.exp (↑(inner ℝ ((WithLp.toLp 2
            (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) t) * Complex.I)
          = Complex.exp (-(↑(inner ℝ T mUM)) * Complex.I)
            * Complex.exp (↑(inner ℝ T u) * Complex.I) := by
        intro u
        have hcast : (↑(inner ℝ ((WithLp.toLp 2
              (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) t) : ℂ)
            = ↑(inner ℝ T u) - ↑(inner ℝ T mUM) := by
          rw [hpt u]
          push_cast
          ring
        rw [hcast]
        rw [show (↑(inner ℝ T u) - ↑(inner ℝ T mUM)) * Complex.I
            = -(↑(inner ℝ T mUM)) * Complex.I + ↑(inner ℝ T u) * Complex.I by ring]
        rw [Complex.exp_add]
      have hchar : charFun μ T = ∫ u : U, Complex.exp (↑(inner ℝ T u) * Complex.I) ∂μ := by
        show (∫ x : U, Complex.exp (↑(inner ℝ x T) * Complex.I) ∂μ) = _
        congr 1
        funext u
        rw [real_inner_comm]
      have hL : charFun (Measure.map (fun u : U =>
            (WithLp.toLp 2 (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) μ) t
          = Complex.exp (-(↑(inner ℝ T mUM)) * Complex.I) * charFun μ T := by
        rw [hchar]
        have h1 : charFun (Measure.map (fun u : U =>
              (WithLp.toLp 2 (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) μ) t
            = ∫ u : U, Complex.exp (↑(inner ℝ ((WithLp.toLp 2
                (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) t) * Complex.I) ∂μ := by
          show (∫ x : EuclideanSpace ℝ s, Complex.exp (↑(inner ℝ x t) * Complex.I) ∂(Measure.map (fun u : U =>
            (WithLp.toLp 2 (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) μ)) = _
          rw [MeasureTheory.integral_map hΦ.aemeasurable hfm]
        rw [h1]
        rw [show (fun u : U => Complex.exp (↑(inner ℝ ((WithLp.toLp 2
              (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) t) * Complex.I))
            = fun u : U => Complex.exp (-(↑(inner ℝ T mUM)) * Complex.I)
              * Complex.exp (↑(inner ℝ T u) * Complex.I) from funext hint]
        rw [integral_const_mul]
      have hR : charFun (Measure.map (WithLp.toLp 2)
            (Measure.pi (fun i : s => gaussianReal 0 (Real.toNNReal (c i))))) t
          = Complex.exp (-(↑(∑ i : s, (t.ofLp i) ^ 2 * c i)) / 2) := by
        rw [charFun_pi]
        have hprod : ∀ i : s, charFun (gaussianReal 0 (Real.toNNReal (c i))) (t.ofLp i)
            = Complex.exp (-(↑(t.ofLp i) ^ 2 * ↑(c i)) / 2) := by
          intro i
          rw [ProbabilityTheory.charFun_gaussianReal, Real.coe_toNNReal (c i) (le_of_lt (hc i))]
          congr 1
          push_cast
          ring
        rw [Finset.prod_congr rfl (fun i _ => hprod i)]
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
      have hmean : (∫ x : U, (inner ℝ T x : ℂ) ∂μ) = (inner ℝ T mUM : ℂ) := by
        have h := ContinuousLinearMap.integral_comp_comm
          (L := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)) (φ := fun x : U => inner ℝ T x) (hint1_mu T)
        rw [hmean_mu T] at h
        simpa using h
      have hvar : Var[fun x : U => inner ℝ T x; μ] = ∑ i : s, (t.ofLp i)^2 * c i := by
        rw [variance_eq_integral (X := fun x : U => inner ℝ T x)
          (continuous_const.inner continuous_id).measurable.aemeasurable]
        rw [hmean_mu T]
        have hpt2 : ∀ ω : U, (inner ℝ T ω - inner ℝ T mUM)^2
            = ∑ i : s, ∑ j : s, ((t.ofLp i) * (t.ofLp j)) *
              ((inner ℝ (e i) ω - inner ℝ (e i) mUM) *
                (inner ℝ (e j) ω - inner ℝ (e j) mUM)) := by
          intro ω
          have h1 : inner ℝ T ω = ∑ i : s, (t.ofLp i) * inner ℝ (e i) ω := by
            rw [hTdef, sum_inner]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [real_inner_smul_left]
          have h2 : inner ℝ T mUM = ∑ i : s, (t.ofLp i) * inner ℝ (e i) mUM := by
            rw [hTdef, sum_inner]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [real_inner_smul_left]
          have hs : (∑ i : s, ((t.ofLp i) * inner ℝ (e i) ω - (t.ofLp i) * inner ℝ (e i) mUM))
              = ∑ i : s, (t.ofLp i) * (inner ℝ (e i) ω - inner ℝ (e i) mUM) :=
            Finset.sum_congr rfl (fun i _ => by ring)
          rw [h1, h2, ← Finset.sum_sub_distrib, hs, sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          ring
        have hcongr : (fun ω : U => (inner ℝ T ω - inner ℝ T mUM)^2)
            = fun ω : U => ∑ i : s, ∑ j : s, ((t.ofLp i) * (t.ofLp j)) *
              ((inner ℝ (e i) ω - inner ℝ (e i) mUM) *
                (inner ℝ (e j) ω - inner ℝ (e j) mUM)) := funext hpt2
        rw [hcongr]
        have hInt : ∀ i j : s, Integrable (fun ω : U =>
            ((t.ofLp i) * (t.ofLp j)) *
              ((inner ℝ (e i) ω - inner ℝ (e i) mUM) *
                (inner ℝ (e j) ω - inner ℝ (e j) mUM))) μ :=
          fun i j => (hint2_mu (e i) (e j)).const_mul _
        rw [integral_finset_sum (Finset.univ)
          (f := fun (i : s) (ω : U) => ∑ j : s, ((t.ofLp i) * (t.ofLp j)) *
              ((inner ℝ (e i) ω - inner ℝ (e i) mUM) *
                (inner ℝ (e j) ω - inner ℝ (e j) mUM)))
          (fun i _ => MeasureTheory.integrable_finset_sum (Finset.univ)
            (fun j _ => hInt i j))]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_finset_sum (Finset.univ)
          (f := fun (j : s) (ω : U) => ((t.ofLp i) * (t.ofLp j)) *
              ((inner ℝ (e i) ω - inner ℝ (e i) mUM) *
                (inner ℝ (e j) ω - inner ℝ (e j) mUM)))
          (fun j _ => hInt i j)]
        have hterm : ∀ j : s, (∫ ω : U, ((t.ofLp i) * (t.ofLp j)) *
              ((inner ℝ (e i) ω - inner ℝ (e i) mUM) *
                (inner ℝ (e j) ω - inner ℝ (e j) mUM)) ∂μ)
            = (t.ofLp i) * (t.ofLp j) * (if (↑i : ℕ) = ↑j then c ↑i else 0) := by
          intro j
          rw [integral_const_mul, hcov_mu (↑i) (↑j)]
        rw [Finset.sum_congr rfl (fun j _ => hterm j)]
        have hsingle : (∑ j ∈ (Finset.univ : Finset s),
              (t.ofLp i) * (t.ofLp j) * (if (↑i : ℕ) = ↑j then c ↑i else 0))
            = (t.ofLp i) * (t.ofLp i) * (if (↑i : ℕ) = ↑i then c ↑i else 0) :=
          Finset.sum_eq_single i (fun j _ hji => by
            have h' : ¬ ((↑i : ℕ) = ↑j) := fun hh => hji (Subtype.ext hh.symm)
            simp [h']) (fun hi => absurd (Finset.mem_univ i) hi)
        rw [hsingle]
        have hif : (if (↑i : ℕ) = ↑i then c ↑i else 0) = c ↑i := if_pos rfl
        rw [hif]
        ring
      have hcharT : charFun μ T = Complex.exp ((inner ℝ T mUM : ℂ) * Complex.I
          - ↑(∑ i : s, (t.ofLp i)^2 * c i) / 2) := by
        rw [ProbabilityTheory.IsGaussian.charFun_eq (t := T), hmean, hvar]
      rw [hL, hR, hcharT, ← Complex.exp_add]
      congr 1
      ring
    have step1 : Measure.map (WithLp.ofLp : EuclideanSpace ℝ s → (s → ℝ))
        (Measure.map (fun u : U =>
          (WithLp.toLp 2 (fun i : s => inner ℝ (e i) (u - mUM)) : EuclideanSpace ℝ s)) μ)
        = Measure.map (fun u : U => fun i : s => inner ℝ (e i) (u - mUM)) μ := by
      rw [Measure.map_map hofLp hΦ]
      congr 1
    have step2 : Measure.map (WithLp.ofLp : EuclideanSpace ℝ s → (s → ℝ))
        (Measure.map (WithLp.toLp 2)
          (Measure.pi (fun i : s => gaussianReal 0 (Real.toNNReal (c i)))))
        = Measure.pi (fun i : s => gaussianReal 0 (Real.toNNReal (c i))) := by
      rw [Measure.map_map hofLp htoLp]
      have hfun : ((WithLp.ofLp ∘ WithLp.toLp 2) : (s → ℝ) → (s → ℝ)) = id := by
        funext x
        exact WithLp.ofLp_toLp 2 x
      rw [hfun, Measure.map_id]
    rw [← step1, hE, step2]
  refine Measure.eq_infinitePi (fun k : ℕ => gaussianReal 0 (Real.toNNReal (c k))) ?_
  intro s t ht
  have hΨ : Measurable (fun u : U => fun k : ℕ => inner ℝ (e k) (u - mUM)) :=
    measurable_pi_iff.mpr (fun k => (hcontT (e k)).measurable)
  have hΦs : Measurable (fun u : U => fun i : s => inner ℝ (e i) (u - mUM)) :=
    measurable_pi_iff.mpr (fun i => (hcontT (e i)).measurable)
  have hcyl : MeasurableSet ((↑s : Set ℕ).pi t) :=
    MeasurableSet.pi s.finite_toSet.countable (fun i _ => ht i)
  have hS : MeasurableSet (Set.pi Set.univ (fun i : s => t ↑i)) :=
    MeasurableSet.pi Set.countable_univ (fun i _ => ht ↑i)
  have hpre : (fun u : U => fun k : ℕ => inner ℝ (e k) (u - mUM)) ⁻¹' ((↑s : Set ℕ).pi t)
      = (fun u : U => fun i : s => inner ℝ (e i) (u - mUM)) ⁻¹'
          (Set.pi Set.univ (fun i : s => t ↑i)) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.mem_coe]
    constructor
    · intro h i
      exact h ↑i i.2
    · intro h i hi
      exact h ⟨i, hi⟩
  rw [Measure.map_apply hΨ hcyl, hpre, ← Measure.map_apply hΦs hS, hmarg s, Measure.pi_pi]
  exact Finset.prod_coe_sort s (fun i => gaussianReal 0 (Real.toNNReal (c i)) (t i))
  /- @proof-region region.target-node.session.ae43bc3dcf4d3457 end -/

end Statlib.Imported
end

