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
theorem statopia_math_node_488254885_6df2d178 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc_pos : ∀ k : ℕ, 0 < c k)
    (mu : Measure U) [IsProbabilityMeasure mu]
    (hmu_gauss : ProbabilityTheory.IsGaussian mu) (m : U)
    (hmu_mean : ∀ v : U, (∫ u, inner ℝ v u ∂mu) = inner ℝ v m)
    (hmu_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v m) * (inner ℝ w u - inner ℝ w m) ∂mu)
        = ∑' k : ℕ, c k * inner ℝ (e k) v * inner ℝ (e k) w)
    (n : ℕ),
    MeasureTheory.Measure.map (fun u : U => fun i : Fin n => inner ℝ (e i) u) mu
      = MeasureTheory.Measure.pi
          (fun i : Fin n =>
            ProbabilityTheory.gaussianReal (inner ℝ (e i) m)
              ⟨c i, le_of_lt (hc_pos i)⟩) := by
  /- @proof-region region.target-node.session.6a633440e8da3e0b begin -/
  classical
  intro U _ _ _ _ _ _ e c hc_pos mu hprob hmu_gauss m hmu_mean hmu_cov n
  haveI hgauss : ProbabilityTheory.IsGaussian mu := hmu_gauss
  set ν : Fin n → Measure ℝ := fun i => ProbabilityTheory.gaussianReal (inner ℝ (e i) m) ⟨c i, le_of_lt (hc_pos i)⟩ with hν
  haveI hνprob : ∀ i, IsProbabilityMeasure (ν i) := fun i => by rw [hν]; exact inferInstance
  set L : U → EuclideanSpace ℝ (Fin n) := fun u => WithLp.toLp 2 (fun i => inner ℝ (e i) u) with hL
  have hLmeas : Measurable L := by measurability
  have hcharPi : ∀ t : EuclideanSpace ℝ (Fin n),
      charFun (Measure.map (WithLp.toLp 2) (Measure.pi ν)) t
        = Complex.exp ((↑(∑ i : Fin n, (t.ofLp i) * inner ℝ (e i) m) : ℂ) * Complex.I - (↑(∑ i : Fin n, ((⟨c i, le_of_lt (hc_pos i)⟩ : NNReal) : ℝ) * (t.ofLp i) ^ 2) : ℂ) / 2) := by
    intro t
    rw [MeasureTheory.charFun_pi]
    have hfac : ∀ i : Fin n, charFun (ν i) (t.ofLp i)
        = Complex.exp ((↑(t.ofLp i) * ↑(inner ℝ (e i) m) : ℂ) * Complex.I - (↑↑(⟨c i, le_of_lt (hc_pos i)⟩ : NNReal) : ℂ) * (↑(t.ofLp i) : ℂ) ^ 2 / 2) := by
      intro i
      change charFun (ProbabilityTheory.gaussianReal (inner ℝ (e i) m) ⟨c i, le_of_lt (hc_pos i)⟩) (t.ofLp i) = _
      exact ProbabilityTheory.charFun_gaussianReal (t.ofLp i)
    rw [Finset.prod_congr rfl fun i _ => hfac i]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_div]
  have hcharMap : ∀ t : EuclideanSpace ℝ (Fin n),
      charFun (Measure.map L mu) t
        = Complex.exp ((↑(∑ i : Fin n, (t.ofLp i) * inner ℝ (e i) m) : ℂ) * Complex.I - (↑(∑ i : Fin n, ((⟨c i, le_of_lt (hc_pos i)⟩ : NNReal) : ℝ) * (t.ofLp i) ^ 2) : ℂ) / 2) := by
    intro t
    set w : U := ∑ i : Fin n, (t.ofLp i) • e i with hw
    have hInt : Integrable (fun x : U => id x) mu :=
      (IsGaussian.memLp_id mu 2 (by norm_num)).integrable (by norm_num)
    have hinner_wm : inner ℝ w m = ∑ i : Fin n, (t.ofLp i) * inner ℝ (e i) m := by
      simp only [hw, sum_inner, real_inner_smul_left]
    have hmean_w : inner ℝ w (∫ x : U, id x ∂mu) = ∑ i : Fin n, (t.ofLp i) * inner ℝ (e i) m := by
      have h1 : inner ℝ w (∫ x : U, id x ∂mu) = ∫ x : U, inner ℝ w x ∂mu := by
        show (innerSL ℝ w) (∫ x : U, id x ∂mu) = ∫ x : U, (innerSL ℝ w) (id x) ∂mu
        rw [← ContinuousLinearMap.integral_comp_comm (innerSL ℝ w) hInt]
      rw [h1, hmu_mean w, hinner_wm]
    have hinner : ∀ u : U, inner ℝ t (L u) = inner ℝ w u := by
      intro u
      have hleft : inner ℝ t (L u) = ∑ i : Fin n, inner ℝ (t.ofLp i) (inner ℝ (e i) u) := by
        rw [show L u = WithLp.toLp 2 (fun i : Fin n => inner ℝ (e i) u) from rfl, PiLp.inner_apply]
      have hright : inner ℝ w u = ∑ i : Fin n, (t.ofLp i) * inner ℝ (e i) u := by
        rw [hw, sum_inner]
        simp only [real_inner_smul_left]
      rw [hleft, hright]
      exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
    have hstep : charFun (Measure.map L mu) t = charFun mu w := by
      simp only [charFun]
      rw [MeasureTheory.integral_map_of_stronglyMeasurable hLmeas] <;> try fun_prop
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by
        show Complex.exp (↑(inner ℝ (L u) t) * Complex.I) = Complex.exp (↑(inner ℝ u w) * Complex.I)
        rw [real_inner_comm t (L u), hinner u, real_inner_comm u w])
    have hcov : ((covarianceBilin mu) w) w = ∑ i : Fin n, ((⟨c i, le_of_lt (hc_pos i)⟩ : NNReal) : ℝ) * (t.ofLp i) ^ 2 := by
      have horth : ∀ a b : ℕ, inner ℝ (e a) (e b) = if a = b then (1 : ℝ) else 0 :=
        fun a b => orthonormal_iff_ite.mp e.orthonormal a b
      have hgen : ∀ k : ℕ, inner ℝ (e k) w = ∑ j : Fin n, (if k = (j : ℕ) then t.ofLp j else 0) := by
        intro k
        rw [real_inner_comm w (e k), hw, sum_inner]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [real_inner_smul_left, horth (j : ℕ) k]
        by_cases h : k = (j : ℕ)
        · rw [if_pos h.symm, if_pos h, mul_one]
        · have h1 : ¬ ((j : ℕ) = k) := fun hh => h hh.symm
          rw [if_neg h1, if_neg h, mul_zero]
      have hterm : ∀ i : Fin n, inner ℝ (e (i : ℕ)) w = t.ofLp i := by
        intro i
        have hsum : (∑ j : Fin n, (if (i : ℕ) = (j : ℕ) then t.ofLp j else 0))
            = ∑ j : Fin n, (if j = i then t.ofLp j else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases h : j = i
          · simp [h]
          · have h2 : ¬ ((i : ℕ) = (j : ℕ)) := fun hh => h (Fin.ext hh.symm)
            simp [h, h2]
        rw [hgen (i : ℕ), hsum, Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
      rw [covarianceBilin_apply_eq_cov (IsGaussian.memLp_id mu 2 (by norm_num)) w w]
      have hform : cov[fun u : U => inner ℝ w u, fun u : U => inner ℝ w u; mu]
          = ∫ u, (inner ℝ w u - inner ℝ w m) * (inner ℝ w u - inner ℝ w m) ∂mu := by
        have h1 : cov[fun u : U => inner ℝ w u, fun u : U => inner ℝ w u; mu]
            = ∫ u, (inner ℝ w u - ∫ x : U, inner ℝ w x ∂mu) *
                (inner ℝ w u - ∫ x : U, inner ℝ w x ∂mu) ∂mu := rfl
        rw [h1, hmu_mean w]
      rw [hform, hmu_cov w w]
      have hsupp : ∀ k : ℕ, k ∉ (Finset.univ.image (fun i : Fin n => (i : ℕ))) →
          c k * inner ℝ (e k) w * inner ℝ (e k) w = 0 := by
        intro k hk
        have h0 : inner ℝ (e k) w = 0 := by
          rw [hgen k]
          refine Finset.sum_eq_zero fun j _ => ?_
          have hne : k ≠ (j : ℕ) := fun hh =>
            hk (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by simp [hh]⟩)
          exact if_neg hne
        simp [h0]
      rw [tsum_eq_sum (s := Finset.univ.image (fun i : Fin n => (i : ℕ))) hsupp]
      rw [Finset.sum_image (fun a _ b _ hab => Fin.ext hab)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm i]
      show c (i : ℕ) * t.ofLp i * t.ofLp i = c (i : ℕ) * t.ofLp i ^ 2
      ring
    rw [hstep, IsGaussian.charFun_eq' w, hmean_w, hcov]
  have hmain : Measure.map L mu = Measure.map (WithLp.toLp 2) (Measure.pi ν) := by
    refine MeasureTheory.Measure.ext_of_charFun ?_
    funext t
    rw [hcharMap t, hcharPi t]
  have hToLp_meas : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    WithLp.measurable_toLp 2 _
  have hOfLp_meas : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) := by
    first
      | measurability
      | exact (by fun_prop : Continuous (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))).measurable
  have hπ_meas : Measurable (fun u : U => fun i : Fin n => inner ℝ (e i) u) := by measurability
  have hinj : Function.Injective (Measure.map (WithLp.toLp 2) : Measure (Fin n → ℝ) → Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a b hab
    have ha := congrArg (Measure.map (WithLp.ofLp) : Measure (EuclideanSpace ℝ (Fin n)) → Measure (Fin n → ℝ)) hab
    rw [MeasureTheory.Measure.map_map hOfLp_meas hToLp_meas,
      MeasureTheory.Measure.map_map hOfLp_meas hToLp_meas] at ha
    have hcomp : (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ∘ (WithLp.toLp 2) = id :=
      funext fun x => WithLp.ofLp_toLp 2 x
    rw [hcomp] at ha
    simpa using ha
  refine hinj ?_
  rw [← hmain]
  rw [MeasureTheory.Measure.map_map hToLp_meas hπ_meas]
  rfl
  /- @proof-region region.target-node.session.6a633440e8da3e0b end -/

end Statlib.Imported
end

