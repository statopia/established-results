import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_266406687_5f4c375e_1ac7bf3b

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
theorem statopia_math_node_1420010127_b25b6ecd : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc : ∀ k : ℕ, 0 < c k)
    (μ : Measure U) [IsProbabilityMeasure μ]
    (hmu_gauss : ProbabilityTheory.IsGaussian μ)
    (m : U)
    (hmean : ∀ v : U, ∫ u, inner ℝ v u ∂μ = inner ℝ v m)
    (hcov_diag : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) m) * (inner ℝ (e l) u - inner ℝ (e l) m) ∂μ
        = if k = l then c k else 0)
    (hint1 : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2 : ∀ v w : U,
      Integrable (fun u : U => (inner ℝ v u - inner ℝ v m) * (inner ℝ w u - inner ℝ w m)) μ)
    (F : Finset ℕ),
    Measure.map (fun u : U => fun k : (F : Set ℕ) => inner ℝ (e k) u) μ
      = Measure.pi (fun k : (F : Set ℕ) =>
          gaussianReal (inner ℝ (e k) m) (Real.toNNReal (c k))) := by
  /- @proof-region region.target-node.session.07d04d06fb896411 begin -/
  intro U _ _ _ _ _ _ e c hc μ _ hmu_gauss m hmean hcov_diag hint1 hint2 F
  classical
  haveI hμgauss : IsGaussian μ := hmu_gauss
  let ψ : U → ↥(F : Set ℕ) → ℝ := fun u k => inner ℝ (e (k : ℕ)) u
  let Ψ : U →L[ℝ] PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ) :=
    ∑ k : ↥(F : Set ℕ),
      (innerSL ℝ (e (k : ℕ))).smulRight
        (WithLp.toLp 2 (Function.update (0 : ↥(F : Set ℕ) → ℝ) k 1))
  have hΨ : ∀ u : U, (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)) u = WithLp.toLp 2 (ψ u) := by
    intro u
    apply WithLp.ofLp_injective
    funext j
    show (Ψ u).ofLp j = inner ℝ (e (j : ℕ)) u
    have hΨu : (Ψ u).ofLp
        = ∑ k : ↥(F : Set ℕ),
            (inner ℝ (e (k : ℕ)) u) • (Function.update (0 : ↥(F : Set ℕ) → ℝ) k 1) := by
      simp only [Ψ, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
        WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_toLp, innerSL_apply_apply]
    rw [hΨu, Finset.sum_apply]
    have hterm : ∀ k ∈ (Finset.univ : Finset ↥(F : Set ℕ)), k ≠ j →
        ((inner ℝ (e (k : ℕ)) u) • (Function.update (0 : ↥(F : Set ℕ) → ℝ) k 1)) j = 0 := by
      intro k _ hkj
      have hjk : j ≠ k := fun h => hkj h.symm
      have h1 : (Function.update (0 : ↥(F : Set ℕ) → ℝ) k 1) j = 0 := by
        simp [hjk]
      show inner ℝ (e (k : ℕ)) u • (Function.update (0 : ↥(F : Set ℕ) → ℝ) k 1) j = 0
      rw [h1, smul_zero]
    have hself : ((inner ℝ (e (j : ℕ)) u) •
        (Function.update (0 : ↥(F : Set ℕ) → ℝ) j 1)) j = inner ℝ (e (j : ℕ)) u := by
      simp
    rw [Finset.sum_eq_single j hterm (fun hj => absurd (Finset.mem_univ j) hj), hself]
  let ν : ↥(F : Set ℕ) → Measure ℝ :=
    fun k => gaussianReal (inner ℝ (e (k : ℕ)) m) (Real.toNNReal (c (k : ℕ)))
  have hνprob : ∀ k : ↥(F : Set ℕ), IsProbabilityMeasure (ν k) := by
    intro k
    exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  haveI : ∀ k : ↥(F : Set ℕ), IsProbabilityMeasure (ν k) := hνprob
  haveI hGΨ : IsGaussian (Measure.map (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)) μ) :=
    isGaussian_map Ψ
  have hchar : ∀ t : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ),
      charFun (Measure.map (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)) μ) t
        = charFun (Measure.map (WithLp.toLp 2) (Measure.pi ν)) t := by
    intro t
    have hcoord : ∀ (u : U) (k : ↥(F : Set ℕ)), (Ψ u).ofLp k = inner ℝ (e (k : ℕ)) u := by
      intro u k
      rw [hΨ u, WithLp.ofLp_toLp]
    have hL : charFun (Measure.map (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)) μ) t
        = Complex.exp ((↑(∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m)) * Complex.I
            - ↑(∑ k : ↥(F : Set ℕ), (t.ofLp k) ^ 2 * c (k : ℕ)) / 2) :=
      statopia_math_node_266406687_5f4c375e U e c μ m hmean hcov_diag hint1 hint2 F Ψ hcoord hGΨ t
    have htoNN : ∀ k : ↥(F : Set ℕ),
        ((Real.toNNReal (c (k : ℕ)) : NNReal) : ℂ) = (↑(c (k : ℕ)) : ℂ) := by
      intro k
      have h : ((Real.toNNReal (c (k : ℕ)) : NNReal) : ℝ) = c (k : ℕ) := by
        first
          | exact Real.coe_toNNReal _ (le_of_lt (hc (k : ℕ)))
          | simp [Real.toNNReal_of_nonneg (le_of_lt (hc (k : ℕ)))]
          | simp [Real.toNNReal, max_eq_left (le_of_lt (hc (k : ℕ)))]
      first
        | exact_mod_cast h
        | exact congrArg (fun r : ℝ => (r : ℂ)) h
    have hcast1 : (↑(∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m) : ℂ)
        = ∑ k : ↥(F : Set ℕ), (↑(t.ofLp k) : ℂ) * (↑(inner ℝ (e (k : ℕ)) m) : ℂ) := by
      push_cast
      first
        | rfl
        | simp
        | ring
    have hcast2 : (↑(∑ k : ↥(F : Set ℕ), (t.ofLp k) ^ 2 * c (k : ℕ)) : ℂ)
        = ∑ k : ↥(F : Set ℕ), (↑(t.ofLp k) : ℂ) ^ 2 * (↑(c (k : ℕ)) : ℂ) := by
      push_cast
      first
        | rfl
        | simp
        | ring
    have hExp : (↑(∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m) : ℂ) * Complex.I
          - ↑(∑ k : ↥(F : Set ℕ), (t.ofLp k) ^ 2 * c (k : ℕ)) / 2
        = ∑ k : ↥(F : Set ℕ), ((↑(t.ofLp k) : ℂ) * (↑(inner ℝ (e (k : ℕ)) m) : ℂ) * Complex.I
            - ↑↑(Real.toNNReal (c (k : ℕ))) * (↑(t.ofLp k) : ℂ) ^ 2 / 2) := by
      rw [hcast1, hcast2, Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [htoNN k]
      ring
    have hprod : (∏ k : ↥(F : Set ℕ), charFun (ν k) (t.ofLp k))
        = ∏ k : ↥(F : Set ℕ),
            Complex.exp ((↑(t.ofLp k) : ℂ) * (↑(inner ℝ (e (k : ℕ)) m) : ℂ) * Complex.I
              - ↑↑(Real.toNNReal (c (k : ℕ))) * (↑(t.ofLp k) : ℂ) ^ 2 / 2) :=
      Finset.prod_congr rfl (fun k _ => ProbabilityTheory.charFun_gaussianReal (t.ofLp k))
    rw [hL, MeasureTheory.charFun_pi, hprod, ← Complex.exp_sum]
    exact congrArg Complex.exp hExp
  have hmapΨ : Measure.map (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)) μ
      = Measure.map (WithLp.toLp 2) (Measure.pi ν) :=
    Measure.ext_of_charFun (funext hchar)
  have hψmeas : Measurable ψ := by
    refine measurable_pi_iff.mpr (fun k => ?_)
    exact (innerSL ℝ (e (k : ℕ))).continuous.measurable
  have hcomp : Measure.map (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)) μ
      = Measure.map (WithLp.toLp 2) (Measure.map ψ μ) := by
    have hfe : (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)) = WithLp.toLp 2 ∘ ψ := by
      funext u
      exact hΨ u
    rw [hfe, Measure.map_map (WithLp.measurable_toLp 2 _) hψmeas]
  have hdesc : Measure.map ψ μ = Measure.pi ν := by
    have hmain : Measure.map (WithLp.toLp 2) (Measure.map ψ μ)
        = Measure.map (WithLp.toLp 2) (Measure.pi ν) := hcomp.symm.trans hmapΨ
    have hinj : Function.Injective
        (Measure.map ⇑(MeasurableEquiv.toLp 2 (↥(F : Set ℕ) → ℝ))) :=
      MeasurableEquiv.map_measurableEquiv_injective _
    rw [MeasurableEquiv.coe_toLp] at hinj
    exact hinj hmain
  exact hdesc

  /- @proof-region region.target-node.session.07d04d06fb896411 end -/

end Statlib.Imported
end

