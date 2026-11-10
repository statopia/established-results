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
theorem statopia_math_node_266406687_5f4c375e : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (μ : Measure U) [IsProbabilityMeasure μ]
    (m : U)
    (hmean : ∀ v : U, ∫ u, inner ℝ v u ∂μ = inner ℝ v m)
    (hcov_diag : ∀ k l : ℕ, ∫ u, (inner ℝ (e k) u - inner ℝ (e k) m) *
      (inner ℝ (e l) u - inner ℝ (e l) m) ∂μ = if k = l then c k else 0)
    (hint1 : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2 : ∀ v w : U, Integrable (fun u : U =>
      (inner ℝ v u - inner ℝ v m) * (inner ℝ w u - inner ℝ w m)) μ)
    (F : Finset ℕ)
    (Ψ : U →L[ℝ] PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ))
    (hcoord : ∀ (u : U) (k : ↥(F : Set ℕ)), (Ψ u).ofLp k = inner ℝ (e (k : ℕ)) u)
    (hG : ProbabilityTheory.IsGaussian
      (Measure.map (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)) μ))
    (t : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)),
    MeasureTheory.charFun
        (Measure.map (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)) μ) t
      = Complex.exp ((↑(∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m)) * Complex.I -
          ↑(∑ k : ↥(F : Set ℕ), (t.ofLp k) ^ 2 * c (k : ℕ)) / 2) := by
  /- @proof-region region.target-node.session.e260cad929b298e9 begin -/
  intro U _ _ _ _ _ _ e c μ _ m hmean hcov_diag hint1 hint2 F Ψ hcoord hG t
  set ν := Measure.map (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)) μ with hν
  haveI hGν : IsGaussian ν := by rw [hν]; exact hG
  have hcont : Continuous (fun x : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ) => inner ℝ t x) :=
    continuous_const.inner continuous_id
  have hint_eq : ∀ u : U, inner ℝ t (Ψ u)
      = ∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) u := by
    intro u
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcoord u k]
    simp [mul_comm]
  have hA_real : ∫ x : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ), inner ℝ t x ∂ν
      = ∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m := by
    rw [hν,
      MeasureTheory.integral_map (φ := (Ψ : U → PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ)))
        Ψ.continuous.measurable.aemeasurable hcont.aestronglyMeasurable]
    simp only [hint_eq]
    rw [MeasureTheory.integral_finset_sum]
    · exact Finset.sum_congr rfl
        (fun k _ => by rw [MeasureTheory.integral_const_mul, hmean (e (k : ℕ))])
    · intro k _
      exact (hint1 (e (k : ℕ))).const_mul (t.ofLp k)
  have hA : ∫ x : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ), (inner ℝ t x : ℂ) ∂ν
      = ↑(∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m) := by
    have hbridge : (∫ x : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ), (inner ℝ t x : ℂ) ∂ν)
        = ↑(∫ x : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ), inner ℝ t x ∂ν) :=
      integral_ofReal (𝕜 := ℂ)
        (f := fun x : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ) => inner ℝ t x)
    rw [hbridge, hA_real]
  have hB : Var[fun x : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ) => inner ℝ t x; ν]
      = ∑ k : ↥(F : Set ℕ), (t.ofLp k) ^ 2 * c (k : ℕ) := by
    have hcont2 : Continuous (fun ω : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ) =>
        (inner ℝ t ω - ∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m) ^ 2) :=
      (hcont.sub continuous_const).pow 2
    have hvar : Var[fun x : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ) => inner ℝ t x; ν]
        = ∫ ω : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ),
            (inner ℝ t ω - ∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m) ^ 2 ∂ν := by
      rw [ProbabilityTheory.variance_eq_integral hcont.aemeasurable, hA_real]
    have hmap : (∫ ω : PiLp 2 (fun _ : ↥(F : Set ℕ) => ℝ),
          (inner ℝ t ω - ∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m) ^ 2 ∂ν)
        = ∫ u : U,
            (inner ℝ t (Ψ u) - ∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m) ^ 2 ∂μ := by
      rw [hν]
      exact MeasureTheory.integral_map Ψ.continuous.measurable.aemeasurable
        hcont2.aestronglyMeasurable
    have hexp : ∀ u : U,
        (inner ℝ t (Ψ u) - ∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m) ^ 2
          = ∑ k : ↥(F : Set ℕ), ∑ l : ↥(F : Set ℕ), t.ofLp k * t.ofLp l *
              ((inner ℝ (e (k : ℕ)) u - inner ℝ (e (k : ℕ)) m) *
                (inner ℝ (e (l : ℕ)) u - inner ℝ (e (l : ℕ)) m)) := by
      intro u
      have h1 : inner ℝ t (Ψ u) - ∑ k : ↥(F : Set ℕ), t.ofLp k * inner ℝ (e (k : ℕ)) m
          = ∑ k : ↥(F : Set ℕ),
              t.ofLp k * (inner ℝ (e (k : ℕ)) u - inner ℝ (e (k : ℕ)) m) := by
        rw [hint_eq u, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [h1, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      ring
    have hInt : (∫ u : U, ∑ k : ↥(F : Set ℕ), ∑ l : ↥(F : Set ℕ), t.ofLp k * t.ofLp l *
          ((inner ℝ (e (k : ℕ)) u - inner ℝ (e (k : ℕ)) m) *
            (inner ℝ (e (l : ℕ)) u - inner ℝ (e (l : ℕ)) m)) ∂μ)
        = ∑ k : ↥(F : Set ℕ), ∑ l : ↥(F : Set ℕ), ∫ u : U, t.ofLp k * t.ofLp l *
          ((inner ℝ (e (k : ℕ)) u - inner ℝ (e (k : ℕ)) m) *
            (inner ℝ (e (l : ℕ)) u - inner ℝ (e (l : ℕ)) m)) ∂μ := by
      have h1 : (∫ u : U, ∑ k : ↥(F : Set ℕ), ∑ l : ↥(F : Set ℕ), t.ofLp k * t.ofLp l *
            ((inner ℝ (e (k : ℕ)) u - inner ℝ (e (k : ℕ)) m) *
              (inner ℝ (e (l : ℕ)) u - inner ℝ (e (l : ℕ)) m)) ∂μ)
          = ∑ k : ↥(F : Set ℕ), ∫ u : U, ∑ l : ↥(F : Set ℕ), t.ofLp k * t.ofLp l *
            ((inner ℝ (e (k : ℕ)) u - inner ℝ (e (k : ℕ)) m) *
              (inner ℝ (e (l : ℕ)) u - inner ℝ (e (l : ℕ)) m)) ∂μ :=
        MeasureTheory.integral_finset_sum Finset.univ (fun k _ =>
          MeasureTheory.integrable_finset_sum Finset.univ (fun l _ =>
            (hint2 (e (k : ℕ)) (e (l : ℕ))).const_mul (t.ofLp k * t.ofLp l)))
      rw [h1]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact MeasureTheory.integral_finset_sum Finset.univ (fun l _ =>
        (hint2 (e (k : ℕ)) (e (l : ℕ))).const_mul (t.ofLp k * t.ofLp l))
    have hsum : (∑ k : ↥(F : Set ℕ), ∑ l : ↥(F : Set ℕ), ∫ u : U, t.ofLp k * t.ofLp l *
          ((inner ℝ (e (k : ℕ)) u - inner ℝ (e (k : ℕ)) m) *
            (inner ℝ (e (l : ℕ)) u - inner ℝ (e (l : ℕ)) m)) ∂μ)
        = ∑ k : ↥(F : Set ℕ), (t.ofLp k) ^ 2 * c (k : ℕ) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hstep : (∑ l : ↥(F : Set ℕ), ∫ u : U, t.ofLp k * t.ofLp l *
            ((inner ℝ (e (k : ℕ)) u - inner ℝ (e (k : ℕ)) m) *
              (inner ℝ (e (l : ℕ)) u - inner ℝ (e (l : ℕ)) m)) ∂μ)
          = ∑ l : ↥(F : Set ℕ),
              t.ofLp k * t.ofLp l * (if (k : ℕ) = (l : ℕ) then c (k : ℕ) else 0) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [MeasureTheory.integral_const_mul, hcov_diag (k : ℕ) (l : ℕ)]
      rw [hstep]
      have key : (∑ l : ↥(F : Set ℕ),
            t.ofLp k * t.ofLp l * (if (k : ℕ) = (l : ℕ) then c (k : ℕ) else 0))
          = t.ofLp k * t.ofLp k * (if (k : ℕ) = (k : ℕ) then c (k : ℕ) else 0) := by
        refine Finset.sum_eq_single k ?_ ?_
        · intro l _ hlk
          have hne : (k : ℕ) ≠ (l : ℕ) := fun h => hlk (Subtype.ext h).symm
          simp [hne]
        · intro hk
          exact absurd (Finset.mem_univ k) hk
      rw [key]
      simp [sq]
    rw [hvar, hmap]
    simp only [hexp]
    rw [hInt, hsum]
  simp only [IsGaussian.charFun_eq t, hA, hB]
  /- @proof-region region.target-node.session.e260cad929b298e9 end -/

end Statlib.Imported
end

