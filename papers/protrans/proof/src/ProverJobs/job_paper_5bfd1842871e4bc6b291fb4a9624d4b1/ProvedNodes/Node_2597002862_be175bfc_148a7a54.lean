import Statlib.HighDim.Vocabulary.RandomVector
import Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_mgf_mono_param
import Lean
import ProverJobs.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.Vocabulary
import ProverJobs.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.Base

namespace PaperProofTasks.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1

open MeasureTheory ProbabilityTheory
open _root_.PaperProofTasks.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_2597002862_be175bfc : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : Ω → EuclideanSpace ℝ (Fin n)) (C σ : NNReal)
    (hC : ∀ j : Fin n, HasSubgaussianMGF (fun ω => (X ω).ofLp j) C μ)
    (hsigma : (C : ℝ) * (n : ℝ) ≤ (σ : ℝ) ^ 2),
    Statlib.HighDim.Vocabulary.IsSubGaussianVector X σ μ := by
  /- @proof-region region.target-node.session.590934251318e281 begin -/
  intro Ω Ωmeas μ μprob n X C σ hC hσ
  refine ⟨fun v => ?_⟩
  have hinner : ∀ ω, inner ℝ (X ω) v = ∑ j : Fin n, v.ofLp j * (X ω).ofLp j := by
    intro ω
    rw [PiLp.inner_apply]
    simp [mul_comm]
  let c : Fin n → NNReal := fun j => ⟨(v.ofLp j)^2, by positivity⟩ * C
  have hYsub : ∀ j : Fin n, HasSubgaussianMGF (fun ω => v.ofLp j * (X ω).ofLp j) (c j) μ :=
    fun j => (hC j).const_mul (v.ofLp j)
  have hfold : ∀ s : Finset (Fin n),
      HasSubgaussianMGF (fun ω => ∑ j ∈ s, v.ofLp j * (X ω).ofLp j) ((∑ j ∈ s, NNReal.sqrt (c j))^2) μ := by
    intro s
    refine Finset.induction_on (motive := fun s => HasSubgaussianMGF (fun ω => ∑ j ∈ s, v.ofLp j * (X ω).ofLp j) ((∑ j ∈ s, NNReal.sqrt (c j))^2) μ) s ?_ ?_
    · simpa using (HasSubgaussianMGF.fun_zero (μ := μ))
    · intro k s hk ih
      have hfun : (fun ω => v.ofLp k * (X ω).ofLp k + ∑ j ∈ s, v.ofLp j * (X ω).ofLp j)
          = (fun ω => ∑ j ∈ insert k s, v.ofLp j * (X ω).ofLp j) := by
        funext ω
        rw [Finset.sum_insert hk]
      have hproxy : NNReal.sqrt (c k) + NNReal.sqrt ((∑ j ∈ s, NNReal.sqrt (c j))^2)
          = ∑ j ∈ insert k s, NNReal.sqrt (c j) := by
        rw [Finset.sum_insert hk]
        rw [pow_two, NNReal.sqrt_mul_self]
      have hadd := (hYsub k).add ih
      rw [hfun, hproxy] at hadd
      exact hadd
  have hsum : HasSubgaussianMGF (fun ω => ∑ j, v.ofLp j * (X ω).ofLp j) ((∑ j, NNReal.sqrt (c j))^2) μ := by
    simpa using hfold Finset.univ
  have hproj : HasSubgaussianMGF (fun ω => inner ℝ (X ω) v) ((∑ j, NNReal.sqrt (c j))^2) μ := by
    rw [show (fun ω => inner ℝ (X ω) v) = (fun ω => ∑ j, v.ofLp j * (X ω).ofLp j) from funext hinner]
    exact hsum
  have hbound : ((∑ j, NNReal.sqrt (c j))^2) ≤ σ ^ 2 * ‖v‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_pow, NNReal.coe_sum, NNReal.coe_mul]
    have hsqrt_cast : ∀ j : Fin n, ((NNReal.sqrt (c j) : NNReal) : ℝ) = |v.ofLp j| * Real.sqrt (C : ℝ) := by
      intro j
      rw [Real.coe_sqrt]
      have hc : ((c j : NNReal) : ℝ) = (v.ofLp j)^2 * (C : ℝ) := rfl
      rw [hc, Real.sqrt_mul (x := (v.ofLp j)^2) (by positivity) (C : ℝ), Real.sqrt_sq_eq_abs]
    have hnn : ((‖v‖₊ : NNReal) : ℝ) = ‖v‖ := by rfl
    have hsum_eq : (∑ j : Fin n, ((NNReal.sqrt (c j) : NNReal) : ℝ)) = (∑ j : Fin n, |v.ofLp j|) * Real.sqrt (C : ℝ) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => hsqrt_cast j)
    rw [hsum_eq, mul_pow, Real.sq_sqrt (x := (C : ℝ)) (by positivity), hnn]
    have hnorm_eq : (∑ j : Fin n, (v.ofLp j)^2) = ‖v‖^2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl (fun j _ => by rw [Real.norm_eq_abs, sq_abs])
    have hCS : (∑ j : Fin n, |v.ofLp j|)^2 ≤ ‖v‖^2 * (n : ℝ) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) (fun j => |v.ofLp j|) (fun _ => (1:ℝ))
      have e1 : (∑ j : Fin n, |v.ofLp j| * 1) = (∑ j : Fin n, |v.ofLp j|) := by simp
      have e2 : (∑ j : Fin n, |v.ofLp j| ^ 2) = ‖v‖^2 := by
        rw [← hnorm_eq]
        exact Finset.sum_congr rfl (fun j _ => sq_abs (v.ofLp j))
      have e3 : (∑ j : Fin n, (1:ℝ) ^ 2) = (n : ℝ) := by simp
      rw [e1, e2, e3] at h
      exact h
    calc (∑ j : Fin n, |v.ofLp j|)^2 * (C : ℝ)
        ≤ (‖v‖^2 * (n : ℝ)) * (C : ℝ) := by
          have hc0 : (0:ℝ) ≤ (C : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_right hCS hc0
      _ = ‖v‖^2 * ((C : ℝ) * (n : ℝ)) := by ring
      _ ≤ ‖v‖^2 * (↑σ)^2 := by
          have hv0 : (0:ℝ) ≤ ‖v‖^2 := by positivity
          exact mul_le_mul_of_nonneg_left hσ hv0
      _ = (↑σ)^2 * ‖v‖^2 := by ring
  exact Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_mgf_mono_param hbound hproj
  /- @proof-region region.target-node.session.590934251318e281 end -/

end Statlib.Imported

