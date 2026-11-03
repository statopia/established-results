import Lean
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Vocabulary
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Base

namespace PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_3902516804_05785fef : ∀ (L L_eps : ℝ) (hL : 0 < L) (hL_eps : 0 < L_eps),
    0 < max (4 * L ^ 2) (L_eps ^ 2) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (p q : ℕ), 2 ≤ p → 1 ≤ q →
        ∀ (E fH X : Ω → Fin p → ℝ) (H : Ω → Fin q → ℝ) (eps : Ω → ℝ),
          (∀ (i : Fin p), Measurable (fun ω => E ω i)) →
          (∀ (j : Fin q), Measurable (fun ω => H ω j)) →
          (∀ (k : Fin p), Measurable (fun ω => fH ω k)) →
          (∀ (l : Fin p), Measurable (fun ω => X ω l)) →
          Measurable eps →
          (∀ (i : Fin p), HasSubgaussianMGF (fun ω => E ω i) ⟨L ^ 2, sq_nonneg L⟩ μ) →
          (∀ (j : Fin q), HasSubgaussianMGF (fun ω => H ω j) ⟨L ^ 2, sq_nonneg L⟩ μ) →
          (∀ (k : Fin p), HasSubgaussianMGF (fun ω => fH ω k) ⟨L ^ 2, sq_nonneg L⟩ μ) →
          HasSubgaussianMGF eps ⟨L_eps ^ 2, sq_nonneg L_eps⟩ μ →
          (∀ (ω : Ω) (i : Fin p), X ω i = fH ω i + E ω i) →
          ∀ (a : MomentCoordIdx p q) (t : ℝ),
            Integrable (fun ω => Real.exp (t * momentCoord E fH X H eps a ω)) μ ∧
              Integrable (fun ω => Real.exp (-t * momentCoord E fH X H eps a ω)) μ ∧
                ∫ ω, Real.exp (t * momentCoord E fH X H eps a ω) ∂μ ≤
                  Real.exp (max (4 * L ^ 2) (L_eps ^ 2) * t ^ 2 / 2) ∧
                  ∫ ω, Real.exp (-t * momentCoord E fH X H eps a ω) ∂μ ≤
                    Real.exp (max (4 * L ^ 2) (L_eps ^ 2) * t ^ 2 / 2) := by
  /- @proof-region region.target-node.session.806bc0b052fbd174 begin -/
  intro L L_eps hL hL_eps
  have h4 : (0 : ℝ) < 4 * L ^ 2 := by nlinarith [sq_nonneg L]
  have hc : (0 : ℝ) < max (4 * L ^ 2) (L_eps ^ 2) := lt_of_lt_of_le h4 (le_max_left _ _)
  refine ⟨hc, ?_⟩
  intro Ω _ μ _ p q hp hq E fH X H eps hE hH hfH hX hEps hEsub hHsub hfHsub hEpssub hXeq a t
  have hmono : ∀ {Y : Ω → ℝ} {c₁ : NNReal}, c₁ ≤ (⟨max (4 * L ^ 2) (L_eps ^ 2), le_of_lt hc⟩ : NNReal) →
      HasSubgaussianMGF Y c₁ μ →
        HasSubgaussianMGF Y (⟨max (4 * L ^ 2) (L_eps ^ 2), le_of_lt hc⟩ : NNReal) μ := by
    intro Y c₁ hle h
    refine ⟨h.1, ?_⟩
    intro s
    refine (h.mgf_le s).trans (Real.exp_le_exp.2 ?_)
    have hcoe : (c₁ : ℝ) ≤ max (4 * L ^ 2) (L_eps ^ 2) := hle
    have hs : (0 : ℝ) ≤ s ^ 2 / 2 := by positivity
    calc (c₁ : ℝ) * s ^ 2 / 2 = (c₁ : ℝ) * (s ^ 2 / 2) := by ring
      _ ≤ max (4 * L ^ 2) (L_eps ^ 2) * (s ^ 2 / 2) := mul_le_mul_of_nonneg_right hcoe hs
      _ = max (4 * L ^ 2) (L_eps ^ 2) * s ^ 2 / 2 := by ring
  have hLc : (⟨L ^ 2, sq_nonneg L⟩ : NNReal) ≤
      (⟨max (4 * L ^ 2) (L_eps ^ 2), le_of_lt hc⟩ : NNReal) := by
    have h : (L ^ 2 : ℝ) ≤ max (4 * L ^ 2) (L_eps ^ 2) :=
      calc (L ^ 2 : ℝ) ≤ 4 * L ^ 2 := by nlinarith [sq_nonneg L]
        _ ≤ max (4 * L ^ 2) (L_eps ^ 2) := le_max_left _ _
    exact h
  have hEpsc : (⟨L_eps ^ 2, sq_nonneg L_eps⟩ : NNReal) ≤
      (⟨max (4 * L ^ 2) (L_eps ^ 2), le_of_lt hc⟩ : NNReal) :=
    le_max_right (4 * L ^ 2) (L_eps ^ 2)
  have hAddc : ((NNReal.sqrt ⟨L ^ 2, sq_nonneg L⟩ + NNReal.sqrt ⟨L ^ 2, sq_nonneg L⟩) ^ 2 : NNReal)
      ≤ (⟨max (4 * L ^ 2) (L_eps ^ 2), le_of_lt hc⟩ : NNReal) := by
    have hcoe : (((NNReal.sqrt ⟨L ^ 2, sq_nonneg L⟩ + NNReal.sqrt ⟨L ^ 2, sq_nonneg L⟩) ^ 2 : NNReal) : ℝ)
        ≤ max (4 * L ^ 2) (L_eps ^ 2) := by
      push_cast
      have hx : (Real.sqrt (L ^ 2)) ^ 2 = L ^ 2 := Real.sq_sqrt (sq_nonneg L)
      nlinarith [le_max_left (4 * (L ^ 2)) (L_eps ^ 2), Real.sqrt_nonneg (L ^ 2)]
    exact hcoe
  have hZa : HasSubgaussianMGF (fun ω => momentCoord E fH X H eps a ω)
      ⟨max (4 * L ^ 2) (L_eps ^ 2), le_of_lt hc⟩ μ := by
    rcases a with i | (j | (k | (l | u)))
    · simpa only [momentCoord] using hmono hLc (hEsub i)
    · simpa only [momentCoord] using hmono hLc (hHsub j)
    · simpa only [momentCoord] using hmono hLc (hfHsub k)
    · have hadd := (hfHsub l).add (hEsub l)
      have hcongr : HasSubgaussianMGF (fun ω => X ω l)
          ((NNReal.sqrt ⟨L ^ 2, sq_nonneg L⟩ + NNReal.sqrt ⟨L ^ 2, sq_nonneg L⟩) ^ 2) μ := by
        refine hadd.congr ?_
        filter_upwards with ω
        exact (hXeq ω l).symm
      simpa only [momentCoord] using hmono hAddc hcongr
    · simpa only [momentCoord] using hmono hEpsc hEpssub
  refine ⟨hZa.1 t, hZa.1 (-t), ?_, ?_⟩
  · have h := hZa.mgf_le t
    simp only [ProbabilityTheory.mgf] at h
    simpa using h
  · have h := hZa.mgf_le (-t)
    simp only [ProbabilityTheory.mgf] at h
    simpa using h
  /- @proof-region region.target-node.session.806bc0b052fbd174 end -/

end Statlib.Imported

