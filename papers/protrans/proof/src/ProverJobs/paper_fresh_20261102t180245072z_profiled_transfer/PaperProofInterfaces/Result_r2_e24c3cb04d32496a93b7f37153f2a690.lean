import Lean
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Vocabulary
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.ProvedNodes
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Base

namespace PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574

open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

theorem paper_6881610d85e44b6089ed4cd810570574
    (L L_eps : ℝ) (hL : 0 < L) (hL_eps : 0 < L_eps) :
    ∃ V : ℝ, 0 < V ∧
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
        (p q : ℕ) (hp : 2 ≤ p) (hq : 1 ≤ q)
        (E fH X : Ω → Fin p → ℝ) (H : Ω → Fin q → ℝ) (eps : Ω → ℝ),
        (∀ i, Measurable (fun ω => E ω i)) →
        (∀ j, Measurable (fun ω => H ω j)) →
        (∀ k, Measurable (fun ω => fH ω k)) →
        (∀ l, Measurable (fun ω => X ω l)) →
        Measurable eps →
        (∀ i, Integrable (fun ω => E ω i) μ) →
        (∀ j, Integrable (fun ω => H ω j) μ) →
        (∀ k, Integrable (fun ω => fH ω k) μ) →
        (∀ l, Integrable (fun ω => X ω l) μ) →
        Integrable eps μ →
        (∀ a b : MomentCoordIdx.{u} p q,
          Integrable (fun ω =>
            momentCoord E fH X H eps a ω * momentCoord E fH X H eps b ω) μ) →
        (∀ i, ∫ ω, E ω i ∂μ = 0) →
        (∀ j, ∫ ω, H ω j ∂μ = 0) →
        (∀ k, ∫ ω, fH ω k ∂μ = 0) →
        (∫ ω, eps ω ∂μ = 0) →
        (∀ i, HasSubgaussianMGF (fun ω => E ω i) ⟨L ^ 2, sq_nonneg L⟩ μ) →
        (∀ j, HasSubgaussianMGF (fun ω => H ω j) ⟨L ^ 2, sq_nonneg L⟩ μ) →
        (∀ k, HasSubgaussianMGF (fun ω => fH ω k) ⟨L ^ 2, sq_nonneg L⟩ μ) →
        HasSubgaussianMGF eps ⟨L_eps ^ 2, sq_nonneg L_eps⟩ μ →
        (∀ ω i, X ω i = fH ω i + E ω i) →
        ((∀ (r : ℕ), 2 ≤ r → ∀ a b : MomentCoordIdx.{u} p q,
          ∫⁻ ω, ENNReal.ofReal
            (|momentCoord E fH X H eps a ω * momentCoord E fH X H eps b ω
              - ∫ ω', momentCoord E fH X H eps a ω'
                  * momentCoord E fH X H eps b ω' ∂μ| ^ r) ∂μ
          ≤ ENNReal.ofReal ((r.factorial : ℝ) * V ^ r)) ∧
        (∀ (κ : Type) [Fintype κ] (a b : κ → MomentCoordIdx.{u} p q) (u : κ → ℝ) (D : ℝ),
          0 ≤ D → (∑ k, |u k|) ≤ D →
          ∀ (r : ℕ), 2 ≤ r →
            ∫⁻ ω, ENNReal.ofReal
              (|∑ k, u k
                  * (momentCoord E fH X H eps (a k) ω * momentCoord E fH X H eps (b k) ω
                    - ∫ ω', momentCoord E fH X H eps (a k) ω'
                        * momentCoord E fH X H eps (b k) ω' ∂μ)| ^ r) ∂μ
            ≤ ENNReal.ofReal ((r.factorial : ℝ) * (V * D) ^ r)))
:= by
  /- @proof-region region.root.c18eea9194c2 begin -/
  have hmax : (0 : ℝ) < max (4 * L ^ 2) (L_eps ^ 2) := by
    have h2 : (0 : ℝ) < L ^ 2 := pow_pos hL 2
    have h4 : (0 : ℝ) < 4 * L ^ 2 := by linarith
    exact lt_max_iff.mpr (Or.inl h4)
  have hexp2 : (0 : ℝ) < (Real.exp 1) ^ 2 := pow_pos (Real.exp_pos 1) 2
  have hVpos : (0 : ℝ) < 8 * max (4 * L ^ 2) (L_eps ^ 2) * (Real.exp 1) ^ 2 :=
    mul_pos (mul_pos (by norm_num) hmax) hexp2
  refine ⟨8 * max (4 * L ^ 2) (L_eps ^ 2) * (Real.exp 1) ^ 2, hVpos, ?_⟩
  intro Ω mΩ μ hμ p q hp hq E fH X H eps hEmeas hHmeas hfHmeas hXmeas hepsmeas
    hEint hHint hfHint hXint hepsint hprod hE0 hH0 hfH0 heps0 hEsub hHsub hfHsub hepssub hXeq
  obtain ⟨_, hunif⟩ := statopia_math_node_3902516804_05785fef L L_eps hL hL_eps
  have hunif' := hunif μ p q hp hq E fH X H eps hEmeas hHmeas hfHmeas hXmeas hepsmeas
    hEsub hHsub hfHsub hepssub hXeq
  have hcoord : ∀ a : MomentCoordIdx p q,
      Measurable (fun ω => momentCoord E fH X H eps a ω) := by
    intro a
    cases a with
    | up c =>
      rcases c with i | c1
      · simpa only [momentCoord] using hEmeas i
      · rcases c1 with j | c2
        · simpa only [momentCoord] using hHmeas j
        · rcases c2 with k | c3
          · simpa only [momentCoord] using hfHmeas k
          · rcases c3 with l | m
            · simpa only [momentCoord] using hXmeas l
            · simpa only [momentCoord] using hepsmeas
  have key : ∀ (r : ℕ), 2 ≤ r → ∀ a b : MomentCoordIdx p q,
      ∫⁻ ω, ENNReal.ofReal
        (|momentCoord E fH X H eps a ω * momentCoord E fH X H eps b ω
          - ∫ ω', momentCoord E fH X H eps a ω'
              * momentCoord E fH X H eps b ω' ∂μ| ^ r) ∂μ
      ≤ ENNReal.ofReal
          ((r.factorial : ℝ) * (8 * max (4 * L ^ 2) (L_eps ^ 2) * (Real.exp 1) ^ 2) ^ r) := by
    intro r hr a b
    exact statopia_math_node_576069795_77c22b31 (max (4 * L ^ 2) (L_eps ^ 2)) hmax μ
      (fun ω => momentCoord E fH X H eps a ω)
      (fun ω => momentCoord E fH X H eps b ω)
      (hcoord a) (hcoord b)
      (fun t => (hunif' a t).1) (fun t => (hunif' a t).2.1)
      (fun t => (hunif' a t).2.2.1) (fun t => (hunif' a t).2.2.2)
      (fun t => (hunif' b t).1) (fun t => (hunif' b t).2.1)
      (fun t => (hunif' b t).2.2.1) (fun t => (hunif' b t).2.2.2)
      (hprod a b) r hr
  refine ⟨key, ?_⟩
  intro κ inst a b u D hD hsum r hr
  exact statopia_math_node_1907643924_c0d46037 μ
    (8 * max (4 * L ^ 2) (L_eps ^ 2) * (Real.exp 1) ^ 2) D hVpos hD u hsum
    (fun k ω => momentCoord E fH X H eps (a k) ω * momentCoord E fH X H eps (b k) ω
      - ∫ ω', momentCoord E fH X H eps (a k) ω'
          * momentCoord E fH X H eps (b k) ω' ∂μ)
    (fun k => Measurable.sub ((hcoord (a k)).mul (hcoord (b k))) measurable_const)
    (fun k r hr => key r hr (a k) (b k)) r hr
  /- @proof-region region.root.c18eea9194c2 end -/

end Statlib.Imported

-- Paper root revision 12662f51-8cf3-456d-a31c-a0603d2387ca

