import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2945293653_548ae0bd_878bb98d

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_287517620_f22d7735 : ∀ (p : ℕ) (hp : 0 < p)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : (Fin p → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (j : Fin p)
    (W U : Ω → (Fin p → ℝ)) (V : Ω → ℝ) (Q : Fin p → Fin p → Ω → ℝ)
    (hU : ∀ l : Fin p, Measurable (fun x : Ω => U x l))
    (hV : Measurable (fun x : Ω => V x))
    (hQnn : ∀ (k l : Fin p) (x : Ω), 0 ≤ Q k l x)
    (hQmaj : ∀ (x : Ω) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ k l : Fin p,
      |(iteratedFDeriv ℝ 3 f (W x + s • U x))
          (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))| ≤ Q k l x)
    (hInt1 : Integrable (fun x : Ω =>
      (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x) μ)
    (hInt2 : Integrable (fun x : Ω =>
      (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x) μ)
    (hInt3 : ∀ k : Fin p, Integrable (fun x : Ω =>
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
        (Pi.single k (1 : ℝ)) * U x k * V x) μ)
    (hInt4 : Integrable (fun x : Ω =>
      ∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l| * |V x|) μ)
    (hE0 : (∫ x, (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x ∂μ) = 0)
    (hE1 : ∀ k : Fin p,
      (∫ x, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
        (Pi.single k (1 : ℝ)) * U x k * V x ∂μ) = 0),
    |∫ x, (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x ∂μ|
      ≤ (1 / 2) * ∫ x,
          (∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l|) * |V x| ∂μ := by
  /- @proof-region region.target-node.session.627906d70ad11910 begin -/
  intro p hp Ω _ μ _ f hf j W U V Q hU hV hQnn hQmaj hInt1 hInt2 hInt3 hInt4 hE0 hE1
  have hDir : ∀ (a b c x : Fin p → ℝ),
      (iteratedFDeriv ℝ 3 f x) ![a, b, c]
        = (fderiv ℝ (fun y : Fin p → ℝ =>
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) c) y) b) x) a := by
    intro a b c x
    have hfderiv : ∀ (n : WithTop ℕ∞) (g : (Fin p → ℝ) → ℝ), ContDiff ℝ (n + 1) g →
        ContDiff ℝ n (fun y : Fin p → ℝ => fderiv ℝ g y) := by
      intro n g hg
      have hsnd : ContDiff ℝ (n + 1)
          (Prod.snd : (Fin p → ℝ) × (Fin p → ℝ) → (Fin p → ℝ)) :=
        (contDiff_snd (𝕜 := ℝ) (n := ⊤)).of_le le_top
      have hunc : ContDiff ℝ (n + 1)
          (Function.uncurry (fun (_ : Fin p → ℝ) (z : Fin p → ℝ) => g z)) := by
        simpa [Function.uncurry] using hg.comp hsnd
      simpa using ContDiff.fderiv (𝕜 := ℝ)
        (f := fun (_ : Fin p → ℝ) (z : Fin p → ℝ) => g z)
        (g := fun x : Fin p → ℝ => x) hunc contDiff_id le_rfl
    have h23 : (2 : WithTop ℕ∞) + 1 = 3 := by norm_num
    have h12 : (1 : WithTop ℕ∞) + 1 = 2 := by norm_num
    have hD1 : ContDiff ℝ 2 (fun y : Fin p → ℝ => fderiv ℝ f y) :=
      hfderiv 2 f (h23.symm ▸ hf)
    have hG : ContDiff ℝ 2 (fun y : Fin p → ℝ => (fderiv ℝ f y) c) :=
      hD1.clm_apply contDiff_const
    have hD2 : ContDiff ℝ 1 (fun y : Fin p → ℝ =>
        fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) c) y) :=
      hfderiv 1 (fun z : Fin p → ℝ => (fderiv ℝ f z) c) (h12.symm ▸ hG)
    have hinit : Fin.init ![a, b, c] = (![a, b] : Fin 2 → (Fin p → ℝ)) := by
      funext i
      fin_cases i <;> simp [Fin.init]
    have hlast : (![a, b, c] : Fin 3 → (Fin p → ℝ)) (Fin.last 2) = c := by
      simp
    have hA : (iteratedFDeriv ℝ 3 f x) ![a, b, c]
        = ((iteratedFDeriv ℝ 2 (fun y : Fin p → ℝ => fderiv ℝ f y) x) ![a, b]) c := by
      have h1 := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := f) (x := x) (n := 2)
        (m := ![a, b, c])
      simpa [hinit, hlast] using h1
    have hB : ((iteratedFDeriv ℝ 2 (fun y : Fin p → ℝ => fderiv ℝ f y) x) ![a, b]) c
        = (iteratedFDeriv ℝ 2 (fun y : Fin p → ℝ => (fderiv ℝ f y) c) x) ![a, b] := by
      have h1 := iteratedFDeriv_clm_apply_const_apply (𝕜 := ℝ)
        (c := fun y : Fin p → ℝ => fderiv ℝ f y) hD1 (i := 2) (by norm_num)
        (x := x) (u := c) (m := ![a, b])
      exact h1.symm
    have hC : (iteratedFDeriv ℝ 2 (fun y : Fin p → ℝ => (fderiv ℝ f y) c) x) ![a, b]
        = ((fderiv ℝ (fderiv ℝ (fun y : Fin p → ℝ => (fderiv ℝ f y) c)) x) a) b := by
      have h1 := iteratedFDeriv_two_apply (𝕜 := ℝ)
        (f := fun y : Fin p → ℝ => (fderiv ℝ f y) c) (z := x) (m := ![a, b])
      simpa using h1
    have hD : (fderiv ℝ (fun y : Fin p → ℝ =>
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) c) y) b) x) a
        = ((fderiv ℝ (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) c)) x) a) b := by
      have h1 := iteratedFDeriv_clm_apply_const_apply (𝕜 := ℝ)
        (c := fun y : Fin p → ℝ => fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) c) y) hD2
        (i := 1) (by norm_num) (x := x) (u := b) (m := ![a])
      simp only [iteratedFDeriv_one_apply] at h1
      simpa using h1
    calc (iteratedFDeriv ℝ 3 f x) ![a, b, c]
        = ((iteratedFDeriv ℝ 2 (fun y : Fin p → ℝ => fderiv ℝ f y) x) ![a, b]) c := hA
      _ = (iteratedFDeriv ℝ 2 (fun y : Fin p → ℝ => (fderiv ℝ f y) c) x) ![a, b] := hB
      _ = ((fderiv ℝ (fderiv ℝ (fun y : Fin p → ℝ => (fderiv ℝ f y) c)) x) a) b := hC
      _ = (fderiv ℝ (fun y : Fin p → ℝ =>
            (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) c) y) b) x) a := hD.symm
  have hstep : ∀ (x : Ω) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ k l : Fin p,
      |(fderiv ℝ (fun y : Fin p → ℝ =>
          (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) y)
            (Pi.single k (1 : ℝ))) (W x + s • U x)) (Pi.single l (1 : ℝ))| ≤ Q k l x := by
    intro x s hs k l
    have htup : (fun t : Fin 3 => Pi.single (![l, k, j] t) (1 : ℝ))
        = ![Pi.single l (1 : ℝ), Pi.single k (1 : ℝ), Pi.single j (1 : ℝ)] := by
      funext t
      fin_cases t <;> simp
    rw [← hDir (Pi.single l (1 : ℝ)) (Pi.single k (1 : ℝ)) (Pi.single j (1 : ℝ)) (W x + s • U x),
      ← htup]
    exact hQmaj x s hs k l
  have hTaylor : ∀ x : Ω,
      |(fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ))
        - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
            (Pi.single k (1 : ℝ)) * U x k|
      ≤ (1 / 2) * ∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l| := by
    intro x
    exact statopia_math_node_2945293653_548ae0bd p f hf (W x) (U x) j (fun k l => Q k l x)
      (hstep x)
  have hCint : Integrable (fun x : Ω => ∑ k : Fin p,
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
        (Pi.single k (1 : ℝ)) * U x k * V x) μ := by
    refine integrable_finset_sum Finset.univ (fun k _ => ?_)
    exact hInt3 k
  have hC0 : (∫ x : Ω, ∑ k : Fin p,
      (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
        (Pi.single k (1 : ℝ)) * U x k * V x ∂μ) = 0 := by
    rw [integral_finset_sum Finset.univ (fun k _ => hInt3 k)]
    simp [hE1]
  have hB1 : Integrable (fun x : Ω => (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x
      - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x) μ := hInt1.sub hInt2
  have hRint : Integrable (fun x : Ω => (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x
      - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x
      - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
          (Pi.single k (1 : ℝ)) * U x k * V x) μ := hB1.sub hCint
  have hAeq : (∫ x : Ω, (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x ∂μ)
      = ∫ x : Ω, ((fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x
          - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x
          - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
              (Pi.single k (1 : ℝ)) * U x k * V x) ∂μ := by
    rw [integral_sub hB1 hCint, integral_sub hInt1 hInt2, hE0, hC0]
    ring
  have hAbsInt : Integrable (fun x : Ω => |(fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x
      - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x
      - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
          (Pi.single k (1 : ℝ)) * U x k * V x|) μ := by
    simpa only [Real.norm_eq_abs] using hRint.norm
  have hSfun : (fun x : Ω => ∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l| * |V x|)
      = fun x : Ω => (∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l|) * |V x| := by
    funext x
    simp only [Finset.sum_mul]
  have hSint : Integrable (fun x : Ω =>
      (∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l|) * |V x|) μ := by
    rw [← hSfun]
    exact hInt4
  have hmajInt : Integrable (fun x : Ω =>
      (1 / 2) * ((∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l|) * |V x|)) μ := by
    simpa using hSint.const_mul (1 / 2)
  have hbound : ∀ x : Ω,
      |(fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x
        - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x
        - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
            (Pi.single k (1 : ℝ)) * U x k * V x|
      ≤ (1 / 2) * ((∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l|) * |V x|) := by
    intro x
    have hT : (∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
            (Pi.single k (1 : ℝ)) * U x k * V x)
        = (∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
            (Pi.single k (1 : ℝ)) * U x k) * V x := by
      rw [Finset.sum_mul]
    have hfac : (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x
        - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x
        - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
            (Pi.single k (1 : ℝ)) * U x k * V x
        = ((fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ))
            - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
                (Pi.single k (1 : ℝ)) * U x k) * V x := by
      rw [hT]
      ring
    rw [hfac, abs_mul]
    calc |(fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ))
            - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
                (Pi.single k (1 : ℝ)) * U x k| * |V x|
        ≤ ((1 / 2) * ∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l|) * |V x| :=
          mul_le_mul_of_nonneg_right (hTaylor x) (abs_nonneg (V x))
      _ = (1 / 2) * ((∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l|) * |V x|) := by ring
  have hnorm := norm_integral_le_integral_norm (μ := μ)
    (fun x : Ω => (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x
      - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x
      - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
          (Pi.single k (1 : ℝ)) * U x k * V x)
  calc |∫ x : Ω, (fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x ∂μ|
      = |∫ x : Ω, ((fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x
          - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x
          - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
              (Pi.single k (1 : ℝ)) * U x k * V x) ∂μ| := by rw [hAeq]
    _ ≤ ∫ x : Ω, |(fderiv ℝ f (W x + U x)) (Pi.single j (1 : ℝ)) * V x
          - (fderiv ℝ f (W x)) (Pi.single j (1 : ℝ)) * V x
          - ∑ k : Fin p, (fderiv ℝ (fun z : Fin p → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) (W x))
              (Pi.single k (1 : ℝ)) * U x k * V x| ∂μ := by
        simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ ∫ x : Ω, (1 / 2) * ((∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l|) * |V x|) ∂μ :=
        integral_mono_ae hAbsInt hmajInt (Filter.Eventually.of_forall hbound)
    _ = (1 / 2) * ∫ x : Ω, (∑ k : Fin p, ∑ l : Fin p, Q k l x * |U x k| * |U x l|) * |V x| ∂μ := by
        rw [integral_const_mul]
  /- @proof-region region.target-node.session.627906d70ad11910 end -/

end

end Statlib.Imported

