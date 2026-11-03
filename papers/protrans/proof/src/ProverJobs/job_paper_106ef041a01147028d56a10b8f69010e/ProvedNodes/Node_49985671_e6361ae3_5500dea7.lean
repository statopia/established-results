import Statlib.StatFoundation.RandomVariable.SubGaussian.subgaussian_fourth_moment_le
import Lean
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Vocabulary
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Base

namespace PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e

open _root_.PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_49985671_e6361ae3 : ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (Prow : Measure ((Fin p → ℝ) × (Fin q → ℝ))) [IsProbabilityMeasure Prow]
    (f : (Fin q → ℝ) → Fin p → ℝ) (L : ℝ) (hL : 0 < L)
    (hIntE : ∀ i : Fin p, Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i) Prow)
    (hE0 : ∀ i : Fin p, ∫ x : (Fin p → ℝ) × (Fin q → ℝ), x.1 i ∂Prow = 0)
    (hIntH : ∀ j : Fin q, Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j) Prow)
    (hH0 : ∀ j : Fin q, ∫ x : (Fin p → ℝ) × (Fin q → ℝ), x.2 j ∂Prow = 0)
    (hIntf : ∀ i : Fin p, Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i) Prow)
    (hf0 : ∀ i : Fin p, ∫ x : (Fin p → ℝ) × (Fin q → ℝ), f x.2 i ∂Prow = 0)
    (hSgE : ∀ i : Fin p,
      HasSubgaussianMGF (fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i) ⟨L, hL.le⟩ Prow)
    (hSgH : ∀ j : Fin q,
      HasSubgaussianMGF (fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j) ⟨L, hL.le⟩ Prow)
    (hSgf : ∀ i : Fin p,
      HasSubgaussianMGF (fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i) ⟨L, hL.le⟩ Prow)
    (hIntX : ∀ (i j : Fin p), Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
      (f x.2 i + x.1 i) * (f x.2 j + x.1 j)) Prow)
    (hIntEH : ∀ (i : Fin p) (j : Fin q), Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
      x.1 i * x.2 j) Prow)
    (a b : Fin p),
    |∫ x : (Fin p → ℝ) × (Fin q → ℝ),
      (f x.2 a + x.1 a) * (f x.2 b + x.1 b) ∂Prow| ≤ 8 * max L 1 := by
  /- @proof-region region.target-node.session.8dba8f67acac86fd begin -/
  intro p q hp hq Prow hProb f L hL hIntE hE0 hIntH hH0 hIntf hf0 hSgE hSgH hSgf hIntX hIntEH a b
  haveI : IsProbabilityMeasure Prow := hProb
  have key : ∀ (X : (Fin p → ℝ) × (Fin q → ℝ) → ℝ),
      HasSubgaussianMGF X ⟨L, hL.le⟩ Prow →
      Integrable (fun x => X x ^ 2) Prow ∧ ∫ x, X x ^ 2 ∂Prow ≤ 2 * L := by
    intro X hX
    set t : ℝ := Real.sqrt (2 / L) with ht
    have htpos : 0 < t := by
      rw [ht]; exact Real.sqrt_pos.2 (by positivity)
    have htsq : t ^ 2 = 2 / L := by
      rw [ht]; exact Real.sq_sqrt (by positivity)
    have harg : L * t ^ 2 / 2 = 1 := by
      rw [htsq]; field_simp
    have hexp_pos : Integrable (fun x => Real.exp (t * X x)) Prow := hX.integrable_exp_mul t
    have hexp_neg : Integrable (fun x => Real.exp (-t * X x)) Prow := hX.integrable_exp_mul (-t)
    have hb_pos : ∫ x, Real.exp (t * X x) ∂Prow ≤ Real.exp 1 := by
      have h : ∫ x, Real.exp (t * X x) ∂Prow ≤ Real.exp (L * t ^ 2 / 2) := hX.2 t
      rwa [harg] at h
    have hb_neg : ∫ x, Real.exp (-t * X x) ∂Prow ≤ Real.exp 1 := by
      have h : ∫ x, Real.exp (-t * X x) ∂Prow ≤ Real.exp (L * (-t) ^ 2 / 2) := hX.2 (-t)
      have h2 : L * (-t) ^ 2 / 2 = 1 := by rw [neg_sq]; exact harg
      rwa [h2] at h
    have hFint : Integrable (fun x => Real.exp (t * X x) + Real.exp (-t * X x)) Prow :=
      hexp_pos.add hexp_neg
    have hc2 : Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => (2:ℝ)) Prow :=
      MeasureTheory.integrable_const 2
    have hsubi : Integrable (fun x => Real.exp (t * X x) + Real.exp (-t * X x) - 2) Prow :=
      hFint.sub hc2
    have hmaj_int :
        Integrable (fun x => (Real.exp (t * X x) + Real.exp (-t * X x) - 2) * (L / 2)) Prow :=
      hsubi.mul_const (L / 2)
    have hpt : ∀ x : (Fin p → ℝ) × (Fin q → ℝ),
        X x ^ 2 ≤ (Real.exp (t * X x) + Real.exp (-t * X x) - 2) * (L / 2) := by
      intro x
      have h1 : 1 + (t * X x) ^ 2 / 2 ≤ Real.cosh (t * X x) :=
        Statlib.StatFoundation.RandomVariable.SubGaussian.cosh_ge_one_add_half_sq (t * X x)
      rw [Real.cosh_eq, ← neg_mul] at h1
      have h2 : (t * X x) ^ 2 ≤ Real.exp (t * X x) + Real.exp (-t * X x) - 2 := by linarith
      have hL2 : (0:ℝ) ≤ L / 2 := by linarith
      have h3 := mul_le_mul_of_nonneg_right h2 hL2
      have h4 : (t * X x) ^ 2 * (L / 2) = X x ^ 2 := by
        have hLt : L * t ^ 2 = 2 := by linarith [harg]
        nlinarith [hLt]
      rw [h4] at h3
      exact h3
    have hmaj_nonneg : ∀ x : (Fin p → ℝ) × (Fin q → ℝ),
        0 ≤ (Real.exp (t * X x) + Real.exp (-t * X x) - 2) * (L / 2) := by
      intro x
      exact le_trans (sq_nonneg (X x)) (hpt x)
    have hX2_int : Integrable (fun x => X x ^ 2) Prow := by
      refine Integrable.mono hmaj_int ?_ ?_
      · exact (hX.integrable.aestronglyMeasurable).pow 2
      · refine Filter.Eventually.of_forall fun x => ?_
        have hn : ‖X x ^ 2‖ = X x ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X x))]
        have hm : ‖(Real.exp (t * X x) + Real.exp (-t * X x) - 2) * (L / 2)‖
            = (Real.exp (t * X x) + Real.exp (-t * X x) - 2) * (L / 2) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (hmaj_nonneg x)]
        rw [hn, hm]
        exact hpt x
    refine ⟨hX2_int, ?_⟩
    have hInt2 : ∫ x, (2:ℝ) ∂Prow = 2 := by simp
    have hsubeq : ∫ x, (Real.exp (t * X x) + Real.exp (-t * X x) - 2) ∂Prow
        = (∫ x, (Real.exp (t * X x) + Real.exp (-t * X x)) ∂Prow) - (∫ x, (2:ℝ) ∂Prow) :=
      MeasureTheory.integral_sub hFint hc2
    have haddeq : ∫ x, (Real.exp (t * X x) + Real.exp (-t * X x)) ∂Prow
        = (∫ x, Real.exp (t * X x) ∂Prow) + (∫ x, Real.exp (-t * X x) ∂Prow) :=
      MeasureTheory.integral_add hexp_pos hexp_neg
    have e1 : ∫ x, (Real.exp (t * X x) + Real.exp (-t * X x) - 2) * (L / 2) ∂Prow
        = (∫ x, (Real.exp (t * X x) + Real.exp (-t * X x) - 2) ∂Prow) * (L / 2) :=
      MeasureTheory.integral_mul_const (L / 2)
        (fun x => Real.exp (t * X x) + Real.exp (-t * X x) - 2)
    have e2 : ∫ x, (Real.exp (t * X x) + Real.exp (-t * X x) - 2) ∂Prow
        = ((∫ x, Real.exp (t * X x) ∂Prow) + (∫ x, Real.exp (-t * X x) ∂Prow)) - 2 := by
      rw [hsubeq, haddeq, hInt2]
    have hbnd :
        ((∫ x, Real.exp (t * X x) ∂Prow) + (∫ x, Real.exp (-t * X x) ∂Prow) - 2) * (L / 2)
          ≤ 2 * L := by
      have hA1 : (∫ x, Real.exp (t * X x) ∂Prow) + (∫ x, Real.exp (-t * X x) ∂Prow) - 2
          ≤ 2 * Real.exp 1 - 2 := by linarith
      have hs1 : ((∫ x, Real.exp (t * X x) ∂Prow) + (∫ x, Real.exp (-t * X x) ∂Prow) - 2)
            * (L / 2) ≤ (2 * Real.exp 1 - 2) * (L / 2) :=
        mul_le_mul_of_nonneg_right hA1 (by linarith)
      have hs2 : (2 * Real.exp 1 - 2) * (L / 2) ≤ 2 * L := by
        have h3 : Real.exp 1 - 1 ≤ 2 := by linarith [Real.exp_one_lt_three]
        nlinarith [hL.le, h3]
      linarith
    have hmono : ∫ x, X x ^ 2 ∂Prow
        ≤ ∫ x, (Real.exp (t * X x) + Real.exp (-t * X x) - 2) * (L / 2) ∂Prow :=
      integral_mono hX2_int hmaj_int hpt
    have hfinal : ∫ x, (Real.exp (t * X x) + Real.exp (-t * X x) - 2) * (L / 2) ∂Prow
        ≤ 2 * L := by
      rw [e1, e2]
      exact hbnd
    linarith
  have hAint : Integrable (fun x => (f x.2 a) ^ 2) Prow := (key (fun x => f x.2 a) (hSgf a)).1
  have hA2 : ∫ x, (f x.2 a) ^ 2 ∂Prow ≤ 2 * L := (key (fun x => f x.2 a) (hSgf a)).2
  have hBint : Integrable (fun x => (x.1 a) ^ 2) Prow := (key (fun x => x.1 a) (hSgE a)).1
  have hB2 : ∫ x, (x.1 a) ^ 2 ∂Prow ≤ 2 * L := (key (fun x => x.1 a) (hSgE a)).2
  have hCint : Integrable (fun x => (f x.2 b) ^ 2) Prow := (key (fun x => f x.2 b) (hSgf b)).1
  have hC2 : ∫ x, (f x.2 b) ^ 2 ∂Prow ≤ 2 * L := (key (fun x => f x.2 b) (hSgf b)).2
  have hDint : Integrable (fun x => (x.1 b) ^ 2) Prow := (key (fun x => x.1 b) (hSgE b)).1
  have hD2 : ∫ x, (x.1 b) ^ 2 ∂Prow ≤ 2 * L := (key (fun x => x.1 b) (hSgE b)).2
  have habs4 : ∀ P Q R S : ℝ,
      |P * R + P * S + Q * R + Q * S| ≤ P ^ 2 + Q ^ 2 + R ^ 2 + S ^ 2 := by
    intro P Q R S
    rw [abs_le]
    constructor
    · nlinarith [two_mul_le_add_sq P (-R), two_mul_le_add_sq P (-S),
        two_mul_le_add_sq Q (-R), two_mul_le_add_sq Q (-S)]
    · nlinarith [two_mul_le_add_sq P R, two_mul_le_add_sq P S,
        two_mul_le_add_sq Q R, two_mul_le_add_sq Q S]
  have hmaj : Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
      (f x.2 a) ^ 2 + (x.1 a) ^ 2 + (f x.2 b) ^ 2 + (x.1 b) ^ 2) Prow :=
    ((hAint.add hBint).add hCint).add hDint
  have hpt4 : ∀ x : (Fin p → ℝ) × (Fin q → ℝ),
      |(f x.2 a + x.1 a) * (f x.2 b + x.1 b)|
        ≤ (f x.2 a) ^ 2 + (x.1 a) ^ 2 + (f x.2 b) ^ 2 + (x.1 b) ^ 2 := by
    intro x
    have hE : (f x.2 a + x.1 a) * (f x.2 b + x.1 b)
        = f x.2 a * f x.2 b + f x.2 a * x.1 b + x.1 a * f x.2 b + x.1 a * x.1 b := by
      ring
    rw [hE]
    exact habs4 _ _ _ _
  have hprodabs_int : Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
      |(f x.2 a + x.1 a) * (f x.2 b + x.1 b)|) Prow := by
    have h := (hIntX a b).norm
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    exact Real.norm_eq_abs _
  have hsum_eq : ∫ x, ((f x.2 a) ^ 2 + (x.1 a) ^ 2 + (f x.2 b) ^ 2 + (x.1 b) ^ 2) ∂Prow
      = (∫ x, (f x.2 a) ^ 2 ∂Prow) + (∫ x, (x.1 a) ^ 2 ∂Prow)
        + (∫ x, (f x.2 b) ^ 2 ∂Prow) + (∫ x, (x.1 b) ^ 2 ∂Prow) := by
    have hsp1 : ∫ x, ((f x.2 a) ^ 2 + (x.1 a) ^ 2 + (f x.2 b) ^ 2 + (x.1 b) ^ 2) ∂Prow
        = (∫ x, ((f x.2 a) ^ 2 + (x.1 a) ^ 2 + (f x.2 b) ^ 2) ∂Prow)
          + (∫ x, (x.1 b) ^ 2 ∂Prow) :=
      MeasureTheory.integral_add ((hAint.add hBint).add hCint) hDint
    have hsp2 : ∫ x, ((f x.2 a) ^ 2 + (x.1 a) ^ 2 + (f x.2 b) ^ 2) ∂Prow
        = (∫ x, ((f x.2 a) ^ 2 + (x.1 a) ^ 2) ∂Prow) + (∫ x, (f x.2 b) ^ 2 ∂Prow) :=
      MeasureTheory.integral_add (hAint.add hBint) hCint
    have hsp3 : ∫ x, ((f x.2 a) ^ 2 + (x.1 a) ^ 2) ∂Prow
        = (∫ x, (f x.2 a) ^ 2 ∂Prow) + (∫ x, (x.1 a) ^ 2 ∂Prow) :=
      MeasureTheory.integral_add hAint hBint
    rw [hsp1, hsp2, hsp3]
  have hsum_le : (∫ x, (f x.2 a) ^ 2 ∂Prow) + (∫ x, (x.1 a) ^ 2 ∂Prow)
      + (∫ x, (f x.2 b) ^ 2 ∂Prow) + (∫ x, (x.1 b) ^ 2 ∂Prow) ≤ 8 * L := by
    linarith [hA2, hB2, hC2, hD2]
  have hstep1 : |∫ x, (f x.2 a + x.1 a) * (f x.2 b + x.1 b) ∂Prow|
      ≤ ∫ x, |(f x.2 a + x.1 a) * (f x.2 b + x.1 b)| ∂Prow :=
    MeasureTheory.abs_integral_le_integral_abs
  have hstep2 : ∫ x, |(f x.2 a + x.1 a) * (f x.2 b + x.1 b)| ∂Prow
      ≤ ∫ x, ((f x.2 a) ^ 2 + (x.1 a) ^ 2 + (f x.2 b) ^ 2 + (x.1 b) ^ 2) ∂Prow :=
    integral_mono hprodabs_int hmaj hpt4
  calc |∫ x, (f x.2 a + x.1 a) * (f x.2 b + x.1 b) ∂Prow|
      ≤ ∫ x, |(f x.2 a + x.1 a) * (f x.2 b + x.1 b)| ∂Prow := hstep1
    _ ≤ ∫ x, ((f x.2 a) ^ 2 + (x.1 a) ^ 2 + (f x.2 b) ^ 2 + (x.1 b) ^ 2) ∂Prow := hstep2
    _ = (∫ x, (f x.2 a) ^ 2 ∂Prow) + (∫ x, (x.1 a) ^ 2 ∂Prow)
        + (∫ x, (f x.2 b) ^ 2 ∂Prow) + (∫ x, (x.1 b) ^ 2 ∂Prow) := hsum_eq
    _ ≤ 8 * L := hsum_le
    _ ≤ 8 * max L 1 := by
        have hle : L ≤ max L 1 := le_max_left L 1
        nlinarith
  /- @proof-region region.target-node.session.8dba8f67acac86fd end -/

end

end Statlib.Imported

