import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1595882321_18775fcf : ∀ (m n : ℕ)
    (A : Matrix (Fin m) (Fin n) ℝ),
    ‖A.map (fun r : ℝ => (r : ℂ))‖ = ‖A‖ := by
  /- @proof-region region.target-node.session.6273921ccaaca9f8 begin -/
  intro m n A
  have hsqC : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    intro r
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, pow_two]
  have hsqR : ∀ r : ℝ, ‖r‖ ^ 2 = r ^ 2 := by
    intro r
    rw [Real.norm_eq_abs, sq_abs]
  have hsqinj : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ 2 = b ^ 2 → a = b := by
    intro a b ha hb h
    rw [(Real.sqrt_sq ha).symm, (Real.sqrt_sq hb).symm, h]
  have hsqle : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ 2 ≤ b ^ 2 → a ≤ b := by
    intro a b ha hb h
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
      _ = b := Real.sqrt_sq hb
  have hnc : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    intro w
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hreim : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I) = ⟨x, y⟩ := by
    intro x y
    apply Complex.ext <;> simp
  have hsplit : ∀ x y : ℝ, ‖((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = x ^ 2 + y ^ 2 := by
    intro x y
    rw [hreim x y, hnc]
  have hbound : ∀ {𝕜 : Type} [RCLike 𝕜] (M : Matrix (Fin m) (Fin n) 𝕜) (x : EuclideanSpace 𝕜 (Fin n)),
      ‖(Matrix.toEuclideanLin M) x‖ ≤ ‖M‖ * ‖x‖ := by
    intro 𝕜 _ M x
    have h := Matrix.l2_opNorm_mulVec M x
    rw [Matrix.toEuclideanLin_apply]
    exact h
  have key : ∀ {𝕜 : Type} [RCLike 𝕜] (M : Matrix (Fin m) (Fin n) 𝕜) (c : ℝ), 0 ≤ c →
      (∀ x : EuclideanSpace 𝕜 (Fin n), ‖(Matrix.toEuclideanLin M) x‖ ≤ c * ‖x‖) → ‖M‖ ≤ c := by
    intro 𝕜 _ M c hc h
    rw [Matrix.l2_opNorm_def M]
    refine ContinuousLinearMap.opNorm_le_bound _ hc (fun x => ?_)
    exact h x
  have hnn : ∀ {𝕜 : Type} [RCLike 𝕜] (M : Matrix (Fin m) (Fin n) 𝕜), (0 : ℝ) ≤ ‖M‖ := by
    intro 𝕜 _ M
    rw [Matrix.l2_opNorm_def M]
    exact norm_nonneg _
  have hnorm : ∀ (k : ℕ) (f : Fin k → ℝ),
      ‖(WithLp.toLp 2 (fun i => ((f i : ℝ) : ℂ)) : EuclideanSpace ℂ (Fin k))‖
        = ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin k))‖ := by
    intro k f
    have h1 : ‖(WithLp.toLp 2 (fun i => ((f i : ℝ) : ℂ)) : EuclideanSpace ℂ (Fin k))‖ ^ 2
        = ∑ i, (f i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [WithLp.ofLp_toLp]
      exact hsqC (f i)
    have h2 : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin k))‖ ^ 2 = ∑ i, (f i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [WithLp.ofLp_toLp]
      exact hsqR (f i)
    exact hsqinj _ _ (norm_nonneg _) (norm_nonneg _) (h1.trans h2.symm)
  have main : ∀ B : Matrix (Fin m) (Fin n) ℂ, (∀ i j, B i j = ((A i j : ℝ) : ℂ)) → ‖B‖ = ‖A‖ := by
    intro B hB
    have hmv : ∀ u : EuclideanSpace ℝ (Fin n),
        B.mulVec (fun j => ((u.ofLp j : ℝ) : ℂ)) = fun i => ((A.mulVec u.ofLp i : ℝ) : ℂ) := by
      intro u
      funext i
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_congr rfl (fun j _ => by rw [hB i j])]
      push_cast
      rfl
    refine le_antisymm ?_ ?_
    · refine key B ‖A‖ (hnn A) (fun z => ?_)
      set zr : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => (z.ofLp j).re) with hzrdef
      set zi : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => (z.ofLp j).im) with hzidef
      have hzr : ∀ j, zr.ofLp j = (z.ofLp j).re := fun j => by rw [hzrdef, WithLp.ofLp_toLp]
      have hzi : ∀ j, zi.ofLp j = (z.ofLp j).im := fun j => by rw [hzidef, WithLp.ofLp_toLp]
      have hzj : ∀ j, z.ofLp j = ((zr.ofLp j : ℝ) : ℂ) + ((zi.ofLp j : ℝ) : ℂ) * Complex.I := by
        intro j
        rw [hzr j, hzi j]
        exact (hreim (z.ofLp j).re (z.ofLp j).im).symm
      have hcoord : ∀ i, (B.mulVec z.ofLp) i
          = ((A.mulVec zr.ofLp) i : ℂ) + ((A.mulVec zi.ofLp) i : ℂ) * Complex.I := by
        intro i
        have hterm : ∀ j, B i j * z.ofLp j
            = ((A i j : ℝ) : ℂ) * ((zr.ofLp j : ℝ) : ℂ)
              + ((A i j : ℝ) : ℂ) * ((zi.ofLp j : ℝ) : ℂ) * Complex.I := by
          intro j
          rw [hB i j, hzj j]
          ring
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.sum_mul]
        push_cast
        rfl
      have hsqB : ‖(Matrix.toEuclideanLin B) z‖ ^ 2
          = ‖(Matrix.toEuclideanLin A) zr‖ ^ 2 + ‖(Matrix.toEuclideanLin A) zi‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [Matrix.ofLp_toEuclideanLin_apply]
        rw [hcoord i, hsplit, hsqR, hsqR]
      have hsqZ : ‖z‖ ^ 2 = ‖zr‖ ^ 2 + ‖zi‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hzr i, hzi i, hsqR, hsqR]
        exact hnc (z.ofLp i)
      have h3 : ‖(Matrix.toEuclideanLin A) zr‖ ^ 2 ≤ (‖A‖ * ‖zr‖) ^ 2 := by
        nlinarith [hbound A zr, norm_nonneg ((Matrix.toEuclideanLin A) zr),
          mul_nonneg (hnn A) (norm_nonneg zr)]
      have h4 : ‖(Matrix.toEuclideanLin A) zi‖ ^ 2 ≤ (‖A‖ * ‖zi‖) ^ 2 := by
        nlinarith [hbound A zi, norm_nonneg ((Matrix.toEuclideanLin A) zi),
          mul_nonneg (hnn A) (norm_nonneg zi)]
      have hA2 : (‖A‖ * ‖zr‖) ^ 2 + (‖A‖ * ‖zi‖) ^ 2 = (‖A‖ * ‖z‖) ^ 2 := by
        simp only [mul_pow]
        rw [hsqZ]
        ring
      have hmain : ‖(Matrix.toEuclideanLin B) z‖ ^ 2 ≤ (‖A‖ * ‖z‖) ^ 2 := by
        rw [hsqB]
        linarith [h3, h4, hA2]
      exact hsqle _ _ (norm_nonneg _) (mul_nonneg (hnn A) (norm_nonneg z)) hmain
    · refine key A ‖B‖ (hnn B) (fun u => ?_)
      set uC : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun j => ((u.ofLp j : ℝ) : ℂ)) with huCdef
      have hone : ‖(Matrix.toEuclideanLin A) u‖ = ‖(Matrix.toEuclideanLin B) uC‖ := by
        simp only [Matrix.toEuclideanLin_apply, huCdef, WithLp.ofLp_toLp, hmv u]
        exact (hnorm m (fun i => A.mulVec u.ofLp i)).symm
      have hnormu : ‖uC‖ = ‖u‖ := by
        rw [huCdef, hnorm n u.ofLp, WithLp.toLp_ofLp]
      rw [hone, ← hnormu]
      exact hbound B uC
  exact main (A.map (fun r : ℝ => (r : ℂ))) (fun i j => rfl)
  /- @proof-region region.target-node.session.6273921ccaaca9f8 end -/

end Statlib.Imported

