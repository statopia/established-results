import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix

open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_1013838252_0af447c5 : ∀ (m1 m2 : ℕ)
    (Sigma : Matrix (Fin m1 × Fin m2) (Fin m1 × Fin m2) ℝ)
    (hSigma : Sigma.PosDef),
    (∀ A : Matrix (Fin m1) (Fin m2) ℝ,
      (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2, vecOf A a * Sigma a b * vecOf A b) =
          secondMomentForm Sigma A ∧
        0 ≤ ∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
              vecOf A a * Sigma a b * vecOf A b) ∧
    (∀ Apr C A : Matrix (Fin m1) (Fin m2) ℝ,
      (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
          vecOf (Apr + C) a * Sigma a b * vecOf A b) =
        (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
            vecOf Apr a * Sigma a b * vecOf A b) +
          (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
            vecOf C a * Sigma a b * vecOf A b)) ∧
    (∀ (t : ℝ) (Apr A : Matrix (Fin m1) (Fin m2) ℝ),
      (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
          vecOf (t • Apr) a * Sigma a b * vecOf A b) =
        t * (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
              vecOf Apr a * Sigma a b * vecOf A b)) ∧
    (∀ Apr A C : Matrix (Fin m1) (Fin m2) ℝ,
      (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
          vecOf Apr a * Sigma a b * vecOf (A + C) b) =
        (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
            vecOf Apr a * Sigma a b * vecOf A b) +
          (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
            vecOf Apr a * Sigma a b * vecOf C b)) ∧
    (∀ (t : ℝ) (Apr A : Matrix (Fin m1) (Fin m2) ℝ),
      (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
          vecOf Apr a * Sigma a b * vecOf (t • A) b) =
        t * (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
              vecOf Apr a * Sigma a b * vecOf A b)) ∧
    (∀ Apr A : Matrix (Fin m1) (Fin m2) ℝ,
      (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
          vecOf Apr a * Sigma a b * vecOf A b) =
        (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
          vecOf A a * Sigma a b * vecOf Apr b)) ∧
    (∀ Apr A : Matrix (Fin m1) (Fin m2) ℝ,
      (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
          vecOf Apr a * Sigma a b * vecOf A b) =
        ∑ a : Fin m1 × Fin m2, vecOf Apr a * (Sigma.mulVec (vecOf A)) a) ∧
    (∀ A : Matrix (Fin m1) (Fin m2) ℝ,
      Real.sqrt (∑ a : Fin m1 × Fin m2, vecOf A a ^ 2) = frobNorm A) ∧
    (∀ (Mhat H : Matrix (Fin m1) (Fin m2) ℝ) (eps : ℝ),
      secondMomentForm Sigma (Mhat - eps • H) =
        secondMomentForm Sigma Mhat -
            2 * eps * (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
              vecOf Mhat a * Sigma a b * vecOf H b) +
          eps ^ 2 * secondMomentForm Sigma H) ∧
    (∀ Mhat Mbar H D : Matrix (Fin m1) (Fin m2) ℝ,
      (∀ i : Fin m1, ∀ j : Fin m2, (Mhat - Mbar) i j = (H + D) i j) →
        (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
            vecOf Mhat a * Sigma a b * vecOf H b) =
            (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
              vecOf Mbar a * Sigma a b * vecOf H b) +
              (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
                vecOf (H + D) a * Sigma a b * vecOf H b) ∧
          (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
              vecOf (H + D) a * Sigma a b * vecOf H b) =
            (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
              vecOf H a * Sigma a b * vecOf H b) +
              (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
                vecOf D a * Sigma a b * vecOf H b)) := by
  /- @proof-region region.target-node.session.4d380ba9cf2b9bd5 begin -/
  intro m1 m2 Sigma hSigma
  let B : Matrix (Fin m1) (Fin m2) ℝ → Matrix (Fin m1) (Fin m2) ℝ → ℝ :=
    fun A1 A2 => ∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
      vecOf A1 a * Sigma a b * vecOf A2 b
  have hgoal :
      (∀ A : Matrix (Fin m1) (Fin m2) ℝ, B A A = secondMomentForm Sigma A) ∧
      (∀ A : Matrix (Fin m1) (Fin m2) ℝ, 0 ≤ B A A) ∧
      (∀ A1 A2 A : Matrix (Fin m1) (Fin m2) ℝ, B (A1 + A2) A = B A1 A + B A2 A) ∧
      (∀ (c : ℝ) (A1 A : Matrix (Fin m1) (Fin m2) ℝ), B (c • A1) A = c * B A1 A) ∧
      (∀ A1 A2 A : Matrix (Fin m1) (Fin m2) ℝ, B A1 (A2 + A) = B A1 A2 + B A1 A) ∧
      (∀ (c : ℝ) (A1 A2 : Matrix (Fin m1) (Fin m2) ℝ), B A1 (c • A2) = c * B A1 A2) ∧
      (∀ A1 A2 : Matrix (Fin m1) (Fin m2) ℝ, B A1 A2 = B A2 A1) ∧
      (∀ A1 A2 : Matrix (Fin m1) (Fin m2) ℝ,
        B A1 A2 = ∑ a : Fin m1 × Fin m2, vecOf A1 a * (Sigma.mulVec (vecOf A2)) a) ∧
      (∀ A : Matrix (Fin m1) (Fin m2) ℝ,
        Real.sqrt (∑ a : Fin m1 × Fin m2, vecOf A a ^ 2) = frobNorm A) ∧
      (∀ (Mhat H : Matrix (Fin m1) (Fin m2) ℝ) (eps : ℝ),
        secondMomentForm Sigma (Mhat - eps • H) =
          secondMomentForm Sigma Mhat - 2 * eps * B Mhat H +
            eps ^ 2 * secondMomentForm Sigma H) ∧
      (∀ (Mhat Mbar H D : Matrix (Fin m1) (Fin m2) ℝ),
        (∀ (i : Fin m1) (j : Fin m2), (Mhat - Mbar) i j = (H + D) i j) →
          B Mhat H = B Mbar H + B (H + D) H ∧
            B (H + D) H = B H H + B D H) := by
    have hsymm : ∀ a b : Fin m1 × Fin m2, Sigma a b = Sigma b a := by
      intro a b
      have h := hSigma.isHermitian.apply a b
      simpa using h.symm
    have hmv : ∀ (M : Matrix (Fin m1 × Fin m2) (Fin m1 × Fin m2) ℝ)
        (v : Fin m1 × Fin m2 → ℝ), M.mulVec v = fun a => ∑ b, M a b * v b := by
      intro M v
      funext a
      rfl
    have hB : ∀ A1 A2 : Matrix (Fin m1) (Fin m2) ℝ,
        B A1 A2 = ∑ a : Fin m1 × Fin m2, vecOf A1 a * (Sigma.mulVec (vecOf A2)) a := by
      intro A1 A2
      dsimp only [B]
      rw [hmv Sigma (vecOf A2)]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    have hqq : ∀ X : Matrix (Fin m1) (Fin m2) ℝ, secondMomentForm Sigma X = B X X :=
      fun X => rfl
    have hadd1 : ∀ A1 A2 A : Matrix (Fin m1) (Fin m2) ℝ,
        B (A1 + A2) A = B A1 A + B A2 A := by
      intro A1 A2 A
      dsimp only [B]
      simp only [vecOf, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    have hsmul1 : ∀ (c : ℝ) (A1 A : Matrix (Fin m1) (Fin m2) ℝ),
        B (c • A1) A = c * B A1 A := by
      intro c A1 A
      dsimp only [B]
      simp only [vecOf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    have hadd2 : ∀ A1 A2 A : Matrix (Fin m1) (Fin m2) ℝ,
        B A1 (A2 + A) = B A1 A2 + B A1 A := by
      intro A1 A2 A
      dsimp only [B]
      simp only [vecOf, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
    have hsmul2 : ∀ (c : ℝ) (A1 A2 : Matrix (Fin m1) (Fin m2) ℝ),
        B A1 (c • A2) = c * B A1 A2 := by
      intro c A1 A2
      dsimp only [B]
      simp only [vecOf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    have hsym : ∀ A1 A2 : Matrix (Fin m1) (Fin m2) ℝ, B A1 A2 = B A2 A1 := by
      intro A1 A2
      dsimp only [B]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      rw [hsymm y x]
      ring
    have hneg1 : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ, B (-X) Y = -B X Y := by
      intro X Y
      simpa using hsmul1 (-1) X Y
    have hneg2 : ∀ X Y : Matrix (Fin m1) (Fin m2) ℝ, B X (-Y) = -B X Y := by
      intro X Y
      simpa using hsmul2 (-1) X Y
    have hnonneg : ∀ A : Matrix (Fin m1) (Fin m2) ℝ, 0 ≤ B A A := by
      intro A
      have hBA : B A A = vecOf A ⬝ᵥ Sigma.mulVec (vecOf A) := by
        rw [hB A A]
        rfl
      rw [hBA]
      have hstar : star (vecOf A) = vecOf A := by
        funext i
        simp
      have h := hSigma.posSemidef.dotProduct_mulVec_nonneg (vecOf A)
      rw [hstar] at h
      exact h
    have hnorm : ∀ A : Matrix (Fin m1) (Fin m2) ℝ,
        Real.sqrt (∑ a : Fin m1 × Fin m2, vecOf A a ^ 2) = frobNorm A := by
      intro A
      simp only [frobNorm]
      congr 1
      rw [Fintype.sum_prod_type]
      rfl
    have hquad : ∀ P Q : Matrix (Fin m1) (Fin m2) ℝ,
        B (P - Q) (P - Q) = B P P - 2 * B P Q + B Q Q := by
      intro P Q
      rw [sub_eq_add_neg]
      simp only [hadd1, hadd2, hneg1, hneg2]
      rw [hsym Q P]
      ring
    refine ⟨fun A => rfl, hnonneg, hadd1, hsmul1, hadd2, hsmul2, hsym, hB, hnorm, ?_, ?_⟩
    · intro Mhat H eps
      simp only [hqq]
      rw [hquad Mhat (eps • H)]
      rw [hsmul2 eps Mhat H, hsmul1 eps H (eps • H), hsmul2 eps H H]
      ring
    · intro Mhat Mbar H D h
      have hMD : Mhat - Mbar = H + D := by
        ext i j
        exact h i j
      have hM : Mhat = Mbar + (H + D) := by
        rw [← hMD]
        abel
      refine ⟨?_, ?_⟩
      · rw [hM, hadd1]
      · rw [hadd1]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hgoal
  exact ⟨fun A => ⟨h1 A, h2 A⟩, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

  /- @proof-region region.target-node.session.4d380ba9cf2b9bd5 end -/

end Statlib.Imported

