import Lean
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Vocabulary
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Base
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_283558168_72fffefb_dab35fce
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_3099734836_21621514_eff5fc6b

namespace PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5


open scoped BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported

noncomputable section
open scoped BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1216269461_011b141c : ∀ (p : ℕ) (hp : 0 < p) (beta : ℝ) (hbeta : 0 < beta)
    (phi : ℝ) (hphi : 1 ≤ phi) (y : Fin p → ℝ)
    (d1 d2 d3 : ℝ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (C2 : ℝ)
    (hC2 : phi ^ 3 + phi ^ 2 * beta + phi * beta ^ 2 ≤ C2 * (phi * beta ^ 2)),
    let C1 : ℝ := max (max 1 d3) (max (6 * d2) (6 * d1))
    let Z : (Fin p → ℝ) → ℝ := fun w => ∑ m : Fin p, Real.exp (beta * (w m - y m))
    let pi : (Fin p → ℝ) → Fin p → ℝ :=
      fun w j => Real.exp (beta * (w j - y j)) / Z w
    let W : (Fin p → ℝ) → Fin p → Fin p → ℝ :=
      fun w j k => pi w j * (if j = k then (1 : ℝ) else 0) + pi w j * pi w k
    let P : (Fin p → ℝ) → Fin p → Fin p → Fin p → ℝ :=
      fun w j k l =>
        pi w j * (if j = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)
        + pi w j * pi w l * (if j = k then (1 : ℝ) else 0)
        + pi w j * pi w k * (if j = l then (1 : ℝ) else 0)
        + pi w j * pi w k * (if k = l then (1 : ℝ) else 0)
        + 2 * pi w j * pi w k * pi w l
    let Q : (Fin p → ℝ) → Fin p → Fin p → Fin p → ℝ :=
      fun w j k l =>
        phi ^ 3 * d3 * pi w j * pi w k * pi w l
        + phi ^ 2 * d2 * beta *
            (W w j k * pi w l + W w j l * pi w k + W w k l * pi w j)
        + phi * d1 * beta ^ 2 * P w j k l
    1 ≤ C1 ∧
      (∀ w : Fin p → ℝ,
        ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, Q w a b c
          = phi ^ 3 * d3 + 6 * phi ^ 2 * d2 * beta + 6 * phi * d1 * beta ^ 2) ∧
      (∀ w : Fin p → ℝ,
        (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, Q w a b c)
          ≤ C1 * (phi ^ 3 + phi ^ 2 * beta + phi * beta ^ 2)) ∧
      (∀ w : Fin p → ℝ,
        (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, Q w a b c)
          ≤ C1 * C2 * (phi * beta ^ 2)) := by
  /- @proof-region region.target-node.session.23bb33a965d770cd begin -/
  intro p hp beta hbeta phi hphi y d1 d2 d3 hd1 hd2 hd3 C2 hC2
  have hsoft := statopia_math_node_283558168_72fffefb p hp beta hbeta y
  have hsum1 : ∀ w : Fin p → ℝ,
      (∑ j : Fin p, Real.exp (beta * (w j - y j)) / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) = 1 :=
    fun w => (hsoft.2 w).2.2.1
  have hphi0 : (0 : ℝ) ≤ phi := by linarith
  have hbeta0 : (0 : ℝ) ≤ beta := le_of_lt hbeta
  have hp3 : (0 : ℝ) ≤ phi ^ 3 := pow_nonneg hphi0 3
  have hp2 : (0 : ℝ) ≤ phi ^ 2 * beta := mul_nonneg (pow_nonneg hphi0 2) hbeta0
  have hp1 : (0 : ℝ) ≤ phi * beta ^ 2 := mul_nonneg hphi0 (pow_nonneg hbeta0 2)
  have hCn : (0 : ℝ) ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) :=
    le_trans zero_le_one (le_trans (le_max_left 1 d3) (le_max_left _ _))
  have hgen : ∀ (π : Fin p → ℝ), (∑ j : Fin p, π j) = 1 →
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
          (phi ^ 3 * d3 * π a * π b * π c
            + phi ^ 2 * d2 * beta *
                ((π a * (if a = b then (1 : ℝ) else 0) + π a * π b) * π c
                  + (π a * (if a = c then (1 : ℝ) else 0) + π a * π c) * π b
                  + (π b * (if b = c then (1 : ℝ) else 0) + π b * π c) * π a)
            + phi * d1 * beta ^ 2 *
                (π a * (if a = c then (1 : ℝ) else 0) * (if a = b then (1 : ℝ) else 0)
                  + π a * π c * (if a = b then (1 : ℝ) else 0)
                  + π a * π b * (if a = c then (1 : ℝ) else 0)
                  + π a * π b * (if b = c then (1 : ℝ) else 0)
                  + 2 * π a * π b * π c))) =
        phi ^ 3 * d3 + 6 * phi ^ 2 * d2 * beta + 6 * phi * d1 * beta ^ 2 := by
    intro π hπ
    have pull : ∀ (c : ℝ) (f : Fin p → ℝ), (∑ i : Fin p, c * f i) = c * (∑ i : Fin p, f i) := by
      intro c f
      simp only [Finset.mul_sum]
    have hD : ∀ a : Fin p, (∑ b : Fin p, (if a = b then (1 : ℝ) else 0)) = 1 := by
      intro a
      have h : (∑ b : Fin p, (if a = b then (1 : ℝ) else 0))
          = (if a = a then (1 : ℝ) else 0) := by
        apply Finset.sum_eq_single a
        · intro b _ hb
          simp [hb.symm]
        · intro ha
          simp at ha
      rw [h]
      simp
    have hπmul : ∀ a : Fin p, (∑ b : Fin p, π a * π b) = π a := by
      intro a
      simp only [pull, hπ, mul_one]
    have hδmul : ∀ a : Fin p, (∑ b : Fin p, π a * (if a = b then (1 : ℝ) else 0)) = π a := by
      intro a
      simp only [pull, hD, mul_one]
    have triple_pull : ∀ (K : ℝ) (f : Fin p → Fin p → Fin p → ℝ),
        (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, K * f a b c)
          = K * (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, f a b c) := by
      intro K f
      simp only [Finset.mul_sum]
    have hA : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, phi ^ 3 * d3 * π a * π b * π c)
        = phi ^ 3 * d3 := by
      have s1 : ∀ a b : Fin p, (∑ c : Fin p, phi ^ 3 * d3 * π a * π b * π c)
          = phi ^ 3 * d3 * π a * π b := by
        intro a b
        simp only [pull, hπ, mul_one]
      have s2 : ∀ a : Fin p, (∑ b : Fin p, phi ^ 3 * d3 * π a * π b) = phi ^ 3 * d3 * π a := by
        intro a
        simp only [pull, hπ, mul_one]
      simp only [s1, s2, pull, hπ, mul_one]
    have hB1 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
        phi ^ 2 * d2 * beta * ((π a * (if a = b then (1 : ℝ) else 0) + π a * π b) * π c))
        = 2 * (phi ^ 2 * d2 * beta) := by
      have h0 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
          (π a * (if a = b then (1 : ℝ) else 0) + π a * π b) * π c) = 2 := by
        have s1 : ∀ a b : Fin p,
            (∑ c : Fin p, (π a * (if a = b then (1 : ℝ) else 0) + π a * π b) * π c)
              = (π a * (if a = b then (1 : ℝ) else 0) + π a * π b) := by
          intro a b
          simp only [pull, hπ, mul_one]
        have s2 : ∀ a : Fin p,
            (∑ b : Fin p, (π a * (if a = b then (1 : ℝ) else 0) + π a * π b)) = 2 * π a := by
          intro a
          simp only [Finset.sum_add_distrib, pull, hD, hπ, mul_one]
          ring
        simp only [s1, s2, pull, hπ, mul_one]
      rw [triple_pull, h0]
      ring
    have hB2 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
        phi ^ 2 * d2 * beta * ((π a * (if a = c then (1 : ℝ) else 0) + π a * π c) * π b))
        = 2 * (phi ^ 2 * d2 * beta) := by
      have h0 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
          (π a * (if a = c then (1 : ℝ) else 0) + π a * π c) * π b) = 2 := by
        have s1 : ∀ a b : Fin p,
            (∑ c : Fin p, (π a * (if a = c then (1 : ℝ) else 0) + π a * π c) * π b)
              = 2 * π a * π b := by
          intro a b
          rw [← Finset.sum_mul]
          simp only [Finset.sum_add_distrib, pull, hD, hπ, mul_one]
          ring
        have s2 : ∀ a : Fin p, (∑ b : Fin p, 2 * π a * π b) = 2 * π a := by
          intro a
          simp only [pull, hπ, mul_one]
        simp only [s1, s2, pull, hπ, mul_one]
      rw [triple_pull, h0]
      ring
    have hB3 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
        phi ^ 2 * d2 * beta * ((π b * (if b = c then (1 : ℝ) else 0) + π b * π c) * π a))
        = 2 * (phi ^ 2 * d2 * beta) := by
      have h0 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
          (π b * (if b = c then (1 : ℝ) else 0) + π b * π c) * π a) = 2 := by
        have s1 : ∀ a b : Fin p,
            (∑ c : Fin p, (π b * (if b = c then (1 : ℝ) else 0) + π b * π c) * π a)
              = 2 * π b * π a := by
          intro a b
          rw [← Finset.sum_mul]
          simp only [Finset.sum_add_distrib, pull, hD, hπ, mul_one]
          ring
        have s2 : ∀ a : Fin p, (∑ b : Fin p, 2 * π b * π a) = 2 * π a := by
          intro a
          rw [← Finset.sum_mul]
          simp only [pull, hπ, mul_one]
        simp only [s1, s2, pull, hπ, mul_one]
      rw [triple_pull, h0]
      ring
    have hC1 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
        phi * d1 * beta ^ 2 * (π a * (if a = c then (1 : ℝ) else 0) * (if a = b then (1 : ℝ) else 0)))
        = phi * d1 * beta ^ 2 := by
      have h0 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
          π a * (if a = c then (1 : ℝ) else 0) * (if a = b then (1 : ℝ) else 0)) = 1 := by
        have s1 : ∀ a b : Fin p,
            (∑ c : Fin p, π a * (if a = c then (1 : ℝ) else 0) * (if a = b then (1 : ℝ) else 0))
              = π a * (if a = b then (1 : ℝ) else 0) := by
          intro a b
          rw [← Finset.sum_mul]
          simp only [hδmul]
        simp only [s1, hδmul, hπ]
      rw [triple_pull, h0]
      ring
    have hC2 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
        phi * d1 * beta ^ 2 * (π a * π c * (if a = b then (1 : ℝ) else 0)))
        = phi * d1 * beta ^ 2 := by
      have h0 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
          π a * π c * (if a = b then (1 : ℝ) else 0)) = 1 := by
        have s1 : ∀ a b : Fin p,
            (∑ c : Fin p, π a * π c * (if a = b then (1 : ℝ) else 0))
              = π a * (if a = b then (1 : ℝ) else 0) := by
          intro a b
          have e : ∀ c : Fin p, π a * π c * (if a = b then (1 : ℝ) else 0)
              = (π a * (if a = b then (1 : ℝ) else 0)) * π c := by
            intro c
            ring
          simp only [e, pull, hπ, mul_one]
        simp only [s1, hδmul, hπ]
      rw [triple_pull, h0]
      ring
    have hC3 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
        phi * d1 * beta ^ 2 * (π a * π b * (if a = c then (1 : ℝ) else 0)))
        = phi * d1 * beta ^ 2 := by
      have h0 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
          π a * π b * (if a = c then (1 : ℝ) else 0)) = 1 := by
        have s1 : ∀ a b : Fin p,
            (∑ c : Fin p, π a * π b * (if a = c then (1 : ℝ) else 0)) = π a * π b := by
          intro a b
          simp only [pull, hD, mul_one]
        simp only [s1, hπmul, hπ]
      rw [triple_pull, h0]
      ring
    have hC4 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
        phi * d1 * beta ^ 2 * (π a * π b * (if b = c then (1 : ℝ) else 0)))
        = phi * d1 * beta ^ 2 := by
      have h0 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
          π a * π b * (if b = c then (1 : ℝ) else 0)) = 1 := by
        have s1 : ∀ a b : Fin p,
            (∑ c : Fin p, π a * π b * (if b = c then (1 : ℝ) else 0)) = π a * π b := by
          intro a b
          simp only [pull, hD, mul_one]
        simp only [s1, hπmul, hπ]
      rw [triple_pull, h0]
      ring
    have hC5 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
        phi * d1 * beta ^ 2 * (2 * π a * π b * π c))
        = 2 * (phi * d1 * beta ^ 2) := by
      have h0 : (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, 2 * π a * π b * π c) = 2 := by
        have s1 : ∀ a b : Fin p, (∑ c : Fin p, 2 * π a * π b * π c) = 2 * π a * π b := by
          intro a b
          simp only [pull, hπ, mul_one]
        have s2 : ∀ a : Fin p, (∑ b : Fin p, 2 * π a * π b) = 2 * π a := by
          intro a
          simp only [pull, hπ, mul_one]
        simp only [s1, s2, pull, hπ, mul_one]
      rw [triple_pull, h0]
      ring
    simp only [mul_add, Finset.sum_add_distrib]
    simp only [hA, hB1, hB2, hB3, hC1, hC2, hC3, hC4, hC5]
    ring
  have hstep : phi ^ 3 * d3 + 6 * phi ^ 2 * d2 * beta + 6 * phi * d1 * beta ^ 2
      ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) * (phi ^ 3 + phi ^ 2 * beta + phi * beta ^ 2) := by
    have h1 : d3 ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) :=
      le_trans (le_max_right 1 d3) (le_max_left _ _)
    have h2 : 6 * d2 ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) :=
      le_trans (le_max_left (6 * d2) (6 * d1)) (le_max_right _ _)
    have h3 : 6 * d1 ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) :=
      le_trans (le_max_right (6 * d2) (6 * d1)) (le_max_right _ _)
    have e1 : phi ^ 3 * d3 ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) * phi ^ 3 := by
      have h := mul_le_mul_of_nonneg_left h1 hp3
      calc phi ^ 3 * d3 ≤ phi ^ 3 * max (max 1 d3) (max (6 * d2) (6 * d1)) := h
        _ = max (max 1 d3) (max (6 * d2) (6 * d1)) * phi ^ 3 := by ring
    have e2 : 6 * phi ^ 2 * d2 * beta ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) * (phi ^ 2 * beta) := by
      have h := mul_le_mul_of_nonneg_left h2 hp2
      calc 6 * phi ^ 2 * d2 * beta = phi ^ 2 * beta * (6 * d2) := by ring
        _ ≤ phi ^ 2 * beta * max (max 1 d3) (max (6 * d2) (6 * d1)) := h
        _ = max (max 1 d3) (max (6 * d2) (6 * d1)) * (phi ^ 2 * beta) := by ring
    have e3 : 6 * phi * d1 * beta ^ 2 ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) * (phi * beta ^ 2) := by
      have h := mul_le_mul_of_nonneg_left h3 hp1
      calc 6 * phi * d1 * beta ^ 2 = phi * beta ^ 2 * (6 * d1) := by ring
        _ ≤ phi * beta ^ 2 * max (max 1 d3) (max (6 * d2) (6 * d1)) := h
        _ = max (max 1 d3) (max (6 * d2) (6 * d1)) * (phi * beta ^ 2) := by ring
    calc phi ^ 3 * d3 + 6 * phi ^ 2 * d2 * beta + 6 * phi * d1 * beta ^ 2
        ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) * phi ^ 3
            + max (max 1 d3) (max (6 * d2) (6 * d1)) * (phi ^ 2 * beta)
            + max (max 1 d3) (max (6 * d2) (6 * d1)) * (phi * beta ^ 2) := by
          exact add_le_add (add_le_add e1 e2) e3
      _ = max (max 1 d3) (max (6 * d2) (6 * d1)) * (phi ^ 3 + phi ^ 2 * beta + phi * beta ^ 2) := by
          ring
  have hstep2 : phi ^ 3 * d3 + 6 * phi ^ 2 * d2 * beta + 6 * phi * d1 * beta ^ 2
      ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) * C2 * (phi * beta ^ 2) := by
    refine le_trans hstep ?_
    calc max (max 1 d3) (max (6 * d2) (6 * d1)) * (phi ^ 3 + phi ^ 2 * beta + phi * beta ^ 2)
        ≤ max (max 1 d3) (max (6 * d2) (6 * d1)) * (C2 * (phi * beta ^ 2)) :=
          mul_le_mul_of_nonneg_left hC2 hCn
      _ = max (max 1 d3) (max (6 * d2) (6 * d1)) * C2 * (phi * beta ^ 2) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left 1 d3) (le_max_left _ _)
  · intro w
    exact hgen (fun j => Real.exp (beta * (w j - y j)) / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) (hsum1 w)
  · intro w
    exact le_trans (le_of_eq (hgen (fun j => Real.exp (beta * (w j - y j)) / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) (hsum1 w))) hstep
  · intro w
    exact le_trans (le_of_eq (hgen (fun j => Real.exp (beta * (w j - y j)) / (∑ m : Fin p, Real.exp (beta * (w m - y m)))) (hsum1 w))) hstep2
  /- @proof-region region.target-node.session.23bb33a965d770cd end -/

end Statlib.Imported
end

