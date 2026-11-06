import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_db83446827638fb9ceb4
import ProverJobs.ResidualE2ESupport20261106.M_d346a3d12a13a42d1732

namespace PaperProofTasks.ResidualE2ESupport20261106


run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2390824386_f5f4c323 : ∀ (m n r : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
    (mu0 : ℝ)
    (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (hU : U0.transpose * U0 = 1) (hV : V0.transpose * V0 = 1)
    (hmu : 0 ≤ mu0 * (r : ℝ))
    (hrowU : rowNorm U0 ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)))
    (hrowV : rowNorm V0 ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)))
    (D : ℕ) (b : Fin D → Matrix (Fin m) (Fin n) ℝ)
    (hb_orth : ∀ p q : Fin D, frobInner (b p) (b q) = (if p = q then (1 : ℝ) else 0))
    (hb_mem : ∀ p : Fin D, MemTangentRect U0 V0 (b p))
    (hb_span : ∀ Y : Matrix (Fin m) (Fin n) ℝ, MemTangentRect U0 V0 Y →
      ∃ c : Fin D → ℝ, Y = ∑ p : Fin D, c p • b p)
    (z : Fin m → Fin n → Matrix (Fin m) (Fin n) ℝ)
    (hz_mem : ∀ (i : Fin m) (j : Fin n), MemTangentRect U0 V0 (z i j))
    (hz_orth : ∀ (i : Fin m) (j : Fin n) (Y : Matrix (Fin m) (Fin n) ℝ),
      MemTangentRect U0 V0 Y → frobInner (matrixUnit i j) Y = frobInner (z i j) Y),
    (∀ (i : Fin m) (j : Fin n),
        frobNorm (z i j) ≤
          Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) + Real.sqrt (mu0 * (r : ℝ) / (n : ℝ))) ∧
    (∀ (i : Fin m) (j : Fin n),
        frobNorm (z i j) ^ 2 ≤
          2 * (mu0 * (r : ℝ) / (m : ℝ) + mu0 * (r : ℝ) / (n : ℝ))) ∧
    (∀ (i : Fin m) (j : Fin n), frobNorm (z i j) ^ 2 ≤ 4 * mu0 * (r : ℝ) / (n : ℝ)) ∧
    (∀ (i : Fin m) (j : Fin n),
        Real.sqrt (∑ p : Fin D, (tangentCoords b i j p) ^ 2) = frobNorm (z i j)) ∧
    (∀ (i : Fin m) (j : Fin n),
        (∑ p : Fin D, (tangentCoords b i j p) ^ 2) ≤ 4 * mu0 * (r : ℝ) / (n : ℝ)) ∧
    ((⨆ i : Fin m, ⨆ j : Fin n, (∑ p : Fin D, (tangentCoords b i j p) ^ 2))
        ≤ 4 * mu0 * (r : ℝ) / (n : ℝ)) ∧
    ((∑ i : Fin m, ∑ j : Fin n,
        (fun p q : Fin D => tangentCoords b i j p * tangentCoords b i j q))
        = (1 : Matrix (Fin D) (Fin D) ℝ)) ∧
    (D ≤ r * (m + n)) ∧
    (D ≤ m * n) := by
  /- @proof-region region.target-node.session.cc124dc7b5407813 begin -/
  intro m n r hm hn hmn mu0 U0 V0 hU hV hmu hrowU hrowV D b hb_orth hb_mem hb_span z hz_mem hz_orth
  have hA : ∀ (i : Fin m) (j : Fin n),
      frobNorm (z i j) ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) +
        Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) := by
    intro i j
    exact statopia_math_node_2051336761_98c59cdc m n r mu0 U0 V0 i j (z i j) hm hn hU hV hmu
      hrowU hrowV (hz_mem i j) (hz_orth i j)
  have hD : ∀ (i : Fin m) (j : Fin n),
      Real.sqrt (∑ p : Fin D, (tangentCoords b i j p) ^ 2) = frobNorm (z i j) := by
    intro i j
    have htr : ∀ (A B : Matrix (Fin m) (Fin n) ℝ),
        frobInner A B = (A * B.transpose).trace := by
      intro A B
      simp [frobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    have hsymm : ∀ (A B : Matrix (Fin m) (Fin n) ℝ), frobInner A B = frobInner B A := by
      intro A B
      simp only [frobInner]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b' _ => mul_comm _ _))
    have hlin : ∀ (a : Fin D → ℝ) (W : Matrix (Fin m) (Fin n) ℝ),
        frobInner (∑ p, a p • b p) W = ∑ p, a p * frobInner (b p) W := by
      intro a W
      have hs : frobInner (∑ p, a p • b p) W = ∑ p, frobInner (a p • b p) W := by
        conv_lhs => rw [htr]
        rw [Matrix.sum_mul, Matrix.trace_sum]
        exact Finset.sum_congr rfl (fun p _ => (htr (a p • b p) W).symm)
      rw [hs]
      exact Finset.sum_congr rfl (fun p _ => by
        conv_lhs => rw [htr]
        rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← htr])
    have hlinR : ∀ (a : Fin D → ℝ) (W : Matrix (Fin m) (Fin n) ℝ),
        frobInner W (∑ p, a p • b p) = ∑ p, a p * frobInner W (b p) := by
      intro a W
      rw [hsymm W (∑ p, a p • b p), hlin a W]
      exact Finset.sum_congr rfl (fun p _ => by rw [hsymm (b p) W])
    obtain ⟨c, hc⟩ := hb_span (z i j) (hz_mem i j)
    have hcoeff : ∀ p, c p = b p i j := by
      intro p
      have h1 : frobInner (z i j) (b p) = c p := by
        rw [hc, hlin]
        simp only [hb_orth]
        simp
      have h2 : frobInner (z i j) (b p) = b p i j := by
        rw [← hz_orth i j (b p) (hb_mem p)]
        simp only [frobInner, matrixUnit]
        rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single j]
          · simp
          · intro b' _ hb'; simp [hb']
          · intro hj; exact absurd (Finset.mem_univ j) hj
        · intro a _ ha
          apply Finset.sum_eq_zero
          intro b' _
          simp [ha]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [← h1]
      exact h2
    have hnorm : frobNorm (z i j) ^ 2 = frobInner (z i j) (z i j) := by
      rw [frobNorm, Real.sq_sqrt (by positivity)]
      simp only [frobInner]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b' _
      ring
    have hparseval : frobInner (z i j) (z i j) = ∑ p, (b p i j) ^ 2 := by
      rw [hc, hlin]
      apply Finset.sum_congr rfl
      intro p _
      rw [hlinR]
      have hsum : ∑ q : Fin D, c q * frobInner (b p) (b q) = c p := by
        simp only [hb_orth]
        rw [Finset.sum_eq_single p]
        · rw [if_pos rfl, mul_one]
        · intro q _ hq; rw [if_neg (Ne.symm hq), mul_zero]
        · intro hp; exact absurd (Finset.mem_univ p) hp
      rw [hsum, hcoeff p]
      ring
    have hsq : ∑ p : Fin D, (tangentCoords b i j p) ^ 2 = frobNorm (z i j) ^ 2 := by
      simp only [tangentCoords]
      rw [← hparseval, ← hnorm]
    have hnn : (0 : ℝ) ≤ frobNorm (z i j) := Real.sqrt_nonneg _
    rw [hsq, Real.sqrt_sq hnn]
  have hB : ∀ (i : Fin m) (j : Fin n),
      frobNorm (z i j) ^ 2 ≤
        2 * (mu0 * (r : ℝ) / (m : ℝ) + mu0 * (r : ℝ) / (n : ℝ)) := by
    intro i j
    have hnn : (0 : ℝ) ≤ frobNorm (z i j) := Real.sqrt_nonneg _
    have h1 := hA i j
    have ha0 : (0 : ℝ) ≤ mu0 * (r : ℝ) / (m : ℝ) := div_nonneg hmu (by positivity)
    have hb0 : (0 : ℝ) ≤ mu0 * (r : ℝ) / (n : ℝ) := div_nonneg hmu (by positivity)
    have hXn : (0 : ℝ) ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) + Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq : frobNorm (z i j) ^ 2 ≤
        (Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) + Real.sqrt (mu0 * (r : ℝ) / (n : ℝ))) ^ 2 := by
      have hdiff : (0 : ℝ) ≤
          Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) + Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) -
            frobNorm (z i j) := by linarith
      have hsum : (0 : ℝ) ≤
          Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) + Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) +
            frobNorm (z i j) := by linarith
      nlinarith [mul_nonneg hdiff hsum]
    have hsqrt :
        (Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) + Real.sqrt (mu0 * (r : ℝ) / (n : ℝ))) ^ 2 ≤
          2 * (mu0 * (r : ℝ) / (m : ℝ) + mu0 * (r : ℝ) / (n : ℝ)) := by
      nlinarith [Real.sq_sqrt ha0, Real.sq_sqrt hb0,
        Real.sqrt_nonneg (mu0 * (r : ℝ) / (m : ℝ)),
        Real.sqrt_nonneg (mu0 * (r : ℝ) / (n : ℝ)),
        sq_nonneg (Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) - Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)))]
    linarith
  have hC : ∀ (i : Fin m) (j : Fin n), frobNorm (z i j) ^ 2 ≤ 4 * mu0 * (r : ℝ) / (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hAleB : mu0 * (r : ℝ) / (m : ℝ) ≤ mu0 * (r : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_left hmu hnpos (by exact_mod_cast hmn)
    intro i j
    have h2 : 2 * (mu0 * (r : ℝ) / (m : ℝ) + mu0 * (r : ℝ) / (n : ℝ)) ≤
        4 * mu0 * (r : ℝ) / (n : ℝ) := by
      have key : 4 * mu0 * (r : ℝ) / (n : ℝ) = 4 * (mu0 * (r : ℝ) / (n : ℝ)) := by ring
      rw [key]
      nlinarith [hAleB]
    linarith [hB i j, h2]
  have hE : ∀ (i : Fin m) (j : Fin n),
      (∑ p : Fin D, (tangentCoords b i j p) ^ 2) ≤ 4 * mu0 * (r : ℝ) / (n : ℝ) := by
    intro i j
    have hsq : (∑ p : Fin D, (tangentCoords b i j p) ^ 2) = frobNorm (z i j) ^ 2 := by
      rw [← hD i j, Real.sq_sqrt (by positivity)]
    rw [hsq]
    exact hC i j
  have hF : (⨆ i : Fin m, ⨆ j : Fin n, (∑ p : Fin D, (tangentCoords b i j p) ^ 2))
      ≤ 4 * mu0 * (r : ℝ) / (n : ℝ) := by
    haveI hmne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    haveI hnne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    apply ciSup_le
    intro i
    apply ciSup_le
    intro j
    exact hE i j
  have hG : (∑ i : Fin m, ∑ j : Fin n,
      Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j) : Matrix (Fin D) (Fin D) ℝ) = 1 := by
    ext p q
    have key :
        (∑ i : Fin m, ∑ j : Fin n,
            Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)) p q
          = frobInner (b p) (b q) := by
      simp [frobInner, Matrix.sum_apply, Matrix.vecMulVec, tangentCoords]
    rw [key, hb_orth p q]
    simp [Matrix.one_apply]
  have hH : D ≤ r * (m + n) :=
    (statopia_math_node_2263768880_be0f4d53 m n r D U0 V0 b hb_orth hb_mem).1
  have hI : D ≤ m * n :=
    (statopia_math_node_2263768880_be0f4d53 m n r D U0 V0 b hb_orth hb_mem).2
  refine ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩
  /- @proof-region region.target-node.session.cc124dc7b5407813 end -/

end

end Statlib.Imported

