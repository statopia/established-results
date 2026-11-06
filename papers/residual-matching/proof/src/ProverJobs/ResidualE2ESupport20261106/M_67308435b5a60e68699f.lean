import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1840280243_8691960b : ∀ (d : ℕ) (a : ℝ) (p q : Fin d) (hpq : p ≠ q)
    (hB : (Matrix.diagonal
      (fun r : Fin d => ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ))).IsHermitian),
    (∑ k : Fin d, (hB.eigenvalues k) ^ ((3 : ℝ) / 2)) = 2 * |a| ^ (3 : ℕ) := by
  /- @proof-region region.target-node.session.a5172fbd6647744e begin -/
  intro d a p q hpq hB
  classical
  have hcp : (Matrix.diagonal (fun r : Fin d => ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ))).charpoly =
      ∏ r : Fin d, (Polynomial.X - Polynomial.C ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ)) :=
    Matrix.charpoly_diagonal _
  have hchar_ne : (Matrix.diagonal (fun r : Fin d => ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ))).charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hA : ∀ k : Fin d, hB.eigenvalues k = 0 ∨ hB.eigenvalues k = a ^ 2 := by
    intro k
    have hmem : ((hB.eigenvalues k : ℝ) : ℂ) ∈
        (Matrix.diagonal (fun r : Fin d => ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ))).charpoly.roots := by
      rw [Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hB]
      exact Multiset.mem_map.mpr ⟨k, Finset.mem_univ k, rfl⟩
    have hroot : (Matrix.diagonal (fun r : Fin d => ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ))).charpoly.IsRoot ((hB.eigenvalues k : ℝ) : ℂ) :=
      (Polynomial.mem_roots hchar_ne).mp hmem
    have heval : Polynomial.eval ((hB.eigenvalues k : ℝ) : ℂ)
        (Matrix.diagonal (fun r : Fin d => ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ))).charpoly = 0 := hroot
    rw [hcp] at heval
    rw [Polynomial.eval_prod] at heval
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
    obtain ⟨r, -, hr⟩ := Finset.prod_eq_zero_iff.mp heval
    have hrt : ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ)) = hB.eigenvalues k :=
      Complex.ofReal_injective (sub_eq_zero.mp hr).symm
    rw [← hrt]
    by_cases h : r = p ∨ r = q
    · right; rw [if_pos h]
    · left; rw [if_neg h]
  have hsplit : ∀ r : Fin d, ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ) =
      (if r = p then ((a ^ 2 : ℝ) : ℂ) else 0) + (if r = q then ((a ^ 2 : ℝ) : ℂ) else 0) := by
    intro r
    by_cases hp : r = p
    · by_cases hq : r = q
      · exact absurd (hp.symm.trans hq) hpq
      · subst hp; simp [hq]
    · by_cases hq : r = q
      · subst hq; simp [hp]
      · simp [hp, hq]
  have hsumA : ∑ r : Fin d, ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ) = ((2 * a ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun r _ => hsplit r), Finset.sum_add_distrib]
    have hp1 : ∑ r : Fin d, (if r = p then ((a ^ 2 : ℝ) : ℂ) else 0) = ((a ^ 2 : ℝ) : ℂ) := by
      rw [Finset.sum_ite_eq']
      simp
    have hq1 : ∑ r : Fin d, (if r = q then ((a ^ 2 : ℝ) : ℂ) else 0) = ((a ^ 2 : ℝ) : ℂ) := by
      rw [Finset.sum_ite_eq']
      simp
    rw [hp1, hq1]
    push_cast
    ring
  have htrace : (Matrix.diagonal (fun r : Fin d => ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ))).trace =
      ∑ k : Fin d, ((hB.eigenvalues k : ℝ) : ℂ) := Matrix.IsHermitian.trace_eq_sum_eigenvalues hB
  have htraceD : (Matrix.diagonal (fun r : Fin d => ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ))).trace =
      ∑ r : Fin d, ((if r = p ∨ r = q then a ^ 2 else 0 : ℝ) : ℂ) := Matrix.trace_diagonal _
  have hsumB : ∑ k : Fin d, hB.eigenvalues k = 2 * a ^ 2 := by
    have hcast : ((∑ k : Fin d, hB.eigenvalues k : ℝ) : ℂ) = ((2 * a ^ 2 : ℝ) : ℂ) := by
      have h1 : ((∑ k : Fin d, hB.eigenvalues k : ℝ) : ℂ) = ∑ k : Fin d, ((hB.eigenvalues k : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h1, ← htrace, htraceD, hsumA]
    exact Complex.ofReal_injective hcast
  have h3 : |a| ^ 3 = |a| * a ^ 2 := by
    rw [show (3:ℕ) = 2 + 1 by norm_num, pow_succ, sq_abs]
    ring
  have hrpow_sq : (a ^ 2 : ℝ) ^ ((3:ℝ)/2) = |a| * a ^ 2 := by
    rw [Real.rpow_div_two_eq_sqrt (r := 3) (sq_nonneg a), Real.sqrt_sq_eq_abs]
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    exact h3
  have hrpow : ∀ k : Fin d, (hB.eigenvalues k) ^ ((3:ℝ)/2) = |a| * hB.eigenvalues k := by
    intro k
    rcases hA k with h | h
    · rw [h, Real.zero_rpow (show ((3:ℝ)/2) ≠ 0 by norm_num), mul_zero]
    · rw [h, hrpow_sq]
  calc ∑ k : Fin d, (hB.eigenvalues k) ^ ((3:ℝ)/2)
      = ∑ k : Fin d, |a| * hB.eigenvalues k := Finset.sum_congr rfl (fun k _ => hrpow k)
    _ = |a| * ∑ k : Fin d, hB.eigenvalues k := by rw [Finset.mul_sum]
    _ = |a| * (2 * a ^ 2) := by rw [hsumB]
    _ = 2 * |a| ^ 3 := by rw [h3]; ring
  /- @proof-region region.target-node.session.a5172fbd6647744e end -/

end Statlib.Imported

