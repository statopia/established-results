import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_67308435b5a60e68699f

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
theorem statopia_math_node_3460908849_468d1fc0 : ∀ (d : ℕ) (a : ℝ) (p q : Fin d) (hpq : p ≠ q),
    let Z : Matrix (Fin d) (Fin d) ℂ :=
      fun r s => if (r = p ∧ s = q) ∨ (r = q ∧ s = p) then (a : ℂ) else 0
    ((d : ℝ)⁻¹) * (∑ k : Fin d,
      (((Matrix.isHermitian_conjTranspose_mul_self Z).eigenvalues k) ^ ((3 : ℝ) / 2)))
      ≤ 2 * |a| ^ 3 / (d : ℝ) := by
  /- @proof-region region.target-node.session.e760892db2f4303d begin -/
  intro d a p q hpq
  dsimp only
  set Z : Matrix (Fin d) (Fin d) ℂ :=
    fun r s => if (r = p ∧ s = q) ∨ (r = q ∧ s = p) then (a : ℂ) else 0
  set c : Fin d → ℝ := fun r => if r = p ∨ r = q then a ^ 2 else 0 with hcdef
  have hZZ : Z.conjTranspose * Z = Matrix.diagonal (fun r => ((c r : ℝ) : ℂ)) := by
    have hZdef : ∀ r s : Fin d,
        Z r s = (if (r = p ∧ s = q) ∨ (r = q ∧ s = p) then (a : ℂ) else 0) := fun r s => rfl
    have hstar : ∀ t r : Fin d, star (Z t r) = Z t r := by
      intro t r
      rw [hZdef t r]
      by_cases h : (t = p ∧ r = q) ∨ (t = q ∧ r = p)
      · rw [if_pos h]
        simpa using Complex.conj_ofReal a
      · rw [if_neg h]
        simp
    have hp : ∀ x : Fin d, Z p x = (if x = q then (a : ℂ) else 0) := by
      intro x
      rw [hZdef p x]
      by_cases h : x = q
      · rw [if_pos (Or.inl ⟨rfl, h⟩), if_pos h]
      · have hc : ¬ ((p = p ∧ x = q) ∨ (p = q ∧ x = p)) := by
          rintro (⟨-, h1⟩ | ⟨h1, -⟩)
          · exact h h1
          · exact hpq h1
        rw [if_neg hc, if_neg h]
    have hq : ∀ x : Fin d, Z q x = (if x = p then (a : ℂ) else 0) := by
      intro x
      rw [hZdef q x]
      by_cases h : x = p
      · rw [if_pos (Or.inr ⟨rfl, h⟩), if_pos h]
      · have hc : ¬ ((q = p ∧ x = q) ∨ (q = q ∧ x = p)) := by
          rintro (⟨h1, -⟩ | ⟨-, h1⟩)
          · exact hpq h1.symm
          · exact h h1
        rw [if_neg hc, if_neg h]
    have hsq : ∀ x : ℝ, (x : ℂ) * (x : ℂ) = ((x ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [pow_two, Complex.ofReal_mul]
    have hct : ∀ x y : Fin d, Z.conjTranspose x y = star (Z y x) := fun x y => rfl
    ext r s
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [hct, hstar]
    have hcongr : ∀ t : Fin d, Z t r * Z t s =
        (if t = p then (Z p r * Z p s) else 0) + (if t = q then (Z q r * Z q s) else 0) := by
      intro t
      by_cases htp : t = p
      · rw [htp, if_pos rfl, if_neg hpq, add_zero]
      · by_cases htq : t = q
        · rw [htq, if_neg (fun hh => hpq hh.symm), if_pos rfl, zero_add]
        · have h1 : Z t r = 0 := by
            rw [hZdef t r]
            exact if_neg (by rintro (⟨hh, -⟩ | ⟨hh, -⟩); exacts [htp hh, htq hh])
          have h2 : Z t s = 0 := by
            rw [hZdef t s]
            exact if_neg (by rintro (⟨hh, -⟩ | ⟨hh, -⟩); exacts [htp hh, htq hh])
          rw [h1, h2, if_neg htp, if_neg htq, zero_mul, add_zero]
    have e1 : (∑ t : Fin d, (if t = p then (Z p r * Z p s) else 0)) = Z p r * Z p s := by
      have h := Finset.sum_eq_single (f := fun t : Fin d => (if t = p then (Z p r * Z p s) else 0))
        p (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ p) h)
      simpa using h
    have e2 : (∑ t : Fin d, (if t = q then (Z q r * Z q s) else 0)) = Z q r * Z q s := by
      have h := Finset.sum_eq_single (f := fun t : Fin d => (if t = q then (Z q r * Z q s) else 0))
        q (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ q) h)
      simpa using h
    have h2pt : (∑ t : Fin d, Z t r * Z t s) = Z p r * Z p s + Z q r * Z q s := by
      have hstep : (∑ t : Fin d, Z t r * Z t s) = ∑ t : Fin d,
          ((if t = p then (Z p r * Z p s) else 0) + (if t = q then (Z q r * Z q s) else 0)) :=
        Finset.sum_congr rfl (fun t _ => hcongr t)
      rw [hstep, Finset.sum_add_distrib, e1, e2]
    rw [h2pt, hp r, hp s, hq r, hq s]
    by_cases hrs : r = s
    · rw [hrs, if_pos rfl]
      by_cases hsp : s = p
      · rw [hsp]
        have hc : c p = a ^ 2 := by
          have h2 : (if p = p ∨ p = q then a ^ 2 else 0) = a ^ 2 := if_pos (Or.inl rfl)
          simpa [hcdef] using h2
        rw [if_neg hpq, if_pos rfl, hc, zero_mul, zero_add, hsq]
      · by_cases hsq' : s = q
        · rw [hsq']
          have hc : c q = a ^ 2 := by
            have h2 : (if q = p ∨ q = q then a ^ 2 else 0) = a ^ 2 := if_pos (Or.inr rfl)
            simpa [hcdef] using h2
          rw [if_pos rfl, if_neg (fun hh : q = p => hpq hh.symm), hc, mul_zero, add_zero, hsq]
        · have hc : c s = 0 := by
            have h2 : (if s = p ∨ s = q then a ^ 2 else 0) = 0 :=
              if_neg (by rintro (hh | hh); exacts [hsp hh, hsq' hh])
            simpa [hcdef] using h2
          rw [if_neg hsq', if_neg hsp, hc]
          simp
    · have e3 : (if r = q then (a : ℂ) else 0) * (if s = q then (a : ℂ) else 0) = 0 := by
        by_cases hq1 : r = q
        · have hq2 : ¬ (s = q) := fun h => hrs (hq1.trans h.symm)
          rw [if_pos hq1, if_neg hq2, mul_zero]
        · rw [if_neg hq1, zero_mul]
      have e4 : (if r = p then (a : ℂ) else 0) * (if s = p then (a : ℂ) else 0) = 0 := by
        by_cases hp1 : r = p
        · have hp2 : ¬ (s = p) := fun h => hrs (hp1.trans h.symm)
          rw [if_pos hp1, if_neg hp2, mul_zero]
        · rw [if_neg hp1, zero_mul]
      rw [if_neg hrs, e3, e4, add_zero]
  have hmain :
      (∑ k : Fin d,
        (((Matrix.isHermitian_conjTranspose_mul_self Z).eigenvalues k) ^ ((3 : ℝ) / 2)))
        = 2 * |a| ^ 3 := by
    let hB : (Matrix.diagonal (fun r => ((c r : ℝ) : ℂ))).IsHermitian :=
      hZZ ▸ Matrix.isHermitian_conjTranspose_mul_self Z
    have heig :
        (Matrix.isHermitian_conjTranspose_mul_self Z).eigenvalues = hB.eigenvalues := by
      refine (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self Z) hB).mpr ?_
      rw [hZZ]
    have hsumB : (∑ k : Fin d, (hB.eigenvalues k) ^ ((3 : ℝ) / 2)) = 2 * |a| ^ 3 := by
      have hx := statopia_math_node_1840280243_8691960b d a p q hpq hB
      simpa [Real.rpow_natCast] using hx
    rw [heig]
    exact hsumB
  rw [hmain, div_eq_inv_mul]
  /- @proof-region region.target-node.session.e760892db2f4303d end -/

end Statlib.Imported

