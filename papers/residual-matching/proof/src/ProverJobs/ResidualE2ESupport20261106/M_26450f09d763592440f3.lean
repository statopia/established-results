import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_82362cd7c8b5ac5d556f

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
theorem statopia_math_node_3044336349_4fb621ca : ∀ (N : ℕ) [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.IsHermitian) (t : ℝ),
    sSup (Set.range hA.eigenvalues) ≤ t ↔
      ∀ v : Fin N → ℂ,
        (∑ i : Fin N, ∑ j : Fin N, star (v i) * v j * A i j).re ≤
          t * (∑ i : Fin N, ‖v i‖ ^ 2) := by
  /- @proof-region region.target-node.session.831378c42105a294 begin -/
  intro N _ A hA t
  set M := sSup (Set.range hA.eigenvalues) with hMdef
  have hbdd : BddAbove (Set.range hA.eigenvalues) := Set.finite_range hA.eigenvalues |>.bddAbove
  have hMle : ∀ j, hA.eigenvalues j ≤ M := fun j => le_csSup hbdd (Set.mem_range_self j)
  have hne : (Set.range hA.eigenvalues).Nonempty :=
    ⟨hA.eigenvalues ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, Set.mem_range_self _⟩
  have hMbound : M ≤ t ↔ ∀ j, hA.eigenvalues j ≤ t := by
    constructor
    · intro h j; exact le_trans (hMle j) h
    · intro h; exact csSup_le hne (by rintro b ⟨j, rfl⟩; exact h j)
  rw [hMbound]
  have hQeq : ∀ v : Fin N → ℂ,
      (∑ i, ∑ j, star (v i) * v j * A i j)
        = inner ℂ (WithLp.toLp 2 v) (Matrix.toEuclideanLin A (WithLp.toLp 2 v)) := by
    intro v
    rw [Matrix.toEuclideanLin_apply, PiLp.inner_apply]
    simp only [RCLike.inner_apply, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (fun j => A i j) ⬝ᵥ v = ∑ j, A i j * v j from rfl, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [starRingEnd_apply]
    ring
  constructor
  · intro hMt v
    obtain ⟨hid, hpar⟩ := statopia_math_node_2281494419_677a8c9a N A hA v
    rw [hid, ← hpar]
    calc ∑ j, hA.eigenvalues j * ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 v)‖ ^ 2
        ≤ ∑ j, t * ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 v)‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hMt j) (sq_nonneg _)
      _ = t * ∑ j, ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 v)‖ ^ 2 := by
          rw [Finset.mul_sum]
  · intro hv j
    have hQ : (∑ i, ∑ j', star ((hA.eigenvectorBasis j).ofLp i) * (hA.eigenvectorBasis j).ofLp j' * A i j').re = hA.eigenvalues j := by
      have hid := (statopia_math_node_2281494419_677a8c9a N A hA ((hA.eigenvectorBasis j).ofLp)).1
      rw [hid]
      simp only [WithLp.toLp_ofLp, OrthonormalBasis.inner_eq_ite]
      have hnorm : ∀ x : Fin N, ‖(if x = j then (1 : ℂ) else 0)‖ ^ 2 = (if x = j then (1 : ℝ) else 0) := by
        intro x
        by_cases hx : x = j <;> simp [hx]
      simp only [hnorm]
      have key : (∑ x, hA.eigenvalues x * (if x = j then (1 : ℝ) else 0)) = hA.eigenvalues j * (if j = j then (1 : ℝ) else 0) := by
        apply Finset.sum_eq_single j
        · intro c _ hc; simp [hc]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      rw [key]; simp
    have hB : (∑ i, ‖((hA.eigenvectorBasis j).ofLp) i‖ ^ 2) = 1 := by
      rw [← EuclideanSpace.norm_sq_eq (hA.eigenvectorBasis j)]
      rw [OrthonormalBasis.norm_eq_one (hA.eigenvectorBasis) j]
      norm_num
    have hv0 := hv ((hA.eigenvectorBasis j).ofLp)
    rw [hQ, hB, mul_one] at hv0
    exact hv0
  /- @proof-region region.target-node.session.831378c42105a294 end -/

end Statlib.Imported

