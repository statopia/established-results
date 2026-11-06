import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.VonNeumann
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_5646161454d091b90885

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3642284588_bdf66dbb : ∀ (m n : ℕ) (hnm : n ≤ m)
    (A B : Matrix (Fin m) (Fin n) ℝ),
    (A.transpose * B).trace ≤ ∑ i : Fin n, sv hnm A i * sv hnm B i := by
  /- @proof-region region.target-node.session.c4de7ea7e30d1338 begin -/
  intro m n hnm A B
  rcases n with _ | n
  · simp
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ n) hnm⟩⟩
  set X : Matrix (Fin m) (Fin m) ℝ :=
    (fun i j => if h : (j : ℕ) < n + 1 then B i ⟨j, h⟩ else 0) with hX
  set Y : Matrix (Fin m) (Fin m) ℝ :=
    (fun i j => if h : (i : ℕ) < n + 1 then A j ⟨i, h⟩ else 0) with hY
  have hpadsum : ∀ {N : ℕ}, n + 1 ≤ N → ∀ F : Fin (n + 1) → ℝ,
      (∑ k : Fin N, (if h : (k : ℕ) < n + 1 then F ⟨(k : ℕ), h⟩ else 0))
        = ∑ a : Fin (n + 1), F a := by
    intro N hN F
    have hL : (∑ k : Fin N, (if h : (k : ℕ) < n + 1 then F ⟨(k : ℕ), h⟩ else 0))
        = ∑ r ∈ Finset.range N, (if h : r < n + 1 then F ⟨r, h⟩ else 0) :=
      Fin.sum_univ_eq_sum_range (fun r : ℕ => if h : r < n + 1 then F ⟨r, h⟩ else 0) N
    have hR : (∑ a : Fin (n + 1), F a)
        = ∑ r ∈ Finset.range (n + 1), (if h : r < n + 1 then F ⟨r, h⟩ else 0) := by
      rw [← Fin.sum_univ_eq_sum_range (fun r : ℕ => if h : r < n + 1 then F ⟨r, h⟩ else 0) (n + 1)]
      refine Finset.sum_congr rfl ?_
      intro a _
      simp only [dif_pos a.isLt]
    rw [hL, hR]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro r hr
      simp only [Finset.mem_range] at hr ⊢
      exact Nat.lt_of_lt_of_le hr hN
    · intro r _ hr2
      simp only [Finset.mem_range] at hr2
      exact dif_neg hr2
  have hXY : X * Y = B * A.transpose := by
    ext i j
    rw [hX, hY]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    have hpt : ∀ k : Fin m,
        (if h : (k : ℕ) < n + 1 then B i ⟨(k : ℕ), h⟩ else 0) *
          (if h : (k : ℕ) < n + 1 then A j ⟨(k : ℕ), h⟩ else 0)
        = (if h : (k : ℕ) < n + 1 then B i ⟨(k : ℕ), h⟩ * A j ⟨(k : ℕ), h⟩ else 0) := by
      intro k
      by_cases hk : (k : ℕ) < n + 1
      · simp only [dif_pos hk]
      · simp only [dif_neg hk, zero_mul]
    rw [Finset.sum_congr rfl (fun k _ => hpt k)]
    exact hpadsum hnm (fun a => B i a * A j a)
  have hvn := Statlib.HighDim.MatrixAnalysis.von_neumann_trace_inequality m X Y
  have hpad := statopia_math_node_2686874991_4d504235 m (n + 1) hnm
  have hpadX : ∀ k : Fin (min m m), Statlib.HighDim.MatrixAnalysis.singularValues X k
      = if h : (k : ℕ) < n + 1 then sv hnm B ⟨k, h⟩ else 0 := by
    simpa only [hX] using (hpad B).1
  have hpadY : ∀ k : Fin (min m m), Statlib.HighDim.MatrixAnalysis.singularValues Y k
      = if h : (k : ℕ) < n + 1 then sv hnm A ⟨k, h⟩ else 0 := by
    simpa only [hY] using (hpad A).2
  have hsum : (∑ k : Fin (min m m), Statlib.HighDim.MatrixAnalysis.singularValues X k
        * Statlib.HighDim.MatrixAnalysis.singularValues Y k)
      = ∑ i : Fin (n + 1), sv hnm A i * sv hnm B i := by
    have hpt : ∀ k : Fin (min m m),
        Statlib.HighDim.MatrixAnalysis.singularValues X k
            * Statlib.HighDim.MatrixAnalysis.singularValues Y k
          = (if h : (k : ℕ) < n + 1 then
              sv hnm A ⟨(k : ℕ), h⟩ * sv hnm B ⟨(k : ℕ), h⟩ else 0) := by
      intro k
      rw [hpadX k, hpadY k]
      by_cases hk : (k : ℕ) < n + 1
      · simp only [dif_pos hk]
        exact mul_comm _ _
      · simp only [dif_neg hk, zero_mul]
    rw [Finset.sum_congr rfl (fun k _ => hpt k)]
    exact hpadsum (le_min hnm hnm) (fun a => sv hnm A a * sv hnm B a)
  rw [Matrix.trace_mul_comm, ← hXY]
  exact le_trans (le_abs_self ((X * Y).trace)) (le_trans hvn (le_of_eq hsum))
  /- @proof-region region.target-node.session.c4de7ea7e30d1338 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3642284588_bdf66dbb


