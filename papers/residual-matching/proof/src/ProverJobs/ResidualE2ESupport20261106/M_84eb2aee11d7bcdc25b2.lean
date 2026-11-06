import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

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
theorem statopia_math_node_3729350466_f4b48ace : ∀ (nS nT : ℕ) (f : Fin nT → ℝ) (g : Fin nS → ℝ)
    (hf : Antitone f) (hg : Antitone g) (hg_nonneg : ∀ j : Fin nS, 0 ≤ g j) (hle : nS ≤ nT)
    (hmult : Multiset.map f (Finset.univ : Finset (Fin nT)).val
      = Multiset.map g (Finset.univ : Finset (Fin nS)).val + (nT - nS) • ({(0 : ℝ)} : Multiset ℝ))
    (k : ℕ) (hk : k < nS) (hk' : k < nT), f ⟨k, hk'⟩ = g ⟨k, hk⟩ := by
  /- @proof-region region.target-node.session.d37dd8bd55a66969 begin -/
  intro nS nT f g hf hg hg_nonneg hle hmult k hk hk'
  have hF : Multiset.map f (Finset.univ : Finset (Fin nT)).val = ↑(List.ofFn f) := Fin.univ_val_map f
  have hG : Multiset.map g (Finset.univ : Finset (Fin nS)).val = ↑(List.ofFn g) := Fin.univ_val_map g
  have hzero : ∀ m : ℕ, m • ({(0 : ℝ)} : Multiset ℝ) = ↑(List.replicate m (0 : ℝ)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [add_nsmul, one_nsmul, ih, List.replicate_succ, add_comm]
      simp
  have hcoe : (↑(List.ofFn f) : Multiset ℝ) = ↑(List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ)) := by
    rw [hF, hG, hzero] at hmult
    rw [hmult, Multiset.coe_add]
  have anti_ofFn : ∀ (n : ℕ) (u : Fin n → ℝ), Antitone u → Antitone (List.ofFn u).get := by
    intro n u hu i j hij
    show (List.ofFn u)[j.val]'j.isLt ≤ (List.ofFn u)[i.val]'i.isLt
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact hu (by simpa using hij)
  have hsortf : (List.ofFn f).SortedGE := anti_ofFn nT f hf
  have hsortg : (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ)).SortedGE := by
    unfold List.SortedGE
    have hanti₁ : Antitone (List.ofFn g).get := anti_ofFn nS g hg
    intro i j hij
    have hleij : i.val ≤ j.val := by simpa using hij
    by_cases hj : j.val < (List.ofFn g).length
    · have hi : i.val < (List.ofFn g).length := Nat.lt_of_le_of_lt hleij hj
      have h1 : (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ)).get j
          = (List.ofFn g).get ⟨j.val, hj⟩ := by
        show (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ))[j.val]'j.isLt
          = (List.ofFn g)[j.val]'hj
        exact List.getElem_append_left hj
      have h2 : (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ)).get i
          = (List.ofFn g).get ⟨i.val, hi⟩ := by
        show (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ))[i.val]'i.isLt
          = (List.ofFn g)[i.val]'hi
        exact List.getElem_append_left hi
      rw [h1, h2]
      exact hanti₁ (by simpa using hij)
    · have hjlen : (List.ofFn g).length ≤ j.val := Nat.le_of_not_lt hj
      have h1 : (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ)).get j = 0 := by
        show (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ))[j.val]'j.isLt = 0
        rw [List.getElem_append_right hjlen]
        simp
      by_cases hi : i.val < (List.ofFn g).length
      · have h2 : (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ)).get i
            = (List.ofFn g).get ⟨i.val, hi⟩ := by
          show (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ))[i.val]'i.isLt
            = (List.ofFn g)[i.val]'hi
          exact List.getElem_append_left hi
        rw [h1, h2]
        show (0 : ℝ) ≤ (List.ofFn g)[i.val]'hi
        rw [List.getElem_ofFn]
        exact hg_nonneg _
      · have h2 : (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ)).get i = 0 := by
          show (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ))[i.val]'i.isLt = 0
          rw [List.getElem_append_right (Nat.le_of_not_lt hi)]
          simp
        rw [h1, h2]
  have heq : List.ofFn f = List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ) :=
    List.Perm.eq_of_sortedGE hsortf hsortg (Multiset.coe_eq_coe.mp hcoe)
  have hk2 : k < (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ)).length := by
    simp
    omega
  have key : ∀ (l₁ l₂ : List ℝ) (m : ℕ), l₁ = l₂ → ∀ (h₁ : m < l₁.length) (h₂ : m < l₂.length),
      l₁[m]'h₁ = l₂[m]'h₂ := by
    rintro l₁ l₂ m rfl h₁ h₂
    exact congrArg (fun p => l₁[m]'p) (Subsingleton.elim h₁ h₂)
  have hget := key (List.ofFn f) (List.ofFn g ++ List.replicate (nT - nS) (0 : ℝ)) k heq
    (by simpa using hk') hk2
  rw [List.getElem_ofFn, List.getElem_append_left (by simpa using hk), List.getElem_ofFn] at hget
  exact hget
  /- @proof-region region.target-node.session.d37dd8bd55a66969 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3729350466_f4b48ace


