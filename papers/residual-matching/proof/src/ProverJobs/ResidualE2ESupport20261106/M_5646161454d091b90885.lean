import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.Vocabulary.SVD
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_40b5c5bff1ae5131cc00

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
theorem statopia_math_node_2686874991_4d504235 : ∀ (m p : ℕ) (hpm : p ≤ m)
    (C : Matrix (Fin m) (Fin p) ℝ),
    (∀ k : Fin (min m m),
        Statlib.HighDim.MatrixAnalysis.singularValues
            (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨(j : ℕ), h⟩ else 0) k
          = if h : (k : ℕ) < p then sv hpm C ⟨(k : ℕ), h⟩ else 0) ∧
      (∀ k : Fin (min m m),
        Statlib.HighDim.MatrixAnalysis.singularValues
            (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨(i : ℕ), h⟩ else 0) k
          = if h : (k : ℕ) < p then sv hpm C ⟨(k : ℕ), h⟩ else 0) := by
  /- @proof-region region.target-node.session.5eefc5b8bf866dca begin -/
  intro m p hpm C
  by_cases hm0 : m = 0
  · subst m
    exact ⟨fun k => absurd k.isLt (by simp), fun k => absurd k.isLt (by simp)⟩
  · refine ⟨?_, ?_⟩
    · intro k
      by_cases hk : (k : ℕ) < p
      · rw [dif_pos hk]
        simp only [sv, Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary]
        unfold Statlib.HighDim.Vocabulary.singularValues
        have hbb : (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)).transpose
            * (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0))
            = (fun i j : Fin m => if h : (i : ℕ) < p ∧ (j : ℕ) < p then (C.transpose * C) ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) := by
          ext i j
          simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
          by_cases hi : (i : ℕ) < p
          · by_cases hj : (j : ℕ) < p
            · simp only [dif_pos hi, dif_pos hj, dif_pos (⟨hi, hj⟩ : (i : ℕ) < p ∧ (j : ℕ) < p)]
            · simp only [dif_pos hi, dif_neg hj, dif_neg (fun h : (i : ℕ) < p ∧ (j : ℕ) < p => hj h.2)]
              simp
          · simp only [dif_neg hi, dif_neg (fun h : (i : ℕ) < p ∧ (j : ℕ) < p => hi h.1)]
            simp
        have hS : (C.transpose * C).IsHermitian :=
          Statlib.HighDim.Vocabulary.singularValues._proof_1 C
        have hne : (C.transpose * C).PosSemidef := by
          simpa using Matrix.posSemidef_conjTranspose_mul_self C
        have hnn : ∀ i : Fin p, 0 ≤ hS.eigenvalues i := by
          intro i
          have hpos := Matrix.PosSemidef.eigenvalues_nonneg hne i
          have h2 : hne.1.eigenvalues = hS.eigenvalues :=
            (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr rfl
          rw [h2] at hpos
          exact hpos
        have hT : Matrix.IsHermitian (fun i j : Fin m => if h : (i : ℕ) < p ∧ (j : ℕ) < p then (C.transpose * C) ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) := by
          rw [← hbb]
          exact Statlib.HighDim.Vocabulary.singularValues._proof_1 (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)
        have key := statopia_math_node_3439180840_d82a2d61 p m hpm (C.transpose * C) hS hnn hT
          (⟨(k : ℕ), lt_of_lt_of_le k.isLt (Nat.min_le_right m m)⟩ : Fin m) hk
        have hfunL : (Statlib.HighDim.Vocabulary.singularValues._proof_1 (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)).eigenvalues = hT.eigenvalues :=
          (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (Statlib.HighDim.Vocabulary.singularValues._proof_1 (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)) hT).mpr (congrArg Matrix.charpoly hbb)
        have hidxB : (Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2 (Fin.castLE (Nat.min_le_right m p) (Fin.castLE (sv._proof_1 hpm) ⟨(k : ℕ), hk⟩))).val = (k : ℕ) := by simp
        have hidxAm : (Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2 (Fin.castLE (Nat.min_le_right m m) k)).val = (k : ℕ) := by simp
        have hidxAa : Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2 (Fin.castLE (Nat.min_le_right m m) k) = (⟨(k : ℕ), by simpa using (⟨(k : ℕ), lt_of_lt_of_le k.isLt (Nat.min_le_right m m)⟩ : Fin m).isLt⟩ : Fin (Fintype.card (Fin m))) := Fin.ext (by simpa using hidxAm)
        have hidxBb : Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2 (Fin.castLE (Nat.min_le_right m p) (Fin.castLE (sv._proof_1 hpm) ⟨(k : ℕ), hk⟩)) = (⟨(k : ℕ), by simpa using hk⟩ : Fin (Fintype.card (Fin p))) := Fin.ext (by simpa using hidxB)
        rw [hidxAa, hidxBb]
        have hEig₀ : Matrix.IsHermitian.eigenvalues₀ (Statlib.HighDim.Vocabulary.singularValues._proof_1 (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)) = Matrix.IsHermitian.eigenvalues₀ hT := by
          funext j
          have h := congrFun hfunL ((Fintype.equivOfCardEq (by simp : Fintype.card (Fin (Fintype.card (Fin m))) = Fintype.card (Fin m))) j)
          simpa [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h
        rw [hEig₀]
        exact congrArg Real.sqrt key
      · rw [dif_neg hk]
        have hfact : (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0))
            = C * Matrix.of (fun (a : Fin p) (j : Fin m) => if (a : ℕ) = (j : ℕ) then (1 : ℝ) else 0) := by
          ext i j
          simp only [Matrix.mul_apply, Matrix.of_apply]
          by_cases hj : (j : ℕ) < p
          · rw [dif_pos hj, eq_comm, Finset.sum_eq_single ⟨j, hj⟩]
            · simp
            · intro b _ hb
              have hbj : (b : ℕ) ≠ (j : ℕ) := fun hc => hb (Fin.ext hc)
              simp [hbj]
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [dif_neg hj, eq_comm]
            apply Finset.sum_eq_zero
            intro a _
            have haj : (a : ℕ) ≠ (j : ℕ) := by have := a.isLt; omega
            simp [haj]
        have hrank : Matrix.rank (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)) ≤ p := by
          rw [hfact]
          calc Matrix.rank (C * Matrix.of (fun (a : Fin p) (j : Fin m) => if (a : ℕ) = (j : ℕ) then (1 : ℝ) else 0))
              ≤ Matrix.rank C := Matrix.rank_mul_le_left C _
            _ ≤ p := by simpa using Matrix.rank_le_card_width C
        have hk1 : Matrix.rank (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)) < (k : ℕ) + 1 := by
          have hpk : p ≤ (k : ℕ) := by omega
          omega
        exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties
          (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0))
          (Or.inl ⟨⟨0, Nat.pos_of_ne_zero hm0⟩⟩)).2.2.2 k hk1
    · intro k
      by_cases hk : (k : ℕ) < p
      · rw [dif_pos hk]
        simp only [sv, Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary]
        unfold Statlib.HighDim.Vocabulary.singularValues
        have hS : (C.transpose * C).IsHermitian :=
          Statlib.HighDim.Vocabulary.singularValues._proof_1 C
        have hne : (C.transpose * C).PosSemidef := by
          simpa using Matrix.posSemidef_conjTranspose_mul_self C
        have hnn : ∀ i : Fin p, 0 ≤ hS.eigenvalues i := by
          intro i
          have hpos2 := Matrix.PosSemidef.eigenvalues_nonneg hne i
          have h2 : hne.1.eigenvalues = hS.eigenvalues :=
            (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr rfl
          rw [h2] at hpos2
          exact hpos2
        have hbb : (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)).transpose
            * (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0))
            = (fun i j : Fin m => if h : (i : ℕ) < p ∧ (j : ℕ) < p then (C.transpose * C) ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) := by
          ext i j
          simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
          by_cases hi : (i : ℕ) < p
          · by_cases hj : (j : ℕ) < p
            · simp only [dif_pos hi, dif_pos hj, dif_pos (⟨hi, hj⟩ : (i : ℕ) < p ∧ (j : ℕ) < p)]
            · simp only [dif_pos hi, dif_neg hj, dif_neg (fun h : (i : ℕ) < p ∧ (j : ℕ) < p => hj h.2)]
              simp
          · simp only [dif_neg hi, dif_neg (fun h : (i : ℕ) < p ∧ (j : ℕ) < p => hi h.1)]
            simp
        have hT : Matrix.IsHermitian (fun i j : Fin m => if h : (i : ℕ) < p ∧ (j : ℕ) < p then (C.transpose * C) ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) := by
          rw [← hbb]
          exact Statlib.HighDim.Vocabulary.singularValues._proof_1 (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)
        have key := statopia_math_node_3439180840_d82a2d61 p m hpm (C.transpose * C) hS hnn hT
          (⟨(k : ℕ), lt_of_lt_of_le k.isLt (Nat.min_le_right m m)⟩ : Fin m) hk
        have hCrowOff : (Matrix.of (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨(i : ℕ), h⟩ else 0))
            = (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)).transpose := by
          ext i j; rfl
        have hgram : (Matrix.of (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨(i : ℕ), h⟩ else 0)).transpose
              * (Matrix.of (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨(i : ℕ), h⟩ else 0))
            = (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0))
              * (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)).transpose := by
          rw [hCrowOff]; rfl
        have hcharpoly : ((Matrix.of (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨(i : ℕ), h⟩ else 0)).transpose
              * (Matrix.of (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨(i : ℕ), h⟩ else 0))).charpoly
            = Matrix.charpoly (fun i j : Fin m => if h : (i : ℕ) < p ∧ (j : ℕ) < p then (C.transpose * C) ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) :=
          (congrArg Matrix.charpoly hgram).trans
            ((Matrix.charpoly_mul_comm (Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)) ((Matrix.of (fun i j : Fin m => if h : (j : ℕ) < p then C i ⟨j, h⟩ else 0)).transpose)).trans
              (congrArg Matrix.charpoly hbb))
        have hfunL : (Statlib.HighDim.Vocabulary.singularValues._proof_1 (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨(i : ℕ), h⟩ else 0)).eigenvalues = hT.eigenvalues :=
          (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (Statlib.HighDim.Vocabulary.singularValues._proof_1 (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨(i : ℕ), h⟩ else 0)) hT).mpr hcharpoly
        have hidxA : (Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2 (Fin.castLE (Nat.min_le_right m m) k)).val = (k : ℕ) := by simp
        have hidxB : (Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2 (Fin.castLE (Nat.min_le_right m p) (Fin.castLE (sv._proof_1 hpm) ⟨(k : ℕ), hk⟩))).val = (k : ℕ) := by simp
        have hidxAa : Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2 (Fin.castLE (Nat.min_le_right m m) k) = (⟨(k : ℕ), by simpa using (⟨(k : ℕ), lt_of_lt_of_le k.isLt (Nat.min_le_right m m)⟩ : Fin m).isLt⟩ : Fin (Fintype.card (Fin m))) := Fin.ext (by simpa using hidxA)
        have hidxBb : Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2 (Fin.castLE (Nat.min_le_right m p) (Fin.castLE (sv._proof_1 hpm) ⟨(k : ℕ), hk⟩)) = (⟨(k : ℕ), by simpa using hk⟩ : Fin (Fintype.card (Fin p))) := Fin.ext (by simpa using hidxB)
        rw [hidxAa, hidxBb]
        have hEig₀ : Matrix.IsHermitian.eigenvalues₀ (Statlib.HighDim.Vocabulary.singularValues._proof_1 (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨(i : ℕ), h⟩ else 0)) = Matrix.IsHermitian.eigenvalues₀ hT := by
          funext j
          have h := congrFun hfunL ((Fintype.equivOfCardEq (by simp : Fintype.card (Fin (Fintype.card (Fin m))) = Fintype.card (Fin m))) j)
          simpa [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h
        rw [hEig₀]
        exact congrArg Real.sqrt key
      · rw [dif_neg hk]
        have hfact2 : (Matrix.of (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨i, h⟩ else 0))
            = Matrix.of (fun (i : Fin m) (a : Fin p) => if (i : ℕ) = (a : ℕ) then (1 : ℝ) else 0)
              * Matrix.of (fun (a : Fin p) (j : Fin m) => C j a) := by
          ext i j
          simp only [Matrix.mul_apply, Matrix.of_apply]
          by_cases hi : (i : ℕ) < p
          · rw [dif_pos hi, eq_comm, Finset.sum_eq_single ⟨i, hi⟩]
            · simp
            · intro b _ hb
              have hbi : (i : ℕ) ≠ (b : ℕ) := fun hc => hb (Fin.ext hc.symm)
              simp [hbi]
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [dif_neg hi, eq_comm]
            apply Finset.sum_eq_zero
            intro a _
            have hai : (i : ℕ) ≠ (a : ℕ) := by have := a.isLt; omega
            simp [hai]
        have hrank2 : Matrix.rank (Matrix.of (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨i, h⟩ else 0)) ≤ p := by
          rw [hfact2]
          calc Matrix.rank (Matrix.of (fun (i : Fin m) (a : Fin p) => if (i : ℕ) = (a : ℕ) then (1 : ℝ) else 0)
                * Matrix.of (fun (a : Fin p) (j : Fin m) => C j a))
              ≤ Matrix.rank (Matrix.of (fun (i : Fin m) (a : Fin p) => if (i : ℕ) = (a : ℕ) then (1 : ℝ) else 0)) := Matrix.rank_mul_le_left _ _
            _ ≤ p := by simpa using Matrix.rank_le_card_width (Matrix.of (fun (i : Fin m) (a : Fin p) => if (i : ℕ) = (a : ℕ) then (1 : ℝ) else 0))
        have hk2 : Matrix.rank (Matrix.of (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨i, h⟩ else 0)) < (k : ℕ) + 1 := by
          have hpk : p ≤ (k : ℕ) := by omega
          omega
        exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties
          (Matrix.of (fun i j : Fin m => if h : (i : ℕ) < p then C j ⟨i, h⟩ else 0))
          (Or.inl ⟨⟨0, Nat.pos_of_ne_zero hm0⟩⟩)).2.2.2 k hk2
  /- @proof-region region.target-node.session.5eefc5b8bf866dca end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_2686874991_4d504235


