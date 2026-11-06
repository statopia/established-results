import Statlib.HighDim.Concentration.GaussianQuadraticForm
import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_2ce0255179bdd26af5d8
import ProverJobs.ResidualE2ESupport20261106.M_983b93e5b7a9bbf1ef65

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
theorem statopia_math_node_4102978787_3acbcbe4 : ∀ (m n : ℕ) [NeZero (m + n)]
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hD : ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
        (A.map Complex.ofReal)
        (Matrix.transpose (A.map Complex.ofReal))
        (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm : Matrix (Fin (m + n)) (Fin (m + n)) ℂ).IsHermitian),
    sSup (Set.range fun i : Fin (m + n) => (hD.eigenvalues i : ℝ)) =
      Statlib.HighDim.MatrixAnalysis.opNorm A := by
  /- @proof-region region.target-node.session.2679d4e7764ccacf begin -/
  intro m n hmn A hD
  haveI hN : NeZero (m + n) := hmn
  let B : Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
        (A.map Complex.ofReal)
        (Matrix.transpose (A.map Complex.ofReal))
        (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm
  have hB : B.IsHermitian := hD
  have h1 : sSup (Set.range fun i : Fin (m + n) => |(hB.eigenvalues i : ℝ)|) = ‖B‖ :=
    statopia_math_node_1550178179_06242ca1 (m + n) B hB
  have h2 : ‖B‖ = Statlib.HighDim.MatrixAnalysis.opNorm A := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    exact statopia_math_node_1606911688_c7dc5675 m n A
  have hpos : 0 < m + n := Nat.pos_of_ne_zero (NeZero.ne (m + n))
  have hneg : ∀ i : Fin (m + n), ∃ j : Fin (m + n), hD.eigenvalues j = -(hD.eigenvalues i) := by
    let σ' : Fin m ⊕ Fin n → ℂ := Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ))
    let σ : Fin (m + n) → ℂ := fun k => σ' (finSumFinEquiv.symm k)
    let B' : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
      Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (A.map Complex.ofReal)
        (Matrix.transpose (A.map Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ)
    have hσ' : ∀ u : Fin m ⊕ Fin n, σ' u * σ' u = 1 := by
      rintro (x | y) <;> simp [σ']
    have hkey' : ∀ u v : Fin m ⊕ Fin n, σ' u * σ' v * B' u v = -B' u v := by
      rintro (x | y) (z | w) <;> simp [σ', B', Matrix.fromBlocks]
    have hσ : ∀ k : Fin (m + n), σ k * σ k = 1 := fun k => hσ' (finSumFinEquiv.symm k)
    have hkey : ∀ k l : Fin (m + n), σ k * σ l * B k l = -B k l :=
      fun k l => hkey' (finSumFinEquiv.symm k) (finSumFinEquiv.symm l)
    have hPP : Matrix.diagonal σ * Matrix.diagonal σ = 1 := by
      ext k l
      rw [Matrix.diagonal_mul, Matrix.diagonal_apply]
      by_cases hkl : k = l
      · subst hkl
        simpa using hσ k
      · simp [hkl]
    have hPBP : Matrix.diagonal σ * B * Matrix.diagonal σ = -B := by
      ext k l
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      calc σ k * B k l * σ l = σ k * σ l * B k l := by ring
        _ = (-B) k l := hkey k l
    have hIU : ∀ c : ℝ, IsUnit (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c + B) ↔
        IsUnit (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c - B) := by
      intro c
      have halg : algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c
          = Matrix.diagonal (fun _ => (c : ℂ)) := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp [Algebra.algebraMap_eq_smul_one]
        · simp [Algebra.algebraMap_eq_smul_one, hab]
      have hDc : Matrix.diagonal σ * Matrix.diagonal (fun _ => (c : ℂ)) * Matrix.diagonal σ
          = Matrix.diagonal (fun _ => (c : ℂ)) := by
        ext a b
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl]
          calc σ a * (c : ℂ) * σ a = (c : ℂ) * (σ a * σ a) := by ring
            _ = (c : ℂ) := by rw [hσ a, mul_one]
        · rw [if_neg hab]
          ring
      have hconj : Matrix.diagonal σ * (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c - B) * Matrix.diagonal σ
          = algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c + B := by
        rw [halg]
        calc Matrix.diagonal σ * (Matrix.diagonal (fun _ => (c : ℂ)) - B) * Matrix.diagonal σ
            = Matrix.diagonal σ * Matrix.diagonal (fun _ => (c : ℂ)) * Matrix.diagonal σ
                - Matrix.diagonal σ * B * Matrix.diagonal σ := by rw [mul_sub, sub_mul]
          _ = Matrix.diagonal (fun _ => (c : ℂ)) - (-B) := by rw [hDc, hPBP]
          _ = Matrix.diagonal (fun _ => (c : ℂ)) + B := by rw [sub_neg_eq_add]
      have hPun : IsUnit (Matrix.diagonal σ) :=
        ⟨⟨Matrix.diagonal σ, Matrix.diagonal σ, hPP, hPP⟩, rfl⟩
      constructor
      · intro h
        have h2 : IsUnit (Matrix.diagonal σ * (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c - B) * Matrix.diagonal σ) := by
          rw [hconj]
          exact h
        have h3 : IsUnit (Matrix.diagonal σ * (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c - B)) := by
          have h4 := h2.mul hPun
          rwa [show (Matrix.diagonal σ * (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c - B) * Matrix.diagonal σ) * Matrix.diagonal σ
              = Matrix.diagonal σ * (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c - B) by
            rw [mul_assoc, hPP, mul_one]] at h4
        have h5 := hPun.mul h3
        rwa [show Matrix.diagonal σ * (Matrix.diagonal σ * (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c - B))
            = algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c - B by
          rw [← mul_assoc, hPP, one_mul]] at h5
      · intro h
        rw [← hconj]
        exact (hPun.mul h).mul hPun

    have hclosure : ∀ c : ℝ, c ∈ spectrum ℝ B → -c ∈ spectrum ℝ B := by
      intro c hc
      have h1 : ¬ IsUnit (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c - B) := by
        simpa only [spectrum, Set.mem_setOf_eq] using hc
      have h2 : ¬ IsUnit (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c + B) :=
        fun h => h1 ((hIU c).mp h)
      have heq : algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) (-c) - B
          = -(algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) c + B) := by
        rw [map_neg, neg_add, sub_eq_add_neg]
      show ¬ IsUnit (algebraMap ℝ (Matrix (Fin (m + n)) (Fin (m + n)) ℂ) (-c) - B)
      rw [heq]
      intro h
      exact h2 (by simpa using h.neg)
    intro i
    have hmem : hD.eigenvalues i ∈ spectrum ℝ B := hD.eigenvalues_mem_spectrum_real i
    have hmem2 : -(hD.eigenvalues i) ∈ spectrum ℝ B := hclosure _ hmem
    rw [Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hD] at hmem2
    obtain ⟨j, hj⟩ := hmem2
    exact ⟨j, hj⟩

  have h3 : sSup (Set.range fun i : Fin (m + n) => (hD.eigenvalues i : ℝ)) =
      sSup (Set.range fun i : Fin (m + n) => |(hD.eigenvalues i : ℝ)|) := by
    have hbds : BddAbove (Set.range fun i : Fin (m + n) => hD.eigenvalues i) :=
      ⟨∑ i : Fin (m + n), |(hD.eigenvalues i : ℝ)|, by
        rintro _ ⟨i, rfl⟩
        exact le_trans (le_abs_self _)
          (Finset.single_le_sum (f := fun i : Fin (m + n) => |(hD.eigenvalues i : ℝ)|)
            (fun i _ => abs_nonneg _) (Finset.mem_univ i))⟩
    have hbdr : BddAbove (Set.range fun i : Fin (m + n) => |(hD.eigenvalues i : ℝ)|) :=
      ⟨∑ i : Fin (m + n), |(hD.eigenvalues i : ℝ)|, by
        rintro _ ⟨i, rfl⟩
        exact Finset.single_le_sum (f := fun i : Fin (m + n) => |(hD.eigenvalues i : ℝ)|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ i)⟩
    have hne : (Set.range fun i : Fin (m + n) => hD.eigenvalues i).Nonempty :=
      ⟨_, ⟨⟨0, hpos⟩, rfl⟩⟩
    have hner : (Set.range fun i : Fin (m + n) => |(hD.eigenvalues i : ℝ)|).Nonempty :=
      ⟨_, ⟨⟨0, hpos⟩, rfl⟩⟩
    refine le_antisymm ?_ ?_
    · refine csSup_le hne ?_
      rintro _ ⟨i, rfl⟩
      exact le_trans (le_abs_self _) (le_csSup hbdr ⟨i, rfl⟩)
    · refine csSup_le hner ?_
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hneg i
      have hji : (hD.eigenvalues i : ℝ) ≥ -(sSup (Set.range fun i : Fin (m + n) => hD.eigenvalues i)) := by
        have hle : hD.eigenvalues j ≤ sSup (Set.range fun i : Fin (m + n) => hD.eigenvalues i) :=
          le_csSup hbds ⟨j, rfl⟩
        rw [hj] at hle
        linarith
      refine abs_le.mpr ⟨hji, le_csSup hbds ⟨i, rfl⟩⟩

  exact h3.trans (h1.trans h2)

  /- @proof-region region.target-node.session.2679d4e7764ccacf end -/

end Statlib.Imported

