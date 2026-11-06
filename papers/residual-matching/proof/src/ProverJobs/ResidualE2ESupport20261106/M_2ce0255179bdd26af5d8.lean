import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1550178179_06242ca1 : ∀ (N : ℕ) [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.IsHermitian),
    sSup (Set.range fun i : Fin N => |(hA.eigenvalues i : ℝ)|) = ‖A‖ := by
  /- @proof-region region.target-node.session.b5e8748a6f271739 begin -/
  intro N hN A hA
  have hpos : 0 < N := Nat.pos_of_ne_zero (hN.out)
  haveI : Nonempty (Fin N) := ⟨⟨0, hpos⟩⟩
  have hne : (Set.range fun i : Fin N => |(hA.eigenvalues i : ℝ)|).Nonempty :=
    ⟨_, ⟨⟨0, hpos⟩, rfl⟩⟩
  have hbdd : BddAbove (Set.range fun i : Fin N => |(hA.eigenvalues i : ℝ)|) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hle : sSup (Set.range fun i : Fin N => |(hA.eigenvalues i : ℝ)|) ≤ ‖A‖ := by
    apply csSup_le hne
    rintro x ⟨i, rfl⟩
    have hmem : hA.eigenvalues i ∈ spectrum ℝ A := hA.eigenvalues_mem_spectrum_real i
    have h := spectrum.norm_le_norm_of_mem hmem
    simpa using h
  have hge : ‖A‖ ≤ sSup (Set.range fun i : Fin N => |(hA.eigenvalues i : ℝ)|) := by
    have hU1 : ‖(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)‖ = 1 := by
      have h2 : ‖(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)‖ *
          ‖(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)‖ = 1 := by
        rw [← CStarRing.norm_star_mul_self,
          Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary]
        simp
      nlinarith [norm_nonneg (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ),
        sq_nonneg (‖(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)‖ - 1)]
    have hU2 : ‖star (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)‖ = 1 := by
      have hst : star (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) =
          (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ).conjTranspose := rfl
      rw [hst, Matrix.l2_opNorm_conjTranspose]
      exact hU1
    have hAeq : A = (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *
        Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
        star (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
      have hspec := hA.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at hspec
      exact hspec
    calc ‖A‖ = ‖(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *
          Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
          star (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)‖ :=
          congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => ‖M‖) hAeq
      _ ≤ ‖(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *
            Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)‖ *
          ‖star (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)‖ *
            ‖Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)‖) *
          ‖star (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)‖ := by
          rw [hU1, hU2, one_mul, mul_one]
      _ = ‖(RCLike.ofReal ∘ hA.eigenvalues : Fin N → ℂ)‖ := Matrix.l2_opNorm_diagonal _
      _ = sSup (Set.range fun i : Fin N => |(hA.eigenvalues i : ℝ)|) := by
          have hnv : ∀ i : Fin N,
              ((‖(RCLike.ofReal (hA.eigenvalues i) : ℂ)‖₊ : NNReal) : ℝ) = |(hA.eigenvalues i : ℝ)| := by
            intro i
            simp
          rw [Pi.norm_def]
          refine le_antisymm ?_ ?_
          · have hC : (0:ℝ) ≤ sSup (Set.range fun i : Fin N => |(hA.eigenvalues i : ℝ)|) :=
              le_trans (abs_nonneg _) (le_csSup hbdd ⟨⟨0, hpos⟩, rfl⟩)
            have hsup : Finset.univ.sup (fun b : Fin N => ‖(RCLike.ofReal (hA.eigenvalues b) : ℂ)‖₊) ≤
                (⟨_, hC⟩ : NNReal) := by
              apply Finset.sup_le
              intro i _
              have h3 : ((‖(RCLike.ofReal (hA.eigenvalues i) : ℂ)‖₊ : NNReal) : ℝ) ≤
                  ((⟨_, hC⟩ : NNReal) : ℝ) := by
                rw [show ((‖(RCLike.ofReal (hA.eigenvalues i) : ℂ)‖₊ : NNReal) : ℝ) =
                    |(hA.eigenvalues i : ℝ)| from hnv i]
                exact le_csSup hbdd ⟨i, rfl⟩
              exact NNReal.coe_le_coe.mp h3
            exact NNReal.coe_le_coe.mpr hsup
          · apply csSup_le hne
            rintro x ⟨i, rfl⟩
            have h1 : (fun b : Fin N => ‖(RCLike.ofReal (hA.eigenvalues b) : ℂ)‖₊) i ≤
                Finset.univ.sup (fun b : Fin N => ‖(RCLike.ofReal (hA.eigenvalues b) : ℂ)‖₊) :=
              Finset.le_sup (f := fun b : Fin N => ‖(RCLike.ofReal (hA.eigenvalues b) : ℂ)‖₊)
                (Finset.mem_univ i)
            have h2 : ((‖(RCLike.ofReal (hA.eigenvalues i) : ℂ)‖₊ : NNReal) : ℝ) ≤
                ((Finset.univ.sup
                  (fun b : Fin N => ‖(RCLike.ofReal (hA.eigenvalues b) : ℂ)‖₊) : NNReal) : ℝ) :=
              NNReal.coe_le_coe.mpr h1
            rw [show ((‖(RCLike.ofReal (hA.eigenvalues i) : ℂ)‖₊ : NNReal) : ℝ) =
              |(hA.eigenvalues i : ℝ)| from hnv i] at h2
            exact h2
  exact le_antisymm hle hge
  /- @proof-region region.target-node.session.b5e8748a6f271739 end -/

end Statlib.Imported

