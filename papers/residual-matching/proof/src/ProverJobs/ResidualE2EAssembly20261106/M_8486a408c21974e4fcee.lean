import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548
import ProverJobs.ResidualE2EAssembly20261106.M_7f3eea621b0d2e005d06
import ProverJobs.ResidualE2EAssembly20261106.M_eeb0c48628f53be1e6d9

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching


run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false in
theorem statopia_math_node_76282859_7583a873 : ∀ {m n r : ℕ} (p Lam th : ℝ)
    (mask : Matrix (Fin m) (Fin n) ℝ) (U0 : Matrix (Fin m) (Fin r) ℝ)
    (V0 : Matrix (Fin n) (Fin r) ℝ)
    (hGood :
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
        p Lam th mask U0 V0),
    PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.MaskEvent
      Lam th p mask
      (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.tangentSpace
        U0 V0) := by
  /- @proof-region region.target-node.session.41f62bdb1ef443c2 begin -/
  intro m n r p Lam th mask U0 V0 hGood
  have hTO : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p mask A =
        PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.TOm p mask A := by
    intro A
    ext i j
    simp [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask,
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Wmask,
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.TOm,
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.projMask] <;> ring
  have hiT : ∀ X Y : Matrix (Fin m) (Fin n) ℝ,
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.innerTrace X Y =
        PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.innerTrace Y X := by
    intro X Y
    simp only [PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.innerTrace]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hconv : ∀ X Y : Matrix (Fin m) (Fin n) ℝ,
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.innerTrace X Y =
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner X Y := by
    intro X Y
    simp only [PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.innerTrace,
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobInner]
  have hbF : ∀ {m' k l : ℕ} (A : Matrix (Fin m') (Fin k) ℝ) (C : Matrix (Fin m') (Fin l) ℝ),
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.bFactor A C =
        PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.bFactor C A := by
    intro m' k l A C
    simp only [PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.bFactor]
    rw [mul_comm (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frob C)
        (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm A),
      mul_comm (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm C)
        (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frob A),
      min_comm]
  unfold PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.MaskEvent
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hGood.1
  · intro k L R
    rw [← hTO (L * Rᵀ)]
    exact hGood.2.2.2 k L R
  · intro k l A1 A2 B1 B2
    have h3 := hGood.2.2.1 l k B1 B2 A1 A2
    rw [hiT (A1 * A2ᵀ) (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.TOm p mask (B1 * B2ᵀ)),
      ← hTO (B1 * B2ᵀ),
      hconv (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p mask (B1 * B2ᵀ)) (A1 * A2ᵀ),
      hbF A1 B1, hbF A2 B2]
    exact h3
  · intro X hX
    have hmem : PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect U0 V0 X := by
      have hspan :
          PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.tangentSpace U0 V0 =
            Submodule.span ℝ {M : Matrix (Fin m) (Fin n) ℝ |
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect U0 V0 M} :=
        rfl
      rw [hspan] at hX
      have hle :
          Submodule.span ℝ {M : Matrix (Fin m) (Fin n) ℝ |
              PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect U0 V0 M} ≤
            { carrier := {M : Matrix (Fin m) (Fin n) ℝ |
                PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.MemTangentRect U0 V0 M}
              zero_mem' := ⟨0, 0, by simp⟩
              add_mem' := by
                intro Y Z hY hZ
                obtain ⟨A1, B1, rfl⟩ := hY
                obtain ⟨A2, B2, rfl⟩ := hZ
                exact ⟨A1 + A2, B1 + B2, by
                  simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
                  abel⟩
              smul_mem' := by
                intro c Y hY
                obtain ⟨A1, B1, rfl⟩ := hY
                exact ⟨c • A1, c • B1, by
                  simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_add]⟩ } :=
        Submodule.span_le.mpr (fun Y hY => hY)
      exact hle hX
    have h2 := hGood.2.1 X X hmem hmem
    have hsq : th * PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frob X ^ 2 =
        th * PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm X *
          PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm X := by
      simp only [PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frob,
        PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq,
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.frobNorm] <;> ring
    rw [hiT X (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.TOm p mask X),
      ← hTO X,
      hconv (PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p mask X) X,
      hsq]
    have h2' := h2
    exact h2'
  /- @proof-region region.target-node.session.41f62bdb1ef443c2 end -/

end Statlib.Imported

