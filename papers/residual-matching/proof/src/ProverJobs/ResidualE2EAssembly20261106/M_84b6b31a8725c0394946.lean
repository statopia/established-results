import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656

-- External DAG node: ext_model_2 (AXIOM)
example : Prop := (∀ (n r : ℕ) (U X : Matrix (Fin n) (Fin r) ℝ) (hr : 0 < r) (hrn : r ≤ n),
    0 < Statlib.Imported.SMin
      (fun i : Fin r => Statlib.HighDim.MatrixAnalysis.singularValues X
        (Fin.castLE (Nat.le_min.mpr ⟨hrn, le_refl r⟩) i)) →
    (⨅ R : {R : Matrix (Fin r) (Fin r) ℝ // Matrix.transpose R * R = 1},
        Statlib.Imported.frob (U - X * R.1)) ^ 2
      ≤ (2 * (Real.sqrt 2 - 1) *
          Statlib.Imported.SMin
            (fun i : Fin r => Statlib.HighDim.MatrixAnalysis.singularValues X
              (Fin.castLE (Nat.le_min.mpr ⟨hrn, le_refl r⟩) i)) ^ 2)⁻¹ *
          Statlib.Imported.frobSq (U * Matrix.transpose U - X * Matrix.transpose X))
axiom ext_model_2 : (∀ (n r : ℕ) (U X : Matrix (Fin n) (Fin r) ℝ) (hr : 0 < r) (hrn : r ≤ n),
    0 < Statlib.Imported.SMin
      (fun i : Fin r => Statlib.HighDim.MatrixAnalysis.singularValues X
        (Fin.castLE (Nat.le_min.mpr ⟨hrn, le_refl r⟩) i)) →
    (⨅ R : {R : Matrix (Fin r) (Fin r) ℝ // Matrix.transpose R * R = 1},
        Statlib.Imported.frob (U - X * R.1)) ^ 2
      ≤ (2 * (Real.sqrt 2 - 1) *
          Statlib.Imported.SMin
            (fun i : Fin r => Statlib.HighDim.MatrixAnalysis.singularValues X
              (Fin.castLE (Nat.le_min.mpr ⟨hrn, le_refl r⟩) i)) ^ 2)⁻¹ *
          Statlib.Imported.frobSq (U * Matrix.transpose U - X * Matrix.transpose X))

