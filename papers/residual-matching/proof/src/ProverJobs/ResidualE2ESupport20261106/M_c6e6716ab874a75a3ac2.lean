import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_fa8bbc31a4e4e2df874d
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106.Statlib.Imported

theorem sv_eq_sparse_svals {m n : ℕ} (hnm : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    sv hnm A i = _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals A i := by
  unfold sv _root_.Statlib.HighDim.MatrixAnalysis.singularValues
    _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported.svals
  rfl

end ResidualLoss20261106.Statlib.Imported

