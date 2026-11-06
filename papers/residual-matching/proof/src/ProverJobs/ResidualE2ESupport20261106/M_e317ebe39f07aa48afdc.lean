import Lean
import ProverJobs.ResidualE2ESupport20261106.M_707ea02fa582735d59c3
import ProverJobs.ResidualE2ESupport20261106.M_2864ef2bb5c92a2242e0
import ProverJobs.ResidualE2ESupport20261106.M_b828eaea2831fe887898
import ProverJobs.ResidualE2ESupport20261106.M_19397ecf43739ad33005

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory
namespace ResidualSparseRepair20261106.DenseGaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianTail _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

theorem denseSymmetricPolynomialRate_one_ninth : DenseSymmetricPolynomialRate (1 / 9) := by
  intro rhoMinus hmin hmin1
  obtain ⟨C, hC, hbound⟩ := gaussian_sym_sqrt_cdf_polynomial_rate rhoMinus hmin
  refine ⟨C, hC, 2, ?_⟩
  intro m n hm hn hnm hratio hrho1 x
  have hm1 : 1 ≤ m := by omega
  have hh := hbound m n hm hn hnm hratio x
  rw [gaussianExpectedCovariance_symmetric_cdf m n hm1 hn x,
    symmetricSqrtMP_cdf_eq_density ((n : ℝ) / m) (lt_of_lt_of_le hmin hratio) hrho1 x] at hh
  exact hh

end ResidualSparseRepair20261106.DenseGaussian

#print axioms ResidualSparseRepair20261106.DenseGaussian.denseSymmetricPolynomialRate_one_ninth

