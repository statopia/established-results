import Lean
import ProverJobs.ResidualE2ESupport20261106.M_5f4ada936965058f2e9c
import ProverJobs.ResidualE2ESupport20261106.M_a75ea75a9ac4707e1a61

namespace PaperProofTasks.ResidualE2ESupport20261106

open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianCalculus
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianResolventBounds

theorem normalized_pointwise_loop {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : A.conjTranspose = A.transpose)
    (z : ℂ) (hz : 0 < z.im) :
    ((∑ i : Fin m, ∑ j : Fin n, A i j * (A * gramResolvent A z) i j) -
      (∑ i : Fin m, ∑ j : Fin n,
        weightedResolventDerivative A (Matrix.single i j (1 : ℂ)) z i j)) =
      (m : ℂ) * n *
        (1 + (z + (n : ℂ) / m - 1 + (m : ℂ)⁻¹) * normalizedGramTrace A z +
          ((n : ℂ) / m) * z * normalizedGramTrace A z ^ 2 +
          (z / m) * normalizedGramSquareTrace A z) := by
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hgram : A.transpose * A = (m : ℝ) • gramMatrix A := by
    rw [gramMatrix, hA, smul_smul, mul_inv_cancel₀ hmne, one_smul]
  rw [weighted_entry_contraction, hgram, Matrix.smul_mul, Matrix.trace_smul,
    gram_mul_resolvent_identity A z hz,
    weighted_derivative_trace_polynomial A hA z hz]
  simp only [Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, Matrix.trace_smul,
    smul_eq_mul, Complex.real_smul, Complex.ofReal_natCast,
    normalizedGramTrace, normalizedGramSquareTrace]
  field_simp
  <;> ring

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.normalized_pointwise_loop

