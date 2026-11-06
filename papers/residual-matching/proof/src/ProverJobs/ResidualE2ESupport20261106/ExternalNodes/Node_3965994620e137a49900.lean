import Lean
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory

namespace ResidualSparseRepair20261106

-- Retained literature input: BvH Theorem 3.16, proof §9.2, and (3.4).
-- Homogeneous independent-entry specialization; not an internally proved theorem.
axiom bvh_lower_edge :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
        {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → Matrix (Fin m) (Fin n) ℝ)
        (hA_meas : ∀ i j, Measurable (fun ω => A ω i j))
        (hA_int : ∀ i j, Integrable (fun ω => A ω i j) μ ∧
          Integrable (fun ω => (A ω i j) ^ 2) μ)
        (hA_indep : iIndepFun (fun (ij : Fin m × Fin n) ω => A ω ij.1 ij.2) μ)
        (hA_mean : ∀ i j, ∫ ω, A ω i j ∂μ = 0)
        (hA_var : ∀ i j, ∫ ω, (A ω i j) ^ 2 ∂μ = 1 / (m : ℝ))
        (R : ℝ) (hR : 0 ≤ R)
        (hA_bound : ∀ᵐ ω ∂μ, ∀ i j, |A ω i j| ≤ R)
        (t : ℝ) (ht : 0 ≤ t),
        μ {ω | Statlib.Imported.svals (A ω) ⟨n - 1, by omega⟩ <
            1 - Real.sqrt ((n : ℝ) / (m : ℝ)) - 3 * C *
              (Real.rpow (m : ℝ) (-(1 / 4)) * Real.rpow (Real.log (m : ℝ)) (3 / 4)
                + Real.rpow (m : ℝ) (-(1 / 2)) * Real.sqrt t
                + Real.rpow R (1 / 3) * Real.rpow t (2 / 3) + R * t)} ≤
          ENNReal.ofReal (6 * (m : ℝ) * Real.exp (-t))

#print axioms bvh_lower_edge
end ResidualSparseRepair20261106

