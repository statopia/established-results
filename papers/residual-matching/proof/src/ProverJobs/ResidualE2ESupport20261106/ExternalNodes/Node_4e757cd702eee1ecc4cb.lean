import Lean
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

-- External DAG node: ext_model_1 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory in (∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ (n : ℕ),
      ∀ {Ω : Type*}, ∀ [MeasurableSpace Ω], ∀ (μ : Measure Ω),
      ∀ [IsProbabilityMeasure μ],
      ∀ (Z0 : Matrix (Fin d) (Fin d) ℂ), Z0.IsHermitian →
      ∀ (Z : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ),
      ∀ (G : Ω → Matrix (Fin d) (Fin d) ℂ),
      iIndepFun (fun (i : Fin n) (ω : Ω) => Z i ω) μ →
      (∀ i ω, (Z i ω).IsHermitian) →
      (∀ i a b, Measurable fun ω => Z i ω a b) →
      (∀ i a b, Integrable (fun ω => Z i ω a b) μ) →
      (∀ i a b, ∫ ω, Z i ω a b ∂μ = 0) →
      (∀ i, Integrable (fun ω => (d : ℝ)⁻¹ * ∑ k : Fin d,
          ((Matrix.isHermitian_conjTranspose_mul_self (Z i ω)).eigenvalues k) ^
            ((3 : ℝ) / 2)) μ) →
      (∀ ω, (G ω).IsHermitian) →
      (∀ a b, Measurable fun ω => G ω a b) →
      (∀ a b, Integrable (fun ω => G ω a b) μ) →
      IsGaussian (μ.map fun ω (p : Fin d × Fin d) => G ω p.1 p.2) →
      (∀ a b, ∫ ω, G ω a b ∂μ = ∫ ω, (Z0 + ∑ i : Fin n, Z i ω) a b ∂μ) →
      (∀ a b c e, ∫ ω, (G ω a b - ∫ ω', G ω' a b ∂μ) *
            (starRingEnd ℂ) (G ω c e - ∫ ω', G ω' c e ∂μ) ∂μ
          = ∫ ω, ((Z0 + ∑ i : Fin n, Z i ω) a b
                - ∫ ω', (Z0 + ∑ i : Fin n, Z i ω') a b ∂μ) * (starRingEnd ℂ)
                ((Z0 + ∑ i : Fin n, Z i ω) c e
                - ∫ ω', (Z0 + ∑ i : Fin n, Z i ω') c e ∂μ) ∂μ) →
      IndepFun (fun ω (p : Fin n × Fin d × Fin d) => Z p.1 ω p.2.1 p.2.2)
        (fun ω (q : Fin d × Fin d) => G ω q.1 q.2) μ →
      ∀ (z : ℂ), 0 < z.im →
        (‖(∫ ω, ((d : ℂ)⁻¹ * Matrix.trace
              ((z • 1 - (Z0 + ∑ i : Fin n, Z i ω))⁻¹)) ∂μ)
            - ∫ ω, ((d : ℂ)⁻¹ * Matrix.trace ((z • 1 - G ω)⁻¹)) ∂μ‖
          ≤ C * (z.im ^ 4)⁻¹ *
              (Finset.univ.sum fun i : Fin n =>
                ∫ ω, (d : ℝ)⁻¹ * ∑ k : Fin d,
                  ((Matrix.isHermitian_conjTranspose_mul_self (Z i ω)).eigenvalues k) ^
                    ((3 : ℝ) / 2) ∂μ))))
axiom ext_model_1 : (open MeasureTheory ProbabilityTheory in (∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ (n : ℕ),
      ∀ {Ω : Type*}, ∀ [MeasurableSpace Ω], ∀ (μ : Measure Ω),
      ∀ [IsProbabilityMeasure μ],
      ∀ (Z0 : Matrix (Fin d) (Fin d) ℂ), Z0.IsHermitian →
      ∀ (Z : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ),
      ∀ (G : Ω → Matrix (Fin d) (Fin d) ℂ),
      iIndepFun (fun (i : Fin n) (ω : Ω) => Z i ω) μ →
      (∀ i ω, (Z i ω).IsHermitian) →
      (∀ i a b, Measurable fun ω => Z i ω a b) →
      (∀ i a b, Integrable (fun ω => Z i ω a b) μ) →
      (∀ i a b, ∫ ω, Z i ω a b ∂μ = 0) →
      (∀ i, Integrable (fun ω => (d : ℝ)⁻¹ * ∑ k : Fin d,
          ((Matrix.isHermitian_conjTranspose_mul_self (Z i ω)).eigenvalues k) ^
            ((3 : ℝ) / 2)) μ) →
      (∀ ω, (G ω).IsHermitian) →
      (∀ a b, Measurable fun ω => G ω a b) →
      (∀ a b, Integrable (fun ω => G ω a b) μ) →
      IsGaussian (μ.map fun ω (p : Fin d × Fin d) => G ω p.1 p.2) →
      (∀ a b, ∫ ω, G ω a b ∂μ = ∫ ω, (Z0 + ∑ i : Fin n, Z i ω) a b ∂μ) →
      (∀ a b c e, ∫ ω, (G ω a b - ∫ ω', G ω' a b ∂μ) *
            (starRingEnd ℂ) (G ω c e - ∫ ω', G ω' c e ∂μ) ∂μ
          = ∫ ω, ((Z0 + ∑ i : Fin n, Z i ω) a b
                - ∫ ω', (Z0 + ∑ i : Fin n, Z i ω') a b ∂μ) * (starRingEnd ℂ)
                ((Z0 + ∑ i : Fin n, Z i ω) c e
                - ∫ ω', (Z0 + ∑ i : Fin n, Z i ω') c e ∂μ) ∂μ) →
      IndepFun (fun ω (p : Fin n × Fin d × Fin d) => Z p.1 ω p.2.1 p.2.2)
        (fun ω (q : Fin d × Fin d) => G ω q.1 q.2) μ →
      ∀ (z : ℂ), 0 < z.im →
        (‖(∫ ω, ((d : ℂ)⁻¹ * Matrix.trace
              ((z • 1 - (Z0 + ∑ i : Fin n, Z i ω))⁻¹)) ∂μ)
            - ∫ ω, ((d : ℂ)⁻¹ * Matrix.trace ((z • 1 - G ω)⁻¹)) ∂μ‖
          ≤ C * (z.im ^ 4)⁻¹ *
              (Finset.univ.sum fun i : Fin n =>
                ∫ ω, (d : ℝ)⁻¹ * ∑ k : Fin d,
                  ((Matrix.isHermitian_conjTranspose_mul_self (Z i ω)).eigenvalues k) ^
                    ((3 : ℝ) / 2) ∂μ))))

