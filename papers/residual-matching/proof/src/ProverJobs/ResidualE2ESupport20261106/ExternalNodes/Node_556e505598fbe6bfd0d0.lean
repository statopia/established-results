import Lean
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory

namespace ResidualSparseRepair20261106

/-- A finite affine image of independent real standard Gaussians.
    This supplies the joint Gaussian requirement from BvH §2.1.2 / Remark 2.3. -/
def HasStandardGaussianRepresentation {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z0 : Matrix (Fin d) (Fin d) ℂ)
    (G : Ω → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (N : ℕ) (g : Fin N → Ω → ℝ) (B : Fin N → Matrix (Fin d) (Fin d) ℂ),
    (∀ i, Measurable (g i)) ∧ iIndepFun g μ ∧
    (∀ i, Measure.map (g i) μ = gaussianReal 0 1) ∧
    (∀ i, (B i).IsHermitian) ∧
    ∀ ω, G ω = Z0 + ∑ i : Fin N, (g i ω : ℂ) • B i

-- Retained literature input: BvH, Universality and Sharp Matrix Concentration
-- Inequalities, Corollary 2.7 (PDF p.12), norm version of its second inequality.
-- https://web.math.princeton.edu/~rvan/tuniv240625.pdf
-- Only that single consequence is retained, with real symmetric X/G and an
-- explicit Gaussian representation. No arbitrary covariance-matched G is allowed.
-- The paper's complex-vector sigma_* is at most twice the real-vector version
-- below: decompose each complex unit vector into real and imaginary parts,
-- apply the L2 triangle inequality to the four real bilinear forms, and use
-- (||Re u||+||Im u||)(||Re v||+||Im v||) <= 2. The reverse inequality is immediate.
-- This absolute factor is absorbed in the existential universal constant C.
-- Covariances are written without conjugation; for Hermitian X/G the conjugated
-- version is equivalent by swapping the last two entry indices.
axiom bvh_upper_concentration :
    ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (n : ℕ) (hd : 2 ≤ d)
        {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Z0 : Matrix (Fin d) (Fin d) ℂ) (Z : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
        (X : Ω → Matrix (Fin d) (Fin d) ℂ) (G : Ω → Matrix (Fin d) (Fin d) ℂ)
        (hZ0h : Z0.IsHermitian)
        (hZh : ∀ i ω, (Z i ω).IsHermitian)
        (hZmeas : ∀ i a b, Measurable fun ω => Z i ω a b)
        (hZint : ∀ i a b, Integrable (fun ω => Z i ω a b) μ)
        (hZmean : ∀ i a b, ∫ ω, Z i ω a b ∂μ = 0)
        (hZindep : iIndepFun (fun (i : Fin n) (ω : Ω) => Z i ω) μ)
        (hXmeas : ∀ a b, Measurable fun ω => X ω a b)
        (hGmeas : ∀ a b, Measurable fun ω => G ω a b)
        (hXh : ∀ ω, (X ω).IsHermitian) (hGh : ∀ ω, (G ω).IsHermitian)
        (hXreal : ∀ ω a b, (X ω a b).im = 0)
        (hGreal : ∀ ω a b, (G ω a b).im = 0)
        (hGaussian : HasStandardGaussianRepresentation μ Z0 G)
        (hXdef : ∀ ω a b, X ω a b = Z0 a b + ∑ i : Fin n, Z i ω a b)
        (hGmean : ∀ a b, ∫ ω, G ω a b ∂μ = ∫ ω, X ω a b ∂μ)
        (hGcov : ∀ a b c e,
          ∫ ω, ((G ω a b - ∫ ω', G ω' a b ∂μ) * (G ω c e - ∫ ω', G ω' c e ∂μ)) ∂μ =
            ∫ ω, ((X ω a b - ∫ ω', X ω' a b ∂μ) * (X ω c e - ∫ ω', X ω' c e ∂μ)) ∂μ)
        (R sigmaX sigmaStarX : ℝ) (hRpos : 0 ≤ R)
        (hR : ∀ ω, ∀ i : Fin n,
          sSup (Set.range fun q : Fin d => |(hZh i ω).eigenvalues q|) ≤ R)
        (S2 : Matrix (Fin d) (Fin d) ℂ) (hS2herm : S2.IsHermitian)
        (hS2 : ∀ a b : Fin d,
          S2 a b = ∫ ω, (∑ c : Fin d,
            (X ω a c - ∫ ω', X ω' a c ∂μ) * (X ω c b - ∫ ω', X ω' c b ∂μ)) ∂μ)
        (hsigmaXdef : sigmaX =
          Real.sqrt (sSup (Set.range fun q : Fin d => |(hS2herm.eigenvalues q)|)))
        (hsigmaStar : sigmaStarX =
          sSup {y : ℝ | ∃ p : (Fin d → ℝ) × (Fin d → ℝ),
            (∑ a : Fin d, (p.1 a) ^ 2 = 1 ∧ ∑ b : Fin d, (p.2 b) ^ 2 = 1) ∧
              y = Real.sqrt (∫ ω, ‖∑ a : Fin d, ∑ b : Fin d,
                (p.1 a : ℂ) * (X ω a b - ∫ ω', X ω' a b ∂μ) * (p.2 b : ℂ)‖ ^ 2 ∂μ)})
        (hsigmaStarSharp : 0 ≤ sigmaStarX)
        (hsigmaStarBound : sigmaStarX ≤ sigmaX) ,
      ∀ (t : ℝ), 0 ≤ t →
        μ {ω | C * (sigmaStarX * Real.sqrt t +
              R ^ ((1 : ℝ) / 3) * sigmaX ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) + R * t) <
            |sSup (Set.range fun q : Fin d => |(hXh ω).eigenvalues q|) -
              ∫ ω', sSup (Set.range fun q : Fin d => |(hGh ω').eigenvalues q|) ∂μ|} ≤
          ENNReal.ofReal ((d : ℝ) * Real.exp (-t))

#print axioms bvh_upper_concentration
end ResidualSparseRepair20261106

