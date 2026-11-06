import Lean
import Mathlib

namespace PaperProofTasks.ResidualE2ESupport20261106

-- Shared append-only definitions for the root theorem and every Math node.
-- Node Formalize may add def/abbrev/structure/class/inductive declarations here.

/-! ## Symmetrized Stieltjes transforms and the Gaussian comparator law -/

/-- The Stieltjes transform `m_ν(z) = ∫ (x - z)⁻¹ dν(x)` at a complex point `z` of the
symmetrized empirical singular-value measure
`ν = (2n)⁻¹ ∑_{i : Fin n} (δ_{s i} + δ_{-(s i)})` attached to a family `s : Fin n → ℝ` of
singular values. -/
noncomputable def symStieltjesSvals {n : ℕ} (s : Fin n → ℝ) (z : ℂ) : ℂ :=
  ((2 * (n : ℝ))⁻¹ : ℂ) *
    (∑ i : Fin n, (((s i : ℂ) - z)⁻¹ + (-(s i : ℂ) - z)⁻¹))

/-- The law of an `m × n` array of independent standard normal entries (written as a function
of two indices, i.e. as an element of `Matrix (Fin m) (Fin n) ℝ` up to definitional
equality), i.e. the law of the Gaussian comparator `G₀ = m^{-1/2} (g_{ij})` before the
deterministic rescaling `m^{-1/2}`. -/
noncomputable def stdNormalMatrixMeasure (m n : ℕ) :
    MeasureTheory.Measure (Fin m → Fin n → ℝ) :=
  MeasureTheory.Measure.pi
    (fun _ : Fin m =>
      MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))

/-! ## The Marchenko–Pastur law and its Stieltjes transform -/

/-- The Marchenko–Pastur density with aspect ratio `rho` in the normalization with entry
variance `1/m`, i.e. the density supported on `[(1 - √rho)^2, (1 + √rho)^2]` given by
`f_ρ(x) = (2 π ρ x)⁻¹ √(((1+√ρ)^2 - x) (x - (1-√ρ)^2))`, and `0` outside the support. -/
noncomputable def mpDensity (rho x : ℝ) : ℝ :=
  (1 / (2 * Real.pi * rho * x)) *
      Real.sqrt
        (((1 + Real.sqrt rho) ^ 2 - x) * (x - (1 - Real.sqrt rho) ^ 2)) *
    (if (1 - Real.sqrt rho) ^ 2 ≤ x ∧ x ≤ (1 + Real.sqrt rho) ^ 2 then (1 : ℝ) else 0)

/-- The Stieltjes transform `s_ρ(z) = ∫ (x - z)⁻¹ dMP_ρ(x)` of the Marchenko–Pastur law with
aspect ratio `ρ = n/m` (normalization with entry variance `1/m`). This is the closed-form
solution of the Marchenko–Pastur self-consistent equation
`s_ρ(z) = ((1 - ρ - z) - ρ z s_ρ(z))⁻¹` that is analytic on the upper half plane `Im z > 0`. -/
noncomputable def mpStieltjes (rho : ℝ) (z : ℂ) : ℂ :=
  MeasureTheory.integral MeasureTheory.volume
    (fun x : ℝ => ((x : ℂ) - z)⁻¹ * (mpDensity rho x : ℂ))

