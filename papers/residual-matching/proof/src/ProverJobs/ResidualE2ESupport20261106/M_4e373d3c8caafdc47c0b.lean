import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianStein
import Lean
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianStein

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory

namespace ResidualSparseRepair20261106.GaussianCalculus

private theorem derivative_projection (p : ℕ) (f : (Fin p → ℝ) → ℂ)
    (hf : ∀ x j, Differentiable ℝ (fun t : ℝ => f (Function.update x j t)))
    (L : ℂ →L[ℝ] ℝ) (x : Fin p → ℝ) (j : Fin p) :
    deriv (fun t : ℝ => L (f (Function.update x j t))) (x j) =
      L (deriv (fun t : ℝ => f (Function.update x j t)) (x j)) := by
  exact (L.hasFDerivAt.comp_hasDerivAt (x j) ((hf x j (x j)).hasDerivAt)).deriv

theorem standard_product_stein_complex (p : ℕ) (hp : 0 < p)
    (f : (Fin p → ℝ) → ℂ)
    (hf_bdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hf_diff : ∀ x j, Differentiable ℝ (fun t : ℝ => f (Function.update x j t)))
    (hf_int : ∀ j, Integrable (fun x => (x j : ℂ) * f x)
      (Measure.pi (fun _ : Fin p => gaussianReal 0 1)))
    (hf_int_deriv : ∀ j, Integrable (fun x =>
      deriv (fun t : ℝ => f (Function.update x j t)) (x j))
      (Measure.pi (fun _ : Fin p => gaussianReal 0 1))) :
    ∀ j, (∫ x, (x j : ℂ) * f x ∂(Measure.pi (fun _ : Fin p => gaussianReal 0 1))) =
      ∫ x, deriv (fun t : ℝ => f (Function.update x j t)) (x j)
        ∂(Measure.pi (fun _ : Fin p => gaussianReal 0 1)) := by
  let μ := Measure.pi (fun _ : Fin p => gaussianReal 0 1)
  have project (L : ℂ →L[ℝ] ℝ) (j : Fin p) :
      (∫ x, x j * L (f x) ∂μ) =
        ∫ x, L (deriv (fun t : ℝ => f (Function.update x j t)) (x j)) ∂μ := by
    have hb : ∃ C : ℝ, ∀ x, |L (f x)| ≤ C := by
      obtain ⟨C, hC⟩ := hf_bdd
      refine ⟨‖L‖ * C, fun x => ?_⟩
      have h1 : |L (f x)| ≤ ‖L‖ * ‖f x‖ := by
        simpa only [Real.norm_eq_abs] using L.le_opNorm (f x)
      exact h1.trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))
    have hd : ∀ x j, Differentiable ℝ (fun t : ℝ => L (f (Function.update x j t))) :=
      fun x j => L.differentiable.comp (hf_diff x j)
    have hi : ∀ j, Integrable (fun x => x j * L (f x)) μ := by
      intro j
      simpa only [← Complex.real_smul, map_smul, smul_eq_mul] using
        L.integrable_comp (hf_int j)
    have hid : ∀ j, Integrable (fun x =>
        deriv (fun t : ℝ => L (f (Function.update x j t))) (x j)) μ := by
      intro j
      simp_rw [derivative_projection p f hf_diff L]
      exact L.integrable_comp (hf_int_deriv j)
    have h := Statlib.StatFoundation.Convergence.steinIdentity_diagonal_gaussianVector
      p hp (fun _ => 1) (by intro j; norm_num) μ rfl (by infer_instance)
      (fun x => L (f x)) hb hd hi hid j
    simp_rw [derivative_projection p f hf_diff L] at h
    simpa only [NNReal.coe_one, one_mul] using h
  intro j
  apply Complex.ext
  · have h := project Complex.reCLM j
    change Complex.reCLM (∫ x, (x j : ℂ) * f x ∂μ) =
      Complex.reCLM (∫ x, deriv (fun t : ℝ => f (Function.update x j t)) (x j) ∂μ)
    rw [← Complex.reCLM.integral_comp_comm (hf_int j),
      ← Complex.reCLM.integral_comp_comm (hf_int_deriv j)]
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using h
  · have h := project Complex.imCLM j
    change Complex.imCLM (∫ x, (x j : ℂ) * f x ∂μ) =
      Complex.imCLM (∫ x, deriv (fun t : ℝ => f (Function.update x j t)) (x j) ∂μ)
    rw [← Complex.imCLM.integral_comp_comm (hf_int j),
      ← Complex.imCLM.integral_comp_comm (hf_int_deriv j)]
    simpa only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using h

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.standard_product_stein_complex

