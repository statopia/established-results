import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianStein
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open Statlib.StatFoundation.RandomVariable.Gaussian

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3953135755_4b3e498f : ∀ (n : ℕ) (hn : 1 ≤ n)
    (Lambda : Matrix (Fin n) (Fin n) ℝ) (hLambda : Lambda.PosSemidef)
    (Phi : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hPhi_meas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Phi p.1 p.2))
    (hPhi_bdd : ∃ C : ℝ, ∀ x y' : Fin n → ℝ, |Phi x y'| ≤ C)
    (hPhi_diff : ∀ y' : Fin n → ℝ, ContDiff ℝ 1 (fun x : Fin n → ℝ => Phi x y'))
    (y : Fin n → ℝ)
    (hint_coord : ∀ j : Fin n,
      Integrable (fun z : Fin n → ℝ => z j * Phi (Slepian.canonicalGaussianVector Lambda z) y)
        (standardPi n))
    (hint_deriv : ∀ l : Fin n,
      Integrable (fun z : Fin n → ℝ =>
          deriv (fun s : ℝ =>
              Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
            ((Slepian.canonicalGaussianVector Lambda z) l))
        (standardPi n))
    (k : Fin n),
    ∫ z, (Slepian.canonicalGaussianVector Lambda z) k *
          Phi (Slepian.canonicalGaussianVector Lambda z) y ∂(standardPi n)
      = ∑ l : Fin n, Lambda k l *
          ∫ z, deriv (fun s : ℝ =>
                Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
              ((Slepian.canonicalGaussianVector Lambda z) l) ∂(standardPi n) := by
  /- @proof-region region.target-node.session.4787e68a747d2de6 begin -/
  intro n hn Lambda hLambda Phi hPhi_meas hPhi_bdd hPhi_diff y hint_coord hint_deriv k
  have hpos : 0 < n := by omega
  have hsp : standardPi n
      = Measure.pi (fun i : Fin n => gaussianReal 0 ((fun _ => (1 : NNReal)) i)) := rfl
  have hcv : ∀ z : Fin n → ℝ,
      Slepian.canonicalGaussianVector Lambda z = (CFC.sqrt Lambda).mulVec z := by
    intro z
    first
      | rfl
      | exact Slepian.matrixMulVecCLM_apply (CFC.sqrt Lambda) z
  have hsp_prob : IsProbabilityMeasure (standardPi n) := Slepian.standardPi_probability n
  have hAA : CFC.sqrt Lambda * CFC.sqrt Lambda = Lambda := Matrix.PosSemidef.sqrt_mul_self hLambda
  have hAsym : Matrix.transpose (CFC.sqrt Lambda) = CFC.sqrt Lambda := by
    have hh : (CFC.sqrt Lambda).IsHermitian :=
      Matrix.PosSemidef.isHermitian (Matrix.PosSemidef.posSemidef_sqrt (A := Lambda))
    have h1 : (CFC.sqrt Lambda).conjTranspose = CFC.sqrt Lambda := hh.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  have hcv_update : ∀ (x : Fin n → ℝ) (j : Fin n) (t : ℝ),
      Slepian.canonicalGaussianVector Lambda (Function.update x j t)
        = Slepian.canonicalGaussianVector Lambda x
          + (t - x j) • ((CFC.sqrt Lambda).mulVec (Pi.single j 1)) := by
    intro x j t
    have hupd : Function.update x j t = x + (t - x j) • (Pi.single j 1 : Fin n → ℝ) := by
      funext m
      by_cases hm : m = j
      · simp [Function.update, hm]
        try ring
      · simp [Function.update, hm]
    simp only [hcv]
    rw [hupd]
    simp only [← Matrix.mulVecLin_apply, map_add, map_smul]
  have hmulvec_apply : ∀ (v : Fin n → ℝ) (i : Fin n),
      ((CFC.sqrt Lambda).mulVec v) i = ∑ j : Fin n, (CFC.sqrt Lambda) i j * v j := by
    intro v i
    first
      | rfl
      | simp [Matrix.mulVec, Matrix.dotProduct]
  have hpi_single : ∀ (w : Fin n → ℝ), w = ∑ l : Fin n, w l • (Pi.single l 1 : Fin n → ℝ) := by
    intro w
    funext m
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hbm
      simp [Pi.single_apply, Ne.symm hbm]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  have hf_bdd : ∃ C : ℝ, ∀ x : Fin n → ℝ,
      |Phi (Slepian.canonicalGaussianVector Lambda x) y| ≤ C := by
    obtain ⟨C, hC⟩ := hPhi_bdd
    exact ⟨C, fun x => hC _ y⟩
  have hf_diff : ∀ (x : Fin n → ℝ) (j : Fin n),
      Differentiable ℝ (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update x j t)) y) := by
    intro x j
    have hΦ : Differentiable ℝ (fun u : Fin n → ℝ => Phi u y) :=
      (hPhi_diff y).differentiable (by simp)
    have hline : Differentiable ℝ (fun t : ℝ =>
        Slepian.canonicalGaussianVector Lambda x + (t - x j) • ((CFC.sqrt Lambda).mulVec (Pi.single j 1))) := by
      fun_prop
    have heq : (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update x j t)) y)
        = fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda x + (t - x j) • ((CFC.sqrt Lambda).mulVec (Pi.single j 1))) y := by
      funext t
      rw [hcv_update]
    rw [heq]
    exact hΦ.comp hline
  have hpartial : ∀ (z : Fin n → ℝ) (l : Fin n),
      deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
          ((Slepian.canonicalGaussianVector Lambda z) l)
        = (fderiv ℝ (fun u : Fin n → ℝ => Phi u y) (Slepian.canonicalGaussianVector Lambda z)) (Pi.single l 1) := by
    intro z l
    have hF : HasFDerivAt (fun u : Fin n → ℝ => Phi u y)
        (fderiv ℝ (fun u : Fin n → ℝ => Phi u y) (Slepian.canonicalGaussianVector Lambda z))
        (Slepian.canonicalGaussianVector Lambda z) :=
      (((hPhi_diff y).differentiable (by simp)).differentiableAt).hasFDerivAt
    have hF' : HasFDerivAt (fun u : Fin n → ℝ => Phi u y)
        (fderiv ℝ (fun u : Fin n → ℝ => Phi u y)
          (Function.update (Slepian.canonicalGaussianVector Lambda z) l ((Slepian.canonicalGaussianVector Lambda z) l)))
        (Function.update (Slepian.canonicalGaussianVector Lambda z) l ((Slepian.canonicalGaussianVector Lambda z) l)) := by
      rw [Function.update_eq_self]
      exact hF
    have hupd : HasDerivAt (Function.update (Slepian.canonicalGaussianVector Lambda z) l)
        (Pi.single l 1) ((Slepian.canonicalGaussianVector Lambda z) l) :=
      hasDerivAt_update (Slepian.canonicalGaussianVector Lambda z) l ((Slepian.canonicalGaussianVector Lambda z) l)
    have hcomp := HasFDerivAt.comp_hasDerivAt ((Slepian.canonicalGaussianVector Lambda z) l) hF' hupd
    have hd := hcomp.deriv
    rw [Function.update_eq_self] at hd
    exact hd
  have hsingle : ∀ (z : Fin n → ℝ) (j : Fin n), True := fun _ _ => trivial
  have hchain : ∀ (z : Fin n → ℝ) (j : Fin n),
      deriv (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update z j t)) y) (z j)
        = ∑ l : Fin n, (CFC.sqrt Lambda) l j *
            deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
              ((Slepian.canonicalGaussianVector Lambda z) l) := by
    intro z j
    have hfun : (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update z j t)) y)
        = fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda z + (t - z j) • ((CFC.sqrt Lambda).mulVec (Pi.single j 1))) y := by
      funext t
      rw [hcv_update]
    rw [hfun]
    have hderiv_eq : deriv (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda z + (t - z j) • ((CFC.sqrt Lambda).mulVec (Pi.single j 1))) y) (z j)
        = (fderiv ℝ (fun u : Fin n → ℝ => Phi u y) (Slepian.canonicalGaussianVector Lambda z)) ((CFC.sqrt Lambda).mulVec (Pi.single j 1)) := by
      have hF : HasFDerivAt (fun u : Fin n → ℝ => Phi u y)
          (fderiv ℝ (fun u : Fin n → ℝ => Phi u y)
            (Slepian.canonicalGaussianVector Lambda z + (z j - z j) • ((CFC.sqrt Lambda).mulVec (Pi.single j 1))))
          (Slepian.canonicalGaussianVector Lambda z + (z j - z j) • ((CFC.sqrt Lambda).mulVec (Pi.single j 1))) :=
        (((hPhi_diff y).differentiable (by simp)).differentiableAt).hasFDerivAt
      have hcurve : HasDerivAt (fun t : ℝ => Slepian.canonicalGaussianVector Lambda z + (t - z j) • ((CFC.sqrt Lambda).mulVec (Pi.single j 1)))
          ((CFC.sqrt Lambda).mulVec (Pi.single j 1)) (z j) := by
        rw [hasDerivAt_pi]
        intro m
        have h1 : HasDerivAt (fun t : ℝ => t - z j) 1 (z j) := (hasDerivAt_id (z j)).sub_const (z j)
        have h2 : HasDerivAt (fun t : ℝ => (t - z j) * ((CFC.sqrt Lambda).mulVec (Pi.single j 1)) m)
            (1 * ((CFC.sqrt Lambda).mulVec (Pi.single j 1)) m) (z j) := h1.mul_const _
        have h3 : HasDerivAt (fun t : ℝ => Slepian.canonicalGaussianVector Lambda z m + (t - z j) * ((CFC.sqrt Lambda).mulVec (Pi.single j 1)) m)
            (1 * ((CFC.sqrt Lambda).mulVec (Pi.single j 1)) m) (z j) := h2.const_add _
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] using h3
      have hcomp := HasFDerivAt.comp_hasDerivAt (z j) hF hcurve
      have hd := hcomp.deriv
      simpa [sub_self, zero_smul, add_zero] using hd
    rw [hderiv_eq]
    have hsingle' : ∀ l : Fin n, ((CFC.sqrt Lambda).mulVec (Pi.single j 1)) l = (CFC.sqrt Lambda) l j := by
      intro l
      rw [hmulvec_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hbj
        simp [Pi.single_apply, hbj]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hsum : (fderiv ℝ (fun u : Fin n → ℝ => Phi u y) (Slepian.canonicalGaussianVector Lambda z))
          ((CFC.sqrt Lambda).mulVec (Pi.single j 1))
        = ∑ l : Fin n, (CFC.sqrt Lambda) l j *
            ((fderiv ℝ (fun u : Fin n → ℝ => Phi u y) (Slepian.canonicalGaussianVector Lambda z)) (Pi.single l 1)) := by
      conv_lhs => rw [hpi_single ((CFC.sqrt Lambda).mulVec (Pi.single j 1))]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, hsingle']
    rw [hsum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [← hpartial z l]
  have hint_deriv' : ∀ j : Fin n,
      Integrable (fun z : Fin n → ℝ => deriv (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update z j t)) y) (z j)) (standardPi n) := by
    intro j
    have heq : (fun z : Fin n → ℝ => deriv (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update z j t)) y) (z j))
        = fun z : Fin n → ℝ => ∑ l : Fin n, (CFC.sqrt Lambda) l j *
            deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y) ((Slepian.canonicalGaussianVector Lambda z) l) := by
      funext z
      exact hchain z j
    rw [heq]
    exact MeasureTheory.integrable_finset_sum Finset.univ (fun l _ => (hint_deriv l).const_mul ((CFC.sqrt Lambda) l j))
  have hstein : ∀ j : Fin n,
      ∫ z, z j * Phi (Slepian.canonicalGaussianVector Lambda z) y ∂(standardPi n)
        = ∫ z, deriv (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update z j t)) y) (z j) ∂(standardPi n) := by
    intro j
    have h := Statlib.StatFoundation.Convergence.steinIdentity_diagonal_gaussianVector n hpos (fun _ => (1 : NNReal))
      (by intro i; simp) (standardPi n) hsp hsp_prob
      (fun z => Phi (Slepian.canonicalGaussianVector Lambda z) y) hf_bdd hf_diff hint_coord hint_deriv'
    simpa using h j
  have step1 : ∫ z, (Slepian.canonicalGaussianVector Lambda z) k * Phi (Slepian.canonicalGaussianVector Lambda z) y ∂(standardPi n)
      = ∑ i : Fin n, (CFC.sqrt Lambda) k i * ∫ z, z i * Phi (Slepian.canonicalGaussianVector Lambda z) y ∂(standardPi n) := by
    have hF : (fun z : Fin n → ℝ => (Slepian.canonicalGaussianVector Lambda z) k * Phi (Slepian.canonicalGaussianVector Lambda z) y)
        = fun z : Fin n → ℝ => ∑ i : Fin n, (CFC.sqrt Lambda) k i * (z i * Phi (Slepian.canonicalGaussianVector Lambda z) y) := by
      funext z
      rw [hcv z, hmulvec_apply]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hF]
    rw [MeasureTheory.integral_finset_sum (Finset.univ)
      (fun i _ => (hint_coord i).const_mul ((CFC.sqrt Lambda) k i))]
    exact Finset.sum_congr rfl (fun i _ => MeasureTheory.integral_const_mul ((CFC.sqrt Lambda) k i)
      (fun z => z i * Phi (Slepian.canonicalGaussianVector Lambda z) y))
  have step2 : ∑ i : Fin n, (CFC.sqrt Lambda) k i * ∫ z, z i * Phi (Slepian.canonicalGaussianVector Lambda z) y ∂(standardPi n)
      = ∑ i : Fin n, (CFC.sqrt Lambda) k i *
          ∫ z, deriv (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update z i t)) y) (z i) ∂(standardPi n) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hstein i]
  have step3 : ∀ i : Fin n,
      ∫ z, deriv (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update z i t)) y) (z i) ∂(standardPi n)
        = ∑ l : Fin n, (CFC.sqrt Lambda) l i *
            (∫ z, deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
              ((Slepian.canonicalGaussianVector Lambda z) l) ∂(standardPi n)) := by
    intro i
    have hF : (fun z : Fin n → ℝ => deriv (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update z i t)) y) (z i))
        = fun z : Fin n → ℝ => ∑ l : Fin n, (CFC.sqrt Lambda) l i *
            deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
              ((Slepian.canonicalGaussianVector Lambda z) l) := by
      funext z
      exact hchain z i
    rw [hF]
    rw [MeasureTheory.integral_finset_sum (Finset.univ)
      (fun l _ => (hint_deriv l).const_mul ((CFC.sqrt Lambda) l i))]
    exact Finset.sum_congr rfl (fun l _ => MeasureTheory.integral_const_mul ((CFC.sqrt Lambda) l i)
      (fun z => deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
        ((Slepian.canonicalGaussianVector Lambda z) l)))
  have step4 : ∑ i : Fin n, (CFC.sqrt Lambda) k i *
        (∑ l : Fin n, (CFC.sqrt Lambda) l i *
          (∫ z, deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
            ((Slepian.canonicalGaussianVector Lambda z) l) ∂(standardPi n)))
      = ∑ l : Fin n, (∑ i : Fin n, (CFC.sqrt Lambda) k i * (CFC.sqrt Lambda) l i) *
          (∫ z, deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
            ((Slepian.canonicalGaussianVector Lambda z) l) ∂(standardPi n)) := by
    have h1 : ∀ i : Fin n, (CFC.sqrt Lambda) k i *
          (∑ l : Fin n, (CFC.sqrt Lambda) l i *
            (∫ z, deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
              ((Slepian.canonicalGaussianVector Lambda z) l) ∂(standardPi n)))
        = ∑ l : Fin n, (CFC.sqrt Lambda) k i * (CFC.sqrt Lambda) l i *
            (∫ z, deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
              ((Slepian.canonicalGaussianVector Lambda z) l) ∂(standardPi n)) := by
      intro i
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro l _
      ring
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [← Finset.sum_mul]
  have hcoef : ∀ l : Fin n, (∑ i : Fin n, (CFC.sqrt Lambda) k i * (CFC.sqrt Lambda) l i) = Lambda k l := by
    intro l
    have hsym : ∀ i : Fin n, (CFC.sqrt Lambda) l i = (CFC.sqrt Lambda) i l := by
      intro i
      have hh := congrFun (congrFun hAsym l) i
      rw [Matrix.transpose_apply] at hh
      exact hh.symm
    have h1 : (∑ i : Fin n, (CFC.sqrt Lambda) k i * (CFC.sqrt Lambda) l i)
        = ∑ i : Fin n, (CFC.sqrt Lambda) k i * (CFC.sqrt Lambda) i l := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsym i]
    rw [h1, ← Matrix.mul_apply]
    exact congrFun (congrFun hAA k) l
  calc ∫ z, (Slepian.canonicalGaussianVector Lambda z) k * Phi (Slepian.canonicalGaussianVector Lambda z) y ∂(standardPi n)
      = ∑ i : Fin n, (CFC.sqrt Lambda) k i * ∫ z, z i * Phi (Slepian.canonicalGaussianVector Lambda z) y ∂(standardPi n) := step1
    _ = ∑ i : Fin n, (CFC.sqrt Lambda) k i *
          ∫ z, deriv (fun t : ℝ => Phi (Slepian.canonicalGaussianVector Lambda (Function.update z i t)) y) (z i) ∂(standardPi n) := step2
    _ = ∑ i : Fin n, (CFC.sqrt Lambda) k i *
          (∑ l : Fin n, (CFC.sqrt Lambda) l i *
            (∫ z, deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
              ((Slepian.canonicalGaussianVector Lambda z) l) ∂(standardPi n))) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [step3 i]
    _ = ∑ l : Fin n, (∑ i : Fin n, (CFC.sqrt Lambda) k i * (CFC.sqrt Lambda) l i) *
          (∫ z, deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
            ((Slepian.canonicalGaussianVector Lambda z) l) ∂(standardPi n)) := step4
    _ = ∑ l : Fin n, Lambda k l *
          (∫ z, deriv (fun s : ℝ => Phi (Function.update (Slepian.canonicalGaussianVector Lambda z) l s) y)
            ((Slepian.canonicalGaussianVector Lambda z) l) ∂(standardPi n)) := by
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [hcoef l]
  /- @proof-region region.target-node.session.4787e68a747d2de6 end -/

end Statlib.Imported

