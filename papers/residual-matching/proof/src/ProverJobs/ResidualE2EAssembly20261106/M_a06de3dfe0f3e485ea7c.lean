import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_4099765160_cf18766e : ∀ (m n : ℕ) (p : ℝ) (Om : Matrix (Fin m) (Fin n) ℝ)
    (Lambda theta : ℝ) (Tstar : Submodule ℝ (Matrix (Fin m) (Fin n) ℝ))
    (hLambda : 0 ≤ Lambda)
    (hMask : MaskEvent Lambda theta p Om Tstar),
    (∀ (k : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
        (X : Matrix (Fin m) (Fin n) ℝ),
      |innerTrace (A * Matrix.transpose B) X| ≤ frob A * frob B * spectralNorm X) ∧
    (∀ (k l : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ)
        (A : Matrix (Fin m) (Fin l) ℝ) (B : Matrix (Fin n) (Fin l) ℝ),
      |innerTrace (A * Matrix.transpose B) (TOm p Om (L * Matrix.transpose R))|
        ≤ Lambda * twoInfNorm L * twoInfNorm R * frob A * frob B) := by
  /- @proof-region region.target-node.session.5dab39d7859a086b begin -/
  intro m n p Om Lambda theta Tstar hLambda hMask
  have hP :
      ∀ (k : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
        (X : Matrix (Fin m) (Fin n) ℝ),
        |innerTrace (A * Matrix.transpose B) X| ≤ frob A * frob B * spectralNorm X := by
    intro k A B X
    set cA : Fin k → EuclideanSpace ℝ (Fin m) := fun t => WithLp.toLp 2 (fun i => A i t) with hcA
    set cB : Fin k → EuclideanSpace ℝ (Fin n) := fun t => WithLp.toLp 2 (fun j => B j t) with hcB
    have hident : innerTrace (A * Matrix.transpose B) X
        = ∑ t, inner ℝ (cA t) ((Matrix.toEuclideanLin X) (cB t)) := by
      have reindex : ∀ (g : Fin m → Fin n → Fin k → ℝ),
          ∑ i, ∑ j, ∑ t, g i j t = ∑ t, ∑ i, ∑ j, g i j t := by
        intro g
        calc ∑ i, ∑ j, ∑ t, g i j t
            = ∑ i, ∑ t, ∑ j, g i j t := by
              apply Finset.sum_congr rfl; intro i _
              exact Finset.sum_comm
          _ = ∑ t, ∑ i, ∑ j, g i j t := Finset.sum_comm
      have hcol : ∀ t : Fin k, inner ℝ (cA t) ((Matrix.toEuclideanLin X) (cB t))
          = ∑ i, ∑ j, A i t * X i j * B j t := by
        intro t
        rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply]
        rw [hcA, hcB]
        simp
        apply Finset.sum_congr rfl; intro i _
        change (∑ j, X i j * B j t) * A i t = ∑ j, A i t * X i j * B j t
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _
        ring
      rw [Finset.sum_congr rfl (fun t (_ : t ∈ (Finset.univ : Finset (Fin k))) => hcol t)]
      unfold innerTrace
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [reindex (fun i j t => (A i t * B j t) * X i j)]
      apply Finset.sum_congr rfl; intro t _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    have hbound : ∀ t, |inner ℝ (cA t) ((Matrix.toEuclideanLin X) (cB t))|
        ≤ ‖cA t‖ * (spectralNorm X * ‖cB t‖) := by
      intro t
      have h1 := abs_real_inner_le_norm (cA t) ((Matrix.toEuclideanLin X) (cB t))
      have h2 := Statlib.HighDim.MatrixAnalysis.opNorm_vec_le X (cB t)
      calc |inner ℝ (cA t) ((Matrix.toEuclideanLin X) (cB t))|
          ≤ ‖cA t‖ * ‖(Matrix.toEuclideanLin X) (cB t)‖ := h1
        _ ≤ ‖cA t‖ * (spectralNorm X * ‖cB t‖) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have hcolsA : frobSq A = ∑ t, ‖cA t‖ ^ 2 := by
      have h1 : ∀ t : Fin k, ‖cA t‖ ^ 2 = ∑ i, (A i t) ^ 2 := by
        intro t
        rw [hcA, EuclideanSpace.norm_sq_eq]
        apply Finset.sum_congr rfl; intro i _
        simp
      unfold frobSq
      simp only [h1]
      rw [Finset.sum_comm]
    have hcolsB : frobSq B = ∑ t, ‖cB t‖ ^ 2 := by
      have h1 : ∀ t : Fin k, ‖cB t‖ ^ 2 = ∑ j, (B j t) ^ 2 := by
        intro t
        rw [hcB, EuclideanSpace.norm_sq_eq]
        apply Finset.sum_congr rfl; intro j _
        simp
      unfold frobSq
      simp only [h1]
      rw [Finset.sum_comm]
    have hCS : ∑ t, ‖cA t‖ * ‖cB t‖ ≤ frob A * frob B := by
      have hfA : 0 ≤ frobSq A := by
        unfold frobSq
        exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (s := Finset.univ)
        (r := fun t => ‖cA t‖ * ‖cB t‖) (f := fun t => ‖cA t‖ ^ 2) (g := fun t => ‖cB t‖ ^ 2)
        (fun t _ => sq_nonneg _) (fun t _ => sq_nonneg _) (fun t _ => by ring)
      rw [← hcolsA, ← hcolsB] at hcs
      have hsnn : 0 ≤ ∑ t, ‖cA t‖ * ‖cB t‖ :=
        Finset.sum_nonneg (fun t _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      have hstep := Real.sqrt_le_sqrt hcs
      rw [Real.sqrt_sq hsnn] at hstep
      have hfm : Real.sqrt (frobSq A * frobSq B) = frob A * frob B := by
        rw [Real.sqrt_mul hfA]; rfl
      rw [hfm] at hstep
      exact hstep
    calc |innerTrace (A * Matrix.transpose B) X|
        = |∑ t, inner ℝ (cA t) ((Matrix.toEuclideanLin X) (cB t))| := by rw [hident]
      _ ≤ ∑ t, |inner ℝ (cA t) ((Matrix.toEuclideanLin X) (cB t))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, ‖cA t‖ * (spectralNorm X * ‖cB t‖) := Finset.sum_le_sum (fun t _ => hbound t)
      _ = spectralNorm X * ∑ t, ‖cA t‖ * ‖cB t‖ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun t _ => by ring)
      _ ≤ spectralNorm X * (frob A * frob B) :=
            mul_le_mul_of_nonneg_left hCS (Statlib.HighDim.MatrixAnalysis.opNorm_nonneg X)
      _ = frob A * frob B * spectralNorm X := by ring
  constructor
  · exact hP
  · intro k l L R A B
    have hSchur : spectralNorm (TOm p Om (L * Matrix.transpose R))
        ≤ Lambda * twoInfNorm L * twoInfNorm R := hMask.2.1 k L R
    have hb := hP l A B (TOm p Om (L * Matrix.transpose R))
    have hfA : 0 ≤ frob A := Real.sqrt_nonneg (frobSq A)
    have hfB : 0 ≤ frob B := Real.sqrt_nonneg (frobSq B)
    have hfAB : 0 ≤ frob A * frob B := mul_nonneg hfA hfB
    calc
      |innerTrace (A * Matrix.transpose B) (TOm p Om (L * Matrix.transpose R))|
          ≤ frob A * frob B * spectralNorm (TOm p Om (L * Matrix.transpose R)) := hb
      _ ≤ frob A * frob B * (Lambda * twoInfNorm L * twoInfNorm R) :=
            mul_le_mul_of_nonneg_left hSchur hfAB
      _ = Lambda * twoInfNorm L * twoInfNorm R * frob A * frob B := by ring
  /- @proof-region region.target-node.session.5dab39d7859a086b end -/

end

end Statlib.Imported

