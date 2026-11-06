import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false in
theorem statopia_math_node_3881171327_07a9338e : ∀ (m n kk : ℕ) (Uk : Matrix (Fin m) (Fin kk) ℝ) (Vk : Matrix (Fin n) (Fin kk) ℝ)
    (dk : Fin kk → ℝ)
    (hU : Matrix.transpose Uk * Uk = 1)
    (hV : Matrix.transpose Vk * Vk = 1)
    (hdkpos : ∀ j : Fin kk, 0 < dk j)
    (hmin : 0 < min m n),
    ∀ j : Fin kk, dk j ≤ spectralNorm (Uk * Matrix.diagonal dk * Matrix.transpose Vk) := by
  /- @proof-region region.target-node.session.785fa9f27268244c begin -/
  intro m n kk Uk Vk dk hU hV hdkpos hmin j
  classical
  have hn : 0 < n := lt_of_lt_of_le hmin (Nat.min_le_right m n)
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hspec := (Statlib.HighDim.MatrixAnalysis.singular_value_properties
    (Uk * Matrix.diagonal dk * Matrix.transpose Vk) (Or.inr hne)).1 hmin
  rw [spectralNorm, dif_pos hmin, hspec]
  have hmv : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (y : Fin q → ℝ) (i : Fin p),
      M.mulVec y i = ∑ a, M i a * y a := by
    intro p q M y i
    simp only [Matrix.mulVec]
    rfl
  have hsumj : ∀ l : Fin kk, ∑ a : Fin n, Vk a l * Vk a j = if l = j then (1 : ℝ) else 0 := by
    intro l
    have h := congrFun (congrFun hV l) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Matrix.transpose_apply] using h
  have hsumU : ∑ i : Fin m, Uk i j * Uk i j = 1 := by
    have h := congrFun (congrFun hU j) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Matrix.transpose_apply] using h
  have hcol : (Matrix.transpose Vk).mulVec (fun a : Fin n => Vk a j)
      = fun l : Fin kk => if l = j then (1 : ℝ) else 0 := by
    funext l
    simp only [hmv, Matrix.transpose_apply]
    exact hsumj l
  have hdiag : (Matrix.diagonal dk).mulVec (fun l : Fin kk => if l = j then (1 : ℝ) else 0)
      = fun l : Fin kk => if l = j then dk j else 0 := by
    funext b
    simp only [hmv]
    rw [Finset.sum_eq_single b]
    · by_cases h : b = j <;> simp [h]
    · intro c _ hc
      have hbc : ¬ (b = c) := fun hbc' => hc hbc'.symm
      simp [Matrix.diagonal_apply, hbc]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  have hUcol : Uk.mulVec (fun l : Fin kk => if l = j then dk j else 0)
      = fun i : Fin m => Uk i j * dk j := by
    funext i
    simp only [hmv]
    rw [Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      simp [hc]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hmulVec_mul : ∀ {p q r : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (B : Matrix (Fin q) (Fin r) ℝ)
      (y : Fin r → ℝ), (A * B).mulVec y = A.mulVec (B.mulVec y) := by
    intro p q r A B y
    funext i
    simp only [hmv, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => by ring))
  have hmul : (Uk * Matrix.diagonal dk * Matrix.transpose Vk).mulVec (fun a : Fin n => Vk a j)
      = fun i : Fin m => Uk i j * dk j := by
    simp only [hmulVec_mul, hcol, hdiag, hUcol]
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun a : Fin n => Vk a j)
  have hv2 : ‖v‖ ^ 2 = 1 := by
    have hsumJ : ∑ i : Fin n, Vk i j * Vk i j = 1 := by
      have h := hsumj j
      simpa using h
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin n, ‖v.ofLp i‖ ^ 2 = ∑ i : Fin n, Vk i j * Vk i j := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hvof : v.ofLp i = Vk i j := rfl
          rw [hvof, Real.norm_eq_abs, sq_abs]
          ring
      _ = 1 := hsumJ
  have hv : ‖v‖ = 1 := by
    have h0 : 0 ≤ ‖v‖ := norm_nonneg v
    have hfac : (‖v‖ - 1) * (‖v‖ + 1) = 0 := by nlinarith [hv2]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · linarith
    · linarith
  let w : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i : Fin m => Uk i j * dk j)
  have hw2 : ‖w‖ ^ 2 = dk j ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin m, ‖w.ofLp i‖ ^ 2 = ∑ i : Fin m, (Uk i j * dk j) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hwof : w.ofLp i = Uk i j * dk j := rfl
          rw [hwof, Real.norm_eq_abs, sq_abs]
      _ = dk j ^ 2 := by
          have hterm : ∀ i : Fin m, (Uk i j * dk j) ^ 2 = (Uk i j * Uk i j) * dk j ^ 2 := by
            intro i
            ring
          rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_mul, hsumU, one_mul]
  have hw : ‖w‖ = dk j := by
    have h0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hpos : 0 < dk j := hdkpos j
    have hfac : (‖w‖ - dk j) * (‖w‖ + dk j) = 0 := by nlinarith [hw2]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · linarith
    · linarith
  have hWv : (Matrix.toEuclideanLin (Uk * Matrix.diagonal dk * Matrix.transpose Vk)) v = w := by
    rw [Matrix.toEuclideanLin_apply]
    show WithLp.toLp 2 ((Uk * Matrix.diagonal dk * Matrix.transpose Vk).mulVec (fun a : Fin n => Vk a j))
      = WithLp.toLp 2 (fun i : Fin m => Uk i j * dk j)
    rw [hmul]
  have hnorm : ‖(Matrix.toEuclideanLin (Uk * Matrix.diagonal dk * Matrix.transpose Vk)) v‖ = dk j := by
    rw [hWv, hw]
  have hop := Statlib.HighDim.MatrixAnalysis.opNorm_vec_le
    (Uk * Matrix.diagonal dk * Matrix.transpose Vk) v
  rw [hnorm, hv, mul_one, Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2] at hop
  exact hop
  /- @proof-region region.target-node.session.785fa9f27268244c end -/

end Statlib.Imported

