import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SoftThresholdDenoisingHelpers
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
theorem statopia_math_node_919610516_79178f41 : ∀ {m n r : ℕ} (hr : 0 < r) (hrn : r ≤ n)
    (hnm : n ≤ m) (M0 : Matrix (Fin m) (Fin n) ℝ) (U0 : Matrix (Fin m) (Fin r) ℝ)
    (V0 : Matrix (Fin n) (Fin r) ℝ) (d0 : Fin r → ℝ)
    (hM0 : M0 = U0 * Matrix.diagonal d0 * Matrix.transpose V0)
    (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
    (hd0 : ∀ i : Fin r, 0 < d0 i) (h : r - 1 < min m n),
    Statlib.HighDim.MatrixAnalysis.singularValues M0 ⟨r - 1, h⟩ ≤ ⨅ i : Fin r, d0 i := by
  /- @proof-region region.target-node.session.27c56dd5dab2c391 begin -/
  classical
  intro m n r hr hrn hnm M0 U0 V0 d0 hM0 hU0 hV0 hd0 h
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  refine le_ciInf (f := fun i : Fin r => d0 i) ?_
  intro j
  set d' : Fin r → ℝ := fun i => if i = j then 0 else d0 i with hd'def
  set B : Matrix (Fin m) (Fin n) ℝ := U0 * Matrix.diagonal d' * Matrix.transpose V0 with hBdef
  set E : Matrix (Fin m) (Fin n) ℝ :=
    d0 j • Matrix.vecMulVec (fun i => U0 i j) (fun l => V0 l j) with hEdef
  have hBrank : B.rank ≤ r - 1 := by
    have hdr : (Matrix.diagonal d').rank = Fintype.card {i : Fin r // d' i ≠ 0} :=
      Matrix.rank_diagonal d'
    have hlt : Fintype.card {i : Fin r // d' i ≠ 0} < r := by
      have hcard :=
        Fintype.card_subtype_lt (p := fun i : Fin r => d' i ≠ 0) (x := j) (by simp [hd'def])
      simpa [Fintype.card_fin] using hcard
    have h1 : B.rank ≤ (Matrix.diagonal d').rank := by
      rw [hBdef]
      calc (U0 * Matrix.diagonal d' * Matrix.transpose V0).rank
          ≤ (U0 * Matrix.diagonal d').rank := Matrix.rank_mul_le_left _ _
        _ ≤ (Matrix.diagonal d').rank := Matrix.rank_mul_le_right _ _
    omega
  have hEop : Statlib.HighDim.MatrixAnalysis.opNorm E ≤ d0 j := by
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2, Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (le_of_lt (hd0 j)) ?_
    intro x hx
    change ‖(Matrix.toEuclideanLin E) x‖ ≤ d0 j
    set c : ℝ := ∑ l : Fin n, V0 l j * x.ofLp l with hcdef
    have hU : ∑ i : Fin m, U0 i j * U0 i j = 1 := by
      have h := congrFun (congrFun hU0 j) j
      simpa [Matrix.mul_apply] using h
    have hV : ∑ l : Fin n, V0 l j * V0 l j = 1 := by
      have h := congrFun (congrFun hV0 j) j
      simpa [Matrix.mul_apply] using h
    have hxn : ∑ l : Fin n, (x.ofLp l) ^ 2 = 1 := by
      have h := (Statlib.HighDim.MatrixAnalysis.col_norm_sq x).symm
      rw [hx] at h
      simpa using h
    have hc1 : c ≤ 1 := by
      have key : 2 * c ≤ 2 := by
        calc 2 * c = ∑ l : Fin n, 2 * (V0 l j * x.ofLp l) := by
              rw [hcdef, Finset.mul_sum]
          _ ≤ ∑ l : Fin n, ((V0 l j) ^ 2 + (x.ofLp l) ^ 2) :=
              Finset.sum_le_sum (fun l _ => by nlinarith [sq_nonneg (V0 l j - x.ofLp l)])
          _ = 2 := by
              rw [Finset.sum_add_distrib]
              have hV' : ∑ l : Fin n, (V0 l j) ^ 2 = 1 := by
                rw [← hV]; exact Finset.sum_congr rfl (fun l _ => by ring)
              rw [hV', hxn]
              norm_num
      linarith
    have hc2 : -c ≤ 1 := by
      have key : -2 * c ≤ 2 := by
        calc -2 * c = ∑ l : Fin n, (-2) * (V0 l j * x.ofLp l) := by
              rw [hcdef, Finset.mul_sum]
          _ ≤ ∑ l : Fin n, ((V0 l j) ^ 2 + (x.ofLp l) ^ 2) :=
              Finset.sum_le_sum (fun l _ => by nlinarith [sq_nonneg (V0 l j + x.ofLp l)])
          _ = 2 := by
              rw [Finset.sum_add_distrib]
              have hV' : ∑ l : Fin n, (V0 l j) ^ 2 = 1 := by
                rw [← hV]; exact Finset.sum_congr rfl (fun l _ => by ring)
              rw [hV', hxn]
              norm_num
      linarith
    have hcsq : c ^ 2 ≤ 1 := by nlinarith [hc1, hc2]
    have hterm : ∀ i : Fin m, ((Matrix.toEuclideanLin E) x).ofLp i = d0 j * (U0 i j * c) := by
      intro i
      rw [Matrix.ofLp_toEuclideanLin_apply, hEdef, hcdef]
      simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    have hcalc : ‖(Matrix.toEuclideanLin E) x‖ ^ 2 ≤ (d0 j) ^ 2 := by
      rw [Statlib.HighDim.MatrixAnalysis.col_norm_sq]
      calc ∑ i : Fin m, ((Matrix.toEuclideanLin E) x).ofLp i ^ 2
          = ∑ i : Fin m, (d0 j * (U0 i j * c)) ^ 2 :=
            Finset.sum_congr rfl (fun i _ => by rw [hterm i])
        _ = (d0 j) ^ 2 * c ^ 2 * ∑ i : Fin m, U0 i j * U0 i j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
        _ = (d0 j) ^ 2 * c ^ 2 := by rw [hU]; ring
        _ ≤ (d0 j) ^ 2 * 1 := by nlinarith [hcsq, sq_nonneg (d0 j)]
        _ = (d0 j) ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hcalc
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (le_of_lt (hd0 j))] at hsqrt
  have hrow : ∀ (e : Fin r → ℝ) (i : Fin m) (l : Fin n),
      (U0 * Matrix.diagonal e * Matrix.transpose V0) i l = ∑ x : Fin r, U0 i x * e x * V0 l x := by
    intro e i l
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.mul_diagonal e U0 i x, Matrix.transpose_apply]
  have hdecomp : M0 = B + E := by
    rw [hM0, hBdef, hEdef]
    ext i l
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hrow d0 i l, hrow d' i l,
      Matrix.vecMulVec_apply]
    have hsum : ∑ x : Fin r, U0 i x * d' x * V0 l x
        = ∑ x : Fin r,
            (U0 i x * d0 x * V0 l x - (if x = j then U0 i j * d0 j * V0 l j else 0)) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : x = j
      · subst hx
        simp [hd'def]
      · simp [hd'def, hx]
    rw [hsum, Finset.sum_sub_distrib]
    have h2 : ∑ x : Fin r, (if x = j then U0 i j * d0 j * V0 l j else 0)
        = U0 i j * d0 j * V0 l j := by
      simp
    rw [h2]
    ring
  have h0 := Statlib.HighDim.MatrixAnalysis.singularValues_tail_le_of_rank_add_opNorm_le
    (A := B) (E := E) (r := r - 1) (k := r - 1) (lam := d0 j) hBrank hEop le_rfl h
  simpa [hdecomp] using h0
  /- @proof-region region.target-node.session.27c56dd5dab2c391 end -/

end Statlib.Imported

