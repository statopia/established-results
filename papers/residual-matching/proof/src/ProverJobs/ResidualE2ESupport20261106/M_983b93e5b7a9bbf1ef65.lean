import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1606911688_c7dc5675 : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (m + n))
        ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
          (A.map Complex.ofReal)
          (Matrix.transpose (A.map Complex.ofReal))
          (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm :
          Matrix (Fin (m + n)) (Fin (m + n)) ℂ))‖
      = Statlib.HighDim.MatrixAnalysis.opNorm A := by
  /- @proof-region region.target-node.session.8d8feee180444d1c begin -/
  intro m n A
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_def]
  set M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (A.map Complex.ofReal)
      (Matrix.transpose (A.map Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ) with hM
  set D : Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm with hD
  set TD : EuclideanSpace ℂ (Fin (m + n)) →L[ℂ] EuclideanSpace ℂ (Fin (m + n)) :=
    (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) D with hTD
  have hAl : Statlib.HighDim.MatrixAnalysis.opNorm A =
      ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖ := by
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    exact Matrix.l2_opNorm_def A
  have hop0 : 0 ≤ Statlib.HighDim.MatrixAnalysis.opNorm A := by
    rw [hAl]
    exact norm_nonneg _
  have hcz : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_norm_sq]
    show z.re * z.re + z.im * z.im = z.re ^ 2 + z.im ^ 2
    ring
  have hbr : ∀ (a b : ℕ) (E : Matrix (Fin a) (Fin b) ℝ) (u : Fin b → ℂ),
      ∑ i : Fin a, ‖((E.map Complex.ofReal).mulVec u) i‖ ^ 2 ≤
        (Statlib.HighDim.MatrixAnalysis.opNorm E) ^ 2 * ∑ j : Fin b, ‖u j‖ ^ 2 := by
    intro a b E u
    have hz1 : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by
      intro x y
      simp
    have hz2 : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by
      intro x y
      simp
    have hcrs : ∀ r s : ℝ, ‖(r : ℂ) + (s : ℂ) * Complex.I‖ ^ 2 = r ^ 2 + s ^ 2 := by
      intro r s
      rw [hcz, hz1, hz2]
    have hcoord : (E.map Complex.ofReal).mulVec u
        = fun i => ((E.mulVec (fun j => (u j).re)) i : ℂ)
            + ((E.mulVec (fun j => (u j).im)) i : ℂ) * Complex.I := by
      funext i
      show (∑ j : Fin b, (E i j : ℂ) * u j)
        = ((∑ j : Fin b, E i j * (u j).re : ℝ) : ℂ)
            + ((∑ j : Fin b, E i j * (u j).im : ℝ) : ℂ) * Complex.I
      have hterm : ∀ j : Fin b, (E i j : ℂ) * u j
          = ((E i j * (u j).re : ℝ) : ℂ) + ((E i j * (u j).im : ℝ) : ℂ) * Complex.I := by
        intro j
        conv_lhs => rw [← Complex.re_add_im (u j)]
        push_cast
        ring
      calc ∑ j : Fin b, (E i j : ℂ) * u j
          = ∑ j : Fin b,
              (((E i j * (u j).re : ℝ) : ℂ) + ((E i j * (u j).im : ℝ) : ℂ) * Complex.I) :=
            Finset.sum_congr rfl (fun j _ => hterm j)
        _ = (∑ j : Fin b, ((E i j * (u j).re : ℝ) : ℂ))
              + (∑ j : Fin b, ((E i j * (u j).im : ℝ) : ℂ)) * Complex.I := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
        _ = ((∑ j : Fin b, E i j * (u j).re : ℝ) : ℂ)
              + ((∑ j : Fin b, E i j * (u j).im : ℝ) : ℂ) * Complex.I := by
            have hcol : ∀ (f : Fin b → ℝ), (∑ j : Fin b, ((f j : ℝ) : ℂ))
                = ((∑ j : Fin b, f j : ℝ) : ℂ) := by
              intro f
              have hcoe : ∀ x : ℝ, (↑x : ℂ) = Complex.ofRealHom x := fun x => rfl
              simp only [hcoe]
              rw [← map_sum Complex.ofRealHom]
            rw [hcol (fun j => E i j * (u j).re)]
            rw [hcol (fun j => E i j * (u j).im)]
    have hnorm : ∀ i : Fin a, ‖((E.map Complex.ofReal).mulVec u) i‖ ^ 2
        = ((E.mulVec (fun j => (u j).re)) i) ^ 2 + ((E.mulVec (fun j => (u j).im)) i) ^ 2 := by
      intro i
      rw [hcoord]
      exact hcrs _ _
    have hkey : ∀ (p : Fin b → ℝ),
        ∑ i : Fin a, ((E.mulVec p) i) ^ 2
          ≤ (Statlib.HighDim.MatrixAnalysis.opNorm E) ^ 2 * ∑ j : Fin b, (p j) ^ 2 := by
      intro p
      have h1 : ∑ i : Fin a, ((E.mulVec p) i) ^ 2
          = ‖(Matrix.toEuclideanLin E) (WithLp.toLp 2 p)‖ ^ 2 := by
        rw [Matrix.toEuclideanLin_apply_piLp_toLp, EuclideanSpace.norm_sq_eq]
        refine Finset.sum_congr rfl ?_
        intro i _
        show ((E.mulVec p) i) ^ 2 = ‖(E.mulVec p) i‖ ^ 2
        simp
      have h3 : ‖(Matrix.toEuclideanLin E) (WithLp.toLp 2 p)‖ ^ 2
          ≤ (Statlib.HighDim.MatrixAnalysis.opNorm E) ^ 2 *
            ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin b))‖ ^ 2 := by
        have h2 := Statlib.HighDim.MatrixAnalysis.opNorm_vec_le E (WithLp.toLp 2 p)
        have h4 := mul_le_mul h2 h2
          (norm_nonneg ((Matrix.toEuclideanLin E) (WithLp.toLp 2 p)))
          (mul_nonneg (Statlib.HighDim.MatrixAnalysis.opNorm_nonneg E) (norm_nonneg _))
        calc ‖(Matrix.toEuclideanLin E) (WithLp.toLp 2 p)‖ ^ 2
            = ‖(Matrix.toEuclideanLin E) (WithLp.toLp 2 p)‖ *
                ‖(Matrix.toEuclideanLin E) (WithLp.toLp 2 p)‖ := by ring
          _ ≤ (Statlib.HighDim.MatrixAnalysis.opNorm E *
                ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin b))‖) *
                (Statlib.HighDim.MatrixAnalysis.opNorm E *
                ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin b))‖) := h4
          _ = (Statlib.HighDim.MatrixAnalysis.opNorm E) ^ 2 *
                ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin b))‖ ^ 2 := by ring
      have h5 : ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin b))‖ ^ 2
          = ∑ j : Fin b, (p j) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        refine Finset.sum_congr rfl ?_
        intro j _
        simp
      rw [h1]
      refine le_trans h3 ?_
      rw [h5]
    have hs : ∑ i : Fin a, ‖((E.map Complex.ofReal).mulVec u) i‖ ^ 2
        = ∑ i : Fin a,
            (((E.mulVec (fun j => (u j).re)) i) ^ 2 + ((E.mulVec (fun j => (u j).im)) i) ^ 2) :=
      Finset.sum_congr rfl (fun i _ => hnorm i)
    rw [hs, Finset.sum_add_distrib]
    refine le_trans (add_le_add (hkey (fun j => (u j).re)) (hkey (fun j => (u j).im))) ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    have hfin : ∑ j : Fin b, ((u j).re ^ 2 + (u j).im ^ 2) = ∑ j : Fin b, ‖u j‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact (hcz (u j)).symm
    rw [hfin]
  have hmv : ∀ (y : Fin (m + n) → ℂ) (k : Fin m ⊕ Fin n),
      (D.mulVec y) (finSumFinEquiv k) = (M.mulVec (y ∘ ⇑finSumFinEquiv)) k := by
    intro y k
    have hleft : (D.mulVec y) (finSumFinEquiv k)
        = ∑ j : Fin (m + n), M k (⇑finSumFinEquiv.symm j) * y j := by
      show (∑ j : Fin (m + n), D (finSumFinEquiv k) j * y j)
        = ∑ j : Fin (m + n), M k (⇑finSumFinEquiv.symm j) * y j
      refine Finset.sum_congr rfl ?_
      intro j _
      show M (⇑finSumFinEquiv.symm (finSumFinEquiv k)) (⇑finSumFinEquiv.symm j) * y j
        = M k (⇑finSumFinEquiv.symm j) * y j
      rw [Equiv.symm_apply_apply]
    have hright : (M.mulVec (y ∘ ⇑finSumFinEquiv)) k
        = ∑ j : Fin m ⊕ Fin n, M k j * (y ∘ ⇑finSumFinEquiv) j := rfl
    rw [hleft, hright]
    rw [← Equiv.sum_comp finSumFinEquiv
      (fun j : Fin (m + n) => M k (⇑finSumFinEquiv.symm j) * y j)]
    simp only [Equiv.symm_apply_apply, Function.comp_apply]
  have hsplit : ∀ (z : Fin m ⊕ Fin n → ℂ),
      ∑ k : Fin m ⊕ Fin n, ‖(M.mulVec z) k‖ ^ 2
        = ∑ i : Fin m, ‖((A.map Complex.ofReal).mulVec (z ∘ Sum.inr)) i‖ ^ 2
          + ∑ j : Fin n,
              ‖((Matrix.transpose (A.map Complex.ofReal)).mulVec (z ∘ Sum.inl)) j‖ ^ 2 := by
    intro z
    have h1 : M.mulVec z
        = Sum.elim ((A.map Complex.ofReal).mulVec (z ∘ Sum.inr))
            ((Matrix.transpose (A.map Complex.ofReal)).mulVec (z ∘ Sum.inl)) := by
      rw [hM, Matrix.fromBlocks_mulVec]
      simp
    rw [h1, Fintype.sum_sum_type]
    simp
  have hnormx : ∀ (x : EuclideanSpace ℂ (Fin (m + n))),
      ‖x‖ ^ 2 = ∑ k : Fin m ⊕ Fin n, ‖(x.ofLp ∘ ⇑finSumFinEquiv) k‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    exact (Equiv.sum_comp finSumFinEquiv (fun i => ‖x.ofLp i‖ ^ 2)).symm
  have hTc : ∀ (w : Fin (m + n) → ℂ),
      (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) D (WithLp.toLp 2 w)
        = WithLp.toLp 2 (D.mulVec w) := fun w =>
    Matrix.toEuclideanLin_apply_piLp_toLp D w
  have hnormLpC : ∀ (k : ℕ) (f : Fin k → ℂ),
      ‖(WithLp.toLp 2 f : EuclideanSpace ℂ (Fin k))‖ ^ 2 = ∑ i : Fin k, ‖f i‖ ^ 2 := by
    intro k f
    rw [EuclideanSpace.norm_sq_eq]
  have hnormLpR : ∀ (k : ℕ) (f : Fin k → ℝ),
      ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin k))‖ ^ 2 = ∑ i : Fin k, ‖f i‖ ^ 2 := by
    intro k f
    rw [EuclideanSpace.norm_sq_eq]
  have hcolG : ∀ {k : ℕ} (f : Fin k → ℝ),
      (∑ j : Fin k, ((f j : ℝ) : ℂ)) = ((∑ j : Fin k, f j : ℝ) : ℂ) := by
    intro k f
    have hcoe : ∀ x : ℝ, (↑x : ℂ) = Complex.ofRealHom x := fun x => rfl
    simp only [hcoe]
    rw [← map_sum Complex.ofRealHom]
  have hcv : ∀ r : ℝ, ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    intro r
    rw [hcz]
    simp
  have hcast : ∀ (a b : ℕ) (E : Matrix (Fin a) (Fin b) ℝ) (p : Fin b → ℝ),
      (E.map Complex.ofReal).mulVec (fun j => ((p j : ℝ) : ℂ))
        = fun i => ((E.mulVec p) i : ℂ) := by
    intro a b E p
    funext i
    show (∑ j : Fin b, (E i j : ℂ) * ((p j : ℝ) : ℂ))
      = ((∑ j : Fin b, E i j * p j : ℝ) : ℂ)
    have hstep : ∀ j : Fin b,
        (E i j : ℂ) * ((p j : ℝ) : ℂ) = ((E i j * p j : ℝ) : ℂ) := by
      intro j
      rw [← Complex.ofReal_mul]
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    exact hcolG (fun j => E i j * p j)
  have hzero : ∀ (k l : ℕ) (C : Matrix (Fin k) (Fin l) ℂ),
      C.mulVec (0 : Fin l → ℂ) = 0 := by
    intro k l C
    funext i
    show (∑ j : Fin l, C i j * 0) = 0
    simp
  have hupper : ‖TD‖ ≤ Statlib.HighDim.MatrixAnalysis.opNorm A := by
    refine ContinuousLinearMap.opNorm_le_bound _ hop0 (fun x => ?_)
    have hval : TD x = WithLp.toLp 2 (D.mulVec x.ofLp) := by
      conv_lhs => rw [← WithLp.toLp_ofLp 2 x]
      exact hTc x.ofLp
    have hsq : ‖TD x‖ ^ 2 ≤ (Statlib.HighDim.MatrixAnalysis.opNorm A) ^ 2 * ‖x‖ ^ 2 := by
      rw [hval, hnormLpC]
      have h1 : ∑ i : Fin (m + n), ‖(D.mulVec x.ofLp) i‖ ^ 2
          = ∑ k : Fin m ⊕ Fin n, ‖(M.mulVec (x.ofLp ∘ ⇑finSumFinEquiv)) k‖ ^ 2 := by
        rw [← Equiv.sum_comp finSumFinEquiv
          (fun i : Fin (m + n) => ‖(D.mulVec x.ofLp) i‖ ^ 2)]
        exact Finset.sum_congr rfl (fun k _ => by rw [hmv x.ofLp k])
      rw [h1, hsplit (x.ofLp ∘ ⇑finSumFinEquiv), hnormx x, Fintype.sum_sum_type]
      have hb1 := hbr m n A ((x.ofLp ∘ ⇑finSumFinEquiv) ∘ Sum.inr)
      have hb2 := hbr n m (Matrix.transpose A) ((x.ofLp ∘ ⇑finSumFinEquiv) ∘ Sum.inl)
      rw [Statlib.HighDim.MatrixAnalysis.opNorm_transpose A] at hb2
      refine le_trans (add_le_add hb1 hb2) ?_
      simp only [Function.comp_apply]
      exact le_of_eq (by ring)
    have h0 : (0:ℝ) ≤ ‖TD x‖ := norm_nonneg _
    have hs : (0:ℝ) ≤ Statlib.HighDim.MatrixAnalysis.opNorm A * ‖x‖ :=
      mul_nonneg hop0 (norm_nonneg x)
    have hsq2 : ‖TD x‖ ^ 2
        ≤ (Statlib.HighDim.MatrixAnalysis.opNorm A * ‖x‖) ^ 2 := by
      rw [mul_pow]
      exact hsq
    have h := Real.sqrt_le_sqrt hsq2
    rw [Real.sqrt_sq h0, Real.sqrt_sq hs] at h
    exact h
  have hlower : Statlib.HighDim.MatrixAnalysis.opNorm A ≤ ‖TD‖ := by
    rw [hAl]
    set TA : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
      (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A with hTA
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
    let wv : Fin m ⊕ Fin n → ℂ :=
      Sum.elim (fun _ => 0) (fun j => ((v.ofLp j : ℝ) : ℂ))
    let xw : Fin (m + n) → ℂ := fun t => wv (⇑finSumFinEquiv.symm t)
    let xvec : EuclideanSpace ℂ (Fin (m + n)) := WithLp.toLp 2 xw
    have hxvec : xvec = WithLp.toLp 2 xw := rfl
    have hxc : xw ∘ ⇑finSumFinEquiv = wv := by
      funext k
      show wv (⇑finSumFinEquiv.symm (finSumFinEquiv k)) = wv k
      rw [Equiv.symm_apply_apply]
    have hvalv : TA v = WithLp.toLp 2 (A.mulVec v.ofLp) := by
      conv_lhs => rw [← WithLp.toLp_ofLp 2 v]
      exact Matrix.toEuclideanLin_apply_piLp_toLp A v.ofLp
    have hnv : ‖xvec‖ ^ 2 = ‖v‖ ^ 2 := by
      have e1 : ‖xvec‖ ^ 2 = ∑ k : Fin m ⊕ Fin n, ‖wv k‖ ^ 2 := by
        rw [hxvec, hnormLpC, ← Equiv.sum_comp finSumFinEquiv
          (fun i : Fin (m + n) => ‖xw i‖ ^ 2)]
        exact Finset.sum_congr rfl (fun k _ => by rw [← hxc, Function.comp_apply])
      have e2 : ∑ k : Fin m ⊕ Fin n, ‖wv k‖ ^ 2 = ‖v‖ ^ 2 := by
        have h0 : (∑ i : Fin m, ‖wv (Sum.inl i)‖ ^ 2) = 0 := by
          refine Finset.sum_eq_zero (fun i _ => ?_)
          show ‖(0 : ℂ)‖ ^ 2 = 0
          simp
        have h1 : (∑ j : Fin n, ‖wv (Sum.inr j)‖ ^ 2)
            = ∑ j : Fin n, ‖v.ofLp j‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          show ‖((v.ofLp j : ℝ) : ℂ)‖ ^ 2 = ‖v.ofLp j‖ ^ 2
          rw [hcv]
          simp
        rw [Fintype.sum_sum_type, h0, h1, zero_add, ← hnormLpR, WithLp.toLp_ofLp]
      rw [e1, e2]
    have hTv : ‖TD xvec‖ ^ 2 = ‖TA v‖ ^ 2 := by
      have f1 : ‖TD xvec‖ ^ 2 = ∑ i : Fin (m + n), ‖(D.mulVec xw) i‖ ^ 2 := by
        rw [hxvec, hTc xw, hnormLpC]
      have f2 : ∑ i : Fin (m + n), ‖(D.mulVec xw) i‖ ^ 2
          = ∑ k : Fin m ⊕ Fin n, ‖(M.mulVec wv) k‖ ^ 2 := by
        rw [← Equiv.sum_comp finSumFinEquiv
          (fun i : Fin (m + n) => ‖(D.mulVec xw) i‖ ^ 2)]
        exact Finset.sum_congr rfl (fun k _ => by rw [hmv xw k, hxc])
      have f3 : ∑ k : Fin m ⊕ Fin n, ‖(M.mulVec wv) k‖ ^ 2
          = ∑ i : Fin m, ‖(A.mulVec v.ofLp) i‖ ^ 2 := by
        rw [hsplit wv]
        have h0 : (∑ j : Fin n,
            ‖((Matrix.transpose (A.map Complex.ofReal)).mulVec (wv ∘ Sum.inl)) j‖ ^ 2) = 0 := by
          have hz : (wv ∘ Sum.inl) = (0 : Fin m → ℂ) := rfl
          rw [hz, hzero n m (Matrix.transpose (A.map Complex.ofReal))]
          simp
        have h1 : (∑ i : Fin m,
            ‖((A.map Complex.ofReal).mulVec (wv ∘ Sum.inr)) i‖ ^ 2)
            = ∑ i : Fin m, ‖(A.mulVec v.ofLp) i‖ ^ 2 := by
          have hinr : (wv ∘ Sum.inr) = (fun j => ((v.ofLp j : ℝ) : ℂ)) := rfl
          rw [hinr, hcast m n A v.ofLp]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          show ‖((A.mulVec v.ofLp) i : ℂ)‖ ^ 2 = ‖(A.mulVec v.ofLp) i‖ ^ 2
          rw [hcv]
          simp
        rw [h1, h0, add_zero]
      have f4 : ‖TA v‖ ^ 2 = ∑ i : Fin m, ‖(A.mulVec v.ofLp) i‖ ^ 2 := by
        rw [hvalv, hnormLpR]
      rw [f1, f2, f3, f4]
    have hTvn : ‖TD xvec‖ = ‖TA v‖ := by
      have := congrArg Real.sqrt hTv
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
    have hnvn : ‖xvec‖ = ‖v‖ := by
      have := congrArg Real.sqrt hnv
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
    calc ‖TA v‖ = ‖TD xvec‖ := hTvn.symm
      _ ≤ ‖TD‖ * ‖xvec‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖TD‖ * ‖v‖ := by rw [hnvn]
  exact le_antisymm hupper hlower
  /- @proof-region region.target-node.session.8d8feee180444d1c end -/

end Statlib.Imported

