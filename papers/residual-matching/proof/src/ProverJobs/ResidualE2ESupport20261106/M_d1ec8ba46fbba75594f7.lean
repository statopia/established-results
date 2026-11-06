import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3715382306_6ae91894 : ∀ (m n : ℕ) (p : ℝ) (hp : 0 < p) (Om : Fin m → Fin n → ℝ)
    (Lam : ℝ) (hLam : 0 ≤ Lam) (hWnorm : specNorm (Wmask p Om) ≤ Lam)
    (k l : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (C : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
    |frobInner (Tmask p Om (A * B.transpose)) (C * D.transpose)|
      ≤ Lam * bFactor A C * bFactor B D := by
  /- @proof-region region.target-node.session.3ed39f0712b56b93 begin -/
  intro m n p hp Om Lam hLam hW k l A B C D
  classical
  have hexp : frobInner (Tmask p Om (A * B.transpose)) (C * D.transpose)
      = ∑ st : Fin k × Fin l, ∑ i : Fin m, ∑ j : Fin n,
          (A i st.1 * C i st.2) * Wmask p Om i j * (B j st.1 * D j st.2) := by
    have e1 : frobInner (Tmask p Om (A * B.transpose)) (C * D.transpose)
        = ∑ i : Fin m, ∑ j : Fin n,
            Wmask p Om i j * (∑ s : Fin k, A i s * B j s) * (∑ t : Fin l, C i t * D j t) := by
      simp only [frobInner, Tmask, Matrix.mul_apply, Matrix.transpose_apply]
    have e2 : (∑ i : Fin m, ∑ j : Fin n,
            Wmask p Om i j * (∑ s : Fin k, A i s * B j s) * (∑ t : Fin l, C i t * D j t))
        = ∑ i : Fin m, ∑ j : Fin n, ∑ s : Fin k, ∑ t : Fin l,
            Wmask p Om i j * (A i s * B j s) * (C i t * D j t) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have h1 : Wmask p Om i j * (∑ s : Fin k, A i s * B j s)
          = ∑ s : Fin k, Wmask p Om i j * (A i s * B j s) := by
        rw [Finset.mul_sum]
      have h2 : ∀ s : Fin k,
          Wmask p Om i j * (A i s * B j s) * (∑ t : Fin l, C i t * D j t)
            = ∑ t : Fin l, Wmask p Om i j * (A i s * B j s) * (C i t * D j t) := by
        intro s
        rw [Finset.mul_sum]
      calc Wmask p Om i j * (∑ s : Fin k, A i s * B j s) * (∑ t : Fin l, C i t * D j t)
          = (∑ s : Fin k, Wmask p Om i j * (A i s * B j s))
              * (∑ t : Fin l, C i t * D j t) := by rw [h1]
        _ = ∑ s : Fin k,
              Wmask p Om i j * (A i s * B j s) * (∑ t : Fin l, C i t * D j t) := by
              rw [Finset.sum_mul]
        _ = ∑ s : Fin k, ∑ t : Fin l,
              Wmask p Om i j * (A i s * B j s) * (C i t * D j t) :=
              Finset.sum_congr rfl (fun s _ => h2 s)
    have e3 : (∑ i : Fin m, ∑ j : Fin n, ∑ s : Fin k, ∑ t : Fin l,
            Wmask p Om i j * (A i s * B j s) * (C i t * D j t))
        = ∑ s : Fin k, ∑ t : Fin l, ∑ i : Fin m, ∑ j : Fin n,
            Wmask p Om i j * (A i s * B j s) * (C i t * D j t) := by
      calc ∑ i : Fin m, ∑ j : Fin n, ∑ s : Fin k, ∑ t : Fin l,
              Wmask p Om i j * (A i s * B j s) * (C i t * D j t)
          = ∑ i : Fin m, ∑ s : Fin k, ∑ j : Fin n, ∑ t : Fin l,
              Wmask p Om i j * (A i s * B j s) * (C i t * D j t) :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
        _ = ∑ s : Fin k, ∑ i : Fin m, ∑ j : Fin n, ∑ t : Fin l,
              Wmask p Om i j * (A i s * B j s) * (C i t * D j t) := Finset.sum_comm
        _ = ∑ s : Fin k, ∑ i : Fin m, ∑ t : Fin l, ∑ j : Fin n,
              Wmask p Om i j * (A i s * B j s) * (C i t * D j t) :=
            Finset.sum_congr rfl
              (fun s _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
        _ = ∑ s : Fin k, ∑ t : Fin l, ∑ i : Fin m, ∑ j : Fin n,
              Wmask p Om i j * (A i s * B j s) * (C i t * D j t) :=
            Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
    have hu : (∑ s : Fin k, ∑ t : Fin l, ∑ i : Fin m, ∑ j : Fin n,
            Wmask p Om i j * (A i s * B j s) * (C i t * D j t))
        = ∑ st : Fin k × Fin l, ∑ i : Fin m, ∑ j : Fin n,
            Wmask p Om i j * (A i st.1 * B j st.1) * (C i st.2 * D j st.2) := by
      rw [← Finset.sum_product (f := fun st : Fin k × Fin l =>
            ∑ i : Fin m, ∑ j : Fin n,
              Wmask p Om i j * (A i st.1 * B j st.1) * (C i st.2 * D j st.2))]
      rw [Finset.univ_product_univ]
    have e4 : (∑ st : Fin k × Fin l, ∑ i : Fin m, ∑ j : Fin n,
            Wmask p Om i j * (A i st.1 * B j st.1) * (C i st.2 * D j st.2))
        = ∑ st : Fin k × Fin l, ∑ i : Fin m, ∑ j : Fin n,
            (A i st.1 * C i st.2) * Wmask p Om i j * (B j st.1 * D j st.2) :=
      Finset.sum_congr rfl (fun st _ => Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => by ring)))
    exact e1.trans (e2.trans (e3.trans (hu.trans e4)))
  have hpoint : ∀ st : Fin k × Fin l,
      |∑ i : Fin m, ∑ j : Fin n,
          (A i st.1 * C i st.2) * Wmask p Om i j * (B j st.1 * D j st.2)|
        ≤ Lam * Real.sqrt (∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
              * Real.sqrt (∑ j : Fin n, (B j st.1 * D j st.2) ^ 2) := by
    intro st
    have hsum : (∑ i : Fin m, ∑ j : Fin n,
          (A i st.1 * C i st.2) * Wmask p Om i j * (B j st.1 * D j st.2))
        = ∑ i : Fin m, (A i st.1 * C i st.2)
            * ((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i := by
      apply Finset.sum_congr rfl
      intro i _
      have hmv : ((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i
          = ∑ j : Fin n, Wmask p Om i j * (B j st.1 * D j st.2) := by
        rfl
      rw [hmv, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsum]
    have key : ∀ (f g : Fin m → ℝ),
        ∑ i : Fin m, f i * g i
          ≤ Real.sqrt (∑ i : Fin m, f i ^ 2) * Real.sqrt (∑ i : Fin m, g i ^ 2) :=
      fun f g => Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g
    have hcs1 : |∑ i : Fin m, (A i st.1 * C i st.2)
          * ((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i|
        ≤ Real.sqrt (∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
          * Real.sqrt (∑ i : Fin m,
              (((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i) ^ 2) := by
      have hpos := key (fun i => A i st.1 * C i st.2)
        (fun i => ((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i)
      have hnegsq : (∑ i : Fin m, (-(A i st.1 * C i st.2)) ^ 2)
          = ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => by ring)
      have hnegs : (∑ i : Fin m, (-(A i st.1 * C i st.2))
            * ((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i)
          = -(∑ i : Fin m, (A i st.1 * C i st.2)
            * ((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have hneg := key (fun i => -(A i st.1 * C i st.2))
        (fun i => ((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i)
      rw [hnegsq, hnegs] at hneg
      rw [abs_le]
      exact ⟨by linarith [hneg], hpos⟩
    have hnormW : ‖(Matrix.toEuclideanLin (Wmask p Om))
          (WithLp.toLp 2 (fun j : Fin n => B j st.1 * D j st.2))‖
        = Real.sqrt (∑ i : Fin m,
            (((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i) ^ 2) := by
      rw [Matrix.toEuclideanLin_apply_piLp_toLp, EuclideanSpace.norm_eq]
      simp [Real.norm_eq_abs]
    have hnrmy : ‖(WithLp.toLp 2 (fun j : Fin n => B j st.1 * D j st.2) :
          EuclideanSpace ℝ (Fin n))‖
        = Real.sqrt (∑ j : Fin n, (B j st.1 * D j st.2) ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      have hsum : (∑ i : Fin n,
          ‖(WithLp.toLp 2 (fun j : Fin n => B j st.1 * D j st.2) :
            EuclideanSpace ℝ (Fin n)).ofLp i‖ ^ 2)
          = ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Real.norm_eq_abs, pow_two, pow_two]
        rcases le_total 0 (B j st.1 * D j st.2) with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h]; ring
      rw [hsum]
    have hop : Real.sqrt (∑ i : Fin m,
          (((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i) ^ 2)
        ≤ specNorm (Wmask p Om) * Real.sqrt (∑ j : Fin n, (B j st.1 * D j st.2) ^ 2) := by
      have hop2 : ‖(Matrix.toEuclideanLin (Wmask p Om))
            (WithLp.toLp 2 (fun j : Fin n => B j st.1 * D j st.2))‖
          ≤ specNorm (Wmask p Om) * ‖(WithLp.toLp 2 (fun j : Fin n => B j st.1 * D j st.2) :
              EuclideanSpace ℝ (Fin n))‖ :=
        ContinuousLinearMap.le_opNorm
          ((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (Wmask p Om))
          (WithLp.toLp 2 (fun j : Fin n => B j st.1 * D j st.2) : EuclideanSpace ℝ (Fin n))
      rw [hnormW, hnrmy] at hop2
      exact hop2
    calc |∑ i : Fin m, (A i st.1 * C i st.2)
            * ((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i|
        ≤ Real.sqrt (∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
            * Real.sqrt (∑ i : Fin m,
              (((Wmask p Om).mulVec (fun j : Fin n => B j st.1 * D j st.2)) i) ^ 2) := hcs1
      _ ≤ Real.sqrt (∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
            * (specNorm (Wmask p Om)
              * Real.sqrt (∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)) :=
          mul_le_mul_of_nonneg_left hop (Real.sqrt_nonneg _)
      _ = specNorm (Wmask p Om) * Real.sqrt (∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
            * Real.sqrt (∑ j : Fin n, (B j st.1 * D j st.2) ^ 2) := by ring
      _ ≤ Lam * Real.sqrt (∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
            * Real.sqrt (∑ j : Fin n, (B j st.1 * D j st.2) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_right hW (Real.sqrt_nonneg _)
  have hcs : ∑ st : Fin k × Fin l,
        Real.sqrt (∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
          * Real.sqrt (∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)
      ≤ Real.sqrt (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
          * Real.sqrt (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2) := by
    exact Real.sum_sqrt_mul_sqrt_le Finset.univ
      (fun st => Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (fun st => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hx : Real.sqrt (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
      ≤ bFactor A C := by
    have sq_frobA : (frobNorm A) ^ 2 = ∑ i : Fin m, ∑ s : Fin k, A i s ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun s _ => sq_nonneg _)))
    have sq_frobC : (frobNorm C) ^ 2 = ∑ i : Fin m, ∑ t : Fin l, C i t ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun t _ => sq_nonneg _)))
    have h2 : ∀ i : Fin m, (∑ st : Fin k × Fin l, (A i st.1 * C i st.2) ^ 2)
        = ∑ s : Fin k, ∑ t : Fin l, (A i s * C i t) ^ 2 := by
      intro i
      rw [← Finset.sum_product (f := fun st : Fin k × Fin l => (A i st.1 * C i st.2) ^ 2),
        Finset.univ_product_univ]
    have h3 : ∀ i : Fin m, (∑ s : Fin k, ∑ t : Fin l, (A i s * C i t) ^ 2)
        = (∑ s : Fin k, A i s ^ 2) * (∑ t : Fin l, C i t ^ 2) := by
      intro i
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun s _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun t _ => by ring))
    have hSsq : (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
        = ∑ i : Fin m, (∑ s : Fin k, A i s ^ 2) * (∑ t : Fin l, C i t ^ 2) := by
      rw [Finset.sum_comm]
      simp only [h2, h3]
    have hrowC : ∀ i : Fin m, Real.sqrt (∑ t : Fin l, C i t ^ 2) ≤ rowNorm C := by
      intro i
      exact le_csSup (Set.finite_range
        (fun i : Fin m => Real.sqrt (∑ t : Fin l, C i t ^ 2))).bddAbove ⟨i, rfl⟩
    have hrowC0 : 0 ≤ rowNorm C :=
      Real.iSup_nonneg (fun i => Real.sqrt_nonneg _)
    have hC2 : ∀ i : Fin m, (∑ t : Fin l, C i t ^ 2) ≤ (rowNorm C) ^ 2 := by
      intro i
      calc (∑ t : Fin l, C i t ^ 2) = (Real.sqrt (∑ t : Fin l, C i t ^ 2)) ^ 2 :=
            (Real.sq_sqrt (Finset.sum_nonneg (fun t _ => sq_nonneg _))).symm
        _ ≤ (rowNorm C) ^ 2 := by
            simpa [pow_two] using mul_self_le_mul_self (Real.sqrt_nonneg _) (hrowC i)
    have hrowA : ∀ i : Fin m, Real.sqrt (∑ s : Fin k, A i s ^ 2) ≤ rowNorm A := by
      intro i
      exact le_csSup (Set.finite_range
        (fun i : Fin m => Real.sqrt (∑ s : Fin k, A i s ^ 2))).bddAbove ⟨i, rfl⟩
    have hrowA0 : 0 ≤ rowNorm A :=
      Real.iSup_nonneg (fun i => Real.sqrt_nonneg _)
    have hA2 : ∀ i : Fin m, (∑ s : Fin k, A i s ^ 2) ≤ (rowNorm A) ^ 2 := by
      intro i
      calc (∑ s : Fin k, A i s ^ 2) = (Real.sqrt (∑ s : Fin k, A i s ^ 2)) ^ 2 :=
            (Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg _))).symm
        _ ≤ (rowNorm A) ^ 2 := by
            simpa [pow_two] using mul_self_le_mul_self (Real.sqrt_nonneg _) (hrowA i)
    have hb1 : (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
        ≤ (frobNorm A) ^ 2 * (rowNorm C) ^ 2 := by
      rw [hSsq]
      calc ∑ i : Fin m, (∑ s : Fin k, A i s ^ 2) * (∑ t : Fin l, C i t ^ 2)
          ≤ ∑ i : Fin m, (∑ s : Fin k, A i s ^ 2) * (rowNorm C) ^ 2 :=
            Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hC2 i)
              (Finset.sum_nonneg (fun s _ => sq_nonneg _)))
        _ = (∑ i : Fin m, ∑ s : Fin k, A i s ^ 2) * (rowNorm C) ^ 2 := by
            rw [Finset.sum_mul]
        _ = (frobNorm A) ^ 2 * (rowNorm C) ^ 2 := by rw [sq_frobA]
    have hb2 : (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
        ≤ (rowNorm A) ^ 2 * (frobNorm C) ^ 2 := by
      rw [hSsq]
      calc ∑ i : Fin m, (∑ s : Fin k, A i s ^ 2) * (∑ t : Fin l, C i t ^ 2)
          ≤ ∑ i : Fin m, (rowNorm A) ^ 2 * (∑ t : Fin l, C i t ^ 2) :=
            Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hA2 i)
              (Finset.sum_nonneg (fun t _ => sq_nonneg _)))
        _ = (rowNorm A) ^ 2 * (∑ i : Fin m, ∑ t : Fin l, C i t ^ 2) := by
            rw [Finset.mul_sum]
        _ = (rowNorm A) ^ 2 * (frobNorm C) ^ 2 := by rw [sq_frobC]
    have hfac1 : 0 ≤ frobNorm A * rowNorm C :=
      mul_nonneg (Real.sqrt_nonneg _) hrowC0
    have hfac2 : 0 ≤ rowNorm A * frobNorm C :=
      mul_nonneg hrowA0 (Real.sqrt_nonneg _)
    have hb0 : 0 ≤ bFactor A C := by
      simp only [bFactor]
      exact le_min hfac1 hfac2
    have hmin : (bFactor A C) ^ 2
        = min ((frobNorm A * rowNorm C) ^ 2) ((rowNorm A * frobNorm C) ^ 2) := by
      simp only [bFactor]
      rcases le_total (frobNorm A * rowNorm C) (rowNorm A * frobNorm C) with h | h
      · rw [min_eq_left h, min_eq_left (by simpa [pow_two] using mul_self_le_mul_self hfac1 h)]
      · rw [min_eq_right h, min_eq_right (by simpa [pow_two] using mul_self_le_mul_self hfac2 h)]
    have hsq : (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
        ≤ (bFactor A C) ^ 2 := by
      rw [hmin]
      have hb1' : (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
          ≤ (frobNorm A * rowNorm C) ^ 2 := by simpa [mul_pow] using hb1
      have hb2' : (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
          ≤ (rowNorm A * frobNorm C) ^ 2 := by simpa [mul_pow] using hb2
      exact le_min hb1' hb2'
    calc Real.sqrt (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
        ≤ Real.sqrt ((bFactor A C) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = bFactor A C := Real.sqrt_sq hb0
  have hy : Real.sqrt (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)
      ≤ bFactor B D := by
    have sq_frobB : (frobNorm B) ^ 2 = ∑ j : Fin n, ∑ s : Fin k, B j s ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun s _ => sq_nonneg _)))
    have sq_frobD : (frobNorm D) ^ 2 = ∑ j : Fin n, ∑ t : Fin l, D j t ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun t _ => sq_nonneg _)))
    have h2 : ∀ j : Fin n, (∑ st : Fin k × Fin l, (B j st.1 * D j st.2) ^ 2)
        = ∑ s : Fin k, ∑ t : Fin l, (B j s * D j t) ^ 2 := by
      intro j
      rw [← Finset.sum_product (f := fun st : Fin k × Fin l => (B j st.1 * D j st.2) ^ 2),
        Finset.univ_product_univ]
    have h3 : ∀ j : Fin n, (∑ s : Fin k, ∑ t : Fin l, (B j s * D j t) ^ 2)
        = (∑ s : Fin k, B j s ^ 2) * (∑ t : Fin l, D j t ^ 2) := by
      intro j
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun s _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun t _ => by ring))
    have hTsq : (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)
        = ∑ j : Fin n, (∑ s : Fin k, B j s ^ 2) * (∑ t : Fin l, D j t ^ 2) := by
      rw [Finset.sum_comm]
      simp only [h2, h3]
    have hrowD : ∀ j : Fin n, Real.sqrt (∑ t : Fin l, D j t ^ 2) ≤ rowNorm D := by
      intro j
      exact le_csSup (Set.finite_range
        (fun j : Fin n => Real.sqrt (∑ t : Fin l, D j t ^ 2))).bddAbove ⟨j, rfl⟩
    have hrowD0 : 0 ≤ rowNorm D :=
      Real.iSup_nonneg (fun j => Real.sqrt_nonneg _)
    have hD2 : ∀ j : Fin n, (∑ t : Fin l, D j t ^ 2) ≤ (rowNorm D) ^ 2 := by
      intro j
      calc (∑ t : Fin l, D j t ^ 2) = (Real.sqrt (∑ t : Fin l, D j t ^ 2)) ^ 2 :=
            (Real.sq_sqrt (Finset.sum_nonneg (fun t _ => sq_nonneg _))).symm
        _ ≤ (rowNorm D) ^ 2 := by
            simpa [pow_two] using mul_self_le_mul_self (Real.sqrt_nonneg _) (hrowD j)
    have hrowB : ∀ j : Fin n, Real.sqrt (∑ s : Fin k, B j s ^ 2) ≤ rowNorm B := by
      intro j
      exact le_csSup (Set.finite_range
        (fun j : Fin n => Real.sqrt (∑ s : Fin k, B j s ^ 2))).bddAbove ⟨j, rfl⟩
    have hrowB0 : 0 ≤ rowNorm B :=
      Real.iSup_nonneg (fun j => Real.sqrt_nonneg _)
    have hB2 : ∀ j : Fin n, (∑ s : Fin k, B j s ^ 2) ≤ (rowNorm B) ^ 2 := by
      intro j
      calc (∑ s : Fin k, B j s ^ 2) = (Real.sqrt (∑ s : Fin k, B j s ^ 2)) ^ 2 :=
            (Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg _))).symm
        _ ≤ (rowNorm B) ^ 2 := by
            simpa [pow_two] using mul_self_le_mul_self (Real.sqrt_nonneg _) (hrowB j)
    have hb1 : (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)
        ≤ (frobNorm B) ^ 2 * (rowNorm D) ^ 2 := by
      rw [hTsq]
      calc ∑ j : Fin n, (∑ s : Fin k, B j s ^ 2) * (∑ t : Fin l, D j t ^ 2)
          ≤ ∑ j : Fin n, (∑ s : Fin k, B j s ^ 2) * (rowNorm D) ^ 2 :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hD2 j)
              (Finset.sum_nonneg (fun s _ => sq_nonneg _)))
        _ = (∑ j : Fin n, ∑ s : Fin k, B j s ^ 2) * (rowNorm D) ^ 2 := by
            rw [Finset.sum_mul]
        _ = (frobNorm B) ^ 2 * (rowNorm D) ^ 2 := by rw [sq_frobB]
    have hb2 : (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)
        ≤ (rowNorm B) ^ 2 * (frobNorm D) ^ 2 := by
      rw [hTsq]
      calc ∑ j : Fin n, (∑ s : Fin k, B j s ^ 2) * (∑ t : Fin l, D j t ^ 2)
          ≤ ∑ j : Fin n, (rowNorm B) ^ 2 * (∑ t : Fin l, D j t ^ 2) :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hB2 j)
              (Finset.sum_nonneg (fun t _ => sq_nonneg _)))
        _ = (rowNorm B) ^ 2 * (∑ j : Fin n, ∑ t : Fin l, D j t ^ 2) := by
            rw [Finset.mul_sum]
        _ = (rowNorm B) ^ 2 * (frobNorm D) ^ 2 := by rw [sq_frobD]
    have hfac1 : 0 ≤ frobNorm B * rowNorm D :=
      mul_nonneg (Real.sqrt_nonneg _) hrowD0
    have hfac2 : 0 ≤ rowNorm B * frobNorm D :=
      mul_nonneg hrowB0 (Real.sqrt_nonneg _)
    have hb0 : 0 ≤ bFactor B D := by
      simp only [bFactor]
      exact le_min hfac1 hfac2
    have hmin : (bFactor B D) ^ 2
        = min ((frobNorm B * rowNorm D) ^ 2) ((rowNorm B * frobNorm D) ^ 2) := by
      simp only [bFactor]
      rcases le_total (frobNorm B * rowNorm D) (rowNorm B * frobNorm D) with h | h
      · rw [min_eq_left h, min_eq_left (by simpa [pow_two] using mul_self_le_mul_self hfac1 h)]
      · rw [min_eq_right h, min_eq_right (by simpa [pow_two] using mul_self_le_mul_self hfac2 h)]
    have hsq : (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)
        ≤ (bFactor B D) ^ 2 := by
      rw [hmin]
      have hb1' : (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)
          ≤ (frobNorm B * rowNorm D) ^ 2 := by simpa [mul_pow] using hb1
      have hb2' : (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)
          ≤ (rowNorm B * frobNorm D) ^ 2 := by simpa [mul_pow] using hb2
      exact le_min hb1' hb2'
    calc Real.sqrt (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)
        ≤ Real.sqrt ((bFactor B D) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = bFactor B D := Real.sqrt_sq hb0
  have hx0 : 0 ≤ Real.sqrt (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2) :=
    Real.sqrt_nonneg _
  have hy0 : 0 ≤ Real.sqrt (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2) :=
    Real.sqrt_nonneg _
  have h1 : Real.sqrt (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
      * Real.sqrt (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)
      ≤ bFactor A C * bFactor B D :=
    mul_le_mul hx hy hy0 (le_trans hx0 hx)
  calc |frobInner (Tmask p Om (A * B.transpose)) (C * D.transpose)|
      = |∑ st : Fin k × Fin l, ∑ i : Fin m, ∑ j : Fin n,
          (A i st.1 * C i st.2) * Wmask p Om i j * (B j st.1 * D j st.2)| := by rw [hexp]
    _ ≤ ∑ st : Fin k × Fin l,
          |∑ i : Fin m, ∑ j : Fin n,
            (A i st.1 * C i st.2) * Wmask p Om i j * (B j st.1 * D j st.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ st : Fin k × Fin l,
          Lam * Real.sqrt (∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
            * Real.sqrt (∑ j : Fin n, (B j st.1 * D j st.2) ^ 2) :=
        Finset.sum_le_sum (fun st _ => hpoint st)
    _ = Lam * ∑ st : Fin k × Fin l,
          Real.sqrt (∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
            * Real.sqrt (∑ j : Fin n, (B j st.1 * D j st.2) ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun st _ => by ring)
    _ ≤ Lam * (Real.sqrt (∑ st : Fin k × Fin l, ∑ i : Fin m, (A i st.1 * C i st.2) ^ 2)
          * Real.sqrt (∑ st : Fin k × Fin l, ∑ j : Fin n, (B j st.1 * D j st.2) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hLam
    _ ≤ Lam * (bFactor A C * bFactor B D) := mul_le_mul_of_nonneg_left h1 hLam
    _ = Lam * bFactor A C * bFactor B D := by ring
  /- @proof-region region.target-node.session.3ed39f0712b56b93 end -/

end

end Statlib.Imported

