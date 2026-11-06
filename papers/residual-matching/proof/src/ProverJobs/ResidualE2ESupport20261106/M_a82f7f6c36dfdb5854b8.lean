import Statlib.HighDim.Vocabulary.Norms
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
theorem statopia_math_node_3027807291_2d8bfe45 : ∀ (m n : ℕ) (p Lam : ℝ)
    (Om : Fin m → Fin n → ℝ) (hp : 0 < p) (hLam : 0 ≤ Lam)
    (hW : specNorm (Wmask p Om) ≤ Lam),
    ∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
      specNorm (Tmask p Om (L * R.transpose)) ≤ Lam * rowNorm L * rowNorm R := by
  /- @proof-region region.target-node.session.5840c2daf4e16e7e begin -/
  intro m n p Lam Om hp hLam_nonneg hLam k L R
  have hOp : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)),
      ‖(Matrix.toEuclideanLin A) v‖ ≤ specNorm A * ‖v‖ := by
    intro A v
    have h := ContinuousLinearMap.le_opNorm
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) v
    simpa [specNorm] using h
  have hWv : ∀ (v : EuclideanSpace ℝ (Fin n)),
      ‖(Matrix.toEuclideanLin (Wmask p Om)) v‖ ≤ Lam * ‖v‖ := by
    intro v
    refine le_trans (hOp (Wmask p Om) v) ?_
    exact mul_le_mul_of_nonneg_right hLam (norm_nonneg v)
  have hE1 : ∀ {N : ℕ} (u : EuclideanSpace ℝ (Fin N)), ‖u‖ ^ 2 = ∑ i : Fin N, (u.ofLp i) ^ 2 := by
    intro N u
    rw [← real_inner_self_eq_norm_sq u, PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [RCLike.inner_apply']
    simp [sq]
  have hE2 : ∀ {N : ℕ} (w : Fin N → ℝ),
      ‖Statlib.HighDim.Vocabulary.toEuclidean w‖ = Real.sqrt (∑ i : Fin N, (w i) ^ 2) := by
    intro N w
    have h3 : ‖Statlib.HighDim.Vocabulary.toEuclidean w‖ ^ 2 = ∑ i : Fin N, (w i) ^ 2 := by
      rw [hE1]
      simp [Statlib.HighDim.Vocabulary.toEuclidean]
    conv_lhs => rw [← Real.sqrt_sq (norm_nonneg (Statlib.HighDim.Vocabulary.toEuclidean w))]
    rw [h3]
  have hWsqrt : ∀ (w : Fin n → ℝ),
      Real.sqrt (∑ i : Fin m, (∑ j : Fin n, Wmask p Om i j * w j) ^ 2)
        ≤ Lam * Real.sqrt (∑ j : Fin n, (w j) ^ 2) := by
    intro w
    have h := hWv (Statlib.HighDim.Vocabulary.toEuclidean w)
    have hLP : (Matrix.toEuclideanLin (Wmask p Om)) (Statlib.HighDim.Vocabulary.toEuclidean w)
        = Statlib.HighDim.Vocabulary.toEuclidean
            (fun i : Fin m => ∑ j : Fin n, Wmask p Om i j * w j) := by
      simp [Statlib.HighDim.Vocabulary.toEuclidean]
      try rfl
    rw [hLP] at h
    simp only [hE2] at h
    exact h
  have hLrow : ∀ i : Fin m, Real.sqrt (∑ s : Fin k, (L i s) ^ 2) ≤ rowNorm L := by
    intro i
    refine le_ciSup (f := fun i : Fin m => Real.sqrt (∑ s : Fin k, (L i s) ^ 2)) ?_ i
    exact Set.Finite.bddAbove (Set.finite_range _)
  have hRrow : ∀ j : Fin n, Real.sqrt (∑ s : Fin k, (R j s) ^ 2) ≤ rowNorm R := by
    intro j
    refine le_ciSup (f := fun j : Fin n => Real.sqrt (∑ s : Fin k, (R j s) ^ 2)) ?_ j
    exact Set.Finite.bddAbove (Set.finite_range _)
  have hrowLnn : 0 ≤ rowNorm L :=
    Real.iSup_nonneg (f := fun i : Fin m => Real.sqrt (∑ s : Fin k, (L i s) ^ 2))
      (fun i => Real.sqrt_nonneg _)
  have hrowRnn : 0 ≤ rowNorm R :=
    Real.iSup_nonneg (f := fun j : Fin n => Real.sqrt (∑ s : Fin k, (R j s) ^ 2))
      (fun j => Real.sqrt_nonneg _)
  have hCS : ∀ {N : ℕ} (f g : Fin N → ℝ),
      |∑ i : Fin N, f i * g i|
        ≤ Real.sqrt (∑ i : Fin N, f i ^ 2) * Real.sqrt (∑ i : Fin N, g i ^ 2) := by
    intro N f g
    have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := f) (g := g)
    have hA' : 0 ≤ ∑ i : Fin N, f i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hB' : 0 ≤ ∑ i : Fin N, g i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    calc |∑ i : Fin N, f i * g i| = Real.sqrt ((∑ i : Fin N, f i * g i) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∑ i : Fin N, f i ^ 2) * (∑ i : Fin N, g i ^ 2)) := Real.sqrt_le_sqrt h
      _ = Real.sqrt (∑ i : Fin N, f i ^ 2) * Real.sqrt (∑ i : Fin N, g i ^ 2) := Real.sqrt_mul hA' _
  have hA : ∀ (x : Fin n → ℝ) (y : Fin m → ℝ),
      |∑ i : Fin m, ∑ j : Fin n, y i * (Tmask p Om (L * R.transpose) i j * x j)|
        ≤ Lam * rowNorm L * rowNorm R * Real.sqrt (∑ i : Fin m, (y i) ^ 2)
            * Real.sqrt (∑ j : Fin n, (x j) ^ 2) := by
    intro x y
    set X : Matrix (Fin m) (Fin k) ℝ := fun i s => y i * L i s with hX
    set Y : Matrix (Fin m) (Fin k) ℝ := fun i s => ∑ j : Fin n, Wmask p Om i j * (x j * R j s) with hY
    have hEq : (∑ i : Fin m, ∑ j : Fin n, y i * (Tmask p Om (L * R.transpose) i j * x j))
        = frobInner X Y := by
      rw [frobInner, hX, hY]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have step1 : (∑ j : Fin n, y i * (Tmask p Om (L * R.transpose) i j * x j))
          = ∑ j : Fin n, ∑ s : Fin k, y i * (Wmask p Om i j * (L i s * R j s)) * x j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hT : Tmask p Om (L * R.transpose) i j
            = Wmask p Om i j * ∑ s : Fin k, L i s * R j s := by
          simp [Tmask, Matrix.mul_apply, Matrix.transpose_apply]
        rw [hT]
        calc y i * ((Wmask p Om i j * ∑ s : Fin k, L i s * R j s) * x j)
            = (y i * Wmask p Om i j * x j) * (∑ s : Fin k, L i s * R j s) := by ring
          _ = ∑ s : Fin k, (y i * Wmask p Om i j * x j) * (L i s * R j s) := by
              rw [Finset.mul_sum]
          _ = ∑ s : Fin k, y i * (Wmask p Om i j * (L i s * R j s)) * x j :=
              Finset.sum_congr rfl (fun s _ => by ring)
      rw [step1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hii : |frobInner X Y| ≤ frobNorm X * frobNorm Y := by
      have hin : ∀ i : Fin m, |∑ s : Fin k, X i s * Y i s|
          ≤ Real.sqrt (∑ s : Fin k, (X i s) ^ 2) * Real.sqrt (∑ s : Fin k, (Y i s) ^ 2) :=
        fun i => hCS (fun s => X i s) (fun s => Y i s)
      have h1 : |∑ i : Fin m, ∑ s : Fin k, X i s * Y i s|
          ≤ ∑ i : Fin m, Real.sqrt (∑ s : Fin k, (X i s) ^ 2)
              * Real.sqrt (∑ s : Fin k, (Y i s) ^ 2) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum (fun i _ => hin i)
      have h2 : ∑ i : Fin m, Real.sqrt (∑ s : Fin k, (X i s) ^ 2)
            * Real.sqrt (∑ s : Fin k, (Y i s) ^ 2)
          ≤ Real.sqrt (∑ i : Fin m, ∑ s : Fin k, (X i s) ^ 2)
            * Real.sqrt (∑ i : Fin m, ∑ s : Fin k, (Y i s) ^ 2) := by
        have h := hCS (fun i : Fin m => Real.sqrt (∑ s : Fin k, (X i s) ^ 2))
          (fun i : Fin m => Real.sqrt (∑ s : Fin k, (Y i s) ^ 2))
        refine le_trans (le_abs_self _) ?_
        refine le_trans h ?_
        have e1 : ∀ i : Fin m, (Real.sqrt (∑ s : Fin k, (X i s) ^ 2)) ^ 2 = ∑ s : Fin k, (X i s) ^ 2 :=
          fun i => Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg _))
        have e2 : ∀ i : Fin m, (Real.sqrt (∑ s : Fin k, (Y i s) ^ 2)) ^ 2 = ∑ s : Fin k, (Y i s) ^ 2 :=
          fun i => Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg _))
        rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_congr rfl (fun i _ => e2 i)]
      have h3 : |∑ i : Fin m, ∑ s : Fin k, X i s * Y i s| = |frobInner X Y| := by rw [frobInner]
      rw [h3] at h1
      refine le_trans h1 ?_
      refine le_trans h2 ?_
      rfl
    have hiii : frobNorm X ≤ rowNorm L * Real.sqrt (∑ i : Fin m, (y i) ^ 2) := by
      have hX2 : (frobNorm X) ^ 2 = ∑ i : Fin m, ∑ s : Fin k, (X i s) ^ 2 := by
        rw [frobNorm,
          Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun s _ => sq_nonneg _)))]
      have hrow : ∀ i : Fin m, ∑ s : Fin k, (X i s) ^ 2 ≤ (y i) ^ 2 * (rowNorm L) ^ 2 := by
        intro i
        have hLi : ∑ s : Fin k, (L i s) ^ 2 ≤ (rowNorm L) ^ 2 := by
          calc ∑ s : Fin k, (L i s) ^ 2 = (Real.sqrt (∑ s : Fin k, (L i s) ^ 2)) ^ 2 :=
                (Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg _))).symm
            _ ≤ (rowNorm L) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hLrow i) 2
        calc ∑ s : Fin k, (X i s) ^ 2 = (y i) ^ 2 * ∑ s : Fin k, (L i s) ^ 2 := by
              rw [hX, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun s _ => by ring)
          _ ≤ (y i) ^ 2 * (rowNorm L) ^ 2 := mul_le_mul_of_nonneg_left hLi (sq_nonneg _)
      have hsq : (frobNorm X) ^ 2 ≤ (rowNorm L * Real.sqrt (∑ i : Fin m, (y i) ^ 2)) ^ 2 := by
        rw [hX2, mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
        calc ∑ i : Fin m, ∑ s : Fin k, (X i s) ^ 2
            ≤ ∑ i : Fin m, (y i) ^ 2 * (rowNorm L) ^ 2 := Finset.sum_le_sum (fun i _ => hrow i)
          _ = (rowNorm L) ^ 2 * ∑ i : Fin m, (y i) ^ 2 := by rw [← Finset.sum_mul]; ring
      have h2 : 0 ≤ frobNorm X := Real.sqrt_nonneg _
      have h3 : 0 ≤ rowNorm L * Real.sqrt (∑ i : Fin m, (y i) ^ 2) :=
        mul_nonneg hrowLnn (Real.sqrt_nonneg _)
      nlinarith [hsq, h2, h3]
    have hiv : frobNorm Y ≤ Lam * (rowNorm R * Real.sqrt (∑ j : Fin n, (x j) ^ 2)) := by
      have hY2 : (frobNorm Y) ^ 2 = ∑ i : Fin m, ∑ s : Fin k, (Y i s) ^ 2 := by
        rw [frobNorm,
          Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun s _ => sq_nonneg _)))]
      have hcol : ∀ s : Fin k, ∑ i : Fin m, (Y i s) ^ 2
          ≤ Lam ^ 2 * ∑ j : Fin n, (x j * R j s) ^ 2 := by
        intro s
        have h := hWsqrt (fun j : Fin n => x j * R j s)
        have hS : ∑ i : Fin m, (Y i s) ^ 2
            = ∑ i : Fin m, (∑ j : Fin n, Wmask p Om i j * (x j * R j s)) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hY]
        rw [hS]
        have hnn : 0 ≤ ∑ j : Fin n, (x j * R j s) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
        calc ∑ i : Fin m, (∑ j : Fin n, Wmask p Om i j * (x j * R j s)) ^ 2
            = (Real.sqrt (∑ i : Fin m, (∑ j : Fin n, Wmask p Om i j * (x j * R j s)) ^ 2)) ^ 2 :=
              (Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))).symm
          _ ≤ (Lam * Real.sqrt (∑ j : Fin n, (x j * R j s) ^ 2)) ^ 2 :=
              pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
          _ = Lam ^ 2 * ∑ j : Fin n, (x j * R j s) ^ 2 := by rw [mul_pow, Real.sq_sqrt hnn]
      have hA1 : ∑ s : Fin k, ∑ j : Fin n, (x j * R j s) ^ 2
          = ∑ j : Fin n, ∑ s : Fin k, (x j * R j s) ^ 2 := Finset.sum_comm
      have hA2 : ∑ j : Fin n, ∑ s : Fin k, (x j * R j s) ^ 2
          = ∑ j : Fin n, (x j) ^ 2 * ∑ s : Fin k, (R j s) ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun s _ => by ring)
      have hA3 : ∑ j : Fin n, (x j) ^ 2 * ∑ s : Fin k, (R j s) ^ 2
          ≤ ∑ j : Fin n, (x j) ^ 2 * (rowNorm R) ^ 2 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        calc ∑ s : Fin k, (R j s) ^ 2 = (Real.sqrt (∑ s : Fin k, (R j s) ^ 2)) ^ 2 :=
              (Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg _))).symm
          _ ≤ (rowNorm R) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hRrow j) 2
      have hA4 : ∑ j : Fin n, (x j) ^ 2 * (rowNorm R) ^ 2
          = (rowNorm R) ^ 2 * ∑ j : Fin n, (x j) ^ 2 := by
        rw [← Finset.sum_mul]; ring
      have hsq : (frobNorm Y) ^ 2
          ≤ (Lam * (rowNorm R * Real.sqrt (∑ j : Fin n, (x j) ^ 2))) ^ 2 := by
        rw [hY2]
        rw [Finset.sum_comm]
        calc ∑ s : Fin k, ∑ i : Fin m, (Y i s) ^ 2
            ≤ ∑ s : Fin k, Lam ^ 2 * ∑ j : Fin n, (x j * R j s) ^ 2 :=
              Finset.sum_le_sum (fun s _ => hcol s)
          _ = Lam ^ 2 * ∑ s : Fin k, ∑ j : Fin n, (x j * R j s) ^ 2 := by
              rw [← Finset.mul_sum]
          _ ≤ Lam ^ 2 * ((rowNorm R) ^ 2 * ∑ j : Fin n, (x j) ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Lam)
              rw [hA1, hA2]
              exact le_trans hA3 (le_of_eq hA4)
          _ = (Lam * (rowNorm R * Real.sqrt (∑ j : Fin n, (x j) ^ 2))) ^ 2 := by
              rw [mul_pow, mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
              try ring
      have h2 : 0 ≤ frobNorm Y := Real.sqrt_nonneg _
      have h3 : 0 ≤ Lam * (rowNorm R * Real.sqrt (∑ j : Fin n, (x j) ^ 2)) :=
        mul_nonneg hLam_nonneg (mul_nonneg hrowRnn (Real.sqrt_nonneg _))
      nlinarith [hsq, h2, h3]
    have hprod : frobNorm X * frobNorm Y
        ≤ (rowNorm L * Real.sqrt (∑ i : Fin m, (y i) ^ 2))
          * (Lam * (rowNorm R * Real.sqrt (∑ j : Fin n, (x j) ^ 2))) :=
      mul_le_mul hiii hiv (Real.sqrt_nonneg _) (mul_nonneg hrowLnn (Real.sqrt_nonneg _))
    calc |∑ i : Fin m, ∑ j : Fin n, y i * (Tmask p Om (L * R.transpose) i j * x j)|
        = |frobInner X Y| := by rw [hEq]
      _ ≤ frobNorm X * frobNorm Y := hii
      _ ≤ (rowNorm L * Real.sqrt (∑ i : Fin m, (y i) ^ 2))
            * (Lam * (rowNorm R * Real.sqrt (∑ j : Fin n, (x j) ^ 2))) := hprod
      _ = Lam * rowNorm L * rowNorm R * Real.sqrt (∑ i : Fin m, (y i) ^ 2)
            * Real.sqrt (∑ j : Fin n, (x j) ^ 2) := by ring
  have hbilin : ∀ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)),
      |inner ℝ y ((Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x)|
        ≤ Lam * rowNorm L * rowNorm R * ‖x‖ * ‖y‖ := by
    intro x y
    have h1 : inner ℝ y ((Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x)
        = ∑ i : Fin m, ∑ j : Fin n, y.ofLp i * (Tmask p Om (L * R.transpose) i j * x.ofLp j) := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.ofLp_toEuclideanLin_apply, RCLike.inner_apply']
      simp only [Matrix.mulVec]
      have dotdef : ∀ (u v : Fin n → ℝ), u ⬝ᵥ v = ∑ j, u j * v j := fun u v => rfl
      rw [dotdef, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp
    have hsqrt_y : Real.sqrt (∑ i : Fin m, (y.ofLp i) ^ 2) = ‖y‖ := by
      rw [← hE2]
      simp [Statlib.HighDim.Vocabulary.toEuclidean]
    have hsqrt_x : Real.sqrt (∑ j : Fin n, (x.ofLp j) ^ 2) = ‖x‖ := by
      rw [← hE2]
      simp [Statlib.HighDim.Vocabulary.toEuclidean]
    calc |inner ℝ y ((Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x)|
        = |∑ i : Fin m, ∑ j : Fin n, y.ofLp i * (Tmask p Om (L * R.transpose) i j * x.ofLp j)| := by
          rw [h1]
      _ ≤ Lam * rowNorm L * rowNorm R * Real.sqrt (∑ i : Fin m, (y.ofLp i) ^ 2)
            * Real.sqrt (∑ j : Fin n, (x.ofLp j) ^ 2) := hA _ _
      _ = Lam * rowNorm L * rowNorm R * ‖x‖ * ‖y‖ := by rw [hsqrt_y, hsqrt_x]; ring
  have hCnn : 0 ≤ Lam * rowNorm L * rowNorm R :=
    mul_nonneg (mul_nonneg hLam_nonneg hrowLnn) hrowRnn
  rw [specNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ hCnn (fun x => ?_)
  show ‖(Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x‖
      ≤ Lam * rowNorm L * rowNorm R * ‖x‖
  rcases eq_or_ne ((Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x) 0 with h0 | h0
  · rw [h0, norm_zero]
    exact mul_nonneg hCnn (norm_nonneg x)
  · have hvpos : 0 < ‖(Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x‖ :=
      norm_pos_iff.mpr h0
    have hb := hbilin x ((Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x)
    rw [real_inner_self_eq_norm_sq ((Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x),
      abs_of_nonneg (by positivity)] at hb
    have hkey : ‖(Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x‖
        * (‖(Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x‖
          - Lam * rowNorm L * rowNorm R * ‖x‖) ≤ 0 := by nlinarith [hb]
    have hkey2 : ‖(Matrix.toEuclideanLin (Tmask p Om (L * R.transpose))) x‖
        - Lam * rowNorm L * rowNorm R * ‖x‖ ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      exact absurd hkey (not_le.mpr (mul_pos hvpos hc))
    linarith

  /- @proof-region region.target-node.session.5840c2daf4e16e7e end -/

end

end Statlib.Imported

