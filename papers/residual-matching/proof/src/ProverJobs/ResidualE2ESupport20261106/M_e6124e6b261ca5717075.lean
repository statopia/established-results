import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
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
theorem statopia_math_node_992664654_dad774ce : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
    specNorm (Matrix.reindex (finSumFinEquiv : (Fin m ⊕ Fin n) ≃ Fin (m + n)) finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A (Matrix.transpose A)
        (0 : Matrix (Fin n) (Fin n) ℝ)))
      = specNorm A := by
  /- @proof-region region.target-node.session.6f1a850eb4c7c068 begin -/
  intro m n A
  have hspec : ∀ {r s : ℕ} (M : Matrix (Fin r) (Fin s) ℝ),
      specNorm M = Statlib.HighDim.MatrixAnalysis.opNorm M := by
    intro r s M
    exact ((Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 M).trans (Matrix.l2_opNorm_def M)).symm
  have hspecT : ∀ {r s : ℕ} (M : Matrix (Fin r) (Fin s) ℝ),
      specNorm M.transpose = specNorm M := by
    intro r s M
    exact (hspec M.transpose).trans
      ((Statlib.HighDim.MatrixAnalysis.opNorm_transpose M).trans (hspec M).symm)
  have hsplit : ∀ {r s : ℕ} (u : Fin r → ℝ) (w : Fin s → ℝ),
      ‖(WithLp.toLp 2 (Sum.elim u w) : EuclideanSpace ℝ (Fin r ⊕ Fin s))‖ ^ 2
        = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin r))‖ ^ 2
          + ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin s))‖ ^ 2 := by
    intro r s u w
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
    simp [EuclideanSpace.norm_sq_eq]
  have key1 : ∀ {p q : ℕ} (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ),
      specNorm (Matrix.reindex (finSumFinEquiv : (Fin p ⊕ Fin q) ≃ Fin (p + q)) finSumFinEquiv M)
        = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M :
            EuclideanSpace ℝ (Fin p ⊕ Fin q) →L[ℝ] EuclideanSpace ℝ (Fin p ⊕ Fin q))‖ := by
    intro p q M
    set e : (Fin p ⊕ Fin q) ≃ Fin (p + q) := finSumFinEquiv with he
    have hC : ∀ {r : ℕ} (X : Matrix (Fin r) (Fin r) ℝ),
        specNorm X = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) X :
          EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r))‖ := by
      intro r X
      exact ((hspec X).trans (Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 X)).trans
        (Matrix.l2_opNorm_toEuclideanCLM X).symm
    rw [hC]
    set Θ : EuclideanSpace ℝ (Fin (p + q)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin p ⊕ Fin q) :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm with hΘ
    have hΘact : ∀ (v : Fin (p + q) → ℝ),
        (Θ (WithLp.toLp 2 v)).ofLp = fun j => v (e j) := by
      intro v
      rw [hΘ, LinearIsometryEquiv.piLpCongrLeft_apply]
      funext j
      rfl
    have hΘsymm : ∀ (y : EuclideanSpace ℝ (Fin p ⊕ Fin q)),
        (Θ.symm y).ofLp = fun i => y.ofLp (e.symm i) := by
      intro y
      have h1 : Θ (WithLp.toLp 2 ((Θ.symm y).ofLp)) = y := by
        rw [WithLp.toLp_ofLp]
        simp
      have h2 := hΘact ((Θ.symm y).ofLp)
      rw [h1] at h2
      funext i
      have h3 := congrFun h2 (e.symm i)
      simpa using h3.symm
    have hfc1 : ∀ (w : Fin (p + q) → ℝ),
        (↑(LinearEquiv.funCongrLeft ℝ ℝ e) : (Fin (p + q) → ℝ) →ₗ[ℝ]
          (Fin p ⊕ Fin q → ℝ)) w = fun j => w (e j) := fun w => rfl
    have hfc2 : ∀ (u : Fin p ⊕ Fin q → ℝ),
        (↑(LinearEquiv.funCongrLeft ℝ ℝ e.symm) : (Fin p ⊕ Fin q → ℝ) →ₗ[ℝ]
          (Fin (p + q) → ℝ)) u = fun i => u (e.symm i) := fun u => rfl
    have hmv : ∀ (w : Fin (p + q) → ℝ),
        (Matrix.reindex e e M).mulVec w
          = fun i => M.mulVec (fun j => w (e j)) (e.symm i) := by
      intro w
      have h := congrArg (fun (f : (Fin (p + q) → ℝ) →ₗ[ℝ] (Fin (p + q) → ℝ)) => f w)
        (Matrix.mulVecLin_reindex e e M)
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply] at h
      rw [h, hfc1, hfc2]
    have hpt : ∀ (x : EuclideanSpace ℝ (Fin (p + q))),
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.reindex e e M)) x
          = Θ.symm ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) (Θ x)) := by
      intro x
      have key : ((Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.reindex e e M)) x).ofLp
          = (Θ.symm ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) (Θ x))).ofLp := by
        rw [Matrix.ofLp_toEuclideanCLM, hΘsymm, Matrix.ofLp_toEuclideanCLM]
        have hΘx : (Θ x).ofLp = fun j => x.ofLp (e j) := by
          conv_lhs => rw [← WithLp.toLp_ofLp 2 x]
          exact hΘact x.ofLp
        rw [hΘx]
        exact hmv x.ofLp
      have key2 := congrArg (WithLp.toLp 2) key
      simpa only [WithLp.toLp_ofLp] using key2
    apply le_antisymm
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
      rw [hpt x]
      calc ‖Θ.symm ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) (Θ x))‖
          = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) (Θ x)‖ :=
            LinearIsometryEquiv.norm_map Θ.symm _
        _ ≤ ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M)‖ * ‖Θ x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M)‖ * ‖x‖ := by
            rw [LinearIsometryEquiv.norm_map Θ x]
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun y => ?_)
      have hy : (Matrix.toEuclideanCLM (𝕜 := ℝ) M) y
          = Θ ((Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.reindex e e M)) (Θ.symm y)) := by
        have h := hpt (Θ.symm y)
        rw [show Θ (Θ.symm y) = y from by simp] at h
        have h2 := congrArg (fun z => Θ z) h
        simpa using h2.symm
      rw [hy]
      calc ‖Θ ((Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.reindex e e M)) (Θ.symm y))‖
          = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.reindex e e M)) (Θ.symm y)‖ :=
            LinearIsometryEquiv.norm_map Θ _
        _ ≤ ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.reindex e e M))‖ * ‖Θ.symm y‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.reindex e e M))‖ * ‖y‖ := by
            rw [LinearIsometryEquiv.norm_map Θ.symm y]
  have key2 : ∀ {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ),
      ‖(Matrix.toEuclideanCLM (𝕜 := ℝ)
          (Matrix.fromBlocks (0 : Matrix (Fin p) (Fin p) ℝ) A A.transpose
            (0 : Matrix (Fin q) (Fin q) ℝ)) :
          EuclideanSpace ℝ (Fin p ⊕ Fin q) →L[ℝ] EuclideanSpace ℝ (Fin p ⊕ Fin q))‖
        = specNorm A := by
    intro p q A
    let Bl : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
      Matrix.fromBlocks (0 : Matrix (Fin p) (Fin p) ℝ) A A.transpose (0 : Matrix (Fin q) (Fin q) ℝ)
    let T : EuclideanSpace ℝ (Fin p ⊕ Fin q) →L[ℝ] EuclideanSpace ℝ (Fin p ⊕ Fin q) :=
      Matrix.toEuclideanCLM (𝕜 := ℝ) Bl
    change ‖T‖ = specNorm A
    have hmul : ∀ (z : EuclideanSpace ℝ (Fin p ⊕ Fin q)),
        (T z).ofLp
          = Sum.elim (A.mulVec (z.ofLp ∘ Sum.inr)) (A.transpose.mulVec (z.ofLp ∘ Sum.inl)) := by
      intro z
      show ((Matrix.toEuclideanCLM (𝕜 := ℝ) Bl) z).ofLp = _
      rw [Matrix.ofLp_toEuclideanCLM, Matrix.fromBlocks_mulVec]
      simp only [Matrix.zero_mulVec, zero_add, add_zero]
    have hdecomp : ∀ (z : EuclideanSpace ℝ (Fin p ⊕ Fin q)),
        ‖z‖ ^ 2 = ‖(WithLp.toLp 2 (z.ofLp ∘ Sum.inl) : EuclideanSpace ℝ (Fin p))‖ ^ 2
          + ‖(WithLp.toLp 2 (z.ofLp ∘ Sum.inr) : EuclideanSpace ℝ (Fin q))‖ ^ 2 := by
      intro z
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
      simp [EuclideanSpace.norm_sq_eq]
    have hT : ∀ (z : EuclideanSpace ℝ (Fin p ⊕ Fin q)),
        ‖T z‖ ^ 2
          = ‖(WithLp.toLp 2 (A.mulVec (z.ofLp ∘ Sum.inr)) : EuclideanSpace ℝ (Fin p))‖ ^ 2
            + ‖(WithLp.toLp 2 (A.transpose.mulVec (z.ofLp ∘ Sum.inl)) :
                EuclideanSpace ℝ (Fin q))‖ ^ 2 := by
      intro z
      rw [EuclideanSpace.norm_sq_eq, hmul z, Fintype.sum_sum_type]
      simp [EuclideanSpace.norm_sq_eq]
    have hb1 : ∀ (w : Fin q → ℝ),
        ‖(WithLp.toLp 2 (A.mulVec w) : EuclideanSpace ℝ (Fin p))‖
          ≤ specNorm A * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin q))‖ := by
      intro w
      have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin q))
      rw [← Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 A, ← hspec A] at h
      simpa using h
    have hb2 : ∀ (v : Fin p → ℝ),
        ‖(WithLp.toLp 2 (A.transpose.mulVec v) : EuclideanSpace ℝ (Fin q))‖
          ≤ specNorm A * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p))‖ := by
      intro v
      have h := Matrix.l2_opNorm_mulVec A.transpose (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p))
      rw [← Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 A.transpose, ← hspec A.transpose,
        hspecT A] at h
      simpa using h
    have hsq_le : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a ^ 2 ≤ b ^ 2 → a ≤ b := by
      intro a b ha hb hab
      have hprod : (a - b) * (a + b) ≤ 0 := by nlinarith
      have hsum : (0:ℝ) ≤ a + b := by linarith
      rcases eq_or_lt_of_le hsum with h0 | hpos
      · have ha0 : a = 0 := by linarith
        have hb0 : b = 0 := by linarith
        linarith
      · by_contra hcon
        push_neg at hcon
        have hgt : 0 < a - b := by linarith
        have hpos' : 0 < (a + b) * (a - b) := mul_pos hpos hgt
        nlinarith
    have hsq_eq : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a ^ 2 = b ^ 2 → a = b := by
      intro a b ha hb hab
      exact le_antisymm (hsq_le ha hb (le_of_eq hab)) (hsq_le hb ha (ge_of_eq hab))
    have hAn : (0:ℝ) ≤ specNorm A := by
      show (0:ℝ) ≤ ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖
      exact norm_nonneg _
    apply le_antisymm
    · refine ContinuousLinearMap.opNorm_le_bound T hAn (fun z => ?_)
      have e1 := hb1 (z.ofLp ∘ Sum.inr)
      have e2 := hb2 (z.ofLp ∘ Sum.inl)
      have e3 := hdecomp z
      have eT := hT z
      have hsq1 : ‖(WithLp.toLp 2 (A.mulVec (z.ofLp ∘ Sum.inr)) : EuclideanSpace ℝ (Fin p))‖ ^ 2
          ≤ (specNorm A * ‖(WithLp.toLp 2 (z.ofLp ∘ Sum.inr) : EuclideanSpace ℝ (Fin q))‖) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_le_mul e1 e1 (norm_nonneg _) (mul_nonneg hAn (norm_nonneg _))
      have hsq2 : ‖(WithLp.toLp 2 (A.transpose.mulVec (z.ofLp ∘ Sum.inl)) :
            EuclideanSpace ℝ (Fin q))‖ ^ 2
          ≤ (specNorm A * ‖(WithLp.toLp 2 (z.ofLp ∘ Sum.inl) : EuclideanSpace ℝ (Fin p))‖) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_le_mul e2 e2 (norm_nonneg _) (mul_nonneg hAn (norm_nonneg _))
      have keyeq : (specNorm A * ‖z‖) ^ 2
          = (specNorm A * ‖(WithLp.toLp 2 (z.ofLp ∘ Sum.inl) : EuclideanSpace ℝ (Fin p))‖) ^ 2
            + (specNorm A * ‖(WithLp.toLp 2 (z.ofLp ∘ Sum.inr) : EuclideanSpace ℝ (Fin q))‖) ^ 2 := by
        rw [show (specNorm A * ‖z‖) ^ 2 = (specNorm A) ^ 2 * ‖z‖ ^ 2 by ring, e3]
        ring
      have hsq : ‖T z‖ ^ 2 ≤ (specNorm A * ‖z‖) ^ 2 := by
        rw [eT, keyeq]
        linarith [hsq1, hsq2]
      exact hsq_le (norm_nonneg (T z)) (mul_nonneg hAn (norm_nonneg z)) hsq
    · let SA : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
        (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A
      have hSA : specNorm A = ‖SA‖ := rfl
      rw [hSA]
      refine ContinuousLinearMap.opNorm_le_bound SA (norm_nonneg T) (fun x => ?_)
      set z : EuclideanSpace ℝ (Fin p ⊕ Fin q) :=
        WithLp.toLp 2 (Sum.elim (0 : Fin p → ℝ) x.ofLp) with hzdef
      have hLx : SA x = WithLp.toLp 2 (A.mulVec x.ofLp) := by
        show (Matrix.toEuclideanLin A) x = WithLp.toLp 2 (A.mulVec x.ofLp)
        rw [Matrix.toEuclideanLin_apply]
      rw [hLx]
      have hzl : z.ofLp ∘ Sum.inl = (0 : Fin p → ℝ) := by
        funext i
        simp [hzdef]
      have hzr : z.ofLp ∘ Sum.inr = x.ofLp := by
        funext i
        simp [hzdef]
      have hzero : A.transpose.mulVec (0 : Fin p → ℝ) = 0 := by
        rw [← Matrix.mulVecLin_apply]
        exact map_zero _
      have h0p : ‖(WithLp.toLp 2 (0 : Fin p → ℝ) : EuclideanSpace ℝ (Fin p))‖ ^ 2 = 0 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp
      have h0q : ‖(WithLp.toLp 2 (0 : Fin q → ℝ) : EuclideanSpace ℝ (Fin q))‖ ^ 2 = 0 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp
      have hxx : ‖(WithLp.toLp 2 x.ofLp : EuclideanSpace ℝ (Fin q))‖ = ‖x‖ := by
        rw [show (WithLp.toLp 2 x.ofLp : EuclideanSpace ℝ (Fin q)) = x from by simp]
      have hTzsq : ‖T z‖ ^ 2
          = ‖(WithLp.toLp 2 (A.mulVec x.ofLp) : EuclideanSpace ℝ (Fin p))‖ ^ 2 := by
        have h1 := hT z
        rw [hzl, hzr, hzero] at h1
        rw [h1, h0q]
        ring
      have hTzn : ‖T z‖ = ‖(WithLp.toLp 2 (A.mulVec x.ofLp) : EuclideanSpace ℝ (Fin p))‖ :=
        hsq_eq (norm_nonneg _) (norm_nonneg _) hTzsq
      have hzsq : ‖z‖ ^ 2 = ‖x‖ ^ 2 := by
        have h1 := hdecomp z
        rw [hzl, hzr] at h1
        rw [h1, h0p, hxx]
        ring
      have hzn : ‖z‖ = ‖x‖ := hsq_eq (norm_nonneg _) (norm_nonneg _) hzsq
      calc ‖(WithLp.toLp 2 (A.mulVec x.ofLp) : EuclideanSpace ℝ (Fin p))‖
          = ‖T z‖ := hTzn.symm
        _ ≤ ‖T‖ * ‖z‖ := ContinuousLinearMap.le_opNorm T z
        _ = ‖T‖ * ‖x‖ := by rw [hzn]
  exact Eq.trans (key1 _) (key2 A)
  /- @proof-region region.target-node.session.6f1a850eb4c7c068 end -/

end

end Statlib.Imported

