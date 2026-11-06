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
theorem statopia_math_node_625384939_fdaf230d : ∀ (m n r D : ℕ) (p theta : ℝ)
    (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (b : Fin D → Matrix (Fin m) (Fin n) ℝ) (Om : Fin m → Fin n → ℝ)
    (hb_orth : ∀ q1 q2 : Fin D, frobInner (b q1) (b q2) = if q1 = q2 then 1 else 0)
    (hb_span : ∀ X : Matrix (Fin m) (Fin n) ℝ, MemTangentRect U0 V0 X →
      ∃ c : Fin D → ℝ, X = ∑ q : Fin D, c q • b q)
    (hspec : specNorm (∑ i : Fin m, ∑ j : Fin n, (p⁻¹ * Om i j - 1) •
        Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)) ≤ theta),
    ∀ A B : Matrix (Fin m) (Fin n) ℝ, MemTangentRect U0 V0 A → MemTangentRect U0 V0 B →
      |frobInner (Tmask p Om A) B| ≤ theta * frobNorm A * frobNorm B := by
  /- @proof-region region.target-node.session.71219043905477a6 begin -/
  intro m n r D p theta U0 V0 b Om hb_orth hb_span hspec A B hA hB
  classical
  have hdiag : ∀ (c : Fin D → ℝ) (a : Fin D),
      ∑ i : Fin D, c i * (if a = i then (1 : ℝ) else 0) = c a := by
    intro c a
    simp
  have hlin1 : ∀ (c : Fin D → ℝ) (X : Fin D → Matrix (Fin m) (Fin n) ℝ)
      (Y : Matrix (Fin m) (Fin n) ℝ),
      frobInner (∑ i, c i • X i) Y = ∑ i, c i * frobInner (X i) Y := by
    intro c X Y
    have h1 : ∀ (a : Fin m) (b : Fin n),
        (∑ i : Fin D, c i * X i a b) * Y a b = ∑ i : Fin D, c i * (X i a b * Y a b) := by
      intro a b
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [frobInner]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, h1]
    calc ∑ a : Fin m, ∑ b : Fin n, ∑ i : Fin D, c i * (X i a b * Y a b)
        = ∑ a : Fin m, ∑ i : Fin D, ∑ b : Fin n, c i * (X i a b * Y a b) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ i : Fin D, ∑ a : Fin m, ∑ b : Fin n, c i * (X i a b * Y a b) :=
          Finset.sum_comm
      _ = ∑ i : Fin D, c i * frobInner (X i) Y := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [frobInner]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
  have hlin2 : ∀ (X : Matrix (Fin m) (Fin n) ℝ) (c : Fin D → ℝ)
      (Y : Fin D → Matrix (Fin m) (Fin n) ℝ),
      frobInner X (∑ i, c i • Y i) = ∑ i, c i * frobInner X (Y i) := by
    intro X c Y
    have h1 : ∀ (a : Fin m) (b : Fin n),
        X a b * (∑ i : Fin D, c i * Y i a b) = ∑ i : Fin D, c i * (X a b * Y i a b) := by
      intro a b
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [frobInner]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, h1]
    calc ∑ a : Fin m, ∑ b : Fin n, ∑ i : Fin D, c i * (X a b * Y i a b)
        = ∑ a : Fin m, ∑ i : Fin D, ∑ b : Fin n, c i * (X a b * Y i a b) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ i : Fin D, ∑ a : Fin m, ∑ b : Fin n, c i * (X a b * Y i a b) :=
          Finset.sum_comm
      _ = ∑ i : Fin D, c i * frobInner X (Y i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [frobInner]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
  obtain ⟨cA, hcA⟩ := hb_span A hA
  obtain ⟨cB, hcB⟩ := hb_span B hB
  have hcoefA : ∀ a : Fin D, frobInner (b a) A = cA a := by
    intro a
    rw [hcA, hlin2 (b a) cA b]
    simp only [hb_orth]
    exact hdiag cA a
  have hcoefB : ∀ a : Fin D, frobInner (b a) B = cB a := by
    intro a
    rw [hcB, hlin2 (b a) cB b]
    simp only [hb_orth]
    exact hdiag cB a
  have hAexp : A = ∑ a : Fin D, frobInner (b a) A • b a := by
    conv_lhs => rw [hcA]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoefA a]
  have hBexp : B = ∑ a : Fin D, frobInner (b a) B • b a := by
    conv_lhs => rw [hcB]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoefB a]
  let Mm : Matrix (Fin D) (Fin D) ℝ :=
    ∑ i : Fin m, ∑ j : Fin n,
      (p⁻¹ * Om i j - 1) • Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)
  have hspec' : specNorm Mm ≤ theta := hspec
  have hMmentry : ∀ a b' : Fin D,
      Mm a b' = ∑ i : Fin m, ∑ j : Fin n,
        (p⁻¹ * Om i j - 1) * (b a i j) * (b b' i j) := by
    intro a b'
    show (∑ i : Fin m, ∑ j : Fin n,
        (p⁻¹ * Om i j - 1) • Matrix.vecMulVec (tangentCoords b i j) (tangentCoords b i j)) a b'
      = ∑ i : Fin m, ∑ j : Fin n, (p⁻¹ * Om i j - 1) * (b a i j) * (b b' i j)
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec,
      Matrix.of_apply, tangentCoords]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have hW : ∀ a b' : Fin D, frobInner (Tmask p Om (b a)) (b b') = Mm a b' := by
    intro a b'
    rw [hMmentry a b', frobInner]
    simp only [Tmask, Wmask]
  have hTmasklin : Tmask p Om A = ∑ a : Fin D, frobInner (b a) A • Tmask p Om (b a) := by
    conv_lhs => rw [hAexp]
    ext i j
    simp only [Tmask, Wmask, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  have hbilin : frobInner (Tmask p Om A) B
      = ∑ a : Fin D, ∑ a' : Fin D, frobInner (b a) A * Mm a a' * frobInner (b a') B := by
    have step1 : frobInner (Tmask p Om A) B
        = ∑ a : Fin D, frobInner (b a) A * frobInner (Tmask p Om (b a)) B := by
      rw [hTmasklin, hlin1 (fun a => frobInner (b a) A) (fun a => Tmask p Om (b a)) B]
    have step2 : ∀ a : Fin D,
        frobInner (Tmask p Om (b a)) B = ∑ a' : Fin D, Mm a a' * frobInner (b a') B := by
      intro a
      conv_lhs => rw [hBexp]
      rw [hlin2 (Tmask p Om (b a)) (fun a' => frobInner (b a') B) b]
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      rw [hW a a']
      ring
    rw [step1]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [step2 a, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    ring
  have hAA : ∑ a : Fin D, (frobInner (b a) A)^2 = ∑ i : Fin m, ∑ j : Fin n, (A i j)^2 := by
    have h1' : frobInner (∑ a : Fin D, frobInner (b a) A • b a) A
        = ∑ a : Fin D, (frobInner (b a) A)^2 := by
      rw [hlin1 (fun a => frobInner (b a) A) b A]
      simp only [pow_two]
    have hsub : frobInner (∑ a : Fin D, frobInner (b a) A • b a) A = frobInner A A := by
      rw [← hAexp]
    have h2 : frobInner A A = ∑ i : Fin m, ∑ j : Fin n, (A i j)^2 := by
      simp only [frobInner, pow_two]
    rw [← h1', hsub]
    exact h2
  have hBB : ∑ a : Fin D, (frobInner (b a) B)^2 = ∑ i : Fin m, ∑ j : Fin n, (B i j)^2 := by
    have h1' : frobInner (∑ a : Fin D, frobInner (b a) B • b a) B
        = ∑ a : Fin D, (frobInner (b a) B)^2 := by
      rw [hlin1 (fun a => frobInner (b a) B) b B]
      simp only [pow_two]
    have hsub : frobInner (∑ a : Fin D, frobInner (b a) B • b a) B = frobInner B B := by
      rw [← hBexp]
    have h2 : frobInner B B = ∑ i : Fin m, ∑ j : Fin n, (B i j)^2 := by
      simp only [frobInner, pow_two]
    rw [← h1', hsub]
    exact h2
  have hnormA : ‖(WithLp.toLp 2 (fun a : Fin D => frobInner (b a) A) : EuclideanSpace ℝ (Fin D))‖
      = frobNorm A := by
    rw [EuclideanSpace.norm_eq, frobNorm]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [hAA]
  have hnormB : ‖(WithLp.toLp 2 (fun a : Fin D => frobInner (b a) B) : EuclideanSpace ℝ (Fin D))‖
      = frobNorm B := by
    rw [EuclideanSpace.norm_eq, frobNorm]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [hBB]
  have hinner_eq : (∑ a : Fin D, ∑ a' : Fin D,
        frobInner (b a) A * Mm a a' * frobInner (b a') B)
      = inner ℝ (WithLp.toLp 2 (Mm.mulVec (fun a' => frobInner (b a') B)))
          (WithLp.toLp 2 (fun a => frobInner (b a) A)) := by
    rw [EuclideanSpace.inner_toLp_toLp]
    change (∑ a : Fin D, ∑ a' : Fin D,
        frobInner (b a) A * Mm a a' * frobInner (b a') B)
      = ∑ a : Fin D, frobInner (b a) A * star ((Mm.mulVec (fun a' => frobInner (b a') B)) a)
    simp only [Matrix.mulVec, star_trivial]
    change (∑ a : Fin D, ∑ a' : Fin D,
        frobInner (b a) A * Mm a a' * frobInner (b a') B)
      = ∑ a : Fin D, frobInner (b a) A * ∑ a' : Fin D, Mm a a' * frobInner (b a') B
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    ring
  have hTx : ((Matrix.toEuclideanLin Mm).toContinuousLinearMap)
        (WithLp.toLp 2 (fun a' => frobInner (b a') B))
      = WithLp.toLp 2 (Mm.mulVec (fun a' => frobInner (b a') B)) := by
    show (Matrix.toEuclideanLin Mm) (WithLp.toLp 2 (fun a' => frobInner (b a') B))
      = WithLp.toLp 2 (Mm.mulVec (fun a' => frobInner (b a') B))
    exact Matrix.toEuclideanLin_apply_piLp_toLp Mm _
  have hstep : |inner ℝ (WithLp.toLp 2 (Mm.mulVec (fun a' => frobInner (b a') B)))
        (WithLp.toLp 2 (fun a => frobInner (b a) A))|
      ≤ specNorm Mm * frobNorm A * frobNorm B := by
    have h2 : ‖(WithLp.toLp 2 (Mm.mulVec (fun a' => frobInner (b a') B)) : EuclideanSpace ℝ (Fin D))‖
        ≤ specNorm Mm * frobNorm B := by
      rw [← hnormB, ← hTx]
      exact ContinuousLinearMap.le_opNorm _ _
    have h1 := abs_real_inner_le_norm
      (WithLp.toLp 2 (Mm.mulVec (fun a' => frobInner (b a') B)))
      (WithLp.toLp 2 (fun a => frobInner (b a) A))
    rw [hnormA] at h1
    calc |inner ℝ (WithLp.toLp 2 (Mm.mulVec (fun a' => frobInner (b a') B)))
          (WithLp.toLp 2 (fun a => frobInner (b a) A))|
        ≤ ‖(WithLp.toLp 2 (Mm.mulVec (fun a' => frobInner (b a') B)) : EuclideanSpace ℝ (Fin D))‖
            * frobNorm A := h1
      _ ≤ (specNorm Mm * frobNorm B) * frobNorm A :=
          mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
      _ = specNorm Mm * frobNorm A * frobNorm B := by ring
  rw [hbilin, hinner_eq]
  calc |inner ℝ (WithLp.toLp 2 (Mm.mulVec (fun a' => frobInner (b a') B)))
        (WithLp.toLp 2 (fun a => frobInner (b a) A))|
      ≤ specNorm Mm * frobNorm A * frobNorm B := hstep
    _ ≤ theta * frobNorm A * frobNorm B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hspec' (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  /- @proof-region region.target-node.session.71219043905477a6 end -/

end

end Statlib.Imported

