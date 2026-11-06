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
theorem statopia_math_node_3968230781_9dc3fc25 : ∀ (m n r : ℕ) (hr : 0 < r) (hn : 1 ≤ n) (hnm : n ≤ m)
    (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (hU : U0.transpose * U0 = 1) (hV : V0.transpose * V0 = 1),
    ∃ (D : ℕ) (b : Fin D → Matrix (Fin m) (Fin n) ℝ)
      (z : Fin m → Fin n → Matrix (Fin m) (Fin n) ℝ),
      (∀ p : Fin D, MemTangentRect U0 V0 (b p)) ∧
      (∀ p q : Fin D, frobInner (b p) (b q) = if p = q then (1 : ℝ) else 0) ∧
      (∀ X : Matrix (Fin m) (Fin n) ℝ, MemTangentRect U0 V0 X →
        ∃ c : Fin D → ℝ, X = ∑ p : Fin D, c p • b p) ∧
      (∀ (i : Fin m) (j : Fin n), MemTangentRect U0 V0 (z i j)) ∧
      (∀ (i : Fin m) (j : Fin n) (Y : Matrix (Fin m) (Fin n) ℝ),
        MemTangentRect U0 V0 Y →
        frobInner (matrixUnit i j) Y = frobInner (z i j) Y) ∧
      (∀ (i : Fin m) (j : Fin n),
        frobNorm (z i j) = Real.sqrt (∑ p : Fin D, (tangentCoords b i j p) ^ 2)) := by
  /- @proof-region region.target-node.session.e740bc74f5228f1c begin -/
  intro m n r hr hn hnm U0 V0 hU hV
  let F := EuclideanSpace ℝ (Fin m × Fin n)
  let toMat : F → Matrix (Fin m) (Fin n) ℝ := fun v i j => v.ofLp (i, j)
  let toF : Matrix (Fin m) (Fin n) ℝ → F := fun X => WithLp.toLp 2 (fun p : Fin m × Fin n => X p.1 p.2)
  have htoMat_toF : ∀ X : Matrix (Fin m) (Fin n) ℝ, toMat (toF X) = X := by
    intro X
    ext i j
    simp [toMat, toF]
  have htoF_toMat : ∀ v : F, toF (toMat v) = v := by
    intro v
    simp [toMat, toF]
  have htoMat_add : ∀ v w : F, toMat (v + w) = toMat v + toMat w := by
    intro v w
    ext i j
    rfl
  have htoMat_smul : ∀ (c : ℝ) (v : F), toMat (c • v) = c • toMat v := by
    intro c v
    ext i j
    rfl
  have htoMat_zero : toMat 0 = (0 : Matrix (Fin m) (Fin n) ℝ) := by
    ext i j
    rfl
  have hinner_eq : ∀ (v w : F), inner ℝ v w = frobInner (toMat v) (toMat w) := by
    intro v w
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [frobInner, toMat, dotProduct, mul_comm]
    rw [Fintype.sum_prod_type]
  let T : Submodule ℝ F :=
    { carrier := {v | MemTangentRect U0 V0 (toMat v)}
      zero_mem' := by
        refine ⟨0, 0, ?_⟩
        rw [htoMat_zero]
        simp
      add_mem' := by
        rintro v w ⟨A, B, hv⟩ ⟨A', B', hw⟩
        refine ⟨A + A', B + B', ?_⟩
        rw [htoMat_add, hv, hw]
        simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
        abel
      smul_mem' := by
        rintro c v ⟨A, B, hv⟩
        refine ⟨c • A, c • B, ?_⟩
        rw [htoMat_smul, hv]
        simp [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul] }
  let D := Module.finrank ℝ ↥T
  let hb : OrthonormalBasis (Fin D) ℝ ↥T := stdOrthonormalBasis ℝ ↥T
  let b : Fin D → Matrix (Fin m) (Fin n) ℝ := fun p => toMat (hb p : F)
  let zf : Fin m → Fin n → ↥T := fun i j => ∑ p : Fin D, tangentCoords b i j p • hb p
  let z : Fin m → Fin n → Matrix (Fin m) (Fin n) ℝ := fun i j => toMat (zf i j : F)
  have htoMat_sum : ∀ (s : Finset (Fin D)) (f : Fin D → F),
      toMat (∑ p ∈ s, f p) = ∑ p ∈ s, toMat (f p) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro f
      simp [htoMat_zero]
    | insert a s ha ih =>
      intro f
      simp [Finset.sum_insert ha, htoMat_add, ih]
  have hcoe_sum : ∀ (a : Fin D → ℝ),
      ((∑ p : Fin D, a p • hb p : ↥T) : F) = ∑ p : Fin D, a p • (hb p : F) := by
    intro a
    have hgen : ∀ s : Finset (Fin D),
        ((∑ p ∈ s, a p • hb p : ↥T) : F) = ∑ p ∈ s, a p • (hb p : F) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.sum_insert hx]
        simp [ih]
    exact hgen Finset.univ
  have h1 : ∀ p : Fin D, MemTangentRect U0 V0 (b p) := fun p => (hb p).2
  have h2 : ∀ p q : Fin D, frobInner (b p) (b q) = if p = q then 1 else 0 := by
    intro p q
    have hstep : frobInner (b p) (b q) = inner ℝ (hb p) (hb q) := by
      have h1' : frobInner (b p) (b q) = frobInner (toMat (hb p : F)) (toMat (hb q : F)) := rfl
      rw [h1', ← hinner_eq (hb p : F) (hb q : F), ← Submodule.coe_inner T (hb p) (hb q)]
    rw [hstep]
    exact (orthonormal_iff_ite.mp hb.orthonormal) p q
  have h3 : ∀ X : Matrix (Fin m) (Fin n) ℝ, MemTangentRect U0 V0 X →
      ∃ c : Fin D → ℝ, X = ∑ p : Fin D, c p • b p := by
    intro X hX
    have hmem : toF X ∈ T := by
      show MemTangentRect U0 V0 (toMat (toF X))
      rw [htoMat_toF]
      exact hX
    have hrepr := OrthonormalBasis.sum_repr' hb (⟨toF X, hmem⟩ : ↥T)
    have hcoef : ∀ p : Fin D, inner ℝ (hb p) (⟨toF X, hmem⟩ : ↥T) = frobInner (b p) X := by
      intro p
      rw [Submodule.coe_inner, hinner_eq]
    refine ⟨fun p => frobInner (b p) X, ?_⟩
    have hcoeF : (∑ p : Fin D, frobInner (b p) X • (hb p : F)) = toF X := by
      have hsum : ((∑ p : Fin D, frobInner (b p) X • hb p : ↥T) : F)
          = ∑ p : Fin D, frobInner (b p) X • (hb p : F) :=
        hcoe_sum (fun p => frobInner (b p) X)
      rw [← hsum]
      have hsub : (∑ p : Fin D, frobInner (b p) X • hb p : ↥T) = ⟨toF X, hmem⟩ := by
        rw [← hrepr]
        exact Finset.sum_congr rfl (fun p _ => by rw [hcoef])
      rw [hsub]
    have htot : toMat (∑ p : Fin D, frobInner (b p) X • (hb p : F))
        = ∑ p : Fin D, frobInner (b p) X • b p := by
      rw [htoMat_sum]
      exact Finset.sum_congr rfl (fun p _ => by simp [htoMat_smul, b])
    rw [← htot, hcoeF, htoMat_toF]
  have h4 : ∀ (i : Fin m) (j : Fin n), MemTangentRect U0 V0 (z i j) := fun i j => (zf i j).2
  have h5 : ∀ (i : Fin m) (j : Fin n) (Y : Matrix (Fin m) (Fin n) ℝ),
      MemTangentRect U0 V0 Y → frobInner (matrixUnit i j) Y = frobInner (z i j) Y := by
    intro i j Y hY
    have hYmem : toF Y ∈ T := by
      show MemTangentRect U0 V0 (toMat (toF Y))
      rw [htoMat_toF]
      exact hY
    set y : ↥T := ⟨toF Y, hYmem⟩ with hy
    have hyval : (y : F) = toF Y := by rw [hy]
    have hunit : ∀ X : Matrix (Fin m) (Fin n) ℝ, frobInner (matrixUnit i j) X = X i j := by
      intro X
      rw [frobInner, Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp [matrixUnit]
        · intro b _ hb'
          simp [matrixUnit, hb']
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      · intro a _ ha
        simp [matrixUnit, ha]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have hrepr : (∑ p : Fin D, inner ℝ (hb p) y • hb p : ↥T) = y :=
      OrthonormalBasis.sum_repr' hb y
    have hYexp : toF Y = ∑ p : Fin D, inner ℝ (hb p) y • (hb p : F) := by
      have h1 : ((∑ p : Fin D, inner ℝ (hb p) y • hb p : ↥T) : F) = toF Y :=
        (congrArg (fun z : ↥T => (z : F)) hrepr).trans hyval
      exact h1.symm.trans (hcoe_sum (fun p => inner ℝ (hb p) y))
    have hentry : ∀ p : Fin D, inner ℝ (toF (matrixUnit i j)) (hb p : F) = tangentCoords b i j p := by
      intro p
      rw [hinner_eq (toF (matrixUnit i j)) (hb p : F)]
      simpa [b, htoMat_toF] using hunit (b p)
    have hzF0 : toF (z i j) = ((zf i j : ↥T) : F) := by
      rw [show z i j = toMat (zf i j : F) from rfl, htoF_toMat]
    have hL : frobInner (matrixUnit i j) Y
        = ∑ p : Fin D, tangentCoords b i j p * inner ℝ (hb p) y := by
      have h1 : frobInner (matrixUnit i j) Y = inner ℝ (toF (matrixUnit i j)) (toF Y) := by
        rw [← htoMat_toF (matrixUnit i j), ← htoMat_toF Y,
          ← hinner_eq (toF (matrixUnit i j)) (toF Y)]
      rw [h1, hYexp, inner_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [real_inner_smul_right, hentry p]
      exact mul_comm (inner ℝ (hb p) y) (tangentCoords b i j p)
    have hR : frobInner (z i j) Y
        = ∑ p : Fin D, tangentCoords b i j p * inner ℝ (hb p) y := by
      have h1 : frobInner (z i j) Y = inner ℝ (zf i j) y := by
        rw [← htoMat_toF (z i j), ← htoMat_toF Y,
          ← hinner_eq (toF (z i j)) (toF Y), hzF0, ← hyval,
          ← Submodule.coe_inner T (zf i j) y]
      have h2 : inner ℝ (zf i j) y = ∑ p : Fin D, tangentCoords b i j p * inner ℝ (hb p) y := by
        rw [show zf i j = (∑ p : Fin D, tangentCoords b i j p • hb p : ↥T) from rfl]
        rw [sum_inner]
        exact Finset.sum_congr rfl
          (fun p _ => real_inner_smul_left (hb p) y (tangentCoords b i j p))
      rw [h1, h2]
    rw [hL, hR]
  have hparseval : ∀ (a : Fin D → ℝ),
      inner ℝ (∑ p : Fin D, a p • hb p) (∑ p : Fin D, a p • hb p) = ∑ p : Fin D, a p ^ 2 := by
    intro a
    rw [Orthonormal.inner_sum hb.orthonormal a a Finset.univ]
    exact Finset.sum_congr rfl (fun p _ => by simp [sq])
  have h6 : ∀ (i : Fin m) (j : Fin n),
      frobNorm (z i j) = Real.sqrt (∑ p : Fin D, (tangentCoords b i j p) ^ 2) := by
    intro i j
    have hnormfi : frobInner (z i j) (z i j) = ∑ p : Fin D, (tangentCoords b i j p) ^ 2 := by
      have h1 : frobInner (z i j) (z i j) = inner ℝ (toF (z i j)) (toF (z i j)) := by
        rw [← htoMat_toF (z i j), ← hinner_eq (toF (z i j)) (toF (z i j))]
      rw [h1]
      have hzF : toF (z i j) = ((∑ p : Fin D, tangentCoords b i j p • hb p : ↥T) : F) := by
        rw [show z i j = toMat (zf i j : F) from rfl, htoF_toMat]
      rw [hzF, ← Submodule.coe_inner T (∑ p : Fin D, tangentCoords b i j p • hb p : ↥T)
        (∑ p : Fin D, tangentCoords b i j p • hb p : ↥T)]
      exact hparseval (tangentCoords b i j)
    have hnorm : frobNorm (z i j) = Real.sqrt (frobInner (z i j) (z i j)) := by
      rw [frobNorm, frobInner]
      congr 1
      simp [sq]
    rw [hnorm, hnormfi]
  exact ⟨D, b, z, h1, h2, h3, h4, h5, h6⟩
  /- @proof-region region.target-node.session.e740bc74f5228f1c end -/

end

end Statlib.Imported

