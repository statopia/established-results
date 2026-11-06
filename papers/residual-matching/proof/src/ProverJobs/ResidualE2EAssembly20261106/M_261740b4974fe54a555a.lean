import Statlib.HighDim.MatrixAnalysis.FrobeniusNormSvdRelation
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48
import ProverJobs.ResidualE2EAssembly20261106.M_8e241f0ee96b21c5ad51

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
theorem statopia_math_node_1316590956_d1ca58c8 : ∀ (m n r : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hr : 1 ≤ r)
    (X X0 : Matrix (Fin m) (Fin r) ℝ) (Y Y0 : Matrix (Fin n) (Fin r) ℝ)
    (hbal : Matrix.transpose X * X = Matrix.transpose Y * Y)
    (hbal0 : Matrix.transpose X0 * X0 = Matrix.transpose Y0 * Y0),
    (let F : Matrix (Fin (m + n)) (Fin r) ℝ := Fin.append (fun a => X a) (fun b => Y b);
     let F0 : Matrix (Fin (m + n)) (Fin r) ℝ := Fin.append (fun a => X0 a) (fun b => Y0 b);
     frobSq (F * Matrix.transpose F - F0 * Matrix.transpose F0) ≤
       8 * frobSq (X * Matrix.transpose Y - X0 * Matrix.transpose Y0)) := by
  /- @proof-region region.target-node.session.26fa824f9472b723 begin -/
  intro m n r hm hn hr X X0 Y Y0 hbalX hbalX0 F F0
  have hF : F = Fin.append (fun a => X a) (fun b => Y b) := rfl
  have hF0 : F0 = Fin.append (fun a => X0 a) (fun b => Y0 b) := rfl
  have hFrobTrace : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ),
      frobSq A = (Matrix.transpose A * A).trace := by
    intro a b A
    have h := (Statlib.HighDim.MatrixAnalysis.frobenius_norm_svd_relation A).2.2
    show (∑ i, ∑ j, A i j ^ 2) = (Matrix.transpose A * A).trace
    exact h.symm
  have hcyc : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin a) ℝ),
      (A * B).trace = (B * A).trace := by
    intro a b A B
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [mul_comm]
  have hReorder : ∀ {a b c d : ℕ} (F : Fin a → Fin b → Fin c → Fin d → ℝ),
      (∑ i, ∑ j, ∑ t, ∑ s, F i j t s) = (∑ t, ∑ s, ∑ i, ∑ j, F i j t s) := by
    intro a b c d F
    calc (∑ i, ∑ j, ∑ t, ∑ s, F i j t s)
        = ∑ i, ∑ t, ∑ j, ∑ s, F i j t s := by
            apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
      _ = ∑ t, ∑ i, ∑ j, ∑ s, F i j t s := by
            rw [Finset.sum_comm]
      _ = ∑ t, ∑ i, ∑ s, ∑ j, F i j t s := by
            apply Finset.sum_congr rfl; intro t _
            apply Finset.sum_congr rfl; intro i _
            rw [Finset.sum_comm]
      _ = ∑ t, ∑ s, ∑ i, ∑ j, F i j t s := by
            apply Finset.sum_congr rfl; intro t _; rw [Finset.sum_comm]
  have hPairing : ∀ {a b c d : ℕ}
      (A : Matrix (Fin a) (Fin c) ℝ) (B : Matrix (Fin b) (Fin c) ℝ)
      (C : Matrix (Fin a) (Fin d) ℝ) (D : Matrix (Fin b) (Fin d) ℝ),
      (∑ i, ∑ j, (A * Matrix.transpose B) i j * (C * Matrix.transpose D) i j)
        = (∑ t, ∑ s, (Matrix.transpose A * C) t s * (Matrix.transpose B * D) t s) := by
    intro a b c d A B C D
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul_sum]
    rw [← hReorder (F := fun i j t s => (A i t * C i s) * (B j t * D j s))]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro s _
    ring
  have hFF : Matrix.transpose F * F
      = Matrix.transpose X * X + Matrix.transpose Y * Y := by
    ext s t
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply]
    rw [Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; simp only [hF, Fin.append_left]
    · apply Finset.sum_congr rfl; intro i _; simp only [hF, Fin.append_right]
  have hF0F0 : Matrix.transpose F0 * F0
      = Matrix.transpose X0 * X0 + Matrix.transpose Y0 * Y0 := by
    ext s t
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply]
    rw [Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; simp only [hF0, Fin.append_left]
    · apply Finset.sum_congr rfl; intro i _; simp only [hF0, Fin.append_right]
  have hFF0 : Matrix.transpose F * F0
      = Matrix.transpose X * X0 + Matrix.transpose Y * Y0 := by
    ext s t
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply]
    rw [Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; simp only [hF, hF0, Fin.append_left]
    · apply Finset.sum_congr rfl; intro i _; simp only [hF, hF0, Fin.append_right]
  have hSelf : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ),
      frobSq A = ∑ i, ∑ j, A i j * A i j := by
    intro a b A
    simp only [frobSq]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hSqDiff : ∀ {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℝ),
      frobSq (A - B) = frobSq A + frobSq B - 2 * (∑ i, ∑ j, A i j * B i j) := by
    intro a b A B
    have key : ∀ (i : Fin a) (j : Fin b),
        (A i j - B i j) ^ 2 = A i j ^ 2 + B i j ^ 2 - 2 * (A i j * B i j) := by
      intro i j; ring
    simp only [frobSq, Matrix.sub_apply, key, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum]
  have hGram : ∀ {a c : ℕ} (M : Matrix (Fin a) (Fin c) ℝ),
      frobSq (M * Matrix.transpose M) = frobSq (Matrix.transpose M * M) := by
    intro a c M
    rw [hSelf (A := M * Matrix.transpose M)]
    rw [hPairing (A := M) (B := M) (C := M) (D := M)]
    rw [hSelf (A := Matrix.transpose M * M)]
  have hSqAdd : ∀ {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℝ),
      frobSq (A + B) = frobSq A + frobSq B + 2 * (∑ i, ∑ j, A i j * B i j) := by
    intro a b A B
    have key : ∀ (i : Fin a) (j : Fin b),
        (A i j + B i j) ^ 2 = A i j ^ 2 + B i j ^ 2 + 2 * (A i j * B i j) := by
      intro i j; ring
    simp only [frobSq, Matrix.add_apply, key, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum]
  have hAddSelf : ∀ {a b : ℕ} (S : Matrix (Fin a) (Fin b) ℝ),
      frobSq (S + S) = 4 * frobSq S := by
    intro a b S
    simp only [frobSq, Matrix.add_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hCrossL : (∑ i, ∑ j,
        (F * Matrix.transpose F) i j * (F0 * Matrix.transpose F0) i j)
      = frobSq (Matrix.transpose F * F0) := by
    rw [hSelf (A := Matrix.transpose F * F0)]
    exact hPairing (A := F) (B := F) (C := F0) (D := F0)
  have hLHS : frobSq (F * Matrix.transpose F - F0 * Matrix.transpose F0)
      = 4 * frobSq (Matrix.transpose X * X) + 4 * frobSq (Matrix.transpose X0 * X0)
        - 2 * frobSq (Matrix.transpose X * X0 + Matrix.transpose Y * Y0) := by
    rw [hSqDiff (A := F * Matrix.transpose F) (B := F0 * Matrix.transpose F0)]
    rw [hCrossL, hFF0]
    rw [hGram (M := F), hGram (M := F0)]
    rw [hFF, hF0F0]
    rw [← hbalX, ← hbalX0]
    rw [hAddSelf (S := Matrix.transpose X * X), hAddSelf (S := Matrix.transpose X0 * X0)]
  have hXY : frobSq (X * Matrix.transpose Y) = frobSq (Matrix.transpose X * X) := by
    rw [hSelf (A := X * Matrix.transpose Y)]
    rw [hPairing (A := X) (B := Y) (C := X) (D := Y)]
    rw [← hbalX]
    rw [← hSelf (A := Matrix.transpose X * X)]
  have hX0Y0 : frobSq (X0 * Matrix.transpose Y0) = frobSq (Matrix.transpose X0 * X0) := by
    rw [hSelf (A := X0 * Matrix.transpose Y0)]
    rw [hPairing (A := X0) (B := Y0) (C := X0) (D := Y0)]
    rw [← hbalX0]
    rw [← hSelf (A := Matrix.transpose X0 * X0)]
  have hCrossR : (∑ i, ∑ j,
        (X * Matrix.transpose Y) i j * (X0 * Matrix.transpose Y0) i j)
      = (∑ t, ∑ s, (Matrix.transpose X * X0) t s * (Matrix.transpose Y * Y0) t s) :=
    hPairing (A := X) (B := Y) (C := X0) (D := Y0)
  have hRHS : frobSq (X * Matrix.transpose Y - X0 * Matrix.transpose Y0)
      = frobSq (Matrix.transpose X * X) + frobSq (Matrix.transpose X0 * X0)
        - 2 * (∑ t, ∑ s,
            (Matrix.transpose X * X0) t s * (Matrix.transpose Y * Y0) t s) := by
    rw [hSqDiff (A := X * Matrix.transpose Y) (B := X0 * Matrix.transpose Y0)]
    rw [hXY, hX0Y0, hCrossR]
  have hFrobNonneg : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ), 0 ≤ frobSq A := by
    intro a b A
    simp only [frobSq]
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    positivity
  have hPSR : frobSq (Matrix.transpose X * X0 + Matrix.transpose Y * Y0)
      = frobSq (Matrix.transpose X * X0) + frobSq (Matrix.transpose Y * Y0)
        + 2 * (∑ t, ∑ s,
            (Matrix.transpose X * X0) t s * (Matrix.transpose Y * Y0) t s) :=
    hSqAdd (A := Matrix.transpose X * X0) (B := Matrix.transpose Y * Y0)
  have h_c : 2 * (∑ t, ∑ s,
      (Matrix.transpose X * X0) t s * (Matrix.transpose Y * Y0) t s)
      ≤ frobSq (Matrix.transpose X * X0) + frobSq (Matrix.transpose Y * Y0) := by
    have h := hFrobNonneg (Matrix.transpose X * X0 - Matrix.transpose Y * Y0)
    rw [hSqDiff (A := Matrix.transpose X * X0) (B := Matrix.transpose Y * Y0)] at h
    linarith
  have hInv : ∀ {a c : ℕ} (A B : Matrix (Fin a) (Fin c) ℝ),
      frobSq (Matrix.transpose A * B)
        = ∑ i, ∑ j, (A * Matrix.transpose A) i j * (B * Matrix.transpose B) i j := by
    intro a c A B
    rw [hSelf (A := Matrix.transpose A * B)]
    exact (hPairing (A := A) (B := A) (C := B) (D := B)).symm
  have hCSsq : ∀ {a b : ℕ} (U V : Matrix (Fin a) (Fin b) ℝ),
      (∑ i, ∑ j, U i j * V i j) ^ 2 ≤ frobSq U * frobSq V := by
    intro a b U V
    have hfl : (∑ p : Fin a × Fin b, U p.1 p.2 * V p.1 p.2)
        = ∑ i, ∑ j, U i j * V i j :=
      Fintype.sum_prod_type (f := fun p : Fin a × Fin b => U p.1 p.2 * V p.1 p.2)
    have hflU : (∑ p : Fin a × Fin b, U p.1 p.2 ^ 2) = frobSq U := by
      simp only [frobSq]
      exact Fintype.sum_prod_type (f := fun p : Fin a × Fin b => U p.1 p.2 ^ 2)
    have hflV : (∑ p : Fin a × Fin b, V p.1 p.2 ^ 2) = frobSq V := by
      simp only [frobSq]
      exact Fintype.sum_prod_type (f := fun p : Fin a × Fin b => V p.1 p.2 ^ 2)
    rw [← hfl, ← hflU, ← hflV]
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset (Fin a × Fin b))
      (r := fun p => U p.1 p.2 * V p.1 p.2)
      (f := fun p => U p.1 p.2 ^ 2) (g := fun p => V p.1 p.2 ^ 2)
      (fun p _ => sq_nonneg _) (fun p _ => sq_nonneg _) (fun p _ => by ring)
  have hp2 : frobSq (Matrix.transpose X * X0) ^ 2
      ≤ frobSq (Matrix.transpose X * X) * frobSq (Matrix.transpose X0 * X0) := by
    rw [hInv (A := X) (B := X0)]
    have h := hCSsq (X * Matrix.transpose X) (X0 * Matrix.transpose X0)
    rw [hGram (M := X), hGram (M := X0)] at h
    exact h
  have hq2 : frobSq (Matrix.transpose Y * Y0) ^ 2
      ≤ frobSq (Matrix.transpose X * X) * frobSq (Matrix.transpose X0 * X0) := by
    rw [hInv (A := Y) (B := Y0)]
    have h := hCSsq (Y * Matrix.transpose Y) (Y0 * Matrix.transpose Y0)
    rw [hGram (M := Y), hGram (M := Y0)] at h
    rw [← hbalX, ← hbalX0] at h
    exact h
  have h_pq : frobSq (Matrix.transpose X * X0) + frobSq (Matrix.transpose Y * Y0)
      ≤ frobSq (Matrix.transpose X * X) + frobSq (Matrix.transpose X0 * X0) := by
    have hp0 : 0 ≤ frobSq (Matrix.transpose X * X0) := hFrobNonneg (Matrix.transpose X * X0)
    have hq0 : 0 ≤ frobSq (Matrix.transpose Y * Y0) := hFrobNonneg (Matrix.transpose Y * Y0)
    have hA0 : 0 ≤ frobSq (Matrix.transpose X * X) := hFrobNonneg (Matrix.transpose X * X)
    have hB0 : 0 ≤ frobSq (Matrix.transpose X0 * X0) := hFrobNonneg (Matrix.transpose X0 * X0)
    have hsq : (frobSq (Matrix.transpose X * X0) + frobSq (Matrix.transpose Y * Y0)) ^ 2
        ≤ (frobSq (Matrix.transpose X * X) + frobSq (Matrix.transpose X0 * X0)) ^ 2 := by
      nlinarith [hp2, hq2,
        sq_nonneg (frobSq (Matrix.transpose X * X0) - frobSq (Matrix.transpose Y * Y0)),
        sq_nonneg (frobSq (Matrix.transpose X * X) - frobSq (Matrix.transpose X0 * X0))]
    have hpq0 : 0 ≤ frobSq (Matrix.transpose X * X0) + frobSq (Matrix.transpose Y * Y0) := by
      linarith
    have hab0 : 0 ≤ frobSq (Matrix.transpose X * X) + frobSq (Matrix.transpose X0 * X0) := by
      linarith
    have h := (sq_le_sq).mp hsq
    rw [abs_of_nonneg hpq0, abs_of_nonneg hab0] at h
    exact h
  rw [hLHS, hRHS, hPSR]
  linarith [h_c, h_pq]
  /- @proof-region region.target-node.session.26fa824f9472b723 end -/

end

end Statlib.Imported

