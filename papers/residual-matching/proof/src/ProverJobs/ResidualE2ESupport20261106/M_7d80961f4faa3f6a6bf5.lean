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
theorem statopia_math_node_4096280673_29405c81 : ∀ (m n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAcov : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      ∫ ω, A ω i j * A ω k l ∂μ = if (i, j) = (k, l) then 1 / (m : ℝ) else 0)
    (hAprodint : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      MeasureTheory.Integrable (fun ω => A ω i j * A ω k l) μ)
    (v w : Fin (m + n) → ℝ),
    (∫ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
        (v a : ℂ) * ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
            (Matrix.map (A ω) Complex.ofReal)
            (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
            (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
            finSumFinEquiv.symm finSumFinEquiv.symm) a b * (w b : ℂ)‖ ^ 2 ∂μ)
      = (1 / (m : ℝ)) * ∑ i, ∑ j,
          (v (finSumFinEquiv (Sum.inl i)) * w (finSumFinEquiv (Sum.inr j)) +
            v (finSumFinEquiv (Sum.inr j)) * w (finSumFinEquiv (Sum.inl i))) ^ 2 := by
  /- @proof-region region.target-node.session.454188c143179843 begin -/
  intro m n Ω _ μ A hAcov hAprodint v w
  have hcomplex : ∀ ω : Ω, (∑ a : Fin (m + n), ∑ b : Fin (m + n),
      (v a : ℂ) * ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
          (Matrix.map (A ω) Complex.ofReal)
          (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
          (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm) a b * (w b : ℂ))
      = ((∑ i : Fin m, ∑ j : Fin n,
          (v (finSumFinEquiv (Sum.inl i)) * w (finSumFinEquiv (Sum.inr j)) +
            v (finSumFinEquiv (Sum.inr j)) * w (finSumFinEquiv (Sum.inl i))) * A ω i j : ℝ) : ℂ) := by
    intro ω
    have hD : ∀ (s t : Fin m ⊕ Fin n),
        ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (Matrix.map (A ω) Complex.ofReal) (Matrix.transpose (Matrix.map (A ω) Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) (finSumFinEquiv s) (finSumFinEquiv t)
        = (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (Matrix.map (A ω) Complex.ofReal) (Matrix.transpose (Matrix.map (A ω) Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ)) s t := by
      intro s t
      simp [Matrix.submatrix_apply]
    have hreindex : ∀ g : Fin (m + n) → ℂ, (∑ a, g a) = ∑ s : Fin m ⊕ Fin n, g (finSumFinEquiv s) := by
      intro g
      exact (Fintype.sum_equiv finSumFinEquiv (fun s => g (finSumFinEquiv s)) g (fun s => rfl)).symm
    simp only [hreindex, hD]
    simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
    simp [Matrix.fromBlocks]
    have h1 : (∑ x : Fin n, ∑ x_1 : Fin m, (↑(v (Fin.natAdd m x)) : ℂ) * ↑(A ω x_1 x) * ↑(w (Fin.castAdd n x_1)))
        = ∑ i : Fin m, ∑ j : Fin n, (↑(v (Fin.natAdd m j)) : ℂ) * ↑(A ω i j) * ↑(w (Fin.castAdd n i)) := Finset.sum_comm
    rw [h1]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnorm : ∀ ω : Ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
      (v a : ℂ) * ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
          (Matrix.map (A ω) Complex.ofReal)
          (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
          (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm) a b * (w b : ℂ)‖ ^ 2
      = (∑ i : Fin m, ∑ j : Fin n,
          (v (finSumFinEquiv (Sum.inl i)) * w (finSumFinEquiv (Sum.inr j)) +
            v (finSumFinEquiv (Sum.inr j)) * w (finSumFinEquiv (Sum.inl i))) * A ω i j) ^ 2 := by
    intro ω
    rw [hcomplex ω]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
  have hInt : (∫ ω, (∑ i : Fin m, ∑ j : Fin n,
          (v (finSumFinEquiv (Sum.inl i)) * w (finSumFinEquiv (Sum.inr j)) +
            v (finSumFinEquiv (Sum.inr j)) * w (finSumFinEquiv (Sum.inl i))) * A ω i j) ^ 2 ∂μ)
      = (1 / (m : ℝ)) * ∑ i, ∑ j,
          (v (finSumFinEquiv (Sum.inl i)) * w (finSumFinEquiv (Sum.inr j)) +
            v (finSumFinEquiv (Sum.inr j)) * w (finSumFinEquiv (Sum.inl i))) ^ 2 := by
    let c : Fin m → Fin n → ℝ := fun i j =>
      v (finSumFinEquiv (Sum.inl i)) * w (finSumFinEquiv (Sum.inr j)) +
        v (finSumFinEquiv (Sum.inr j)) * w (finSumFinEquiv (Sum.inl i))
    change (∫ ω, (∑ i, ∑ j, c i j * A ω i j) ^ 2 ∂μ) = (1 / (m : ℝ)) * ∑ i, ∑ j, (c i j) ^ 2
    have hsq : ∀ ω : Ω, (∑ i, ∑ j, c i j * A ω i j) ^ 2
        = ∑ r : (Fin m × Fin n) × (Fin m × Fin n),
            (c r.1.1 r.1.2 * c r.2.1 r.2.2) * (A ω r.1.1 r.1.2 * A ω r.2.1 r.2.2) := by
      intro ω
      have hp : (∑ i : Fin m, ∑ j : Fin n, c i j * A ω i j)
          = ∑ p : Fin m × Fin n, c p.1 p.2 * A ω p.1 p.2 :=
        (Fintype.sum_prod_type (fun p : Fin m × Fin n => c p.1 p.2 * A ω p.1 p.2)).symm
      have h2 : (∑ p : Fin m × Fin n, c p.1 p.2 * A ω p.1 p.2) ^ 2
          = ∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n,
              (c p.1 p.2 * A ω p.1 p.2) * (c q.1 q.2 * A ω q.1 q.2) := by
        rw [sq, Finset.sum_mul_sum]
      have h3 : (∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n,
              (c p.1 p.2 * A ω p.1 p.2) * (c q.1 q.2 * A ω q.1 q.2))
          = ∑ r : (Fin m × Fin n) × (Fin m × Fin n),
              (c r.1.1 r.1.2 * A ω r.1.1 r.1.2) * (c r.2.1 r.2.2 * A ω r.2.1 r.2.2) :=
        (Fintype.sum_prod_type (fun r : (Fin m × Fin n) × (Fin m × Fin n) =>
          (c r.1.1 r.1.2 * A ω r.1.1 r.1.2) * (c r.2.1 r.2.2 * A ω r.2.1 r.2.2))).symm
      rw [hp, h2, h3]
      exact Finset.sum_congr rfl (fun r _ => by ring)
    have hstep : (∫ ω, ∑ r : (Fin m × Fin n) × (Fin m × Fin n),
            (c r.1.1 r.1.2 * c r.2.1 r.2.2) * (A ω r.1.1 r.1.2 * A ω r.2.1 r.2.2) ∂μ)
        = ∑ r : (Fin m × Fin n) × (Fin m × Fin n),
            (c r.1.1 r.1.2 * c r.2.1 r.2.2) *
              (if (r.1.1, r.1.2) = (r.2.1, r.2.2) then 1 / (m : ℝ) else 0) := by
      have hint : ∀ r : (Fin m × Fin n) × (Fin m × Fin n),
          Integrable (fun ω => (c r.1.1 r.1.2 * c r.2.1 r.2.2) * (A ω r.1.1 r.1.2 * A ω r.2.1 r.2.2)) μ :=
        fun r => (hAprodint r.1.1 r.1.2 r.2.1 r.2.2).const_mul (c r.1.1 r.1.2 * c r.2.1 r.2.2)
      rw [MeasureTheory.integral_finset_sum (Finset.univ)]
      · apply Finset.sum_congr rfl
        intro r _
        rw [integral_const_mul_of_integrable (hAprodint r.1.1 r.1.2 r.2.1 r.2.2)]
        rw [hAcov r.1.1 r.1.2 r.2.1 r.2.2]
      · intro r _
        exact hint r
    have hdiag : (∑ r : (Fin m × Fin n) × (Fin m × Fin n),
            (c r.1.1 r.1.2 * c r.2.1 r.2.2) *
              (if (r.1.1, r.1.2) = (r.2.1, r.2.2) then 1 / (m : ℝ) else 0))
        = (1 / (m : ℝ)) * ∑ i : Fin m, ∑ j : Fin n, (c i j) ^ 2 := by
      have hclean : (∑ r : (Fin m × Fin n) × (Fin m × Fin n),
              (c r.1.1 r.1.2 * c r.2.1 r.2.2) *
                (if (r.1.1, r.1.2) = (r.2.1, r.2.2) then 1 / (m : ℝ) else 0))
          = ∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n,
              (c p.1 p.2 * c q.1 q.2) * (if p = q then 1 / (m : ℝ) else 0) :=
        Fintype.sum_prod_type (fun r : (Fin m × Fin n) × (Fin m × Fin n) =>
          (c r.1.1 r.1.2 * c r.2.1 r.2.2) * (if r.1 = r.2 then 1 / (m : ℝ) else 0))
      rw [hclean]
      have hinner : ∀ p : Fin m × Fin n,
          (∑ q : Fin m × Fin n, (c p.1 p.2 * c q.1 q.2) * (if p = q then 1 / (m : ℝ) else 0))
            = (c p.1 p.2 * c p.1 p.2) * (1 / (m : ℝ)) := by
        intro p
        rw [Finset.sum_eq_single p]
        · simp
        · intro q _ hq
          simp only [if_neg (Ne.symm hq), mul_zero]
        · intro hp
          exact absurd (Finset.mem_univ p) hp
      have hs1 : (∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n,
              (c p.1 p.2 * c q.1 q.2) * (if p = q then 1 / (m : ℝ) else 0))
          = ∑ p : Fin m × Fin n, (c p.1 p.2 * c p.1 p.2) * (1 / (m : ℝ)) :=
        Finset.sum_congr rfl (fun p _ => hinner p)
      rw [hs1]
      have hs4 : (∑ p : Fin m × Fin n, (c p.1 p.2 * c p.1 p.2) * (1 / (m : ℝ)))
          = (1 / (m : ℝ)) * ∑ p : Fin m × Fin n, (c p.1 p.2 * c p.1 p.2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      rw [hs4]
      have hs2 : (∑ p : Fin m × Fin n, c p.1 p.2 * c p.1 p.2)
          = ∑ p : Fin m × Fin n, (c p.1 p.2) ^ 2 :=
        Finset.sum_congr rfl (fun p _ => by ring)
      rw [hs2]
      have hs3 : (∑ p : Fin m × Fin n, (c p.1 p.2) ^ 2) = ∑ i : Fin m, ∑ j : Fin n, (c i j) ^ 2 :=
        Fintype.sum_prod_type (fun p : Fin m × Fin n => (c p.1 p.2) ^ 2)
      rw [hs3]
    simp only [hsq]
    rw [hstep]
    rw [hdiag]
  simp only [hnorm]
  exact hInt
  /- @proof-region region.target-node.session.454188c143179843 end -/

end Statlib.Imported

