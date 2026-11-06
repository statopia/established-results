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
theorem statopia_math_node_2263768880_be0f4d53 : ∀ (m n r D : ℕ)
    (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (b : Fin D → Matrix (Fin m) (Fin n) ℝ)
    (hb_orth : ∀ (p q : Fin D), frobInner (b p) (b q) = (if p = q then (1 : ℝ) else 0))
    (hb_mem : ∀ (p : Fin D), MemTangentRect U0 V0 (b p)),
    D ≤ r * (m + n) ∧ D ≤ m * n := by
  /- @proof-region region.target-node.session.d018d8794ac91370 begin -/
  intro m n r D U0 V0 b hb_orth hb_mem
  have hfrob_add : ∀ (A B W : Matrix (Fin m) (Fin n) ℝ),
      frobInner (A + B) W = frobInner A W + frobInner B W := by
    intro A B W
    simp [frobInner, add_mul, Finset.sum_add_distrib]
  have hfrob_smul : ∀ (c : ℝ) (A W : Matrix (Fin m) (Fin n) ℝ),
      frobInner (c • A) W = c * frobInner A W := by
    intro c A W
    simp [frobInner, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hsum : ∀ (g : Fin D → ℝ) (W : Matrix (Fin m) (Fin n) ℝ),
      frobInner (∑ p, g p • b p) W = ∑ p, g p * frobInner (b p) W := by
    intro g W
    have key : ∀ s : Finset (Fin D),
        frobInner (∑ p ∈ s, g p • b p) W = ∑ p ∈ s, g p * frobInner (b p) W := by
      intro s
      induction s using Finset.induction with
      | empty => simp [frobInner]
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, hfrob_add, hfrob_smul, ih]
    simpa using key Finset.univ
  have hcollapse : ∀ (f : Fin D → ℝ) (q : Fin D),
      (∑ p : Fin D, (if p = q then f p else 0)) = f q := by
    intro f q
    have key : ∀ s : Finset (Fin D),
        (∑ p ∈ s, (if p = q then f p else 0)) = if q ∈ s then f q else 0 := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, ih]
          by_cases h : a = q
          · rw [← h]
            simp [ha]
          · have h' : ¬ q = a := fun hq => h hq.symm
            simp [h, h']
    simpa using key Finset.univ
  have hlin : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg q
    have h2 : ∀ p : Fin D, g p * frobInner (b p) (b q) = if p = q then g p else 0 := by
      intro p
      rw [hb_orth p q]
      split_ifs with h
      · simp
      · simp
    have h1 : (∑ p, g p * frobInner (b p) (b q)) = g q := by
      rw [show (∑ p, g p * frobInner (b p) (b q)) = ∑ p, (if p = q then g p else 0) from
        Finset.sum_congr rfl (fun p _ => h2 p)]
      exact hcollapse g q
    have h3 : frobInner (∑ p, g p • b p) (b q) = ∑ p, g p * frobInner (b p) (b q) :=
      hsum g (b q)
    have h4 : frobInner (0 : Matrix (Fin m) (Fin n) ℝ) (b q) = 0 := by
      simpa using hfrob_smul 0 (0 : Matrix (Fin m) (Fin n) ℝ) (b q)
    have h5 : (∑ p, g p * frobInner (b p) (b q)) = 0 := by
      rw [← h3, hg, h4]
    rw [← h1]
    exact h5
  have hfin_mn : Module.finrank ℝ (Matrix (Fin m) (Fin n) ℝ) = m * n := by
    rw [Module.finrank_eq_card_basis (Matrix.stdBasis ℝ (Fin m) (Fin n))]
    simp [Fintype.card_prod]
  have hI : D ≤ m * n := by
    have h : Fintype.card (Fin D) ≤ Module.finrank ℝ (Matrix (Fin m) (Fin n) ℝ) :=
      hlin.fintype_card_le_finrank
    rw [hfin_mn] at h
    simpa using h
  have hfin_nr : Module.finrank ℝ (Matrix (Fin n) (Fin r) ℝ) = n * r := by
    rw [Module.finrank_eq_card_basis (Matrix.stdBasis ℝ (Fin n) (Fin r))]
    simp [Fintype.card_prod]
  have hfin_mr : Module.finrank ℝ (Matrix (Fin m) (Fin r) ℝ) = m * r := by
    rw [Module.finrank_eq_card_basis (Matrix.stdBasis ℝ (Fin m) (Fin r))]
    simp [Fintype.card_prod]
  have hfin_prod : Module.finrank ℝ (Matrix (Fin n) (Fin r) ℝ × Matrix (Fin m) (Fin r) ℝ)
      = n * r + m * r := by
    rw [Module.finrank_prod, hfin_nr, hfin_mr]
  have hH : D ≤ r * (m + n) := by
    classical
    have hb_mem' : ∀ p : Fin D, ∃ A : Matrix (Fin n) (Fin r) ℝ,
        ∃ B : Matrix (Fin m) (Fin r) ℝ, b p = U0 * A.transpose + B * V0.transpose := hb_mem
    choose A B hAB using hb_mem'
    let φ : (Matrix (Fin n) (Fin r) ℝ × Matrix (Fin m) (Fin r) ℝ) →ₗ[ℝ]
        Matrix (Fin m) (Fin n) ℝ :=
      { toFun := fun x => U0 * x.1.transpose + x.2 * V0.transpose
        map_add' := by
          intro x y
          simp only [Prod.fst_add, Prod.snd_add, Matrix.transpose_add, Matrix.mul_add,
            Matrix.add_mul]
          abel
        map_smul' := by
          intro c x
          simp [Prod.smul_fst, Prod.smul_snd, Matrix.transpose_smul, Matrix.mul_smul,
            Matrix.smul_mul, smul_add] }
    have hφp : ∀ p : Fin D, φ (A p, B p) = b p := by
      intro p
      exact (hAB p).symm
    have hc_lin : LinearIndependent ℝ (fun p : Fin D => (A p, B p)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg q
      have hsumφ : φ (∑ p, g p • (A p, B p)) = ∑ p, g p • b p := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun p _ => by rw [map_smul, hφp p]
      have hg0 : ∑ p, g p • b p = 0 := by
        rw [← hsumφ, hg, map_zero]
      exact (Fintype.linearIndependent_iff.mp hlin) g hg0 q
    have hle : D ≤ Module.finrank ℝ (Matrix (Fin n) (Fin r) ℝ × Matrix (Fin m) (Fin r) ℝ) := by
      have h := hc_lin.fintype_card_le_finrank
      simpa using h
    rw [hfin_prod] at hle
    calc D ≤ n * r + m * r := hle
      _ = r * (m + n) := by ring
  exact ⟨hH, hI⟩
  /- @proof-region region.target-node.session.d018d8794ac91370 end -/

end

end Statlib.Imported

