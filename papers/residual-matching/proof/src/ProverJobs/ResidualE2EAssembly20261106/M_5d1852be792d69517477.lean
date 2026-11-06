import Statlib.HighDim.MatrixAnalysis.KyFan
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48
import ProverJobs.ResidualE2EAssembly20261106.M_261740b4974fe54a555a
import ProverJobs.ResidualE2EAssembly20261106.M_6ab257f44c787db196fd
import ProverJobs.ResidualE2EAssembly20261106.M_5cdafcc3cf895c0de6cc
import ProverJobs.ResidualE2EAssembly20261106.M_84b6b31a8725c0394946

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
theorem statopia_math_node_3282353922_3efb933f : ∀ (m n r : ℕ) (hr : 1 ≤ r) (hmn : r ≤ m + n)
    (f : ℝ) (hf : 0 ≤ f)
    (X X0 : Matrix (Fin m) (Fin r) ℝ) (Y Y0 : Matrix (Fin n) (Fin r) ℝ),
    (let F : Matrix (Fin (m + n)) (Fin r) ℝ := Fin.append (fun a => X a) (fun b => Y b);
     let F0 : Matrix (Fin (m + n)) (Fin r) ℝ := Fin.append (fun a => X0 a) (fun b => Y0 b);
     let sr : ℝ := SMin (fun i : Fin r =>
       Statlib.HighDim.MatrixAnalysis.singularValues F0
         (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i));
     0 < sr →
     frobSq (F * Matrix.transpose F - F0 * Matrix.transpose F0) ≤ 8 * f ^ 2 →
     ∃ O : Matrix (Fin r) (Fin r) ℝ,
       Matrix.transpose O * O = 1 ∧
         frobSq (F * O - F0) ≤ 4 * f ^ 2 / ((Real.sqrt 2 - 1) * sr ^ 2) ∧
         frobSq (X * O - X0) + frobSq (Y * O - Y0) ≤
           4 * f ^ 2 / ((Real.sqrt 2 - 1) * sr ^ 2) ∧
         (∀ (sig0 : Fin r → ℝ), sr ^ 2 = 2 * SMin sig0 →
           frobSq (X * O - X0) + frobSq (Y * O - Y0) ≤
             2 * f ^ 2 / ((Real.sqrt 2 - 1) * SMin sig0))) := by
  /- @proof-region region.target-node.session.1ed1da9d52dd7729 begin -/
  intro m n r hr hmn f hf X X0 Y Y0 F F0 sig hsigma hgram
  have hr0 : 0 < r := by omega
  have hsigpos : 0 < sig := hsigma
  have hfsq_nonneg : ∀ {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ), 0 ≤ frobSq A := by
    intro p q A
    unfold frobSq
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  obtain ⟨Rm, hRm_orth, hRm_min⟩ :=
    statopia_math_node_897344607_f43704b9 (m + n) r hr0 F F0
  have hRR : Rm * Matrix.transpose Rm = 1 :=
    Statlib.HighDim.MatrixAnalysis.orth_square_mul_transpose Rm hRm_orth
  have hExt := ext_model_2 (m + n) r F F0 hr0 hmn hsigpos
  rw [← hRm_min] at hExt
  have hfsq : frobSq (F - F0 * Rm) = frob (F - F0 * Rm) ^ 2 := by
    unfold frob
    rw [Real.sq_sqrt (hfsq_nonneg _)]
  have hmain1 : frobSq (F - F0 * Rm) ≤
      (2 * (Real.sqrt 2 - 1) * SMin (fun i : Fin r =>
        Statlib.HighDim.MatrixAnalysis.singularValues F0
          (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i)) ^ 2)⁻¹ *
        frobSq (F * Matrix.transpose F - F0 * Matrix.transpose F0) := by
    rw [hfsq]
    exact hExt
  have hSMin : SMin (fun i : Fin r =>
      Statlib.HighDim.MatrixAnalysis.singularValues F0
        (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i)) = sig := rfl
  have hkey : (2 * (Real.sqrt 2 - 1) * sig ^ 2)⁻¹ * (8 * f ^ 2) =
      4 * f ^ 2 / ((Real.sqrt 2 - 1) * sig ^ 2) := by
    have h1 : (Real.sqrt 2 - 1) ≠ 0 := by linarith [Real.one_lt_sqrt_two]
    have h2 : sig ≠ 0 := ne_of_gt hsigpos
    field_simp
    ring
  have hKnn : (0 : ℝ) ≤ (2 * (Real.sqrt 2 - 1) * sig ^ 2)⁻¹ := by
    have h1 : (0 : ℝ) < Real.sqrt 2 - 1 := by linarith [Real.one_lt_sqrt_two]
    have h2 : (0 : ℝ) < sig ^ 2 := by nlinarith [hsigpos]
    exact inv_nonneg.mpr (by nlinarith)
  have hbound_sq : frobSq (F - F0 * Rm) ≤ 4 * f ^ 2 / ((Real.sqrt 2 - 1) * sig ^ 2) := by
    have hstep : (2 * (Real.sqrt 2 - 1) * SMin (fun i : Fin r =>
        Statlib.HighDim.MatrixAnalysis.singularValues F0
          (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i)) ^ 2)⁻¹ *
        frobSq (F * Matrix.transpose F - F0 * Matrix.transpose F0) ≤
      (2 * (Real.sqrt 2 - 1) * SMin (fun i : Fin r =>
        Statlib.HighDim.MatrixAnalysis.singularValues F0
          (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i)) ^ 2)⁻¹ * (8 * f ^ 2) := by
      rw [hSMin]
      exact mul_le_mul_of_nonneg_left hgram hKnn
    have hfin : (2 * (Real.sqrt 2 - 1) * SMin (fun i : Fin r =>
        Statlib.HighDim.MatrixAnalysis.singularValues F0
          (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i)) ^ 2)⁻¹ * (8 * f ^ 2) ≤
        4 * f ^ 2 / ((Real.sqrt 2 - 1) * sig ^ 2) := by
      rw [hSMin, hkey]
    exact le_trans hmain1 (le_trans hstep hfin)
  have frobSq_mul_transpose : ∀ {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
      (M : Matrix (Fin q) (Fin q) ℝ),
      M * Matrix.transpose M = 1 → frobSq (A * M) = frobSq A := by
    intro p q A M hM
    unfold frobSq
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_apply]
    calc ∑ j : Fin q, (∑ k : Fin q, A i k * M k j) ^ 2
        = ∑ j : Fin q, ∑ k : Fin q, ∑ l : Fin q,
            (A i k * M k j) * (A i l * M l j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [sq, Finset.sum_mul_sum]
      _ = ∑ k : Fin q, ∑ l : Fin q, ∑ j : Fin q,
            (A i k * M k j) * (A i l * M l j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ k : Fin q, ∑ l : Fin q,
            (A i k * A i l) * (M * Matrix.transpose M) k l := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [Matrix.mul_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.transpose_apply]
          ring
      _ = ∑ k : Fin q, ∑ l : Fin q,
            (A i k * A i l) * (if k = l then (1 : ℝ) else 0) := by
          rw [hM]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [Matrix.one_apply]
      _ = ∑ k : Fin q, A i k ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hzero : ∀ l ∈ (Finset.univ : Finset (Fin q)), l ≠ k →
              (A i k * A i l) * (if k = l then (1 : ℝ) else 0) = 0 := by
            intro l _ hlk
            rw [if_neg (Ne.symm hlk)]
            ring
          have hmem : k ∉ (Finset.univ : Finset (Fin q)) →
              (A i k * A i k) * (if k = k then (1 : ℝ) else 0) = 0 := by
            intro hk
            exact absurd (Finset.mem_univ k) hk
          rw [Finset.sum_eq_single k hzero hmem]
          rw [if_pos rfl]
          ring
  have hinv : frobSq ((F - F0 * Rm) * Matrix.transpose Rm) = frobSq (F - F0 * Rm) := by
    refine frobSq_mul_transpose (F - F0 * Rm) (Matrix.transpose Rm) ?_
    simpa using hRm_orth
  have hFR : (F - F0 * Rm) * Matrix.transpose Rm = F * Matrix.transpose Rm - F0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hRR]
    simp
  have hFbound : frobSq (F * Matrix.transpose Rm - F0) ≤
      4 * f ^ 2 / ((Real.sqrt 2 - 1) * sig ^ 2) := by
    rw [← hFR, hinv]
    exact hbound_sq
  have hsplit : frobSq (F * Matrix.transpose Rm - F0) =
      frobSq (X * Matrix.transpose Rm - X0) + frobSq (Y * Matrix.transpose Rm - Y0) := by
    have hcast : ∀ x : Fin m, finSumFinEquiv (Sum.inl x) = Fin.castAdd n x := by
      intro x
      have h := finSumFinEquiv_symm_apply_castAdd (m := m) (n := n) x
      have h2 := congrArg finSumFinEquiv h
      simpa using h2.symm
    have hnat : ∀ y : Fin n, finSumFinEquiv (Sum.inr y) = Fin.natAdd m y := by
      intro y
      have h := finSumFinEquiv_symm_apply_natAdd (m := m) (n := n) y
      have h2 := congrArg finSumFinEquiv h
      simpa using h2.symm
    have hsumsplit : ∀ g : Fin (m + n) → ℝ,
        (∑ i : Fin (m + n), g i)
          = (∑ a : Fin m, g (Fin.castAdd n a)) + ∑ b : Fin n, g (Fin.natAdd m b) := by
      intro g
      rw [← Equiv.sum_comp finSumFinEquiv g, Fintype.sum_sum_type]
      simp only [hcast, hnat]
    have hrowF : ∀ (a : Fin m) (k : Fin r), F (Fin.castAdd n a) k = X a k := by
      intro a k
      show Fin.append (fun a : Fin m => X a) (fun b : Fin n => Y b)
        (Fin.castAdd n a) k = X a k
      rw [Fin.append_left]
    have hrowF0 : ∀ (a : Fin m) (t : Fin r), F0 (Fin.castAdd n a) t = X0 a t := by
      intro a t
      show Fin.append (fun a : Fin m => X0 a) (fun b : Fin n => Y0 b)
        (Fin.castAdd n a) t = X0 a t
      rw [Fin.append_left]
    have hrowG : ∀ (b : Fin n) (k : Fin r), F (Fin.natAdd m b) k = Y b k := by
      intro b k
      show Fin.append (fun a : Fin m => X a) (fun b : Fin n => Y b)
        (Fin.natAdd m b) k = Y b k
      rw [Fin.append_right]
    have hrowG0 : ∀ (b : Fin n) (t : Fin r), F0 (Fin.natAdd m b) t = Y0 b t := by
      intro b t
      show Fin.append (fun a : Fin m => X0 a) (fun b : Fin n => Y0 b)
        (Fin.natAdd m b) t = Y0 b t
      rw [Fin.append_right]
    have hrowL : ∀ (a : Fin m) (t : Fin r),
        (F * Matrix.transpose Rm - F0) (Fin.castAdd n a) t
          = (X * Matrix.transpose Rm - X0) a t := by
      intro a t
      show (F * Matrix.transpose Rm) (Fin.castAdd n a) t - F0 (Fin.castAdd n a) t
        = (X * Matrix.transpose Rm) a t - X0 a t
      have h1 : (∑ k : Fin r, F (Fin.castAdd n a) k * Matrix.transpose Rm k t)
          = ∑ k : Fin r, X a k * Matrix.transpose Rm k t := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hrowF a k]
      rw [Matrix.mul_apply, Matrix.mul_apply, h1, hrowF0 a t]
    have hrowR : ∀ (b : Fin n) (t : Fin r),
        (F * Matrix.transpose Rm - F0) (Fin.natAdd m b) t
          = (Y * Matrix.transpose Rm - Y0) b t := by
      intro b t
      show (F * Matrix.transpose Rm) (Fin.natAdd m b) t - F0 (Fin.natAdd m b) t
        = (Y * Matrix.transpose Rm) b t - Y0 b t
      have h1 : (∑ k : Fin r, F (Fin.natAdd m b) k * Matrix.transpose Rm k t)
          = ∑ k : Fin r, Y b k * Matrix.transpose Rm k t := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hrowG b k]
      rw [Matrix.mul_apply, Matrix.mul_apply, h1, hrowG0 b t]
    unfold frobSq
    rw [hsumsplit (fun i : Fin (m + n) =>
      ∑ t : Fin r, (F * Matrix.transpose Rm - F0) i t ^ 2)]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      exact Finset.sum_congr rfl fun t _ => by rw [hrowL a t]
    · refine Finset.sum_congr rfl fun b _ => ?_
      exact Finset.sum_congr rfl fun t _ => by rw [hrowR b t]
  refine ⟨Matrix.transpose Rm, ?_, ?_, ?_, ?_⟩
  · simpa using hRR
  · exact hFbound
  · rw [← hsplit]
    exact hFbound
  · intro sig0 hsig0
    rw [← hsplit]
    refine le_trans hFbound ?_
    have hd : (Real.sqrt 2 - 1) ≠ 0 := by linarith [Real.one_lt_sqrt_two]
    have hs : (0 : ℝ) < SMin sig0 := by nlinarith [hsigpos, hsig0]
    have key : 4 * f ^ 2 / ((Real.sqrt 2 - 1) * sig ^ 2)
        = 2 * f ^ 2 / ((Real.sqrt 2 - 1) * SMin sig0) := by
      rw [hsig0]
      field_simp
      ring
    exact key.le
  /- @proof-region region.target-node.session.1ed1da9d52dd7729 end -/

end

end Statlib.Imported

