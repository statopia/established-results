import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SvdSortedExists
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48

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
theorem statopia_math_node_3063245539_44590815 : ∀ (r N : ℕ) (hr : 1 ≤ r) (hNr : r ≤ N)
    (sig0 : Fin r → ℝ) (hsmin : 0 < SMin sig0)
    (F : Matrix (Fin N) (Fin r) ℝ)
    (hF : Matrix.transpose F * F = Matrix.diagonal (fun t => 2 * sig0 t)),
    (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩) ^ 2
        = 2 * SMin sig0 ∧
      0 < Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩ := by
  /- @proof-region region.target-node.session.390dc5d6ca40b47a begin -/
  intro r N hr hNr sig0 hsig F hF
  haveI : NeZero r := ⟨by omega⟩
  have hmin : min N r = r := by omega
  have hlt : ∀ k : Fin r, k.val < min N r := fun k => by rw [hmin]; exact k.isLt
  have hltN : ∀ k : Fin r, k.val < N := fun k => by have h := k.isLt; omega
  obtain ⟨s, hs⟩ := Statlib.HighDim.MatrixAnalysis.svd_sorted_exists (A := F)
  obtain ⟨su, sv, ssig, hsu, hsv, hdiag, _, hFeq⟩ := s
  have hσ : ∀ k : Fin r,
      Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩ = ssig ⟨k.val, hltN k⟩ k := by
    intro k
    rw [Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary, ← hs ⟨k.val, hlt k⟩]
    rfl
  have hvv : sv * sv.transpose = 1 := mul_eq_one_comm.mpr hsv
  have hcol : ∀ k : Fin r, ∑ i : Fin r, (sv i k) ^ 2 = 1 := by
    intro k
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M k k) hsv
    simpa [Matrix.mul_apply, sq] using h
  have hrow : ∀ i : Fin r, ∑ k : Fin r, (sv i k) ^ 2 = 1 := by
    intro i
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M i i) hvv
    simpa [Matrix.mul_apply, sq] using h
  have hmul2 : ∀ k j : Fin r,
      (sv.transpose * Matrix.diagonal (fun t : Fin r => 2 * sig0 t)) k j = sv j k * (2 * sig0 j) := by
    intro k j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
      mul_ite, mul_zero, ite_mul, zero_mul]
    simp
  have hsum2 : ∀ k : Fin r,
      (sv.transpose * Matrix.diagonal (fun t : Fin r => 2 * sig0 t) * sv) k k
        = 2 * ∑ i : Fin r, (sv i k) ^ 2 * sig0 i := by
    intro k
    rw [Matrix.mul_apply]
    have h : ∀ j : Fin r,
        (sv.transpose * Matrix.diagonal (fun t : Fin r => 2 * sig0 t)) k j * sv j k
          = sv j k * sv j k * (2 * sig0 j) := by
      intro j
      rw [hmul2 k j]
      ring
    simp only [h]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hdiagSS : ssig.transpose * ssig
      = Matrix.diagonal
          (fun k : Fin r => (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2) := by
    ext k l
    rw [Matrix.mul_apply]
    by_cases hkl : k = l
    · subst hkl
      rw [Matrix.diagonal_apply_eq]
      have hstep : ∑ i : Fin N, ssig i k * ssig i k
          = ssig ⟨k.val, hltN k⟩ k * ssig ⟨k.val, hltN k⟩ k := by
        refine Finset.sum_eq_single (⟨k.val, hltN k⟩ : Fin N) ?_ ?_
        · intro i _ hi
          have hne : (i : ℕ) ≠ (k : ℕ) := by
            intro hh
            exact hi (Fin.ext hh)
          rw [hdiag i k hne, zero_mul]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
      have hp : ∀ j : Fin N, ssig.transpose k j * ssig j k = ssig j k * ssig j k := by
        intro j
        rw [Matrix.transpose_apply]
      have hgoal : ∑ j : Fin N, ssig.transpose k j * ssig j k
          = ssig ⟨k.val, hltN k⟩ k * ssig ⟨k.val, hltN k⟩ k :=
        (Finset.sum_congr rfl (fun j _ => hp j)).trans hstep
      rw [hgoal, hσ k]
      ring
    · rw [Matrix.diagonal_apply, if_neg hkl]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Matrix.transpose_apply]
      by_cases hi : (i : ℕ) = (k : ℕ)
      · have hne : (i : ℕ) ≠ (l : ℕ) := by
          intro hh
          exact hkl (Fin.ext (by omega))
        rw [hdiag i l hne, mul_zero]
      · rw [hdiag i k hi, zero_mul]
  have hcancel : sv.transpose * (F.transpose * F) * sv = ssig.transpose * ssig := by
    rw [hFeq]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc su.transpose su, hsu, Matrix.one_mul]
    rw [hsv, Matrix.mul_one]
    rw [← Matrix.mul_assoc sv.transpose sv, hsv, Matrix.one_mul]
  have hmain : sv.transpose * Matrix.diagonal (fun t : Fin r => 2 * sig0 t) * sv
      = Matrix.diagonal
          (fun k : Fin r => (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2) := by
    rw [← hF, hcancel, hdiagSS]
  have hmain2 : Matrix.diagonal (fun t : Fin r => 2 * sig0 t)
      = sv * Matrix.diagonal
          (fun k : Fin r => (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2)
        * sv.transpose := by
    rw [← hmain]
    simp only [Matrix.mul_assoc, hvv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hvv, Matrix.one_mul]
  have hkey : ∀ k : Fin r,
      (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2
        = 2 * ∑ i : Fin r, (sv i k) ^ 2 * sig0 i := by
    intro k
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M k k) hmain
    dsimp only at h
    rw [Matrix.diagonal_apply_eq] at h
    rw [← h, hsum2 k]
  have hmul3 : ∀ i j : Fin r,
      (sv * Matrix.diagonal
        (fun k : Fin r => (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2)) i j
        = sv i j * (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨j.val, hlt j⟩) ^ 2 := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul]
    simp
  have hsum3 : ∀ i : Fin r,
      (sv * Matrix.diagonal
          (fun k : Fin r => (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2)
        * sv.transpose) i i
        = ∑ k : Fin r, (sv i k) ^ 2
            * (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2 := by
    intro i
    rw [Matrix.mul_apply]
    have h : ∀ k : Fin r,
        (sv * Matrix.diagonal
            (fun k : Fin r => (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2)) i k
          * sv.transpose k i
          = sv i k * sv i k
            * (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2 := by
      intro k
      rw [hmul3 i k, Matrix.transpose_apply]
      ring
    simp only [h]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hcross : ∀ i : Fin r, 2 * sig0 i
      = ∑ k : Fin r, (sv i k) ^ 2
          * (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2 := by
    intro i
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M i i) hmain2
    dsimp only at h
    rw [Matrix.diagonal_apply_eq] at h
    rw [h, hsum3 i]
  have hminle : ∀ i : Fin r, SMin sig0 ≤ sig0 i :=
    fun i => ciInf_le (Set.finite_range sig0).bddBelow i
  have hminat : ∃ i0 : Fin r, sig0 i0 = SMin sig0 := by
    obtain ⟨i0, -, hi0⟩ :=
      Finset.exists_min_image (Finset.univ : Finset (Fin r)) sig0 Finset.univ_nonempty
    exact ⟨i0, le_antisymm (le_ciInf (fun j => hi0 j (Finset.mem_univ j)))
      (ciInf_le (Set.finite_range sig0).bddBelow i0)⟩
  have hnonneg : 0 ≤ Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩ :=
    (Statlib.HighDim.MatrixAnalysis.singular_value_properties F (Or.inl ⟨⟨0, by omega⟩⟩)).2.1 _
  have hmono : ∀ k : Fin r,
      (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩) ^ 2
        ≤ (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2 := by
    intro k
    have hle : (⟨k.val, hlt k⟩ : Fin (min N r)) ≤ ⟨r - 1, by omega⟩ := by
      simp only [Fin.le_def]
      have := k.isLt
      omega
    have h1 : Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩
        ≤ Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩ :=
      Statlib.HighDim.MatrixAnalysis.singularValues_antitone F hle
    have h3 : 0 ≤ Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩ :=
      (Statlib.HighDim.MatrixAnalysis.singular_value_properties F (Or.inl ⟨⟨0, by omega⟩⟩)).2.1 _
    nlinarith [h1, hnonneg, h3]
  have hlower : 2 * SMin sig0
      ≤ (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩) ^ 2 := by
    rw [hkey ⟨r - 1, by omega⟩]
    have hck : ∑ i : Fin r, (sv i ⟨r - 1, by omega⟩) ^ 2 = 1 := hcol ⟨r - 1, by omega⟩
    have hstep : SMin sig0 ≤ ∑ i : Fin r, (sv i ⟨r - 1, by omega⟩) ^ 2 * sig0 i := by
      calc SMin sig0 = ∑ i : Fin r, (sv i ⟨r - 1, by omega⟩) ^ 2 * SMin sig0 := by
            rw [← Finset.sum_mul, hck, one_mul]
        _ ≤ ∑ i : Fin r, (sv i ⟨r - 1, by omega⟩) ^ 2 * sig0 i :=
            Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hminle i) (sq_nonneg _))
    nlinarith [hstep]
  have hupper : (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩) ^ 2
      ≤ 2 * SMin sig0 := by
    obtain ⟨i0, hi0⟩ := hminat
    have hci := hcross i0
    have hri : ∑ k : Fin r, (sv i0 k) ^ 2 = 1 := hrow i0
    have hstep : (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩) ^ 2
        ≤ ∑ k : Fin r, (sv i0 k) ^ 2
            * (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2 := by
      calc (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩) ^ 2
          = ∑ k : Fin r, (sv i0 k) ^ 2
              * (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩) ^ 2 := by
              rw [← Finset.sum_mul, hri, one_mul]
        _ ≤ ∑ k : Fin r, (sv i0 k) ^ 2
              * (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨k.val, hlt k⟩) ^ 2 :=
              Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hmono k) (sq_nonneg _))
    rw [← hi0, hci]
    exact hstep
  have heq : (Statlib.HighDim.MatrixAnalysis.singularValues F ⟨r - 1, by omega⟩) ^ 2
      = 2 * SMin sig0 := le_antisymm hupper hlower
  refine ⟨heq, lt_of_le_of_ne hnonneg ?_⟩
  intro hzero
  rw [← hzero] at heq
  linarith [hsig, heq]
  /- @proof-region region.target-node.session.390dc5d6ca40b47a end -/

end

end Statlib.Imported

