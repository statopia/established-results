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
theorem statopia_math_node_2051336761_98c59cdc : ∀ (m n r : ℕ) (mu0 : ℝ)
    (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (i : Fin m) (j : Fin n) (zM : Matrix (Fin m) (Fin n) ℝ)
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hU : U0.transpose * U0 = 1) (hV : V0.transpose * V0 = 1)
    (hmu : 0 ≤ mu0 * (r : ℝ))
    (hrowU : rowNorm U0 ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)))
    (hrowV : rowNorm V0 ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)))
    (hz_mem : MemTangentRect U0 V0 zM)
    (hz_orth : ∀ (Y : Matrix (Fin m) (Fin n) ℝ), MemTangentRect U0 V0 Y →
      frobInner (matrixUnit i j) Y = frobInner zM Y),
    frobNorm zM ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) + Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) := by
  /- @proof-region region.target-node.session.30e9d0182131f1cf begin -/
  intro m n r mu0 U0 V0 i j zM hm hn hU hV hmu hrowU hrowV hz_mem hz_orth
  obtain ⟨A, B, hAB⟩ := hz_mem
  set R1 : Matrix (Fin r) (Fin n) ℝ := U0.transpose * zM with hR1def
  set R2 : Matrix (Fin m) (Fin r) ℝ := zM * V0 with hR2def
  set R3 : Matrix (Fin r) (Fin r) ℝ := R1 * V0 with hR3def
  have hunit : ∀ X : Matrix (Fin m) (Fin n) ℝ, frobInner (matrixUnit i j) X = X i j := by
    intro X
    simp only [frobInner, matrixUnit]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    · intro b _ hb
      rw [Finset.sum_eq_zero]
      intro k _
      simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hmemU : ∀ C : Matrix (Fin n) (Fin r) ℝ, MemTangentRect U0 V0 (U0 * C.transpose) := by
    intro C; exact ⟨C, 0, by simp⟩
  have hmemV : ∀ C : Matrix (Fin m) (Fin r) ℝ, MemTangentRect U0 V0 (C * V0.transpose) := by
    intro C; exact ⟨0, C, by simp⟩
  have hgenU : ∀ {p : ℕ} (X : Matrix (Fin m) (Fin p) ℝ) (C : Matrix (Fin r) (Fin p) ℝ),
      frobInner X (U0 * C) = frobInner (U0.transpose * X) C := by
    intro p X C
    have e1 : frobInner X (U0 * C) = ∑ l, ∑ t, ∑ k, X l k * (U0 l t * C t k) := by
      unfold frobInner
      simp only [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _; exact Finset.sum_comm
    have e2 : frobInner (U0.transpose * X) C
        = ∑ l, ∑ t, ∑ k, X l k * (U0 l t * C t k) := by
      unfold frobInner
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      have s1 : (∑ t, ∑ k, ∑ l, (U0 l t * X l k) * C t k)
          = ∑ t, ∑ l, ∑ k, (U0 l t * X l k) * C t k := by
        apply Finset.sum_congr rfl; intro t _; exact Finset.sum_comm
      have s2 : (∑ t, ∑ l, ∑ k, (U0 l t * X l k) * C t k)
          = ∑ l, ∑ t, ∑ k, (U0 l t * X l k) * C t k := Finset.sum_comm
      have s3 : (∑ l, ∑ t, ∑ k, (U0 l t * X l k) * C t k)
          = ∑ l, ∑ t, ∑ k, X l k * (U0 l t * C t k) := by
        apply Finset.sum_congr rfl; intro l _
        apply Finset.sum_congr rfl; intro t _
        apply Finset.sum_congr rfl; intro k _
        ring
      exact s1.trans (s2.trans s3)
    exact e1.trans e2.symm
  have hgenV : ∀ (X : Matrix (Fin m) (Fin n) ℝ) (C : Matrix (Fin m) (Fin r) ℝ),
      frobInner X (C * V0.transpose) = frobInner C (X * V0) := by
    intro X C
    have e1 : frobInner X (C * V0.transpose) = ∑ l, ∑ t, ∑ k, X l k * (C l t * V0 k t) := by
      unfold frobInner
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _; exact Finset.sum_comm
    have e2 : frobInner C (X * V0) = ∑ l, ∑ t, ∑ k, X l k * (C l t * V0 k t) := by
      unfold frobInner
      simp only [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro t _
      apply Finset.sum_congr rfl; intro k _
      ring
    exact e1.trans e2.symm
  have hsymm : ∀ {a b : ℕ} (P Q : Matrix (Fin a) (Fin b) ℝ), frobInner P Q = frobInner Q P := by
    intro a b P Q
    unfold frobInner
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => mul_comm _ _))
  have hR1 : ∀ t k, R1 t k = U0 i t * (if k = j then 1 else 0) := by
    intro t k
    have hC : ∀ C : Matrix (Fin n) (Fin r) ℝ,
        (∑ s, U0 i s * C j s) = ∑ s, ∑ k', R1 s k' * C k' s := by
      intro C
      have h := hz_orth (U0 * C.transpose) (hmemU C)
      rw [hunit (U0 * C.transpose)] at h
      rw [hgenU zM C.transpose, ← hR1def] at h
      have hL : (U0 * C.transpose) i j = ∑ s, U0 i s * C j s := by
        rw [Matrix.mul_apply]; simp only [Matrix.transpose_apply]
      have hR : frobInner R1 C.transpose = ∑ s, ∑ k', R1 s k' * C k' s := by
        unfold frobInner
        simp only [Matrix.transpose_apply]
      rw [hL, hR] at h
      exact h
    have hLval : ∑ s, U0 i s * (matrixUnit k t) j s = U0 i t * (if k = j then 1 else 0) := by
      simp only [matrixUnit]
      by_cases hjk : k = j
      · rw [if_pos hjk]
        rw [Finset.sum_eq_single t]
        · simp [hjk.symm]
        · intro b _ hb; simp [hjk.symm, hb]
        · intro h; exact absurd (Finset.mem_univ t) h
      · rw [if_neg hjk]
        rw [show ∑ s, U0 i s * (if j = k ∧ s = t then (1:ℝ) else 0) = 0 from by
          apply Finset.sum_eq_zero
          intro s _
          simp [show j ≠ k from fun hh => hjk hh.symm]]
        rw [mul_zero]
    have hRval : ∑ s, ∑ k', R1 s k' * (matrixUnit k t) k' s = R1 t k := by
      simp only [matrixUnit]
      rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ k) h
      · intro b _ hb
        apply Finset.sum_eq_zero
        intro k' _
        simp [hb]
      · intro h; exact absurd (Finset.mem_univ t) h
    have ht := hC (matrixUnit k t)
    rw [hLval, hRval] at ht
    exact ht.symm
  have hR2 : ∀ l t, R2 l t = (if l = i then 1 else 0) * V0 j t := by
    intro l t
    have hC : ∀ C : Matrix (Fin m) (Fin r) ℝ,
        (∑ s, C i s * V0 j s) = ∑ s, ∑ t', C s t' * R2 s t' := by
      intro C
      have h := hz_orth (C * V0.transpose) (hmemV C)
      rw [hunit (C * V0.transpose)] at h
      rw [hgenV zM C, ← hR2def] at h
      have hL : (C * V0.transpose) i j = ∑ s, C i s * V0 j s := by
        rw [Matrix.mul_apply]; simp only [Matrix.transpose_apply]
      have hR : frobInner C R2 = ∑ s, ∑ t', C s t' * R2 s t' := rfl
      rw [hL, hR] at h
      exact h
    have hLval : ∑ s, (matrixUnit l t) i s * V0 j s = (if l = i then 1 else 0) * V0 j t := by
      simp only [matrixUnit]
      by_cases hli : l = i
      · rw [if_pos hli]
        rw [Finset.sum_eq_single t]
        · simp [hli.symm]
        · intro b _ hb; simp [hli.symm, hb]
        · intro h; exact absurd (Finset.mem_univ t) h
      · rw [if_neg hli]
        rw [show ∑ s, (if i = l ∧ s = t then (1:ℝ) else 0) * V0 j s = 0 from by
          apply Finset.sum_eq_zero
          intro s _
          simp [show i ≠ l from fun hh => hli hh.symm]]
        rw [zero_mul]
    have hRval : ∑ s, ∑ t', (matrixUnit l t) s t' * R2 s t' = R2 l t := by
      simp only [matrixUnit]
      rw [Finset.sum_eq_single l]
      · rw [Finset.sum_eq_single t]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ t) h
      · intro b _ hb
        apply Finset.sum_eq_zero
        intro t' _
        simp [hb]
      · intro h; exact absurd (Finset.mem_univ l) h
    have ht := hC (matrixUnit l t)
    rw [hLval, hRval] at ht
    exact ht.symm
  have hR3alt : U0.transpose * R2 = R3 := by
    rw [hR2def, hR3def, ← Matrix.mul_assoc, hR1def]
  have hUz : U0.transpose * zM = A.transpose + (U0.transpose * B) * V0.transpose := by
    rw [hAB, Matrix.mul_add]
    rw [← Matrix.mul_assoc U0.transpose U0 A.transpose,
        ← Matrix.mul_assoc U0.transpose B V0.transpose, hU, Matrix.one_mul]
  have hVz : zM * V0 = U0 * (A.transpose * V0) + B := by
    rw [hAB, Matrix.add_mul]
    rw [Matrix.mul_assoc U0 A.transpose V0, Matrix.mul_assoc B V0.transpose V0,
        hV, Matrix.mul_one]
  have hUzV : (U0.transpose * zM) * V0 = A.transpose * V0 + U0.transpose * B := by
    rw [hUz, Matrix.add_mul]
    rw [Matrix.mul_assoc (U0.transpose * B) V0.transpose V0, hV, Matrix.mul_one]
  have eA1 : U0 * R1 = U0 * A.transpose + U0 * ((U0.transpose * B) * V0.transpose) := by
    rw [hR1def, hUz, Matrix.mul_add]
  have eA2 : R2 * V0.transpose = U0 * (A.transpose * V0) * V0.transpose + B * V0.transpose := by
    rw [hR2def, hVz, Matrix.add_mul]
  have eA3 : U0 * R3 * V0.transpose
      = U0 * (A.transpose * V0) * V0.transpose + (U0 * (U0.transpose * B)) * V0.transpose := by
    rw [hR3def, hR1def, hUzV, Matrix.mul_add, Matrix.add_mul]
  have Massoc : (U0 * (U0.transpose * B)) * V0.transpose
      = U0 * ((U0.transpose * B) * V0.transpose) :=
    Matrix.mul_assoc U0 (U0.transpose * B) V0.transpose
  have hdecomp : zM = U0 * R1 + R2 * V0.transpose - U0 * R3 * V0.transpose := by
    rw [eA1, eA2, eA3, Massoc, hAB]
    abel
  have hinner1 : frobInner zM (U0 * R1) = ∑ t, (U0 i t)^2 := by
    rw [hgenU zM R1, ← hR1def]
    have hinner : ∀ t : Fin r, ∑ k, R1 t k * R1 t k = (U0 i t)^2 := by
      intro t
      have h1 : ∀ k : Fin n, R1 t k * R1 t k = (U0 i t)^2 * (if k = j then 1 else 0) := by
        intro k
        rw [hR1 t k]
        by_cases hk : k = j <;> simp [hk] <;> ring
      rw [Finset.sum_congr rfl (fun k _ => h1 k)]
      rw [← Finset.mul_sum]
      have hone : ∑ k : Fin n, (if k = j then (1:ℝ) else 0) = 1 := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [hone, mul_one]
    unfold frobInner
    exact Finset.sum_congr rfl (fun t _ => hinner t)
  have hinner2 : frobInner zM (R2 * V0.transpose) = ∑ t, (V0 j t)^2 := by
    rw [hgenV zM R2, ← hR2def]
    unfold frobInner
    have hinner : ∀ l : Fin m, ∑ t, R2 l t * R2 l t
        = (if l = i then (1:ℝ) else 0) * ∑ t, (V0 j t)^2 := by
      intro l
      have h1 : ∀ t : Fin r, R2 l t * R2 l t = (if l = i then (1:ℝ) else 0) * (V0 j t)^2 := by
        intro t
        rw [hR2 l t]
        by_cases hl : l = i <;> simp [hl] <;> ring
      rw [Finset.sum_congr rfl (fun t _ => h1 t)]
      rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun l _ => hinner l)]
    rw [← Finset.sum_mul]
    have hone : ∑ l : Fin m, (if l = i then (1:ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hone, one_mul]
  have hinner3 : frobInner zM (U0 * R3 * V0.transpose) = frobInner R3 R3 := by
    rw [hgenV zM (U0 * R3), ← hR2def, ← hsymm R2 (U0 * R3), hgenU R2 R3, hR3alt]
  have hlinear : frobInner zM (U0 * R1 + R2 * V0.transpose - U0 * R3 * V0.transpose)
      = frobInner zM (U0 * R1) + frobInner zM (R2 * V0.transpose)
        - frobInner zM (U0 * R3 * V0.transpose) := by
    simp only [frobInner, Matrix.add_apply, Matrix.sub_apply, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hstep : frobInner zM zM
      = frobInner zM (U0 * R1 + R2 * V0.transpose - U0 * R3 * V0.transpose) :=
    congrArg (fun W => frobInner zM W) hdecomp
  have hval : frobInner zM zM
      = (∑ t, (U0 i t)^2) + (∑ t, (V0 j t)^2) - frobInner R3 R3 := by
    rw [hstep, hlinear, hinner1, hinner2, hinner3]
  have hnn3 : 0 ≤ frobInner R3 R3 := by
    unfold frobInner
    exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun k _ => mul_self_nonneg (R3 t k)))
  have hle : frobInner zM zM ≤ (∑ t, (U0 i t)^2) + (∑ t, (V0 j t)^2) := by
    linarith [hval, hnn3]
  have hfr : frobNorm zM = Real.sqrt (frobInner zM zM) := by
    unfold frobNorm
    congr 1
    unfold frobInner
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => by ring))
  set α : ℝ := Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) with hα
  set β : ℝ := Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) with hβ
  have hαnn : 0 ≤ α := by rw [hα]; exact Real.sqrt_nonneg _
  have hβnn : 0 ≤ β := by rw [hβ]; exact Real.sqrt_nonneg _
  have hbddU : BddAbove (Set.range (fun i : Fin m => Real.sqrt (∑ j, (U0 i j)^2))) := by
    refine ⟨Real.sqrt (∑ i, ∑ j, (U0 i j)^2), ?_⟩
    rintro _ ⟨i0, rfl⟩
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
      (Finset.mem_univ i0)
  have hbddV : BddAbove (Set.range (fun j : Fin n => Real.sqrt (∑ i, (V0 j i)^2))) := by
    refine ⟨Real.sqrt (∑ j, ∑ i, (V0 j i)^2), ?_⟩
    rintro _ ⟨j0, rfl⟩
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (Finset.mem_univ j0)
  have haU : Real.sqrt (∑ t, (U0 i t)^2) ≤ α := by
    have h1 : Real.sqrt (∑ t, (U0 i t)^2) ≤ rowNorm U0 := by
      simpa [rowNorm] using le_ciSup hbddU i
    exact le_trans h1 hrowU
  have hbV : Real.sqrt (∑ t, (V0 j t)^2) ≤ β := by
    have h1 : Real.sqrt (∑ t, (V0 j t)^2) ≤ rowNorm V0 := by
      simpa [rowNorm] using le_ciSup hbddV j
    exact le_trans h1 hrowV
  have ha2 : (∑ t, (U0 i t)^2) ≤ α^2 := by
    have hsq : Real.sqrt (∑ t, (U0 i t)^2) ^ 2 = ∑ t, (U0 i t)^2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun t _ => sq_nonneg (U0 i t)))
    have h0 : (0 : ℝ) ≤ Real.sqrt (∑ t, (U0 i t)^2) := Real.sqrt_nonneg _
    nlinarith [haU, hαnn, hsq, h0]
  have hb2 : (∑ t, (V0 j t)^2) ≤ β^2 := by
    have hsq : Real.sqrt (∑ t, (V0 j t)^2) ^ 2 = ∑ t, (V0 j t)^2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun t _ => sq_nonneg (V0 j t)))
    have h0 := Real.sqrt_nonneg (∑ t, (V0 j t)^2)
    nlinarith [hbV, hβnn, hsq, h0]
  have h1 : frobNorm zM ≤ Real.sqrt ((∑ t, (U0 i t)^2) + (∑ t, (V0 j t)^2)) := by
    rw [hfr]; exact Real.sqrt_le_sqrt hle
  have h2 : Real.sqrt ((∑ t, (U0 i t)^2) + (∑ t, (V0 j t)^2)) ≤ Real.sqrt (α^2 + β^2) := by
    apply Real.sqrt_le_sqrt; linarith [ha2, hb2]
  have h3 : Real.sqrt (α ^ 2 + β ^ 2) ≤ α + β := by
    have hnn : (0 : ℝ) ≤ α + β := add_nonneg hαnn hβnn
    rw [← Real.sqrt_sq hnn]
    apply Real.sqrt_le_sqrt
    have hsq : α ^ 2 + β ^ 2 + 2 * (α * β) = (α + β) ^ 2 := by ring
    have h2ab : (0 : ℝ) ≤ 2 * (α * β) := by
      have hab : (0 : ℝ) ≤ α * β := mul_nonneg hαnn hβnn
      linarith [hab]
    linarith [hsq, h2ab]
  exact le_trans h1 (le_trans h2 h3)
  /- @proof-region region.target-node.session.30e9d0182131f1cf end -/

end

end Statlib.Imported

