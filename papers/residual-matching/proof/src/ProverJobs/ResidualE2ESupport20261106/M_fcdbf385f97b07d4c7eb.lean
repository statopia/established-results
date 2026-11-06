import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
-- Server-owned verified dependencies for one standalone Math node.
import ProverJobs.ResidualE2ESupport20261106.ExternalNodes.Node_556e505598fbe6bfd0d0
import ProverJobs.ResidualE2ESupport20261106.M_a9a8bba09ddbecaccb87
import ProverJobs.ResidualE2ESupport20261106.M_dd508d27ad365f443d21
import ProverJobs.ResidualE2ESupport20261106.M_2ce0255179bdd26af5d8
import ProverJobs.ResidualE2ESupport20261106.M_e827bd528140b757b3ec
import ProverJobs.ResidualE2ESupport20261106.M_983b93e5b7a9bbf1ef65
import ProverJobs.ResidualE2ESupport20261106.M_2004f28d8600f1caa2b4
import ProverJobs.ResidualE2ESupport20261106.M_16393836de1500c0c075
import ProverJobs.ResidualE2ESupport20261106.M_0ab8bb2017abfa95e120
import ProverJobs.ResidualE2ESupport20261106.M_6f31c9b9bce7b01a3a28
import ProverJobs.ResidualE2ESupport20261106.M_33a8aa225c9a44b03a84
import ProverJobs.ResidualE2ESupport20261106.M_36c2e0ee0bcce41f385b
import ProverJobs.ResidualE2ESupport20261106.M_1826cf4a199ca47d64c5
import ProverJobs.ResidualE2ESupport20261106.M_fd4cdab3b3f7ab294c05
import ProverJobs.ResidualE2ESupport20261106.M_edb957e472d1bec8db32
import ProverJobs.ResidualE2ESupport20261106.M_e10a9713d4032f7747b4

import ProverJobs.ResidualE2ESupport20261106.M_655541399eba6e711ce1

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
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

set_option maxHeartbeats 4000000
set_option autoImplicit false in
theorem statopia_math_node_2034633510_f859b6bb : ∀ (D0 : ℝ) (hD0 : 0 < D0) (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0)
    (CD : ℝ) (hCD : max (Kt * (D0 + 12)) (D0 + 20) ≤ CD),
    ∃ M1 : ℕ, ∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hM1 : M1 ≤ m)
      (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
      (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p),
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (XT Mask : Ω → Matrix (Fin m) (Fin n) ℝ) (L : ℝ),
      L = CD * Real.log ((m : ℝ) * (n : ℝ)) + (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 →
      (∀ (i : Fin m) (j : Fin n), Measurable fun ω => XT ω i j) →
      (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => XT ω i j) μ) →
      (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (XT ω i j) ^ 2) μ) →
      (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
      (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
      (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
      iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => XT ω ij.1 ij.2) μ →
      iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
      IndepFun (fun ω (ij : Fin m × Fin n) => XT ω ij.1 ij.2)
        (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
      (∀ (i : Fin m) (j : Fin n), ∫ ω, XT ω i j ∂μ = 0) →
      (∀ (i : Fin m) (j : Fin n), ∫ ω, (XT ω i j) ^ 2 ∂μ = 1) →
      (∀ (ω : Ω) (i : Fin m) (j : Fin n), |XT ω i j| ≤ 3 * L) →
      ∃ E : Set Ω,
        (∀ ω : Ω, 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m <
            Statlib.HighDim.MatrixAnalysis.opNorm (maskedScaled p (XT ω) (Mask ω)) → ω ∈ E) ∧
        μ E ≤ ENNReal.ofReal (((m : ℝ) + (n : ℝ)) *
          Real.exp (-(CD * Real.log ((m : ℝ) * (n : ℝ))))) := by
  /- @proof-region region.target-node.session.e930d1af0357fa95 begin -/
  set_option maxHeartbeats 800000 in
  classical


  intro D0 hD0 Kt hKt alpha0 halpha0 CD hCD
  obtain ⟨Cw, hCwpos, hCw⟩ := statopia_math_node_3840929802_9daf1dcd
  obtain ⟨Ch, hChpos, hcite⟩ := ResidualSparseRepair20261106.bvh_upper_concentration
  have hCD0 : 0 < CD := lt_of_lt_of_le (by linarith : (0 : ℝ) < D0 + 20)
    (le_trans (le_max_right _ _) hCD)
  have hT0 : (0 : ℝ) < (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by positivity
  obtain ⟨Mnum, hMnum⟩ := statopia_math_node_2243148282_1fc9761b alpha0 CD
    ((10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
    Ch Cw halpha0 hCD0 hT0 hChpos.le hCwpos.le
  refine ⟨max 17 Mnum, ?_⟩







  intro m n hm hn hnm hM1 p hp0 hp1 hsparse
  intro Ω Ωmeas μ μprob XT Mask L hL hXTmeas hXTint hXTint2 hMaskmeas hMask01 hMasklaw
    hXTindep hMaskindep hIndep hXTmean hXTvar hXTb
  have hCDpos : 0 < CD :=
    lt_of_lt_of_le (by linarith : (0:ℝ) < D0 + 20) (le_trans (le_max_right _ _) hCD)
  have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hlogm : 0 < Real.log (m:ℝ) := Real.log_pos (by linarith)
  have hlogmn : 0 < Real.log ((m:ℝ) * (n:ℝ)) := by
    apply Real.log_pos
    nlinarith
  have hTpos : (0:ℝ) < (10:ℝ)^6 * (Kt+1)^4 * (D0+1)^4 * (alpha0+1)^4 := by positivity
  have hLpos : 0 < L := by
    rw [hL]
    have h1 : 0 < CD * Real.log ((m:ℝ) * (n:ℝ)) := mul_pos hCDpos hlogmn
    linarith
  have hsqrtmp : (0:ℝ) < Real.sqrt ((m:ℝ) * p) := Real.sqrt_pos.2 (by positivity)
  have hRpos : (0:ℝ) < 3 * L / Real.sqrt ((m:ℝ) * p) := by
    have : (0:ℝ) < 3 * L := by linarith
    exact div_pos this hsqrtmp
  set Eel : Fin m × Fin n → Matrix (Fin m) (Fin n) ℝ :=
    fun q i j => if (i, j) = q then 1 else 0 with hEel
  set W : Fin m × Fin n → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun q => (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) ((Eel q).map Complex.ofReal)
      (Matrix.transpose ((Eel q).map Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm with hWdef
  have hWentry : ∀ (q : Fin m × Fin n) (a b : Fin (m + n)), W q a b = 0 ∨ W q a b = 1 := by
    intro q a b
    obtain ⟨s, rfl⟩ : ∃ s : Fin m ⊕ Fin n, finSumFinEquiv s = a :=
      ⟨finSumFinEquiv.symm a, finSumFinEquiv.apply_symm_apply a⟩
    obtain ⟨t, rfl⟩ : ∃ t : Fin m ⊕ Fin n, finSumFinEquiv t = b :=
      ⟨finSumFinEquiv.symm b, finSumFinEquiv.apply_symm_apply b⟩
    rw [hWdef]
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases s with i | i <;> rcases t with j | j
    · left
      simp [Matrix.fromBlocks]
    · by_cases h : (i, j) = q
      · right
        have h1 : (Eel q) i j = 1 := by rw [hEel]; simp [h]
        simp [Matrix.fromBlocks, h1]
      · left
        have h1 : (Eel q) i j = 0 := by rw [hEel]; simp [h]
        simp [Matrix.fromBlocks, h1]
    · by_cases h : (j, i) = q
      · right
        have h1 : (Eel q) j i = 1 := by rw [hEel]; simp [h]
        simp [Matrix.fromBlocks, h1]
      · left
        have h1 : (Eel q) j i = 0 := by rw [hEel]; simp [h]
        simp [Matrix.fromBlocks, h1]
    · left
      simp [Matrix.fromBlocks]


  have hWherm : ∀ q : Fin m × Fin n, (W q).IsHermitian := by
    intro q
    have h0m : (0 : Matrix (Fin m) (Fin m) ℂ).IsHermitian := by
      refine Matrix.IsHermitian.ext ?_
      intro a b
      simp
    have h0n : (0 : Matrix (Fin n) (Fin n) ℂ).IsHermitian := by
      refine Matrix.IsHermitian.ext ?_
      intro a b
      simp
    have hB : ((Eel q).map Complex.ofReal).conjTranspose
        = Matrix.transpose ((Eel q).map Complex.ofReal) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
      simp
    have hfb : (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
        ((Eel q).map Complex.ofReal)
        (Matrix.transpose ((Eel q).map Complex.ofReal))
        (0 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian :=
      Matrix.IsHermitian.fromBlocks h0m hB h0n
    have hh : ∀ (s t : Fin m ⊕ Fin n),
        star ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
          ((Eel q).map Complex.ofReal)
          (Matrix.transpose ((Eel q).map Complex.ofReal))
          (0 : Matrix (Fin n) (Fin n) ℂ)) t s)
          = (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
            ((Eel q).map Complex.ofReal)
            (Matrix.transpose ((Eel q).map Complex.ofReal))
            (0 : Matrix (Fin n) (Fin n) ℂ)) s t := by
      intro s t
      have h := congrFun (congrFun hfb.eq s) t
      simpa only [Matrix.conjTranspose_apply] using h
    refine Matrix.IsHermitian.ext ?_
    intro a b
    show star (W q b a) = W q a b
    rw [hWdef]
    simp only [Matrix.submatrix_apply]
    exact hh (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)

  have hWeval : ∀ (q : Fin m × Fin n) (s t : Fin m ⊕ Fin n),
      W q (finSumFinEquiv s) (finSumFinEquiv t)
        = (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) ((Eel q).map Complex.ofReal)
            (Matrix.transpose ((Eel q).map Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ)) s t := by
    intro q s t
    rw [hWdef]
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have hdilHerm : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (A.map Complex.ofReal)
        (Matrix.transpose (A.map Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm).IsHermitian := by
    intro A
    have h0m : (0 : Matrix (Fin m) (Fin m) ℂ).IsHermitian := by
      refine Matrix.IsHermitian.ext ?_
      intro a b
      simp
    have h0n : (0 : Matrix (Fin n) (Fin n) ℂ).IsHermitian := by
      refine Matrix.IsHermitian.ext ?_
      intro a b
      simp
    have hB : (A.map Complex.ofReal).conjTranspose = Matrix.transpose (A.map Complex.ofReal) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
      simp
    have hfb := Matrix.IsHermitian.fromBlocks h0m hB h0n
    have hh : ∀ (s t : Fin m ⊕ Fin n),
        star ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (A.map Complex.ofReal)
          (Matrix.transpose (A.map Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ)) t s)
          = (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (A.map Complex.ofReal)
            (Matrix.transpose (A.map Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ)) s t := by
      intro s t
      have h := congrFun (congrFun hfb.eq s) t
      simpa only [Matrix.conjTranspose_apply] using h
    refine Matrix.IsHermitian.ext ?_
    intro a b
    simp only [Matrix.submatrix_apply]
    exact hh _ _

  have hWsum : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      (∑ q : Fin m × Fin n, (((A q.1 q.2 : ℝ)) : ℂ) • W q)
        = (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (A.map Complex.ofReal)
            (Matrix.transpose (A.map Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
            finSumFinEquiv.symm finSumFinEquiv.symm := by
    intro A
    ext a b
    obtain ⟨s, rfl⟩ : ∃ s : Fin m ⊕ Fin n, finSumFinEquiv s = a :=
      ⟨finSumFinEquiv.symm a, finSumFinEquiv.apply_symm_apply a⟩
    obtain ⟨t, rfl⟩ : ∃ t : Fin m ⊕ Fin n, finSumFinEquiv t = b :=
      ⟨finSumFinEquiv.symm b, finSumFinEquiv.apply_symm_apply b⟩
    have hsm : ∀ (c z : ℂ), c • z = c * z := fun c z => rfl
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.sum_apply,
      Matrix.smul_apply, hsm, hWeval]

    rcases s with i | i <;> rcases t with j | j
    · simp [Matrix.fromBlocks]
    · have hterm : ∀ q : Fin m × Fin n,
          (((A q.1 q.2 : ℝ)) : ℂ) *
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) ((Eel q).map Complex.ofReal)
                (Matrix.transpose ((Eel q).map Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ))
              (Sum.inl i) (Sum.inr j)
            = if q = (i, j) then (((A i j : ℝ)) : ℂ) else 0 := by
        intro q
        by_cases hq : q = (i, j)
        · subst hq
          simp [Matrix.fromBlocks, hEel]
        · rw [if_neg hq]
          have h1 : (Eel q) i j = 0 := by
            rw [hEel]
            simp [show (i, j) ≠ q from fun h => hq h.symm]
          simp [Matrix.fromBlocks, h1]

      rw [Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => hterm q),
        Finset.sum_eq_single (i, j)]
      · simp [Matrix.fromBlocks]
      · intro q _ hne
        exact if_neg hne
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hterm : ∀ q : Fin m × Fin n,
          (((A q.1 q.2 : ℝ)) : ℂ) *
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) ((Eel q).map Complex.ofReal)
                (Matrix.transpose ((Eel q).map Complex.ofReal)) (0 : Matrix (Fin n) (Fin n) ℂ))
              (Sum.inr i) (Sum.inl j)
            = if q = (j, i) then (((A j i : ℝ)) : ℂ) else 0 := by
        intro q
        by_cases hq : q = (j, i)
        · subst hq
          simp [Matrix.fromBlocks, hEel]
        · rw [if_neg hq]
          have h1 : (Eel q) j i = 0 := by
            rw [hEel]
            simp [show (j, i) ≠ q from fun h => hq h.symm]
          simp [Matrix.fromBlocks, h1]

      rw [Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => hterm q),
        Finset.sum_eq_single (j, i)]
      · simp [Matrix.fromBlocks]
      · intro q _ hne
        exact if_neg hne
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp [Matrix.fromBlocks]


  obtain ⟨W₀, hW₀herm, hW₀norm, hW₀entry, hW₀lin⟩ :=
    statopia_math_node_3644274559_77b175cc m n
  have hWnorm : ∀ q : Fin m × Fin n, ‖W q‖ = 1 := by
    intro q
    have hopE : Statlib.HighDim.MatrixAnalysis.opNorm (Eel q) = 1 := by
      rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
      rw [← (hW₀lin (Eel q)).2]
      have hsingle : (∑ p : Fin m × Fin n, (((Eel q p.1 p.2 : ℝ)) : ℂ) • W₀ p) = W₀ q := by
        rw [Finset.sum_eq_single q]
        · rw [show Eel q q.1 q.2 = 1 from by rw [hEel]; simp]
          simp
        · intro p _ hp
          rw [show Eel q p.1 p.2 = 0 from by
            rw [hEel]
            simp [show (p.1, p.2) ≠ q from fun h => hp (by simpa using h)]]
          simp
        · intro h
          exact absurd (Finset.mem_univ q) h
      rw [hsingle, hW₀norm q]
    have hWq : ‖W q‖ = Statlib.HighDim.MatrixAnalysis.opNorm (Eel q) := by
      have hsum : W q = ∑ p : Fin m × Fin n, (((Eel q p.1 p.2 : ℝ)) : ℂ) • W p :=
        (hWsum (Eel q)).symm
      rw [hsum, hWsum (Eel q), Matrix.l2_opNorm_def]
      exact statopia_math_node_1606911688_c7dc5675 m n (Eel q)

    rw [hWq, hopE]

  have hWlin : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      (∑ p : Fin m × Fin n, (((A p.1 p.2 : ℝ)) : ℂ) • W p).IsHermitian ∧
      ‖∑ p : Fin m × Fin n, (((A p.1 p.2 : ℝ)) : ℂ) • W p‖ = Statlib.HighDim.MatrixAnalysis.opNorm A := by
    intro A
    constructor
    · rw [hWsum A]
      exact hdilHerm A
    · rw [hWsum A, Matrix.l2_opNorm_def]
      exact statopia_math_node_1606911688_c7dc5675 m n A


  have hAmeas : ∀ (i : Fin m) (j : Fin n),
      Measurable fun ω => maskedScaled p (XT ω) (Mask ω) i j :=
    fun i j => ((hMaskmeas i j).mul (hXTmeas i j)).div_const _

  have hentry : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
      |maskedScaled p (XT ω) (Mask ω) i j| ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := by
    intro ω i j
    have habs : |Real.sqrt ((m : ℝ) * p)| = Real.sqrt ((m : ℝ) * p) := abs_of_pos hsqrtmp
    have hkey : |maskedScaled p (XT ω) (Mask ω) i j|
        = |Mask ω i j * XT ω i j| / Real.sqrt ((m : ℝ) * p) := by
      show |Mask ω i j * XT ω i j / Real.sqrt ((m : ℝ) * p)| = _
      rw [abs_div, habs]
    rw [hkey]
    apply div_le_div_of_nonneg_right _ (le_of_lt hsqrtmp)
    rcases hMask01 i j ω with h | h
    · rw [h, zero_mul, abs_zero]
      have : (0 : ℝ) < 3 * L := by linarith
      linarith
    · rw [h, one_mul]
      linarith [hXTb ω i j]
  have hmom (h h' : Fin m × Fin n) :=
    statopia_math_node_3553486712_c6cf8bba m n (by omega) hn p hp0 hp1 μ XT Mask
      hXTmeas hXTint hXTint2 hXTindep hXTmean hXTvar hMaskmeas hMask01 hMasklaw
      hMaskindep hIndep h h'
  have hAint : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω => maskedScaled p (XT ω) (Mask ω) i j) μ :=
    fun i j => (hmom (i, j) (i, j)).1
  have hmean : ∀ (i : Fin m) (j : Fin n),
      ∫ ω, maskedScaled p (XT ω) (Mask ω) i j ∂μ = 0 :=
    fun i j => (hmom (i, j) (i, j)).2.1
  have hsecond : ∀ (h h' : Fin m × Fin n),
      ∫ ω, maskedScaled p (XT ω) (Mask ω) h.1 h.2
          * maskedScaled p (XT ω) (Mask ω) h'.1 h'.2 ∂μ
        = if h = h' then 1 / (m : ℝ) else 0 :=
    fun h h' => (hmom h h').2.2.2
  have hAindep : iIndepFun
      (fun (ij : Fin m × Fin n) (ω : Ω) => maskedScaled p (XT ω) (Mask ω) ij.1 ij.2) μ := by
    have h := statopia_math_node_2156877478_7316b341
      (fun (ij : Fin m × Fin n) (ω : Ω) => XT ω ij.1 ij.2)
      (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2)
      (fun q : ℝ × ℝ => q.2 * q.1 / Real.sqrt ((m : ℝ) * p))
      hXTindep hMaskindep hIndep
      (fun ij => (hXTmeas ij.1 ij.2).aemeasurable)
      (fun ij => (hMaskmeas ij.1 ij.2).aemeasurable)
      (by
        have h1 : Measurable fun q : ℝ × ℝ => q.2 * q.1 := measurable_snd.mul measurable_fst
        exact h1.div_const _)
    simpa only [maskedScaled] using h
  set ν : Measure ((Fin m × Fin n) → ℝ) :=
    Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) with hν
  haveI hνprob : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  set μ₂ : Measure (Ω × ((Fin m × Fin n) → ℝ)) := μ.prod ν with hμ₂
  haveI hμ₂prob : IsProbabilityMeasure μ₂ := by rw [hμ₂]; infer_instance
  set Zs : Fin (m * n) → (Ω × ((Fin m × Fin n) → ℝ)) →
      Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun i ω => (((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
      (finProdFinEquiv.symm i).2 : ℝ) : ℂ) • W (finProdFinEquiv.symm i) with hZs
  have hZs_apply : ∀ (i : Fin (m * n)) (ω : Ω × ((Fin m × Fin n) → ℝ))
      (a b : Fin (m + n)),
      Zs i ω a b
        = (((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
            (finProdFinEquiv.symm i).2 : ℝ) : ℂ) * (W (finProdFinEquiv.symm i)) a b := by
    intro i ω a b
    show ((((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
            (finProdFinEquiv.symm i).2 : ℝ) : ℂ)) * (W (finProdFinEquiv.symm i)) a b = _
    rfl
  have hsmul_norm : ∀ (c : ℂ) (A : Matrix (Fin (m + n)) (Fin (m + n)) ℂ),
      ‖c • A‖ ≤ ‖c‖ * ‖A‖ := by
    intro c A
    have h1 : ‖c • A‖
        = ‖c • (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖ := by
      rw [Matrix.l2_opNorm_def, map_smul]
    rw [h1, Matrix.l2_opNorm_def]
    exact ContinuousLinearMap.opNorm_smul_le c _
  have hcnorm : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ = |x| := by
    intro x
    have h1 : ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    calc ‖((x : ℝ) : ℂ)‖ = Real.sqrt (‖((x : ℝ) : ℂ)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (x ^ 2) := by rw [h1]
      _ = |x| := Real.sqrt_sq_eq_abs x
  have hZs_entry : ∀ (i : Fin (m * n)) (ω : Ω × ((Fin m × Fin n) → ℝ)),
      ‖Zs i ω‖ ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := by
    intro i ω
    set c : ℂ := (((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
      (finProdFinEquiv.symm i).2 : ℝ) : ℂ) with hc
    have hstep : ‖Zs i ω‖ ≤ ‖c‖ := by
      show ‖c • W (finProdFinEquiv.symm i)‖ ≤ ‖c‖
      calc ‖c • W (finProdFinEquiv.symm i)‖ ≤ ‖c‖ * ‖W (finProdFinEquiv.symm i)‖ :=
            hsmul_norm _ _
        _ = ‖c‖ := by rw [hWnorm, mul_one]
    calc ‖Zs i ω‖ ≤ ‖c‖ := hstep
      _ = |((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
            (finProdFinEquiv.symm i).2 : ℝ)| := by
          rw [hc]
          exact hcnorm _
      _ ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := hentry ω.1 _ _
  set Xmat : (Ω × ((Fin m × Fin n) → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun ω => ∑ i, Zs i ω with hXmat
  have hZs_herm : ∀ (i : Fin (m * n)) (ω : Ω × ((Fin m × Fin n) → ℝ)),
      (Zs i ω).IsHermitian := by
    intro i ω
    have hW := hWherm (finProdFinEquiv.symm i)
    refine Matrix.IsHermitian.ext ?_
    intro a b
    have hWeq : star ((W (finProdFinEquiv.symm i)) b a) = (W (finProdFinEquiv.symm i)) a b := by
      have h := congrFun (congrFun hW.eq a) b
      simpa only [Matrix.conjTranspose_apply] using h
    show star (Zs i ω b a) = Zs i ω a b
    rw [hZs_apply i ω b a, hZs_apply i ω a b]
    have hstar : star ((((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2 : ℝ)) : ℂ)
        = ((((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2 : ℝ)) : ℂ) := by simp
    rw [star_mul, hstar, hWeq]
    ring
  have hZs_meas : ∀ (i : Fin (m * n)) (a b : Fin (m + n)),
      Measurable fun ω : Ω × ((Fin m × Fin n) → ℝ) => Zs i ω a b := by
    intro i a b
    have hfun : (fun ω : Ω × ((Fin m × Fin n) → ℝ) => Zs i ω a b)
        = fun ω => (((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
            (finProdFinEquiv.symm i).2 : ℝ) : ℂ) * (W (finProdFinEquiv.symm i)) a b := by
      funext ω
      exact hZs_apply i ω a b
    rw [hfun]
    exact (Complex.ofRealCLM.measurable.comp
      ((hAmeas (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).comp measurable_fst)).mul_const _
  have hfst_int : ∀ (g : Ω → ℝ), Integrable g μ →
      ∫ ω : Ω × ((Fin m × Fin n) → ℝ), g ω.1 ∂μ₂ = ∫ ω, g ω ∂μ := by
    intro g hg
    rw [hμ₂]
    rw [MeasureTheory.integral_prod (f := fun ω : Ω × ((Fin m × Fin n) → ℝ) => g ω.1)
      (MeasureTheory.Integrable.comp_fst hg ν)]
    simp
  have hZs_int : ∀ (i : Fin (m * n)) (a b : Fin (m + n)),
      Integrable (fun ω => Zs i ω a b) μ₂ := by
    intro i a b
    have hbd : ∀ᵐ ω ∂μ₂, ‖Zs i ω a b‖ ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := by
      filter_upwards with ω
      rw [hZs_apply i ω a b]
      rcases hWentry (finProdFinEquiv.symm i) a b with h | h
      · rw [h, mul_zero, norm_zero]
        exact le_of_lt hRpos
      · rw [h, mul_one, hcnorm]
        exact hentry ω.1 _ _
    exact MeasureTheory.Integrable.of_bound ((hZs_meas i a b).aestronglyMeasurable) _ hbd
  have hZs_mean : ∀ (i : Fin (m * n)) (a b : Fin (m + n)),
      ∫ ω, Zs i ω a b ∂μ₂ = 0 := by
    intro i a b
    have hmul_int : ∀ c : ℂ,
        ∫ ω : Ω × ((Fin m × Fin n) → ℝ),
          (((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
            (finProdFinEquiv.symm i).2 : ℝ) : ℂ) * c ∂μ₂ = 0 := by
      intro c
      rw [MeasureTheory.integral_mul_const c
          (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
            (((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
              (finProdFinEquiv.symm i).2 : ℝ) : ℂ)),
        integral_complex_ofReal,
        hfst_int _ (hAint (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2),
        hmean (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2]
      simp
    calc ∫ ω, Zs i ω a b ∂μ₂
        = ∫ ω, (((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
            (finProdFinEquiv.symm i).2 : ℝ) : ℂ) * (W (finProdFinEquiv.symm i)) a b ∂μ₂ := by
          simp only [hZs_apply]
      _ = 0 := hmul_int _
  have hZs_sum : ∀ (ω : Ω × ((Fin m × Fin n) → ℝ)),
      (∑ i : Fin (m * n), Zs i ω)
        = ∑ q : Fin m × Fin n,
            (((maskedScaled p (XT ω.1) (Mask ω.1)) q.1 q.2 : ℝ) : ℂ) • W q := by
    intro ω
    have h := Equiv.sum_comp (finProdFinEquiv (m := m) (n := n)).symm
      (fun q : Fin m × Fin n =>
        (((maskedScaled p (XT ω.1) (Mask ω.1)) q.1 q.2 : ℝ) : ℂ) • W q)
    simpa only [hZs] using h
  have hXherm : ∀ ω : Ω × ((Fin m × Fin n) → ℝ), (Xmat ω).IsHermitian := by
    intro ω
    show (∑ i : Fin (m * n), Zs i ω).IsHermitian
    rw [hZs_sum ω]
    exact (hWlin (maskedScaled p (XT ω.1) (Mask ω.1))).1
  have hR0 : (0 : ℝ) ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := le_of_lt hRpos
  have hZRbound : ∀ᵐ ω ∂μ₂, ∀ i : Fin (m * n), ‖Zs i ω‖ ≤ 3 * L / Real.sqrt ((m : ℝ) * p) :=
    Filter.Eventually.of_forall (fun ω i => hZs_entry i ω)
  have hXdef : ∀ ω : Ω × ((Fin m × Fin n) → ℝ),
      Xmat ω = 0 + ∑ i : Fin (m * n), Zs i ω := by
    intro ω
    show (∑ i : Fin (m * n), Zs i ω) = 0 + ∑ i : Fin (m * n), Zs i ω
    simp
  have hXmeas : ∀ (a b : Fin (m + n)),
      Measurable fun ω : Ω × ((Fin m × Fin n) → ℝ) => Xmat ω a b := by
    intro a b
    have hsum : Measurable fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
        ∑ i : Fin (m * n), Zs i ω a b :=
      Finset.measurable_sum _ (fun i _ => hZs_meas i a b)
    have hfun : (fun ω : Ω × ((Fin m × Fin n) → ℝ) => Xmat ω a b)
        = fun ω => ∑ i : Fin (m * n), Zs i ω a b := by
      funext ω
      simp only [hXmat, Matrix.sum_apply]
    rw [hfun]
    exact hsum
  have hXmean : ∀ (a b : Fin (m + n)), ∫ ω, Xmat ω a b ∂μ₂ = 0 := by
    intro a b
    have hfun : (fun ω : Ω × ((Fin m × Fin n) → ℝ) => Xmat ω a b)
        = fun ω => ∑ i : Fin (m * n), Zs i ω a b := by
      funext ω
      simp only [hXmat, Matrix.sum_apply]
    rw [hfun]
    have hsum_int : ∫ ω : Ω × ((Fin m × Fin n) → ℝ), ∑ i : Fin (m * n), Zs i ω a b ∂μ₂
        = ∑ i : Fin (m * n), ∫ ω : Ω × ((Fin m × Fin n) → ℝ), Zs i ω a b ∂μ₂ :=
      MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hZs_int i a b)
    rw [hsum_int]
    simp [hZs_mean]
  have hZs_mul : ∀ (i j : Fin (m * n)) (a b c e : Fin (m + n))
      (ω : Ω × ((Fin m × Fin n) → ℝ)),
      Zs i ω a b * Zs j ω c e
        = (((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
              (finProdFinEquiv.symm i).2
            * (maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm j).1
              (finProdFinEquiv.symm j).2 : ℝ) : ℂ)
          * ((W (finProdFinEquiv.symm i)) a b * (W (finProdFinEquiv.symm j)) c e) := by
    intro i j a b c e ω
    rw [hZs_apply i ω a b, hZs_apply j ω c e]
    push_cast
    ring
  have hZs_prod : ∀ (i j : Fin (m * n)) (a b c e : Fin (m + n)),
      ∫ ω, Zs i ω a b * Zs j ω c e ∂μ₂
        = (((if finProdFinEquiv.symm i = finProdFinEquiv.symm j then 1 / (m : ℝ) else 0
              : ℝ)) : ℂ)
            * ((W (finProdFinEquiv.symm i)) a b * (W (finProdFinEquiv.symm j)) c e) := by
    intro i j a b c e
    simp only [hZs_mul]
    rw [MeasureTheory.integral_mul_const
      ((W (finProdFinEquiv.symm i)) a b * (W (finProdFinEquiv.symm j)) c e)
      (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
        (((maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm i).1
            (finProdFinEquiv.symm i).2
          * (maskedScaled p (XT ω.1) (Mask ω.1)) (finProdFinEquiv.symm j).1
            (finProdFinEquiv.symm j).2 : ℝ) : ℂ)),
      integral_complex_ofReal,
      hfst_int _ ((hmom (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)).2.2.1),
      hsecond (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)]
  have hXmul : ∀ (a b c e : Fin (m + n)) (ω : Ω × ((Fin m × Fin n) → ℝ)),
      Xmat ω a b * Xmat ω c e
        = ∑ i : Fin (m * n), ∑ j : Fin (m * n), Zs i ω a b * Zs j ω c e := by
    intro a b c e ω
    have h1 : Xmat ω a b = ∑ i : Fin (m * n), Zs i ω a b := by
      simp only [hXmat, Matrix.sum_apply]
    have h2 : Xmat ω c e = ∑ j : Fin (m * n), Zs j ω c e := by
      simp only [hXmat, Matrix.sum_apply]
    rw [h1, h2, Finset.sum_mul_sum]
  have hZs_inner : ∀ (i : Fin (m * n)) (a b c e : Fin (m + n)),
      (∑ j : Fin (m * n), ∫ ω, Zs i ω a b * Zs j ω c e ∂μ₂)
        = (((1 / (m : ℝ) : ℝ)) : ℂ)
            * ((W (finProdFinEquiv.symm i)) a b * (W (finProdFinEquiv.symm i)) c e) := by
    intro i a b c e
    rw [Finset.sum_eq_single i]
    · rw [hZs_prod i i a b c e, if_pos rfl]
    · intro j _ hj
      have hne : finProdFinEquiv.symm i ≠ finProdFinEquiv.symm j := by
        intro h
        exact hj (finProdFinEquiv.symm.injective h).symm
      rw [hZs_prod i j a b c e, if_neg hne]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hZs_ab_le : ∀ (i : Fin (m * n)) (ω : Ω × ((Fin m × Fin n) → ℝ))
      (a b : Fin (m + n)), ‖Zs i ω a b‖ ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := by
    intro i ω a b
    rw [hZs_apply i ω a b]
    rcases hWentry (finProdFinEquiv.symm i) a b with h | h
    · rw [h, mul_zero, norm_zero]
      exact hR0
    · rw [h, mul_one, hcnorm]
      exact hentry ω.1 (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have hZsprod_int : ∀ (i j : Fin (m * n)) (a b c e : Fin (m + n)),
      Integrable (fun ω => Zs i ω a b * Zs j ω c e) μ₂ := by
    intro i j a b c e
    have hbd : ∀ᵐ ω ∂μ₂,
        ‖Zs i ω a b * Zs j ω c e‖ ≤ (3 * L / Real.sqrt ((m : ℝ) * p)) ^ 2 := by
      filter_upwards with ω
      rw [norm_mul]
      simpa only [pow_two] using
        mul_le_mul (hZs_ab_le i ω a b) (hZs_ab_le j ω c e) (norm_nonneg _) hR0
    exact MeasureTheory.Integrable.of_bound
      ((hZs_meas i a b).mul (hZs_meas j c e)).aestronglyMeasurable _ hbd
  have hXcov : ∀ (a b c e : Fin (m + n)),
      ∫ ω, Xmat ω a b * Xmat ω c e ∂μ₂
        = (((1 / (m : ℝ) : ℝ)) : ℂ)
            * (∑ i : Fin (m * n),
                (W (finProdFinEquiv.symm i)) a b * (W (finProdFinEquiv.symm i)) c e) := by
    intro a b c e
    have hinner : ∀ i : Fin (m * n),
        Integrable (fun ω => ∑ j : Fin (m * n), Zs i ω a b * Zs j ω c e) μ₂ :=
      fun i => MeasureTheory.integrable_finset_sum Finset.univ
        (fun j _ => hZsprod_int i j a b c e)
    have hcongr : (∫ ω, Xmat ω a b * Xmat ω c e ∂μ₂)
        = ∫ ω, ∑ i : Fin (m * n), ∑ j : Fin (m * n), Zs i ω a b * Zs j ω c e ∂μ₂ :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun ω => hXmul a b c e ω))
    rw [hcongr, MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hinner i)]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun j _ => hZsprod_int i j a b c e),
        hZs_inner i a b c e])]
    rw [← Finset.mul_sum]

  have hXnorm : ∀ (ω : Ω × ((Fin m × Fin n) → ℝ)),
      ‖Xmat ω‖
        = Statlib.HighDim.MatrixAnalysis.opNorm (maskedScaled p (XT ω.1) (Mask ω.1)) := by
    intro ω
    show ‖∑ i : Fin (m * n), Zs i ω‖ = _
    rw [hZs_sum ω]
    exact (hWlin (maskedScaled p (XT ω.1) (Mask ω.1))).2

  have hexp_t_pos : 0 < CD * Real.log ((m : ℝ) * (n : ℝ)) := mul_pos hCDpos hlogmn
  set K : Ω → (Fin m × Fin n → ℝ) :=
    fun ω ij => maskedScaled p (XT ω) (Mask ω) ij.1 ij.2 with hKdef
  have hmeasK : Measurable K := by
    show Measurable (fun ω (ij : Fin m × Fin n) => maskedScaled p (XT ω) (Mask ω) ij.1 ij.2)
    exact measurable_pi_lambda _ (fun ij => hAmeas ij.1 ij.2)
  have hfst_map : Measure.map Prod.fst μ₂ = μ := by
    rw [hμ₂, MeasureTheory.Measure.map_fst_prod, MeasureTheory.measure_univ, one_smul]
  have hKmap : Measure.map K μ
      = Measure.pi (fun ij => Measure.map (fun ω => maskedScaled p (XT ω) (Mask ω) ij.1 ij.2) μ) :=
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun ij : Fin m × Fin n => (hAmeas ij.1 ij.2).aemeasurable)).1 hAindep
  have hAlift : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω × ((Fin m × Fin n) → ℝ)) =>
      maskedScaled p (XT ω.1) (Mask ω.1) ij.1 ij.2) μ₂ := by
    have hmap : Measure.map (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
        fun ij : Fin m × Fin n => maskedScaled p (XT ω.1) (Mask ω.1) ij.1 ij.2) μ₂
        = Measure.pi (fun ij => Measure.map
            (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
              maskedScaled p (XT ω.1) (Mask ω.1) ij.1 ij.2) μ₂) := by
      have h1 : (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
          fun ij : Fin m × Fin n => maskedScaled p (XT ω.1) (Mask ω.1) ij.1 ij.2)
          = fun ω => K (Prod.fst ω) := rfl
      have hKfst : (fun ω : Ω × ((Fin m × Fin n) → ℝ) => K (Prod.fst ω))
          = K ∘ Prod.fst := rfl
      rw [h1, hKfst, ← MeasureTheory.Measure.map_map hmeasK measurable_fst, hfst_map, hKmap]
      refine congrArg Measure.pi (funext fun ij => ?_)
      have h2 : (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
          maskedScaled p (XT ω.1) (Mask ω.1) ij.1 ij.2)
          = (fun ω => maskedScaled p (XT ω) (Mask ω) ij.1 ij.2) ∘ Prod.fst := rfl
      rw [h2, ← MeasureTheory.Measure.map_map (hAmeas ij.1 ij.2) measurable_fst, hfst_map]
    exact (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun (ij : Fin m × Fin n) =>
        ((hAmeas ij.1 ij.2).comp measurable_fst).aemeasurable)).2 hmap

  have hZsindep_lift : iIndepFun (fun (ij : Fin m × Fin n)
      (ω : Ω × ((Fin m × Fin n) → ℝ)) =>
      ((maskedScaled p (XT ω.1) (Mask ω.1) ij.1 ij.2 : ℝ) : ℂ) • W ij) μ₂ := by
    refine hAlift.comp (fun ij (r : ℝ) => ((r : ℝ) : ℂ) • W ij) ?_
    intro ij
    refine measurable_pi_iff.mpr (fun a => ?_)
    refine measurable_pi_iff.mpr (fun b => ?_)
    exact Complex.ofRealCLM.measurable.mul_const _
  set G₀ : (Ω × ((Fin m × Fin n) → ℝ)) → Fin m → Fin n → ℝ :=
    fun ω i j => ω.2 (i, j) / Real.sqrt ((m : ℝ)) with hG₀
  have hG₀meas : ∀ (i : Fin m) (j : Fin n),
      Measurable fun ω : Ω × ((Fin m × Fin n) → ℝ) => G₀ ω i j := by
    intro i j
    show Measurable fun ω : Ω × ((Fin m × Fin n) → ℝ) => ω.2 (i, j) / Real.sqrt ((m : ℝ))
    exact ((measurable_pi_apply (i, j)).comp measurable_snd).div_const _
  have hZ0herm : (0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ).IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro a b
    simp
  have hd_two : 2 ≤ m + n := by omega
  have hZsindep_pair : iIndepFun (fun (ij : Fin m × Fin n)
      (ω : Ω × ((Fin m × Fin n) → ℝ)) => Zs (finProdFinEquiv ij) ω) μ₂ := by
    have h := hZsindep_lift
    simpa only [hZs, Equiv.symm_apply_apply] using h
  have hZsindep : iIndepFun (fun (i : Fin (m * n))
      (ω : Ω × ((Fin m × Fin n) → ℝ)) => Zs i ω) μ₂ :=
    ProbabilityTheory.iIndepFun.of_precomp
      (f := fun (i : Fin (m * n)) (ω : Ω × ((Fin m × Fin n) → ℝ)) => Zs i ω)
      (g := fun ij : Fin m × Fin n => finProdFinEquiv ij)
      finProdFinEquiv.surjective hZsindep_pair



  set Gmat : (Ω × ((Fin m × Fin n) → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun ω => ∑ q : Fin m × Fin n, (((G₀ ω q.1 q.2 : ℝ)) : ℂ) • W q with hGmat
  have hGherm : ∀ ω : Ω × ((Fin m × Fin n) → ℝ), (Gmat ω).IsHermitian :=
    fun ω => (hWlin (fun i j => G₀ ω i j)).1
  have hGmeas : ∀ (a b : Fin (m + n)),
      Measurable fun ω : Ω × ((Fin m × Fin n) → ℝ) => Gmat ω a b := by
    intro a b
    have hfun : (fun ω : Ω × ((Fin m × Fin n) → ℝ) => Gmat ω a b)
        = fun ω => ∑ q : Fin m × Fin n,
            (((G₀ ω q.1 q.2 : ℝ)) : ℂ) * (W q) a b := by
      funext ω
      simp only [hGmat, Matrix.sum_apply]
      rfl
    rw [hfun]
    exact Finset.measurable_sum _ (fun q _ =>
      (Complex.ofRealCLM.measurable.comp (hG₀meas q.1 q.2)).mul_const _)
  have hG_apply : ∀ (ω : Ω × ((Fin m × Fin n) → ℝ)) (a b : Fin (m + n)),
      Gmat ω a b = ∑ q : Fin m × Fin n, (((G₀ ω q.1 q.2 : ℝ)) : ℂ) * (W q) a b := by
    intro ω a b
    simp only [hGmat, Matrix.sum_apply]
    rfl
  have hGnorm : ∀ ω : Ω × ((Fin m × Fin n) → ℝ),
      ‖Gmat ω‖ = Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => G₀ ω i j) := by
    intro ω
    show ‖∑ q : Fin m × Fin n, (((G₀ ω q.1 q.2 : ℝ)) : ℂ) • W q‖ = _
    exact (hWlin (fun i j => G₀ ω i j)).2
  obtain ⟨hcoord_int, hcoord_mean, hcoordp_int, hcoordp_mean, hcoordsq, _⟩ :=
    statopia_math_node_1043732631_ea2639e2 (Fin m × Fin n)
  have hsnd_int : ∀ (g : (Fin m × Fin n → ℝ) → ℝ), Integrable g ν →
      ∫ ω : Ω × ((Fin m × Fin n) → ℝ), g ω.2 ∂μ₂ = ∫ g', g g' ∂ν := by
    intro g hg
    rw [hμ₂]
    rw [MeasureTheory.integral_prod (f := fun ω : Ω × ((Fin m × Fin n) → ℝ) => g ω.2)
      (MeasureTheory.Integrable.comp_snd hg μ)]
    simp
  have hG0_int : ∀ q : Fin m × Fin n,
      Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) => G₀ ω q.1 q.2) μ₂ := by
    intro q
    exact (MeasureTheory.Integrable.comp_snd (hcoord_int (q.1, q.2)) μ).div_const _
  have hG0_mean : ∀ q : Fin m × Fin n,
      ∫ ω : Ω × ((Fin m × Fin n) → ℝ), G₀ ω q.1 q.2 ∂μ₂ = 0 := by
    intro q
    have h1 : ∫ ω : Ω × ((Fin m × Fin n) → ℝ), ω.2 (q.1, q.2) ∂μ₂ = 0 := by
      rw [hsnd_int (fun g : (Fin m × Fin n) → ℝ => g (q.1, q.2)) (hcoord_int (q.1, q.2))]
      exact hcoord_mean (q.1, q.2)
    have hfun : (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
          ω.2 (q.1, q.2) / Real.sqrt ((m : ℝ)))
        = fun ω => ω.2 (q.1, q.2) * (Real.sqrt ((m : ℝ)))⁻¹ := by
      funext ω
      rw [div_eq_mul_inv]
    show ∫ ω : Ω × ((Fin m × Fin n) → ℝ), ω.2 (q.1, q.2) / Real.sqrt ((m : ℝ)) ∂μ₂ = 0
    rw [hfun, MeasureTheory.integral_mul_const, h1, zero_mul]
  have hGsummand_int : ∀ (q : Fin m × Fin n) (a b : Fin (m + n)),
      Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
        (((G₀ ω q.1 q.2 : ℝ)) : ℂ) * (W q) a b) μ₂ := by
    intro q a b
    have hc : Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
        ((G₀ ω q.1 q.2 : ℝ) : ℂ)) μ₂ := by
      refine MeasureTheory.Integrable.mono (hG0_int q).norm ?_ ?_
      · exact (Complex.ofRealCLM.measurable.comp (hG₀meas q.1 q.2)).aestronglyMeasurable
      · filter_upwards with ω
        rw [hcnorm]
        simp
    exact hc.mul_const _
  have hGmean : ∀ (a b : Fin (m + n)),
      ∫ ω, Gmat ω a b ∂μ₂ = ∫ ω, Xmat ω a b ∂μ₂ := by
    intro a b
    rw [hXmean a b]
    have hfun : (fun ω : Ω × ((Fin m × Fin n) → ℝ) => Gmat ω a b)
        = fun ω => ∑ q : Fin m × Fin n, (((G₀ ω q.1 q.2 : ℝ)) : ℂ) * (W q) a b := by
      funext ω
      exact hG_apply ω a b
    rw [hfun, MeasureTheory.integral_finset_sum Finset.univ
      (fun q _ => hGsummand_int q a b)]
    refine Finset.sum_eq_zero (fun q _ => ?_)
    rw [MeasureTheory.integral_mul_const, integral_complex_ofReal, hG0_mean q]
    simp
  have hGpair_int : ∀ q q' : Fin m × Fin n,
      Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) => ω.2 q * ω.2 q') μ₂ :=
    fun q q' => MeasureTheory.Integrable.comp_snd (hcoordp_int q q') μ
  have hG0pair_int : ∀ q q' : Fin m × Fin n,
      Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
        G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2) μ₂ := by
    intro q q'
    have hfun : (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
          G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2)
        = fun ω => ((Real.sqrt ((m : ℝ)))⁻¹ * (Real.sqrt ((m : ℝ)))⁻¹) *
            (ω.2 (q.1, q.2) * ω.2 (q'.1, q'.2)) := by
      funext ω
      simp only [hG₀, div_eq_mul_inv]
      ring
    rw [hfun]
    exact (hGpair_int (q.1, q.2) (q'.1, q'.2)).const_mul _
  have hG0pair_mean : ∀ q q' : Fin m × Fin n,
      ∫ ω : Ω × ((Fin m × Fin n) → ℝ), G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2 ∂μ₂
        = ((Real.sqrt ((m : ℝ)))⁻¹ * (Real.sqrt ((m : ℝ)))⁻¹) *
            (if q = q' then 1 else 0) := by
    intro q q'
    have hfun : (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
          G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2)
        = fun ω => ((Real.sqrt ((m : ℝ)))⁻¹ * (Real.sqrt ((m : ℝ)))⁻¹) *
            (ω.2 (q.1, q.2) * ω.2 (q'.1, q'.2)) := by
      funext ω
      simp only [hG₀, div_eq_mul_inv]
      ring
    rw [hfun, MeasureTheory.integral_const_mul,
      hsnd_int (fun g : (Fin m × Fin n → ℝ) => g (q.1, q.2) * g (q'.1, q'.2))
        (hcoordp_int (q.1, q.2) (q'.1, q'.2)),
      hcoordp_mean (q.1, q.2) (q'.1, q'.2)]
  have hGprod : ∀ (a b c e : Fin (m + n)),
      ∫ ω : Ω × ((Fin m × Fin n) → ℝ), Gmat ω a b * Gmat ω c e ∂μ₂
        = (((1 / (m : ℝ) : ℝ)) : ℂ)
            * (∑ i : Fin (m * n),
                (W (finProdFinEquiv.symm i)) a b * (W (finProdFinEquiv.symm i)) c e) := by
    intro a b c e
    have hmul : ∀ ω : Ω × ((Fin m × Fin n) → ℝ), Gmat ω a b * Gmat ω c e
        = ∑ q : Fin m × Fin n, ∑ q' : Fin m × Fin n,
            ((G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2 : ℝ) : ℂ) * ((W q) a b * (W q') c e) := by
      intro ω
      rw [hG_apply ω a b, hG_apply ω c e, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun q' _ => ?_))
      push_cast
      ring
    have hterm : ∀ q q' : Fin m × Fin n,
        Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
          ((G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2 : ℝ) : ℂ) * ((W q) a b * (W q') c e)) μ₂ := by
      intro q q'
      have h1 : Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
          ((G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2 : ℝ) : ℂ)) μ₂ := by
        refine MeasureTheory.Integrable.mono (hG0pair_int q q').norm ?_ ?_
        · exact (Complex.ofRealCLM.measurable.comp
            ((hG₀meas q.1 q.2).mul (hG₀meas q'.1 q'.2))).aestronglyMeasurable
        · filter_upwards with ω
          simp only [hcnorm, Real.norm_eq_abs, abs_abs]
          exact le_rfl
      exact h1.mul_const _
    have hcoef : ((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ : ℝ) = 1 / (m : ℝ) := by
      rw [← mul_inv, Real.mul_self_sqrt (le_of_lt hmpos), one_div]
    have hinner : ∀ q : Fin m × Fin n,
        Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
          ∑ q' : Fin m × Fin n,
            ((G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2 : ℝ) : ℂ) * ((W q) a b * (W q') c e)) μ₂ :=
      fun q => MeasureTheory.integrable_finset_sum Finset.univ (fun q' _ => hterm q q')
    have hcongr : (∫ ω : Ω × ((Fin m × Fin n) → ℝ), Gmat ω a b * Gmat ω c e ∂μ₂)
        = ∫ ω : Ω × ((Fin m × Fin n) → ℝ), ∑ q : Fin m × Fin n, ∑ q' : Fin m × Fin n,
            ((G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2 : ℝ) : ℂ) * ((W q) a b * (W q') c e) ∂μ₂ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hmul)
    have hval : ∀ q : Fin m × Fin n,
        (∫ ω : Ω × ((Fin m × Fin n) → ℝ), ∑ q' : Fin m × Fin n,
            ((G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2 : ℝ) : ℂ) * ((W q) a b * (W q') c e) ∂μ₂)
          = ((1 / (m : ℝ) : ℝ) : ℂ) * ((W q) a b * (W q) c e) := by
      intro q
      have hsum : (∫ ω : Ω × ((Fin m × Fin n) → ℝ), ∑ q' : Fin m × Fin n,
            ((G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2 : ℝ) : ℂ) * ((W q) a b * (W q') c e) ∂μ₂)
          = ∑ q' : Fin m × Fin n, ∫ ω : Ω × ((Fin m × Fin n) → ℝ),
              ((G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2 : ℝ) : ℂ) * ((W q) a b * (W q') c e) ∂μ₂ :=
        MeasureTheory.integral_finset_sum Finset.univ (fun q' _ => hterm q q')
      have htv : ∀ q' : Fin m × Fin n,
          (∫ ω : Ω × ((Fin m × Fin n) → ℝ),
              ((G₀ ω q.1 q.2 * G₀ ω q'.1 q'.2 : ℝ) : ℂ) * ((W q) a b * (W q') c e) ∂μ₂)
            = (↑((1 / (m : ℝ)) * (if q = q' then (1 : ℝ) else 0)) : ℂ) *
                ((W q) a b * (W q') c e) := by
        intro q'
        rw [MeasureTheory.integral_mul_const, integral_complex_ofReal, hG0pair_mean q q', hcoef]
      rw [hsum, Finset.sum_congr rfl (fun q' _ => htv q')]
      have hsingle : (∑ q' : Fin m × Fin n,
          (↑((1 / (m : ℝ)) * (if q = q' then (1 : ℝ) else 0)) : ℂ) *
            ((W q) a b * (W q') c e))
          = (↑(1 / (m : ℝ)) : ℂ) * ((W q) a b * (W q) c e) := by
        refine (Finset.sum_eq_single q ?_ ?_).trans ?_
        · intro q' _ hne
          rw [if_neg (Ne.symm hne), mul_zero, Complex.ofReal_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ q) h
        · rw [if_pos rfl, mul_one]
      rw [hsingle]
    rw [hcongr, MeasureTheory.integral_finset_sum Finset.univ (fun q _ => hinner q),
      Finset.sum_congr rfl (fun q _ => hval q)]
    rw [← Equiv.sum_comp (finProdFinEquiv (m := m) (n := n)).symm
      (fun q : Fin m × Fin n => ((1 / (m : ℝ) : ℝ) : ℂ) * ((W q) a b * (W q) c e))]
    rw [← Finset.mul_sum]
  have hGcov : ∀ (a b c e : Fin (m + n)),
      ∫ ω, (Gmat ω a b - ∫ ω', Gmat ω' a b ∂μ₂)
          * (Gmat ω c e - ∫ ω', Gmat ω' c e ∂μ₂) ∂μ₂
        = ∫ ω, (Xmat ω a b - ∫ ω', Xmat ω' a b ∂μ₂)
            * (Xmat ω c e - ∫ ω', Xmat ω' c e ∂μ₂) ∂μ₂ := by
    intro a b c e
    have h1 : (∫ ω', Gmat ω' a b ∂μ₂) = 0 := by rw [hGmean a b, hXmean a b]
    have h2 : (∫ ω', Gmat ω' c e ∂μ₂) = 0 := by rw [hGmean c e, hXmean c e]
    simp only [h1, h2, hXmean a b, hXmean c e, sub_zero]
    exact (hGprod a b c e).trans (hXcov a b c e).symm
  haveI hNem : NeZero (m + n) := ⟨by omega⟩


  have hlamG_le : ∀ (ω : Ω × ((Fin m × Fin n) → ℝ)),
      sSup (Set.range fun q : Fin (m + n) => (hGherm ω).eigenvalues q) ≤ ‖Gmat ω‖ := by
    intro ω
    refine Real.sSup_le (fun x hx => ?_) (norm_nonneg _)
    obtain ⟨q, rfl⟩ := hx
    have heq := statopia_math_node_1550178179_06242ca1 (m + n) (Gmat ω) (hGherm ω)
    calc (hGherm ω).eigenvalues q ≤ |(hGherm ω).eigenvalues q| := le_abs_self _
      _ ≤ ‖Gmat ω‖ := by
          rw [← heq]
          exact le_csSup (Set.finite_range _ |>.bddAbove) (Set.mem_range_self q)
  have habsX : ∀ (ω : Ω × ((Fin m × Fin n) → ℝ)),
      sSup (Set.range fun q : Fin (m + n) => |(hXherm ω).eigenvalues q|) = ‖Xmat ω‖ :=
    fun ω => statopia_math_node_1550178179_06242ca1 (m + n) (Xmat ω) (hXherm ω)
  have habsG : ∀ (ω : Ω × ((Fin m × Fin n) → ℝ)),
      sSup (Set.range fun q : Fin (m + n) => |(hGherm ω).eigenvalues q|) = ‖Gmat ω‖ :=
    fun ω => statopia_math_node_1550178179_06242ca1 (m + n) (Gmat ω) (hGherm ω)
  have hop_smul : ∀ (c : ℝ) (A : Matrix (Fin m) (Fin n) ℝ),
      Statlib.HighDim.MatrixAnalysis.opNorm (c • A)
        = |c| * Statlib.HighDim.MatrixAnalysis.opNorm A := by
    intro c A
    simp only [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2, Matrix.l2_opNorm_def,
      map_smul, norm_smul, Real.norm_eq_abs]




  have hopW_int : Integrable (fun g : (Fin m × Fin n) → ℝ =>
      Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => g (i, j))) ν :=
    statopia_math_node_288165421_707c7f6f m n
  have hGop_int : Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
      Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => G₀ ω i j)) μ₂ := by
    have hfun : (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
          Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => G₀ ω i j))
        = fun ω => (Real.sqrt ((m : ℝ)))⁻¹ *
            Statlib.HighDim.MatrixAnalysis.opNorm
              (((fun (i : Fin m) (j : Fin n) => ω.2 (i, j)) : Matrix (Fin m) (Fin n) ℝ)) := by
      funext ω
      have hsm : (fun i j => G₀ ω i j)
          = ((Real.sqrt ((m : ℝ)))⁻¹) •
              (((fun (i : Fin m) (j : Fin n) => ω.2 (i, j)) : Matrix (Fin m) (Fin n) ℝ)) := by
        funext i j
        show ω.2 (i, j) / Real.sqrt ((m : ℝ))
          = (Real.sqrt ((m : ℝ)))⁻¹ * ω.2 (i, j)
        rw [div_eq_mul_inv, mul_comm]

      rw [hsm, hop_smul, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 hmpos))]
    rw [hfun]
    exact MeasureTheory.Integrable.comp_snd (hopW_int.const_mul _) μ
  have hGmat_int : Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) => ‖Gmat ω‖) μ₂ := by
    have hfun : (fun ω : Ω × ((Fin m × Fin n) → ℝ) => ‖Gmat ω‖)
        = fun ω => Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => G₀ ω i j) := by
      funext ω
      exact hGnorm ω
    rw [hfun]
    exact hGop_int
  have hGpt : ∀ (ω : Ω × ((Fin m × Fin n) → ℝ)),
      ‖Gmat ω‖ = (Real.sqrt ((m : ℝ)))⁻¹ *
        Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => ω.2 (i, j)) := by
    intro ω
    rw [hGnorm ω]
    have hsm : (fun i j => G₀ ω i j)
        = ((Real.sqrt ((m : ℝ)))⁻¹) •
            (((fun (i : Fin m) (j : Fin n) => ω.2 (i, j)) : Matrix (Fin m) (Fin n) ℝ)) := by
      funext i j
      show ω.2 (i, j) / Real.sqrt ((m : ℝ)) = (Real.sqrt ((m : ℝ)))⁻¹ * ω.2 (i, j)
      rw [div_eq_mul_inv, mul_comm]
    rw [hsm, hop_smul, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 hmpos))]
  have hmeanG : (∫ ω : Ω × ((Fin m × Fin n) → ℝ), ‖Gmat ω‖ ∂μ₂)
      ≤ 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + Cw / Real.sqrt ((m : ℝ)) := by
    have hstep : (∫ ω : Ω × ((Fin m × Fin n) → ℝ), ‖Gmat ω‖ ∂μ₂)
        = (Real.sqrt ((m : ℝ)))⁻¹ *
            ∫ g : (Fin m × Fin n) → ℝ,
              Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => g (i, j)) ∂ν := by
      calc (∫ ω : Ω × ((Fin m × Fin n) → ℝ), ‖Gmat ω‖ ∂μ₂)
          = ∫ ω : Ω × ((Fin m × Fin n) → ℝ), (Real.sqrt ((m : ℝ)))⁻¹ *
              Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => ω.2 (i, j)) ∂μ₂ :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hGpt)
        _ = (Real.sqrt ((m : ℝ)))⁻¹ *
              ∫ ω : Ω × ((Fin m × Fin n) → ℝ),
                Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => ω.2 (i, j)) ∂μ₂ := by
            rw [MeasureTheory.integral_const_mul]
        _ = (Real.sqrt ((m : ℝ)))⁻¹ *
              ∫ g : (Fin m × Fin n) → ℝ,
                Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => g (i, j)) ∂ν := by
            rw [hsnd_int (fun g : (Fin m × Fin n) → ℝ =>
              Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => g (i, j))) hopW_int]
    rw [hstep]
    have hb := hCw m n (by omega) hn
    refine le_trans (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg _))) ?_
    have harith : (Real.sqrt ((m : ℝ)))⁻¹ *
          (Real.sqrt ((m : ℝ)) + Real.sqrt ((n : ℝ)) + Cw)
        = 1 + Real.sqrt ((n : ℝ)) / Real.sqrt ((m : ℝ)) + Cw / Real.sqrt ((m : ℝ)) := by
      have hmne : Real.sqrt ((m : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hmpos)
      rw [← div_eq_inv_mul, add_div, add_div, div_self hmne]
    rw [harith, ← Real.sqrt_div (le_of_lt hnpos) ((m : ℝ))]






  have hR : (0 : ℝ) ≤ 3 * L / Real.sqrt ((m : ℝ) * p) := hR0

  set lamX : (Ω × ((Fin m × Fin n) → ℝ)) → ℝ :=

    fun ω => sSup (Set.range fun i : Fin (m + n) => (hXherm ω).eigenvalues i) with hlamXdef
  have hlamX : ∀ ω : Ω × ((Fin m × Fin n) → ℝ),
      lamX ω = sSup (Set.range fun i : Fin (m + n) => (hXherm ω).eigenvalues i) :=
    fun ω => rfl
  set lamG : (Ω × ((Fin m × Fin n) → ℝ)) → ℝ :=
    fun ω => sSup (Set.range fun i : Fin (m + n) => (hGherm ω).eigenvalues i) with hlamGdef
  have hlamG : ∀ ω : Ω × ((Fin m × Fin n) → ℝ),
      lamG ω = sSup (Set.range fun i : Fin (m + n) => (hGherm ω).eigenvalues i) :=
    fun ω => rfl
  set sigmaStarX : ℝ := sSup {y : ℝ | ∃ p : (Fin (m + n) → ℝ) × (Fin (m + n) → ℝ),
      (∑ a : Fin (m + n), (p.1 a) ^ 2 = 1 ∧ ∑ b : Fin (m + n), (p.2 b) ^ 2 = 1) ∧
        y = Real.sqrt (∫ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
          (p.1 a : ℂ) * (Xmat ω a b - ∫ ω', Xmat ω' a b ∂μ₂) * (p.2 b : ℂ)‖ ^ 2 ∂μ₂)}
    with hsigmaStarXdef
  have hsigmaStarX : (0 : ℝ) ≤ sigmaStarX := by
    rw [hsigmaStarXdef]
    refine Real.sSup_nonneg ?_
    intro x hx
    obtain ⟨q, -, hq⟩ := hx
    rw [hq]
    exact Real.sqrt_nonneg _

  have hsection : ∀ (E' : Set (Ω × ((Fin m × Fin n) → ℝ))), MeasurableSet E' →
      (∀ (ω : Ω) (g g' : (Fin m × Fin n → ℝ)), (ω, g) ∈ E' ↔ (ω, g') ∈ E') →
      μ {ω : Ω | (ω, 0) ∈ E'} = μ₂ E' := by
    intro E' hE' hindep
    set S : Set Ω := {ω : Ω | (ω, 0) ∈ E'} with hS
    have hSmeas : MeasurableSet S :=
      hE'.preimage (measurable_id.prod measurable_const)
    have hpre : Prod.fst ⁻¹' S = E' := by
      ext y
      show Prod.fst y ∈ S ↔ y ∈ E'
      rw [hS]
      constructor
      · intro h
        exact (hindep (Prod.fst y) 0 (Prod.snd y)).1 h
      · intro h
        exact (hindep (Prod.fst y) (Prod.snd y) 0).1 h
    rw [← hfst_map, MeasureTheory.Measure.map_apply measurable_fst hSmeas, hpre]
  set S2 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=

    fun a b => ∫ ω, (∑ c : Fin (m + n), (Xmat ω a c - ∫ ω', Xmat ω' a c ∂μ₂) *
      (Xmat ω c b - ∫ ω', Xmat ω' c b ∂μ₂)) ∂μ₂ with hS2def
  have hS2herm : S2.IsHermitian := by
    rw [hS2def]
    refine Matrix.IsHermitian.ext ?_
    intro a b
    have hstar_eq : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun z => rfl
    rw [hstar_eq, ← integral_conj]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [← hstar_eq]
    have hH : ∀ x y : Fin (m + n), star (Xmat ω x y) = Xmat ω y x := by
      intro x y
      simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun (hXherm ω).eq y) x
    have hsum : star (∑ c : Fin (m + n), Xmat ω b c * Xmat ω c a)
        = ∑ c : Fin (m + n), Xmat ω a c * Xmat ω c b := by
      rw [star_sum]
      exact Finset.sum_congr rfl (fun c _ => by rw [star_mul, hH c a, hH b c])
    simpa only [hXmean, sub_zero] using hsum
  have hS2 : ∀ a b : Fin (m + n), S2 a b = ∫ ω, (∑ c : Fin (m + n),
      (Xmat ω a c - ∫ ω', Xmat ω' a c ∂μ₂) * (Xmat ω c b - ∫ ω', Xmat ω' c b ∂μ₂)) ∂μ₂ :=
    fun a b => rfl
  set sigmaX : ℝ := Real.sqrt (sSup (Set.range fun q : Fin (m + n) => |hS2herm.eigenvalues q|))
    with hsigmaXdef
  have hsigmaX : (0 : ℝ) ≤ sigmaX := by
    rw [hsigmaXdef]
    exact Real.sqrt_nonneg _

  have h16 : 16 ≤ m := by have := le_trans (le_max_left 17 Mnum) hM1; omega
  set Dl : (Ω × ((Fin m × Fin n) → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun ω => (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
      ((maskedScaled p (XT ω.1) (Mask ω.1)).map Complex.ofReal)
      (Matrix.transpose ((maskedScaled p (XT ω.1) (Mask ω.1)).map Complex.ofReal))
      (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm with hDl
  have hXeq : ∀ (ω : Ω × ((Fin m × Fin n) → ℝ)) (a b : Fin (m + n)),
      Xmat ω a b = Dl ω a b := by
    intro ω a b
    show (∑ i : Fin (m * n), Zs i ω) a b = Dl ω a b
    rw [hZs_sum ω, hWsum]
  have hAmeasL : ∀ (i : Fin m) (j : Fin n),
      Measurable fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
        maskedScaled p (XT ω.1) (Mask ω.1) i j :=
    fun i j => (hAmeas i j).comp measurable_fst
  have hAintL : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
        maskedScaled p (XT ω.1) (Mask ω.1) i j) μ₂ :=
    fun i j => MeasureTheory.Integrable.comp_fst (hAint i j) ν
  have hmeanL : ∀ (i : Fin m) (j : Fin n),
      ∫ ω : Ω × ((Fin m × Fin n) → ℝ),
        maskedScaled p (XT ω.1) (Mask ω.1) i j ∂μ₂ = 0 := by
    intro i j
    have h1 : (∫ ω : Ω × ((Fin m × Fin n) → ℝ),
          maskedScaled p (XT ω.1) (Mask ω.1) i j ∂μ₂)
        = ∫ ω : Ω × ((Fin m × Fin n) → ℝ),
            (fun x => maskedScaled p (XT x) (Mask x) i j) ω.1 ∂μ₂ := rfl
    rw [h1, hfst_int (fun x => maskedScaled p (XT x) (Mask x) i j) (hAint i j)]
    exact hmean i j
  have hcovL : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      ∫ ω : Ω × ((Fin m × Fin n) → ℝ), maskedScaled p (XT ω.1) (Mask ω.1) i j
          * maskedScaled p (XT ω.1) (Mask ω.1) k l ∂μ₂
        = if (i, j) = (k, l) then 1 / (m : ℝ) else 0 := by
    intro i j k l
    have h1 : (∫ ω : Ω × ((Fin m × Fin n) → ℝ), maskedScaled p (XT ω.1) (Mask ω.1) i j
          * maskedScaled p (XT ω.1) (Mask ω.1) k l ∂μ₂)
        = ∫ ω : Ω × ((Fin m × Fin n) → ℝ),
            (fun x => maskedScaled p (XT x) (Mask x) i j
              * maskedScaled p (XT x) (Mask x) k l) ω.1 ∂μ₂ := rfl
    rw [h1, hfst_int (fun x => maskedScaled p (XT x) (Mask x) i j
        * maskedScaled p (XT x) (Mask x) k l) ((hmom (i, j) (k, l)).2.2.1)]
    exact hsecond (i, j) (k, l)
  have hpintL : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      Integrable (fun ω : Ω × ((Fin m × Fin n) → ℝ) =>
        maskedScaled p (XT ω.1) (Mask ω.1) i j
          * maskedScaled p (XT ω.1) (Mask ω.1) k l) μ₂ :=
    fun i j k l => MeasureTheory.Integrable.comp_fst ((hmom (i, j) (k, l)).2.2.1) ν
  have hS2dil : ∀ a b : Fin (m + n), S2 a b = ∫ ω, (∑ c : Fin (m + n),
      Dl ω a c * Dl ω c b) ∂μ₂ := by
    intro a b
    rw [hS2 a b]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    exact Finset.sum_congr rfl (fun c _ => by
      rw [hXmean a c, sub_zero, hXmean c b, sub_zero, hXeq ω a c, hXeq ω c b])
  have hsigmaX_one : sigmaX = 1 := by
    have h := statopia_math_node_1598762335_905f24e9 m n hm hn hnm μ₂
      (fun ω a b => maskedScaled p (XT ω.1) (Mask ω.1) a b)
      hAintL hmeanL hcovL hpintL S2 hS2herm hS2dil
    rw [hsigmaXdef, h, Real.sqrt_one]
  have hIntEq : ∀ (q : (Fin (m + n) → ℝ) × (Fin (m + n) → ℝ)),
      (∫ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
        (q.1 a : ℂ) * (Xmat ω a b - ∫ ω', Xmat ω' a b ∂μ₂) * (q.2 b : ℂ)‖ ^ 2 ∂μ₂)
        = ∫ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
            (q.1 a : ℂ) * Dl ω a b * (q.2 b : ℂ)‖ ^ 2 ∂μ₂ := by
    intro q
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    have hsum : (∑ a : Fin (m + n), ∑ b : Fin (m + n),
        (q.1 a : ℂ) * (Xmat ω a b - ∫ ω', Xmat ω' a b ∂μ₂) * (q.2 b : ℂ))
        = ∑ a : Fin (m + n), ∑ b : Fin (m + n),
            (q.1 a : ℂ) * Dl ω a b * (q.2 b : ℂ) := by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [hXmean a b, sub_zero, hXeq ω a b]
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hsum
  have hSet : {y : ℝ | ∃ p : (Fin (m + n) → ℝ) × (Fin (m + n) → ℝ),
      (∑ a : Fin (m + n), (p.1 a) ^ 2 = 1 ∧ ∑ b : Fin (m + n), (p.2 b) ^ 2 = 1) ∧
        y = Real.sqrt (∫ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
          (p.1 a : ℂ) * (Xmat ω a b - ∫ ω', Xmat ω' a b ∂μ₂) * (p.2 b : ℂ)‖ ^ 2 ∂μ₂)}
      = {y : ℝ | ∃ v w : Fin (m + n) → ℝ,
        (∑ a : Fin (m + n), (v a) ^ 2 = 1 ∧ ∑ b : Fin (m + n), (w b) ^ 2 = 1) ∧
          y = Real.sqrt (∫ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
            (v a : ℂ) * Dl ω a b * (w b : ℂ)‖ ^ 2 ∂μ₂)} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1, q.2, hq, by rw [hIntEq q]⟩
    · rintro ⟨v, w, hvw, rfl⟩
      exact ⟨(v, w), hvw, by rw [← hIntEq (v, w)]⟩
  have hSigEq : sigmaStarX = sSup {y : ℝ | ∃ v w : Fin (m + n) → ℝ,
      (∑ a : Fin (m + n), (v a) ^ 2 = 1 ∧ ∑ b : Fin (m + n), (w b) ^ 2 = 1) ∧
      y = Real.sqrt (∫ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
        (v a : ℂ) * Dl ω a b * (w b : ℂ)‖ ^ 2 ∂μ₂)} := by
    rw [hsigmaStarXdef, hSet]
  have hsigmaStarSharp : sigmaStarX ≤ 2 / Real.sqrt ((m : ℝ)) := by
    rw [hSigEq]
    exact statopia_math_node_2447966418_633b2e4d m n h16 μ₂
      (fun ω a b => maskedScaled p (XT ω.1) (Mask ω.1) a b)
      hAmeasL hAintL hmeanL hcovL hpintL
  have hsigmaStarBound : sigmaStarX ≤ sigmaX := by
    rw [hsigmaX_one]
    refine le_trans hsigmaStarSharp ?_
    rw [div_le_iff₀ (Real.sqrt_pos.2 hmpos), one_mul]
    have h16' : (16:ℝ) ≤ (m:ℝ) := by exact_mod_cast h16
    have h2 : Real.sqrt (4:ℝ) ≤ Real.sqrt ((m:ℝ)) := Real.sqrt_le_sqrt (by linarith)
    have h4' : Real.sqrt (4:ℝ) = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h4'] at h2
  have hWreal : ∀ (q : Fin m × Fin n) (a b : Fin (m + n)), (W q a b).im = 0 := by
    intro q a b
    rcases hWentry q a b with h | h <;> simp only [h, Complex.zero_im, Complex.one_im]
  have hXreal : ∀ (ω : Ω × ((Fin m × Fin n) → ℝ)) (a b : Fin (m + n)),
      (Xmat ω a b).im = 0 := by
    intro ω a b
    change ((∑ i : Fin (m * n), Zs i ω) a b).im = 0
    simp only [Matrix.sum_apply, Complex.im_sum, hZs_apply, Complex.mul_im,
      Complex.ofReal_im, hWreal, mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  have hGreal : ∀ (ω : Ω × ((Fin m × Fin n) → ℝ)) (a b : Fin (m + n)),
      (Gmat ω a b).im = 0 := by
    intro ω a b
    rw [hG_apply]
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_im, hWreal,
      mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  have hGrep : ResidualSparseRepair20261106.HasStandardGaussianRepresentation μ₂
      (0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) Gmat := by
    have hsndmap : Measure.map (Prod.snd : Ω × ((Fin m × Fin n) → ℝ) →
        ((Fin m × Fin n) → ℝ)) μ₂ = ν := by
      rw [hμ₂, MeasureTheory.Measure.map_snd_prod, MeasureTheory.measure_univ, one_smul]
    have hlaw : ∀ q : Fin m × Fin n,
        Measure.map (fun ω : Ω × ((Fin m × Fin n) → ℝ) => ω.2 q) μ₂ = gaussianReal 0 1 := by
      intro q
      change Measure.map ((fun g : (Fin m × Fin n) → ℝ => g q) ∘ Prod.snd) μ₂ = _
      rw [← Measure.map_map (measurable_pi_apply q) measurable_snd, hsndmap]
      exact (MeasureTheory.measurePreserving_eval (fun _ : Fin m × Fin n => gaussianReal 0 1) q).map_eq
    have hpair : iIndepFun (fun q : Fin m × Fin n =>
        fun ω : Ω × ((Fin m × Fin n) → ℝ) => ω.2 q) μ₂ := by
      apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (fun q => ((measurable_pi_apply q).comp measurable_snd).aemeasurable)).2
      change Measure.map (Prod.snd : Ω × ((Fin m × Fin n) → ℝ) → ((Fin m × Fin n) → ℝ)) μ₂ = _
      rw [hsndmap]
      change Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) = _
      congr 1
      funext q
      exact (hlaw q).symm
    let gg : Fin (m * n) → (Ω × ((Fin m × Fin n) → ℝ)) → ℝ :=
      fun i ω => ω.2 (finProdFinEquiv.symm i)
    let BB : Fin (m * n) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
      fun i => (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) • W (finProdFinEquiv.symm i)
    refine ⟨m * n, gg, BB, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (measurable_pi_apply _).comp measurable_snd
    · exact ProbabilityTheory.iIndepFun.precomp
        (g := (finProdFinEquiv (m := m) (n := n)).symm)
        (finProdFinEquiv.symm.injective) hpair
    · intro i
      exact hlaw _
    · intro i
      refine Matrix.IsHermitian.ext ?_
      intro a b
      have hweq : star (W (finProdFinEquiv.symm i) b a) = W (finProdFinEquiv.symm i) a b := by
        simpa only [Matrix.conjTranspose_apply] using
          congrFun (congrFun (hWherm (finProdFinEquiv.symm i)).eq a) b
      change star (((Real.sqrt (m : ℝ))⁻¹ : ℝ) * W (finProdFinEquiv.symm i) b a) =
        (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) * W (finProdFinEquiv.symm i) a b
      rw [star_mul, hweq]
      simp [mul_comm]
    · intro ω
      rw [zero_add]
      change (∑ q : Fin m × Fin n, ((G₀ ω q.1 q.2 : ℝ) : ℂ) • W q) = _
      rw [← Equiv.sum_comp (finProdFinEquiv (m := m) (n := n)).symm
        (fun q : Fin m × Fin n => ((G₀ ω q.1 q.2 : ℝ) : ℂ) • W q)]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [gg, BB, hG₀, div_eq_mul_inv, Complex.ofReal_mul, smul_smul]
  have hexists_E : ∃ E : Set Ω,
      (∀ ω : Ω, 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + 1 * deltaM m <
          Statlib.HighDim.MatrixAnalysis.opNorm (maskedScaled p (XT ω) (Mask ω)) → ω ∈ E) ∧
      μ E ≤ ENNReal.ofReal
        (((m : ℝ) + (n : ℝ)) * Real.exp (-(CD * Real.log ((m : ℝ) * (n : ℝ))))) := by
    have hdev5 := hcite (d := m + n) (n := m * n) hd_two μ₂
      (0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) Zs Xmat Gmat
      hZ0herm hZs_herm hZs_meas hZs_int hZs_mean hZsindep hXmeas hGmeas hXherm hGherm
      hXreal hGreal hGrep
      (fun ω a b => by
        rw [hXdef ω]
        simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.zero_apply])
      hGmean hGcov (3 * L / Real.sqrt ((m : ℝ) * p)) sigmaX sigmaStarX hR0
      (fun ω i => by
        rw [statopia_math_node_1550178179_06242ca1 (m + n) (Zs i ω) (hZs_herm i ω)]
        exact hZs_entry i ω)
      S2 hS2herm hS2 hsigmaXdef hsigmaStarXdef hsigmaStarX hsigmaStarBound
    let t : ℝ := CD * Real.log ((m : ℝ) * (n : ℝ))
    let R : ℝ := 3 * L / Real.sqrt ((m : ℝ) * p)
    let B : ℝ := Ch * (sigmaStarX * Real.sqrt t +
      R ^ ((1 : ℝ) / 3) * sigmaX ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) + R * t)
    have hnum : Ch * (2 / Real.sqrt (m : ℝ) * Real.sqrt t +
        R ^ ((1 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) + R * t) +
        Cw / Real.sqrt (m : ℝ) ≤ deltaM m := by
      have hh := hMnum m n hm hn hnm (le_trans (le_max_right 17 Mnum) hM1)
        p hp0 hp1 hsparse
      simpa only [← hL, div_eq_mul_inv] using hh
    have hBnum : B + Cw / Real.sqrt (m : ℝ) ≤ deltaM m := by
      have hsg := mul_le_mul_of_nonneg_right hsigmaStarSharp (Real.sqrt_nonneg t)
      have hb : B ≤ Ch * (2 / Real.sqrt (m : ℝ) * Real.sqrt t +
          R ^ ((1 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) + R * t) := by
        dsimp only [B]
        rw [hsigmaX_one, Real.one_rpow, mul_one]
        apply mul_le_mul_of_nonneg_left _ hChpos.le
        linarith
      linarith
    have hdevnorm : μ₂ {ω | B < |‖Xmat ω‖ - ∫ ω', ‖Gmat ω'‖ ∂μ₂|} ≤
        ENNReal.ofReal (((m : ℝ) + (n : ℝ)) * Real.exp (-t)) := by
      have hh := hdev5 t hexp_t_pos.le
      simpa only [statopia_math_node_1550178179_06242ca1, Nat.cast_add] using hh
    let E' : Set (Ω × ((Fin m × Fin n) → ℝ)) :=
      {z | 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + deltaM m < ‖Xmat z‖}
    have hE'meas : MeasurableSet E' := by
      have hopMeas : Measurable (fun g : (Fin m × Fin n) → ℝ =>
          Statlib.HighDim.MatrixAnalysis.opNorm (fun i j => g (i, j))) := by
        let curry : ((Fin m × Fin n) → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ :=
          { toFun := fun g i j => g (i, j)
            map_add' := by intros; rfl
            map_smul' := by intros; rfl }
        let LL : ((Fin m × Fin n) → ℝ) →ₗ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
          (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap).toLinearMap.comp curry
        have hh := LL.toContinuousLinearMap.continuous.norm.measurable
        simpa only [LL, curry, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearMap.coe_mk, AddHom.coe_mk,
          Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2, Matrix.l2_opNorm_def] using hh
      have hnmeas : Measurable (fun z : Ω × ((Fin m × Fin n) → ℝ) => ‖Xmat z‖) := by
        have hh := hopMeas.comp (hmeasK.comp
          (measurable_fst : Measurable (Prod.fst : Ω × ((Fin m × Fin n) → ℝ) → Ω)))
        convert hh using 1
        funext z
        rw [hXnorm]
        rfl
      exact measurableSet_lt measurable_const hnmeas
    have hE'ind : ∀ (ω : Ω) (g g' : (Fin m × Fin n) → ℝ),
        (ω, g) ∈ E' ↔ (ω, g') ∈ E' := by
      intro ω g g'
      dsimp only [E', Set.mem_setOf_eq]
      simp only [hXnorm, Prod.fst]
    refine ⟨{ω : Ω | (ω, 0) ∈ E'}, ?_, ?_⟩
    · intro ω hω
      dsimp only [E', Set.mem_setOf_eq]
      rw [hXnorm]
      simpa only [one_mul] using hω
    · rw [hsection E' hE'meas hE'ind]
      refine le_trans (measure_mono ?_) hdevnorm
      intro z hz
      change B < |‖Xmat z‖ - ∫ ω', ‖Gmat ω'‖ ∂μ₂|
      have hz' : 1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + deltaM m < ‖Xmat z‖ := hz
      exact lt_of_lt_of_le (by linarith [hmeanG]) (le_abs_self _)


  exact hexists_E
  /- @proof-region region.target-node.session.e930d1af0357fa95 end -/

end Statlib.Imported

#print axioms Statlib.Imported.statopia_math_node_2034633510_f859b6bb

