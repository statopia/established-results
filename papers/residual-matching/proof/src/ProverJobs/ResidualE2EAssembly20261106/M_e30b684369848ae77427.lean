import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548
import ProverJobs.ResidualE2EAssembly20261106.M_8486a408c21974e4fcee
import ProverJobs.ResidualE2EAssembly20261106.M_89e6677ba7ddbfdc0536
import ProverJobs.ResidualE2EAssembly20261106.M_3b7837ec897a8f11f4d4
import ProverJobs.ResidualE2EAssembly20261106.M_7f3eea621b0d2e005d06
import ProverJobs.ResidualE2EAssembly20261106.M_eeb0c48628f53be1e6d9

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching





run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false in
theorem statopia_math_node_201159926_475d9972 : ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m)
    (hlog1 : 1 ≤ Real.log (m : ℝ))
    (r : ℕ) (hr : 0 < r) (hrn : 12 * r ≤ n) (hlast : r - 1 < n)
    (p sigma mu0 mu1 Lam th CLam Cthet : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hsig : 0 < sigma)
    (hmu0 : 0 < mu0) (hmu01 : mu0 ≤ mu1)
    (hLam_le : Lam ≤ CLam * Real.sqrt ((m : ℝ) / p))
    (hth_le : th ≤ Cthet * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)))
    (M0 : Matrix (Fin m) (Fin n) ℝ) (U0 : Matrix (Fin m) (Fin r) ℝ)
    (V0 : Matrix (Fin n) (Fin r) ℝ) (d0 : Fin r → ℝ)
    (hM0 : M0 = U0 * Matrix.diagonal d0 * Matrix.transpose V0)
    (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
    (hd0 : ∀ i : Fin r, 0 < d0 i) (hd0_anti : Antitone d0)
    (hlevU0 : ∀ i : Fin m, rowL2Sq U0 i ≤ mu0 * (r : ℝ) / (m : ℝ))
    (hlevV0 : ∀ j : Fin n, rowL2Sq V0 j ≤ mu0 * (r : ℝ) / (n : ℝ))
    (mask : Matrix (Fin m) (Fin n) ℝ)
    (hbin : ∀ (i : Fin m) (j : Fin n), mask i j = 0 ∨ mask i j = 1)
    (hGood :
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
        p Lam th mask U0 V0)
    (s_1 s_star kappa : ℝ)
    (h_s_1 : s_1 = psi hnm M0 ⟨0, hn⟩)
    (h_s_star : s_star = psi hnm M0 ⟨r - 1, hlast⟩)
    (hs_star_pos : 0 < s_star) (hkappa : kappa = s_1 / s_star)
    (CsampE : ℝ) (hCsampE_pos : 0 < CsampE)
    (h_samp : CsampE * kappa ^ 2 * (max mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)
        + (max mu0 mu1) ^ 2 * (r : ℝ) ^ 2) ≤ (n : ℝ) * p)
    (CM CCM C1 B : ℝ)
    (hCMdef : CM = 1 + 3 * C1) (hC1_ge1 : 1 ≤ C1)
    (hCCM_pos : 0 < CCM) (hCCM_le : CCM ≤ CsampE)
    (hBdef : B = CLam * max mu0 mu1 * (r : ℝ) / Real.sqrt ((n : ℝ) * p))
    (hBeta : 2 * C1 * B ≤ 1 / 2)
    (M : Matrix (Fin m) (Fin n) ℝ) (hMmem : M ∈ candidateSet r mu1)
    (hHard : sigma * Real.sqrt ((m : ℝ) / p) < s_1)
    (hDltb : spectralNorm (M - M0)
        ≤ 2 * C1 * (sigma * Real.sqrt ((m : ℝ) / p)) + 4 * C1 * B * s_1)
    (h165 : ∀ {Ωs : Type} [instOmS : MeasurableSpace Ωs] (mu : Measure Ωs)
      [IsProbabilityMeasure mu] (Om : Ωs → Matrix (Fin m) (Fin n) ℝ),
      (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Om ω i j) →
      ProbabilityTheory.iIndepFun (fun (ij : Fin m × Fin n) (ω : Ωs) => Om ω ij.1 ij.2) mu →
      (∀ (i : Fin m) (j : Fin n), mu {ω : Ωs | Om ω i j = 1} = ENNReal.ofReal p) →
      (∀ (i : Fin m) (j : Fin n) (ω : Ωs), Om ω i j = 0 ∨ Om ω i j = 1) →
      ∀ (ω : Ωs),
        PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.MaskEvent
            Lam th p (Om ω)
            (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.tangentSpace
              U0 V0) →
          PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.npCondition
              CCM mu0 mu1 d0 p m n →
            ∀ (M' : Matrix (Fin m) (Fin n) ℝ),
              PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.InLowRankClass
                  r mu1 M' →
                PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.spectralNorm
                    M' ≤
                  CM * PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.SMax
                    d0 →
                (p / 2) *
                    PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq
                      (M' - M0) ≤
                  PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq
                    (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.projMask
                                        (Om ω) (M' - M0))), (p / 2) * (frobNorm (M - M0)) ^ 2 ≤ (frobNorm (projMask mask (M - M0))) ^ 2 := by
  /- @proof-region region.target-node.session.f8604f66a2050324 begin -/
  intro m n hm hn hnm hlog1 r hr hrn hlast p sigma mu0 mu1 Lam th CLam Cthet hp hp1 hsig hmu0
    hmu01 hLam_le hth_le M0 U0 V0 d0 hM0 hU0 hV0 hd0 hd0_anti hlevU0 hlevV0 mask hbin hGood s_1
    s_star kappa h_s_1 h_s_star hs_star_pos hkappa CsampE hCsampE_pos h_samp CM CCM C1 B hCMdef
    hC1_ge1 hCCM_pos hCCM_le hBdef hBeta M hMmem hHard hDltb h165
  let Om : ((Fin m × Fin n) → ℝ) → Matrix (Fin m) (Fin n) ℝ :=
    fun ω i j => if ω (i, j) = 1 then (1 : ℝ) else 0
  let ω0 : (Fin m × Fin n) → ℝ := fun k => mask k.1 k.2
  have hOm0 : Om ω0 = mask := by
    ext i j
    dsimp only [Om, ω0]
    rcases hbin i j with h | h
    · simp [h]
    · simp [h]
  let muB : Measure ℝ :=
    ENNReal.ofReal p • Measure.dirac (1 : ℝ) + ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)
  haveI hμB : MeasureTheory.IsProbabilityMeasure muB := by
    constructor
    have hd1 : (Measure.dirac (1 : ℝ)) Set.univ = 1 := Measure.dirac_apply_of_mem (Set.mem_univ 1)
    have hd0 : (Measure.dirac (0 : ℝ)) Set.univ = 1 := Measure.dirac_apply_of_mem (Set.mem_univ 0)
    have hsum : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
      rw [← ENNReal.ofReal_add (le_of_lt hp) (by linarith : (0 : ℝ) ≤ 1 - p)]
      have hpp : p + (1 - p) = 1 := by ring
      rw [hpp, ENNReal.ofReal_one]
    simp only [muB, Measure.add_apply, Measure.smul_apply, hd1, hd0, smul_eq_mul, mul_one, hsum]
  let mu : Measure ((Fin m × Fin n) → ℝ) := Measure.pi (fun _ : Fin m × Fin n => muB)
  haveI hμ : MeasureTheory.IsProbabilityMeasure mu :=
    Measure.pi.instIsProbabilityMeasure (fun _ : Fin m × Fin n => muB)
  have hmeas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω : (Fin m × Fin n) → ℝ => Om ω i j := by
    intro i j
    have hset : MeasurableSet {ω : (Fin m × Fin n) → ℝ | ω (i, j) = 1} :=
      measurable_pi_apply (i, j) (measurableSet_singleton 1)
    have hind : (fun ω : (Fin m × Fin n) → ℝ => Om ω i j)
        = {ω : (Fin m × Fin n) → ℝ | ω (i, j) = 1}.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      dsimp only [Om]
      by_cases h : ω (i, j) = 1
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    rw [hind]
    exact Measurable.indicator measurable_const hset
  have hind : ProbabilityTheory.iIndepFun
      (fun (ij : Fin m × Fin n) (ω : (Fin m × Fin n) → ℝ) => Om ω ij.1 ij.2) mu := by
    have hX : ∀ ij : Fin m × Fin n,
        AEMeasurable (fun x : ℝ => if x = 1 then (1 : ℝ) else 0) muB := by
      intro ij
      have h1 : Measurable fun x : ℝ => if x = 1 then (1 : ℝ) else 0 := by
        have heq : (fun x : ℝ => if x = 1 then (1 : ℝ) else 0)
            = {x : ℝ | x = 1}.indicator (fun _ => (1 : ℝ)) := by
          funext x
          by_cases hx : x = 1
          · simp [Set.indicator, hx]
          · simp [Set.indicator, hx]
        rw [heq]
        exact Measurable.indicator measurable_const (measurableSet_singleton 1)
      exact h1.aemeasurable
    have hpi := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin m × Fin n => muB)
      (X := fun (_ : Fin m × Fin n) (x : ℝ) => if x = 1 then (1 : ℝ) else 0) hX
    simpa only [Om] using hpi
  have hmarg : ∀ (i : Fin m) (j : Fin n),
      mu {ω : (Fin m × Fin n) → ℝ | Om ω i j = 1} = ENNReal.ofReal p := by
    intro i j
    have hcoord : ∀ ω : (Fin m × Fin n) → ℝ, (Om ω i j = 1) ↔ ω (i, j) = 1 := by
      intro ω
      dsimp only [Om]
      by_cases h : ω (i, j) = 1
      · simp [h]
      · simp [h]
    have hset : {ω : (Fin m × Fin n) → ℝ | Om ω i j = 1}
        = Set.univ.pi
            (fun k : Fin m × Fin n => if k = (i, j) then ({1} : Set ℝ) else Set.univ) := by
      ext ω
      rw [Set.mem_setOf_eq, hcoord ω, Set.mem_univ_pi]
      constructor
      · intro h k
        by_cases hk : k = (i, j)
        · rw [if_pos hk, Set.mem_singleton_iff, hk]
          exact h
        · rw [if_neg hk]
          exact Set.mem_univ _
      · intro h
        have h' := h (i, j)
        rw [if_pos rfl, Set.mem_singleton_iff] at h'
        exact h'
    have hv : muB ({1} : Set ℝ) = ENNReal.ofReal p := by
      have hd1 : (Measure.dirac (1 : ℝ)) ({1} : Set ℝ) = 1 :=
        Measure.dirac_apply_of_mem (Set.mem_singleton 1)
      have hd0 : (Measure.dirac (0 : ℝ)) ({1} : Set ℝ) = 0 := by
        rw [Measure.dirac_apply' 0 (measurableSet_singleton 1)]
        simp
      simp only [muB, Measure.add_apply, Measure.smul_apply, hd1, hd0, smul_eq_mul, mul_one,
        mul_zero, add_zero]
    have h1 : ∀ b ∈ (Finset.univ : Finset (Fin m × Fin n)), b ≠ (i, j) →
        muB (if b = (i, j) then ({1} : Set ℝ) else Set.univ) = 1 := by
      intro b _ hb
      rw [if_neg hb]
      exact measure_univ
    have h2 : (i, j) ∉ (Finset.univ : Finset (Fin m × Fin n)) →
        muB (if (i, j) = (i, j) then ({1} : Set ℝ) else Set.univ) = 1 := by
      intro hc
      exact absurd (Finset.mem_univ (i, j)) hc
    rw [hset]
    dsimp only [mu]
    rw [Measure.pi_pi]
    rw [Finset.prod_eq_single (i, j) h1 h2]
    simp only [if_pos rfl]
    exact hv
  have hbin2 : ∀ (i : Fin m) (j : Fin n) (ω : (Fin m × Fin n) → ℝ), Om ω i j = 0 ∨ Om ω i j = 1 := by
    intro i j ω
    dsimp only [Om]
    split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hMask : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.MaskEvent
      Lam th p (Om ω0)
      (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.tangentSpace U0 V0) := by
    rw [hOm0]
    exact statopia_math_node_76282859_7583a873 p Lam th mask U0 V0 hGood
  have hCl := statopia_math_node_81579216_84cc7772 (hm := hm) (hn := hn) (hnm := hnm) (hr := hr)
    (hlast := hlast) (p := p) (sigma := sigma) (mu0 := mu0) (mu1 := mu1) (CM := CM) (CCM := CCM)
    (C1 := C1) (B := B) (s_1 := s_1) (s_star := s_star) (kappa := kappa) (CsampE := CsampE)
    (hp := hp) (hp1 := hp1) (hsig := hsig) (hmu0 := hmu0) (hmu01 := hmu01) (hlog1 := hlog1)
    (M0 := M0) (U0 := U0) (V0 := V0) (d0 := d0) (hM0 := hM0) (hU0 := hU0) (hV0 := hV0)
    (hd0 := hd0) (hd0_anti := hd0_anti) (h_s_1 := h_s_1) (h_s_star := h_s_star)
    (hs_star_pos := hs_star_pos) (hkappa := hkappa) (h_samp := h_samp) (hCMdef := hCMdef)
    (hC1_ge1 := hC1_ge1) (hCCM_pos := hCCM_pos) (hCCM_le := hCCM_le) (hBeta := hBeta)
    (hHard := hHard) (M := M) (hDltb := hDltb)
  have hnp : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.npCondition
      CCM mu0 mu1 d0 p m n := hCl.1
  have hIn : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.InLowRankClass
      r mu1 M := by
    obtain ⟨_hrank, k, U, V, d, hk, _hdpos, hU, hV, hM, hUrow, hVrow⟩ := hMmem
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · left
      subst hk0
      rw [hM]
      ext i j
      simp
    · right
      refine ⟨k, U, V, d, hkpos, hk, hU, hV, hM, ?_, ?_⟩
      · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
        have hb : (0 : ℝ) ≤ mu1 * (r : ℝ) / (m : ℝ) :=
          div_nonneg
            (mul_nonneg (le_trans (le_of_lt hmu0) hmu01) (Nat.cast_nonneg r))
            (Nat.cast_nonneg m)
        have hsup : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm
            U = ⨆ i : Fin m, Real.sqrt (rowL2Sq U i) := rfl
        have hbdd : BddAbove (Set.range (fun i : Fin m => Real.sqrt (rowL2Sq U i))) := by
          refine ⟨Real.sqrt (mu1 * (r : ℝ) / (m : ℝ)), ?_⟩
          rintro _ ⟨i, rfl⟩
          exact Real.sqrt_le_sqrt (hUrow i)
        have hle : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm
            U ≤ Real.sqrt (mu1 * (r : ℝ) / (m : ℝ)) := by
          rw [hsup]
          exact ciSup_le (fun i => Real.sqrt_le_sqrt (hUrow i))
        have hnn : (0 : ℝ)
            ≤ PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm
              U := by
          rw [hsup]
          exact (Real.sqrt_nonneg _).trans (le_ciSup hbdd ⟨0, hm⟩)
        have hsq : (Real.sqrt (mu1 * (r : ℝ) / (m : ℝ))) ^ 2 = mu1 * (r : ℝ) / (m : ℝ) :=
          Real.sq_sqrt hb
        nlinarith only [hle, hnn, hsq]
      · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        have hb : (0 : ℝ) ≤ mu1 * (r : ℝ) / (n : ℝ) :=
          div_nonneg
            (mul_nonneg (le_trans (le_of_lt hmu0) hmu01) (Nat.cast_nonneg r))
            (Nat.cast_nonneg n)
        have hsup : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm
            V = ⨆ j : Fin n, Real.sqrt (rowL2Sq V j) := rfl
        have hbdd : BddAbove (Set.range (fun j : Fin n => Real.sqrt (rowL2Sq V j))) := by
          refine ⟨Real.sqrt (mu1 * (r : ℝ) / (n : ℝ)), ?_⟩
          rintro _ ⟨j, rfl⟩
          exact Real.sqrt_le_sqrt (hVrow j)
        have hle : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm
            V ≤ Real.sqrt (mu1 * (r : ℝ) / (n : ℝ)) := by
          rw [hsup]
          exact ciSup_le (fun j => Real.sqrt_le_sqrt (hVrow j))
        have hnn : (0 : ℝ)
            ≤ PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.twoInfNorm
              V := by
          rw [hsup]
          exact (Real.sqrt_nonneg _).trans (le_ciSup hbdd ⟨0, hn⟩)
        have hsq : (Real.sqrt (mu1 * (r : ℝ) / (n : ℝ))) ^ 2 = mu1 * (r : ℝ) / (n : ℝ) :=
          Real.sq_sqrt hb
        nlinarith only [hle, hnn, hsq]
  have hspec : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.spectralNorm M
      ≤ CM * PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.SMax d0 := hCl.2
  have hmain := h165 mu Om hmeas hind hmarg hbin2 ω0 hMask hnp M hIn hspec
  have hRSC : (p / 2) *
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq (M - M0)
      ≤ PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq
        (PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.projMask
          mask (M - M0)) := by
    rw [hOm0] at hmain
    exact hmain
  have hconv2 : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.projMask
      mask (M - M0) = projMask mask (M - M0) := rfl
  have hconv1 : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq
      (M - M0) = (frobNorm (M - M0)) ^ 2 := by
    have hnn : (0 : ℝ) ≤ ∑ i : Fin m, ∑ j : Fin n, (M - M0) i j ^ 2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    simp only [frobNorm, Statlib.HighDim.MatrixAnalysis.frobeniusNorm,
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq]
    rw [Real.sq_sqrt hnn]
  have hconv3 : PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq
      (projMask mask (M - M0)) = (frobNorm (projMask mask (M - M0))) ^ 2 := by
    have hnn : (0 : ℝ) ≤ ∑ i : Fin m, ∑ j : Fin n, (projMask mask (M - M0)) i j ^ 2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    simp only [frobNorm, Statlib.HighDim.MatrixAnalysis.frobeniusNorm,
      PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported.frobSq]
    rw [Real.sq_sqrt hnn]
  rw [hconv2] at hRSC
  rw [hconv1, hconv3] at hRSC
  exact hRSC
  /- @proof-region region.target-node.session.f8604f66a2050324 end -/

end Statlib.Imported

