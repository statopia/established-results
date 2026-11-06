import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548
import ProverJobs.ResidualE2EAssembly20261106.M_faf850de1c7aeae55a9f
import ProverJobs.ResidualE2EAssembly20261106.M_420ada0a005e01361335
import ProverJobs.ResidualE2EAssembly20261106.M_7f3eea621b0d2e005d06

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
theorem statopia_math_node_2171761119_a4c573e9 : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m)
    (r : ℕ) (hr : 0 < r) (hrn : 12 * r ≤ n)
    (p sigma K c Ks C_L CLam mu0 mu1 Lam th : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hsig : 0 < sigma) (hK : 1 ≤ K) (hc : 0 < c)
    (hCLam : 1 ≤ CLam) (hmu0 : 0 < mu0) (hmu01 : mu0 ≤ mu1)
    (hLam_le : Lam ≤ CLam * Real.sqrt ((m : ℝ) / p))
    (M0 : Matrix (Fin m) (Fin n) ℝ) (U0 : Matrix (Fin m) (Fin r) ℝ)
    (V0 : Matrix (Fin n) (Fin r) ℝ) (d0 : Fin r → ℝ)
    (hM0 : M0 = U0 * Matrix.diagonal d0 * Matrix.transpose V0)
    (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
    (hd0 : ∀ i : Fin r, 0 < d0 i)
    (hlevU0 : ∀ i : Fin m, rowL2Sq U0 i ≤ mu0 * (r : ℝ) / (m : ℝ))
    (hlevV0 : ∀ j : Fin n, rowL2Sq V0 j ≤ mu0 * (r : ℝ) / (n : ℝ))
    (mask H M : Matrix (Fin m) (Fin n) ℝ)
    (hbin : ∀ (i : Fin m) (j : Fin n), mask i j = 0 ∨ mask i j = 1)
    (hGood : PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent
      p Lam th mask U0 V0)
    (lamHat : Fin n → ℝ)
    (hnoise : spectralNorm (projMask mask H) ≤ K * sigma * Real.sqrt ((m : ℝ) * p))
    (hlam1 : lamHat ⟨0, hn⟩ ≤ K * Real.sqrt p)
    (hbulk : c * (n : ℝ) * Real.sqrt p ≤ ∑ i ∈ bulkIdx n, lamHat i)
    (hMmem : M ∈ candidateSet r mu1)
    (w : Fin n → ℝ) (hw_nn : ∀ i : Fin n, 0 ≤ w i) (hw0 : 0 < w ⟨0, hn⟩)
    (hloss : normLoss hnm p w lamHat (obsMatrix mask M0 H) mask M
      ≤ ((C_L * w ⟨0, hn⟩ : ℝ) : WithTop ℝ))
    (hrank : Matrix.rank (M - M0) ≤ 2 * r)
    (C1 B : ℝ)
    (hC1spec : K + (K + Real.sqrt C_L) * (max K (max Ks 1) + 1) / c + 1 ≤ C1)
    (hC1_ge1 : 1 ≤ C1)
    (hBdef : B = CLam * max mu0 mu1 * (r : ℝ) / Real.sqrt ((n : ℝ) * p))
    (hbeta : 2 * C1 * B ≤ 1 / 2),
    spectralNorm (M - M0)
      ≤ 2 * C1 * (sigma * Real.sqrt ((m : ℝ) / p)) + 4 * C1 * B * spectralNorm M0 := by
  /- @proof-region region.target-node.session.cdf1189b93fc659b begin -/
  intro m n hm hn hnm r hr hrn p sigma K c Ks C_L CLam mu0 mu1 Lam th
    hp hp1 hsig hK hc hCLam hmu0 hmu01 hLam_le M0 U0 V0 d0 hM0 hU0 hV0 hd0 hlevU0 hlevV0
    mask H M hbin hGood lamHat hnoise hlam1 hbulk hMmem w hw_nn hw0 hloss hrank C1 B
    hC1spec hC1_ge1 hBdef hbeta
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hpne : p ≠ 0 := ne_of_gt hp
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hm0
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hn0
  have hp_inv_nonneg : 0 ≤ (p:ℝ)⁻¹ := le_of_lt (inv_pos.mpr hp)
  have hc_inv_nonneg : 0 ≤ c⁻¹ := le_of_lt (inv_pos.mpr hc)
  have hKs : 0 ≤ K + Real.sqrt C_L := by
    have h := Real.sqrt_nonneg C_L; linarith
  have hspecnn : ∀ (A : Matrix (Fin m) (Fin n) ℝ), 0 ≤ spectralNorm A := by
    intro A
    unfold spectralNorm
    split_ifs with h
    · exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties A
        (Or.inl ⟨⟨0, lt_of_lt_of_le h (Nat.min_le_left m n)⟩⟩)).2.1 ⟨0, h⟩
    · exact le_refl 0
  have hmin : 0 < min m n := by rw [Nat.min_eq_right hnm]; exact hn
  have hne_mn : Nonempty (Fin m) ∨ Nonempty (Fin n) := Or.inr ⟨⟨0, hn⟩⟩
  have hop : ∀ (A : Matrix (Fin m) (Fin n) ℝ),
      Statlib.HighDim.MatrixAnalysis.opNorm A = spectralNorm A := by
    intro A
    have h3 : Statlib.HighDim.MatrixAnalysis.singularValues A ⟨0, hmin⟩ = spectralNorm A := by
      unfold spectralNorm
      rw [dif_pos hmin]
    exact (Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 A).trans
      (((Statlib.HighDim.MatrixAnalysis.singular_value_properties A hne_mn).1 hmin).symm.trans h3)
  have hop_smul : ∀ (c0 : ℝ) (X : Matrix (Fin m) (Fin n) ℝ), 0 ≤ c0 →
      Statlib.HighDim.MatrixAnalysis.opNorm (c0 • X)
        = c0 * Statlib.HighDim.MatrixAnalysis.opNorm X := by
    intro c0 X hc0
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2,
      Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2,
      Matrix.l2_opNorm_def, Matrix.l2_opNorm_def, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hc0]
  have hop_sub : ∀ (X Y : Matrix (Fin m) (Fin n) ℝ),
      Statlib.HighDim.MatrixAnalysis.opNorm (X - Y)
        ≤ Statlib.HighDim.MatrixAnalysis.opNorm X
          + Statlib.HighDim.MatrixAnalysis.opNorm Y := by
    intro X Y
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2,
      Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2,
      Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2,
      Matrix.l2_opNorm_def, Matrix.l2_opNorm_def, Matrix.l2_opNorm_def, map_sub]
    exact norm_sub_le _ _
  have hcross : Real.sqrt ((m:ℝ)/p) * Real.sqrt ((n:ℝ)*p) = Real.sqrt ((m:ℝ)*(n:ℝ)) := by
    rw [← Real.sqrt_mul (le_of_lt (by positivity : (0:ℝ) < (m:ℝ)/p))]
    congr 1
    field_simp
  have hratio : Real.sqrt ((m:ℝ)/p) / Real.sqrt ((m:ℝ)*(n:ℝ)) = 1 / Real.sqrt ((n:ℝ)*p) := by
    rw [div_eq_div_iff (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
      (ne_of_gt (Real.sqrt_pos.2 (by positivity))), one_mul, hcross]
  have hsqrtsplit : Real.sqrt ((m:ℝ)*p) = Real.sqrt ((m:ℝ)/p) * p := by
    rw [show (m:ℝ)*p = ((m:ℝ)/p) * p^2 by field_simp]
    rw [Real.sqrt_mul (le_of_lt (by positivity : (0:ℝ) < (m:ℝ)/p)), Real.sqrt_sq (le_of_lt hp)]
  have hprobe : ∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
      spectralNorm ((p:ℝ)⁻¹ • projMask mask (L * Matrix.transpose R) - L * Matrix.transpose R)
        ≤ Lam * Real.sqrt (twoInfNormSq L) * Real.sqrt (twoInfNormSq R) := by
    intro k L R
    haveI hne_m : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    haveI hne_n : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hG := hGood
    unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.GoodEvent at hG
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hG
    have h4 := hg4 k L R
    simp only [PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.specNorm,
      PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.rowNorm,
      twoInfNormSq, spectralNorm, dif_pos hmin] at h4 hg1 ⊢
    have hLam0 : 0 ≤ Lam := le_trans (norm_nonneg _) hg1
    have hT : (p:ℝ)⁻¹ • projMask mask (L * Matrix.transpose R) - L * Matrix.transpose R
        = PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask p mask
            (L * Matrix.transpose R) := by
      unfold PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Tmask
        PaperProofTasks.job_paper_45fc93d926fd4099b9973daee59eb529.Statlib.Imported.Wmask
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, projMask]
      ring
    have hLHS := ((Statlib.HighDim.MatrixAnalysis.singular_value_properties
        ((p:ℝ)⁻¹ • projMask mask (L * Matrix.transpose R) - L * Matrix.transpose R) hne_mn).1
        hmin).trans
      (Matrix.l2_opNorm_def
        ((p:ℝ)⁻¹ • projMask mask (L * Matrix.transpose R) - L * Matrix.transpose R))
    have hRL : (⨆ i : Fin m, Real.sqrt (∑ j : Fin k, L i j ^ 2))
        ≤ Real.sqrt (sSup (Set.range (rowL2Sq L))) := by
      refine ciSup_le (fun i => Real.sqrt_le_sqrt ?_)
      have hb : rowL2Sq L i ≤ sSup (Set.range (rowL2Sq L)) :=
        le_csSup (Set.finite_range (rowL2Sq L)).bddAbove (Set.mem_range_self i)
      rwa [show rowL2Sq L i = ∑ j : Fin k, L i j ^ 2 from rfl] at hb
    have hRR : (⨆ i : Fin n, Real.sqrt (∑ j : Fin k, R i j ^ 2))
        ≤ Real.sqrt (sSup (Set.range (rowL2Sq R))) := by
      refine ciSup_le (fun i => Real.sqrt_le_sqrt ?_)
      have hb : rowL2Sq R i ≤ sSup (Set.range (rowL2Sq R)) :=
        le_csSup (Set.finite_range (rowL2Sq R)).bddAbove (Set.mem_range_self i)
      rwa [show rowL2Sq R i = ∑ j : Fin k, R i j ^ 2 from rfl] at hb
    have hRHS : (Lam * (⨆ i : Fin m, Real.sqrt (∑ j : Fin k, L i j ^ 2))) *
          (⨆ i : Fin n, Real.sqrt (∑ j : Fin k, R i j ^ 2))
        ≤ Lam * Real.sqrt (sSup (Set.range (rowL2Sq L))) *
            Real.sqrt (sSup (Set.range (rowL2Sq R))) := by
      have h2 : 0 ≤ (⨆ i : Fin n, Real.sqrt (∑ j : Fin k, R i j ^ 2)) :=
        le_trans (Real.sqrt_nonneg _)
          (le_ciSup (f := fun i : Fin n => Real.sqrt (∑ j : Fin k, R i j ^ 2))
            (Set.finite_range _).bddAbove ⟨0, hn⟩)
      have h1 : Lam * (⨆ i : Fin m, Real.sqrt (∑ j : Fin k, L i j ^ 2))
          ≤ Lam * Real.sqrt (sSup (Set.range (rowL2Sq L))) :=
        mul_le_mul_of_nonneg_left hRL hLam0
      exact mul_le_mul h1 hRR h2 (mul_nonneg hLam0 (Real.sqrt_nonneg _))
    rw [hLHS, hT]
    exact le_trans h4 hRHS
  have hMmem' : CandidateClass r mu1 M := by
    simpa only [candidateSet, Set.mem_setOf_eq] using hMmem
  obtain ⟨hMrank, kk, UU, VV, dd, hk, hdd, hUU, hVV, hMM, hlevU, hlevV⟩ := hMmem'
  have hE : spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))
      ≤ 2 * B * (spectralNorm M0 + spectralNorm (M - M0)) := by
    have hLamnn : 0 ≤ CLam * Real.sqrt ((m:ℝ)/p) :=
      mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have hSchur : ∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
        spectralNorm ((p:ℝ)⁻¹ • projMask mask (L * Matrix.transpose R) - L * Matrix.transpose R)
          ≤ (CLam * Real.sqrt ((m:ℝ)/p)) * Real.sqrt (twoInfNormSq L)
            * Real.sqrt (twoInfNormSq R) := by
      intro k L R
      refine le_trans (hprobe k L R) ?_
      have h1 : 0 ≤ Real.sqrt (twoInfNormSq L) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt (twoInfNormSq R) := Real.sqrt_nonneg _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLam_le h1) h2
    have h2550 := statopia_math_node_2550844442_8211841b m n hn hnm r hr p mu0 mu1
      (CLam * Real.sqrt ((m:ℝ)/p)) hp hp1 hmu0 hmu01 hLamnn mask hbin hSchur
      M0 U0 V0 d0 hM0 hU0 hV0 hd0 hlevU0 hlevV0 M hMrank hMmem kk UU VV dd hk hMM hUU hVV
      hdd hlevU hlevV
    have hcoef : (CLam * Real.sqrt ((m:ℝ)/p)) * max mu0 mu1 * (r:ℝ) / Real.sqrt ((m:ℝ)*(n:ℝ))
        = CLam * max mu0 mu1 * (r:ℝ) / Real.sqrt ((n:ℝ)*p) := by
      have h1 : (CLam * Real.sqrt ((m:ℝ)/p)) * max mu0 mu1 * (r:ℝ) / Real.sqrt ((m:ℝ)*(n:ℝ))
          = (CLam * max mu0 mu1 * (r:ℝ)) *
              (Real.sqrt ((m:ℝ)/p) / Real.sqrt ((m:ℝ)*(n:ℝ))) := by
        field_simp
      rw [h1, hratio, one_div, div_eq_mul_inv]
    rw [hBdef]
    calc spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))
        ≤ 2 * ((CLam * Real.sqrt ((m:ℝ)/p)) * max mu0 mu1 * (r:ℝ)
            / Real.sqrt ((m:ℝ)*(n:ℝ))) *
            (spectralNorm M0 + spectralNorm (M - M0)) := h2550
      _ = 2 * (CLam * max mu0 mu1 * (r:ℝ) / Real.sqrt ((n:ℝ)*p)) *
            (spectralNorm M0 + spectralNorm (M - M0)) := by rw [hcoef]
  have hres : Statlib.HighDim.MatrixAnalysis.opNorm (obsMatrix mask M0 H - projMask mask M)
      ≤ (K + Real.sqrt C_L) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M *
          Real.sqrt ((m:ℝ)*p) := by
    have h1461 := statopia_math_node_1461725421_1cd7d47b m n r hn hnm hr hrn p sigma K c
      hp hp1 hsig hK hc mask H M0 M hbin lamHat hrank hnoise hbulk
    obtain ⟨hsHat_nn, hsHat_le⟩ := h1461
    have hsig0 : sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M ≠ 0 := by
      intro h0
      rw [normLoss, if_pos h0] at hloss
      exact absurd hloss (not_le.mpr (WithTop.coe_lt_top (C_L * w ⟨0, hn⟩)))
    have hsigpos : 0 < sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M :=
      lt_of_le_of_ne hsHat_nn (Ne.symm hsig0)
    have hpos : 0 < Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M :=
      mul_pos (Real.sqrt_pos.2 hm0) hsigpos
    have hpsi_top : ∀ (A : Matrix (Fin m) (Fin n) ℝ), psi hnm A ⟨0, hn⟩ = spectralNorm A := by
      intro A
      have hcast : Fin.cast (Nat.min_eq_right hnm).symm ⟨0, hn⟩ = (⟨0, hmin⟩ : Fin (min m n)) :=
        Fin.ext rfl
      have hsv : Statlib.HighDim.MatrixAnalysis.singularValues A ⟨0, hmin⟩
          = Statlib.HighDim.MatrixAnalysis.opNorm A :=
        ((Statlib.HighDim.MatrixAnalysis.singular_value_properties A hne_mn).1 hmin).trans
          (Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 A).symm
      show Statlib.HighDim.MatrixAnalysis.singularValues A
          (Fin.cast (Nat.min_eq_right hnm).symm ⟨0, hn⟩) = spectralNorm A
      rw [hcast, hsv]
      exact hop A
    have hlossr : (p:ℝ)⁻¹ * weightedLoss hnm w lamHat
        (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
          / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M))
        ≤ C_L * w ⟨0, hn⟩ := by
      rw [normLoss, if_neg hsig0] at hloss
      exact WithTop.coe_le_coe.mp hloss
    have hsingle : w ⟨0, hn⟩ *
          (psi hnm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
            / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) ⟨0, hn⟩
            - lamHat ⟨0, hn⟩) ^ 2
        ≤ weightedLoss hnm w lamHat
            (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
              / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) := by
      have hsum := Finset.single_le_sum
        (f := fun i => w i * (psi hnm (fun i j =>
            (obsMatrix mask M0 H - projMask mask M) i j
              / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) i
            - lamHat i) ^ 2)
        (fun i _ => mul_nonneg (hw_nn i) (sq_nonneg _)) (Finset.mem_univ ⟨0, hn⟩)
      simpa only [weightedLoss] using hsum
    have h1 : (p:ℝ)⁻¹ *
          (w ⟨0, hn⟩ * (psi hnm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
            / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) ⟨0, hn⟩
            - lamHat ⟨0, hn⟩) ^ 2)
        ≤ C_L * w ⟨0, hn⟩ :=
      le_trans (mul_le_mul_of_nonneg_left hsingle (le_of_lt (inv_pos.mpr hp))) hlossr
    have h2 : (psi hnm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
            / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) ⟨0, hn⟩
            - lamHat ⟨0, hn⟩) ^ 2 ≤ p * C_L := by
      have hmul : w ⟨0, hn⟩ *
            (psi hnm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
              / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) ⟨0, hn⟩
              - lamHat ⟨0, hn⟩) ^ 2 ≤ (p * C_L) * w ⟨0, hn⟩ := by
        have hh := mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
        calc w ⟨0, hn⟩ *
              (psi hnm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
                / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) ⟨0, hn⟩
                - lamHat ⟨0, hn⟩) ^ 2
            = p * ((p:ℝ)⁻¹ * (w ⟨0, hn⟩ *
              (psi hnm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
                / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) ⟨0, hn⟩
                - lamHat ⟨0, hn⟩) ^ 2)) := by field_simp
          _ ≤ p * (C_L * w ⟨0, hn⟩) := hh
          _ = (p * C_L) * w ⟨0, hn⟩ := by ring
      nlinarith [hmul, hw0]
    have h4 : |psi hnm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
            / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) ⟨0, hn⟩
            - lamHat ⟨0, hn⟩| ≤ Real.sqrt (p * C_L) := by
      have hh := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq_eq_abs] at hh
    have h3 : psi hnm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
            / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) ⟨0, hn⟩
        ≤ (K + Real.sqrt C_L) * Real.sqrt p := by
      have h5 : psi hnm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
              / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) ⟨0, hn⟩
          ≤ lamHat ⟨0, hn⟩ + Real.sqrt (p * C_L) := by
        have hle := (abs_le.mp h4).2
        linarith only [hle]
      have h6 : Real.sqrt (p * C_L) = Real.sqrt p * Real.sqrt C_L :=
        Real.sqrt_mul (le_of_lt hp) C_L
      linarith only [h5, hlam1, h6]
    have hspecN : spectralNorm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
            / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M))
        = (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)⁻¹ *
            Statlib.HighDim.MatrixAnalysis.opNorm (obsMatrix mask M0 H - projMask mask M) := by
      have hscaled : Statlib.HighDim.MatrixAnalysis.opNorm
            ((Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)⁻¹ •
              (obsMatrix mask M0 H - projMask mask M))
          = (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)⁻¹ *
              Statlib.HighDim.MatrixAnalysis.opNorm (obsMatrix mask M0 H - projMask mask M) :=
        hop_smul _ _ (le_of_lt (inv_pos.mpr hpos))
      rw [← hop, ← hscaled]
      congr 1
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    have hNop : Statlib.HighDim.MatrixAnalysis.opNorm (obsMatrix mask M0 H - projMask mask M)
        = (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M) *
          spectralNorm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
            / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) := by
      rw [hspecN, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
    have h9 : spectralNorm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
            / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M))
        ≤ (K + Real.sqrt C_L) * Real.sqrt p := by
      rw [← hpsi_top]
      exact h3
    calc Statlib.HighDim.MatrixAnalysis.opNorm (obsMatrix mask M0 H - projMask mask M)
        = (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M) *
            spectralNorm (fun i j => (obsMatrix mask M0 H - projMask mask M) i j
              / (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M)) := hNop
      _ ≤ (Real.sqrt (m:ℝ) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M) *
            ((K + Real.sqrt C_L) * Real.sqrt p) :=
          mul_le_mul_of_nonneg_left h9 (le_of_lt hpos)
      _ = (K + Real.sqrt C_L) *
            (sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M * Real.sqrt ((m:ℝ)*p)) := by
          rw [Real.sqrt_mul (le_of_lt hm0)]
          ring
      _ = (K + Real.sqrt C_L) * sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M *
            Real.sqrt ((m:ℝ)*p) := by ring
  have hA : spectralNorm (M - M0)
      ≤ C1 * (sigma * Real.sqrt ((m:ℝ)/p)
          + spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))) := by
    have hdec : (M - M0)
        = (p:ℝ)⁻¹ • projMask mask H - (p:ℝ)⁻¹ • (obsMatrix mask M0 H - projMask mask M)
          - ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0)) := by
      ext i j
      simp only [projMask, obsMatrix, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
        smul_eq_mul]
      ring
    have ht : spectralNorm (M - M0) ≤ (p:ℝ)⁻¹ * spectralNorm (projMask mask H)
        + (p:ℝ)⁻¹ * Statlib.HighDim.MatrixAnalysis.opNorm
            (obsMatrix mask M0 H - projMask mask M)
        + spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0)) := by
      rw [← hop (M - M0), ← hop (projMask mask H),
        ← hop ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))]
      have h1 : Statlib.HighDim.MatrixAnalysis.opNorm (M - M0)
          ≤ Statlib.HighDim.MatrixAnalysis.opNorm ((p:ℝ)⁻¹ • projMask mask H
              - (p:ℝ)⁻¹ • (obsMatrix mask M0 H - projMask mask M))
            + Statlib.HighDim.MatrixAnalysis.opNorm
                ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0)) := by
        have heq : Statlib.HighDim.MatrixAnalysis.opNorm ((p:ℝ)⁻¹ • projMask mask H
              - (p:ℝ)⁻¹ • (obsMatrix mask M0 H - projMask mask M)
              - ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0)))
            = Statlib.HighDim.MatrixAnalysis.opNorm (M - M0) := by
          rw [← hdec]
        rw [← heq]
        exact hop_sub _ _
      have h2 : Statlib.HighDim.MatrixAnalysis.opNorm ((p:ℝ)⁻¹ • projMask mask H
              - (p:ℝ)⁻¹ • (obsMatrix mask M0 H - projMask mask M))
          ≤ (p:ℝ)⁻¹ * Statlib.HighDim.MatrixAnalysis.opNorm (projMask mask H)
            + (p:ℝ)⁻¹ * Statlib.HighDim.MatrixAnalysis.opNorm
                (obsMatrix mask M0 H - projMask mask M) := by
        have h3 := hop_sub ((p:ℝ)⁻¹ • projMask mask H)
          ((p:ℝ)⁻¹ • (obsMatrix mask M0 H - projMask mask M))
        rw [hop_smul _ _ hp_inv_nonneg, hop_smul _ _ hp_inv_nonneg] at h3
        exact h3
      linarith only [h1, h2]
    have hb1 : (p:ℝ)⁻¹ * spectralNorm (projMask mask H)
        ≤ K * (sigma * Real.sqrt ((m:ℝ)/p)) := by
      calc (p:ℝ)⁻¹ * spectralNorm (projMask mask H)
          ≤ (p:ℝ)⁻¹ * (K * sigma * Real.sqrt ((m:ℝ)*p)) :=
            mul_le_mul_of_nonneg_left hnoise hp_inv_nonneg
        _ = K * (sigma * Real.sqrt ((m:ℝ)/p)) := by rw [hsqrtsplit]; field_simp
    have hb2 : (p:ℝ)⁻¹ * Statlib.HighDim.MatrixAnalysis.opNorm
          (obsMatrix mask M0 H - projMask mask M)
        ≤ (K + Real.sqrt C_L) * (c⁻¹ * (K * sigma * Real.sqrt ((m:ℝ)/p)
            + spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0)))) := by
      have h1461 := statopia_math_node_1461725421_1cd7d47b m n r hn hnm hr hrn p sigma K c
        hp hp1 hsig hK hc mask H M0 M hbin lamHat hrank hnoise hbulk
      obtain ⟨hsHat_nn, hsHat_le⟩ := h1461
      calc (p:ℝ)⁻¹ * Statlib.HighDim.MatrixAnalysis.opNorm
            (obsMatrix mask M0 H - projMask mask M)
          ≤ (p:ℝ)⁻¹ * ((K + Real.sqrt C_L) *
              sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M * Real.sqrt ((m:ℝ)*p)) :=
            mul_le_mul_of_nonneg_left hres hp_inv_nonneg
        _ = (K + Real.sqrt C_L) *
              (sigmaHat hnm lamHat (obsMatrix mask M0 H) mask M * Real.sqrt ((m:ℝ)/p)) := by
            rw [hsqrtsplit]; field_simp
        _ ≤ (K + Real.sqrt C_L) * (c⁻¹ * (K * sigma * Real.sqrt ((m:ℝ)/p)
              + spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0)))) :=
            mul_le_mul_of_nonneg_left hsHat_le hKs
    have hC1spec' : K + (K + Real.sqrt C_L) * (max K (max Ks 1) + 1) * c⁻¹ + 1 ≤ C1 := by
      simpa only [div_eq_mul_inv] using hC1spec
    have hcK : K + (K + Real.sqrt C_L) * K * c⁻¹ ≤ C1 := by
      have hmx : K ≤ max K (max Ks 1) + 1 := by
        have h := le_max_left K (max Ks 1); linarith only [h]
      have h1 : (K + Real.sqrt C_L) * K ≤ (K + Real.sqrt C_L) * (max K (max Ks 1) + 1) :=
        mul_le_mul_of_nonneg_left hmx hKs
      have h2 : (K + Real.sqrt C_L) * K * c⁻¹
          ≤ (K + Real.sqrt C_L) * (max K (max Ks 1) + 1) * c⁻¹ :=
        mul_le_mul_of_nonneg_right h1 hc_inv_nonneg
      linarith only [h2, hC1spec']
    have hce : (K + Real.sqrt C_L) * c⁻¹ + 1 ≤ C1 := by
      have hmx : (1:ℝ) ≤ max K (max Ks 1) + 1 := by
        have h := le_max_left K (max Ks 1); linarith only [h, hK]
      have h1 : (K + Real.sqrt C_L) * 1 ≤ (K + Real.sqrt C_L) * (max K (max Ks 1) + 1) :=
        mul_le_mul_of_nonneg_left hmx hKs
      have h2 : (K + Real.sqrt C_L) * 1 * c⁻¹
          ≤ (K + Real.sqrt C_L) * (max K (max Ks 1) + 1) * c⁻¹ :=
        mul_le_mul_of_nonneg_right h1 hc_inv_nonneg
      linarith only [h2, hC1spec', hK]
    have hh0nn : 0 ≤ sigma * Real.sqrt ((m:ℝ)/p) :=
      mul_nonneg (le_of_lt hsig) (Real.sqrt_nonneg _)
    have henn : 0 ≤ spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0)) := hspecnn _
    have hfin : K * (sigma * Real.sqrt ((m:ℝ)/p))
        + (K + Real.sqrt C_L) * (c⁻¹ * (K * sigma * Real.sqrt ((m:ℝ)/p)
            + spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))))
        + spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))
        ≤ C1 * (sigma * Real.sqrt ((m:ℝ)/p)
            + spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))) := by
      have e1 : (K + (K + Real.sqrt C_L) * K * c⁻¹) * (sigma * Real.sqrt ((m:ℝ)/p))
          ≤ C1 * (sigma * Real.sqrt ((m:ℝ)/p)) :=
        mul_le_mul_of_nonneg_right hcK hh0nn
      have e2 : ((K + Real.sqrt C_L) * c⁻¹ + 1) *
            spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))
          ≤ C1 * spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0)) :=
        mul_le_mul_of_nonneg_right hce henn
      have hid : K * (sigma * Real.sqrt ((m:ℝ)/p))
          + (K + Real.sqrt C_L) * (c⁻¹ * (K * sigma * Real.sqrt ((m:ℝ)/p)
              + spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))))
          + spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0))
          = (K + (K + Real.sqrt C_L) * K * c⁻¹) * (sigma * Real.sqrt ((m:ℝ)/p))
            + ((K + Real.sqrt C_L) * c⁻¹ + 1) *
              spectralNorm ((p:ℝ)⁻¹ • projMask mask (M - M0) - (M - M0)) := by
        ring
      rw [hid]
      linarith only [e1, e2]
    linarith only [ht, hb1, hb2, hfin]
  have hx2 : 2 * C1 * B * spectralNorm (M - M0) ≤ (1/2) * spectralNorm (M - M0) := by
    have h0 := hspecnn (M - M0)
    have h1 := mul_le_mul_of_nonneg_right hbeta h0
    linarith only [h1]
  have hC1nn : 0 ≤ C1 := by linarith only [hC1_ge1]
  have hxnn : 0 ≤ spectralNorm (M - M0) := hspecnn _
  have he1 := mul_le_mul_of_nonneg_left hE hC1nn
  linarith only [hA, he1, hx2]


  /- @proof-region region.target-node.session.cdf1189b93fc659b end -/

end Statlib.Imported

