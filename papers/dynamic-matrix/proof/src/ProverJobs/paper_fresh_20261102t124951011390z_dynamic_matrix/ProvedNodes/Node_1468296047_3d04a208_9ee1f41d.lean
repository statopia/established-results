import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SVDFoundation
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.MatrixRecovery.MatrixRipRecoveryBound
import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_1013838252_0af447c5_513bc185
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_1090440803_1a7ed39c_db459a5c
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_742183086_90d6ace2_056cf6d4
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_791349827_8cd9ad5e_a51ab6c3

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix




open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_1468296047_3d04a208 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (m1 m2 T : ℕ) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (t : Fin T) (n : Fin T → ℕ) (hn : ∀ j, 0 < n j)
    (Sigma : Matrix (Fin m1 × Fin m2) (Fin m1 × Fin m2) ℝ) (hSigma : Sigma.PosDef)
    (mu kappa : ℝ)
    (hmu : mu = lamMin hSigma.isHermitian.eigenvalues)
    (hmu_pos : 0 < mu)
    (hkappa : kappa = lamMax hSigma.isHermitian.eigenvalues / mu)
    (hkappa_ge : 1 ≤ kappa)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (j : Fin T) → Fin (n j) → Ω → Matrix (Fin m1) (Fin m2) ℝ)
    (hX_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (X j i))
    (xi : (j : Fin T) → Fin (n j) → Ω → ℝ)
    (hxi_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (xi j i))
    (M0 : Fin T → Matrix (Fin m1) (Fin m2) ℝ)
    (Y : (j : Fin T) → Fin (n j) → Ω → ℝ)
    (hY : ∀ (j : Fin T) (i : Fin (n j)) (ω : Ω),
      Y j i ω = frobInner (M0 j) (X j i ω) + xi j i ω)
    (hX2 : ∀ (j : Fin T) (i : Fin (n j)),
      Integrable (fun ω => frobNorm (X j i ω) ^ 2) P)
    (hXi : ∀ (j : Fin T) (i : Fin (n j)),
      Integrable (fun ω => |xi j i ω| * frobNorm (X j i ω)) P)
    (hXi_zero : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      ∫ ω, xi j i ω * (X j i ω) a b ∂P = 0)
    (hXi_int : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      Integrable (fun ω => xi j i ω * (X j i ω) a b) P)
    (hYX_int : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      Integrable (fun ω => Y j i ω * (X j i ω) a b) P)
    (hq_int : ∀ (j : Fin T) (M : Matrix (Fin m1) (Fin m2) ℝ) (i : Fin (n j)),
      Integrable (fun ω => frobInner M (X j i ω) ^ 2) P)
    (hDesign : ∀ (j : Fin T) (M : Matrix (Fin m1) (Fin m2) ℝ),
      (1 / (n j : ℝ)) * ∑ i : Fin (n j), ∫ ω, frobInner M (X j i ω) ^ 2 ∂P
        = secondMomentForm Sigma M)
    (w : Fin T → ℝ) (hw_nonneg : ∀ j, 0 ≤ w j)
    (hw_sum : ∑ j : Fin T, w j = 1)
    (Mset : Set (Matrix (Fin m1) (Fin m2) ℝ))
    (hMne : Mset.Nonempty) (hMconv : Convex ℝ Mset)
    (hM0mem : M0 t ∈ Mset)
    (Mtilde : ℝ → Ω → Matrix (Fin m1) (Fin m2) ℝ)
    (hMtilde_mem : ∀ (lam : ℝ) (ω : Ω), Mtilde lam ω ∈ Mset)
    (hMtilde : ∀ (lam : ℝ) (ω : Ω),
      IsMinOn (fun M => localObj Sigma P n Y X w lam M ω) Mset (Mtilde lam ω))
    (lam : ℝ),
    ∀ ω : Ω, 2 * WDelta P n Y X w ω ≤ lam →
      frobNorm (Mtilde lam ω - M0 t) ^ 2
          - kappa * biasH M0 w t * frobNorm (Mtilde lam ω - M0 t)
        ≤ lam * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) / mu := by
  /- @proof-region region.target-node.session.39a1058939380a35 begin -/
  classical
  intro Ω' _ m1 m2 T hm1 hm2 t n hn Sigma hSigma mu kappa hmu hmu_pos hkappa hkappa_ge
    P hP X hX_m xi hxi_m M0 Y hY hX2 hXi hXi_zero hXi_int hYX_int hq_int hDesign
    w hw_nonneg hw_sum Mset hMne hMconv hM0mem Mtilde hMtilde_mem hMtilde lam ω hlam
  let nuc : Matrix (Fin m1) (Fin m2) ℝ → ℝ := Statlib.HighDim.Vocabulary.nuclearNorm
  let opN : Matrix (Fin m1) (Fin m2) ℝ → ℝ := Statlib.HighDim.MatrixAnalysis.opNorm
  let B : Matrix (Fin m1) (Fin m2) ℝ → Matrix (Fin m1) (Fin m2) ℝ → ℝ :=
    fun A1 A2 => ∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
      vecOf A1 a * Sigma a b * vecOf A2 b
  let E : Matrix (Fin m1) (Fin m2) ℝ := ∑ j : Fin T, w j • DeltaMat P n Y X j ω
  let Mbar : Matrix (Fin m1) (Fin m2) ℝ := ∑ j : Fin T, w j • M0 j
  let Mhat : Matrix (Fin m1) (Fin m2) ℝ := Mtilde lam ω
  let H : Matrix (Fin m1) (Fin m2) ℝ := Mhat - M0 t
  let D : Matrix (Fin m1) (Fin m2) ℝ := M0 t - Mbar
  let F : Matrix (Fin m1) (Fin m2) ℝ → ℝ := fun A => localObj Sigma P n Y X w lam A ω
  have hY_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (Y j i) := by
    intro j i
    have hYX : Y j i = fun ω' => frobInner (M0 j) (X j i ω') + xi j i ω' := by
      funext ω'
      exact hY j i ω'
    rw [hYX]
    refine Measurable.add ?_ (hxi_m j i)
    simp only [frobInner]
    fun_prop
  obtain ⟨hBBboth, hBaddl, hBsmull, hBaddr, hBsmulr, hBsymm, hBmv, hBfrob, hquad, haff⟩ :=
    statopia_math_node_1013838252_0af447c5 m1 m2 Sigma hSigma
  have hBB' : ∀ A : Matrix (Fin m1) (Fin m2) ℝ, B A A = secondMomentForm Sigma A :=
    fun A => (hBBboth A).1
  have hBnonneg' : ∀ A : Matrix (Fin m1) (Fin m2) ℝ, 0 ≤ B A A := fun A => (hBBboth A).2
  have hBaddl' : ∀ A1 A2 A : Matrix (Fin m1) (Fin m2) ℝ,
      B (A1 + A2) A = B A1 A + B A2 A := hBaddl
  have hBaddr' : ∀ A1 A2 A : Matrix (Fin m1) (Fin m2) ℝ,
      B A1 (A2 + A) = B A1 A2 + B A1 A := hBaddr
  have hBsmulr' : ∀ (c : ℝ) (A1 A2 : Matrix (Fin m1) (Fin m2) ℝ),
      B A1 (c • A2) = c * B A1 A2 := hBsmulr
  have hquad' : ∀ (Mh Hh : Matrix (Fin m1) (Fin m2) ℝ) (eps : ℝ),
      secondMomentForm Sigma (Mh - eps • Hh)
        = secondMomentForm Sigma Mh - 2 * eps * B Mh Hh
          + eps ^ 2 * secondMomentForm Sigma Hh := hquad
  have haff' : ∀ (Mh Mb Hh Dh : Matrix (Fin m1) (Fin m2) ℝ),
      (∀ (i : Fin m1) (j : Fin m2), (Mh - Mb) i j = (Hh + Dh) i j) →
      B Mh Hh = B Mb Hh + B (Hh + Dh) Hh ∧ B (Hh + Dh) Hh = B Hh Hh + B Dh Hh := haff
  have hnuc_nonneg : ∀ X : Matrix (Fin m1) (Fin m2) ℝ, 0 ≤ nuc X := by
    intro X
    exact (statopia_math_node_791349827_8cd9ad5e m1 m2 0 0 0 X 0).1
  have hpair : ∀ A Bm : Matrix (Fin m1) (Fin m2) ℝ, frobInner A Bm ≤ opN A * nuc Bm := by
    intro A Bm
    exact (statopia_math_node_791349827_8cd9ad5e m1 m2 A Bm 0 0 0).2.2.2.1
  have hnuc_add : ∀ A Bm : Matrix (Fin m1) (Fin m2) ℝ, nuc (A + Bm) ≤ nuc A + nuc Bm := by
    intro A Bm
    exact Statlib.HighDim.MatrixAnalysis.nuclearNorm_add_le A Bm
  have hnuc_neg : ∀ A : Matrix (Fin m1) (Fin m2) ℝ, nuc (-A) = nuc A := by
    intro A
    exact Statlib.HighDim.MatrixRecovery.nuclearNorm_neg A
  have hlamE : 2 * opN E ≤ lam := hlam
  have hopnn : 0 ≤ opN E := Statlib.HighDim.MatrixAnalysis.opNorm_nonneg E
  have hlam_nonneg : 0 ≤ lam := by linarith
  have hcurv : mu * (frobNorm H ^ 2 - kappa * frobNorm D * frobNorm H) ≤ B H H + B D H :=
    statopia_math_node_1090440803_1a7ed39c m1 m2 Sigma hSigma mu kappa hmu hmu_pos hkappa H D
  have hAcurv : B (H + D) H = B H H + B D H := hBaddl' H D H
  have hfi_add : ∀ (M A1 A2 : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner M (A1 + A2) = frobInner M A1 + frobInner M A2 := by
    intro M A1 A2
    have key : ∀ (i : Fin m1) (j : Fin m2),
        M i j * (A1 + A2) i j = M i j * A1 i j + M i j * A2 i j := by
      intro i j
      show M i j * (A1 i j + A2 i j) = M i j * A1 i j + M i j * A2 i j
      ring
    simp only [frobInner, key, Finset.sum_add_distrib]
  have hfi_smul : ∀ (M : Matrix (Fin m1) (Fin m2) ℝ) (c : ℝ)
      (A : Matrix (Fin m1) (Fin m2) ℝ), frobInner M (c • A) = c * frobInner M A := by
    intro M c A
    have key : ∀ (i : Fin m1) (j : Fin m2),
        M i j * (c • A) i j = c * (M i j * A i j) := by
      intro i j
      show M i j * (c * A i j) = c * (M i j * A i j)
      ring
    simp only [frobInner, key, Finset.mul_sum]
  have hfi_sub : ∀ (M A1 A2 : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner M (A1 - A2) = frobInner M A1 - frobInner M A2 := by
    intro M A1 A2
    have key : ∀ (i : Fin m1) (j : Fin m2),
        M i j * (A1 - A2) i j = M i j * A1 i j - M i j * A2 i j := by
      intro i j
      show M i j * (A1 i j - A2 i j) = M i j * A1 i j - M i j * A2 i j
      ring
    simp only [frobInner, key, Finset.sum_sub_distrib]
  have hBsub : ∀ (A1 A2 A3 : Matrix (Fin m1) (Fin m2) ℝ),
      B A1 (A2 - A3) = B A1 A2 - B A1 A3 := by
    intro A1 A2 A3
    rw [sub_eq_add_neg, hBaddr']
    have hneg : B A1 (-A3) = -B A1 A3 := by
      have h := hBsmulr' (-1 : ℝ) A1 A3
      simpa using h
    rw [hneg]
    ring
  have hball : ∃ G : Matrix (Fin m1) (Fin m2) ℝ, opN G ≤ 1 := by
    obtain ⟨svd⟩ := Statlib.HighDim.MatrixAnalysis.svd_exists (0 : Matrix (Fin m1) (Fin m2) ℝ)
    refine ⟨Statlib.HighDim.MatrixAnalysis.svdPosU svd *
      Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV svd), ?_⟩
    exact ((statopia_math_node_791349827_8cd9ad5e m1 m2 0 0 0 0 0).2.2.2.2.2.1 svd).1
  have hunit : ∀ (G X : Matrix (Fin m1) (Fin m2) ℝ), opN G ≤ 1 → frobInner G X ≤ nuc X := by
    intro G X hG
    exact (statopia_math_node_791349827_8cd9ad5e m1 m2 0 0 G X 0).2.1 hG
  have hnuc_seg : ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      nuc ((1 - eps) • Mhat + eps • (M0 t))
        ≤ (1 - eps) * nuc Mhat + eps * nuc (M0 t) := by
    intro eps h0 h1
    obtain ⟨G, -, hG2, hG3⟩ := (statopia_math_node_791349827_8cd9ad5e m1 m2 0 0 0
      ((1 - eps) • Mhat + eps • (M0 t)) 0).2.2.2.2.2.2.1
    have hlin : frobInner G ((1 - eps) • Mhat + eps • (M0 t))
        = (1 - eps) * frobInner G Mhat + eps * frobInner G (M0 t) := by
      rw [hfi_add, hfi_smul, hfi_smul]
    calc nuc ((1 - eps) • Mhat + eps • (M0 t))
        = frobInner G ((1 - eps) • Mhat + eps • (M0 t)) := hG2.symm
      _ = (1 - eps) * frobInner G Mhat + eps * frobInner G (M0 t) := hlin
      _ ≤ (1 - eps) * nuc Mhat + eps * nuc (M0 t) := by
          nlinarith [mul_le_mul_of_nonneg_left (hG3 Mhat)
            (by linarith : (0 : ℝ) ≤ 1 - eps), mul_le_mul_of_nonneg_left (hG3 (M0 t)) h0]

  have hminF : ∀ A : Matrix (Fin m1) (Fin m2) ℝ, A ∈ Mset → F Mhat ≤ F A := by
    intro A hA
    simpa using hMtilde lam ω hA
  have hMhat_mem : Mhat ∈ Mset := hMtilde_mem lam ω
  obtain ⟨-, -, -, hobjloc⟩ :=
    statopia_math_node_742183086_90d6ace2 Ω' m1 m2 T n hn P X hX_m xi hxi_m M0 Y hY_m hY hX2
      hXi hXi_zero hXi_int hYX_int Sigma hSigma w hw_sum hDesign
  have hSM : ∀ A : Matrix (Fin m1) (Fin m2) ℝ,
      (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
        (∑ j : Fin T, w j • M0 j) a b * Sigma (a, b) (a', b') * A a' b') = B Mbar A := by
    intro A
    show (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
        (∑ j : Fin T, w j • M0 j) a b * Sigma (a, b) (a', b') * A a' b')
      = ∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
          (∑ j : Fin T, w j • M0 j) a.1 a.2 * Sigma a b * A b.1 b.2
    simp only [Fintype.sum_prod_type]
  have hF : ∀ A : Matrix (Fin m1) (Fin m2) ℝ,
      F A = secondMomentForm Sigma A - 2 * (B Mbar A + frobInner E A) + lam * nuc A := by
    intro A
    change localObj Sigma P n Y X w lam A ω
        = secondMomentForm Sigma A - 2 * (B Mbar A + frobInner E A) + lam * nuc A
    rw [hobjloc ω A lam, hSM A]

  have hbiasD : biasH M0 w t = frobNorm D := rfl
  have hslow : Mhat ∈ Mset → B (H + D) H ≤ lam * nuc (M0 t) := by
    intro hMmem
    have hAeq : ∀ eps : ℝ, Mhat - eps • H = (1 - eps) • Mhat + eps • (M0 t) := by
      intro eps
      ext i j
      show Mhat i j - eps * (Mhat i j - M0 t i j) = (1 - eps) * Mhat i j + eps * M0 t i j
      ring
    have hexp : ∀ eps : ℝ, F (Mhat - eps • H) - F Mhat
        = -2 * eps * (B (H + D) H - frobInner E H) + eps ^ 2 * B H H
          + lam * (nuc (Mhat - eps • H) - nuc Mhat) := by
      intro eps
      have haff1 : B Mhat H = B Mbar H + B (H + D) H := by
        obtain ⟨h1, -⟩ := haff' Mhat Mbar H D (by
          intro i j
          show Mhat i j - Mbar i j = (Mhat i j - M0 t i j) + (M0 t i j - Mbar i j)
          ring)
        exact h1
      have hquad2 : secondMomentForm Sigma (Mhat - eps • H)
          = secondMomentForm Sigma Mhat - 2 * eps * B Mhat H + eps ^ 2 * B H H := by
        rw [hquad' Mhat H eps, ← hBB' H]
      rw [hF (Mhat - eps • H), hF Mhat, hquad2, hBsub Mbar Mhat (eps • H),
        hfi_sub E Mhat (eps • H), hBsmulr' eps Mbar H, hfi_smul E eps H, haff1]
      ring
    have hkey : ∀ eps : ℝ, 0 < eps → eps < 1 →
        0 ≤ -2 * (B (H + D) H - frobInner E H) + eps * B H H
          + lam * (nuc (M0 t) - nuc Mhat) := by
      intro eps he0 he1
      have hmem : Mhat - eps • H ∈ Mset := by
        rw [hAeq eps]
        exact hMconv hMmem hM0mem (by linarith) he0.le (by ring)
      have hdif : 0 ≤ F (Mhat - eps • H) - F Mhat := by
        have h := hminF (Mhat - eps • H) hmem
        linarith
      have hconv : lam * (nuc (Mhat - eps • H) - nuc Mhat)
          ≤ lam * (eps * (nuc (M0 t) - nuc Mhat)) := by
        have h := hnuc_seg eps he0.le he1.le
        rw [← hAeq eps] at h
        exact mul_le_mul_of_nonneg_left (by linarith) hlam_nonneg
      rw [hexp eps] at hdif
      have hprod : 0 ≤ eps * (-2 * (B (H + D) H - frobInner E H) + eps * B H H
          + lam * (nuc (M0 t) - nuc Mhat)) := by
        nlinarith [hdif, hconv]
      exact (mul_nonneg_iff_of_pos_left he0).1 hprod
    have hlim : 2 * (B (H + D) H - frobInner E H) ≤ lam * (nuc (M0 t) - nuc Mhat) := by
      have hq : 0 ≤ B H H := hBnonneg' H
      have hq1 : 0 < B H H + 1 := by linarith
      have hmain : ∀ eta : ℝ, 0 < eta → 2 * (B (H + D) H - frobInner E H)
          ≤ lam * (nuc (M0 t) - nuc Mhat) + eta := by
        intro eta heta
        have heps0 : 0 < min (1 / 2) (eta / (B H H + 1)) :=
          lt_min (by norm_num) (div_pos heta hq1)
        have heps1 : min (1 / 2) (eta / (B H H + 1)) < 1 :=
          lt_of_le_of_lt (min_le_left _ _) (by norm_num)
        have hk := hkey _ heps0 heps1
        have hle : min (1 / 2) (eta / (B H H + 1)) * B H H ≤ eta := by
          have h4 : min (1 / 2) (eta / (B H H + 1)) * B H H
              ≤ (eta / (B H H + 1)) * B H H :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hq
          have h6 : (eta / (B H H + 1)) * B H H ≤ eta := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hq1]
            nlinarith
          linarith
        nlinarith [hk, hle]
      exact le_of_forall_pos_le_add hmain
    have hpairH : frobInner E H ≤ opN E * nuc H := hpair E H
    have hnucH : nuc H ≤ nuc Mhat + nuc (M0 t) := by
      have hH : H = Mhat + -(M0 t) := by
        show Mhat - M0 t = Mhat + -(M0 t)
        rw [sub_eq_add_neg]
      calc nuc H = nuc (Mhat + -(M0 t)) := by rw [hH]
        _ ≤ nuc Mhat + nuc (-(M0 t)) := hnuc_add Mhat _
        _ = nuc Mhat + nuc (M0 t) := by rw [hnuc_neg]
    have hHnn : 0 ≤ nuc H := hnuc_nonneg H
    have hstep1 : 2 * (opN E * nuc H) ≤ lam * nuc H := by nlinarith [hlamE, hHnn]
    have hstep2 : lam * nuc H ≤ lam * (nuc Mhat + nuc (M0 t)) :=
      mul_le_mul_of_nonneg_left hnucH hlam_nonneg
    nlinarith [hlim, hpairH, hstep1, hstep2]
  have hAc_le : B (H + D) H ≤ lam * nuc (M0 t) := hslow hMhat_mem
  have hcurv2 : mu * (frobNorm H ^ 2 - kappa * frobNorm D * frobNorm H) ≤ lam * nuc (M0 t) := by
    have h' : mu * (frobNorm H ^ 2 - kappa * frobNorm D * frobNorm H) ≤ B (H + D) H := by
      rw [hAcurv]
      exact hcurv
    exact le_trans h' hAc_le
  have hfin : frobNorm H ^ 2 - (kappa * frobNorm D) * frobNorm H ≤ lam * nuc (M0 t) / mu := by
    rw [le_div_iff₀ hmu_pos]
    linarith
  rw [hbiasD]
  exact hfin
  /- @proof-region region.target-node.session.39a1058939380a35 end -/

end Statlib.Imported

