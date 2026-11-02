import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SVDFoundation
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_1013838252_0af447c5_513bc185
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_1090440803_1a7ed39c_db459a5c
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_2332586660_e1256341_5c1368cc
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_2628551730_d82d74eb_c14fc884
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_742183086_90d6ace2_056cf6d4
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_791349827_8cd9ad5e_a51ab6c3

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix






open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_975363148_a48ae5fa : ∀ {Omega : Type*} [MeasurableSpace Omega]
    (m1 m2 T : ℕ) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (t : Fin T) (n : Fin T → ℕ) (hn : ∀ j, 0 < n j)
    (Sigma : Matrix (Fin m1 × Fin m2) (Fin m1 × Fin m2) ℝ) (hSigma : Sigma.PosDef)
    (mu kappa : ℝ)
    (hmu : mu = lamMin hSigma.isHermitian.eigenvalues)
    (hmu_pos : 0 < mu)
    (hkappa : kappa = lamMax hSigma.isHermitian.eigenvalues / mu)
    (hkappa_ge : 1 ≤ kappa)
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : (j : Fin T) → Fin (n j) → Omega → Matrix (Fin m1) (Fin m2) ℝ)
    (hX_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (X j i))
    (xi : (j : Fin T) → Fin (n j) → Omega → ℝ)
    (hxi_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (xi j i))
    (M0 : Fin T → Matrix (Fin m1) (Fin m2) ℝ)
    (Y : (j : Fin T) → Fin (n j) → Omega → ℝ)
    (hY : ∀ (j : Fin T) (i : Fin (n j)) (omega : Omega),
      Y j i omega = frobInner (M0 j) (X j i omega) + xi j i omega)
    (hX2 : ∀ (j : Fin T) (i : Fin (n j)),
      Integrable (fun omega => frobNorm (X j i omega) ^ 2) P)
    (hXi : ∀ (j : Fin T) (i : Fin (n j)),
      Integrable (fun omega => |xi j i omega| * frobNorm (X j i omega)) P)
    (hXi_zero : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      ∫ omega, xi j i omega * (X j i omega) a b ∂P = 0)
    (hXi_int : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      Integrable (fun omega => xi j i omega * (X j i omega) a b) P)
    (hYX_int : ∀ (j : Fin T) (i : Fin (n j)) (a : Fin m1) (b : Fin m2),
      Integrable (fun omega => Y j i omega * (X j i omega) a b) P)
    (hq_int : ∀ (j : Fin T) (M : Matrix (Fin m1) (Fin m2) ℝ) (i : Fin (n j)),
      Integrable (fun omega => frobInner M (X j i omega) ^ 2) P)
    (hDesign : ∀ (j : Fin T) (M : Matrix (Fin m1) (Fin m2) ℝ),
      (1 / (n j : ℝ)) * ∑ i : Fin (n j), ∫ omega, frobInner M (X j i omega) ^ 2 ∂P
        = secondMomentForm Sigma M)
    (w : Fin T → ℝ) (hw_nonneg : ∀ j, 0 ≤ w j)
    (hw_sum : ∑ j : Fin T, w j = 1)
    (Mset : Set (Matrix (Fin m1) (Fin m2) ℝ))
    (hMne : Mset.Nonempty) (hMclosed : IsClosed Mset) (hMconv : Convex ℝ Mset)
    (hM0mem : M0 t ∈ Mset)
    (Mtilde : ℝ → Omega → Matrix (Fin m1) (Fin m2) ℝ)
    (hMtilde_mem : ∀ (lam : ℝ) (omega : Omega), Mtilde lam omega ∈ Mset)
    (hMtilde : ∀ (lam : ℝ) (omega : Omega),
      IsMinOn (fun M => localObj Sigma P n Y X w lam M omega) Mset (Mtilde lam omega))
    (lam : ℝ),
    ∀ omega : Omega, 2 * WDelta P n Y X w omega ≤ lam →
      frobNorm (Mtilde lam omega - M0 t) ≤
        kappa * biasH M0 w t +
          ((1 + Real.sqrt 2) / 2) * (lam / mu) * Real.sqrt ((Matrix.rank (M0 t) : ℝ)) := by
  /- @proof-region region.target-node.session.3f3eb936d771d16a begin -/
  intro Ω instΩ m1 m2 T hm1 hm2 t n hn Sigma hSigma mu kappa hmu hmu_pos hkappa hkappa_ge P instP
    X hX_m xi hxi_m M0 Y hY hX2 hXi hXi_zero hXi_int hYX_int hq_int hDesign w hw_nonneg
    hw_sum Mset hMne hMclosed hMconv hM0mem Mtilde hMtilde_mem hMtilde lam ω hlam
  classical
  set Mhat : Matrix (Fin m1) (Fin m2) ℝ := Mtilde lam ω with hMhatdef
  set Mbar : Matrix (Fin m1) (Fin m2) ℝ := ∑ j : Fin T, w j • M0 j with hMbardef
  set Evec : Matrix (Fin m1) (Fin m2) ℝ := ∑ j : Fin T, w j • DeltaMat P n Y X j ω with hEvecdef
  set H : Matrix (Fin m1) (Fin m2) ℝ := Mhat - M0 t with hHdef
  set Dm : Matrix (Fin m1) (Fin m2) ℝ := M0 t - Mbar with hDdef
  set e : ℝ := frobNorm H with hedef
  set delta : ℝ := frobNorm Dm with hdeltadef
  set W : ℝ := Statlib.HighDim.MatrixAnalysis.opNorm Evec with hWdef
  set B : Matrix (Fin m1) (Fin m2) ℝ → Matrix (Fin m1) (Fin m2) ℝ → ℝ :=
    fun A1 A2 => ∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
      vecOf A1 a * Sigma a b * vecOf A2 b with hBdef
  set Acurv : ℝ := B (H + Dm) H with hAcurvdef
  set R : ℝ := Real.sqrt ((M0 t).rank : ℝ) with hRdef
  obtain ⟨svd⟩ := Statlib.HighDim.MatrixAnalysis.svd_exists (M0 t)
  set U := Statlib.HighDim.MatrixAnalysis.svdPosU svd with hUdef
  set V := Statlib.HighDim.MatrixAnalysis.svdPosV svd with hVdef
  set PU : Matrix (Fin m1) (Fin m1) ℝ := U * Matrix.transpose U with hPUdef
  set PV : Matrix (Fin m2) (Fin m2) ℝ := V * Matrix.transpose V with hPVdef
  set Pperp : Matrix (Fin m1) (Fin m2) ℝ → Matrix (Fin m1) (Fin m2) ℝ :=
    fun X => (1 - PU) * X * (1 - PV) with hPperpdef
  set Hperp : Matrix (Fin m1) (Fin m2) ℝ := Pperp H with hHperpdef
  set Nperp : ℝ := Statlib.HighDim.Vocabulary.nuclearNorm Hperp with hNperpdef
  obtain ⟨svd_perp⟩ := Statlib.HighDim.MatrixAnalysis.svd_exists Hperp
  set Uperp := Statlib.HighDim.MatrixAnalysis.svdPosU svd_perp with hUperpdef
  set Vperp := Statlib.HighDim.MatrixAnalysis.svdPosV svd_perp with hVperpdef
  set Zperp : Matrix (Fin m1) (Fin m2) ℝ := Uperp * Matrix.transpose Vperp with hZperpdef
  set V0 : Matrix (Fin m1) (Fin m2) ℝ := U * Matrix.transpose V + Zperp with hV0def
  have hcert := statopia_math_node_2332586660_e1256341 m1 m2 (M0 t) svd H svd_perp
  obtain ⟨hZtr, hZV, hZop, hZH⟩ := hcert.1
  obtain ⟨hV0op, hV0Mnuc, hV0sub⟩ := hcert.2.1
  obtain ⟨hUVfrob, hV0Hraw⟩ := hcert.2.2
  have hdual := statopia_math_node_791349827_8cd9ad5e m1 m2 0 0 0 0 Mhat
  obtain ⟨-, -, -, -, -, -, -, -, hVex⟩ := hdual
  obtain ⟨Vhat, hVop, hVM, hVsub⟩ := hVex
  have hWDelta : W = WDelta P n Y X w ω := by rw [hWdef, hEvecdef]; rfl
  have hWnn : 0 ≤ W := by rw [hWdef]; exact Statlib.HighDim.MatrixAnalysis.opNorm_nonneg Evec
  have hlamW : 2 * W ≤ lam := by rw [hWDelta]; exact hlam
  have hlamnn : 0 ≤ lam := by linarith
  have he_nn : 0 ≤ e := by rw [hedef]; unfold frobNorm; exact Real.sqrt_nonneg _
  have hd_nn : 0 ≤ delta := by rw [hdeltadef]; unfold frobNorm; exact Real.sqrt_nonneg _
  have hR_nn : 0 ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
  have hNperp_nn : 0 ≤ Nperp := by
    rw [hNperpdef]
    exact (Statlib.HighDim.MatrixAnalysis.nuclearNorm_nonneg Hperp).1
  have hkappa_pos : 0 < kappa := by linarith
  have hY_m : ∀ (j : Fin T) (i : Fin (n j)), Measurable (Y j i) := by
    intro j i
    have hfun : Y j i = fun ω => frobInner (M0 j) (X j i ω) + xi j i ω := funext (hY j i)
    rw [hfun]
    have hXc : ∀ (a : Fin m1) (b : Fin m2), Measurable (fun ω => (X j i ω) a b) := by
      intro a b
      exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hX_m j i))
    have hsum : Measurable (fun ω => frobInner (M0 j) (X j i ω)) := by
      have hEq : (fun ω => frobInner (M0 j) (X j i ω))
          = fun ω => ∑ a : Fin m1, ∑ b : Fin m2, (M0 j) a b * (X j i ω) a b := rfl
      rw [hEq]
      exact Finset.measurable_sum (s := Finset.univ)
        (f := fun a ω => ∑ b : Fin m2, (M0 j) a b * (X j i ω) a b)
        (fun a _ => Finset.measurable_sum (s := Finset.univ)
          (f := fun b ω => (M0 j) a b * (X j i ω) a b)
          (fun b _ => measurable_const.mul (hXc a b)))
    exact hsum.add (hxi_m j i)
  have hbilin := statopia_math_node_1013838252_0af447c5 m1 m2 Sigma hSigma
  obtain ⟨hBB0, hBadd10, hBsmul10, hBadd20, hBsmul20, hBsymm0, hBmulVec0, hBnorm0,
    hBquad0, hBsplit0⟩ := hbilin
  have hBB : ∀ A : Matrix (Fin m1) (Fin m2) ℝ, B A A = secondMomentForm Sigma A :=
    fun A => (hBB0 A).1
  have hBnn : ∀ A : Matrix (Fin m1) (Fin m2) ℝ, 0 ≤ B A A := fun A => (hBB0 A).2
  have hBadd2 : ∀ (A1 A2 A : Matrix (Fin m1) (Fin m2) ℝ),
      B A1 (A2 + A) = B A1 A2 + B A1 A := fun A1 A2 A => hBadd20 A1 A2 A
  have hBsmul2 : ∀ (c : ℝ) (A1 A2 : Matrix (Fin m1) (Fin m2) ℝ),
      B A1 (c • A2) = c * B A1 A2 := fun c A1 A2 => hBsmul20 c A1 A2
  have hBquad : ∀ (X Y : Matrix (Fin m1) (Fin m2) ℝ) (eps : ℝ),
      secondMomentForm Sigma (X - eps • Y) =
        secondMomentForm Sigma X - 2 * eps * B X Y + eps ^ 2 * secondMomentForm Sigma Y :=
    fun X Y eps => hBquad0 X Y eps
  have hBsplit : ∀ (X Y : Matrix (Fin m1) (Fin m2) ℝ) (Hh Dd : Matrix (Fin m1) (Fin m2) ℝ),
      (∀ (i : Fin m1) (j : Fin m2), (X - Y) i j = (Hh + Dd) i j) →
        B X Hh = B Y Hh + B (Hh + Dd) Hh ∧
          B (Hh + Dd) Hh = B Hh Hh + B Dd Hh := fun X Y Hh Dd h => hBsplit0 X Y Hh Dd h
  have hB_nested : ∀ (A1 A2 : Matrix (Fin m1) (Fin m2) ℝ),
      B A1 A2 = ∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
        A1 a b * Sigma (a, b) (a', b') * A2 a' b' := by
    intro A1 A2
    simp [hBdef, vecOf, Fintype.sum_prod_type]
  have hfrob_sub_right : ∀ (A1 A2 A3 : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner A1 (A2 - A3) = frobInner A1 A2 - frobInner A1 A3 := by
    intro A1 A2 A3
    simp only [frobInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hfrob_smul_right : ∀ (c : ℝ) (A1 A2 : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner A1 (c • A2) = c * frobInner A1 A2 := by
    intro c A1 A2
    simp only [frobInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have hfrob_affine : ∀ (t : ℝ) (A1 A2 A3 : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner A1 (A2 - t • A3) = frobInner A1 A2 - t * frobInner A1 A3 := by
    intro t A1 A2 A3
    rw [hfrob_sub_right, hfrob_smul_right]
  have hB_sub_right : ∀ (A1 A2 A3 : Matrix (Fin m1) (Fin m2) ℝ),
      B A1 (A2 - A3) = B A1 A2 - B A1 A3 := by
    intro A1 A2 A3
    have hsp : A2 - A3 = A2 + (-1 : ℝ) • A3 := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsp, hBadd2, hBsmul2]
    ring
  have hB_affine : ∀ (t : ℝ) (A1 A2 A3 : Matrix (Fin m1) (Fin m2) ℝ),
      B A1 (A2 - t • A3) = B A1 A2 - t * B A1 A3 := by
    intro t A1 A2 A3
    rw [hB_sub_right, hBsmul2]
  obtain ⟨-, -, -, hobjform⟩ := statopia_math_node_742183086_90d6ace2 Ω m1 m2 T n hn
    P X hX_m xi hxi_m M0 Y hY_m hY hX2 hXi hXi_zero hXi_int hYX_int Sigma hSigma w hw_sum hDesign
  have hF : ∀ A : Matrix (Fin m1) (Fin m2) ℝ,
      localObj Sigma P n Y X w lam A ω
        = secondMomentForm Sigma A - 2 * (B Mbar A + frobInner Evec A)
          + lam * Statlib.HighDim.Vocabulary.nuclearNorm A := by
    intro A
    rw [hobjform ω A lam]
    have h2 : (∑ a : Fin m1, ∑ b : Fin m2, ∑ a' : Fin m1, ∑ b' : Fin m2,
        (∑ j : Fin T, w j • M0 j) a b * Sigma (a, b) (a', b') * A a' b') = B Mbar A := by
      rw [hB_nested, hMbardef]
    have h3 : frobInner (∑ j : Fin T, w j • DeltaMat P n Y X j ω) A = frobInner Evec A := by
      rw [hEvecdef]
    rw [h2, h3]
  have hMhat_mem : Mhat ∈ Mset := hMtilde_mem lam ω
  have hAt_mem : ∀ (s : ℝ), 0 < s → s ≤ 1 → Mhat - s • H ∈ Mset := by
    intro s hs0 hs1
    have hcombo : (1 - s) • Mhat + s • M0 t ∈ Mset :=
      hMconv hMhat_mem hM0mem (show (0:ℝ) ≤ 1 - s by linarith)
        (show (0:ℝ) ≤ s by linarith) (show (1 - s) + s = 1 by ring)
    have heq : (1 - s) • Mhat + s • M0 t = Mhat - s • H := by
      rw [hHdef]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rwa [heq] at hcombo
  have hentry : ∀ (i : Fin m1) (j : Fin m2), (Mhat - Mbar) i j = (H + Dm) i j := by
    intro i j
    rw [hHdef, hDdef]
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  have hsplit2 : B (H + Dm) H = B H H + B Dm H := (hBsplit Mhat Mbar H Dm hentry).2
  have hsplitH : B Mhat H = B Mbar H + Acurv := by
    rw [(hBsplit Mhat Mbar H Dm hentry).1, hAcurvdef]
  have hcurvA : mu * (e ^ 2 - kappa * delta * e) ≤ Acurv := by
    have hc := statopia_math_node_1090440803_1a7ed39c m1 m2 Sigma hSigma mu kappa hmu hmu_pos
      hkappa H Dm
    have hc' : mu * (e ^ 2 - kappa * delta * e) ≤ B H H + B Dm H := hc
    rw [← hsplit2] at hc'
    rw [← hAcurvdef] at hc'
    exact hc'
  have hdiff : ∀ (s : ℝ),
      localObj Sigma P n Y X w lam (Mhat - s • H) ω - localObj Sigma P n Y X w lam Mhat ω
        = -2 * s * Acurv + 2 * s * frobInner Evec H + s ^ 2 * secondMomentForm Sigma H
          + lam * (Statlib.HighDim.Vocabulary.nuclearNorm (Mhat - s • H)
              - Statlib.HighDim.Vocabulary.nuclearNorm Mhat) := by
    intro s
    rw [hF (Mhat - s • H), hF Mhat, hBquad Mhat H s, hB_affine s Mbar Mhat H,
      hfrob_affine s Evec Mhat H, hsplitH]
    ring
  have hfrob_add_right : ∀ (A1 A2 A3 : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner A1 (A2 + A3) = frobInner A1 A2 + frobInner A1 A3 := by
    intro A1 A2 A3
    have hsp : A2 + A3 = A2 - (-1 : ℝ) • A3 := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsp, hfrob_affine]
    ring
  have hfrob_comb : ∀ (c d : ℝ) (A1 A2 A3 : Matrix (Fin m1) (Fin m2) ℝ),
      frobInner A1 (c • A2 + d • A3) = c * frobInner A1 A2 + d * frobInner A1 A3 := by
    intro c d A1 A2 A3
    rw [hfrob_add_right, hfrob_smul_right, hfrob_smul_right]
  have hunit : ∀ (G X : Matrix (Fin m1) (Fin m2) ℝ),
      Statlib.HighDim.MatrixAnalysis.opNorm G ≤ 1 →
        frobInner G X ≤ Statlib.HighDim.Vocabulary.nuclearNorm X := by
    intro G X hG
    exact (statopia_math_node_791349827_8cd9ad5e m1 m2 0 0 G X 0).2.1 hG
  have hsup : ∀ (X : Matrix (Fin m1) (Fin m2) ℝ),
      Statlib.HighDim.Vocabulary.nuclearNorm X =
        ⨆ (G2 : {N : Matrix (Fin m1) (Fin m2) ℝ //
            Statlib.HighDim.MatrixAnalysis.opNorm N ≤ 1}), frobInner G2.1 X := by
    intro X
    exact (statopia_math_node_791349827_8cd9ad5e m1 m2 0 0 0 X 0).2.2.1
  have hnuc : ∀ (s : ℝ), 0 < s → s ≤ 1 →
      Statlib.HighDim.Vocabulary.nuclearNorm (Mhat - s • H) ≤
        (1 - s) * Statlib.HighDim.Vocabulary.nuclearNorm Mhat +
          s * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) := by
    intro s hs0 hs1
    haveI : Nonempty {N : Matrix (Fin m1) (Fin m2) ℝ //
        Statlib.HighDim.MatrixAnalysis.opNorm N ≤ 1} := ⟨⟨Vhat, hVop⟩⟩
    have hHsplit : Mhat - s • H = (1 - s) • Mhat + s • M0 t := by
      rw [hHdef]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsup (Mhat - s • H), hHsplit]
    refine ciSup_le ?_
    · intro G2
      rw [hfrob_comb]
      have h1 : frobInner G2.1 Mhat ≤ Statlib.HighDim.Vocabulary.nuclearNorm Mhat :=
        hunit G2.1 Mhat G2.2
      have h2 : frobInner G2.1 (M0 t) ≤ Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) :=
        hunit G2.1 (M0 t) G2.2
      have ha : (1 - s) * frobInner G2.1 Mhat ≤
          (1 - s) * Statlib.HighDim.Vocabulary.nuclearNorm Mhat :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have hb : s * frobInner G2.1 (M0 t) ≤
          s * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t) :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt hs0)
      linarith
  have hray : ∀ (s : ℝ), 0 < s → s ≤ 1 →
      0 ≤ -2 * Acurv + 2 * frobInner Evec H + s * secondMomentForm Sigma H
        + lam * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
            - Statlib.HighDim.Vocabulary.nuclearNorm Mhat) := by
    intro s hs0 hs1
    have hnet : 0 ≤ localObj Sigma P n Y X w lam (Mhat - s • H) ω
        - localObj Sigma P n Y X w lam Mhat ω := by
      have hmm : localObj Sigma P n Y X w lam Mhat ω
          ≤ localObj Sigma P n Y X w lam (Mhat - s • H) ω :=
        hMtilde lam ω (hAt_mem s hs0 hs1)
      linarith
    have hnet' : 0 ≤ -2 * s * Acurv + 2 * s * frobInner Evec H
        + s ^ 2 * secondMomentForm Sigma H
        + lam * (Statlib.HighDim.Vocabulary.nuclearNorm (Mhat - s • H)
            - Statlib.HighDim.Vocabulary.nuclearNorm Mhat) := by
      rw [← hdiff s]
      exact hnet
    have hconv : Statlib.HighDim.Vocabulary.nuclearNorm (Mhat - s • H)
        - Statlib.HighDim.Vocabulary.nuclearNorm Mhat
        ≤ s * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
            - Statlib.HighDim.Vocabulary.nuclearNorm Mhat) := by
      have h1 := hnuc s hs0 hs1
      have h2 : (1 - s) * Statlib.HighDim.Vocabulary.nuclearNorm Mhat
          + s * Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
          = Statlib.HighDim.Vocabulary.nuclearNorm Mhat
            + s * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
              - Statlib.HighDim.Vocabulary.nuclearNorm Mhat) := by ring
      linarith [h1, h2]
    have hmul : lam * (Statlib.HighDim.Vocabulary.nuclearNorm (Mhat - s • H)
        - Statlib.HighDim.Vocabulary.nuclearNorm Mhat)
        ≤ s * (lam * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
            - Statlib.HighDim.Vocabulary.nuclearNorm Mhat)) := by
      have h1 := mul_le_mul_of_nonneg_left hconv hlamnn
      have h2 : lam * (s * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
          - Statlib.HighDim.Vocabulary.nuclearNorm Mhat))
          = s * (lam * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
            - Statlib.HighDim.Vocabulary.nuclearNorm Mhat)) := by ring
      linarith [h1, h2]
    have hbound : 0 ≤ -2 * s * Acurv + 2 * s * frobInner Evec H
        + s ^ 2 * secondMomentForm Sigma H
        + s * (lam * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
            - Statlib.HighDim.Vocabulary.nuclearNorm Mhat)) := by
      linarith [hnet', hmul]
    have hfact : -2 * s * Acurv + 2 * s * frobInner Evec H
        + s ^ 2 * secondMomentForm Sigma H
        + s * (lam * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
            - Statlib.HighDim.Vocabulary.nuclearNorm Mhat))
        = s * (-2 * Acurv + 2 * frobInner Evec H + s * secondMomentForm Sigma H
            + lam * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
              - Statlib.HighDim.Vocabulary.nuclearNorm Mhat)) := by ring
    have h2 : (0:ℝ) ≤ s * (-2 * Acurv + 2 * frobInner Evec H
        + s * secondMomentForm Sigma H
        + lam * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
          - Statlib.HighDim.Vocabulary.nuclearNorm Mhat)) := by
      rw [← hfact]
      exact hbound
    exact (mul_nonneg_iff_of_pos_left hs0).mp h2
  have hstep2 : 2 * Acurv ≤ 2 * frobInner Evec H - lam * frobInner V0 H := by
    have hqH_nn : 0 ≤ secondMomentForm Sigma H := by
      rw [← hBB H]
      exact hBnn H
    have hpos : 0 < secondMomentForm Sigma H + 1 := by linarith
    have hmain : 0 ≤ -2 * Acurv + 2 * frobInner Evec H
        + lam * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
            - Statlib.HighDim.Vocabulary.nuclearNorm Mhat) := by
      have key2 : ∀ eps : ℝ, 0 < eps →
          0 ≤ -2 * Acurv + 2 * frobInner Evec H
              + lam * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
                - Statlib.HighDim.Vocabulary.nuclearNorm Mhat) + eps := by
        intro eps heps
        have ht0 : 0 < min (1/2) (eps / (secondMomentForm Sigma H + 1)) :=
          lt_min (by norm_num) (div_pos heps hpos)
        have ht1 : min (1/2) (eps / (secondMomentForm Sigma H + 1)) ≤ 1 := by
          have h := min_le_left (1/2 : ℝ) (eps / (secondMomentForm Sigma H + 1))
          linarith
        have hle : min (1/2) (eps / (secondMomentForm Sigma H + 1))
            ≤ eps / (secondMomentForm Sigma H + 1) := min_le_right _ _
        have hr : secondMomentForm Sigma H / (secondMomentForm Sigma H + 1) ≤ 1 := by
          rw [div_le_one hpos]
          linarith
        have h1 : min (1/2) (eps / (secondMomentForm Sigma H + 1)) * secondMomentForm Sigma H
            ≤ (eps / (secondMomentForm Sigma H + 1)) * secondMomentForm Sigma H :=
          mul_le_mul_of_nonneg_right hle hqH_nn
        have h2 : (eps / (secondMomentForm Sigma H + 1)) * secondMomentForm Sigma H
            = eps * (secondMomentForm Sigma H / (secondMomentForm Sigma H + 1)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        have h3 : eps * (secondMomentForm Sigma H / (secondMomentForm Sigma H + 1)) ≤ eps * 1 :=
          mul_le_mul_of_nonneg_left hr (le_of_lt heps)
        have htq : min (1/2) (eps / (secondMomentForm Sigma H + 1)) * secondMomentForm Sigma H
            ≤ eps := by linarith
        have h := hray _ ht0 ht1
        linarith [h, htq]
      exact le_of_forall_pos_le_add key2
    have hupper : Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
        - Statlib.HighDim.Vocabulary.nuclearNorm Mhat ≤ -frobInner V0 H := by
      have h1 : frobInner V0 Mhat ≤ Statlib.HighDim.Vocabulary.nuclearNorm Mhat := hV0sub Mhat
      have h2 : frobInner V0 H = frobInner V0 Mhat - frobInner V0 (M0 t) := by
        rw [hHdef, hfrob_sub_right]
      linarith [hV0Mnuc, h1, h2]
    have hmul2 : lam * (Statlib.HighDim.Vocabulary.nuclearNorm (M0 t)
        - Statlib.HighDim.Vocabulary.nuclearNorm Mhat) ≤ lam * (-frobInner V0 H) :=
      mul_le_mul_of_nonneg_left hupper hlamnn
    linarith [hmain, hmul2]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hEHraw⟩ := statopia_math_node_2628551730_d82d74eb m1 m2 (M0 t) svd 0 0 Evec H
  have hEH : frobInner Evec H ≤ Real.sqrt 2 * R * W * e + W * Nperp := by
    have hsqrt : Real.sqrt (2 * ((M0 t).rank : ℝ)) = Real.sqrt 2 * R := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), hRdef]
    have h := hEHraw
    rw [hsqrt] at h
    exact h
  have hV0H2 : -R * e + Nperp ≤ frobInner V0 H := hV0Hraw
  have hstep4 : 2 * Acurv ≤ (1 + Real.sqrt 2) * lam * R * e := by
    have hmulE : 2 * frobInner Evec H ≤ 2 * (Real.sqrt 2 * R * W * e + W * Nperp) :=
      mul_le_mul_of_nonneg_left hEH (by norm_num : (0:ℝ) ≤ 2)
    have hmulV : -lam * frobInner V0 H ≤ lam * R * e - lam * Nperp := by
      have h1 : lam * (-R * e + Nperp) ≤ lam * frobInner V0 H :=
        mul_le_mul_of_nonneg_left hV0H2 hlamnn
      have h2 : -(lam * frobInner V0 H) ≤ -(lam * (-R * e + Nperp)) := neg_le_neg h1
      have h3 : -(lam * (-R * e + Nperp)) = lam * R * e - lam * Nperp := by ring
      have h4 : -lam * frobInner V0 H = -(lam * frobInner V0 H) := by ring
      linarith [h2, h3, h4]
    have hNterm : (2 * W - lam) * Nperp ≤ 0 := by
      have h1 : 2 * W - lam ≤ 0 := by linarith
      have h2 : (2 * W - lam) * Nperp ≤ 0 * Nperp := mul_le_mul_of_nonneg_right h1 hNperp_nn
      linarith
    have hcomb : 2 * Acurv ≤ (2 * (Real.sqrt 2 * R) * W + lam * R) * e := by
      have hsum : 2 * Acurv ≤
          2 * (Real.sqrt 2 * R * W * e + W * Nperp) + (lam * R * e - lam * Nperp) := by
        linarith [hstep2, hmulE, hmulV]
      have hsplit : 2 * (Real.sqrt 2 * R * W * e + W * Nperp) + (lam * R * e - lam * Nperp)
          = (2 * (Real.sqrt 2 * R) * W + lam * R) * e + (2 * W - lam) * Nperp := by ring
      linarith [hsum, hsplit, hNterm]
    have hcoef : 2 * (Real.sqrt 2 * R) * W + lam * R ≤ (1 + Real.sqrt 2) * lam * R := by
      have hA : 2 * W * R ≤ lam * R := by
        have h := mul_le_mul_of_nonneg_right hlamW hR_nn
        linarith [h]
      have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have hB : Real.sqrt 2 * (2 * W * R) ≤ Real.sqrt 2 * (lam * R) :=
        mul_le_mul_of_nonneg_left hA hs2
      have hC : 2 * (Real.sqrt 2 * R) * W = Real.sqrt 2 * (2 * W * R) := by ring
      have hD : Real.sqrt 2 * (lam * R) + lam * R = (1 + Real.sqrt 2) * lam * R := by ring
      linarith [hB, hC, hD]
    have hfin : (2 * (Real.sqrt 2 * R) * W + lam * R) * e ≤ ((1 + Real.sqrt 2) * lam * R) * e :=
      mul_le_mul_of_nonneg_right hcoef he_nn
    linarith [hcomb, hfin]
  have hchain : 2 * mu * (e ^ 2 - kappa * delta * e) ≤ (1 + Real.sqrt 2) * lam * R * e := by
    have h5 : 2 * mu * (e ^ 2 - kappa * delta * e) ≤ 2 * Acurv := by linarith [hcurvA]
    linarith [h5, hstep4]
  have hbias : biasH M0 w t = delta := by
    unfold biasH
    rw [← hMbardef, ← hDdef, ← hdeltadef]
  have hfinal : e ≤ kappa * delta + ((1 + Real.sqrt 2) / 2) * (lam / mu) * R := by
    rcases eq_or_lt_of_le he_nn with he0 | hepos
    · rw [← he0]
      have h1 : 0 ≤ kappa * delta := mul_nonneg (le_of_lt hkappa_pos) hd_nn
      have h2 : 0 ≤ ((1 + Real.sqrt 2) / 2) * (lam / mu) * R := by
        have ha : 0 ≤ (1 + Real.sqrt 2) / 2 := by
          have hs := Real.sqrt_nonneg 2
          linarith
        have hb : 0 ≤ lam / mu := div_nonneg hlamnn (le_of_lt hmu_pos)
        exact mul_nonneg (mul_nonneg ha hb) hR_nn
      linarith only [h1, h2]
    · have h2mu : 0 < 2 * mu := by linarith
      have h2mue : 0 < 2 * mu * e := by
        have h1 : 0 < mu * e := mul_pos hmu_pos hepos
        linarith
      have hm : mu ≠ 0 := ne_of_gt hmu_pos
      have hcanc : mu * (lam / mu) = lam := by
        field_simp
      have hB : (2 * mu) * (((1 + Real.sqrt 2) / 2) * (lam / mu) * R)
          = (1 + Real.sqrt 2) * lam * R := by
        have h1 : (2 * mu) * (((1 + Real.sqrt 2) / 2) * (lam / mu) * R)
            = (2 * ((1 + Real.sqrt 2) / 2)) * (mu * (lam / mu)) * R := by ring
        rw [hcanc] at h1
        rw [h1]
        ring
      have hmul : (2 * mu) * (e ^ 2 - kappa * delta * e)
          ≤ ((2 * mu) * (((1 + Real.sqrt 2) / 2) * (lam / mu) * R)) * e := by
        rw [hB]
        exact hchain
      have hpos' : (0:ℝ) ≤ (2 * mu * e) *
          ((((1 + Real.sqrt 2) / 2) * (lam / mu) * R) - (e - kappa * delta)) := by
        linarith only [hmul]
      have hkey : e - kappa * delta ≤ ((1 + Real.sqrt 2) / 2) * (lam / mu) * R := by
        have hle := (mul_nonneg_iff_of_pos_left h2mue).mp hpos'
        linarith only [hle]
      linarith only [hkey]
  have hfinal' := hfinal
  rw [hRdef] at hfinal'
  rw [hbias]
  exact hfinal'
  /- @proof-region region.target-node.session.3f3eb936d771d16a end -/

end Statlib.Imported

