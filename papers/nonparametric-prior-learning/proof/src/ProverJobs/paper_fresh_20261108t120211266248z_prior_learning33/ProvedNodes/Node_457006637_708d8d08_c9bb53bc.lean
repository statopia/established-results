import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_457006637_708d8d08 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Type*) [TopologicalSpace X]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (Γh : H →ₗ[ℝ] H) (Γih : H → H)
    (hΓih_left : ∀ v : H, Γih (Γh v) = v)
    (ιH : Type*) [Preorder ιH]
    (bH : HilbertBasis ιH ℝ H) (mu : ιH → ℝ)
    (hmu_pos : ∀ i : ιH, 0 < mu i) (hmu_anti : Antitone mu)
    (hmu_bdd : ∃ Cb : ℝ, 0 < Cb ∧ ∀ i : ιH, mu i ≤ Cb)
    (s1 s st α : ℝ)
    (hs1_nonneg : 0 ≤ s1) (hs1_lt : s1 < 1) (hs_gt : s1 < s) (hs_le : s ≤ 1)
    (hst_gt : 0 < st) (hst_le : st ≤ 1) (hα : 0 ≤ α)
    (C1c C2c : ℝ) (hC1c : 0 < C1c) (hC2c : 0 < C2c)
    (M1 : ℝ → ℝ) (hM1_mono : Monotone M1) (hM1_nonneg : ∀ r : ℝ, 0 ≤ M1 r)
    (M2 : ℝ → ℝ → ℝ) (hM2_nonneg : ∀ r1 r2 : ℝ, 0 ≤ M2 r1 r2)
    (hM2_mono_fst : ∀ r2 : ℝ, Monotone (fun r : ℝ => M2 r r2))
    (hM2_mono_snd : ∀ r1 : ℝ, Monotone (fun r : ℝ => M2 r1 r))
    (LG : X → U → H)
    (hA1 : (¬ FiniteDimensional ℝ H) → ∀ (w : H) (ρ : ℝ),
      HScale bH mu (α - s) w → ((Int.floor (α - s1 - 1) : ℤ) : ℝ) ≤ ρ → ρ < α - s1 →
      HScale bH mu (-st) (Γih w) ∧ HScale bH mu st (Γh w) ∧ HScale bH mu (ρ - α) w ∧
      (HScaleNorm bH mu (-st) (Γih w)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C1c * (HScaleNorm bH mu (α - s) w) ^ (1 / 2 : ℝ) ∧
      (HScaleNorm bH mu st (Γh w)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C2c * (HScaleNorm bH mu (ρ - α) w) ^ (1 / 2 : ℝ))
    (hA2 : ∀ (x : X) (u : U), UScale e lam (1 - st) u →
      (HScaleNorm bH mu st (Γih (LG x u))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M1 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))))
    (hA3 : ∀ (x : X) (u1 u2 : U), UScale e lam (1 - st) u1 → UScale e lam (1 - st) u2 →
      UScale e lam (1 - st) (u1 - u2) →
      (HScaleNorm bH mu st (Γih (LG x u1 - LG x u2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M2 (ENNReal.toReal (UScaleDist e lam (1 - st) u1 0))
          (ENNReal.toReal (UScaleDist e lam (1 - st) u2 0))) *
          UScaleDist e lam (1 - st) (u1 - u2) 0)
    (hA4 : ∀ (x' : X) (u : U), UScale e lam (1 - st) u →
      Tendsto (fun x : X => (HScaleNorm bH mu st (Γih (LG x u - LG x' u))) ^ (1 / 2 : ℝ))
        (𝓝 x') (𝓝 0))
    (hLG_all_range : ∀ (x : X) (u : U), UScale e lam (1 - st) u → ∃ w : H, Γh w = LG x u), ∀ (x : X) (y : H) (u0 : U), UScale e lam (1 - st) u0 →
      ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ u : U, UScale e lam (1 - st) u →
          UScaleDist e lam (1 - st) u u0 ≤ ENNReal.ofReal delta →
          |Phi Γih LG u x y - Phi Γih LG u0 x y| ≤
            C * (UScaleDist e lam (1 - st) u u0).toReal := by
  /- @proof-region region.target-node.session.58f750a4b7b07465 begin -/
  intro U _ _ H _ _ X _ e lam hlam_pos hlam_anti
  intro Γh Γih hΓih_left ιH _ bH mu hmu_pos hmu_anti hmu_bdd
  intro s1 s st α hs1_nonneg hs1_lt hs_gt hs_le hst_gt hst_le hα
  intro C1c C2c hC1c hC2c M1 hM1_mono hM1_nonneg M2 hM2_nonneg hM2_mono_fst hM2_mono_snd
  intro LG hA1 hA2 hA3 hA4 hLG_all_range x y u0 hu0
  obtain ⟨Cb, hCb_pos, hCb_le⟩ := hmu_bdd
  have hst2 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hCb2 : 0 < Cb ^ (st / 2) := Real.rpow_pos_of_pos hCb_pos _
  have hrpow : (Cb ^ st) ^ (1 / 2 : ℝ) = Cb ^ (st / 2) := by
    have hA : Cb ^ (st * (1 / 2)) = (Cb ^ st) ^ (1 / 2 : ℝ) := Real.rpow_mul (le_of_lt hCb_pos) st (1 / 2)
    rw [← hA]
    congr 1
    ring
  have hkey : ∀ w : H, ENNReal.ofReal ‖w‖ ≤
      ENNReal.ofReal (Cb ^ (st / 2)) * (HScaleNorm bH mu st w) ^ (1 / 2 : ℝ) := by
    intro w
    have hreal : ∑' i : ιH, (inner ℝ (bH i) w) ^ 2 = ‖w‖ ^ 2 := by
      have h := HilbertBasis.tsum_inner_mul_inner bH w w
      rw [real_inner_self_eq_norm_sq] at h
      rw [← h]
      exact tsum_congr (fun i => by rw [pow_two, real_inner_comm (bH i) w])
    have hsumm : Summable (fun i : ιH => (inner ℝ (bH i) w) ^ 2) := by
      simpa only [pow_two, real_inner_comm] using HilbertBasis.summable_inner_mul_inner bH w w
    have hterm : ∀ i : ιH, ENNReal.ofReal ((inner ℝ (bH i) w) ^ 2) ≤
        ENNReal.ofReal (Cb ^ st) * ENNReal.ofReal (mu i ^ (-st) * (inner ℝ (bH i) w) ^ 2) := by
      intro i
      have hi : 0 < mu i := hmu_pos i
      have heq : mu i ^ st * (mu i ^ (-st) * (inner ℝ (bH i) w) ^ 2) = (inner ℝ (bH i) w) ^ 2 := by
        rw [← mul_assoc, ← Real.rpow_add hi, show st + -st = 0 by ring, Real.rpow_zero, one_mul]
      calc ENNReal.ofReal ((inner ℝ (bH i) w) ^ 2)
          = ENNReal.ofReal (mu i ^ st * (mu i ^ (-st) * (inner ℝ (bH i) w) ^ 2)) := by rw [heq]
        _ = ENNReal.ofReal (mu i ^ st) * ENNReal.ofReal (mu i ^ (-st) * (inner ℝ (bH i) w) ^ 2) :=
            ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hi) st)
        _ ≤ ENNReal.ofReal (Cb ^ st) * ENNReal.ofReal (mu i ^ (-st) * (inner ℝ (bH i) w) ^ 2) :=
            mul_le_mul_left
              (ENNReal.ofReal_mono (Real.rpow_le_rpow (le_of_lt hi) (hCb_le i) (le_of_lt hst_gt))) _
    have hsq_le : ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal (Cb ^ st) * HScaleNorm bH mu st w := by
      calc ENNReal.ofReal (‖w‖ ^ 2)
          = ∑' i : ιH, ENNReal.ofReal ((inner ℝ (bH i) w) ^ 2) := by
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hsumm, hreal]
        _ ≤ ∑' i : ιH, ENNReal.ofReal (Cb ^ st) *
              ENNReal.ofReal (mu i ^ (-st) * (inner ℝ (bH i) w) ^ 2) := ENNReal.tsum_le_tsum hterm
        _ = ENNReal.ofReal (Cb ^ st) * HScaleNorm bH mu st w := ENNReal.tsum_mul_left
    have hsq : (ENNReal.ofReal (‖w‖ ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal ‖w‖ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) hst2, ← Real.sqrt_eq_rpow,
        Real.sqrt_sq (norm_nonneg w)]
    calc ENNReal.ofReal ‖w‖
        = (ENNReal.ofReal (‖w‖ ^ 2)) ^ (1 / 2 : ℝ) := hsq.symm
      _ ≤ (ENNReal.ofReal (Cb ^ st) * HScaleNorm bH mu st w) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hsq_le hst2
      _ = (ENNReal.ofReal (Cb ^ st)) ^ (1 / 2 : ℝ) * (HScaleNorm bH mu st w) ^ (1 / 2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ hst2
      _ = ENNReal.ofReal (Cb ^ (st / 2)) * (HScaleNorm bH mu st w) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt (Real.rpow_pos_of_pos hCb_pos st)) hst2, hrpow]
  have hbound : ∀ (w : H) (c : ℝ), 0 ≤ c →
      (HScaleNorm bH mu st w) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c → ‖w‖ ≤ Cb ^ (st / 2) * c := by
    intro w c hc hwc
    have hK : 0 ≤ Cb ^ (st / 2) * c := mul_nonneg (le_of_lt hCb2) hc
    have hle : ENNReal.ofReal ‖w‖ ≤ ENNReal.ofReal (Cb ^ (st / 2) * c) := by
      refine (hkey w).trans ?_
      rw [ENNReal.ofReal_mul (le_of_lt hCb2)]
      exact mul_le_mul_right hwc _
    exact (ENNReal.ofReal_le_ofReal_iff hK).1 hle
  have hUAdd : ∀ a b : U, UScaleNorm e lam (1 - st) (a + b) ≤
      (UScaleNorm e lam (1 - st) a + UScaleNorm e lam (1 - st) a) +
        (UScaleNorm e lam (1 - st) b + UScaleNorm e lam (1 - st) b) := by
    intro a b
    have hterm : ∀ k : ℕ, ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) (a + b)) ^ 2) ≤
        (ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2) +
          ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2)) +
        (ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2) +
          ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2)) := by
      intro k
      have hlam : 0 ≤ lam k ^ (-(1 - st)) := Real.rpow_nonneg (le_of_lt (hlam_pos k)) _
      have hsq : (inner ℝ (e k) (a + b)) ^ 2 ≤
          ((inner ℝ (e k) a) ^ 2 + (inner ℝ (e k) a) ^ 2) +
            ((inner ℝ (e k) b) ^ 2 + (inner ℝ (e k) b) ^ 2) := by
        rw [inner_add_right]
        nlinarith [sq_nonneg (inner ℝ (e k) a - inner ℝ (e k) b)]
      have hna : 0 ≤ lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2 := mul_nonneg hlam (sq_nonneg _)
      have hnb : 0 ≤ lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2 := mul_nonneg hlam (sq_nonneg _)
      have hreal : lam k ^ (-(1 - st)) * (inner ℝ (e k) (a + b)) ^ 2 ≤
          (lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2 +
            lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2) +
          (lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2 +
            lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2) := by
        nlinarith [hlam, hsq, hna, hnb]
      calc ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) (a + b)) ^ 2)
          ≤ ENNReal.ofReal ((lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2 +
              lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2) +
              (lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2 +
                lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2)) := ENNReal.ofReal_mono hreal
        _ = (ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2) +
              ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2)) +
            (ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2) +
              ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2)) := by
            rw [ENNReal.ofReal_add (by linarith) (by linarith), ENNReal.ofReal_add hna hna,
              ENNReal.ofReal_add hnb hnb]
    calc UScaleNorm e lam (1 - st) (a + b)
        = ∑' k : ℕ, ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) (a + b)) ^ 2) := rfl
      _ ≤ ∑' k : ℕ, ((ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2) +
              ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) a) ^ 2)) +
            (ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2) +
              ENNReal.ofReal (lam k ^ (-(1 - st)) * (inner ℝ (e k) b) ^ 2))) :=
          ENNReal.tsum_le_tsum hterm
      _ = (UScaleNorm e lam (1 - st) a + UScaleNorm e lam (1 - st) a) +
            (UScaleNorm e lam (1 - st) b + UScaleNorm e lam (1 - st) b) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
          rfl
  refine ⟨1, by norm_num,
    (Cb ^ (st / 2) * M1 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal)) + ‖Γih y‖) *
      (Cb ^ (st / 2) * M2 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal))
        ((UScaleDist e lam (1 - st) u0 0).toReal)), ?_, ?_⟩
  · exact mul_nonneg (add_nonneg (mul_nonneg (le_of_lt hCb2) (hM1_nonneg _)) (norm_nonneg _))
      (mul_nonneg (le_of_lt hCb2) (hM2_nonneg _ _))
  · intro u hu hD
    have hDfin : UScaleDist e lam (1 - st) u u0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD
    have hDsub : UScale e lam (1 - st) (u - u0) := by
      have hlt : UScaleDist e lam (1 - st) u u0 < ⊤ :=
        lt_of_le_of_lt hD (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
      have hmid : (UScaleNorm e lam (1 - st) (u - u0)) ^ (1 / 2 : ℝ) < ⊤ := hlt
      exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 hmid
    have hDle1 : (UScaleDist e lam (1 - st) u u0).toReal ≤ 1 := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hD
      rwa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1)] at h
    have hAf : UScaleNorm e lam (1 - st) (u - u0) < ⊤ := hDsub
    have hBf : UScaleNorm e lam (1 - st) u0 < ⊤ := hu0
    have hAne : UScaleNorm e lam (1 - st) (u - u0) ≠ ⊤ := ne_of_lt hAf
    have hBne : UScaleNorm e lam (1 - st) u0 ≠ ⊤ := ne_of_lt hBf
    have hrueq : (UScaleDist e lam (1 - st) u 0).toReal =
        ((UScaleNorm e lam (1 - st) u).toReal) ^ (1 / 2 : ℝ) := by
      rw [UScaleDist, sub_zero, ← ENNReal.toReal_rpow]
    have hR0eq : (UScaleDist e lam (1 - st) u0 0).toReal =
        ((UScaleNorm e lam (1 - st) u0).toReal) ^ (1 / 2 : ℝ) := by
      rw [UScaleDist, sub_zero, ← ENNReal.toReal_rpow]
    have hboundD : ∀ (w : H) (c : ℝ), 0 ≤ c →
        (HScaleNorm bH mu st w) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c * UScaleDist e lam (1 - st) u u0 →
        ‖w‖ ≤ Cb ^ (st / 2) * c * (UScaleDist e lam (1 - st) u u0).toReal := by
      intro w c hc hwc
      have hK : 0 ≤ Cb ^ (st / 2) * c := mul_nonneg (le_of_lt hCb2) hc
      have hstep : ENNReal.ofReal ‖w‖ ≤
          ENNReal.ofReal (Cb ^ (st / 2) * c) * UScaleDist e lam (1 - st) u u0 := by
        refine (hkey w).trans ?_
        rw [ENNReal.ofReal_mul (le_of_lt hCb2), mul_assoc]
        exact mul_le_mul_right hwc _
      have hfin : ENNReal.ofReal (Cb ^ (st / 2) * c) * UScaleDist e lam (1 - st) u u0 ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin
      have h := ENNReal.toReal_mono hfin hstep
      rwa [ENNReal.toReal_ofReal (norm_nonneg w), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hK] at h
    have hR0nn : 0 ≤ (UScaleDist e lam (1 - st) u0 0).toReal := ENNReal.toReal_nonneg
    have hsq2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hR0le : (UScaleDist e lam (1 - st) u0 0).toReal ≤
        Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal) := by
      nlinarith [hR0nn, hsq2]
    have hA1' : (UScaleNorm e lam (1 - st) (u - u0)).toReal ≤ 1 := by
      have h := hDle1
      rw [UScaleDist, ← ENNReal.toReal_rpow] at h
      have hnn : 0 ≤ (UScaleNorm e lam (1 - st) (u - u0)).toReal := ENNReal.toReal_nonneg
      have hs : Real.sqrt ((UScaleNorm e lam (1 - st) (u - u0)).toReal) ≤ 1 := by
        rwa [Real.sqrt_eq_rpow]
      nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg ((UScaleNorm e lam (1 - st) (u - u0)).toReal)]
    have hnormU : UScaleNorm e lam (1 - st) u ≤
        (UScaleNorm e lam (1 - st) (u - u0) + UScaleNorm e lam (1 - st) (u - u0)) +
          (UScaleNorm e lam (1 - st) u0 + UScaleNorm e lam (1 - st) u0) := by
      have h := hUAdd (u - u0) u0
      rwa [sub_add_cancel] at h
    have hfinR : ((UScaleNorm e lam (1 - st) (u - u0) + UScaleNorm e lam (1 - st) (u - u0)) +
          (UScaleNorm e lam (1 - st) u0 + UScaleNorm e lam (1 - st) u0)) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hAne, hAne⟩, ENNReal.add_ne_top.2 ⟨hBne, hBne⟩⟩
    have hnormUt : (UScaleNorm e lam (1 - st) u).toReal ≤
        ((UScaleNorm e lam (1 - st) (u - u0)).toReal + (UScaleNorm e lam (1 - st) (u - u0)).toReal) +
          ((UScaleNorm e lam (1 - st) u0).toReal + (UScaleNorm e lam (1 - st) u0).toReal) := by
      have h := ENNReal.toReal_mono hfinR hnormU
      rwa [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hAne, hAne⟩) (ENNReal.add_ne_top.2 ⟨hBne, hBne⟩),
        ENNReal.toReal_add hAne hAne, ENNReal.toReal_add hBne hBne] at h
    have hAle : (UScaleNorm e lam (1 - st) u).toReal ≤
        1 + 1 + ((UScaleNorm e lam (1 - st) u0).toReal + (UScaleNorm e lam (1 - st) u0).toReal) := by
      nlinarith [hnormUt, hA1']
    have hrle : (UScaleDist e lam (1 - st) u 0).toReal ≤
        Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal) := by
      rw [hrueq, hR0eq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      have hBnn : 0 ≤ (UScaleNorm e lam (1 - st) u0).toReal := ENNReal.toReal_nonneg
      have hstep : Real.sqrt ((UScaleNorm e lam (1 - st) u).toReal) ≤
          Real.sqrt (2 + 2 * (UScaleNorm e lam (1 - st) u0).toReal) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [hAle]
      refine hstep.trans ?_
      have hBsq : Real.sqrt ((UScaleNorm e lam (1 - st) u0).toReal) ^ 2 =
          (UScaleNorm e lam (1 - st) u0).toReal := Real.sq_sqrt hBnn
      have hsq : 2 + 2 * (UScaleNorm e lam (1 - st) u0).toReal ≤
          2 * (1 + Real.sqrt ((UScaleNorm e lam (1 - st) u0).toReal)) ^ 2 := by
        nlinarith [hBsq, Real.sqrt_nonneg ((UScaleNorm e lam (1 - st) u0).toReal)]
      calc Real.sqrt (2 + 2 * (UScaleNorm e lam (1 - st) u0).toReal)
          ≤ Real.sqrt (2 * (1 + Real.sqrt ((UScaleNorm e lam (1 - st) u0).toReal)) ^ 2) :=
            Real.sqrt_le_sqrt hsq
        _ = Real.sqrt 2 * (1 + Real.sqrt ((UScaleNorm e lam (1 - st) u0).toReal)) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (by positivity)]
    have hKnn : 0 ≤ Cb ^ (st / 2) * M1 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal)) :=
      mul_nonneg (le_of_lt hCb2) (hM1_nonneg _)
    have hnorm_vu : ‖Γih (LG x u)‖ ≤
        Cb ^ (st / 2) * M1 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal)) := by
      refine (hbound _ _ (hM1_nonneg _) (hA2 x u hu)).trans ?_
      exact mul_le_mul_of_nonneg_left (hM1_mono hrle) (le_of_lt hCb2)
    have hnorm_vu0 : ‖Γih (LG x u0)‖ ≤
        Cb ^ (st / 2) * M1 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal)) := by
      refine (hbound _ _ (hM1_nonneg _) (hA2 x u0 hu0)).trans ?_
      exact mul_le_mul_of_nonneg_left (hM1_mono hR0le) (le_of_lt hCb2)
    have hnorm_sum : ‖Γih (LG x u) + Γih (LG x u0)‖ ≤
        Cb ^ (st / 2) * M1 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal)) +
          (Cb ^ (st / 2) * M1 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal))) := by
      refine (norm_add_le _ _).trans ?_
      linarith
    have hvs : Γih (LG x u) - Γih (LG x u0) = Γih (LG x u - LG x u0) := by
      obtain ⟨w1, hw1⟩ := hLG_all_range x u hu
      obtain ⟨w2, hw2⟩ := hLG_all_range x u0 hu0
      have e1 : Γih (LG x u) = w1 := by rw [← hw1]; exact hΓih_left w1
      have e2 : Γih (LG x u0) = w2 := by rw [← hw2]; exact hΓih_left w2
      rw [e1, e2, ← hw1, ← hw2, ← Γh.map_sub]
      exact (hΓih_left (w1 - w2)).symm
    have hnorm_diff : ‖Γih (LG x u) - Γih (LG x u0)‖ ≤
        Cb ^ (st / 2) * M2 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal))
            ((UScaleDist e lam (1 - st) u0 0).toReal) *
          (UScaleDist e lam (1 - st) u u0).toReal := by
      rw [hvs]
      have h3 := hA3 x u u0 hu hu0 hDsub
      have heq : UScaleDist e lam (1 - st) (u - u0) 0 = UScaleDist e lam (1 - st) u u0 := by
        simp only [UScaleDist, sub_zero]
      rw [heq] at h3
      have h := hboundD (Γih (LG x u - LG x u0))
        (M2 (ENNReal.toReal (UScaleDist e lam (1 - st) u 0))
          (ENNReal.toReal (UScaleDist e lam (1 - st) u0 0)))
        (hM2_nonneg _ _) h3
      refine h.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
      exact mul_le_mul_of_nonneg_left
        (hM2_mono_fst ((UScaleDist e lam (1 - st) u0 0).toReal) hrle) (le_of_lt hCb2)
    have hPhi_sub : Phi Γih LG u x y - Phi Γih LG u0 x y
        = (1 / 2) * (inner ℝ (Γih (LG x u)) (Γih (LG x u)) -
            inner ℝ (Γih (LG x u0)) (Γih (LG x u0)))
          - inner ℝ (Γih y) (Γih (LG x u) - Γih (LG x u0)) := by
      simp only [Phi]
      rw [inner_sub_right]
      have h1 : ‖Γih (LG x u)‖ ^ 2 = inner ℝ (Γih (LG x u)) (Γih (LG x u)) :=
        (real_inner_self_eq_norm_sq _).symm
      have h2 : ‖Γih (LG x u0)‖ ^ 2 = inner ℝ (Γih (LG x u0)) (Γih (LG x u0)) :=
        (real_inner_self_eq_norm_sq _).symm
      rw [h1, h2]
      ring
    have hsqdiff : inner ℝ (Γih (LG x u) - Γih (LG x u0)) (Γih (LG x u) + Γih (LG x u0))
        = inner ℝ (Γih (LG x u)) (Γih (LG x u)) -
          inner ℝ (Γih (LG x u0)) (Γih (LG x u0)) := by
      rw [inner_add_right, inner_sub_left, inner_sub_left,
        real_inner_comm (Γih (LG x u0)) (Γih (LG x u))]
      ring
    have hstep1 : |Phi Γih LG u x y - Phi Γih LG u0 x y| ≤
        ((1 / 2) * ‖Γih (LG x u) + Γih (LG x u0)‖ + ‖Γih y‖) *
          ‖Γih (LG x u) - Γih (LG x u0)‖ := by
      rw [hPhi_sub, ← hsqdiff]
      have h1 : |(1 / 2 : ℝ) * inner ℝ (Γih (LG x u) - Γih (LG x u0))
            (Γih (LG x u) + Γih (LG x u0))| ≤
          (1 / 2) * (‖Γih (LG x u) - Γih (LG x u0)‖ * ‖Γih (LG x u) + Γih (LG x u0)‖) := by
        have hCS := abs_real_inner_le_norm (Γih (LG x u) - Γih (LG x u0))
          (Γih (LG x u) + Γih (LG x u0))
        have h12 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
        rw [abs_mul, h12]
        exact mul_le_mul_of_nonneg_left hCS (by norm_num)
      have h2 : |inner ℝ (Γih y) (Γih (LG x u) - Γih (LG x u0))| ≤
          ‖Γih y‖ * ‖Γih (LG x u) - Γih (LG x u0)‖ := abs_real_inner_le_norm _ _
      calc |(1 / 2 : ℝ) * inner ℝ (Γih (LG x u) - Γih (LG x u0)) (Γih (LG x u) + Γih (LG x u0)) -
            inner ℝ (Γih y) (Γih (LG x u) - Γih (LG x u0))|
          = |(1 / 2 : ℝ) * inner ℝ (Γih (LG x u) - Γih (LG x u0)) (Γih (LG x u) + Γih (LG x u0)) +
              (-(inner ℝ (Γih y) (Γih (LG x u) - Γih (LG x u0))))| := by rw [sub_eq_add_neg]
        _ ≤ |(1 / 2 : ℝ) * inner ℝ (Γih (LG x u) - Γih (LG x u0))
                (Γih (LG x u) + Γih (LG x u0))| +
              |-(inner ℝ (Γih y) (Γih (LG x u) - Γih (LG x u0)))| := abs_add_le _ _
        _ = |(1 / 2 : ℝ) * inner ℝ (Γih (LG x u) - Γih (LG x u0))
                (Γih (LG x u) + Γih (LG x u0))| +
              |inner ℝ (Γih y) (Γih (LG x u) - Γih (LG x u0))| := by rw [abs_neg]
        _ ≤ (1 / 2) * (‖Γih (LG x u) - Γih (LG x u0)‖ * ‖Γih (LG x u) + Γih (LG x u0)‖) +
              ‖Γih y‖ * ‖Γih (LG x u) - Γih (LG x u0)‖ := add_le_add h1 h2
        _ = ((1 / 2) * ‖Γih (LG x u) + Γih (LG x u0)‖ + ‖Γih y‖) *
              ‖Γih (LG x u) - Γih (LG x u0)‖ := by ring
    have hhalf : (1 / 2) * ‖Γih (LG x u) + Γih (LG x u0)‖ + ‖Γih y‖ ≤
        Cb ^ (st / 2) * M1 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal)) + ‖Γih y‖ := by
      linarith [hnorm_sum]
    have hseven : 0 ≤ Cb ^ (st / 2) * M1 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal)) + ‖Γih y‖ :=
      add_nonneg hKnn (norm_nonneg _)
    calc |Phi Γih LG u x y - Phi Γih LG u0 x y|
        ≤ ((1 / 2) * ‖Γih (LG x u) + Γih (LG x u0)‖ + ‖Γih y‖) *
            ‖Γih (LG x u) - Γih (LG x u0)‖ := hstep1
      _ ≤ (Cb ^ (st / 2) * M1 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal)) + ‖Γih y‖) *
            (Cb ^ (st / 2) * M2 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal))
                ((UScaleDist e lam (1 - st) u0 0).toReal) *
              (UScaleDist e lam (1 - st) u u0).toReal) :=
          mul_le_mul hhalf hnorm_diff (norm_nonneg _) hseven
      _ = ((Cb ^ (st / 2) * M1 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal)) + ‖Γih y‖) *
            (Cb ^ (st / 2) * M2 (Real.sqrt 2 * (1 + (UScaleDist e lam (1 - st) u0 0).toReal))
                ((UScaleDist e lam (1 - st) u0 0).toReal))) *
              (UScaleDist e lam (1 - st) u u0).toReal := by ring
  /- @proof-region region.target-node.session.58f750a4b7b07465 end -/

end Statlib.Imported
end

