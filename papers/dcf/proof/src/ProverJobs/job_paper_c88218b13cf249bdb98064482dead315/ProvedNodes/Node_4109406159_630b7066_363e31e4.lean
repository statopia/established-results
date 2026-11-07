import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base

namespace PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported

noncomputable section
universe u
open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_4109406159_630b7066 : ∀ (Cb c1 c2 d3 rE rho phi1 phi2 : ℝ) (LXe LYe Mne Mse LX LY Mn Ms lD lp : ℝ)
    (hCb : 0 < Cb)
    (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2)
    (hd3 : 0 ≤ d3)
    (hrE : 0 ≤ rE)
    (hrho : 0 ≤ rho)
    (hrErho : rE ≤ rho)
    (hLXe : LXe ≤ LX)
    (hLYe : LYe ≤ LY)
    (hMne : Mne ≤ Mn)
    (hMse : Mse ≤ Ms)
    (hLX : 0 ≤ LX)
    (hLY : 0 ≤ LY)
    (hMn : 0 ≤ Mn)
    (hMs : 0 ≤ Ms)
    (hphi1 : 0 < phi1)
    (hphi2 : 0 < phi2)
    (hlp : 0 ≤ lp)
    (hlD : 0 < lD)
    (hlDlp : lD ≤ 2 * lp)
    (hbound : rE ≤ Cb *
      (c1 * (phi1 / 2) ^ 2 * lD ^ 2 *
          ((phi1 / 2 * LXe) * rE + LXe * Real.sqrt lD + phi1 / 2 * Mne)
        + c2 * (phi2 / 2) ^ 2 * lD ^ 2 * d3 *
            ((phi2 / 2 * LYe) * rE + LYe * Real.sqrt lD + phi2 / 2 * Mse)
        + (min (phi1 / 2) (phi2 / 2))⁻¹ * Real.sqrt lD)),
    rE ≤ 8 * Cb *
      (c1 * phi1 ^ 2 * lp ^ 2 * (phi1 * LX * rho + LX * Real.sqrt lp + phi1 * Mn)
        + c2 * phi2 ^ 2 * lp ^ 2 * d3 * (phi2 * LY * rho + LY * Real.sqrt lp + phi2 * Ms)
        + (min phi1 phi2)⁻¹ * Real.sqrt lp) := by
  /- @proof-region region.target-node.session.8ba70f74aaa6ac3b begin -/
  intro Cb c1 c2 d3 rE rho phi1 phi2 LXe LYe Mne Mse LX LY Mn Ms lD lp
    hCb hc1 hc2 hd3 hrE hrho hrErho hLXe hLYe hMne hMse hLX hLY hMn hMs hphi1 hphi2 hlp hlD hlDlp hbound
  set e1 := c1 * (phi1 / 2) ^ 2 * lD ^ 2 * ((phi1 / 2 * LXe) * rE + LXe * Real.sqrt lD + phi1 / 2 * Mne) with he1
  set e2 := c2 * (phi2 / 2) ^ 2 * lD ^ 2 * d3 * ((phi2 / 2 * LYe) * rE + LYe * Real.sqrt lD + phi2 / 2 * Mse) with he2
  set e3 := (min (phi1 / 2) (phi2 / 2))⁻¹ * Real.sqrt lD with he3
  set t1 := c1 * phi1 ^ 2 * lp ^ 2 * (phi1 * LX * rho + LX * Real.sqrt lp + phi1 * Mn) with ht1
  set t2 := c2 * phi2 ^ 2 * lp ^ 2 * d3 * (phi2 * LY * rho + LY * Real.sqrt lp + phi2 * Ms) with ht2
  set t3 := (min phi1 phi2)⁻¹ * Real.sqrt lp with ht3
  have hsD : Real.sqrt lD ≤ 2 * Real.sqrt lp := by
    have h4lp : Real.sqrt (4 * lp) = 2 * Real.sqrt lp := by
      have hsq : (2 * Real.sqrt lp) ^ 2 = 4 * lp := by
        rw [mul_pow, Real.sq_sqrt hlp]
        norm_num
      rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have hle : Real.sqrt lD ≤ Real.sqrt (4 * lp) := Real.sqrt_le_sqrt (by linarith [hlDlp, hlp])
    linarith [hle, h4lp]
  have hlD2 : lD ^ 2 ≤ 4 * lp ^ 2 := by
    have h1 : (0:ℝ) ≤ 2 * lp - lD := by linarith [hlDlp]
    have h2 : (0:ℝ) ≤ 2 * lp + lD := by linarith [hlp, hlD]
    have h3 : (0:ℝ) ≤ (2 * lp - lD) * (2 * lp + lD) := mul_nonneg h1 h2
    have h4 : (2 * lp - lD) * (2 * lp + lD) = 4 * lp ^ 2 - lD ^ 2 := by ring
    linarith [h3, h4]
  have hE1 : e1 ≤ 4 * t1 := by
    rw [he1, ht1]
    have hLXe' : phi1 / 2 * LXe ≤ phi1 * LX := by
      have s1 : phi1 / 2 * LXe ≤ phi1 / 2 * LX :=
        mul_le_mul_of_nonneg_left hLXe (by linarith [hphi1] : (0:ℝ) ≤ phi1 / 2)
      have s2 : phi1 / 2 * LX ≤ phi1 * LX :=
        mul_le_mul_of_nonneg_right (by linarith [hphi1] : phi1 / 2 ≤ phi1) hLX
      linarith [s1, s2]
    have ha : (phi1 / 2 * LXe) * rE ≤ (phi1 * LX) * rho :=
      mul_le_mul hLXe' hrErho hrE (mul_nonneg hphi1.le hLX)
    have hb : LXe * Real.sqrt lD ≤ 2 * (LX * Real.sqrt lp) := by
      have p1 : LXe * Real.sqrt lD ≤ LX * Real.sqrt lD :=
        mul_le_mul_of_nonneg_right hLXe (Real.sqrt_nonneg lD)
      have p2 : LX * Real.sqrt lD ≤ LX * (2 * Real.sqrt lp) :=
        mul_le_mul_of_nonneg_left hsD hLX
      have p3 : LX * (2 * Real.sqrt lp) = 2 * (LX * Real.sqrt lp) := by ring
      linarith [p1, p2, p3]
    have hc : phi1 / 2 * Mne ≤ phi1 * Mn := by
      have s1 : phi1 / 2 * Mne ≤ phi1 / 2 * Mn :=
        mul_le_mul_of_nonneg_left hMne (by linarith [hphi1] : (0:ℝ) ≤ phi1 / 2)
      have s2 : phi1 / 2 * Mn ≤ phi1 * Mn :=
        mul_le_mul_of_nonneg_right (by linarith [hphi1] : phi1 / 2 ≤ phi1) hMn
      linarith [s1, s2]
    have hB : (0:ℝ) ≤ phi1 * LX * rho := mul_nonneg (mul_nonneg hphi1.le hLX) hrho
    have hE' : (0:ℝ) ≤ LX * Real.sqrt lp := mul_nonneg hLX (Real.sqrt_nonneg lp)
    have hF : (0:ℝ) ≤ phi1 * Mn := mul_nonneg hphi1.le hMn
    have hX : (phi1 / 2 * LXe) * rE + LXe * Real.sqrt lD + phi1 / 2 * Mne ≤
        4 * (phi1 * LX * rho + LX * Real.sqrt lp + phi1 * Mn) := by
      have s1 : (phi1 / 2 * LXe) * rE + LXe * Real.sqrt lD + phi1 / 2 * Mne ≤
          phi1 * LX * rho + 2 * (LX * Real.sqrt lp) + phi1 * Mn := by linarith [ha, hb, hc]
      have s2 : phi1 * LX * rho + 2 * (LX * Real.sqrt lp) + phi1 * Mn ≤
          4 * (phi1 * LX * rho + LX * Real.sqrt lp + phi1 * Mn) := by linarith [hB, hE', hF]
      linarith [s1, s2]
    have hcoefle : c1 * (phi1 / 2) ^ 2 * lD ^ 2 ≤ c1 * phi1 ^ 2 * lp ^ 2 := by
      have hmul : c1 * (phi1 / 2) ^ 2 * lD ^ 2 ≤ c1 * (phi1 / 2) ^ 2 * (4 * lp ^ 2) :=
        mul_le_mul_of_nonneg_left hlD2 (mul_nonneg hc1 (sq_nonneg (phi1 / 2)))
      have heq : c1 * (phi1 / 2) ^ 2 * (4 * lp ^ 2) = c1 * phi1 ^ 2 * lp ^ 2 := by ring
      linarith [hmul, heq]
    have hcoefnn : (0:ℝ) ≤ c1 * (phi1 / 2) ^ 2 * lD ^ 2 :=
      mul_nonneg (mul_nonneg hc1 (sq_nonneg (phi1 / 2))) (sq_nonneg lD)
    have h1 := mul_le_mul_of_nonneg_left hX hcoefnn
    have h2 := mul_le_mul_of_nonneg_right hcoefle
      (by linarith [hB, hE', hF] : (0:ℝ) ≤ 4 * (phi1 * LX * rho + LX * Real.sqrt lp + phi1 * Mn))
    linarith [h1, h2]
  have hE2 : e2 ≤ 4 * t2 := by
    rw [he2, ht2]
    have hLYe' : phi2 / 2 * LYe ≤ phi2 * LY := by
      have s1 : phi2 / 2 * LYe ≤ phi2 / 2 * LY :=
        mul_le_mul_of_nonneg_left hLYe (by linarith [hphi2] : (0:ℝ) ≤ phi2 / 2)
      have s2 : phi2 / 2 * LY ≤ phi2 * LY :=
        mul_le_mul_of_nonneg_right (by linarith [hphi2] : phi2 / 2 ≤ phi2) hLY
      linarith [s1, s2]
    have ha : (phi2 / 2 * LYe) * rE ≤ (phi2 * LY) * rho :=
      mul_le_mul hLYe' hrErho hrE (mul_nonneg hphi2.le hLY)
    have hb : LYe * Real.sqrt lD ≤ 2 * (LY * Real.sqrt lp) := by
      have p1 : LYe * Real.sqrt lD ≤ LY * Real.sqrt lD :=
        mul_le_mul_of_nonneg_right hLYe (Real.sqrt_nonneg lD)
      have p2 : LY * Real.sqrt lD ≤ LY * (2 * Real.sqrt lp) :=
        mul_le_mul_of_nonneg_left hsD hLY
      have p3 : LY * (2 * Real.sqrt lp) = 2 * (LY * Real.sqrt lp) := by ring
      linarith [p1, p2, p3]
    have hc : phi2 / 2 * Mse ≤ phi2 * Ms := by
      have s1 : phi2 / 2 * Mse ≤ phi2 / 2 * Ms :=
        mul_le_mul_of_nonneg_left hMse (by linarith [hphi2] : (0:ℝ) ≤ phi2 / 2)
      have s2 : phi2 / 2 * Ms ≤ phi2 * Ms :=
        mul_le_mul_of_nonneg_right (by linarith [hphi2] : phi2 / 2 ≤ phi2) hMs
      linarith [s1, s2]
    have hB : (0:ℝ) ≤ phi2 * LY * rho := mul_nonneg (mul_nonneg hphi2.le hLY) hrho
    have hE' : (0:ℝ) ≤ LY * Real.sqrt lp := mul_nonneg hLY (Real.sqrt_nonneg lp)
    have hF : (0:ℝ) ≤ phi2 * Ms := mul_nonneg hphi2.le hMs
    have hX : (phi2 / 2 * LYe) * rE + LYe * Real.sqrt lD + phi2 / 2 * Mse ≤
        4 * (phi2 * LY * rho + LY * Real.sqrt lp + phi2 * Ms) := by
      have s1 : (phi2 / 2 * LYe) * rE + LYe * Real.sqrt lD + phi2 / 2 * Mse ≤
          phi2 * LY * rho + 2 * (LY * Real.sqrt lp) + phi2 * Ms := by linarith [ha, hb, hc]
      have s2 : phi2 * LY * rho + 2 * (LY * Real.sqrt lp) + phi2 * Ms ≤
          4 * (phi2 * LY * rho + LY * Real.sqrt lp + phi2 * Ms) := by linarith [hB, hE', hF]
      linarith [s1, s2]
    have hcoefle : c2 * (phi2 / 2) ^ 2 * lD ^ 2 * d3 ≤ c2 * phi2 ^ 2 * lp ^ 2 * d3 := by
      have hmul : c2 * (phi2 / 2) ^ 2 * lD ^ 2 ≤ c2 * (phi2 / 2) ^ 2 * (4 * lp ^ 2) :=
        mul_le_mul_of_nonneg_left hlD2 (mul_nonneg hc2 (sq_nonneg (phi2 / 2)))
      have heq : c2 * (phi2 / 2) ^ 2 * (4 * lp ^ 2) = c2 * phi2 ^ 2 * lp ^ 2 := by ring
      have hbase : c2 * (phi2 / 2) ^ 2 * lD ^ 2 ≤ c2 * phi2 ^ 2 * lp ^ 2 := by linarith [hmul, heq]
      exact mul_le_mul_of_nonneg_right hbase hd3
    have hcoefnn : (0:ℝ) ≤ c2 * (phi2 / 2) ^ 2 * lD ^ 2 * d3 :=
      mul_nonneg (mul_nonneg (mul_nonneg hc2 (sq_nonneg (phi2 / 2))) (sq_nonneg lD)) hd3
    have h1 := mul_le_mul_of_nonneg_left hX hcoefnn
    have h2 := mul_le_mul_of_nonneg_right hcoefle
      (by linarith [hB, hE', hF] : (0:ℝ) ≤ 4 * (phi2 * LY * rho + LY * Real.sqrt lp + phi2 * Ms))
    linarith [h1, h2]
  have hE3 : e3 ≤ 4 * t3 := by
    rw [he3, ht3]
    have hminpos : 0 < min phi1 phi2 := lt_min hphi1 hphi2
    have hmin : min (phi1 / 2) (phi2 / 2) = min phi1 phi2 / 2 := by
      apply le_antisymm
      · have h1 : min (phi1 / 2) (phi2 / 2) ≤ phi1 / 2 := min_le_left _ _
        have h2 : min (phi1 / 2) (phi2 / 2) ≤ phi2 / 2 := min_le_right _ _
        have h3 : 2 * min (phi1 / 2) (phi2 / 2) ≤ min phi1 phi2 := by
          apply le_min <;> linarith [h1, h2]
        linarith [h3]
      · have h1 : min phi1 phi2 ≤ phi1 := min_le_left _ _
        have h2 : min phi1 phi2 ≤ phi2 := min_le_right _ _
        apply le_min <;> linarith [h1, h2]
    have hinv : (min (phi1 / 2) (phi2 / 2))⁻¹ = 2 * (min phi1 phi2)⁻¹ := by
      rw [hmin, inv_div]
      ring
    rw [hinv]
    have hmnn : (0:ℝ) ≤ (min phi1 phi2)⁻¹ := inv_nonneg.mpr hminpos.le
    have h1 : 2 * (min phi1 phi2)⁻¹ * Real.sqrt lD ≤ 2 * (min phi1 phi2)⁻¹ * (2 * Real.sqrt lp) :=
      mul_le_mul_of_nonneg_left hsD (by linarith [hmnn] : (0:ℝ) ≤ 2 * (min phi1 phi2)⁻¹)
    have h2 : 2 * (min phi1 phi2)⁻¹ * (2 * Real.sqrt lp) = 4 * ((min phi1 phi2)⁻¹ * Real.sqrt lp) := by ring
    linarith [h1, h2]
  have hT1 : (0:ℝ) ≤ t1 := by
    rw [ht1]
    have h1 : (0:ℝ) ≤ phi1 * LX * rho := mul_nonneg (mul_nonneg hphi1.le hLX) hrho
    have h2 : (0:ℝ) ≤ LX * Real.sqrt lp := mul_nonneg hLX (Real.sqrt_nonneg lp)
    have h3 : (0:ℝ) ≤ phi1 * Mn := mul_nonneg hphi1.le hMn
    have h4 : (0:ℝ) ≤ phi1 * LX * rho + LX * Real.sqrt lp + phi1 * Mn := by linarith [h1, h2, h3]
    exact mul_nonneg (mul_nonneg (mul_nonneg hc1 (sq_nonneg phi1)) (sq_nonneg lp)) h4
  have hT2 : (0:ℝ) ≤ t2 := by
    rw [ht2]
    have h1 : (0:ℝ) ≤ phi2 * LY * rho := mul_nonneg (mul_nonneg hphi2.le hLY) hrho
    have h2 : (0:ℝ) ≤ LY * Real.sqrt lp := mul_nonneg hLY (Real.sqrt_nonneg lp)
    have h3 : (0:ℝ) ≤ phi2 * Ms := mul_nonneg hphi2.le hMs
    have h4 : (0:ℝ) ≤ phi2 * LY * rho + LY * Real.sqrt lp + phi2 * Ms := by linarith [h1, h2, h3]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc2 (sq_nonneg phi2)) (sq_nonneg lp)) hd3) h4
  have hT3 : (0:ℝ) ≤ t3 := by
    rw [ht3]
    have hminpos : 0 < min phi1 phi2 := lt_min hphi1 hphi2
    exact mul_nonneg (inv_nonneg.mpr hminpos.le) (Real.sqrt_nonneg lp)
  have hsum : e1 + e2 + e3 ≤ 4 * (t1 + t2 + t3) := by linarith [hE1, hE2, hE3]
  have hTnn : (0:ℝ) ≤ t1 + t2 + t3 := by linarith [hT1, hT2, hT3]
  have hstep : Cb * (e1 + e2 + e3) ≤ Cb * (4 * (t1 + t2 + t3)) :=
    mul_le_mul_of_nonneg_left hsum hCb.le
  have hCT : (0:ℝ) ≤ Cb * (t1 + t2 + t3) := mul_nonneg hCb.le hTnn
  have hgoal : rE ≤ 8 * Cb * (t1 + t2 + t3) := by
    calc rE ≤ Cb * (4 * (t1 + t2 + t3)) := le_trans hbound hstep
      _ = 4 * (Cb * (t1 + t2 + t3)) := by ring
      _ ≤ 8 * (Cb * (t1 + t2 + t3)) := by linarith [hCT]
      _ = 8 * Cb * (t1 + t2 + t3) := by ring
  exact hgoal
  /- @proof-region region.target-node.session.8ba70f74aaa6ac3b end -/

end Statlib.Imported

end

