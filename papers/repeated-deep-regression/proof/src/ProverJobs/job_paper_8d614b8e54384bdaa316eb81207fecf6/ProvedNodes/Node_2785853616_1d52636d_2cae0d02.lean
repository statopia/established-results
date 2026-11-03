import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base

namespace PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open _root_.PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
noncomputable section
set_option maxHeartbeats 1000000

set_option autoImplicit false in
theorem statopia_math_node_2785853616_1d52636d : ∀ (B1 : ℝ) (hB1 : 0 < B1) (phi : ℝ → ℝ) (rstar : ℝ) (hrstar_pos : 0 < rstar)
    (hsubroot : (∀ r ∈ Set.Ici rstar, 0 ≤ phi r / Real.sqrt r) ∧
      AntitoneOn (fun r => phi r / Real.sqrt r) (Set.Ici rstar))
    (hphi_le : phi rstar ≤ rstar)
    (c38 c39 : ℝ) (hc38 : c38 = (2 : ℝ) ^ 24) (hc39 : c39 = (2 : ℝ) ^ 12)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (r1 : ℝ)
    (hr1 : r1 = 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)))
    (hregime : rstar ≤ r1),
    160 * B1 * phi r1 / r1 + Real.sqrt (8 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ) * r1)) +
      140 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ) * r1) ≤ 1 / 2 := by
  /- @proof-region region.target-node.session.a4b12912d663b010 begin -/
  intro B1 hB1 phi rstar hrstar_pos hsubroot hphi_le c38 c39 hc38 hc39 n m hn hm t ht r1 hr1 hregime
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := mul_pos hnR hmR
  have hc38pos : 0 < c38 := by rw [hc38]; norm_num
  have hc39pos : 0 < c39 := by rw [hc39]; norm_num
  have hrstar_nonneg : 0 ≤ rstar := le_of_lt hrstar_pos
  have hB1sq_pos : 0 < B1 ^ 2 := pow_pos hB1 2
  have hr1pos : 0 < r1 := by
    rw [hr1]
    have h1 : 0 < 2 * c38 * B1 ^ 2 * rstar := by positivity
    have h2 : 0 < 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) := by positivity
    linarith
  have hsqrtrstar_pos : 0 < Real.sqrt rstar := Real.sqrt_pos.mpr hrstar_pos
  have hsqrtr1_pos : 0 < Real.sqrt r1 := Real.sqrt_pos.mpr hr1pos
  have hA_le : 2 * c38 * B1 ^ 2 * rstar ≤ r1 := by
    rw [hr1]
    have h2 : 0 ≤ 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) := by positivity
    linarith
  have hNr1_ge : 2 * c39 * B1 ^ 2 * t ≤ ((n : ℝ) * (m : ℝ)) * r1 := by
    have h1 : 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) ≤ r1 := by
      rw [hr1]
      have h2 : 0 ≤ 2 * c38 * B1 ^ 2 * rstar := by positivity
      linarith
    have h3 := (div_le_iff₀ hNpos).mp h1
    linarith [h3]
  have hNr1_ge' : 2 * 4096 * B1 ^ 2 * t ≤ ((n : ℝ) * (m : ℝ)) * r1 := by
    have h1 : c39 = 4096 := by rw [hc39]; norm_num
    rw [← h1]
    exact hNr1_ge
  have hpsi_anti : phi r1 / Real.sqrt r1 ≤ phi rstar / Real.sqrt rstar :=
    hsubroot.2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hregime) hregime
  have hpsi_rstar : phi rstar / Real.sqrt rstar ≤ Real.sqrt rstar := by
    rw [div_le_iff₀ hsqrtrstar_pos, Real.mul_self_sqrt hrstar_nonneg]
    exact hphi_le
  have hpsi_bound : phi r1 / Real.sqrt r1 ≤ Real.sqrt rstar := le_trans hpsi_anti hpsi_rstar
  have hphi_le_sqrt : phi r1 ≤ Real.sqrt rstar * Real.sqrt r1 :=
    (div_le_iff₀ hsqrtr1_pos).mp hpsi_bound
  have hfac : Real.sqrt (2 * c38 * B1 ^ 2 * rstar) = Real.sqrt (2 * c38) * B1 * Real.sqrt rstar := by
    have h1 : (0 : ℝ) ≤ 2 * c38 := by positivity
    have h2 : (0 : ℝ) ≤ B1 ^ 2 := le_of_lt hB1sq_pos
    rw [show 2 * c38 * B1 ^ 2 * rstar = (2 * c38) * (B1 ^ 2 * rstar) by ring]
    rw [Real.sqrt_mul h1, Real.sqrt_mul h2, Real.sqrt_sq (le_of_lt hB1)]
    ring
  have h2c38_ge : (4096 : ℝ) ≤ Real.sqrt (2 * c38) := by
    have hval : 2 * c38 = (2 : ℝ) ^ 25 := by rw [hc38]; norm_num
    rw [hval]
    have hle : ((4096 : ℝ)) ^ 2 ≤ (2 : ℝ) ^ 25 := by norm_num
    calc (4096 : ℝ) = Real.sqrt ((4096 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt ((2 : ℝ) ^ 25) := (Real.sqrt_le_sqrt_iff (by positivity)).mpr hle
  have hden_ge : 4096 * B1 * Real.sqrt rstar ≤ Real.sqrt r1 := by
    have hle : Real.sqrt (2 * c38) * B1 * Real.sqrt rstar ≤ Real.sqrt r1 := by
      rw [← hfac]
      exact (Real.sqrt_le_sqrt_iff (le_of_lt hr1pos)).mpr hA_le
    nlinarith [hle, h2c38_ge, mul_nonneg (le_of_lt hB1) (Real.sqrt_nonneg rstar)]
  have hT1core : 160 * B1 * Real.sqrt rstar ≤ 5 / 128 * Real.sqrt r1 := by
    nlinarith [hden_ge]
  have hT1 : 160 * B1 * phi r1 / r1 ≤ 5 / 128 := by
    have hstep1 : 160 * B1 * phi r1 ≤ 160 * B1 * (Real.sqrt rstar * Real.sqrt r1) :=
      mul_le_mul_of_nonneg_left hphi_le_sqrt (by positivity)
    have hstep2 : 160 * B1 * (Real.sqrt rstar * Real.sqrt r1) ≤ 5 / 128 * r1 := by
      have h := mul_le_mul_of_nonneg_right hT1core (le_of_lt hsqrtr1_pos)
      calc 160 * B1 * (Real.sqrt rstar * Real.sqrt r1)
          = 160 * B1 * Real.sqrt rstar * Real.sqrt r1 := by ring
        _ ≤ 5 / 128 * Real.sqrt r1 * Real.sqrt r1 := h
        _ = 5 / 128 * r1 := by rw [mul_assoc, Real.mul_self_sqrt (le_of_lt hr1pos)]
    rw [div_le_iff₀ hr1pos]
    linarith [hstep1, hstep2]
  have hT2 : Real.sqrt (8 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ) * r1)) ≤ 1 / 32 := by
    have hden : 0 < (n : ℝ) * (m : ℝ) * r1 := by positivity
    have hq : 8 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ) * r1) ≤ 1 / 1024 := by
      rw [div_le_iff₀ hden]
      nlinarith [hNr1_ge']
    have hsqrt : Real.sqrt (1 / 1024 : ℝ) = 1 / 32 := by
      rw [show (1 / 1024 : ℝ) = (1 / 32) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    calc Real.sqrt (8 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ) * r1))
        ≤ Real.sqrt (1 / 1024 : ℝ) := (Real.sqrt_le_sqrt_iff (by norm_num)).mpr hq
      _ = 1 / 32 := hsqrt
  have hT3 : 140 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ) * r1) ≤ 70 / 4096 := by
    have hden : 0 < (n : ℝ) * (m : ℝ) * r1 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [hNr1_ge']
  have hfin : (5 : ℝ) / 128 + 1 / 32 + 70 / 4096 ≤ 1 / 2 := by norm_num
  linarith [hT1, hT2, hT3, hfin]
  /- @proof-region region.target-node.session.a4b12912d663b010 end -/

end

end Statlib.Imported

