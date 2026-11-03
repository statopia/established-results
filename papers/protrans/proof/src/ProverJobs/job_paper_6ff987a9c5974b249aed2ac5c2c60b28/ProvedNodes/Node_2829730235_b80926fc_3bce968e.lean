import Statlib.StatFoundation.Vocabulary.OrliczNorm
import Lean
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Vocabulary
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Base
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.ProvedNodes.Node_1640497675_b47064b9_a7a8da83
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.ProvedNodes.Node_3975489229_33218fe7_54fd77ae
import ProverJobs.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.ExternalNodes.Node_275509df3e7c4fc2b99f

namespace PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28



open MeasureTheory ProbabilityTheory ENNReal
open scoped ENNReal Matrix
open Statlib.StatFoundation.Vocabulary
open _root_.PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported

open MeasureTheory ProbabilityTheory ENNReal
open scoped ENNReal Matrix
open Statlib.StatFoundation.Vocabulary
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
universe u

set_option autoImplicit false in
theorem statopia_math_node_2829730235_b80926fc : ∀ (q : ℕ) (hq : 1 ≤ q) (L : ℝ) (hL : 0 < L)
    (c : ℝ) (hc : 0 < c),
    ∃ C_H N_H : ℝ, 0 < C_H ∧ 0 < N_H ∧
      ∀ (p : ℕ), 2 ≤ p → ∀ (N : ℕ), 1 ≤ N →
        N_H * Real.log (p : ℝ) ≤ (N : ℝ) →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (ν : Measure ((Fin q → ℝ) × (Fin p → ℝ))) [IsProbabilityMeasure ν]
          (f : (Fin q → ℝ) → (Fin p → ℝ))
          (E : Fin N → Ω → Fin p → ℝ) (H : Fin N → Ω → Fin q → ℝ),
          iIndepFun (fun i ω => (H i ω, E i ω)) μ →
          (∀ i, Measure.map (fun ω => (H i ω, E i ω)) μ = ν) →
          (∀ i j, Measurable (fun ω => E i ω j)) →
          (∀ i l, Measurable (fun ω => H i ω l)) →
          (∀ i j, Measurable (fun ω => f (H i ω) j)) →
          (∀ i j, Integrable (fun ω => E i ω j) μ) →
          (∀ i l, Integrable (fun ω => H i ω l) μ) →
          (∀ i j, Integrable (fun ω => f (H i ω) j) μ) →
          (∀ i j, ∫ ω, E i ω j ∂μ = 0) →
          (∀ i l, ∫ ω, H i ω l ∂μ = 0) →
          (∀ i j, ∫ ω, f (H i ω) j ∂μ = 0) →
          (∀ i j, subgaussianOrliczNorm (fun ω => E i ω j) μ ≤ ENNReal.ofReal L) →
          (∀ i l, subgaussianOrliczNorm (fun ω => H i ω l) μ ≤ ENNReal.ofReal L) →
          (∀ i j, subgaussianOrliczNorm (fun ω => f (H i ω) j) μ ≤ ENNReal.ofReal L) →
          (∀ i j l, Integrable (fun ω => E i ω j * H i ω l) μ) →
          (∀ i j l, ∫ ω, E i ω j * H i ω l ∂μ = 0) →
          (∀ j l, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 j * z.1 l) ν) →
          μ ({ω : Ω | ∃ (j : Fin p) (l : Fin q),
                  C_H * Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) <
                    |((N : ℝ)⁻¹) * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l|} ∪
              {ω : Ω | ∃ (j : Fin p) (l : Fin q),
                  C_H * Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) <
                    |((N : ℝ)⁻¹) * (∑ i : Fin N, E i ω j * H i ω l)|})
            ≤ ENNReal.ofReal ((p : ℝ) ^ (-c) / 20) := by
  /- @proof-region region.target-node.session.d2c39c1ffa7f2916 begin -/
  intro q hq L hL c hc
  obtain ⟨V, hVpos, hV⟩ := statopia_math_node_1640497675_b47064b9 L hL
  obtain ⟨b, hbpos, hb⟩ :=
    _root_.PaperProofTasks.job_paper_ebad183ded244602a77f3710a9957efa.Statlib.Imported.paper_ebad183ded244602a77f3710a9957efa
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h80q : 0 < 80 * (q : ℝ) := by nlinarith
  set κ : ℝ := Real.log (80 * (q : ℝ)) / Real.log 2 with hκdef
  have hκnn : 0 ≤ κ := by
    rw [hκdef]
    exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))
  set D : ℝ := c + 1 + κ with hDdef
  have hDpos : 0 < D := by rw [hDdef]; linarith
  refine ⟨(V / Real.sqrt b) * Real.sqrt D, D / b, ?_, ?_, ?_⟩
  · positivity
  · positivity
  intro p hp N hN1 hNlog Ω _ μ _ ν _ f E H hindep hlaw hEmeas hHmeas hfmeas hEint hHint hfint
    hEcenter hHcenter hfcenter hEsub hHsub hfsub hEH hcEHH hνint
  set CH : ℝ := (V / Real.sqrt b) * Real.sqrt D with hCHdef
  set NH : ℝ := D / b with hNHdef
  have hCHpos : 0 < CH := hCHdef ▸ by positivity
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hratio : 0 < Real.log (p : ℝ) / (N : ℝ) := div_pos hlogp hNpos
  set t : ℝ := CH * Real.sqrt (Real.log (p : ℝ) / (N : ℝ)) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have hφmeas : ∀ i : Fin N, Measurable (fun ω => (H i ω, E i ω)) := by
    intro i
    have hH : Measurable (H i) := measurable_pi_iff.2 (hHmeas i)
    have hE : Measurable (E i) := measurable_pi_iff.2 (hEmeas i)
    first
      | exact Measurable.prodMk hH hE
      | exact measurable_prodMk hH hE
      | exact measurable_prod_iff.mpr ⟨hH, hE⟩
  have hmf : ∀ (i : Fin N) (j : Fin p) (l : Fin q),
      ∫ ω, f (H i ω) j * H i ω l ∂μ = (Mf f ν) j l := by
    intro i j l
    have hνae : AEStronglyMeasurable
        (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 j * z.1 l)
        (Measure.map (fun ω => (H i ω, E i ω)) μ) := by
      rw [hlaw i]
      exact (hνint j l).aestronglyMeasurable
    have h := MeasureTheory.integral_map (μ := μ) (φ := fun ω => (H i ω, E i ω))
      (f := fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 j * z.1 l)
      (hφmeas i).aemeasurable hνae
    rw [hlaw i] at h
    simpa [Mf] using h.symm
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hCHsq : CH ^ 2 = V ^ 2 * (D / b) := by
    rw [hCHdef, mul_pow, div_pow, Real.sq_sqrt (le_of_lt hbpos), Real.sq_sqrt (le_of_lt hDpos)]
    ring
  have ht_sq : t ^ 2 = CH ^ 2 * (Real.log (p : ℝ) / (N : ℝ)) := by
    rw [htdef, mul_pow, Real.sq_sqrt (le_of_lt hratio)]
  have h2 : (D / b) * (Real.log (p : ℝ) / (N : ℝ)) ≤ 1 := by
    have hNlog' : D / b * Real.log (p : ℝ) ≤ (N : ℝ) := by
      rw [← hNHdef]; exact hNlog
    calc (D / b) * (Real.log (p : ℝ) / (N : ℝ)) = (D / b * Real.log (p : ℝ)) / (N : ℝ) := by ring
      _ ≤ (N : ℝ) / (N : ℝ) := div_le_div_of_nonneg_right hNlog' (le_of_lt hNpos)
      _ = 1 := div_self hNne
  have htV : t ≤ V := by
    have h3 : t ^ 2 = V ^ 2 * (D / b) * (Real.log (p : ℝ) / (N : ℝ)) := by
      rw [ht_sq, hCHsq]
    have hsq : t ^ 2 ≤ V ^ 2 := by
      rw [h3]
      calc V ^ 2 * (D / b) * (Real.log (p : ℝ) / (N : ℝ))
          = V ^ 2 * ((D / b) * (Real.log (p : ℝ) / (N : ℝ))) := by ring
        _ ≤ V ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (sq_nonneg V)
        _ = V ^ 2 := by ring
    have h4 := abs_le_of_sq_le_sq hsq (le_of_lt hVpos)
    rwa [abs_of_nonneg (le_of_lt htpos)] at h4
  have hmin : min (t ^ 2 / V ^ 2) (t / V) = t ^ 2 / V ^ 2 := by
    rw [min_eq_left]
    have ht1 : t / V ≤ 1 := by
      rw [div_le_one hVpos]
      exact htV
    have heq : (t / V) * (t / V) = t ^ 2 / V ^ 2 := by
      rw [div_mul_div_comm]
      simp only [← pow_two]
    rw [← heq]
    calc (t / V) * (t / V) ≤ 1 * (t / V) := mul_le_mul_of_nonneg_right ht1 (by positivity)
      _ = t / V := one_mul _
  have hexpD : Real.exp (-(D * Real.log (p : ℝ))) = (p : ℝ) ^ (-D) := by
    rw [Real.rpow_def_of_pos hp0]
    congr 1
    ring
  have hexp : Real.exp (-(b * (N : ℝ) * min (t ^ 2 / V ^ 2) (t / V))) = (p : ℝ) ^ (-D) := by
    have harg : b * (N : ℝ) * min (t ^ 2 / V ^ 2) (t / V) = D * Real.log (p : ℝ) := by
      rw [hmin, ht_sq, hCHsq]
      field_simp
    rw [harg, hexpD]
  have hZFsum : ∀ (j : Fin p) (l : Fin q) (ω : Ω),
      (N : ℝ)⁻¹ * (∑ i : Fin N, (f (H i ω) j * H i ω l - (Mf f ν) j l))
        = (N : ℝ)⁻¹ * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l := by
    intro j l ω
    have hs : (∑ i : Fin N, (f (H i ω) j * H i ω l - (Mf f ν) j l))
        = (∑ i : Fin N, f (H i ω) j * H i ω l) - (N : ℝ) * (Mf f ν) j l := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [hs, mul_sub, ← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
  have htailE : ∀ (j : Fin p) (l : Fin q),
      μ.real {ω : Ω | t < |(N : ℝ)⁻¹ * (∑ i : Fin N, E i ω j * H i ω l)|}
        ≤ 2 * (p : ℝ) ^ (-D) := by
    intro j l
    have hmeas : ∀ i : Fin N, Measurable (fun ω => E i ω j * H i ω l) :=
      fun i => (hEmeas i j).mul (hHmeas i l)
    have hind : iIndepFun (fun i ω => E i ω j * H i ω l) μ :=
      (statopia_math_node_3975489229_33218fe7 N p q Ω μ ν f E H hindep hlaw hHmeas hEmeas
        hνint).2 j l
    have hint : ∀ i : Fin N, Integrable (fun ω => E i ω j * H i ω l) μ :=
      fun i => hEH i j l
    have hcent : ∀ i : Fin N, ∫ ω, E i ω j * H i ω l ∂μ = 0 := fun i => hcEHH i j l
    have hmom : ∀ (i : Fin N) (r : ℕ), 2 ≤ r →
        ∫⁻ ω, ENNReal.ofReal (|E i ω j * H i ω l| ^ r) ∂μ
          ≤ ENNReal.ofReal ((Nat.factorial r : ℝ) * V ^ r) := by
      intro i r hr
      have hVf := hV Ω μ (fun ω => E i ω j) (fun ω => H i ω l) (hEmeas i j) (hHmeas i l)
        (hEsub i j) (hHsub i l)
      have h1 := hVf.2.2 r (by omega)
      have h2' : ∀ ω : Ω, |E i ω j * H i ω l - ∫ ω', E i ω' j * H i ω' l ∂μ| ^ r
          = |E i ω j * H i ω l| ^ r := by
        intro ω
        rw [hcEHH i j l, sub_zero]
      simp only [h2'] at h1
      exact h1
    have h := hb N hN1 V hVpos Ω μ (fun i ω => E i ω j * H i ω l) hmeas hind hint hcent
      hmom t htpos
    rwa [hexp] at h
  have htailF : ∀ (j : Fin p) (l : Fin q),
      μ.real {ω : Ω | t < |(N : ℝ)⁻¹ * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l|}
        ≤ 2 * (p : ℝ) ^ (-D) := by
    intro j l
    have hmeas : ∀ i : Fin N,
        Measurable (fun ω => f (H i ω) j * H i ω l - (Mf f ν) j l) :=
      fun i => ((hfmeas i j).mul (hHmeas i l)).sub measurable_const
    have hind : iIndepFun (fun i ω => f (H i ω) j * H i ω l - (Mf f ν) j l) μ :=
      (statopia_math_node_3975489229_33218fe7 N p q Ω μ ν f E H hindep hlaw hHmeas hEmeas
        hνint).1 j l
    have hint : ∀ i : Fin N,
        Integrable (fun ω => f (H i ω) j * H i ω l - (Mf f ν) j l) μ := by
      intro i
      exact (hV Ω μ (fun ω => f (H i ω) j) (fun ω => H i ω l) (hfmeas i j) (hHmeas i l)
        (hfsub i j) (hHsub i l)).1.sub (integrable_const _)
    have hcent : ∀ i : Fin N,
        ∫ ω, (f (H i ω) j * H i ω l - (Mf f ν) j l) ∂μ = 0 := by
      intro i
      have hVf := hV Ω μ (fun ω => f (H i ω) j) (fun ω => H i ω l) (hfmeas i j) (hHmeas i l)
        (hfsub i j) (hHsub i l)
      have h1 : ∫ ω, (Mf f ν) j l ∂μ = (Mf f ν) j l := by simp
      rw [integral_sub hVf.1 (integrable_const _), h1, hmf i j l, sub_self]
    have hmom : ∀ (i : Fin N) (r : ℕ), 2 ≤ r →
        ∫⁻ ω, ENNReal.ofReal (|f (H i ω) j * H i ω l - (Mf f ν) j l| ^ r) ∂μ
          ≤ ENNReal.ofReal ((Nat.factorial r : ℝ) * V ^ r) := by
      intro i r hr
      have hVf := hV Ω μ (fun ω => f (H i ω) j) (fun ω => H i ω l) (hfmeas i j) (hHmeas i l)
        (hfsub i j) (hHsub i l)
      have h1 := hVf.2.2 r (by omega)
      have h2' : ∀ ω : Ω,
          |f (H i ω) j * H i ω l - ∫ ω', f (H i ω') j * H i ω' l ∂μ| ^ r
            = |f (H i ω) j * H i ω l - (Mf f ν) j l| ^ r := by
        intro ω
        rw [hmf i j l]
      simp only [h2'] at h1
      exact h1
    have h := hb N hN1 V hVpos Ω μ
      (fun i ω => f (H i ω) j * H i ω l - (Mf f ν) j l) hmeas hind hint hcent hmom t htpos
    have hset : {ω : Ω | t < |(N : ℝ)⁻¹ * ∑ i : Fin N,
          (f (H i ω) j * H i ω l - (Mf f ν) j l)|}
        = {ω : Ω | t < |(N : ℝ)⁻¹ * (∑ i : Fin N, f (H i ω) j * H i ω l)
          - (Mf f ν) j l|} := by
      ext ω
      simp only [Set.mem_setOf_eq, hZFsum j l ω]
    rw [hexp, hset] at h
    exact h
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hpcn : 0 ≤ (p:ℝ)^(-c) := Real.rpow_nonneg (le_of_lt hp0) _
  have hpk : (p:ℝ)^(-κ) ≤ 1 / (80 * (q:ℝ)) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogp2 : Real.log 2 ≤ Real.log (p:ℝ) := Real.log_le_log (by norm_num) hp2
    have hκlog : Real.log 2 * κ = Real.log (80 * (q:ℝ)) := by
      rw [mul_comm, hκdef]
      field_simp
    have hle : Real.log (80 * (q:ℝ)) ≤ Real.log (p:ℝ) * κ := by
      calc Real.log (80 * (q:ℝ)) = Real.log 2 * κ := hκlog.symm
        _ ≤ Real.log (p:ℝ) * κ := mul_le_mul_of_nonneg_right hlogp2 hκnn
    have h80 : 80 * (q:ℝ) ≤ (p:ℝ)^κ := by
      rw [Real.rpow_def_of_pos hp0]
      calc 80 * (q:ℝ) = Real.exp (Real.log (80 * (q:ℝ))) := (Real.exp_log h80q).symm
        _ ≤ Real.exp (Real.log (p:ℝ) * κ) := Real.exp_le_exp.2 hle
    calc (p:ℝ)^(-κ) = ((p:ℝ)^κ)⁻¹ := Real.rpow_neg (le_of_lt hp0) κ
      _ = 1 / (p:ℝ)^κ := (one_div _).symm
      _ ≤ 1 / (80 * (q:ℝ)) := div_le_div_of_nonneg_left zero_le_one h80q h80
  have hpinv : (p:ℝ)^(-1:ℝ) ≤ 1 := by
    have h1 : (p:ℝ)^(-(1:ℝ)) = ((p:ℝ)^(1:ℝ))⁻¹ := Real.rpow_neg (le_of_lt hp0) (1:ℝ)
    rw [h1, Real.rpow_one, ← one_div, div_le_one hp0]
    linarith
  have hDsplit : (p:ℝ)^(-D) = (p:ℝ)^(-c) * (p:ℝ)^(-1:ℝ) * (p:ℝ)^(-κ) := by
    rw [show -D = -c + -1 + -κ by rw [hDdef]; ring]
    rw [Real.rpow_add hp0, Real.rpow_add hp0]
  have hfinal_real : 4 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D) ≤ (p:ℝ)^(-c) / 20 := by
    rw [hDsplit]
    have hA : 0 ≤ (p:ℝ)^(-c) * (p:ℝ)^(-1:ℝ) :=
      mul_nonneg hpcn (Real.rpow_nonneg (le_of_lt hp0) _)
    have hstep : (p:ℝ)^(-c) * (p:ℝ)^(-1:ℝ) * (p:ℝ)^(-κ)
        ≤ (p:ℝ)^(-c) * (p:ℝ)^(-1:ℝ) * (1 / (80 * (q:ℝ))) :=
      mul_le_mul_of_nonneg_left hpk hA
    have hpq : (0:ℝ) < 4 * (p:ℝ) * (q:ℝ) := by
      have h2 : (0:ℝ) < 4 * (p:ℝ) := by linarith
      exact mul_pos h2 hqpos
    have hmain : 4 * (p:ℝ) * (q:ℝ) * ((p:ℝ)^(-c) * (p:ℝ)^(-1:ℝ) * (1 / (80 * (q:ℝ))))
        = (p:ℝ)^(-c) / 20 := by
      have hp1 : (p:ℝ)^(-1:ℝ) = ((p:ℝ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hp0) (1:ℝ), Real.rpow_one]
      rw [hp1]
      field_simp
      try ring
    calc 4 * (p:ℝ) * (q:ℝ) * ((p:ℝ)^(-c) * (p:ℝ)^(-1:ℝ) * (p:ℝ)^(-κ))
        ≤ 4 * (p:ℝ) * (q:ℝ) * ((p:ℝ)^(-c) * (p:ℝ)^(-1:ℝ) * (1 / (80 * (q:ℝ)))) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hpq)
      _ = (p:ℝ)^(-c) / 20 := hmain
  have hnn : 0 ≤ 2 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D) := by
    have h1 : (0:ℝ) < 2 * (p:ℝ) := by linarith
    have h2 : (0:ℝ) < 2 * (p:ℝ) * (q:ℝ) := mul_pos h1 hqpos
    exact mul_nonneg (le_of_lt h2) (Real.rpow_nonneg (le_of_lt hp0) _)
  have hsumReal : (∑ j : Fin p, ∑ l : Fin q, (2 * (p:ℝ)^(-D)))
      = 2 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hconv : ∀ s : Set Ω, ENNReal.ofReal (μ.real s) = μ s := by
    intro s
    exact ENNReal.ofReal_toReal (measure_ne_top μ s)
  have hSf : μ.real {ω : Ω | ∃ (j : Fin p) (l : Fin q),
        t < |(N:ℝ)⁻¹ * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l|}
      ≤ 2 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D) := by
    have heq : {ω : Ω | ∃ (j : Fin p) (l : Fin q),
        t < |(N:ℝ)⁻¹ * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l|}
        = ⋃ j : Fin p, ⋃ l : Fin q,
          {ω : Ω | t < |(N:ℝ)⁻¹ * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l|} := by
      ext ω
      simp
    rw [heq]
    calc μ.real (⋃ j : Fin p, ⋃ l : Fin q,
          {ω : Ω | t < |(N:ℝ)⁻¹ * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l|})
        ≤ ∑ j : Fin p, μ.real (⋃ l : Fin q,
          {ω : Ω | t < |(N:ℝ)⁻¹ * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l|}) :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ j : Fin p, ∑ l : Fin q, μ.real
          {ω : Ω | t < |(N:ℝ)⁻¹ * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l|} :=
          Finset.sum_le_sum fun j _ => measureReal_iUnion_fintype_le _
      _ ≤ ∑ j : Fin p, ∑ l : Fin q, (2 * (p:ℝ)^(-D)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => htailF j l
      _ = 2 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D) := hsumReal
  have hSe : μ.real {ω : Ω | ∃ (j : Fin p) (l : Fin q),
        t < |(N:ℝ)⁻¹ * (∑ i : Fin N, E i ω j * H i ω l)|}
      ≤ 2 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D) := by
    have heq : {ω : Ω | ∃ (j : Fin p) (l : Fin q),
        t < |(N:ℝ)⁻¹ * (∑ i : Fin N, E i ω j * H i ω l)|}
        = ⋃ j : Fin p, ⋃ l : Fin q,
          {ω : Ω | t < |(N:ℝ)⁻¹ * (∑ i : Fin N, E i ω j * H i ω l)|} := by
      ext ω
      simp
    rw [heq]
    calc μ.real (⋃ j : Fin p, ⋃ l : Fin q,
          {ω : Ω | t < |(N:ℝ)⁻¹ * (∑ i : Fin N, E i ω j * H i ω l)|})
        ≤ ∑ j : Fin p, μ.real (⋃ l : Fin q,
          {ω : Ω | t < |(N:ℝ)⁻¹ * (∑ i : Fin N, E i ω j * H i ω l)|}) :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ j : Fin p, ∑ l : Fin q, μ.real
          {ω : Ω | t < |(N:ℝ)⁻¹ * (∑ i : Fin N, E i ω j * H i ω l)|} :=
          Finset.sum_le_sum fun j _ => measureReal_iUnion_fintype_le _
      _ ≤ ∑ j : Fin p, ∑ l : Fin q, (2 * (p:ℝ)^(-D)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => htailE j l
      _ = 2 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D) := hsumReal
  have hSb : μ ({ω : Ω | ∃ (j : Fin p) (l : Fin q),
        t < |(N:ℝ)⁻¹ * (∑ i : Fin N, f (H i ω) j * H i ω l) - (Mf f ν) j l|} ∪
      {ω : Ω | ∃ (j : Fin p) (l : Fin q),
        t < |(N:ℝ)⁻¹ * (∑ i : Fin N, E i ω j * H i ω l)|})
      ≤ ENNReal.ofReal (2 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D))
        + ENNReal.ofReal (2 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D)) := by
    refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
    · rw [← hconv]
      exact ENNReal.ofReal_le_ofReal hSf
    · rw [← hconv]
      exact ENNReal.ofReal_le_ofReal hSe
  have hfin : ENNReal.ofReal (2 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D))
      + ENNReal.ofReal (2 * (p:ℝ) * (q:ℝ) * (p:ℝ)^(-D))
      ≤ ENNReal.ofReal ((p:ℝ)^(-c) / 20) := by
    rw [← ENNReal.ofReal_add hnn hnn]
    apply ENNReal.ofReal_le_ofReal
    linarith [hfinal_real]
  exact le_trans hSb hfin


  /- @proof-region region.target-node.session.d2c39c1ffa7f2916 end -/

end Statlib.Imported

