import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Vocabulary
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Base
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.ProvedNodes.Node_127205983_b1e1c88b_2ae14d45
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.ProvedNodes.Node_1873299149_9a24b38e_0252975c
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.ExternalNodes.Node_ef1c67bde1d7453089df

namespace PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer



open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer.ModelShiftLasso

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ModelShiftLasso

set_option autoImplicit false in
theorem statopia_math_node_2523946026_e3500c8d : ∀ (p q K n_t : ℕ) (hp : 2 ≤ p) (hq : 1 ≤ q) (hK : 1 ≤ K) (hnt : 0 < n_t)
    (n_s : Fin K → ℕ) (hns : ∀ k : Fin K, 0 < n_s k) (hnst : n_t ≤ ∑ k, n_s k)
    (Ω : Type) [inst : MeasurableSpace Ω]
    (f : (Fin q → ℝ) → Fin p → ℝ)
    (Xt : Fin n_t → Ω → Fin p → ℝ) (Ht : Fin n_t → Ω → Fin q → ℝ)
    (Et : Fin n_t → Ω → Fin p → ℝ) (Yt : Fin n_t → Ω → ℝ) (epsT : Fin n_t → Ω → ℝ)
    (Xs : (k : Fin K) → Fin (n_s k) → Ω → Fin p → ℝ)
    (Hs : (k : Fin K) → Fin (n_s k) → Ω → Fin q → ℝ)
    (Es : (k : Fin K) → Fin (n_s k) → Ω → Fin p → ℝ)
    (Ys : (k : Fin K) → Fin (n_s k) → Ω → ℝ)
    (epsS : (k : Fin K) → Fin (n_s k) → Ω → ℝ)
    (betaT : Fin p → ℝ) (phiT : Fin q → ℝ)
    (betaS : Fin K → Fin p → ℝ) (phiS : Fin K → Fin q → ℝ)
    (SigmaX : Fin p → Fin p → ℝ) (M : Fin p → Fin q → ℝ) (nsTot : ℝ)
    (hnsTot : nsTot = ∑ k, ((n_s k : ℕ) : ℝ))
    (Cx Cdelta CH Cd Ceps C_phi B_phi C_s s_delta lam C_r L_M : ℝ)
    (hCx : 0 < Cx) (hCdelta : 0 < Cdelta) (hCH : 0 < CH) (hCd : 0 < Cd)
    (hCeps : 0 < Ceps) (hCphi : 0 < C_phi) (hBphi : 0 < B_phi) (hC_s : 0 < C_s)
    (hs_delta : 0 ≤ s_delta) (hL_M : 0 < L_M) (hC_r : 0 < C_r)
    (hlam : 4 * (8 * CH * Real.sqrt (q : ℝ) * l2n phiT +
      (2 * (2 * Cx * C_s + Cdelta * s_delta + Cd * B_phi * Real.sqrt (q : ℝ) +
        L_M * C_phi * Real.sqrt (q : ℝ) + Ceps) + Ceps)) *
      Real.sqrt (Real.log (p : ℝ) / (n_t : ℝ)) ≤ lam)
    (hlam_pos : 0 < 4 * (8 * CH * Real.sqrt (q : ℝ) * l2n phiT +
      (2 * (2 * Cx * C_s + Cdelta * s_delta + Cd * B_phi * Real.sqrt (q : ℝ) +
        L_M * C_phi * Real.sqrt (q : ℝ) + Ceps) + Ceps)) *
      Real.sqrt (Real.log (p : ℝ) / (n_t : ℝ)))
    (s_eta : ℕ) (hs_eta_p : s_eta ≤ p)
    (hS_eta : (supportFinset (etaZero n_s betaT betaS)).card ≤ s_eta)
    (betaInit : Fin p → ℝ)
    (hX_model_t : ∀ (i : Fin n_t) (j : Fin p) (ω : Ω), Xt i ω j = f (Ht i ω) j + Et i ω j)
    (hY_model_t : ∀ (i : Fin n_t) (ω : Ω),
      Yt i ω = vdot (Xt i ω) betaT + vdot (Ht i ω) phiT + epsT i ω)
    (hX_model_s : ∀ (k : Fin K) (i : Fin (n_s k)) (j : Fin p) (ω : Ω),
      Xs k i ω j = f (Hs k i ω) j + Es k i ω j)
    (hY_model_s : ∀ (k : Fin K) (i : Fin (n_s k)) (ω : Ω),
      Ys k i ω = vdot (Xs k i ω) (betaS k) + vdot (Hs k i ω) (phiS k) + epsS k i ω)
    (hphi_bar : l2n (fun s => phiBar n_s phiS s - phiT s) ≤
      C_phi * Real.sqrt (Real.log (p : ℝ) / (n_t : ℝ)))
    (hbeta_init : l1n (fun j => betaInit j - betaBar n_s betaS j) ≤ C_s)
    (hM_row : ∀ j : Fin p,
      Real.sqrt (∑ s : Fin q, (M j s) ^ 2) ≤ L_M * Real.sqrt (q : ℝ))
    (ω : Ω)
    (hG : ω ∈ PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.Gset
      f Et Ht epsT Es Hs epsS SigmaX M betaS phiT phiS nsTot
      Cx Cdelta CH Cd Ceps s_delta B_phi)
    (hR : ω ∈ REvent Xt (supportFinset (etaZero n_s betaT betaS)) C_r),
    GoodAt n_s (fun i => Xt i ω) (fun i => Yt i ω) (fun k i => Xs k i ω)
      (fun k i => Ys k i ω) betaInit (etaZero n_s betaT betaS) C_r lam s_eta := by
  /- @proof-region region.target-node.session.50a5026ba3edc1dc begin -/
  intro p q K n_t hp hq hK hnt n_s hns hnst Ω inst f Xt Ht Et Yt epsT Xs Hs Es Ys epsS
    betaT phiT betaS phiS SigmaX M nsTot hnsTot Cx Cdelta CH Cd Ceps C_phi B_phi C_s s_delta
    lam C_r L_M hCx hCdelta hCH hCd hCeps hCphi hBphi hC_s hs_delta hL_M hC_r hlam hlam_pos
    s_eta hs_eta_p hS_eta betaInit hX_model_t hY_model_t hX_model_s hY_model_s hphi_bar
    hbeta_init hM_row ω hG hR
  intro Zhat hZmin ηhat hηmin
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hnt1 : 1 ≤ n_t := Nat.succ_le_of_lt hnt
  have hns1 : ∀ k : Fin K, 1 ≤ n_s k := fun k => Nat.succ_le_of_lt (hns k)
  have hA := hG
  unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.Gset at hA
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6, hG7, hG8, hG9, hG10⟩ := hA
  let N : ℕ := ∑ k, n_s k
  let a : ℝ := Real.sqrt (Real.log (p : ℝ) / (n_t : ℝ))
  let a_s : ℝ := Real.sqrt (Real.log (p : ℝ) / (N : ℝ))
  let d : Fin p → ℝ := fun j => betaBar n_s betaS j - betaInit j
  let deltaK : Fin K → Fin p → ℝ := fun k j => betaS k j - betaBar n_s betaS j
  let dk : Fin K → Fin q → ℝ := fun k s => phiS k s - phiT s
  let dbar : Fin q → ℝ := fun s => phiBar n_s phiS s - phiT s
  let Gt : Fin p → Fin p → ℝ := fun j t => (1 / (n_t : ℝ)) * ∑ i, Xt i ω j * Xt i ω t
  let Gs : Fin p → Fin p → ℝ := fun j t => (1 / (N : ℝ)) * ∑ k, ∑ i, Xs k i ω j * Xs k i ω t
  let Tbeta : Fin p → ℝ := fun j => (1 / (N : ℝ)) *
    ∑ k, ∑ t, ((∑ i, Xs k i ω j * Xs k i ω t) - (n_s k : ℝ) * SigmaX j t) * deltaK k t
  let Dt : Fin p → Fin q → ℝ := fun j s => (1 / (n_t : ℝ)) * (∑ i, Xt i ω j * Ht i ω s) - M j s
  let Ds : Fin p → Fin q → ℝ := fun j s =>
    (1 / (N : ℝ)) * (∑ k, ∑ i, Xs k i ω j * Hs k i ω s) - M j s
  let Tphi : Fin p → ℝ := fun j => (1 / (N : ℝ)) *
    ∑ k, ∑ s, ((∑ i, Xs k i ω j * Hs k i ω s) - (n_s k : ℝ) * M j s) * dk k s
  let e_t : Fin p → ℝ := fun j => (1 / (n_t : ℝ)) * ∑ i, epsT i ω * Xt i ω j
  let es : Fin p → ℝ := fun j => (1 / (N : ℝ)) * ∑ k, ∑ i, epsS k i ω * Xs k i ω j
  let bvec : Fin p → ℝ := fun j =>
    (1 / (N : ℝ)) * ∑ k, ∑ i, (Ys k i ω - vdot (Xs k i ω) betaInit) * Xs k i ω j
  let C_1 : ℝ := 8 * CH
  let C_2 : ℝ := 2 * (2 * Cx * C_s + Cdelta * s_delta + Cd * B_phi * Real.sqrt (q : ℝ) +
    L_M * C_phi * Real.sqrt (q : ℝ) + Ceps) + Ceps
  let r : Fin n_t → ℝ := fun i =>
    Yt i ω - vdot (Xt i ω) betaInit - Zhat i - vdot (Xt i ω) (etaZero n_s betaT betaS)
  let c : Fin p → ℝ := fun j => (1 / (n_t : ℝ)) * ∑ i, r i * Xt i ω j
  have hmodT : ∀ i : Fin n_t, Yt i ω = vdot (Xt i ω) betaT + vdot (Ht i ω) phiT + epsT i ω :=
    fun i => hY_model_t i ω
  have hmodS : ∀ (k : Fin K) (i : Fin (n_s k)),
      Ys k i ω = vdot (Xs k i ω) (betaS k) + vdot (Hs k i ω) (phiS k) + epsS k i ω :=
    fun k i => hY_model_s k i ω
  have hN : ((N : ℕ) : ℝ) = nsTot := by
    simp only [N, Nat.cast_sum]
    exact hnsTot.symm
  have hNge : n_t ≤ N := by simpa only [N] using hnst
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : 0 < N := lt_of_lt_of_le hnt hNge
    exact_mod_cast h
  have hntpos : (0 : ℝ) < (n_t : ℝ) := by exact_mod_cast hnt
  have hGramT : ∀ j t : Fin p, |Gt j t - SigmaX j t| ≤ Cx * a := by
    have h := hG1
    unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.MatSupLe
      PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.aTcoef at h
    intro j t
    have hj := h j t
    have key : Gt j t =
        (∑ r, (f (Ht r ω) + Et r ω) j * (f (Ht r ω) + Et r ω) t) / (n_t : ℝ) := by
      simp only [Gt, hX_model_t, Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv, Pi.add_apply]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [key]
    simp only [a]
    exact hj
  have hGramS : ∀ j t : Fin p, |Gs j t - SigmaX j t| ≤ Cx * a_s := by
    have h := hG2
    unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.MatSupLe
      PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.aSCoef at h
    intro j t
    have hj := h j t
    have key : Gs j t =
        (∑ k, ∑ r, (f (Hs k r ω) + Es k r ω) j * (f (Hs k r ω) + Es k r ω) t) / nsTot := by
      simp only [Gs, hX_model_s, hN, Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv, Pi.add_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [key]
    simp only [a_s, hN]
    exact hj
  have hTbeta : ∀ j : Fin p, |Tbeta j| ≤ Cdelta * s_delta * a_s := by
    have h3 := hG3
    unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.VecSupLe
      PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.aSCoef at h3
    have hden : nsTot = ((∑ j, n_s j : ℕ) : ℝ) := by
      rw [hnsTot, Nat.cast_sum]
    have hbbar : PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.betaBar
        n_s nsTot betaS = betaBar n_s betaS := by
      funext j
      unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.betaBar
        betaBar sourceWeight
      simp only [hden]
    intro j
    have hj := h3 j
    have hmul : ∀ (k : Fin K) (v : ℝ),
        ((n_s k : ℕ) : ℝ) * ((1 / ((n_s k : ℕ) : ℝ)) * v) = v := by
      intro k v
      have hk : ((n_s k : ℕ) : ℝ) ≠ 0 := by
        have hpos : (0 : ℝ) < ((n_s k : ℕ) : ℝ) := by exact_mod_cast hns k
        exact ne_of_gt hpos
      rw [one_div, ← mul_assoc, mul_inv_cancel₀ hk, one_mul]
    have hinner : ∀ k : Fin K,
        (∑ t, ((∑ i, (f (Hs k i ω) j + Es k i ω j) * (f (Hs k i ω) t + Es k i ω t)) /
              ((n_s k : ℕ) : ℝ) - SigmaX j t) * (betaS k t - betaBar n_s betaS t))
          = (1 / ((n_s k : ℕ) : ℝ)) * ∑ t,
              (((∑ i, (f (Hs k i ω) j + Es k i ω j) * (f (Hs k i ω) t + Es k i ω t)) -
                ((n_s k : ℕ) : ℝ) * SigmaX j t) * (betaS k t - betaBar n_s betaS t)) := by
      intro k
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have hk : ((n_s k : ℕ) : ℝ) ≠ 0 := by
        have hpos : (0 : ℝ) < ((n_s k : ℕ) : ℝ) := by exact_mod_cast hns k
        exact ne_of_gt hpos
      field_simp
      try ring
    have keyA : Tbeta j = (1 / (N : ℝ)) *
        ∑ k, ∑ t, ((∑ i, Xs k i ω j * Xs k i ω t) - ((n_s k : ℕ) : ℝ) * SigmaX j t)
          * (betaS k t - betaBar n_s betaS t) := by
      simp only [Tbeta, deltaK]
    have keyB : (1 / (N : ℝ)) *
        ∑ k, ∑ t, ((∑ i, Xs k i ω j * Xs k i ω t) - ((n_s k : ℕ) : ℝ) * SigmaX j t)
          * (betaS k t - betaBar n_s betaS t)
        = (∑ k, ((n_s k : ℕ) : ℝ) * ∑ t,
            ((∑ i, (f (Hs k i ω) + Es k i ω) j * (f (Hs k i ω) + Es k i ω) t) /
                ((n_s k : ℕ) : ℝ) - SigmaX j t)
              * (betaS k t -
                PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.betaBar
                  n_s nsTot betaS t)) / nsTot := by
      simp only [hX_model_s, Pi.add_apply, hbbar, hinner, hmul, hN]
      ring
    rw [show Tbeta j = (∑ k, ((n_s k : ℕ) : ℝ) * ∑ t,
            ((∑ i, (f (Hs k i ω) + Es k i ω) j * (f (Hs k i ω) + Es k i ω) t) /
                ((n_s k : ℕ) : ℝ) - SigmaX j t)
              * (betaS k t -
                PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.betaBar
                  n_s nsTot betaS t)) / nsTot from keyA.trans keyB]
    simp only [a_s, hN]
    exact hj
  have htri : ∀ F G : Fin q → ℝ,
      Real.sqrt (∑ s, (F s + G s) ^ 2) ≤
        Real.sqrt (∑ s, (F s) ^ 2) + Real.sqrt (∑ s, (G s) ^ 2) := by
    intro F G
    have h1 : (∑ s, (F s + G s) ^ 2) =
        (∑ s, (F s) ^ 2) + 2 * (∑ s, F s * G s) + (∑ s, (G s) ^ 2) := by
      have hstep : (∑ s, (F s + G s) ^ 2) =
          ∑ s, ((F s) ^ 2 + 2 * (F s * G s) + (G s) ^ 2) :=
        Finset.sum_congr rfl (fun s _ => by ring)
      rw [hstep, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h3 : (∑ s, F s * G s) ≤
        Real.sqrt (∑ s, (F s) ^ 2) * Real.sqrt (∑ s, (G s) ^ 2) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin q)) F G
    have h2 : (Real.sqrt (∑ s, (F s) ^ 2) + Real.sqrt (∑ s, (G s) ^ 2)) ^ 2 =
        (∑ s, (F s) ^ 2) + 2 * (Real.sqrt (∑ s, (F s) ^ 2) * Real.sqrt (∑ s, (G s) ^ 2)) +
          (∑ s, (G s) ^ 2) := by
      have hA : (Real.sqrt (∑ s, (F s) ^ 2)) ^ 2 = ∑ s, (F s) ^ 2 :=
        Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg (F s)))
      have hB : (Real.sqrt (∑ s, (G s) ^ 2)) ^ 2 = ∑ s, (G s) ^ 2 :=
        Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg (G s)))
      nlinarith [hA, hB]
    have hkey : (∑ s, (F s + G s) ^ 2) ≤
        (Real.sqrt (∑ s, (F s) ^ 2) + Real.sqrt (∑ s, (G s) ^ 2)) ^ 2 := by
      linarith [h1, h3, h2]
    calc Real.sqrt (∑ s, (F s + G s) ^ 2)
        ≤ Real.sqrt ((Real.sqrt (∑ s, (F s) ^ 2) + Real.sqrt (∑ s, (G s) ^ 2)) ^ 2) :=
          Real.sqrt_le_sqrt hkey
      _ = Real.sqrt (∑ s, (F s) ^ 2) + Real.sqrt (∑ s, (G s) ^ 2) := by
          rw [Real.sqrt_sq]
          positivity
  have hDt : ∀ j : Fin p, Real.sqrt (∑ s, (Dt j s) ^ 2) ≤ 2 * CH * Real.sqrt (q : ℝ) * a := by
    have h4 := hG4
    unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.RowL2Le at h4
    have h6 := hG6
    unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.RowL2Le at h6
    have hsqT : Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (n_t : ℝ)) = Real.sqrt (q : ℝ) * a := by
      have h1 : (q : ℝ) * Real.log (p : ℝ) / (n_t : ℝ) =
          (q : ℝ) * (Real.log (p : ℝ) / (n_t : ℝ)) := by ring
      rw [h1, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (q : ℝ))]
    intro j
    have hsplit : ∀ s : Fin q, Dt j s =
        ((∑ r, f (Ht r ω) j * Ht r ω s) / (n_t : ℝ) - M j s)
          + ((∑ r, Et r ω j * Ht r ω s) / (n_t : ℝ)) := by
      intro s
      have hsum : (∑ i, Xt i ω j * Ht i ω s) =
          (∑ i, f (Ht i ω) j * Ht i ω s) + ∑ i, Et i ω j * Ht i ω s := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by simp only [hX_model_t]; ring)
      simp only [Dt]
      rw [hsum]
      ring
    have hAa : Real.sqrt (∑ s, ((∑ r, f (Ht r ω) j * Ht r ω s) / (n_t : ℝ) - M j s) ^ 2) ≤
        CH * (Real.sqrt (q : ℝ) * a) := by
      have h4j := h4 j
      rw [hsqT] at h4j
      exact h4j
    have hBb : Real.sqrt (∑ s, ((∑ r, Et r ω j * Ht r ω s) / (n_t : ℝ)) ^ 2) ≤
        CH * (Real.sqrt (q : ℝ) * a) := by
      have h6j := h6 j
      rw [hsqT] at h6j
      exact h6j
    calc Real.sqrt (∑ s, (Dt j s) ^ 2)
        = Real.sqrt (∑ s, (((∑ r, f (Ht r ω) j * Ht r ω s) / (n_t : ℝ) - M j s)
            + ((∑ r, Et r ω j * Ht r ω s) / (n_t : ℝ))) ^ 2) := by
          simp only [hsplit]
      _ ≤ Real.sqrt (∑ s, ((∑ r, f (Ht r ω) j * Ht r ω s) / (n_t : ℝ) - M j s) ^ 2)
            + Real.sqrt (∑ s, ((∑ r, Et r ω j * Ht r ω s) / (n_t : ℝ)) ^ 2) :=
          htri _ _
      _ ≤ 2 * CH * Real.sqrt (q : ℝ) * a := by linarith [hAa, hBb]
  have hDs : ∀ j : Fin p, Real.sqrt (∑ s, (Ds j s) ^ 2) ≤ 2 * CH * Real.sqrt (q : ℝ) * a_s := by
    have h5 := hG5
    unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.RowL2Le at h5
    have h7 := hG7
    unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.RowL2Le at h7
    have hsqS : Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot) = Real.sqrt (q : ℝ) * a_s := by
      have h1 : (q : ℝ) * Real.log (p : ℝ) / nsTot =
          (q : ℝ) * (Real.log (p : ℝ) / nsTot) := by ring
      rw [h1, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (q : ℝ))]
      simp only [a_s, hN]
    intro j
    have hsplit : ∀ s : Fin q, Ds j s =
        ((∑ k, ∑ r, f (Hs k r ω) j * Hs k r ω s) / nsTot - M j s)
          + ((∑ k, ∑ r, Es k r ω j * Hs k r ω s) / nsTot) := by
      intro s
      have hsum : (∑ k, ∑ i, Xs k i ω j * Hs k i ω s) =
          (∑ k, ∑ i, f (Hs k i ω) j * Hs k i ω s)
            + ∑ k, ∑ i, Es k i ω j * Hs k i ω s := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by simp only [hX_model_s]; ring)
      simp only [Ds]
      rw [hsum, hN]
      ring
    have hAa : Real.sqrt (∑ s, ((∑ k, ∑ r, f (Hs k r ω) j * Hs k r ω s) / nsTot - M j s) ^ 2) ≤
        CH * (Real.sqrt (q : ℝ) * a_s) := by
      have h5j := h5 j
      rw [hsqS] at h5j
      exact h5j
    have hBb : Real.sqrt (∑ s, ((∑ k, ∑ r, Es k r ω j * Hs k r ω s) / nsTot) ^ 2) ≤
        CH * (Real.sqrt (q : ℝ) * a_s) := by
      have h7j := h7 j
      rw [hsqS] at h7j
      exact h7j
    calc Real.sqrt (∑ s, (Ds j s) ^ 2)
        = Real.sqrt (∑ s, (((∑ k, ∑ r, f (Hs k r ω) j * Hs k r ω s) / nsTot - M j s)
            + ((∑ k, ∑ r, Es k r ω j * Hs k r ω s) / nsTot)) ^ 2) := by
          simp only [hsplit]
      _ ≤ Real.sqrt (∑ s, ((∑ k, ∑ r, f (Hs k r ω) j * Hs k r ω s) / nsTot - M j s) ^ 2)
            + Real.sqrt (∑ s, ((∑ k, ∑ r, Es k r ω j * Hs k r ω s) / nsTot) ^ 2) :=
          htri _ _
      _ ≤ 2 * CH * Real.sqrt (q : ℝ) * a_s := by linarith [hAa, hBb]
  have hTphi : ∀ j : Fin p, |Tphi j| ≤ Cd * B_phi * Real.sqrt (q : ℝ) * a_s := by
    have h := hG10
    unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.VecSupLe
      PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.aSCoef at h
    intro j
    have hj := h j
    have key : Tphi j = (∑ k, ∑ s,
        ((∑ i, (f (Hs k i ω) + Es k i ω) j * Hs k i ω s) - (n_s k : ℝ) * M j s) *
          (fun k => phiS k - phiT) k s) / nsTot := by
      simp only [Tphi, hN, dk, hX_model_s, Pi.add_apply, Pi.sub_apply, Finset.mul_sum,
        Finset.sum_mul, div_eq_mul_inv]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [key]
    simp only [a_s, hN]
    exact hj
  have hMrow : ∀ j : Fin p, Real.sqrt (∑ s, (M j s) ^ 2) ≤ L_M * Real.sqrt (q : ℝ) := hM_row
  have hdbar : Real.sqrt (∑ s, (dbar s) ^ 2) ≤ C_phi * a := by
    simpa only [dbar, a, l2n, l2Sq] using hphi_bar
  have het : ∀ j : Fin p, |e_t j| ≤ Ceps * a := by
    have h := hG8
    unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.VecSupLe at h
    intro j
    have hj := h j
    have key : e_t j = (∑ r, (f (Ht r ω) + Et r ω) j * epsT r ω) / (n_t : ℝ) := by
      simp only [e_t, hX_model_t, Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv, Pi.add_apply]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [key]
    simp only [a]
    exact hj
  have hes : ∀ j : Fin p, |es j| ≤ Ceps * a_s := by
    have h := hG9
    unfold PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported.VecSupLe at h
    intro j
    have hj := h j
    have key : es j = (∑ k, ∑ r, (f (Hs k r ω) + Es k r ω) j * epsS k r ω) / nsTot := by
      simp only [es, hX_model_s, hN, Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv, Pi.add_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [key]
    simp only [a_s, hN]
    exact hj
  have hd : (∑ j, |d j|) ≤ C_s := by
    have h : (∑ j, |betaInit j - betaBar n_s betaS j|) ≤ C_s := by
      simpa only [l1n] using hbeta_init
    calc (∑ j, |d j|) = ∑ j, |betaInit j - betaBar n_s betaS j| := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [d]
          exact (abs_sub_comm _ _).symm
      _ ≤ C_s := h
  have has_le : a_s ≤ a := by
    have hp1' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1'
    have hratio : Real.log (p : ℝ) / (N : ℝ) ≤ Real.log (p : ℝ) / (n_t : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ hlogp
      rw [inv_le_inv₀ hNpos hntpos]
      exact_mod_cast hNge
    simp only [a_s, a]
    exact Real.sqrt_le_sqrt hratio
  have hprof : ∀ z : Fin n_t → ℝ,
      profileObj (fun i j => Xt i ω j) bvec Zhat ≤ profileObj (fun i j => Xt i ω j) bvec z := by
    intro z
    have h := hZmin (Set.mem_univ z)
    simpa only [bvec, profileObj, vecMatT, pooledTrans] using h
  have htune : 4 * (C_1 * Real.sqrt (q : ℝ) * Real.sqrt (∑ s, (phiT s) ^ 2) + C_2) * a ≤ lam := by
    have h := hlam
    simp only [l2n, l2Sq, C_1, C_2, a] at h ⊢
    exact h
  have hscore : maxAbs c ≤ lam / 4 := by
    refine statopia_math_node_1873299149_9a24b38e p q K n_t hp1 hq hK hnt1 n_s hns1
      (fun i j => Xt i ω j) (fun i j => Ht i ω j) (fun i => Yt i ω) (fun i => epsT i ω)
      (fun k i j => Xs k i ω j) (fun k i j => Hs k i ω j) (fun k i => Ys k i ω)
      (fun k i => epsS k i ω) betaT phiT betaInit betaS phiS SigmaX M Zhat
      Cx Cdelta CH Cd Ceps C_phi B_phi C_s L_M hCx hCdelta hCH hCd hCeps hCphi hBphi hC_s hL_M
      s_delta hs_delta lam hmodT hmodS hGramT hGramS hTbeta hDt hDs hTphi hMrow hdbar het hes hd
      has_le hprof htune
  have hlam' : 0 < lam := lt_of_lt_of_le hlam_pos hlam
  have hmin' : ∀ eta : Fin p → ℝ,
      lassoObj (fun i j => Xt i ω j) (fun i => Yt i ω) Zhat betaInit lam ηhat ≤
        lassoObj (fun i j => Xt i ω j) (fun i => Yt i ω) Zhat betaInit lam eta := by
    intro eta
    exact hηmin (Set.mem_univ eta)
  have hre' : ∀ u : Fin p → ℝ, u ∈ reCone (supportFinset (etaZero n_s betaT betaS)) →
      C_r * l2Sq u ≤ (1 / (n_t : ℝ)) * l2Sq (matVec (fun i j => Xt i ω j) u) := by
    intro u hu
    exact hR u hu
  exact statopia_math_node_127205983_b1e1c88b p n_t hp1 hnt1 (fun i j => Xt i ω j)
    (fun i => Yt i ω) Zhat betaInit (etaZero n_s betaT betaS) lam C_r hlam' hC_r s_eta hs_eta_p
    hS_eta ηhat hmin' hscore hre'
  /- @proof-region region.target-node.session.50a5026ba3edc1dc end -/

end ModelShiftLasso
end

