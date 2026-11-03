import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Vocabulary
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Base
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.ProvedNodes.Node_1873299149_9a24b38e_0252975c

namespace PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer.ModelShiftLasso

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ModelShiftLasso

set_option autoImplicit false in
theorem statopia_math_node_127205983_b1e1c88b : ∀ (p n_t : ℕ) (hp : 1 ≤ p) (hnt : 1 ≤ n_t)
    (Xt : Fin n_t → Fin p → ℝ) (Yt : Fin n_t → ℝ) (Zhat : Fin n_t → ℝ)
    (betaInit : Fin p → ℝ) (eta0 : Fin p → ℝ)
    (lam C_r : ℝ) (hlam : 0 < lam) (hC_r : 0 < C_r)
    (s_eta : ℕ) (hs_eta_p : s_eta ≤ p)
    (hS_eta : (supportFinset eta0).card ≤ s_eta)
    (etahat : Fin p → ℝ)
    (hmin : ∀ eta : Fin p → ℝ,
      lassoObj Xt Yt Zhat betaInit lam etahat ≤ lassoObj Xt Yt Zhat betaInit lam eta)
    (hscore : maxAbs (fun j : Fin p =>
      (1 / (n_t : ℝ)) * ∑ i : Fin n_t,
        (Yt i - vdot (Xt i) betaInit - Zhat i - vdot (Xt i) eta0) * Xt i j) ≤ lam / 4)
    (hre : ∀ u : Fin p → ℝ, u ∈ reCone (supportFinset eta0) →
      C_r * l2Sq u ≤ (1 / (n_t : ℝ)) * l2Sq (matVec Xt u)),
    MainBounds Xt eta0 etahat C_r s_eta lam := by
  /- @proof-region region.target-node.session.3fa2e8417b498b75 begin -/
  intro p n_t hp hn_t Xt Yt Zhat βinit eta0 lam C_r hlam hC_r s_eta hs_eta hcard etahat hmin hscore hRE
  classical
  have hCrne : C_r ≠ 0 := ne_of_gt hC_r
  have hnpos : (0 : ℝ) < (n_t : ℝ) := by exact_mod_cast hn_t
  set h : Fin p → ℝ := fun j => etahat j - eta0 j with hdef
  set S : Finset (Fin p) := supportFinset eta0 with hSdef
  set Sq : ℝ := Real.sqrt (s_eta : ℝ) with hSqdef
  have hSq_sq : Sq ^ 2 = (s_eta : ℝ) := by
    rw [hSqdef]
    exact Real.sq_sqrt (by positivity)
  have hSq_nn : 0 ≤ Sq := by
    rw [hSqdef]
    exact Real.sqrt_nonneg _
  set rv : Fin n_t → ℝ := fun i => Yt i - vdot (Xt i) βinit - Zhat i - vdot (Xt i) eta0 with hrvdef
  set cv : Fin p → ℝ := fun j => (1 / (n_t : ℝ)) * ∑ i, rv i * Xt i j with hcvdef
  have hSmem : ∀ j : Fin p, j ∈ S ↔ eta0 j ≠ 0 := by
    intro j
    rw [hSdef]
    simp [supportFinset]
  have hzero : ∀ j : Fin p, j ∉ S → eta0 j = 0 := by
    intro j hj
    by_contra hne
    exact hj ((hSmem j).2 hne)
  have hcj : ∀ j : Fin p, |cv j| ≤ lam / 4 := by
    intro j
    have hsc : maxAbs cv ≤ lam / 4 := by
      simpa only [hcvdef, hrvdef] using hscore
    have h1 : |cv j| ≤ maxAbs cv :=
      le_csSup (Finite.bddAbove_range (fun i : Fin p => |cv i|)) (Set.mem_range_self j)
    linarith
  have hvdot_add : ∀ (i : Fin n_t) (u : Fin p → ℝ),
      vdot (Xt i) (eta0 + u) = vdot (Xt i) eta0 + vdot (Xt i) u := by
    intro i u
    simp only [vdot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hvdot_h : ∀ i : Fin n_t, vdot (Xt i) h = vdot (Xt i) etahat - vdot (Xt i) eta0 := by
    intro i
    simp only [vdot, hdef, mul_sub, Finset.sum_sub_distrib]
  have hadd : eta0 + h = etahat := by
    funext j
    simp only [Pi.add_apply, hdef]
    ring
  have hres : ∀ (u : Fin p → ℝ) (i : Fin n_t),
      Yt i - vdot (Xt i) βinit - Zhat i - vdot (Xt i) (eta0 + u)
        = rv i - vdot (Xt i) u := by
    intro u i
    simp only [hrvdef]
    rw [hvdot_add i u]
    ring
  have hObj : ∀ u : Fin p → ℝ,
      lassoObj Xt Yt Zhat βinit lam (eta0 + u)
        = (1 / (n_t : ℝ)) * ∑ i, (rv i - vdot (Xt i) u) ^ 2 + lam * l1n (eta0 + u) := by
    intro u
    simp only [lassoObj]
    have hsum : ∑ i : Fin n_t, (Yt i - vdot (Xt i) βinit - Zhat i - vdot (Xt i) (eta0 + u)) ^ 2
        = ∑ i : Fin n_t, (rv i - vdot (Xt i) u) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hres u i]
    rw [hsum]
  have hBI : (1 / (n_t : ℝ)) * ∑ i, (rv i - vdot (Xt i) h) ^ 2 + lam * l1n (eta0 + h)
      ≤ (1 / (n_t : ℝ)) * ∑ i, (rv i) ^ 2 + lam * l1n eta0 := by
    have h1 : lassoObj Xt Yt Zhat βinit lam etahat ≤ lassoObj Xt Yt Zhat βinit lam eta0 :=
      hmin eta0
    have h2 : lassoObj Xt Yt Zhat βinit lam etahat
        = (1 / (n_t : ℝ)) * ∑ i, (rv i - vdot (Xt i) h) ^ 2 + lam * l1n (eta0 + h) := by
      rw [← hadd]
      exact hObj h
    have h3 : lassoObj Xt Yt Zhat βinit lam eta0
        = (1 / (n_t : ℝ)) * ∑ i, (rv i) ^ 2 + lam * l1n eta0 := by
      have hz : eta0 + (fun _ : Fin p => (0 : ℝ)) = eta0 := by
        funext j
        simp
      have hb := hObj (fun _ : Fin p => (0 : ℝ))
      rw [hz] at hb
      rw [hb]
      have hv0 : ∀ i : Fin n_t, vdot (Xt i) (fun _ : Fin p => (0 : ℝ)) = 0 := by
        intro i
        simp [vdot]
      simp only [hv0, sub_zero]
    linarith [h1, h2, h3]
  have hExp : (1 / (n_t : ℝ)) * ∑ i, (rv i - vdot (Xt i) h) ^ 2
      = (1 / (n_t : ℝ)) * ∑ i, (rv i) ^ 2
        - (2 / (n_t : ℝ)) * ∑ i, rv i * vdot (Xt i) h
        + (1 / (n_t : ℝ)) * ∑ i, (vdot (Xt i) h) ^ 2 := by
    have hsq : ∑ i : Fin n_t, (rv i - vdot (Xt i) h) ^ 2
        = ∑ i, (rv i) ^ 2 - 2 * ∑ i, rv i * vdot (Xt i) h
          + ∑ i, (vdot (Xt i) h) ^ 2 := by
      calc ∑ i : Fin n_t, (rv i - vdot (Xt i) h) ^ 2
          = ∑ i, ((rv i) ^ 2 - 2 * (rv i * vdot (Xt i) h) + (vdot (Xt i) h) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = ∑ i, ((rv i) ^ 2 - 2 * (rv i * vdot (Xt i) h)) + ∑ i, (vdot (Xt i) h) ^ 2 :=
            Finset.sum_add_distrib
        _ = (∑ i, (rv i) ^ 2 - ∑ i, 2 * (rv i * vdot (Xt i) h))
              + ∑ i, (vdot (Xt i) h) ^ 2 := by
            rw [Finset.sum_sub_distrib]
        _ = ∑ i, (rv i) ^ 2 - 2 * ∑ i, rv i * vdot (Xt i) h
              + ∑ i, (vdot (Xt i) h) ^ 2 := by
            rw [← Finset.mul_sum]
    rw [hsq]
    ring
  have hkey : (1 / (n_t : ℝ)) * l2Sq (matVec Xt h)
      ≤ (2 / (n_t : ℝ)) * ∑ i, rv i * vdot (Xt i) h
        + lam * (l1n eta0 - l1n (eta0 + h)) := by
    have hQe : (1 / (n_t : ℝ)) * ∑ i, (vdot (Xt i) h) ^ 2
        = (1 / (n_t : ℝ)) * l2Sq (matVec Xt h) := by
      simp only [l2Sq, matVec]
    have h1 := hBI
    rw [hExp] at h1
    linarith [hQe]
  have hpair : (1 / (n_t : ℝ)) * ∑ i, rv i * vdot (Xt i) h = ∑ j, cv j * h j := by
    have hstep1 : ∀ i : Fin n_t, rv i * vdot (Xt i) h = ∑ j, rv i * (Xt i j * h j) := by
      intro i
      rw [vdot, Finset.mul_sum]
    have hstep2 : ∑ i : Fin n_t, ∑ j : Fin p, rv i * (Xt i j * h j)
        = ∑ j : Fin p, ∑ i : Fin n_t, rv i * (Xt i j * h j) := Finset.sum_comm
    have hstep3 : ∀ j : Fin p, ∑ i : Fin n_t, rv i * (Xt i j * h j)
        = (∑ i : Fin n_t, rv i * Xt i j) * h j := by
      intro j
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    calc (1 / (n_t : ℝ)) * ∑ i, rv i * vdot (Xt i) h
        = (1 / (n_t : ℝ)) * ∑ i : Fin n_t, ∑ j : Fin p, rv i * (Xt i j * h j) := by
          rw [Finset.sum_congr rfl (fun i _ => hstep1 i)]
      _ = (1 / (n_t : ℝ)) * ∑ j : Fin p, ∑ i : Fin n_t, rv i * (Xt i j * h j) := by
          rw [hstep2]
      _ = (1 / (n_t : ℝ)) * ∑ j : Fin p, (∑ i : Fin n_t, rv i * Xt i j) * h j := by
          rw [Finset.sum_congr rfl (fun j _ => hstep3 j)]
      _ = ∑ j : Fin p, ((1 / (n_t : ℝ)) * ∑ i : Fin n_t, rv i * Xt i j) * h j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = ∑ j : Fin p, cv j * h j := by
          rw [hcvdef]
  have hscore2 : (2 / (n_t : ℝ)) * ∑ i, rv i * vdot (Xt i) h ≤ (lam / 2) * l1n h := by
    have hp2 : (2 / (n_t : ℝ)) * ∑ i, rv i * vdot (Xt i) h = 2 * ∑ j, cv j * h j := by
      calc (2 / (n_t : ℝ)) * ∑ i, rv i * vdot (Xt i) h
          = 2 * ((1 / (n_t : ℝ)) * ∑ i, rv i * vdot (Xt i) h) := by ring
        _ = 2 * ∑ j, cv j * h j := by rw [hpair]
    rw [hp2]
    have habs : |∑ j : Fin p, cv j * h j| ≤ (lam / 4) * l1n h := by
      have h1 : |∑ j : Fin p, cv j * h j| ≤ ∑ j : Fin p, |cv j * h j| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : ∑ j : Fin p, |cv j * h j| ≤ ∑ j : Fin p, (lam / 4) * |h j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hcj j) (abs_nonneg _)
      have h3 : ∑ j : Fin p, (lam / 4) * |h j| = (lam / 4) * l1n h := by
        rw [l1n, Finset.mul_sum]
      linarith [h1, h2, h3]
    have h4 : ∑ j : Fin p, cv j * h j ≤ (lam / 4) * l1n h := le_trans (le_abs_self _) habs
    linarith [h4]
  have hsplit0 : ∀ u : Fin p → ℝ, l1n u = l1On S u + l1On (Finset.univ \ S) u := by
    intro u
    have hsu : ∑ x ∈ Finset.univ \ S, |u x| + ∑ x ∈ S, |u x| = ∑ x, |u x| :=
      Finset.sum_sdiff (Finset.subset_univ S)
    simp only [l1n, l1On]
    linarith [hsu]
  have hsupp : lam * (l1n eta0 - l1n (eta0 + h))
      ≤ lam * (l1On S h - l1On (Finset.univ \ S) h) := by
    have hpt : ∀ j : Fin p, |eta0 j| - |eta0 j + h j| ≤ |h j| := by
      intro j
      have hh1 : |eta0 j| ≤ |eta0 j + h j| + |h j| := by
        have h2 : |eta0 j| = |(eta0 j + h j) + -(h j)| := by
          rw [show (eta0 j + h j) + -(h j) = eta0 j by ring]
        rw [h2]
        have h3 := abs_add_le (eta0 j + h j) (-(h j))
        rwa [abs_neg] at h3
      linarith
    have hA_le : l1On S eta0 - l1On S (eta0 + h) ≤ l1On S h := by
      have h1 : l1On S eta0 ≤ l1On S (eta0 + h) + l1On S h := by
        simp only [l1On, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum (fun j _ => by
          have := hpt j
          linarith)
      linarith
    have hB0 : l1On (Finset.univ \ S) eta0 = 0 := by
      simp only [l1On]
      apply Finset.sum_eq_zero
      intro j hj
      have hj' : j ∉ S := (Finset.mem_sdiff.mp hj).2
      simp only [hzero j hj', abs_zero]
    have hB1 : l1On (Finset.univ \ S) (eta0 + h) = l1On (Finset.univ \ S) h := by
      simp only [l1On]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ∉ S := (Finset.mem_sdiff.mp hj).2
      simp only [Pi.add_apply, hzero j hj', zero_add]
    have h1 : l1n eta0 - l1n (eta0 + h) ≤ l1On S h - l1On (Finset.univ \ S) h := by
      have e0 := hsplit0 eta0
      have e1 := hsplit0 (eta0 + h)
      rw [e0, e1, hB0, hB1]
      linarith [hA_le]
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt hlam)
  have hQ : (1 / (n_t : ℝ)) * l2Sq (matVec Xt h)
      ≤ (3 * lam / 2) * l1On S h - (lam / 2) * l1On (Finset.univ \ S) h := by
    have hL := hsplit0 h
    have h2 : (2 / (n_t : ℝ)) * ∑ i, rv i * vdot (Xt i) h ≤ (lam / 2) * l1n h := hscore2
    rw [hL] at h2
    linarith [hkey, h2, hsupp]
  have hQnn : 0 ≤ (1 / (n_t : ℝ)) * l2Sq (matVec Xt h) := by
    have h1 : 0 ≤ l2Sq (matVec Xt h) := by
      simp only [l2Sq]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h2 : (0 : ℝ) ≤ 1 / (n_t : ℝ) := by positivity
    exact mul_nonneg h2 h1
  have hcone' : l1On (Finset.univ \ S) h ≤ 3 * l1On S h := by
    have hstep : (lam / 2) * l1On (Finset.univ \ S) h ≤ (lam / 2) * (3 * l1On S h) := by
      have h1 : (lam / 2) * l1On (Finset.univ \ S) h ≤ (3 * lam / 2) * l1On S h := by
        linarith [hQ, hQnn]
      linarith [h1]
    exact le_of_mul_le_mul_left hstep (by linarith : (0 : ℝ) < lam / 2)
  have hcone_mem : h ∈ reCone S := by
    rw [reCone, Set.mem_setOf_eq]
    convert hcone' using 2
    apply Finset.ext
    intro a
    simp only [Finset.mem_sdiff]
  have hREh : C_r * l2Sq h ≤ (1 / (n_t : ℝ)) * l2Sq (matVec Xt h) := hRE h hcone_mem
  have hl1 : l1n h ≤ 4 * l1On S h := by
    have hsp := hsplit0 h
    linarith [hsp, hcone']
  have hCS : l1On S h ≤ Sq * l2n h := by
    have hsq1 : Real.sqrt (1 : ℝ) = 1 := by
      rw [show (1 : ℝ) = 1 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    have h1 : l1On S h ≤ Real.sqrt (∑ j ∈ S, (h j) ^ 2) * Real.sqrt ((S.card : ℝ)) := by
      have hsch := Real.sum_sqrt_mul_sqrt_le (s := S) (f := fun j : Fin p => (h j) ^ 2)
        (g := fun _ => (1 : ℝ)) (fun i => sq_nonneg (h i)) (fun i => by norm_num)
      have hsum1 : ∑ j ∈ S, (1 : ℝ) = (S.card : ℝ) := by simp
      calc l1On S h = ∑ j ∈ S, Real.sqrt ((h j) ^ 2) * Real.sqrt (1 : ℝ) := by
            simp only [l1On, Real.sqrt_sq_eq_abs, hsq1, mul_one]
        _ ≤ Real.sqrt (∑ j ∈ S, (h j) ^ 2) * Real.sqrt (∑ j ∈ S, (1 : ℝ)) := hsch
        _ = Real.sqrt (∑ j ∈ S, (h j) ^ 2) * Real.sqrt ((S.card : ℝ)) := by rw [hsum1]
    have h2 : ∑ j ∈ S, (h j) ^ 2 ≤ l2Sq h := by
      simp only [l2Sq]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun x _ _ => sq_nonneg (h x))
    have h3 : Real.sqrt (∑ j ∈ S, (h j) ^ 2) ≤ l2n h := by
      rw [l2n]
      exact Real.sqrt_le_sqrt h2
    have h4 : Real.sqrt ((S.card : ℝ)) ≤ Sq := by
      rw [hSqdef]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hcard)
    calc l1On S h ≤ Real.sqrt (∑ j ∈ S, (h j) ^ 2) * Real.sqrt ((S.card : ℝ)) := h1
      _ ≤ l2n h * Sq := mul_le_mul h3 h4 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Sq * l2n h := by ring
  have hsqh : l2Sq h = (l2n h) ^ 2 := by
    have hnn : (0 : ℝ) ≤ l2Sq h := by
      simp only [l2Sq]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rw [l2n]
    exact (Real.sq_sqrt hnn).symm
  have hCry : C_r * (l2n h) ^ 2 ≤ (1 / (n_t : ℝ)) * l2Sq (matVec Xt h) := by
    have h1 := hREh
    rw [hsqh] at h1
    exact h1
  have hQ2 : (1 / (n_t : ℝ)) * l2Sq (matVec Xt h) ≤ (3 * lam / 2) * l1On S h := by
    have hB_nn : 0 ≤ l1On (Finset.univ \ S) h := by
      simp only [l1On]
      exact Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have h3 : (0 : ℝ) ≤ (lam / 2) * l1On (Finset.univ \ S) h := by
      have h4 : (0 : ℝ) < lam / 2 := by linarith
      exact mul_nonneg (le_of_lt h4) hB_nn
    linarith [hQ, h3]
  have hyCr : C_r * l2n h ≤ (3 * lam / 2) * Sq := by
    have hstep : (3 * lam / 2) * l1On S h ≤ (3 * lam / 2) * (Sq * l2n h) := by
      have h3 : (0 : ℝ) ≤ 3 * lam / 2 := by linarith
      exact mul_le_mul_of_nonneg_left hCS h3
    have hKy : C_r * (l2n h) ^ 2 ≤ ((3 * lam / 2) * Sq) * l2n h := by
      have h1 : (1 / (n_t : ℝ)) * l2Sq (matVec Xt h) ≤ (3 * lam / 2) * (Sq * l2n h) :=
        le_trans hQ2 hstep
      have h2 : C_r * (l2n h) ^ 2 ≤ (1 / (n_t : ℝ)) * l2Sq (matVec Xt h) := hCry
      linarith [h1, h2]
    rcases eq_or_lt_of_le (Real.sqrt_nonneg (l2Sq h) : (0 : ℝ) ≤ l2n h) with h0 | hpos
    · have hy0 : l2n h = 0 := by
        rw [l2n]
        exact h0.symm
      rw [hy0]
      have h3 : (0 : ℝ) ≤ 3 * lam / 2 := by linarith
      simpa using mul_nonneg h3 hSq_nn
    · have h4 : l2n h * (C_r * l2n h) ≤ l2n h * ((3 * lam / 2) * Sq) := by
        linarith [hKy]
      exact le_of_mul_le_mul_left h4 hpos
  have hy : l2n h ≤ 3 / (2 * C_r) * Sq * lam := by
    have hgoal : 3 / (2 * C_r) * Sq * lam = (3 * Sq * lam) / (2 * C_r) := by ring
    rw [hgoal]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C_r)]
    linarith [hyCr]
  have hy1 : l1n h ≤ 6 / C_r * (s_eta : ℝ) * lam := by
    have h1 : l1n h ≤ 4 * (Sq * l2n h) :=
      le_trans hl1 (mul_le_mul_of_nonneg_left hCS (by norm_num : (0 : ℝ) ≤ 4))
    have h2 : 4 * (Sq * l2n h) ≤ 6 / C_r * (s_eta : ℝ) * lam := by
      rw [show 6 / C_r * (s_eta : ℝ) * lam = (6 * (s_eta : ℝ) * lam) / C_r by ring]
      rw [le_div_iff₀ hC_r]
      have hbase : 4 * (Sq * l2n h) * C_r = 4 * Sq * (C_r * l2n h) := by ring
      rw [hbase]
      have hmono : 4 * Sq * (C_r * l2n h) ≤ 4 * Sq * ((3 * lam / 2) * Sq) := by
        apply mul_le_mul_of_nonneg_left hyCr
        have h4 : (0 : ℝ) ≤ 4 * Sq := by linarith [hSq_nn]
        exact h4
      have hval : 4 * Sq * ((3 * lam / 2) * Sq) = 6 * (s_eta : ℝ) * lam := by
        have h4 : 4 * Sq * ((3 * lam / 2) * Sq) = 6 * lam * (Sq ^ 2) := by ring
        rw [h4, hSq_sq]
        ring
      linarith [hmono, hval]
    linarith [h1, h2]
  have hVl2Sq : l2Sq (matVec Xt h) = (l2n (matVec Xt h)) ^ 2 := by
    have hnn : (0 : ℝ) ≤ l2Sq (matVec Xt h) := by
      simp only [l2Sq]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rw [l2n]
    exact (Real.sq_sqrt hnn).symm
  have hQb : (1 / (n_t : ℝ)) * l2Sq (matVec Xt h) ≤ 9 * (s_eta : ℝ) * lam ^ 2 / (4 * C_r) := by
    have h1 : (1 / (n_t : ℝ)) * l2Sq (matVec Xt h) ≤ (3 * lam / 2) * (Sq * l2n h) := by
      have h3 : (0 : ℝ) ≤ 3 * lam / 2 := by linarith
      exact le_trans hQ2 (mul_le_mul_of_nonneg_left hCS h3)
    have h2 : (3 * lam / 2) * (Sq * l2n h) ≤ 9 * (s_eta : ℝ) * lam ^ 2 / (4 * C_r) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * C_r)]
      have hbase : (3 * lam / 2) * (Sq * l2n h) * (4 * C_r)
          = 6 * lam * (Sq * (C_r * l2n h)) := by ring
      rw [hbase]
      have hmono : 6 * lam * (Sq * (C_r * l2n h)) ≤ 6 * lam * (Sq * ((3 * lam / 2) * Sq)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hyCr hSq_nn
        · have h6 : (0 : ℝ) ≤ 6 * lam := by linarith
          exact h6
      have hval : 6 * lam * (Sq * ((3 * lam / 2) * Sq)) = 9 * (s_eta : ℝ) * lam ^ 2 := by
        have h6 : 6 * lam * (Sq * ((3 * lam / 2) * Sq)) = 9 * lam ^ 2 * (Sq ^ 2) := by ring
        rw [h6, hSq_sq]
        ring
      linarith [hmono, hval]
    linarith [h1, h2]
  have hy3 : l2n (matVec Xt h) / Real.sqrt (n_t : ℝ) ≤ 3 / (2 * Real.sqrt C_r) * Sq * lam := by
    have hb : l2Sq (matVec Xt h) ≤ (n_t : ℝ) * (9 * (s_eta : ℝ) * lam ^ 2 / (4 * C_r)) := by
      have h1 : (n_t : ℝ) * ((1 / (n_t : ℝ)) * l2Sq (matVec Xt h))
          ≤ (n_t : ℝ) * (9 * (s_eta : ℝ) * lam ^ 2 / (4 * C_r)) :=
        mul_le_mul_of_nonneg_left hQb (le_of_lt hnpos)
      have h2 : (n_t : ℝ) * ((1 / (n_t : ℝ)) * l2Sq (matVec Xt h)) = l2Sq (matVec Xt h) := by
        field_simp
      rwa [h2] at h1
    have hb_sq : (3 * Sq * lam / (2 * Real.sqrt C_r)) ^ 2 = 9 * (s_eta : ℝ) * lam ^ 2 / (4 * C_r) := by
      have hCr_sq : (Real.sqrt C_r) ^ 2 = C_r := Real.sq_sqrt (le_of_lt hC_r)
      have hden : (2 * Real.sqrt C_r) ^ 2 = 4 * C_r := by
        rw [mul_pow, hCr_sq]
        norm_num
      have hnum : (3 * Sq * lam) ^ 2 = 9 * (s_eta : ℝ) * lam ^ 2 := by
        rw [mul_pow, mul_pow, hSq_sq]
        norm_num
      rw [div_pow, hnum, hden]
    have hb_nn : 0 ≤ 3 * Sq * lam / (2 * Real.sqrt C_r) := by
      have hnum_nn : (0 : ℝ) ≤ 3 * Sq * lam :=
        mul_nonneg (mul_nonneg (by norm_num) hSq_nn) (le_of_lt hlam)
      have hden_nn : (0 : ℝ) ≤ 2 * Real.sqrt C_r := by positivity
      exact div_nonneg hnum_nn hden_nn
    have hsqrt_eq : Real.sqrt ((n_t : ℝ) * (9 * (s_eta : ℝ) * lam ^ 2 / (4 * C_r)))
        = Real.sqrt (n_t : ℝ) * (3 * Sq * lam / (2 * Real.sqrt C_r)) := by
      rw [show (n_t : ℝ) * (9 * (s_eta : ℝ) * lam ^ 2 / (4 * C_r))
            = (n_t : ℝ) * (3 * Sq * lam / (2 * Real.sqrt C_r)) ^ 2 by rw [hb_sq]]
      rw [Real.sqrt_mul (le_of_lt hnpos)]
      rw [Real.sqrt_sq hb_nn]
    have hsqrt : l2n (matVec Xt h)
        ≤ Real.sqrt (n_t : ℝ) * (3 * Sq * lam / (2 * Real.sqrt C_r)) := by
      rw [← hsqrt_eq]
      rw [l2n]
      exact Real.sqrt_le_sqrt hb
    have hgoal_eq : 3 / (2 * Real.sqrt C_r) * Sq * lam = 3 * Sq * lam / (2 * Real.sqrt C_r) := by ring
    rw [hgoal_eq]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt (n_t : ℝ))]
    calc l2n (matVec Xt h)
        ≤ Real.sqrt (n_t : ℝ) * (3 * Sq * lam / (2 * Real.sqrt C_r)) := hsqrt
      _ = 3 * Sq * lam / (2 * Real.sqrt C_r) * Real.sqrt (n_t : ℝ) := by ring
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hdef] using hy1
  · simpa only [hdef, hSqdef] using hy
  · simpa only [hdef, hSqdef] using hy3
  /- @proof-region region.target-node.session.3fa2e8417b498b75 end -/

end ModelShiftLasso
end

