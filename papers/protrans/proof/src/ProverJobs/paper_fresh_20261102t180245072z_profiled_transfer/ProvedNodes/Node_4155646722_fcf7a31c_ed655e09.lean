import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Vocabulary
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Base

namespace PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer.ModelShiftLasso

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ModelShiftLasso

set_option autoImplicit false in
theorem statopia_math_node_4155646722_fcf7a31c : ∀ (p q K n_t : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hK : 1 ≤ K) (hnt : 1 ≤ n_t)
    (n_s : Fin K → ℕ) (hns : ∀ k, 1 ≤ n_s k)
    (Xt : Fin n_t → Fin p → ℝ) (Ht : Fin n_t → Fin q → ℝ)
    (Xs : (k : Fin K) → Fin (n_s k) → Fin p → ℝ)
    (Hs : (k : Fin K) → Fin (n_s k) → Fin q → ℝ)
    (epsS : (k : Fin K) → Fin (n_s k) → ℝ)
    (Ys : (k : Fin K) → Fin (n_s k) → ℝ)
    (betaInit : Fin p → ℝ) (phiT : Fin q → ℝ)
    (betaS : Fin K → Fin p → ℝ) (phiS : Fin K → Fin q → ℝ)
    (SigmaX : Fin p → Fin p → ℝ) (M : Fin p → Fin q → ℝ)
    (hmodel : ∀ (k : Fin K) (irow : Fin (n_s k)),
      Ys k irow = vdot (Xs k irow) (betaS k) + vdot (Hs k irow) (phiS k) + epsS k irow)
    (j : Fin p),
    let N : ℕ := ∑ k, n_s k
    let d : Fin p → ℝ := fun j => betaBar n_s betaS j - betaInit j
    let deltaK : Fin K → Fin p → ℝ := fun k j => betaS k j - betaBar n_s betaS j
    let dk : Fin K → Fin q → ℝ := fun k s => phiS k s - phiT s
    let dbar : Fin q → ℝ := fun s => phiBar n_s phiS s - phiT s
    let Gt : Fin p → Fin p → ℝ := fun j t => (1 / (n_t : ℝ)) * (∑ i, Xt i j * Xt i t)
    let Gs : Fin p → Fin p → ℝ :=
      fun j t => (1 / (N : ℝ)) * (∑ k, ∑ irow, Xs k irow j * Xs k irow t)
    let Tbeta : Fin p → ℝ := fun j => (1 / (N : ℝ)) *
      (∑ k, ∑ t, ((∑ irow, Xs k irow j * Xs k irow t) - (n_s k : ℝ) * SigmaX j t)
        * deltaK k t)
    let Dt : Fin p → Fin q → ℝ :=
      fun j s => (1 / (n_t : ℝ)) * (∑ i, Xt i j * Ht i s) - M j s
    let Ds : Fin p → Fin q → ℝ :=
      fun j s => (1 / (N : ℝ)) * (∑ k, ∑ irow, Xs k irow j * Hs k irow s) - M j s
    let Tphi : Fin p → ℝ := fun j => (1 / (N : ℝ)) *
      (∑ k, ∑ s, ((∑ irow, Xs k irow j * Hs k irow s) - (n_s k : ℝ) * M j s) * dk k s)
    let es : Fin p → ℝ :=
      fun j => (1 / (N : ℝ)) * (∑ k, ∑ irow, epsS k irow * Xs k irow j)
    let bvec : Fin p → ℝ :=
      pooledTrans n_s Xs (fun k irow => Ys k irow - vdot (Xs k irow) betaInit)

    let Z0 : Fin n_t → ℝ := fun i => vdot (Xt i) d + vdot (Ht i) phiT
    let Delta : Fin p → ℝ :=
      fun j => (1 / (n_t : ℝ)) * (∑ i, Z0 i * Xt i j) - bvec j
    Delta j = (∑ t, (Gt j t - Gs j t) * d t) - Tbeta j
      + (∑ s, (Dt j s - Ds j s) * phiT s) - (∑ s, M j s * dbar s) - Tphi j - es j := by
  /- @proof-region region.target-node.session.5c7c74de02fddcf2 begin -/
  intro p q K n_t hp hq hK hn_t n_s hn_s Xt Ht Xs Hs eps_s Ys beta_init phi_t beta_s phi_s SigmaX M hY
  dsimp only
  intro j
  haveI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  have hSpos : 0 < ∑ k, n_s k := by
    obtain ⟨k0⟩ := ‹Nonempty (Fin K)›
    have h1 : n_s k0 ≤ ∑ k, n_s k :=
      Finset.single_le_sum (f := n_s) (fun i _ => Nat.zero_le (n_s i)) (Finset.mem_univ k0)
    have h2 : 0 < n_s k0 := hn_s k0
    omega
  set S : ℝ := ((∑ k, n_s k : ℕ) : ℝ) with hSdef
  have hSposR : (0 : ℝ) < S := by
    rw [hSdef]
    exact Nat.cast_pos.mpr hSpos
  have hSne : S ≠ 0 := ne_of_gt hSposR
  have hScases : S = ∑ k, (n_s k : ℝ) := by
    rw [hSdef]
    exact Nat.cast_sum _ _
  have hsumw : ∑ k, (n_s k : ℝ) / S = 1 := by
    rw [← Finset.sum_div, ← hScases]
    exact div_self hSne
  have hdelta0 : ∀ t, ∑ k, (n_s k : ℝ) / S * (beta_s k t - betaBar n_s beta_s t) = 0 := by
    intro t
    have h1 : (∑ k, (n_s k : ℝ) / S * beta_s k t) = betaBar n_s beta_s t := by
      simp only [betaBar, sourceWeight, hSdef]
    calc ∑ k, (n_s k : ℝ) / S * (beta_s k t - betaBar n_s beta_s t)
        = ∑ k, ((n_s k : ℝ) / S * beta_s k t - (n_s k : ℝ) / S * betaBar n_s beta_s t) :=
          Finset.sum_congr rfl (fun k _ => by ring)
      _ = (∑ k, (n_s k : ℝ) / S * beta_s k t) - ∑ k, (n_s k : ℝ) / S * betaBar n_s beta_s t := by
          simp only [Finset.sum_sub_distrib]
      _ = betaBar n_s beta_s t - (∑ k, (n_s k : ℝ) / S) * betaBar n_s beta_s t := by
          rw [h1, ← Finset.sum_mul]
      _ = 0 := by rw [hsumw]; ring
  have hA :
      (1 / (n_t : ℝ)) * (∑ i, (vdot (Xt i) (fun j => betaBar n_s beta_s j - beta_init j)
          + vdot (Ht i) phi_t) * Xt i j)
      = (∑ t, (1 / (n_t : ℝ) * (∑ i, Xt i j * Xt i t)) * (betaBar n_s beta_s t - beta_init t))
        + (1 / (n_t : ℝ)) * (∑ i, (∑ s, Ht i s * phi_t s) * Xt i j) := by
    have hA1 : (∑ i, ((∑ t, Xt i t * (betaBar n_s beta_s t - beta_init t)) + ∑ s, Ht i s * phi_t s) * Xt i j)
        = (∑ i, (∑ t, Xt i t * (betaBar n_s beta_s t - beta_init t)) * Xt i j)
          + (∑ i, (∑ s, Ht i s * phi_t s) * Xt i j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hA2 : (∑ i, (∑ t, Xt i t * (betaBar n_s beta_s t - beta_init t)) * Xt i j)
        = ∑ t, (∑ i, Xt i j * Xt i t) * (betaBar n_s beta_s t - beta_init t) := by
      have e1 : (∑ i, (∑ t, Xt i t * (betaBar n_s beta_s t - beta_init t)) * Xt i j)
          = ∑ i, ∑ t, Xt i t * (betaBar n_s beta_s t - beta_init t) * Xt i j := by
        exact Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])
      have e2 : (∑ i, ∑ t, Xt i t * (betaBar n_s beta_s t - beta_init t) * Xt i j)
          = ∑ t, ∑ i, Xt i t * (betaBar n_s beta_s t - beta_init t) * Xt i j := Finset.sum_comm
      have e3 : (∑ t, ∑ i, Xt i t * (betaBar n_s beta_s t - beta_init t) * Xt i j)
          = ∑ t, (∑ i, Xt i j * Xt i t) * (betaBar n_s beta_s t - beta_init t) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        have e4 : (∑ i, Xt i t * (betaBar n_s beta_s t - beta_init t) * Xt i j)
            = ∑ i, Xt i j * Xt i t * (betaBar n_s beta_s t - beta_init t) :=
          Finset.sum_congr rfl (fun i _ => by ring)
        rw [e4, Finset.sum_mul]
      rw [e1, e2, e3]
    have hA3 : (1 / (n_t : ℝ)) * (∑ t, (∑ i, Xt i j * Xt i t) * (betaBar n_s beta_s t - beta_init t))
        = ∑ t, (1 / (n_t : ℝ) * (∑ i, Xt i j * Xt i t)) * (betaBar n_s beta_s t - beta_init t) := by
      conv_lhs => rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    calc (1 / (n_t : ℝ)) * (∑ i, ((∑ t, Xt i t * (betaBar n_s beta_s t - beta_init t))
            + ∑ s, Ht i s * phi_t s) * Xt i j)
        = (1 / (n_t : ℝ)) * ((∑ i, (∑ t, Xt i t * (betaBar n_s beta_s t - beta_init t)) * Xt i j)
            + (∑ i, (∑ s, Ht i s * phi_t s) * Xt i j)) := by rw [hA1]
      _ = (1 / (n_t : ℝ)) * (∑ i, (∑ t, Xt i t * (betaBar n_s beta_s t - beta_init t)) * Xt i j)
            + (1 / (n_t : ℝ)) * (∑ i, (∑ s, Ht i s * phi_t s) * Xt i j) := by ring
      _ = (1 / (n_t : ℝ)) * (∑ t, (∑ i, Xt i j * Xt i t) * (betaBar n_s beta_s t - beta_init t))
            + (1 / (n_t : ℝ)) * (∑ i, (∑ s, Ht i s * phi_t s) * Xt i j) := by rw [hA2]
      _ = (∑ t, (1 / (n_t : ℝ) * (∑ i, Xt i j * Xt i t)) * (betaBar n_s beta_s t - beta_init t))
            + (1 / (n_t : ℝ)) * (∑ i, (∑ s, Ht i s * phi_t s) * Xt i j) := by rw [hA3]
  have hB :
      (1 / S) * (∑ k, ∑ i', (Ys k i' - vdot (Xs k i') beta_init) * Xs k i' j)
      = (∑ t, (1 / S * (∑ k, ∑ i', Xs k i' j * Xs k i' t)) * (betaBar n_s beta_s t - beta_init t))
        + (1 / S) * (∑ k, ∑ t, (∑ i', Xs k i' j * Xs k i' t - (n_s k : ℝ) * SigmaX j t)
            * (beta_s k t - betaBar n_s beta_s t))
        + (1 / S) * (∑ k, ∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
        + (1 / S) * (∑ k, ∑ i', eps_s k i' * Xs k i' j) := by
    have hstep : ∀ (k : Fin K) (i' : Fin (n_s k)),
        Ys k i' - vdot (Xs k i') beta_init
        = (∑ t, Xs k i' t * (beta_s k t - beta_init t)) + (∑ s, Hs k i' s * phi_s k s) + eps_s k i' := by
      intro k i'
      have hdist : (∑ t, Xs k i' t * (beta_s k t - beta_init t))
          = (∑ t, Xs k i' t * beta_s k t) - (∑ t, Xs k i' t * beta_init t) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun t _ => by ring)
      rw [hY k i', hdist]
      simp only [vdot]
      ring
    have hB0 : (∑ k, ∑ i', (Ys k i' - vdot (Xs k i') beta_init) * Xs k i' j)
        = ∑ k, ∑ i', ((∑ t, Xs k i' t * (beta_s k t - beta_init t))
            + (∑ s, Hs k i' s * phi_s k s) + eps_s k i') * Xs k i' j :=
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i' _ => by rw [hstep k i']))
    have hsplitB : (∑ k, ∑ i', ((∑ t, Xs k i' t * (beta_s k t - beta_init t))
            + (∑ s, Hs k i' s * phi_s k s) + eps_s k i') * Xs k i' j)
        = (∑ k, ∑ i', (∑ t, Xs k i' t * (beta_s k t - beta_init t)) * Xs k i' j)
          + (∑ k, ∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
          + (∑ k, ∑ i', eps_s k i' * Xs k i' j) := by
      simp only [add_mul, Finset.sum_add_distrib]
    have hcoef : (∑ k, ∑ i', (∑ t, Xs k i' t * (beta_s k t - beta_init t)) * Xs k i' j)
        = (∑ k, ∑ i', (∑ t, Xs k i' t * (beta_s k t - betaBar n_s beta_s t)) * Xs k i' j)
          + (∑ k, ∑ i', (∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t)) * Xs k i' j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      have f : (∑ t, Xs k i' t * (beta_s k t - beta_init t))
          = (∑ t, Xs k i' t * (beta_s k t - betaBar n_s beta_s t))
            + (∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun t _ => by ring)
      rw [f]
      ring
    have hdelta : (∑ k, ∑ i', (∑ t, Xs k i' t * (beta_s k t - betaBar n_s beta_s t)) * Xs k i' j)
        = ∑ k, ∑ t, (∑ i', Xs k i' j * Xs k i' t) * (beta_s k t - betaBar n_s beta_s t) := by
      have e1 : ∀ k, (∑ i', (∑ t, Xs k i' t * (beta_s k t - betaBar n_s beta_s t)) * Xs k i' j)
          = ∑ t, (∑ i', Xs k i' j * Xs k i' t) * (beta_s k t - betaBar n_s beta_s t) := by
        intro k
        have g1 : (∑ i', (∑ t, Xs k i' t * (beta_s k t - betaBar n_s beta_s t)) * Xs k i' j)
            = ∑ i', ∑ t, Xs k i' t * (beta_s k t - betaBar n_s beta_s t) * Xs k i' j :=
          Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])
        have g2 : (∑ i', ∑ t, Xs k i' t * (beta_s k t - betaBar n_s beta_s t) * Xs k i' j)
            = ∑ t, ∑ i', Xs k i' t * (beta_s k t - betaBar n_s beta_s t) * Xs k i' j :=
          Finset.sum_comm
        have g3 : (∑ t, ∑ i', Xs k i' t * (beta_s k t - betaBar n_s beta_s t) * Xs k i' j)
            = ∑ t, (∑ i', Xs k i' j * Xs k i' t) * (beta_s k t - betaBar n_s beta_s t) := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          have g4 : (∑ i', Xs k i' t * (beta_s k t - betaBar n_s beta_s t) * Xs k i' j)
              = ∑ i', Xs k i' j * Xs k i' t * (beta_s k t - betaBar n_s beta_s t) :=
            Finset.sum_congr rfl (fun i' _ => by ring)
          rw [g4, Finset.sum_mul]
        rw [g1, g2, g3]
      exact Finset.sum_congr rfl (fun k _ => e1 k)
    have hD : (∑ k, ∑ i', (∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t)) * Xs k i' j)
        = ∑ t, (∑ k, ∑ i', Xs k i' j * Xs k i' t) * (betaBar n_s beta_s t - beta_init t) := by
      have e1 : ∀ k, (∑ i', (∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t)) * Xs k i' j)
          = ∑ t, (∑ i', Xs k i' j * Xs k i' t) * (betaBar n_s beta_s t - beta_init t) := by
        intro k
        have g1 : (∑ i', (∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t)) * Xs k i' j)
            = ∑ i', ∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t) * Xs k i' j :=
          Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])
        have g2 : (∑ i', ∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t) * Xs k i' j)
            = ∑ t, ∑ i', Xs k i' t * (betaBar n_s beta_s t - beta_init t) * Xs k i' j :=
          Finset.sum_comm
        have g3 : (∑ t, ∑ i', Xs k i' t * (betaBar n_s beta_s t - beta_init t) * Xs k i' j)
            = ∑ t, (∑ i', Xs k i' j * Xs k i' t) * (betaBar n_s beta_s t - beta_init t) := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          have g4 : (∑ i', Xs k i' t * (betaBar n_s beta_s t - beta_init t) * Xs k i' j)
              = ∑ i', Xs k i' j * Xs k i' t * (betaBar n_s beta_s t - beta_init t) :=
            Finset.sum_congr rfl (fun i' _ => by ring)
          rw [g4, Finset.sum_mul]
        rw [g1, g2, g3]
      have e2 : (∑ k, ∑ i', (∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t)) * Xs k i' j)
          = ∑ k, ∑ t, (∑ i', Xs k i' j * Xs k i' t) * (betaBar n_s beta_s t - beta_init t) :=
        Finset.sum_congr rfl (fun k _ => e1 k)
      rw [e2]
      have e3 : (∑ k, ∑ t, (∑ i', Xs k i' j * Xs k i' t) * (betaBar n_s beta_s t - beta_init t))
          = ∑ t, ∑ k, (∑ i', Xs k i' j * Xs k i' t) * (betaBar n_s beta_s t - beta_init t) :=
        Finset.sum_comm
      rw [e3]
      exact Finset.sum_congr rfl (fun t _ => by rw [← Finset.sum_mul])
    have hmulsum : ∀ (f : Fin p → ℝ), (1 / S) * (∑ t, f t) = ∑ t, (1 / S) * f t :=
      fun f => Finset.mul_sum Finset.univ f (1 / S)
    have hX2 : ∀ t : Fin p, (1 / S) * (∑ k, (n_s k : ℝ) * (beta_s k t - betaBar n_s beta_s t)) = 0 := by
      intro t
      have e : (1 / S) * (∑ k, (n_s k : ℝ) * (beta_s k t - betaBar n_s beta_s t))
          = ∑ k, (n_s k : ℝ) / S * (beta_s k t - betaBar n_s beta_s t) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [e, hdelta0 t]
    have hX1 : (∑ k, ∑ t, (n_s k : ℝ) * SigmaX j t * (beta_s k t - betaBar n_s beta_s t))
        = ∑ t, SigmaX j t * (∑ k, (n_s k : ℝ) * (beta_s k t - betaBar n_s beta_s t)) := by
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun t _ => by
        have f : (∑ k, (n_s k : ℝ) * SigmaX j t * (beta_s k t - betaBar n_s beta_s t))
            = ∑ k, SigmaX j t * ((n_s k : ℝ) * (beta_s k t - betaBar n_s beta_s t)) :=
          Finset.sum_congr rfl (fun k _ => by ring)
        rw [f, Finset.mul_sum])
    have hTbeta0 : (1 / S) * (∑ k, ∑ t, (n_s k : ℝ) * SigmaX j t * (beta_s k t - betaBar n_s beta_s t)) = 0 := by
      rw [hX1, hmulsum]
      have e : (∑ t, (1 / S) * (SigmaX j t * (∑ k, (n_s k : ℝ) * (beta_s k t - betaBar n_s beta_s t))))
          = ∑ t, SigmaX j t * ((1 / S) * (∑ k, (n_s k : ℝ) * (beta_s k t - betaBar n_s beta_s t))) :=
        Finset.sum_congr rfl (fun t _ => by ring)
      rw [e]
      refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [hX2 t]
      ring
    have hTbeta : (1 / S) * (∑ k, ∑ t, (∑ i', Xs k i' j * Xs k i' t) * (beta_s k t - betaBar n_s beta_s t))
        = (1 / S) * (∑ k, ∑ t, ((∑ i', Xs k i' j * Xs k i' t) - (n_s k : ℝ) * SigmaX j t)
            * (beta_s k t - betaBar n_s beta_s t))
          + (1 / S) * (∑ k, ∑ t, (n_s k : ℝ) * SigmaX j t * (beta_s k t - betaBar n_s beta_s t)) := by
      have e : (∑ k, ∑ t, (∑ i', Xs k i' j * Xs k i' t) * (beta_s k t - betaBar n_s beta_s t))
          = (∑ k, ∑ t, ((∑ i', Xs k i' j * Xs k i' t) - (n_s k : ℝ) * SigmaX j t)
              * (beta_s k t - betaBar n_s beta_s t))
            + (∑ k, ∑ t, (n_s k : ℝ) * SigmaX j t * (beta_s k t - betaBar n_s beta_s t)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun t _ => by ring)
      rw [e, mul_add]
    have hDsum : (1 / S) * (∑ t, (∑ k, ∑ i', Xs k i' j * Xs k i' t) * (betaBar n_s beta_s t - beta_init t))
        = ∑ t, (1 / S * (∑ k, ∑ i', Xs k i' j * Xs k i' t)) * (betaBar n_s beta_s t - beta_init t) := by
      conv_lhs => rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    calc (1 / S) * (∑ k, ∑ i', (Ys k i' - vdot (Xs k i') beta_init) * Xs k i' j)
        = (1 / S) * ((∑ k, ∑ i', (∑ t, Xs k i' t * (beta_s k t - beta_init t)) * Xs k i' j)
            + (∑ k, ∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
            + (∑ k, ∑ i', eps_s k i' * Xs k i' j)) := by rw [hB0, hsplitB]
      _ = (1 / S) * (∑ k, ∑ i', (∑ t, Xs k i' t * (beta_s k t - beta_init t)) * Xs k i' j)
            + (1 / S) * (∑ k, ∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
            + (1 / S) * (∑ k, ∑ i', eps_s k i' * Xs k i' j) := by ring
      _ = (1 / S) * (∑ k, ∑ i', (∑ t, Xs k i' t * (beta_s k t - betaBar n_s beta_s t)) * Xs k i' j)
              + (1 / S) * (∑ k, ∑ i', (∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t)) * Xs k i' j)
            + (1 / S) * (∑ k, ∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
            + (1 / S) * (∑ k, ∑ i', eps_s k i' * Xs k i' j) := by rw [hcoef]; ring
      _ = (1 / S) * (∑ k, ∑ t, (∑ i', Xs k i' j * Xs k i' t) * (beta_s k t - betaBar n_s beta_s t))
              + (1 / S) * (∑ k, ∑ i', (∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t)) * Xs k i' j)
            + (1 / S) * (∑ k, ∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
            + (1 / S) * (∑ k, ∑ i', eps_s k i' * Xs k i' j) := by rw [hdelta]
      _ = ((1 / S) * (∑ k, ∑ t, ((∑ i', Xs k i' j * Xs k i' t) - (n_s k : ℝ) * SigmaX j t)
                  * (beta_s k t - betaBar n_s beta_s t))
              + (1 / S) * (∑ k, ∑ t, (n_s k : ℝ) * SigmaX j t * (beta_s k t - betaBar n_s beta_s t))
              + (1 / S) * (∑ k, ∑ i', (∑ t, Xs k i' t * (betaBar n_s beta_s t - beta_init t)) * Xs k i' j))
            + (1 / S) * (∑ k, ∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
            + (1 / S) * (∑ k, ∑ i', eps_s k i' * Xs k i' j) := by rw [hTbeta]
      _ = (∑ t, (1 / S * (∑ k, ∑ i', Xs k i' j * Xs k i' t)) * (betaBar n_s beta_s t - beta_init t))
            + (1 / S) * (∑ k, ∑ t, ((∑ i', Xs k i' j * Xs k i' t) - (n_s k : ℝ) * SigmaX j t)
              * (beta_s k t - betaBar n_s beta_s t))
            + (1 / S) * (∑ k, ∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
            + (1 / S) * (∑ k, ∑ i', eps_s k i' * Xs k i' j) := by
        rw [hTbeta0, hD, hDsum]
        ring
  have hcomb :
      (∑ t, (1 / (n_t : ℝ) * (∑ i, Xt i j * Xt i t)) * (betaBar n_s beta_s t - beta_init t))
        - (∑ t, (1 / S * (∑ k, ∑ i', Xs k i' j * Xs k i' t)) * (betaBar n_s beta_s t - beta_init t))
      = ∑ t, ((1 / (n_t : ℝ) * (∑ i, Xt i j * Xt i t))
          - (1 / S * (∑ k, ∑ i', Xs k i' j * Xs k i' t))) * (betaBar n_s beta_s t - beta_init t) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  have hAsAa :
      (1 / (n_t : ℝ)) * (∑ i, (∑ s, Ht i s * phi_t s) * Xt i j)
        - (1 / S) * (∑ k, ∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
      = (∑ s, ((1 / (n_t : ℝ) * (∑ i, Xt i j * Ht i s) - M j s)
            - (1 / S * (∑ k, ∑ i', Xs k i' j * Hs k i' s) - M j s)) * phi_t s)
        - (∑ s, M j s * (phiBar n_s phi_s s - phi_t s))
        - (1 / S) * (∑ k, ∑ s, (∑ i', Xs k i' j * Hs k i' s - (n_s k : ℝ) * M j s)
            * (phi_s k s - phi_t s)) := by
    have hT1 : (1 / (n_t : ℝ)) * (∑ i, (∑ s, Ht i s * phi_t s) * Xt i j)
        = ∑ s, (1 / (n_t : ℝ) * (∑ i, Xt i j * Ht i s)) * phi_t s := by
      have e1 : (∑ i, (∑ s, Ht i s * phi_t s) * Xt i j)
          = ∑ i, ∑ s, Ht i s * phi_t s * Xt i j :=
        Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])
      have e2 : (∑ i, ∑ s, Ht i s * phi_t s * Xt i j)
          = ∑ s, ∑ i, Ht i s * phi_t s * Xt i j := Finset.sum_comm
      have e3 : (∑ s, ∑ i, Ht i s * phi_t s * Xt i j)
          = ∑ s, (∑ i, Xt i j * Ht i s) * phi_t s := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        have e4 : (∑ i, Ht i s * phi_t s * Xt i j) = ∑ i, Xt i j * Ht i s * phi_t s :=
          Finset.sum_congr rfl (fun i _ => by ring)
        rw [e4, Finset.sum_mul]
      rw [e1, e2, e3]
      conv_lhs => rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have hQcomm : ∀ (k : Fin K) (s : Fin q),
        (∑ i', Hs k i' s * Xs k i' j) = (∑ i', Xs k i' j * Hs k i' s) :=
      fun k s => Finset.sum_congr rfl (fun i' _ => by ring)
    have hS1 : (1 / S) * (∑ k, ∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
        = ∑ k, ∑ s, (1 / S * (∑ i', Hs k i' s * Xs k i' j)) * phi_s k s := by
      have e1 : ∀ k, (∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
          = ∑ s, (∑ i', Hs k i' s * Xs k i' j) * phi_s k s := by
        intro k
        have f1 : (∑ i', (∑ s, Hs k i' s * phi_s k s) * Xs k i' j)
            = ∑ i', ∑ s, Hs k i' s * phi_s k s * Xs k i' j :=
          Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])
        have f2 : (∑ i', ∑ s, Hs k i' s * phi_s k s * Xs k i' j)
            = ∑ s, ∑ i', Hs k i' s * phi_s k s * Xs k i' j := Finset.sum_comm
        have f3 : (∑ s, ∑ i', Hs k i' s * phi_s k s * Xs k i' j)
            = ∑ s, (∑ i', Hs k i' s * Xs k i' j) * phi_s k s := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          have f4 : (∑ i', Hs k i' s * phi_s k s * Xs k i' j)
              = ∑ i', Hs k i' s * Xs k i' j * phi_s k s :=
            Finset.sum_congr rfl (fun i' _ => by ring)
          rw [f4, Finset.sum_mul]
        rw [f1, f2, f3]
      conv_lhs => rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [e1 k]
      conv_lhs => rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have hP : ∀ s : Fin q, (∑ k, (1 / S) * (∑ i', Hs k i' s * Xs k i' j))
        = (1 / S) * (∑ k, ∑ i', Xs k i' j * Hs k i' s) := by
      intro s
      have e : (∑ k, (1 / S) * (∑ i', Hs k i' s * Xs k i' j))
          = (1 / S) * ∑ k, (∑ i', Hs k i' s * Xs k i' j) :=
        (Finset.mul_sum Finset.univ (fun k => ∑ i', Hs k i' s * Xs k i' j) (1 / S)).symm
      rw [e]
      congr 1
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i' _ => by ring))
    have hsplit : (∑ k, ∑ s, (1 / S * (∑ i', Hs k i' s * Xs k i' j)) * phi_s k s)
        = (∑ k, ∑ s, (1 / S * (∑ i', Hs k i' s * Xs k i' j)) * phi_t s)
          + (∑ k, ∑ s, (1 / S * (∑ i', Hs k i' s * Xs k i' j)) * (phi_s k s - phi_t s)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have hfirst : (∑ k, ∑ s, (1 / S * (∑ i', Hs k i' s * Xs k i' j)) * phi_t s)
        = ∑ s, (1 / S * (∑ k, ∑ i', Xs k i' j * Hs k i' s)) * phi_t s := by
      have e1 : (∑ k, ∑ s, (1 / S * (∑ i', Hs k i' s * Xs k i' j)) * phi_t s)
          = ∑ s, ∑ k, (1 / S * (∑ i', Hs k i' s * Xs k i' j)) * phi_t s := by
        conv_lhs => rw [Finset.sum_comm]
      rw [e1]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [← Finset.sum_mul, hP s]
    have hdbar : ∀ s : Fin q, (∑ k, (n_s k : ℝ) / S * (phi_s k s - phi_t s))
        = phiBar n_s phi_s s - phi_t s := by
      intro s
      have e1 : (∑ k, (n_s k : ℝ) / S * (phi_s k s - phi_t s))
          = (∑ k, (n_s k : ℝ) / S * phi_s k s) - (∑ k, (n_s k : ℝ) / S * phi_t s) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      have e2 : (∑ k, (n_s k : ℝ) / S * phi_t s) = (∑ k, (n_s k : ℝ) / S) * phi_t s := by
        rw [Finset.sum_mul]
      have e3 : (∑ k, (n_s k : ℝ) / S * phi_s k s) = phiBar n_s phi_s s := by
        simp only [phiBar, sourceWeight, hSdef]
      rw [e1, e2, e3, hsumw]
      ring
    have hsecond : (∑ k, ∑ s, (1 / S * (∑ i', Hs k i' s * Xs k i' j)) * (phi_s k s - phi_t s))
        = (1 / S) * (∑ k, ∑ s, ((∑ i', Xs k i' j * Hs k i' s) - (n_s k : ℝ) * M j s)
            * (phi_s k s - phi_t s))
          + ∑ s, M j s * (phiBar n_s phi_s s - phi_t s) := by
      have e1 : (∑ k, ∑ s, (1 / S * (∑ i', Hs k i' s * Xs k i' j)) * (phi_s k s - phi_t s))
          = (∑ k, ∑ s, ((1 / S) * ((∑ i', Xs k i' j * Hs k i' s) - (n_s k : ℝ) * M j s))
              * (phi_s k s - phi_t s))
            + (∑ k, ∑ s, ((n_s k : ℝ) / S * M j s) * (phi_s k s - phi_t s)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun s _ => by rw [hQcomm k s]; ring)
      have e2 : (∑ k, ∑ s, ((1 / S) * ((∑ i', Xs k i' j * Hs k i' s) - (n_s k : ℝ) * M j s))
              * (phi_s k s - phi_t s))
          = (1 / S) * (∑ k, ∑ s, ((∑ i', Xs k i' j * Hs k i' s) - (n_s k : ℝ) * M j s)
              * (phi_s k s - phi_t s)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun s _ => by ring)
      have e3 : (∑ k, ∑ s, ((n_s k : ℝ) / S * M j s) * (phi_s k s - phi_t s))
          = ∑ s, M j s * (∑ k, (n_s k : ℝ) / S * (phi_s k s - phi_t s)) := by
        conv_lhs => rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun s _ => by
          have f : (∑ k, ((n_s k : ℝ) / S * M j s) * (phi_s k s - phi_t s))
              = ∑ k, M j s * ((n_s k : ℝ) / S * (phi_s k s - phi_t s)) :=
            Finset.sum_congr rfl (fun k _ => by ring)
          rw [f, Finset.mul_sum])
      rw [e1, e2, e3]
      congr 1
      exact Finset.sum_congr rfl (fun s _ => by rw [hdbar s])
    have hcombT : (∑ s, ((1 / (n_t : ℝ) * (∑ i, Xt i j * Ht i s) - M j s)
            - (1 / S * (∑ k, ∑ i', Xs k i' j * Hs k i' s) - M j s)) * phi_t s)
        = (∑ s, (1 / (n_t : ℝ) * (∑ i, Xt i j * Ht i s)) * phi_t s)
          - (∑ s, (1 / S * (∑ k, ∑ i', Xs k i' j * Hs k i' s)) * phi_t s) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [hT1, hS1, hsplit, hfirst, hsecond, hcombT]
    ring
  have hbvec : pooledTrans n_s Xs (fun k irow => Ys k irow - vdot (Xs k irow) beta_init) j
      = (1 / S) * (∑ k, ∑ i', (Ys k i' - vdot (Xs k i') beta_init) * Xs k i' j) := by
    simp only [pooledTrans, vecMatT, hSdef]
  rw [hbvec]
  linear_combination hA - hB + hcomb + hAsAa

  /- @proof-region region.target-node.session.5c7c74de02fddcf2 end -/

end ModelShiftLasso
end

