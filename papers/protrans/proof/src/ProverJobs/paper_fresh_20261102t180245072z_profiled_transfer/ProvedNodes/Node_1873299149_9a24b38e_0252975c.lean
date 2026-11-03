import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Vocabulary
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Base
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.ProvedNodes.Node_3081215765_b752b30e_1d4f57a7
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.ProvedNodes.Node_4155646722_fcf7a31c_ed655e09

namespace PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer


open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer.ModelShiftLasso

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ModelShiftLasso

set_option autoImplicit false in
theorem statopia_math_node_1873299149_9a24b38e : ∀ (p q K n_t : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hK : 1 ≤ K) (hnt : 1 ≤ n_t)
    (n_s : Fin K → ℕ) (hns : ∀ k : Fin K, 1 ≤ n_s k)
    (Xt : Fin n_t → Fin p → ℝ) (Ht : Fin n_t → Fin q → ℝ)
    (Yt : Fin n_t → ℝ) (epsT : Fin n_t → ℝ)
    (Xs : (k : Fin K) → Fin (n_s k) → Fin p → ℝ)
    (Hs : (k : Fin K) → Fin (n_s k) → Fin q → ℝ)
    (Ys : (k : Fin K) → Fin (n_s k) → ℝ)
    (epsS : (k : Fin K) → Fin (n_s k) → ℝ)
    (betaT : Fin p → ℝ) (phiT : Fin q → ℝ) (betaInit : Fin p → ℝ)
    (betaS : Fin K → Fin p → ℝ) (phiS : Fin K → Fin q → ℝ)
    (SigmaX : Fin p → Fin p → ℝ) (M : Fin p → Fin q → ℝ)
    (Zhat : Fin n_t → ℝ)
    (C_x C_delta C_H C_d C_eps C_phi B_phi C_s L_M : ℝ)
    (hC_x : 0 < C_x) (hC_delta : 0 < C_delta) (hC_H : 0 < C_H)
    (hC_d : 0 < C_d) (hC_eps : 0 < C_eps) (hC_phi : 0 < C_phi)
    (hB_phi : 0 < B_phi) (hC_s : 0 < C_s) (hL_M : 0 < L_M)
    (s_delta : ℝ) (hs_delta : 0 ≤ s_delta)
    (lam : ℝ),
    let N : ℕ := ∑ k, n_s k
    let a : ℝ := Real.sqrt (Real.log (p : ℝ) / (n_t : ℝ))
    let a_s : ℝ := Real.sqrt (Real.log (p : ℝ) / (N : ℝ))
    let d : Fin p → ℝ := fun j => betaBar n_s betaS j - betaInit j
    let deltaK : Fin K → Fin p → ℝ := fun k j => betaS k j - betaBar n_s betaS j
    let dk : Fin K → Fin q → ℝ := fun k s => phiS k s - phiT s
    let dbar : Fin q → ℝ := fun s => phiBar n_s phiS s - phiT s
    let Gt : Fin p → Fin p → ℝ := fun j t => (1 / (n_t : ℝ)) * ∑ i, Xt i j * Xt i t
    let Gs : Fin p → Fin p → ℝ :=
      fun j t => (1 / (N : ℝ)) * ∑ k, ∑ i, Xs k i j * Xs k i t
    let Tbeta : Fin p → ℝ := fun j => (1 / (N : ℝ)) *
      ∑ k, ∑ t, ((∑ i, Xs k i j * Xs k i t) - (n_s k : ℝ) * SigmaX j t) * deltaK k t
    let Dt : Fin p → Fin q → ℝ :=
      fun j s => (1 / (n_t : ℝ)) * (∑ i, Xt i j * Ht i s) - M j s
    let Ds : Fin p → Fin q → ℝ :=
      fun j s => (1 / (N : ℝ)) * (∑ k, ∑ i, Xs k i j * Hs k i s) - M j s
    let Tphi : Fin p → ℝ := fun j => (1 / (N : ℝ)) *
      ∑ k, ∑ s, ((∑ i, Xs k i j * Hs k i s) - (n_s k : ℝ) * M j s) * dk k s
    let e_t : Fin p → ℝ := fun j => (1 / (n_t : ℝ)) * ∑ i, epsT i * Xt i j
    let es : Fin p → ℝ := fun j => (1 / (N : ℝ)) * ∑ k, ∑ i, epsS k i * Xs k i j
    let bvec : Fin p → ℝ :=
      pooledTrans n_s Xs (fun k i => Ys k i - vdot (Xs k i) betaInit)
    let Z0 : Fin n_t → ℝ := fun i => vdot (Xt i) d + vdot (Ht i) phiT
    let Delta : Fin p → ℝ := fun j => (1 / (n_t : ℝ)) * (∑ i, Z0 i * Xt i j) - bvec j
    let B_0 : ℝ := 2 * C_x * C_s + C_delta * s_delta + C_d * B_phi * Real.sqrt (q : ℝ) +
      L_M * C_phi * Real.sqrt (q : ℝ) + C_eps
    let C_1 : ℝ := 8 * C_H
    let C_2 : ℝ := 2 * B_0 + C_eps
    let r : Fin n_t → ℝ := fun i =>
      Yt i - vdot (Xt i) betaInit - Zhat i - vdot (Xt i) (etaZero n_s betaT betaS)
    let c : Fin p → ℝ := fun j => (1 / (n_t : ℝ)) * ∑ i, r i * Xt i j
    
    (∀ i, Yt i = vdot (Xt i) betaT + vdot (Ht i) phiT + epsT i) →
    
    (∀ (k : Fin K) (i : Fin (n_s k)),
      Ys k i = vdot (Xs k i) (betaS k) + vdot (Hs k i) (phiS k) + epsS k i) →
    
    (∀ j t, |Gt j t - SigmaX j t| ≤ C_x * a) →
    
    (∀ j t, |Gs j t - SigmaX j t| ≤ C_x * a_s) →
    
    (∀ j, |Tbeta j| ≤ C_delta * s_delta * a_s) →
    
    (∀ j, Real.sqrt (∑ s, (Dt j s) ^ 2) ≤ 2 * C_H * Real.sqrt (q : ℝ) * a) →
    
    (∀ j, Real.sqrt (∑ s, (Ds j s) ^ 2) ≤ 2 * C_H * Real.sqrt (q : ℝ) * a_s) →
    
    (∀ j, |Tphi j| ≤ C_d * B_phi * Real.sqrt (q : ℝ) * a_s) →
    
    (∀ j, Real.sqrt (∑ s, (M j s) ^ 2) ≤ L_M * Real.sqrt (q : ℝ)) →
    
    Real.sqrt (∑ s, (dbar s) ^ 2) ≤ C_phi * a →
    
    (∀ j, |e_t j| ≤ C_eps * a) →
    
    (∀ j, |es j| ≤ C_eps * a_s) →
    
    (∑ j, |d j| ≤ C_s) →
    
    a_s ≤ a →
    
    (∀ z : Fin n_t → ℝ, profileObj Xt bvec Zhat ≤ profileObj Xt bvec z) →
    
    4 * (C_1 * Real.sqrt (q : ℝ) * Real.sqrt (∑ s, (phiT s) ^ 2) + C_2) * a ≤ lam →
    
    maxAbs c ≤ lam / 4 := by
  /- @proof-region region.target-node.session.fb8912edc5fd7db1 begin -/
  intro p q K n_t hp hq hK hn_t n_s hn_s Xt Ht Yt eps_t Xs Hs Ys eps_s beta_t phi_t beta_init beta_s phi_s SigmaX M Zhat
  intro Cx Cdelta CH Cd Ceps Cphi Bphi Cs LM
  intro hCx hCdelta hCH hCd hCeps hCphi hBphi hCs hLM
  intro s_delta hsdelta lam
  intro N a a_s d delta_k dk dbar Gt Gs Tbeta Dt Ds Tphi et es bvec Z0 Delta B0 C1 C2 r c
  let eta0 : Fin p → ℝ := etaZero n_s beta_t beta_s
  intro hYt hYs hGramT hGramS hSpread hCrossT hCrossS hTransfer hPop hSim hNoiseT hNoiseS hInit hRegime hProfile hTune
  haveI : NeZero p := ⟨by omega⟩
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have has : 0 ≤ a_s := Real.sqrt_nonneg _
  have hB0eq : B0 = 2 * Cx * Cs + Cdelta * s_delta + Cd * Bphi * Real.sqrt (q : ℝ) + LM * Cphi * Real.sqrt (q : ℝ) + Ceps := rfl
  have hC1eq : C1 = 8 * CH := rfl
  have hC2eq : C2 = 2 * B0 + Ceps := rfl
  have abs_sub_le_add : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := by
    intro x y
    have h := abs_add_le x (-y)
    simpa using h
  have abs_add4 : ∀ b₁ b₂ b₃ b₄ : ℝ, |b₁ + b₂ + b₃ + b₄| ≤ |b₁| + |b₂| + |b₃| + |b₄| := by
    intro b₁ b₂ b₃ b₄
    have h1 := abs_add_le (b₁ + b₂ + b₃) b₄
    have h2 := abs_add_le (b₁ + b₂) b₃
    have h3 := abs_add_le b₁ b₂
    linarith
  have maxAbs_le_of : ∀ {n : ℕ} [NeZero n] (v : Fin n → ℝ) (c : ℝ), (∀ i, |v i| ≤ c) → maxAbs v ≤ c := by
    intro n hnz v c hv
    haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hnz.out⟩⟩
    have hbdd : BddAbove (Set.range (fun i : Fin n => |v i|)) := Finite.bddAbove_range _
    have hle : (⨆ i : Fin n, |v i|) ≤ c := (ciSup_le_iff hbdd).mpr hv
    exact hle
  have le_maxAbs : ∀ {n : ℕ} (v : Fin n → ℝ) (i : Fin n), |v i| ≤ maxAbs v := by
    intro n v i
    have hbdd : BddAbove (Set.range (fun k : Fin n => |v k|)) := Finite.bddAbove_range _
    have hmem : |v i| ∈ Set.range (fun k : Fin n => |v k|) := Set.mem_range.mpr ⟨i, rfl⟩
    first
      | exact le_csSup hbdd hmem
      | exact le_ciSup hbdd i
  have maxAbs_neg : ∀ {n : ℕ} (v : Fin n → ℝ), maxAbs (fun i => -v i) = maxAbs v := by
    intro n v
    simp only [maxAbs, abs_neg]
  have hDelta_decomp : ∀ j : Fin p, Delta j = (∑ t : Fin p, (Gt j t - Gs j t) * d t) - Tbeta j + (∑ s : Fin q, (Dt j s - Ds j s) * phi_t s) - (∑ s : Fin q, M j s * dbar s) - Tphi j - es j := by
    intro j
    exact statopia_math_node_4155646722_fcf7a31c p q K n_t hp hq hK hn_t n_s hn_s Xt Ht Xs Hs eps_s Ys beta_init phi_t beta_s phi_s SigmaX M hYs j
  have hsqa : ∀ x : ℝ, |x| ^ 2 = x ^ 2 := by
    intro x
    rw [pow_two, pow_two, ← abs_mul, abs_of_nonneg (mul_self_nonneg x)]
  have hB1 : ∀ j : Fin p, |∑ t : Fin p, (Gt j t - Gs j t) * d t| ≤ 2 * Cx * Cs * a := by
    intro j
    have hkey : ∀ t : Fin p, |Gt j t - Gs j t| ≤ Cx * a + Cx * a_s := by
      intro t
      have htri := abs_sub_le_add (Gt j t - SigmaX j t) (Gs j t - SigmaX j t)
      have hsub : Gt j t - Gs j t = (Gt j t - SigmaX j t) - (Gs j t - SigmaX j t) := by ring
      rw [hsub]
      linarith [htri, hGramT j t, hGramS j t]
    have hfac : 0 ≤ Cx * a + Cx * a_s := by
      have h1 : 0 ≤ Cx * a := mul_nonneg hCx.le ha
      have h2 : 0 ≤ Cx * a_s := mul_nonneg hCx.le has
      linarith
    calc |∑ t : Fin p, (Gt j t - Gs j t) * d t|
        ≤ ∑ t : Fin p, |Gt j t - Gs j t| * |d t| := by
          have h := Finset.abs_sum_le_sum_abs (fun t : Fin p => (Gt j t - Gs j t) * d t) Finset.univ
          simpa only [abs_mul] using h
      _ ≤ ∑ t : Fin p, (Cx * a + Cx * a_s) * |d t| := by
          refine Finset.sum_le_sum ?_
          intro t _
          exact mul_le_mul_of_nonneg_right (hkey t) (abs_nonneg _)
      _ = (Cx * a + Cx * a_s) * ∑ t : Fin p, |d t| := by
          rw [Finset.mul_sum]
      _ ≤ (Cx * a + Cx * a_s) * Cs := mul_le_mul_of_nonneg_left hInit hfac
      _ ≤ 2 * Cx * Cs * a := by
          have hCxCs : 0 < Cx * Cs := mul_pos hCx hCs
          calc (Cx * a + Cx * a_s) * Cs = Cx * Cs * a + Cx * Cs * a_s := by ring
            _ ≤ Cx * Cs * a + Cx * Cs * a := by
              have h := mul_le_mul_of_nonneg_left hRegime hCxCs.le
              linarith [h]
            _ = 2 * Cx * Cs * a := by ring
  have hB2 : ∀ j : Fin p, |Tbeta j| ≤ Cdelta * s_delta * a := by
    intro j
    have h0 : 0 ≤ Cdelta * s_delta := mul_nonneg hCdelta.le hsdelta
    calc |Tbeta j| ≤ Cdelta * s_delta * a_s := hSpread j
      _ ≤ Cdelta * s_delta * a := mul_le_mul_of_nonneg_left hRegime h0
  have hB3 : ∀ j : Fin p, |∑ s : Fin q, (Dt j s - Ds j s) * phi_t s| ≤
      4 * CH * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) * a := by
    intro j
    have h1 : |∑ s : Fin q, (Dt j s - Ds j s) * phi_t s| ≤ ∑ s : Fin q, |Dt j s - Ds j s| * |phi_t s| := by
      have h := Finset.abs_sum_le_sum_abs (fun s : Fin q => (Dt j s - Ds j s) * phi_t s) Finset.univ
      simpa only [abs_mul] using h
    have h2 : ∑ s : Fin q, |Dt j s - Ds j s| * |phi_t s| ≤ ∑ s : Fin q, (|Dt j s| + |Ds j s|) * |phi_t s| := by
      refine Finset.sum_le_sum ?_
      intro s _
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have h := abs_sub_le_add (Dt j s) (Ds j s)
      linarith
    have h3 : ∑ s : Fin q, (|Dt j s| + |Ds j s|) * |phi_t s| =
        ∑ s : Fin q, |Dt j s| * |phi_t s| + ∑ s : Fin q, |Ds j s| * |phi_t s| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro s _
      ring
    have h4 : ∑ s : Fin q, |Dt j s| * |phi_t s| ≤
        Real.sqrt (∑ s : Fin q, (Dt j s) ^ 2) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin q)) (fun s => |Dt j s|) (fun s => |phi_t s|)
      simpa only [hsqa] using h
    have h5 : ∑ s : Fin q, |Ds j s| * |phi_t s| ≤
        Real.sqrt (∑ s : Fin q, (Ds j s) ^ 2) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin q)) (fun s => |Ds j s|) (fun s => |phi_t s|)
      simpa only [hsqa] using h
    have hP : 0 ≤ Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) := Real.sqrt_nonneg _
    have hCHq : 0 ≤ 2 * CH * Real.sqrt (q : ℝ) := by
      have h1' : 0 ≤ 2 * CH := by linarith
      exact mul_nonneg h1' (Real.sqrt_nonneg _)
    have e1 : Real.sqrt (∑ s : Fin q, (Dt j s) ^ 2) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) ≤
        (2 * CH * Real.sqrt (q : ℝ) * a) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) :=
      mul_le_mul_of_nonneg_right (hCrossT j) hP
    have e2 : Real.sqrt (∑ s : Fin q, (Ds j s) ^ 2) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) ≤
        (2 * CH * Real.sqrt (q : ℝ) * a_s) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) :=
      mul_le_mul_of_nonneg_right (hCrossS j) hP
    have e3 : (2 * CH * Real.sqrt (q : ℝ) * a_s) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) ≤
        (2 * CH * Real.sqrt (q : ℝ) * a) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRegime hCHq) hP
    have e4 : 2 * ((2 * CH * Real.sqrt (q : ℝ) * a) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2)) =
        4 * CH * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) * a := by ring
    calc |∑ s : Fin q, (Dt j s - Ds j s) * phi_t s| ≤ ∑ s : Fin q, |Dt j s - Ds j s| * |phi_t s| := h1
      _ ≤ ∑ s : Fin q, (|Dt j s| + |Ds j s|) * |phi_t s| := h2
      _ = ∑ s : Fin q, |Dt j s| * |phi_t s| + ∑ s : Fin q, |Ds j s| * |phi_t s| := h3
      _ ≤ Real.sqrt (∑ s : Fin q, (Dt j s) ^ 2) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) +
          Real.sqrt (∑ s : Fin q, (Ds j s) ^ 2) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) := by
          linarith [h4, h5]
      _ ≤ 4 * CH * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) * a := by
          rw [← e4]
          linarith [e1, e2, e3]
  have hB4 : ∀ j : Fin p, |∑ s : Fin q, M j s * dbar s| ≤ LM * Cphi * Real.sqrt (q : ℝ) * a := by
    intro j
    have h1 : |∑ s : Fin q, M j s * dbar s| ≤
        Real.sqrt (∑ s : Fin q, (M j s) ^ 2) * Real.sqrt (∑ s : Fin q, (dbar s) ^ 2) := by
      have h := Finset.abs_sum_le_sum_abs (fun s : Fin q => M j s * dbar s) Finset.univ
      have h1' : ∑ s : Fin q, |M j s * dbar s| = ∑ s : Fin q, |M j s| * |dbar s| := by
        refine Finset.sum_congr rfl ?_
        intro s _
        rw [abs_mul]
      have h2' : ∑ s : Fin q, |M j s| * |dbar s| ≤
          Real.sqrt (∑ s : Fin q, (M j s) ^ 2) * Real.sqrt (∑ s : Fin q, (dbar s) ^ 2) := by
        have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin q)) (fun s => |M j s|) (fun s => |dbar s|)
        simpa only [hsqa] using h
      linarith
    have hq : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
    have h2 : Real.sqrt (∑ s : Fin q, (M j s) ^ 2) * Real.sqrt (∑ s : Fin q, (dbar s) ^ 2) ≤
        (LM * Real.sqrt (q : ℝ)) * (Cphi * a) :=
      mul_le_mul (hPop j) hSim (Real.sqrt_nonneg _) (mul_nonneg hLM.le hq)
    have e5 : (LM * Real.sqrt (q : ℝ)) * (Cphi * a) = LM * Cphi * Real.sqrt (q : ℝ) * a := by ring
    linarith [h1, h2, e5]
  have hB5 : ∀ j : Fin p, |Tphi j| ≤ Cd * Bphi * Real.sqrt (q : ℝ) * a := by
    intro j
    have h0 : 0 ≤ Cd * Bphi * Real.sqrt (q : ℝ) :=
      mul_nonneg (mul_nonneg hCd.le hBphi.le) (Real.sqrt_nonneg _)
    have e6 : Cd * Bphi * Real.sqrt (q : ℝ) * a_s ≤ Cd * Bphi * Real.sqrt (q : ℝ) * a :=
      mul_le_mul_of_nonneg_left hRegime h0
    linarith [hTransfer j, e6]
  have hB6 : ∀ j : Fin p, |es j| ≤ Ceps * a := by
    intro j
    have e7 : Ceps * a_s ≤ Ceps * a := mul_le_mul_of_nonneg_left hRegime hCeps.le
    linarith [hNoiseS j, e7]
  have hDeltaBound : ∀ j : Fin p, |Delta j| ≤
      (4 * CH * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) + B0) * a := by
    intro j
    have hdec := hDelta_decomp j
    have hAB := abs_sub_le_add
      ((∑ t : Fin p, (Gt j t - Gs j t) * d t) + (∑ s : Fin q, (Dt j s - Ds j s) * phi_t s))
      (Tbeta j + (∑ s : Fin q, M j s * dbar s) + Tphi j + es j)
    have hAB2 := abs_add_le (∑ t : Fin p, (Gt j t - Gs j t) * d t) (∑ s : Fin q, (Dt j s - Ds j s) * phi_t s)
    have hQ := abs_add4 (Tbeta j) (∑ s : Fin q, M j s * dbar s) (Tphi j) (es j)
    have hrew : Delta j =
        ((∑ t : Fin p, (Gt j t - Gs j t) * d t) + (∑ s : Fin q, (Dt j s - Ds j s) * phi_t s)) -
          (Tbeta j + (∑ s : Fin q, M j s * dbar s) + Tphi j + es j) := by
      rw [hdec]
      ring
    rw [hrew]
    have hdist : (4 * CH * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) + B0) * a =
        4 * CH * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) * a + 2 * Cx * Cs * a +
          Cdelta * s_delta * a + Cd * Bphi * Real.sqrt (q : ℝ) * a + LM * Cphi * Real.sqrt (q : ℝ) * a +
            Ceps * a := by
      rw [hB0eq]
      ring
    rw [hdist]
    linarith [hAB, hAB2, hQ, hB1 j, hB2 j, hB3 j, hB4 j, hB5 j, hB6 j]
  have hMaxDelta : maxAbs (fun j : Fin p => Delta j) ≤
      (4 * CH * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) + B0) * a :=
    maxAbs_le_of (fun j : Fin p => Delta j) _ (fun j => hDeltaBound j)
  have hProfileZ : maxAbs (fun j : Fin p => (1 / (n_t : ℝ)) * vecMatT Zhat Xt j - bvec j) ≤
      maxAbs (fun j : Fin p => Delta j) := by
    have h := hProfile Z0
    have hZ0 : maxAbs (fun j : Fin p => (1 / (n_t : ℝ)) * vecMatT Z0 Xt j - bvec j) =
        maxAbs (fun j : Fin p => Delta j) := rfl
    exact le_trans h (le_of_eq hZ0)
  have hProfNeg : maxAbs (fun j : Fin p => bvec j - (1 / (n_t : ℝ)) * vecMatT Zhat Xt j) ≤
      maxAbs (fun j : Fin p => Delta j) := by
    have heq : (fun j : Fin p => bvec j - (1 / (n_t : ℝ)) * vecMatT Zhat Xt j) =
        (fun j : Fin p => -((1 / (n_t : ℝ)) * vecMatT Zhat Xt j - bvec j)) := by
      funext j
      ring
    rw [heq, maxAbs_neg]
    exact hProfileZ
  have hkey_eq : ∀ i : Fin n_t,
      Yt i - vdot (Xt i) beta_init - Zhat i - vdot (Xt i) eta0 = Z0 i - Zhat i + eps_t i := by
    intro i
    have hv3 : ∀ (u a1 a2 a3 : Fin p → ℝ),
        vdot u (fun j => a1 j - a2 j - a3 j) = vdot u a1 - vdot u a2 - vdot u a3 := by
      intro u a1 a2 a3
      simp only [vdot, mul_sub, Finset.sum_sub_distrib]
    have hd : (fun j : Fin p => beta_t j - beta_init j - eta0 j) = d := by
      funext j
      have h1 : eta0 j = beta_t j - betaBar n_s beta_s j := rfl
      have h2 : d j = betaBar n_s beta_s j - beta_init j := rfl
      rw [h1, h2]
      ring
    have hv : vdot (Xt i) beta_t - vdot (Xt i) beta_init - vdot (Xt i) eta0 = vdot (Xt i) d := by
      have h := hv3 (Xt i) beta_t beta_init eta0
      rw [hd] at h
      exact h.symm
    have hZ0i : Z0 i = vdot (Xt i) d + vdot (Ht i) phi_t := rfl
    rw [hZ0i, hYt i]
    linarith [hv]
  have hc_eq : ∀ j : Fin p,
      (1 / (n_t : ℝ)) * ∑ i : Fin n_t, (Yt i - vdot (Xt i) beta_init - Zhat i - vdot (Xt i) eta0) * Xt i j =
        Delta j + (bvec j - (1 / (n_t : ℝ)) * vecMatT Zhat Xt j) + et j := by
    intro j
    have h1 : ∑ i : Fin n_t, (Yt i - vdot (Xt i) beta_init - Zhat i - vdot (Xt i) eta0) * Xt i j =
        ∑ i : Fin n_t, (Z0 i - Zhat i + eps_t i) * Xt i j := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hkey_eq i]
    have h2 : ∑ i : Fin n_t, (Z0 i - Zhat i + eps_t i) * Xt i j =
        (∑ i : Fin n_t, Z0 i * Xt i j) - (∑ i : Fin n_t, Zhat i * Xt i j) +
          (∑ i : Fin n_t, eps_t i * Xt i j) := by
      have hs : ∀ i : Fin n_t, (Z0 i - Zhat i + eps_t i) * Xt i j =
          (Z0 i * Xt i j - Zhat i * Xt i j) + eps_t i * Xt i j := by
        intro i
        ring
      simp only [hs, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hD : Delta j = (1 / (n_t : ℝ)) * (∑ i : Fin n_t, Z0 i * Xt i j) - bvec j := rfl
    have hV : vecMatT Zhat Xt j = ∑ i : Fin n_t, Zhat i * Xt i j := rfl
    have hE : et j = (1 / (n_t : ℝ)) * (∑ i : Fin n_t, eps_t i * Xt i j) := rfl
    rw [h1, h2, hD, hV, hE]
    ring
  have hc_bound : ∀ j : Fin p,
      |(1 / (n_t : ℝ)) * ∑ i : Fin n_t, (Yt i - vdot (Xt i) beta_init - Zhat i - vdot (Xt i) eta0) * Xt i j| ≤
        (C1 * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) + C2) * a := by
    intro j
    rw [hc_eq j]
    have hm : |bvec j - (1 / (n_t : ℝ)) * vecMatT Zhat Xt j| ≤
        (4 * CH * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) + B0) * a :=
      le_trans (le_maxAbs (fun j : Fin p => bvec j - (1 / (n_t : ℝ)) * vecMatT Zhat Xt j) j)
        (le_trans hProfNeg hMaxDelta)
    have t1 := abs_add_le (Delta j + (bvec j - (1 / (n_t : ℝ)) * vecMatT Zhat Xt j)) (et j)
    have t2 := abs_add_le (Delta j) (bvec j - (1 / (n_t : ℝ)) * vecMatT Zhat Xt j)
    have hmain : |Delta j + (bvec j - (1 / (n_t : ℝ)) * vecMatT Zhat Xt j) + et j| ≤
        2 * ((4 * CH * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) + B0) * a) + Ceps * a := by
      linarith [t1, t2, hDeltaBound j, hm, hNoiseT j]
    have harith : 2 * ((4 * CH * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) + B0) * a) +
        Ceps * a = (C1 * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) + C2) * a := by
      rw [hC2eq, hC1eq, hB0eq]
      ring
    linarith [hmain, harith]
  have hMaxC : maxAbs (fun j : Fin p => (1 / (n_t : ℝ)) *
      ∑ i : Fin n_t, (Yt i - vdot (Xt i) beta_init - Zhat i - vdot (Xt i) eta0) * Xt i j) ≤
      (C1 * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) + C2) * a :=
    maxAbs_le_of (fun j : Fin p => (1 / (n_t : ℝ)) *
      ∑ i : Fin n_t, (Yt i - vdot (Xt i) beta_init - Zhat i - vdot (Xt i) eta0) * Xt i j) _
      (fun j => hc_bound j)
  have hFinal : (C1 * Real.sqrt (q : ℝ) * Real.sqrt (∑ s : Fin q, (phi_t s) ^ 2) + C2) * a ≤ lam / 4 := by
    linarith [hTune]
  exact le_trans hMaxC hFinal
  /- @proof-region region.target-node.session.fb8912edc5fd7db1 end -/

end ModelShiftLasso
end

