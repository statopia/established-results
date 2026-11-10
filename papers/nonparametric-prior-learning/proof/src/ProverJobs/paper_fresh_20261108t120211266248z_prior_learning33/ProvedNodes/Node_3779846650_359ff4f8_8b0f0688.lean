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
theorem statopia_math_node_3779846650_359ff4f8 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (t : ℝ) (ht : 0 ≤ t)
    (u : U) (hu : UScaleNorm e lam t u < ⊤)
    (ε : ℝ) (hε : 0 < ε),
    ∃ s : Finset (ℕ × ℚ),
      UScaleNorm e lam t (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1) < ⊤ ∧
      UScaleDist e lam t u (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1) < ENNReal.ofReal ε := by
  /- @proof-region region.target-node.session.f7ffac6ba713667d begin -/
  intro U _ _ e lam hlam_pos hlam_anti t ht u hu ε hε
  set w : ℕ → ℝ := fun k => Real.rpow (lam k) (-t) with hw
  set c : ℕ → ℝ := fun k => inner ℝ (e k) u with hc
  have hwpos : ∀ k, 0 < w k := fun k => by
    simp only [hw]
    exact Real.rpow_pos_of_pos (hlam_pos k) _
  have hwnn : ∀ k, 0 ≤ w k := fun k => (hwpos k).le
  set f : ℕ → ℝ := fun k => w k * c k ^ 2 with hf
  have hfnn : ∀ k, 0 ≤ f k := fun k => by
    simp only [hf]
    exact mul_nonneg (hwnn k) (sq_nonneg _)
  have huE : (∑' k, ENNReal.ofReal (f k)) < ⊤ := by
    simp only [UScaleNorm] at hu
    simpa only [hf, hw, hc] using hu
  have hne : (∑' k, ENNReal.ofReal (f k)) ≠ ⊤ := ne_of_lt huE
  have hsummable : Summable f := by
    have h := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal (f k)) hne
    simpa only [ENNReal.toReal_ofReal (hfnn _)] using h
  have hT : (∑' k, ENNReal.ofReal (f k)).toReal = ∑' k, f k := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hfnn hsummable,
      ENNReal.toReal_ofReal (tsum_nonneg hfnn)]
  set A : ℝ := (ε / 2) ^ 2 with hA
  have hApos : 0 < A := by
    rw [hA]; positivity
  have hN_exists : ∃ N : ℕ, 1 ≤ N ∧ ∑' k, f k - A / 2 < ∑ k ∈ Finset.range N, f k := by
    have hlim : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, f k) atTop (𝓝 (∑' k, f k)) :=
      hsummable.hasSum.tendsto_sum_nat
    have hmem : ∀ᶠ n : ℕ in atTop, ∑' k, f k - A / 2 < ∑ k ∈ Finset.range n, f k :=
      hlim.eventually (show Set.Ioi (∑' k, f k - A / 2) ∈ 𝓝 (∑' k, f k) from
        IsOpen.mem_nhds isOpen_Ioi (show ∑' k, f k - A / 2 < ∑' k, f k by linarith))
    obtain ⟨N, hN⟩ := hmem.exists
    have hmono : ∑ k ∈ Finset.range N, f k ≤ ∑ k ∈ Finset.range (max N 1), f k :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (le_max_left N 1)) (fun i _ _ => hfnn i)
    exact ⟨max N 1, le_max_right N 1, lt_of_lt_of_le hN hmono⟩
  obtain ⟨N, hN1, hN2⟩ := hN_exists
  set F : Finset ℕ := Finset.range N with hF
  have hshift : Summable (fun i : ℕ => f (i + N)) :=
    (summable_nat_add_iff N).mpr hsummable
  have htail_real : (∑' i : ℕ, f (i + N)) < A / 2 := by
    have h := hsummable.sum_add_tsum_nat_add N
    linarith
  have htail : (∑' i : ℕ, ENNReal.ofReal (f (i + N))) < ENNReal.ofReal (A / 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hfnn (i + N)) hshift,
      ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    exact htail_real
  set W : ℝ := ∑ k ∈ F, w k with hW
  have hWpos : 0 < W := by
    rw [hW]
    refine Finset.sum_pos (fun i _ => hwpos i) ⟨0, ?_⟩
    rw [hF]
    exact Finset.mem_range.mpr (by omega)
  set δ : ℝ := min 1 (A / (4 * (W + 1))) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min one_pos (by positivity)
  have hδle1 : δ ≤ 1 := by rw [hδ]; exact min_le_left _ _
  have hδle : δ ≤ A / (4 * (W + 1)) := by rw [hδ]; exact min_le_right _ _
  have hδ2 : W * δ ^ 2 ≤ A / 4 := by
    have hs : δ ^ 2 ≤ δ := by nlinarith
    have hW1 : (0:ℝ) < W + 1 := by linarith
    have hstep1 : W * δ ^ 2 ≤ W * δ := mul_le_mul_of_nonneg_left hs hWpos.le
    have hstep2 : W * δ ≤ (W + 1) * δ := by nlinarith
    have hstep3 : (W + 1) * δ ≤ (W + 1) * (A / (4 * (W + 1))) :=
      mul_le_mul_of_nonneg_left hδle hW1.le
    have h4 : (W + 1) * (A / (4 * (W + 1))) = A / 4 := by field_simp
    linarith
  have hrat : ∀ k : ℕ, ∃ q : ℚ, w k * (c k - (q : ℝ)) ^ 2 < w k * δ ^ 2 := by
    intro k
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show c k - δ < c k + δ by linarith)
    refine ⟨r, ?_⟩
    have e1 : -(c k - (r:ℝ)) < δ := by linarith
    have h3 : 0 < (δ - (c k - (r:ℝ))) * (δ + (c k - (r:ℝ))) :=
      mul_pos (by linarith) (by linarith)
    have h4 : (c k - (r:ℝ)) ^ 2 < δ ^ 2 := by nlinarith [h3]
    exact mul_lt_mul_of_pos_left h4 (hwpos k)
  choose q hq using hrat
  have hfinreal : ∑ k ∈ F, w k * (c k - (q k : ℝ)) ^ 2 < A / 2 := by
    have h2 : ∑ k ∈ F, w k * (c k - (q k : ℝ)) ^ 2 ≤ ∑ k ∈ F, w k * δ ^ 2 :=
      Finset.sum_le_sum (fun k _ => (hq k).le)
    have h3 : ∑ k ∈ F, w k * δ ^ 2 = W * δ ^ 2 := by
      rw [hW, Finset.sum_mul]
    linarith
  set qq : ℕ → ℝ := fun k => if k ∈ F then (q k : ℝ) else 0 with hqq
  have hqq_notF : ∀ k, k ∉ F → qq k = 0 := by
    intro k hk
    simp only [hqq]
    simp [hk]
  set s : Finset (ℕ × ℚ) := F.image (fun k => (k, q k)) with hs
  set d : U := ∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1 with hd
  have hd_eq : d = ∑ k ∈ F, (q k : ℝ) • e k := by
    rw [hd, hs, Finset.sum_image]
    simp
  have horth : ∀ i j : ℕ, inner ℝ (e i) (e j) = if i = j then (1:ℝ) else 0 :=
    fun i j => orthonormal_iff_ite.mp e.orthonormal i j
  have hcoord : ∀ k : ℕ, inner ℝ (e k) d = if k ∈ F then (q k : ℝ) else 0 := by
    intro k
    rw [hd_eq, inner_sum]
    have hterm : ∀ i : ℕ, inner ℝ (e k) ((q i : ℝ) • e i) = if i = k then (q i : ℝ) else 0 := by
      intro i
      rw [real_inner_smul_right, horth k i]
      by_cases h : k = i
      · subst h
        simp
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
        simp
    calc ∑ i ∈ F, inner ℝ (e k) ((q i : ℝ) • e i)
        = ∑ i ∈ F, (if i = k then (q i : ℝ) else 0) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = if k ∈ F then (q k : ℝ) else 0 := by
          by_cases hk : k ∈ F
          · rw [if_pos hk]
            rw [Finset.sum_eq_single (s := F) (f := fun i => if i = k then (q i : ℝ) else 0) k
              (fun i _ hik => by simp [hik]) (fun hk' => absurd hk hk')]
            simp
          · rw [if_neg hk]
            refine Finset.sum_eq_zero (fun i hi => ?_)
            have hik : i ≠ k := fun h' => hk (h' ▸ hi)
            simp [hik]
  set G : ℕ → ℝ := fun k => w k * (c k - qq k) ^ 2 with hG
  have hGnn : ∀ k, 0 ≤ G k := fun k => by
    simp only [hG]
    exact mul_nonneg (hwnn k) (sq_nonneg _)
  have hGshift : ∀ i : ℕ, G (i + N) = f (i + N) := by
    intro i
    have hnot : (i + N) ∉ F := by
      rw [hF]
      simp only [Finset.mem_range]
      omega
    simp only [hG, hf]
    rw [hqq_notF (i + N) hnot]
    ring
  have hGs : Summable G := by
    refine (summable_nat_add_iff N).mp ?_
    have hz : (fun i : ℕ => G (i + N)) = fun i : ℕ => f (i + N) := funext hGshift
    rw [hz]
    exact hshift
  have hGsplit : (∑' k, G k) = ∑ k ∈ F, G k + ∑' i, G (i + N) := by
    rw [hF]
    exact (hGs.sum_add_tsum_nat_add N).symm
  have hGfin : ∑ k ∈ F, G k < A / 2 := by
    have h1 : ∑ k ∈ F, G k = ∑ k ∈ F, w k * (c k - (q k : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : qq k = (q k : ℝ) := by
        simp only [hqq]
        simp [hk]
      simp only [hG, hk']
    rw [h1]
    exact hfinreal
  have hGtail : (∑' i, G (i + N)) < A / 2 := by
    have h1 : (∑' i, G (i + N)) = ∑' i, f (i + N) := tsum_congr hGshift
    rw [h1]
    exact htail_real
  have hsum_lt : (∑' k, G k) < A := by
    rw [hGsplit]
    linarith
  have hnorm_eq : UScaleNorm e lam t (u - d) = ∑' k, ENNReal.ofReal (G k) := by
    have h1 : UScaleNorm e lam t (u - d)
        = ∑' k, ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) (u - d)) ^ 2) := rfl
    rw [h1]
    refine tsum_congr (fun k => ?_)
    rw [inner_sub_right, hcoord k]
  have hmain : UScaleNorm e lam t (u - d) < ENNReal.ofReal A := by
    rw [hnorm_eq, ← ENNReal.ofReal_tsum_of_nonneg hGnn hGs]
    exact (ENNReal.ofReal_lt_ofReal_iff hApos).mpr hsum_lt
  have hqqs : Summable (fun k => w k * qq k ^ 2) := by
    refine (summable_nat_add_iff N).mp ?_
    have hz : (fun i : ℕ => w (i + N) * qq (i + N) ^ 2) = fun _ => 0 := by
      funext i
      have hnot : (i + N) ∉ F := by
        rw [hF]
        simp only [Finset.mem_range]
        omega
      rw [hqq_notF (i + N) hnot]
      simp
    rw [hz]
    exact summable_zero
  have hd_norm : UScaleNorm e lam t d = ∑' k, ENNReal.ofReal (w k * qq k ^ 2) := by
    have h1 : UScaleNorm e lam t d
        = ∑' k, ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) d) ^ 2) := rfl
    rw [h1]
    refine tsum_congr (fun k => ?_)
    rw [hcoord k]
  have hd_top : UScaleNorm e lam t d < ⊤ := by
    rw [hd_norm]
    exact Summable.tsum_ofReal_lt_top hqqs
  have hdist : UScaleDist e lam t u d < ENNReal.ofReal ε := by
    have h1 : UScaleDist e lam t u d = (UScaleNorm e lam t (u - d)) ^ (1 / 2 : ℝ) := rfl
    rw [h1]
    refine lt_of_le_of_lt (b := (ENNReal.ofReal A) ^ (1 / 2 : ℝ)) ?_ ?_
    · exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 1 / 2)).mpr hmain.le
    · rw [ENNReal.ofReal_rpow_of_nonneg hApos.le (by norm_num : (0:ℝ) ≤ 1 / 2)]
      rw [ENNReal.ofReal_lt_ofReal_iff hε]
      rw [hA]
      have key : ((ε / 2) ^ 2) ^ (1 / 2 : ℝ) = ε / 2 := by
        have hcast : ((ε / 2) ^ 2 : ℝ) = (ε / 2) ^ (2 : ℝ) :=
          (Real.rpow_natCast (ε / 2) 2).symm
        calc ((ε / 2) ^ 2) ^ (1 / 2 : ℝ) = ((ε / 2) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [hcast]
          _ = (ε / 2) ^ ((2 : ℝ) * (1 / 2 : ℝ)) :=
              (Real.rpow_mul (x := ε / 2) (show (0:ℝ) ≤ ε / 2 by linarith) (2 : ℝ) (1 / 2 : ℝ)).symm
          _ = (ε / 2) ^ (1 : ℝ) := by
              congr 1
              norm_num
          _ = ε / 2 := Real.rpow_one _
      rw [key]
      linarith
  exact ⟨s, hd_top, hdist⟩
  /- @proof-region region.target-node.session.f7ffac6ba713667d end -/

end Statlib.Imported
end

