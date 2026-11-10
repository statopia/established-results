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
theorem statopia_math_node_1214593279_6b91f964 : ∀ (U : Type*) [MeasurableSpace U] (mu : Measure U) [IsProbabilityMeasure mu]
    (A : Set U) (hA : MeasurableSet A)
    (F : ℕ → U → ℝ) (hF_meas : ∀ m : ℕ, Measurable (F m))
    (hF_nonneg : ∀ (m : ℕ) (u : U), 0 ≤ F m u)
    (f : U → ℝ) (hf_nonneg : ∀ u : U, 0 ≤ f u)
    (hconv : ∀ᵐ u ∂mu, Filter.Tendsto (fun m : ℕ => F m u) Filter.atTop (nhds (f u)))
    (K : ℝ) (hK : ∀ m : ℕ, ∫⁻ u : U, ENNReal.ofReal ((F m u) ^ 2) ∂mu ≤ ENNReal.ofReal K)
    (c : ENNReal) (hc : c ≠ ⊤)
    (hlim : ∀ᶠ m in Filter.atTop, ∫⁻ u in A, ENNReal.ofReal (F m u) ∂mu = c),
    ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu = c := by
  /- @proof-region region.target-node.session.9bea93d3f4f2e37f begin -/
  intro U instU mu instMu A hA F hF_meas hF_nonneg f hf_nonneg hconv K hK c hc hlim
  have hupper : ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu ≤ c := by
    change ∫⁻ u, ENNReal.ofReal (f u) ∂(mu.restrict A) ≤ c
    have hfatou :
        ∫⁻ u, Filter.liminf (fun m => ENNReal.ofReal (F m u)) Filter.atTop ∂(mu.restrict A)
          ≤ Filter.liminf (fun m => ∫⁻ u, ENNReal.ofReal (F m u) ∂(mu.restrict A)) Filter.atTop :=
      MeasureTheory.lintegral_liminf_le (fun m => ENNReal.measurable_ofReal.comp (hF_meas m))
    have hliminf :
        Filter.liminf (fun m => ∫⁻ u, ENNReal.ofReal (F m u) ∂(mu.restrict A)) Filter.atTop = c := by
      have hP : Tendsto (fun m => ∫⁻ u, ENNReal.ofReal (F m u) ∂(mu.restrict A)) atTop (nhds c) := by
        rw [tendsto_def]
        intro s hs
        filter_upwards [hlim] with m hm
        show (∫⁻ u, ENNReal.ofReal (F m u) ∂(mu.restrict A)) ∈ s
        rw [hm]
        exact mem_of_mem_nhds hs
      exact hP.liminf_eq
    have hmono :
        ∫⁻ u, ENNReal.ofReal (f u) ∂(mu.restrict A)
          ≤ ∫⁻ u, Filter.liminf (fun m => ENNReal.ofReal (F m u)) Filter.atTop ∂(mu.restrict A) := by
      have key : ∀ (x : ℕ → ℝ) (a : ℝ), 0 ≤ a → Tendsto x atTop (nhds a) →
          Tendsto (fun m => ENNReal.ofReal (x m)) atTop (nhds (ENNReal.ofReal a)) := by
        intro x a ha hx
        rw [tendsto_order]
        constructor
        · intro b hb
          have hbne : b ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hb le_top)
          have hbt : b.toReal < a := by
            have h2 : b.toReal < (ENNReal.ofReal a).toReal :=
              (ENNReal.toReal_lt_toReal hbne ENNReal.ofReal_ne_top).mpr hb
            rwa [ENNReal.toReal_ofReal ha] at h2
          filter_upwards [(tendsto_order.mp hx).1 b.toReal hbt] with m hm
          rw [← ENNReal.ofReal_toReal hbne]
          exact (ENNReal.ofReal_lt_ofReal_iff (q := x m)
            (lt_of_le_of_lt ENNReal.toReal_nonneg hm)).mpr hm
        · intro b hb
          rcases eq_or_ne b ⊤ with htop | hbne
          · rw [htop]
            filter_upwards with m
            exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
          · have hb' : a < b.toReal := (ENNReal.ofReal_lt_iff_lt_toReal ha hbne).mp hb
            filter_upwards [(tendsto_order.mp hx).2 b.toReal hb'] with m hm
            rw [← ENNReal.ofReal_toReal hbne]
            exact (ENNReal.ofReal_lt_ofReal_iff (q := b.toReal)
              (lt_of_le_of_lt ha hb')).mpr hm
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hconv] with u hu
      have hku := key (fun m => F m u) (f u) (hf_nonneg u) hu
      exact le_of_eq hku.liminf_eq.symm
    rw [hliminf] at hfatou
    exact le_trans hmono hfatou
  have hlower : c ≤ ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu := by
    have hmuA : mu A ≠ ⊤ := measure_ne_top mu A
    have hνuniv : (mu.restrict A) Set.univ = mu A := by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    haveI : IsFiniteMeasure (mu.restrict A) :=
      ⟨by rw [hνuniv]; exact lt_top_iff_ne_top.mpr hmuA⟩
    have hLne : (∫⁻ u in A, ENNReal.ofReal (f u) ∂mu) ≠ ⊤ := by
      intro htop
      rw [htop] at hupper
      exact hc (top_le_iff.mp hupper)
    have hfaesm : AEStronglyMeasurable f (mu.restrict A) :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hF_meas m).aestronglyMeasurable)
        (MeasureTheory.ae_mono Measure.restrict_le_self hconv)
    have hLreal : (∫⁻ u in A, ENNReal.ofReal (f u) ∂mu).toReal = ∫ u in A, f u ∂mu :=
      (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall hf_nonneg) hfaesm).symm
    have hfint : Integrable f (mu.restrict A) :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hfaesm
        (Filter.Eventually.of_forall hf_nonneg)).1 hLne
    have hsq_meas : ∀ m : ℕ, Measurable (fun u => (F m u) ^ 2) := by
      intro m
      have h := (hF_meas m).mul (hF_meas m)
      simpa [pow_two] using h
    have hsq_restrict : ∀ m : ℕ, ∫⁻ u in A, ENNReal.ofReal ((F m u) ^ 2) ∂mu
        ≤ ∫⁻ u, ENNReal.ofReal ((F m u) ^ 2) ∂mu := by
      intro m
      rw [← MeasureTheory.lintegral_indicator hA]
      refine MeasureTheory.lintegral_mono (fun u => ?_)
      by_cases hu : u ∈ A
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu]
        exact zero_le _
    have hsq_le : ∀ m : ℕ, ∫ u in A, (F m u) ^ 2 ∂mu ≤ max K 0 := by
      intro m
      have hle : ∫⁻ u in A, ENNReal.ofReal ((F m u) ^ 2) ∂mu ≤ ENNReal.ofReal (max K 0) :=
        le_trans (hsq_restrict m)
          (le_trans (hK m) (ENNReal.ofReal_le_ofReal (le_max_left K 0)))
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun u => sq_nonneg (F m u)) (hsq_meas m).aestronglyMeasurable]
      exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle)
        (le_of_eq (ENNReal.toReal_ofReal (le_max_right K 0)))
    have hsq_intA : ∀ m : ℕ, Integrable (fun u => (F m u) ^ 2) (mu.restrict A) := by
      intro m
      have hle : ∫⁻ u in A, ENNReal.ofReal ((F m u) ^ 2) ∂mu ≤ ENNReal.ofReal (max K 0) :=
        le_trans (hsq_restrict m)
          (le_trans (hK m) (ENNReal.ofReal_le_ofReal (le_max_left K 0)))
      have hne : ∫⁻ u in A, ENNReal.ofReal ((F m u) ^ 2) ∂mu ≠ ⊤ := by
        intro htop
        rw [htop] at hle
        exact ENNReal.ofReal_ne_top (top_le_iff.mp hle)
      exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hsq_meas m).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => sq_nonneg (F m u))).1 hne
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hlim
    have hFint : ∀ m ≥ N, Integrable (fun u => F m u) (mu.restrict A) := by
      intro m hm
      have hne : ∫⁻ u in A, ENNReal.ofReal (F m u) ∂mu ≠ ⊤ := by
        rw [hN m hm]
        exact hc
      exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hF_meas m).aestronglyMeasurable
        (Filter.Eventually.of_forall (hF_nonneg m))).1 hne
    have hFeq : ∀ m ≥ N, ∫ u in A, F m u ∂mu = c.toReal := by
      intro m hm
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (hF_nonneg m)) (hF_meas m).aestronglyMeasurable, hN m hm]
    have hsplit : ∀ (x t : ℝ), 0 < t → min x t + max (x - t) 0 = x := by
      intro x t ht
      rcases le_total x t with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]
        ring
      · rw [min_eq_right h, max_eq_left (by linarith)]
        ring
    have htail_pt : ∀ (x t : ℝ), 0 ≤ x → 0 < t → t * max (x - t) 0 ≤ x ^ 2 := by
      intro x t hx ht
      rcases le_total x t with h | h
      · rw [max_eq_right (by linarith), mul_zero]
        exact sq_nonneg x
      · rw [max_eq_left (by linarith)]
        nlinarith [sq_nonneg (2 * x - t), sq_nonneg t, mul_nonneg hx ht.le]
    have hmain : ∀ t : ℝ, 0 < t → c.toReal ≤ ∫ u in A, f u ∂mu + max K 0 / t := by
      intro t ht
      have htail_int : ∀ m ≥ N, Integrable (fun u => max (F m u - t) 0) (mu.restrict A) := by
        intro m hm
        refine MeasureTheory.Integrable.mono (hFint m hm) ?_ ?_
        · exact (((hF_meas m).sub measurable_const).max measurable_const).aestronglyMeasurable
        · filter_upwards with u
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _),
            abs_of_nonneg (hF_nonneg m u)]
          exact max_le (by linarith) (hF_nonneg m u)
      have hmin_int : ∀ m ≥ N, Integrable (fun u => min (F m u) t) (mu.restrict A) := by
        intro m hm
        refine MeasureTheory.Integrable.of_bound
          ((hF_meas m).min measurable_const).aestronglyMeasurable t ?_
        filter_upwards with u
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF_nonneg m u) ht.le)]
        exact min_le_right _ _
      have hdecomp : ∀ m ≥ N, ∫ u in A, F m u ∂mu
          = ∫ u in A, min (F m u) t ∂mu + ∫ u in A, max (F m u - t) 0 ∂mu := by
        intro m hm
        have h1 : ∫ u in A, F m u ∂mu
            = ∫ u in A, (min (F m u) t + max (F m u - t) 0) ∂mu :=
          MeasureTheory.integral_congr_ae (by
            filter_upwards with u
            exact (hsplit (F m u) t ht).symm)
        rw [h1, MeasureTheory.integral_add (hmin_int m hm) (htail_int m hm)]
      have htail_le : ∀ m ≥ N, t * ∫ u in A, max (F m u - t) 0 ∂mu ≤ max K 0 := by
        intro m hm
        have h1 : t * ∫ u in A, max (F m u - t) 0 ∂mu
            = ∫ u in A, t * max (F m u - t) 0 ∂mu := by
          rw [MeasureTheory.integral_const_mul]
        rw [h1]
        refine le_trans (MeasureTheory.integral_mono ((htail_int m hm).const_mul t) (hsq_intA m)
          (fun u => htail_pt (F m u) t (hF_nonneg m u) ht)) (hsq_le m)
      have hDCT : Tendsto (fun m => ∫ u in A, min (F m u) t ∂mu) atTop
          (nhds (∫ u in A, min (f u) t ∂mu)) := by
        refine MeasureTheory.tendsto_integral_of_dominated_convergence (μ := mu.restrict A)
          (F := fun m u => min (F m u) t) (f := fun u => min (f u) t) (fun _ => t) ?_ ?_ ?_ ?_
        · exact fun m => ((hF_meas m).min measurable_const).aestronglyMeasurable
        · exact MeasureTheory.integrable_const t
        · intro m
          filter_upwards with u
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF_nonneg m u) ht.le)]
          exact min_le_right _ _
        · filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hconv] with u hu
          exact hu.min tendsto_const_nhds
      have hev : ∀ᶠ m in atTop, c.toReal ≤ ∫ u in A, min (F m u) t ∂mu + max K 0 / t := by
        filter_upwards [Filter.eventually_ge_atTop N] with m hm
        have h1 : c.toReal
            = ∫ u in A, min (F m u) t ∂mu + ∫ u in A, max (F m u - t) 0 ∂mu := by
          rw [← hFeq m hm, hdecomp m hm]
        have h2 : ∫ u in A, max (F m u - t) 0 ∂mu ≤ max K 0 / t := by
          rw [le_div_iff₀ ht]
          linarith [htail_le m hm]
        linarith
      have hlim_ge : c.toReal - max K 0 / t ≤ ∫ u in A, min (f u) t ∂mu := by
        by_contra hcon
        push_neg at hcon
        have h2 := (tendsto_order.mp hDCT).2 (c.toReal - max K 0 / t) hcon
        obtain ⟨m, hm1, hm2⟩ := (hev.and h2).exists
        linarith
      have hminf_aesm : AEStronglyMeasurable (fun u => min (f u) t) (mu.restrict A) :=
        aestronglyMeasurable_of_tendsto_ae atTop
          (fun m => ((hF_meas m).min measurable_const).aestronglyMeasurable)
          (by
            filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hconv] with u hu
            exact hu.min tendsto_const_nhds)
      have hmin_le : ∫ u in A, min (f u) t ∂mu ≤ ∫ u in A, f u ∂mu := by
        refine MeasureTheory.integral_mono ?_ hfint (fun u => min_le_left _ _)
        refine MeasureTheory.Integrable.of_bound hminf_aesm t ?_
        filter_upwards with u
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf_nonneg u) ht.le)]
        exact min_le_right _ _
      linarith
    have hreal : c.toReal ≤ ∫ u in A, f u ∂mu := by
      by_contra hcon
      push_neg at hcon
      set d := (c.toReal - ∫ u in A, f u ∂mu) / 2 with hd
      have hdpos : 0 < d := by rw [hd]; linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (max K 0 / d)
      have hnpos : (0:ℝ) < (n:ℝ) := by
        rcases Nat.eq_zero_or_pos n with h | h
        · rw [h] at hn
          simp at hn
          have h0 : 0 ≤ max K 0 / d := div_nonneg (le_max_right K 0) hdpos.le
          linarith
        · exact_mod_cast h
      have hbd : max K 0 / (n:ℝ) ≤ d := by
        rw [div_le_iff₀ hnpos]
        rw [div_lt_iff₀ hdpos] at hn
        linarith
      have h1 := hmain (n:ℝ) hnpos
      rw [hd] at hbd
      linarith
    calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc).symm
      _ ≤ ENNReal.ofReal (∫ u in A, f u ∂mu) := ENNReal.ofReal_le_ofReal hreal
      _ = ∫⁻ u in A, ENNReal.ofReal (f u) ∂mu := by
            rw [← hLreal, ENNReal.ofReal_toReal hLne]
  exact le_antisymm hupper hlower
  /- @proof-region region.target-node.session.9bea93d3f4f2e37f end -/

end Statlib.Imported
end

