import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2540716848_7ce5841c_f4134c6f
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2847970413_3f215f33_c9236254
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_457006637_708d8d08_c9bb53bc

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
theorem statopia_math_node_3082865640_d48798c3 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U]
    [BorelSpace U]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Type*) [TopologicalSpace X]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (Gammaih : H → H) (LG : X → U → H)
    (st : ℝ) (hst_le : st ≤ 1)
    (hLip : ∀ (x : X) (y : H) (u0 : U), UScale e lam (1 - st) u0 →
      ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ u : U, UScale e lam (1 - st) u →
          UScaleDist e lam (1 - st) u u0 ≤ ENNReal.ofReal delta →
          |Phi Gammaih LG u x y - Phi Gammaih LG u0 x y| ≤
            C * (UScaleDist e lam (1 - st) u u0).toReal)
    (hSigma : MeasurableSpace.generateFrom
        {T : Set {u : U // UScale e lam (1 - st) u} |
          ∃ u0 : U, UScale e lam (1 - st) u0 ∧ ∃ eps : ℝ, 0 < eps ∧
            T = {v : {u : U // UScale e lam (1 - st) u} |
                  UScaleDist e lam (1 - st) (v : U) u0 < ENNReal.ofReal eps}}
      = MeasurableSpace.comap (Subtype.val : {u : U // UScale e lam (1 - st) u} → U)
          (borel U))
    (x : X) (y : H) (Q : Measure U)
    (hQ : Q (UScale e lam (1 - st)) = 1)
    (hQae : Q ((UScale e lam (1 - st))ᶜ) = 0),
    AEMeasurable (fun u : U => Phi Gammaih LG u x y) Q := by
  /- @proof-region region.target-node.session.048bf1e6eaecfaa6 begin -/
  intro U _ _ _ _ H _ _ X _ e lam hlam_pos hlam_anti Gammaih LG st hst_le hLip hSigma x y Q hQ hQae
  classical
  have hae : (fun u : U => if UScale e lam (1 - st) u then Phi Gammaih LG u x y else 0)
      =ᵐ[Q] (fun u : U => Phi Gammaih LG u x y) := by
    have hmem : ∀ᵐ u ∂Q, u ∈ UScale e lam (1 - st) := by
      apply MeasureTheory.ae_iff.mpr
      simpa using hQae
    filter_upwards [hmem] with u hu
    rw [if_pos (show UScale e lam (1 - st) u from hu)]
  have hG : Measurable
      (fun u : U => if UScale e lam (1 - st) u then Phi Gammaih LG u x y else 0) := by
    have hbU : (‹MeasurableSpace U› : MeasurableSpace U) = borel U := BorelSpace.measurable_eq
    have hS : MeasurableSet (UScale e lam (1 - st)) := by
      have h1 : Measurable fun u : U => UScaleNorm e lam (1 - st) u := by
        refine Measurable.ennreal_tsum (fun k => ?_)
        have hinner : Measurable fun u : U => inner ℝ (e k) u := by
          have hc : Continuous fun u : U => inner ℝ (e k) u := by
            simpa [coe_innerSL_apply] using
              (ContinuousLinearMap.continuous ((innerSL ℝ) (e k) : U →L[ℝ] ℝ))
          exact hc.measurable
        have hsq : Measurable fun u : U => (inner ℝ (e k) u) ^ 2 := by
          simpa [pow_two] using hinner.mul hinner
        have h3 : Measurable fun u : U =>
            Real.rpow (lam k) (-(1 - st)) * (inner ℝ (e k) u) ^ 2 :=
          measurable_const.mul hsq
        exact ENNReal.measurable_ofReal.comp h3
      exact h1 measurableSet_Iio
    have hpre : ∀ I : Set ℝ, IsOpen I → MeasurableSet
        ((fun u : U => if UScale e lam (1 - st) u then Phi Gammaih LG u x y else 0) ⁻¹' I) := by
      intro I hI
      obtain ⟨Bc, hBmem, hBbase⟩ :=
        statopia_math_node_2847970413_3f215f33 (U := U) e lam hlam_pos hlam_anti (1 - st) (by linarith)
      set A : Set {u : U // UScale e lam (1 - st) u} :=
        {v | Phi Gammaih LG (v : U) x y ∈ I} with hA
      have hopen : ∀ v ∈ A, ∃ eps : ℝ, 0 < eps ∧
          {w : {u : U // UScale e lam (1 - st) u} |
            UScaleDist e lam (1 - st) (w : U) (v : U) < ENNReal.ofReal eps} ⊆ A := by
        intro v hv
        rw [hA] at hv
        obtain ⟨m, hm, hmsub⟩ : ∃ m : ℝ, 0 < m ∧
            ∀ z : ℝ, |z - Phi Gammaih LG (v : U) x y| < m → z ∈ I := by
          obtain ⟨m, hm, hsub⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hv)
          exact ⟨m, hm, fun z hz => hsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hz)⟩
        obtain ⟨delta, hdelta, C, hC, hLipv⟩ := hLip x y (v : U) v.2
        refine ⟨min delta (m / (C + 1)), lt_min hdelta (by positivity), ?_⟩
        intro w hw
        rw [hA]
        have hle : UScaleDist e lam (1 - st) (w : U) (v : U) ≤ ENNReal.ofReal delta :=
          hw.le.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
        have hbound := hLipv (w : U) w.2 hle
        have hdist : (UScaleDist e lam (1 - st) (w : U) (v : U)).toReal ≤ m / (C + 1) := by
          have h2 : UScaleDist e lam (1 - st) (w : U) (v : U) ≤ ENNReal.ofReal (m / (C + 1)) :=
            hw.le.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
          calc (UScaleDist e lam (1 - st) (w : U) (v : U)).toReal
              ≤ (ENNReal.ofReal (m / (C + 1))).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
            _ = m / (C + 1) := ENNReal.toReal_ofReal (by positivity)
        have hCm : C * (UScaleDist e lam (1 - st) (w : U) (v : U)).toReal < m := by
          have h1 : C * (UScaleDist e lam (1 - st) (w : U) (v : U)).toReal ≤ C * (m / (C + 1)) :=
            mul_le_mul_of_nonneg_left hdist hC
          have h2 : C * (m / (C + 1)) < m := by
            have h3 : C / (C + 1) < 1 := by
              rw [div_lt_one (by linarith)]
              linarith
            calc C * (m / (C + 1)) = (C / (C + 1)) * m := by field_simp
              _ < 1 * m := mul_lt_mul_of_pos_right h3 hm
              _ = m := one_mul m
          linarith
        exact hmsub _ (lt_of_le_of_lt hbound hCm)
      obtain ⟨s, hs⟩ := hBbase A hopen
      have hfun : ∀ n : ℕ, MeasurableSet[MeasurableSpace.generateFrom
          {T : Set {u : U // UScale e lam (1 - st) u} |
            ∃ u0 : U, UScale e lam (1 - st) u0 ∧ ∃ eps : ℝ, 0 < eps ∧
              T = {v : {u : U // UScale e lam (1 - st) u} |
                    UScaleDist e lam (1 - st) (v : U) u0 < ENNReal.ofReal eps}}] (Bc n) := by
        intro n
        obtain ⟨u0, hu0, eps, heps, heq⟩ := hBmem n
        rw [heq]
        exact MeasurableSpace.measurableSet_generateFrom ⟨u0, hu0, eps, heps, rfl⟩
      have hgen : MeasurableSet[MeasurableSpace.generateFrom
          {T : Set {u : U // UScale e lam (1 - st) u} |
            ∃ u0 : U, UScale e lam (1 - st) u0 ∧ ∃ eps : ℝ, 0 < eps ∧
              T = {v : {u : U // UScale e lam (1 - st) u} |
                    UScaleDist e lam (1 - st) (v : U) u0 < ENNReal.ofReal eps}}] A := by
        letI : MeasurableSpace {u : U // UScale e lam (1 - st) u} :=
          MeasurableSpace.generateFrom
            {T : Set {u : U // UScale e lam (1 - st) u} |
              ∃ u0 : U, UScale e lam (1 - st) u0 ∧ ∃ eps : ℝ, 0 < eps ∧
                T = {v : {u : U // UScale e lam (1 - st) u} |
                      UScaleDist e lam (1 - st) (v : U) u0 < ENNReal.ofReal eps}}
        rw [hs]
        have hEq : (⋃ n ∈ s, Bc n) = ⋃ n : ℕ, (if n ∈ s then Bc n else ∅) := by
          ext x
          simp only [Set.mem_iUnion]
          constructor
          · rintro ⟨n, hn, hx⟩
            exact ⟨n, by simpa [hn] using hx⟩
          · rintro ⟨n, hx⟩
            by_cases hn : n ∈ s
            · exact ⟨n, hn, by simpa [hn] using hx⟩
            · rw [if_neg hn] at hx
              exact absurd hx (Set.notMem_empty x)
        rw [hEq]
        exact MeasurableSet.iUnion (fun n => by
          by_cases hn : n ∈ s
          · rw [if_pos hn]; exact hfun n
          · rw [if_neg hn]; exact MeasurableSet.empty)
      have hcomap : MeasurableSet[MeasurableSpace.comap
          (Subtype.val : {u : U // UScale e lam (1 - st) u} → U) (borel U)] A := by
        rw [← hSigma]
        exact hgen
      obtain ⟨B', hB', hB'eq⟩ := MeasurableSpace.measurableSet_comap.mp hcomap
      have hB'm : MeasurableSet B' := by
        rw [hbU]
        exact hB'
      have hGeq : ((fun u : U => if UScale e lam (1 - st) u then Phi Gammaih LG u x y else 0) ⁻¹' I)
          = (B' ∩ UScale e lam (1 - st)) ∪
            ((UScale e lam (1 - st))ᶜ ∩ (if (0 : ℝ) ∈ I then Set.univ else ∅)) := by
        ext u
        by_cases hu : UScale e lam (1 - st) u
        · have hmemS : u ∈ UScale e lam (1 - st) := hu
          have hiff : u ∈ B' ↔ Phi Gammaih LG u x y ∈ I := by
            have step : (⟨u, hu⟩ : {u : U // UScale e lam (1 - st) u}) ∈ A ↔
                Phi Gammaih LG u x y ∈ I := by
              rw [hA]
              exact Iff.rfl
            rw [← step, ← hB'eq]
            simp
          simp only [Set.mem_preimage]
          simp [hu, hmemS, hiff]
        · have hmemS : ¬ (u ∈ UScale e lam (1 - st)) := hu
          simp only [Set.mem_preimage]
          by_cases h0 : (0 : ℝ) ∈ I
          · simp [hu, hmemS, h0]
          · simp [hu, hmemS, h0]
      rw [hGeq]
      refine MeasurableSet.union (hB'm.inter hS) (MeasurableSet.inter hS.compl ?_)
      split_ifs with h0
      · exact MeasurableSet.univ
      · exact MeasurableSet.empty
    intro s hs
    have hbR : (inferInstance : MeasurableSpace ℝ) = borel ℝ := BorelSpace.measurable_eq
    have hle : MeasurableSpace.comap
        (fun u : U => if UScale e lam (1 - st) u then Phi Gammaih LG u x y else 0)
        (inferInstance : MeasurableSpace ℝ) ≤ ‹MeasurableSpace U› := by
      rw [hbR]
      unfold borel
      rw [MeasurableSpace.comap_generateFrom]
      refine MeasurableSpace.generateFrom_le ?_
      rintro t ⟨I, hI, ht⟩
      rw [← ht]
      exact hpre I hI
    have hmem : MeasurableSet[MeasurableSpace.comap
        (fun u : U => if UScale e lam (1 - st) u then Phi Gammaih LG u x y else 0)
        (inferInstance : MeasurableSpace ℝ)]
        ((fun u : U => if UScale e lam (1 - st) u then Phi Gammaih LG u x y else 0) ⁻¹' s) := by
      refine MeasurableSpace.measurableSet_comap.mpr ⟨s, hs, ?_⟩
      rfl
    exact hle _ hmem
  exact hG.aemeasurable.congr hae
  /- @proof-region region.target-node.session.048bf1e6eaecfaa6 end -/

end Statlib.Imported
end

