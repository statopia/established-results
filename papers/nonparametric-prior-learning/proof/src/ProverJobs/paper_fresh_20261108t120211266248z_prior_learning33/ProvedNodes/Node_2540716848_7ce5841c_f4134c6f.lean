import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3779846650_359ff4f8_8b0f0688

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
theorem statopia_math_node_2540716848_7ce5841c : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ)
    (hlam_pos : ∀ k : ℕ, 0 < lam k) (hlam_anti : Antitone lam)
    (t : ℝ) (ht : 0 ≤ t),
    MeasurableSpace.generateFrom
        {T : Set {u : U // UScale e lam t u} |
          ∃ u0 : U, UScale e lam t u0 ∧ ∃ eps : ℝ, 0 < eps ∧
            T = {v : {u : U // UScale e lam t u} |
                  UScaleDist e lam t (v : U) u0 < ENNReal.ofReal eps}}
      = MeasurableSpace.comap (Subtype.val : {u : U // UScale e lam t u} → U) (borel U) := by
  /- @proof-region region.target-node.session.f11930466f3a5ac3 begin -/
  intro U _ _ _ _ e lam hlam_pos hlam_anti t ht
  have hgen : MeasurableSpace.generateFrom
      {T : Set {u : U // UScale e lam t u} |
        ∃ u0 : U, UScale e lam t u0 ∧ ∃ eps : ℝ, 0 < eps ∧
          T = {v : {u : U // UScale e lam t u} |
                UScaleDist e lam t (v : U) u0 < ENNReal.ofReal eps}}
      ≤ MeasurableSpace.comap (Subtype.val : {u : U // UScale e lam t u} → U) (borel U) := by
    apply MeasurableSpace.generateFrom_le
    rintro T ⟨u0, hu0, eps, heps, rfl⟩
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{u : U | (UScaleNorm e lam t (u - u0)) ^ (1 / 2 : ℝ) < ENNReal.ofReal eps}, ?_, rfl⟩
    have hf : Measurable fun u : U => UScaleNorm e lam t (u - u0) := by
      simp only [UScaleNorm]
      apply Measurable.ennreal_tsum
      intro k
      have hcont : Continuous fun u : U =>
          Real.rpow (lam k) (-t) * (inner ℝ (e k) (u - u0)) ^ 2 :=
        continuous_const.mul ((continuous_inner.comp
          (continuous_const.prodMk (continuous_id.sub continuous_const))).pow 2)
      exact ENNReal.measurable_ofReal.comp hcont.measurable
    have hmeas : Measurable fun u : U => (UScaleNorm e lam t (u - u0)) ^ (1 / 2 : ℝ) :=
      (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).measurable.comp hf
    rw [show borel U = ‹MeasurableSpace U› from BorelSpace.measurable_eq.symm]
    exact hmeas (isOpen_Iio (a := ENNReal.ofReal eps)).measurableSet
  have hborel : MeasurableSpace.comap (Subtype.val : {u : U // UScale e lam t u} → U) (borel U) ≤
      MeasurableSpace.generateFrom
        {T : Set {u : U // UScale e lam t u} |
          ∃ u0 : U, UScale e lam t u0 ∧ ∃ eps : ℝ, 0 < eps ∧
            T = {v : {u : U // UScale e lam t u} |
                  UScaleDist e lam t (v : U) u0 < ENNReal.ofReal eps}} := by
    have htransfer : ∀ B : Set U, MeasurableSet[borel U] B →
        MeasurableSet[MeasurableSpace.generateFrom
          {T : Set {u : U // UScale e lam t u} |
            ∃ u0 : U, UScale e lam t u0 ∧ ∃ eps : ℝ, 0 < eps ∧
              T = {v : {u : U // UScale e lam t u} |
                    UScaleDist e lam t (v : U) u0 < ENNReal.ofReal eps}}]
          ((Subtype.val : {u : U // UScale e lam t u} → U) ⁻¹' B) := by
      have hopen : ∀ O : Set U, IsOpen O →
          MeasurableSet[MeasurableSpace.generateFrom
            {T : Set {u : U // UScale e lam t u} |
              ∃ u0 : U, UScale e lam t u0 ∧ ∃ eps : ℝ, 0 < eps ∧
                T = {v : {u : U // UScale e lam t u} |
                      UScaleDist e lam t (v : U) u0 < ENNReal.ofReal eps}}]
            ((Subtype.val : {u : U // UScale e lam t u} → U) ⁻¹' O) := by
        set c : ℝ := Real.rpow (lam 0) (-t) with hcdef
        have hc : 0 < c := by
          rw [hcdef]
          exact Real.rpow_pos_of_pos (hlam_pos 0) _
        have hdom : ∀ y : U, ENNReal.ofReal (c * ‖y‖ ^ 2) ≤ UScaleNorm e lam t y := by
          intro y
          have hnorm : ‖y‖ ^ 2 = ∑' k : ℕ, (inner ℝ (e k) y) ^ 2 := by
            rw [← real_inner_self_eq_norm_sq y, ← HilbertBasis.tsum_inner_mul_inner e y y]
            refine tsum_congr fun k => ?_
            rw [real_inner_comm y]
            ring
          have hsummable : Summable fun k : ℕ => (inner ℝ (e k) y) ^ 2 :=
            (HilbertBasis.summable_inner_mul_inner e y y).congr fun k => by
              rw [real_inner_comm y]
              ring
          have hnorm2 : ENNReal.ofReal (‖y‖ ^ 2) =
              ∑' k : ℕ, ENNReal.ofReal ((inner ℝ (e k) y) ^ 2) := by
            rw [hnorm]
            exact ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hsummable
          calc ENNReal.ofReal (c * ‖y‖ ^ 2)
              = ENNReal.ofReal c * ENNReal.ofReal (‖y‖ ^ 2) := by
                rw [ENNReal.ofReal_mul (le_of_lt hc)]
            _ = ENNReal.ofReal c *
                  (∑' k : ℕ, ENNReal.ofReal ((inner ℝ (e k) y) ^ 2)) := by
                rw [hnorm2]
            _ = ∑' k : ℕ, ENNReal.ofReal c * ENNReal.ofReal ((inner ℝ (e k) y) ^ 2) :=
                ENNReal.tsum_mul_left.symm
            _ = ∑' k : ℕ, ENNReal.ofReal (c * (inner ℝ (e k) y) ^ 2) := by
                exact tsum_congr fun k => (ENNReal.ofReal_mul (le_of_lt hc)).symm
            _ ≤ ∑' k : ℕ,
                  ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) y) ^ 2) := by
                apply ENNReal.tsum_le_tsum
                intro k
                apply ENNReal.ofReal_le_ofReal
                have h1 : lam k ≤ lam 0 := hlam_anti (Nat.zero_le k)
                have h2 : lam 0 ^ (-t) ≤ lam k ^ (-t) :=
                  Real.rpow_le_rpow_of_nonpos (hlam_pos k) h1 (by linarith)
                have hck : c ≤ Real.rpow (lam k) (-t) := by
                  simpa [hcdef] using h2
                exact mul_le_mul_of_nonneg_right hck (sq_nonneg _)
            _ = UScaleNorm e lam t y := rfl
        have hdomdist : ∀ y : U, ENNReal.ofReal (Real.sqrt c * ‖y‖) ≤ UScaleDist e lam t y 0 := by
          intro y
          have hcy : (0 : ℝ) ≤ c * ‖y‖ ^ 2 := by positivity
          have hkey : Real.sqrt c * ‖y‖ = (c * ‖y‖ ^ 2) ^ (1 / 2 : ℝ) := by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (le_of_lt hc), Real.sqrt_sq (norm_nonneg y)]
          calc ENNReal.ofReal (Real.sqrt c * ‖y‖)
              = ENNReal.ofReal ((c * ‖y‖ ^ 2) ^ (1 / 2 : ℝ)) := by rw [hkey]
            _ = (ENNReal.ofReal (c * ‖y‖ ^ 2)) ^ (1 / 2 : ℝ) :=
                (ENNReal.ofReal_rpow_of_nonneg hcy (by norm_num)).symm
            _ ≤ (UScaleNorm e lam t y) ^ (1 / 2 : ℝ) :=
                ENNReal.rpow_le_rpow (hdom y) (by norm_num)
            _ = UScaleDist e lam t y 0 := by rw [UScaleDist, sub_zero]
        have hdense : ∀ u : U, UScaleNorm e lam t u < ⊤ → ∀ ε : ℝ, 0 < ε →
            ∃ s : Finset (ℕ × ℚ),
              UScaleNorm e lam t (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1) < ⊤ ∧
              UScaleDist e lam t u (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1) < ENNReal.ofReal ε := by
          exact fun u hu ε hε =>
            statopia_math_node_3779846650_359ff4f8 U e lam hlam_pos hlam_anti t ht u hu ε hε
        intro O hO
        have hcover : ∀ v : {u : U // UScale e lam t u}, (v : U) ∈ O →
            ∃ i : Finset (ℕ × ℚ) × ℚ, 0 < (i.2 : ℝ) ∧
              UScale e lam t (∑ p ∈ i.1, ((p.2 : ℚ) : ℝ) • e p.1) ∧
              v ∈ {w : {u : U // UScale e lam t u} |
                    UScaleDist e lam t (w : U) (∑ p ∈ i.1, ((p.2 : ℚ) : ℝ) • e p.1)
                      < ENNReal.ofReal (i.2 : ℝ)} ∧
              {w : {u : U // UScale e lam t u} |
                    UScaleDist e lam t (w : U) (∑ p ∈ i.1, ((p.2 : ℚ) : ℝ) • e p.1)
                      < ENNReal.ofReal (i.2 : ℝ)} ⊆ Subtype.val ⁻¹' O := by
          intro v hv
          obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.1 hO (v : U) hv
          have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
          obtain ⟨q, hq0, hq2⟩ :=
            exists_rat_btwn (show (0 : ℝ) < δ * Real.sqrt c / 2 by positivity)
          obtain ⟨s, hdS, hdist⟩ := hdense (v : U) v.2 (q : ℝ) hq0
          refine ⟨(s, q), hq0, hdS, hdist, ?_⟩
          intro w hw
          have h1 : Real.sqrt c * ‖(w : U) - (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1)‖ < (q : ℝ) := by
            have h2 : ENNReal.ofReal
                  (Real.sqrt c * ‖(w : U) - (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1)‖) <
                ENNReal.ofReal (q : ℝ) :=
              lt_of_le_of_lt (hdomdist _) (by simpa [UScaleDist, sub_zero] using hw)
            by_contra hcon
            push_neg at hcon
            exact absurd (ENNReal.ofReal_le_ofReal hcon) (not_le.2 h2)
          have h3 : Real.sqrt c * ‖(v : U) - (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1)‖ < (q : ℝ) := by
            have h2 : ENNReal.ofReal
                  (Real.sqrt c * ‖(v : U) - (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1)‖) <
                ENNReal.ofReal (q : ℝ) :=
              lt_of_le_of_lt (hdomdist _) (by simpa [UScaleDist, sub_zero] using hdist)
            by_contra hcon
            push_neg at hcon
            exact absurd (ENNReal.ofReal_le_ofReal hcon) (not_le.2 h2)
          have hδnorm : ‖(w : U) - (v : U)‖ < δ := by
            have hsplit : ‖(w : U) - (v : U)‖ ≤
                ‖(w : U) - (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1)‖ +
                ‖(∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1) - (v : U)‖ := by
              have h0 : (w : U) - (v : U) =
                  ((w : U) - (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1)) +
                  ((∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1) - (v : U)) := by abel
              rw [h0]
              exact norm_add_le _ _
            rw [norm_sub_rev (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1) (v : U)] at hsplit
            have h5 : Real.sqrt c * ‖(w : U) - (v : U)‖ < 2 * (q : ℝ) := by
              have hm := mul_le_mul_of_nonneg_left hsplit (le_of_lt hsc)
              have hd : Real.sqrt c *
                    (‖(w : U) - (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1)‖ +
                     ‖(v : U) - (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1)‖) =
                  Real.sqrt c * ‖(w : U) - (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1)‖ +
                  Real.sqrt c * ‖(v : U) - (∑ p ∈ s, ((p.2 : ℚ) : ℝ) • e p.1)‖ := by ring
              nlinarith [hm]
            have h6 : 2 * (q : ℝ) ≤ δ * Real.sqrt c := by linarith
            have h7 : Real.sqrt c * ‖(w : U) - (v : U)‖ < Real.sqrt c * δ := by
              calc Real.sqrt c * ‖(w : U) - (v : U)‖ < 2 * (q : ℝ) := h5
                _ ≤ δ * Real.sqrt c := h6
                _ = Real.sqrt c * δ := by ring
            have hprod : 0 < Real.sqrt c * (δ - ‖(w : U) - (v : U)‖) := by
              nlinarith [h7, hsc]
            have hpos : 0 < δ - ‖(w : U) - (v : U)‖ := by
              by_contra hle
              push_neg at hle
              nlinarith [hsc, hle, hprod]
            linarith
          exact hδ (by simpa [Metric.mem_ball, dist_eq_norm] using hδnorm)
        have hunion : Subtype.val ⁻¹' O =
            ⋃ i ∈ {i : Finset (ℕ × ℚ) × ℚ | 0 < (i.2 : ℝ) ∧
                UScale e lam t (∑ p ∈ i.1, ((p.2 : ℚ) : ℝ) • e p.1) ∧
                {w : {u : U // UScale e lam t u} |
                    UScaleDist e lam t (w : U) (∑ p ∈ i.1, ((p.2 : ℚ) : ℝ) • e p.1)
                      < ENNReal.ofReal (i.2 : ℝ)} ⊆ Subtype.val ⁻¹' O},
              {w : {u : U // UScale e lam t u} |
                UScaleDist e lam t (w : U) (∑ p ∈ i.1, ((p.2 : ℚ) : ℝ) • e p.1)
                  < ENNReal.ofReal (i.2 : ℝ)} := by
          ext w
          simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
          constructor
          · intro hw
            obtain ⟨i, hi1, hi2, hb, hsub⟩ := hcover w hw
            exact ⟨i, ⟨hi1, hi2, hsub⟩, hb⟩
          · rintro ⟨i, ⟨-, -, hsub⟩, hb⟩
            exact hsub hb
        rw [hunion]
        refine MeasurableSet.biUnion ?_ ?_
        · exact Set.countable_univ.mono (fun x _ => trivial)
        · intro i hi
          exact MeasurableSpace.measurableSet_generateFrom ⟨_, hi.2.1, i.2, hi.1, rfl⟩
      let mU : MeasurableSpace U :=
        { MeasurableSet' := fun B =>
            MeasurableSet[MeasurableSpace.generateFrom
              {T : Set {u : U // UScale e lam t u} |
                ∃ u0 : U, UScale e lam t u0 ∧ ∃ eps : ℝ, 0 < eps ∧
                  T = {v : {u : U // UScale e lam t u} |
                        UScaleDist e lam t (v : U) u0 < ENNReal.ofReal eps}}]
              ((Subtype.val : {u : U // UScale e lam t u} → U) ⁻¹' B)
          measurableSet_empty := by
            simpa using MeasurableSet.empty
          measurableSet_compl := by
            intro B hB
            simpa [Set.preimage_compl] using hB.compl
          measurableSet_iUnion := by
            intro f hf
            simpa [Set.preimage_iUnion] using MeasurableSet.iUnion hf }
      have hborel_le : borel U ≤ mU := by
        refine MeasurableSpace.generateFrom_le ?_
        intro O hO
        exact hopen O hO
      exact fun B hB => hborel_le B hB
    rw [MeasurableSpace.comap_eq_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro t ⟨B, hB, rfl⟩
    exact htransfer B hB
  exact le_antisymm hgen hborel
  /- @proof-region region.target-node.session.f11930466f3a5ac3 end -/

end Statlib.Imported
end

