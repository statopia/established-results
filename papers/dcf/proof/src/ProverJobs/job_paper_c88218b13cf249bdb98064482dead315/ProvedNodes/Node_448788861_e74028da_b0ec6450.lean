import Lean
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Vocabulary
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.Base
import ProverJobs.job_paper_c88218b13cf249bdb98064482dead315.ProvedNodes.Node_436922874_8ad414b4_4d515167

namespace PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_c88218b13cf249bdb98064482dead315.Statlib.Imported

noncomputable section
universe u
open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_448788861_e74028da : ∀ (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 2 ≤ p)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (μX μY : Fin p → ℝ) (d : ℝ)
    (X F : Fin n → Ω → (Fin p → ℝ)) (Y G : Fin m → Ω → (Fin p → ℝ))
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - μX j| ^ 3) μ)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - μX j| ^ 3) μ)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - μY j| ^ 3) μ)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - μY j| ^ 3) μ)
    (hXm : ∀ (i : Fin n) (j : Fin p), Measurable (fun ω => X i ω j))
    (hFm : ∀ (i : Fin n) (j : Fin p), Measurable (fun ω => F i ω j))
    (hYm : ∀ (i : Fin m) (j : Fin p), Measurable (fun ω => Y i ω j))
    (hGm : ∀ (i : Fin m) (j : Fin p), Measurable (fun ω => G i ω j)),
    let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
      if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
      else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩;
    (∀ z c : Fin p → ℝ, maxCoord (T z) (T c) = maxCoord z c) ∧
      (∀ (Z : Ω → (Fin p → ℝ)),
        (∀ j : Fin p, Measurable (fun ω => Z ω j)) →
        ∀ (c : Fin p → ℝ) (lev : ℝ),
          truncThird μ (fun ω => T (Z ω)) (T c) lev = truncThird μ Z c lev) ∧
      (∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)),
        (∀ (i : Fin k) (j : Fin p), Measurable (fun ω => Z i ω j)) →
        ∀ (c : Fin p → ℝ) (lev : ℝ),
          (∀ i : Fin k,
            truncThird μ (fun ω => T (Z i ω)) (T c) lev = truncThird μ (Z i) c lev) ∧
          Mstat μ (fun i ω => T (Z i ω)) (T c) lev = Mstat μ Z c lev) ∧
      Lstat μ (fun i : Fin n => T ∘ X i) (T μX) = Lstat μ X μX ∧
      Lstat μ (fun i : Fin m => T ∘ Y i) (T μY) = Lstat μ Y μY ∧
      (∀ (Z : Ω → (Fin p → ℝ)),
        (∀ j : Fin p, Measurable (fun ω => Z ω j)) →
        ∀ (c : Fin p → ℝ) (lev lev' : ℝ), lev ≤ lev' → 0 < lev →
          truncThird μ Z c lev' ≤ truncThird μ Z c lev) ∧
      (∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)),
        (∀ (i : Fin k) (j : Fin p), Measurable (fun ω => Z i ω j)) →
        ∀ (c : Fin p → ℝ) (lev lev' : ℝ), lev ≤ lev' → 0 < lev →
          Mstat μ Z c lev' ≤ Mstat μ Z c lev) ∧
      (∀ phi1 : ℝ, 1 ≤ phi1 →
        MstatN μ (fun i : Fin n => T ∘ X i) (fun i : Fin n => T ∘ F i) (T μX) (phi1 / 2)
          ≤ MstatN μ X F μX phi1) ∧
      (∀ phi2 : ℝ, 1 ≤ phi2 →
        MstatM μ (fun i : Fin m => T ∘ Y i) (fun i : Fin m => T ∘ G i) (T μY) (phi2 / 2) d
          ≤ MstatM μ Y G μY phi2 d) := by
  /- @proof-region region.target-node.session.8e2c3d6713ea465b begin -/
  intro n m p hn hm hp Ω _ μ _ μX μY d X F Y G hX3 hF3 hY3 hG3 hXm hFm hYm hGm
  intro T
  haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (Fin (p + p)) := ⟨⟨0, by omega⟩⟩
  have hT1 : ∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : (j : ℕ) < p),
      T z j = z ⟨(j : ℕ), hj⟩ := fun z j hj => dif_pos hj
  have hT2 : ∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : p ≤ (j : ℕ)),
      T z j = -z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ :=
    fun z j hj => dif_neg (by omega)
  have hmax : ∀ x y : Fin p → ℝ, maxCoord (T x) (T y) = maxCoord x y := by
    intro x y
    have hb : BddAbove (Set.range fun a : Fin p => |x a - y a|) := Finite.bddAbove_range _
    have hb2 : BddAbove (Set.range fun j : Fin (p + p) => |T x j - T y j|) :=
      Finite.bddAbove_range _
    simp only [maxCoord]
    refine le_antisymm (ciSup_le fun j => ?_) (ciSup_le fun a => ?_)
    · by_cases hj : (j : ℕ) < p
      · have hstep : |T x j - T y j| = |x ⟨(j : ℕ), hj⟩ - y ⟨(j : ℕ), hj⟩| := by
          rw [hT1 x j hj, hT1 y j hj]
        rw [hstep]
        exact le_ciSup hb _
      · have hj' : p ≤ (j : ℕ) := by have := j.isLt; omega
        let b : Fin p := ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩
        have hstep : |T x j - T y j| = |x b - y b| := by
          rw [hT2 x j hj', hT2 y j hj',
            show -x b - -y b = -(x b - y b) from by ring, abs_neg]
        rw [hstep]
        exact le_ciSup hb b
    · let j : Fin (p + p) := ⟨(a : ℕ), by have := a.isLt; omega⟩
      have hjlt : (j : ℕ) < p := a.isLt
      have hstep : |x a - y a| = |T x j - T y j| := by rw [hT1 x j hjlt, hT1 y j hjlt]
      rw [hstep]
      exact le_ciSup hb2 j
  have htrunc : ∀ (Z : Ω → (Fin p → ℝ)), (∀ j : Fin p, Measurable (fun ω => Z ω j)) →
      ∀ (c : Fin p → ℝ) (lev : ℝ),
      truncThird μ (fun ω => T (Z ω)) (T c) lev = truncThird μ Z c lev := by
    intro Z _ c lev
    simp only [truncThird]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hmax])
  have hL : ∀ (N : ℕ) (Z : Fin N → Ω → (Fin p → ℝ)) (c : Fin p → ℝ),
      Lstat μ (fun i => T ∘ Z i) (T c) = Lstat μ Z c := by
    intro N Z c
    have hb : BddAbove (Set.range fun a : Fin p =>
        (N : ℝ)⁻¹ * ∑ i : Fin N, ∫ ω, |Z i ω a - c a| ^ 3 ∂μ) := Finite.bddAbove_range _
    have hb2 : BddAbove (Set.range fun j : Fin (p + p) =>
        (N : ℝ)⁻¹ * ∑ i : Fin N, ∫ ω, |T (Z i ω) j - T c j| ^ 3 ∂μ) :=
      Finite.bddAbove_range _
    simp only [Lstat, Function.comp_apply]
    refine le_antisymm (ciSup_le fun j => ?_) (ciSup_le fun a => ?_)
    · by_cases hj : (j : ℕ) < p
      · have hTj : ∀ z : Fin p → ℝ, T z j = z ⟨(j : ℕ), hj⟩ := fun z => hT1 z j hj
        have hcj : T c j = c ⟨(j : ℕ), hj⟩ := hTj c
        have hsum : ∑ i : Fin N, ∫ ω, |T (Z i ω) j - T c j| ^ 3 ∂μ
            = ∑ i : Fin N, ∫ ω, |Z i ω ⟨(j : ℕ), hj⟩ - c ⟨(j : ℕ), hj⟩| ^ 3 ∂μ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hfun : (fun ω => |T (Z i ω) j - T c j| ^ 3)
              = fun ω => |Z i ω ⟨(j : ℕ), hj⟩ - c ⟨(j : ℕ), hj⟩| ^ 3 := by
            funext ω
            rw [hTj (Z i ω), hcj]
          rw [hfun]
        rw [hsum]
        exact le_ciSup hb _
      · have hj' : p ≤ (j : ℕ) := by have := j.isLt; omega
        let b : Fin p := ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩
        have hTj : ∀ z : Fin p → ℝ, T z j = -z b := fun z => hT2 z j hj'
        have hcj : T c j = -c b := hTj c
        have hsum : ∑ i : Fin N, ∫ ω, |T (Z i ω) j - T c j| ^ 3 ∂μ
            = ∑ i : Fin N, ∫ ω, |Z i ω b - c b| ^ 3 ∂μ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hfun : (fun ω => |T (Z i ω) j - T c j| ^ 3) = fun ω => |Z i ω b - c b| ^ 3 := by
            funext ω
            rw [hTj (Z i ω), hcj,
              show -Z i ω b - -c b = -(Z i ω b - c b) from by ring, abs_neg]
          rw [hfun]
        rw [hsum]
        exact le_ciSup hb b
    · let j : Fin (p + p) := ⟨(a : ℕ), by have := a.isLt; omega⟩
      have hjlt : (j : ℕ) < p := a.isLt
      have hTj : ∀ z : Fin p → ℝ, T z j = z a := fun z => hT1 z j hjlt
      have hcj : T c j = c a := hTj c
      have hsum : ∑ i : Fin N, ∫ ω, |Z i ω a - c a| ^ 3 ∂μ
          = ∑ i : Fin N, ∫ ω, |T (Z i ω) j - T c j| ^ 3 ∂μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hfun : (fun ω => |Z i ω a - c a| ^ 3) = fun ω => |T (Z i ω) j - T c j| ^ 3 := by
          funext ω
          rw [hTj (Z i ω), hcj]
        rw [hfun]
      rw [hsum]
      exact le_ciSup hb2 j
  have hMstatInv : ∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)),
      (∀ (i : Fin k) (j : Fin p), Measurable (fun ω => Z i ω j)) →
      ∀ (c : Fin p → ℝ) (lev : ℝ),
        Mstat μ (fun i ω => T (Z i ω)) (T c) lev = Mstat μ Z c lev := by
    intro k Z hZ c lev
    simp only [Mstat]
    congr 1
    exact Finset.sum_congr rfl fun i _ => htrunc (Z i) (hZ i) c lev
  have hTruncMono : ∀ (p' : ℕ), 1 ≤ p' → ∀ (Z : Ω → (Fin p' → ℝ)),
      (∀ j : Fin p', Measurable (fun ω => Z ω j)) → ∀ (c : Fin p' → ℝ) (lev lev' : ℝ),
      lev ≤ lev' → 0 < lev → truncThird μ Z c lev' ≤ truncThird μ Z c lev := by
    intro p' hp' Z hZ c lev lev' hle hpos
    have hgm : Measurable (fun ω => maxCoord (Z ω) c) := by
      have hy : ∀ j : Fin p', Measurable (fun ω => |Z ω j - c j|) := by
        intro j
        measurability
      simp only [maxCoord]
      exact Measurable.iSup hy
    have hg0 : ∀ ω, 0 ≤ maxCoord (Z ω) c := by
      intro ω
      have hb : BddAbove (Set.range fun j : Fin p' => |Z ω j - c j|) :=
        Finite.bddAbove_range _
      have h1 : |Z ω ⟨0, by omega⟩ - c ⟨0, by omega⟩| ≤ maxCoord (Z ω) c := by
        simpa only [maxCoord] using le_ciSup hb ⟨0, by omega⟩
      exact le_trans (abs_nonneg _) h1
    have hM3 : Measurable fun ω => maxCoord (Z ω) c ^ 3 := by measurability
    have hsetM : MeasurableSet {ω : Ω | lev < maxCoord (Z ω) c ∧ maxCoord (Z ω) c ≤ lev'} :=
      (measurableSet_lt measurable_const hgm).inter (measurableSet_le hgm measurable_const)
    simp only [truncThird]
    let F : Ω → ℝ := fun ω =>
      if lev' < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0
    let H : Ω → ℝ := fun ω =>
      if lev < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0
    let M : Ω → ℝ := fun ω =>
      if lev < maxCoord (Z ω) c ∧ maxCoord (Z ω) c ≤ lev' then maxCoord (Z ω) c ^ 3 else 0
    change ∫ ω, F ω ∂μ ≤ ∫ ω, H ω ∂μ
    have hFH : ∀ ω, H ω = F ω + M ω := by
      intro ω
      simp only [F, H, M]
      by_cases h1 : lev < maxCoord (Z ω) c
      · by_cases h2 : lev' < maxCoord (Z ω) c
        · rw [if_pos h1, if_pos h2,
            if_neg (fun hc : lev < maxCoord (Z ω) c ∧ maxCoord (Z ω) c ≤ lev' =>
              by linarith [hc.2, h2])]
          ring
        · rw [if_pos h1, if_neg h2, if_pos ⟨h1, by linarith⟩]
          ring
      · have h2 : maxCoord (Z ω) c ≤ lev' := by linarith
        rw [if_neg h1, if_neg (by linarith : ¬ lev' < maxCoord (Z ω) c),
          if_neg (fun hc : lev < maxCoord (Z ω) c ∧ maxCoord (Z ω) c ≤ lev' => h1 hc.1)]
        ring
    have hM0 : ∀ ω, 0 ≤ M ω := by
      intro ω
      simp only [M]
      by_cases hc : lev < maxCoord (Z ω) c ∧ maxCoord (Z ω) c ≤ lev'
      · rw [if_pos hc]
        exact pow_nonneg (hg0 ω) 3
      · rw [if_neg hc]
    have hH0 : ∀ ω, 0 ≤ H ω := by
      intro ω
      simp only [H]
      by_cases hc : lev < maxCoord (Z ω) c
      · rw [if_pos hc]
        exact pow_nonneg (hg0 ω) 3
      · rw [if_neg hc]
    have hMmeas : Measurable M := by
      have h : Measurable (fun ω : Ω =>
          if lev < maxCoord (Z ω) c ∧ maxCoord (Z ω) c ≤ lev' then maxCoord (Z ω) c ^ 3 else 0) :=
        Measurable.ite hsetM hM3 measurable_const
      simpa only [M] using h
    have hMint : Integrable M μ := by
      refine Integrable.of_bound hMmeas.aestronglyMeasurable (lev' ^ 3) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hM0 ω)]
      simp only [M]
      by_cases hc : lev < maxCoord (Z ω) c ∧ maxCoord (Z ω) c ≤ lev'
      · rw [if_pos hc]
        have hA : 0 ≤ maxCoord (Z ω) c := hg0 ω
        have hB : 0 ≤ lev' := le_trans hpos.le hle
        have hs2 : maxCoord (Z ω) c * maxCoord (Z ω) c ≤ lev' * lev' :=
          mul_le_mul hc.2 hc.2 hA hB
        have hs3 : maxCoord (Z ω) c * maxCoord (Z ω) c * maxCoord (Z ω) c
            ≤ lev' * lev' * lev' := mul_le_mul hs2 hc.2 hA (mul_nonneg hB hB)
        calc maxCoord (Z ω) c ^ 3
            = maxCoord (Z ω) c * maxCoord (Z ω) c * maxCoord (Z ω) c := by ring
          _ ≤ lev' * lev' * lev' := hs3
          _ = lev' ^ 3 := by ring
      · rw [if_neg hc]
        exact pow_nonneg (by linarith : (0 : ℝ) ≤ lev') 3
    by_cases hH : Integrable H μ
    · have hFH' : ∀ ω, F ω = H ω - M ω := by
        intro ω
        have := hFH ω
        linarith
      have e1 : ∫ ω, F ω ∂μ = ∫ ω, (H ω - M ω) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hFH')
      have e2 : ∫ ω, (H ω - M ω) ∂μ = ∫ ω, H ω ∂μ - ∫ ω, M ω ∂μ :=
        integral_sub hH hMint
      have h3 : 0 ≤ ∫ ω, M ω ∂μ := integral_nonneg hM0
      rw [e1, e2]
      linarith
    · have hH0' : ∫ ω, H ω ∂μ = 0 := integral_undef hH
      by_cases hF : Integrable F μ
      · have e1 : ∫ ω, H ω ∂μ = ∫ ω, (F ω + M ω) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => hFH ω)
        have e2 : ∫ ω, (F ω + M ω) ∂μ = ∫ ω, F ω ∂μ + ∫ ω, M ω ∂μ :=
          integral_add hF hMint
        have h3 : 0 ≤ ∫ ω, M ω ∂μ := integral_nonneg hM0
        rw [hH0'] at e1
        linarith
      · rw [integral_undef hF, hH0']
  have hMstatMono : ∀ (p' : ℕ), 1 ≤ p' → ∀ (k : ℕ) (Z : Fin k → Ω → (Fin p' → ℝ)),
      (∀ (i : Fin k) (j : Fin p'), Measurable (fun ω => Z i ω j)) →
      ∀ (c : Fin p' → ℝ) (lev lev' : ℝ), lev ≤ lev' → 0 < lev →
        Mstat μ Z c lev' ≤ Mstat μ Z c lev := by
    intro p' hp' k Z hZ c lev lev' hle hpos
    simp only [Mstat]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
    exact Finset.sum_le_sum fun i _ => hTruncMono p' hp' (Z i) (hZ i) c lev lev' hle hpos
  have hmeasT : ∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)),
      (∀ (i : Fin k) (j : Fin p), Measurable (fun ω => Z i ω j)) →
      ∀ (i : Fin k) (j : Fin (p + p)), Measurable (fun ω => T (Z i ω) j) := by
    intro k Z hZ i j
    by_cases hj : (j : ℕ) < p
    · have h1 : (fun ω => T (Z i ω) j) = fun ω => Z i ω ⟨(j : ℕ), hj⟩ :=
        funext fun ω => hT1 (Z i ω) j hj
      rw [h1]
      exact hZ i ⟨(j : ℕ), hj⟩
    · have hj' : p ≤ (j : ℕ) := by have := j.isLt; omega
      let b : Fin p := ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩
      have h1 : (fun ω => T (Z i ω) j) = fun ω => -Z i ω b :=
        funext fun ω => hT2 (Z i ω) j hj'
      rw [h1]
      exact (hZ i b).neg
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hlogDpos : 0 < Real.log ((p + p : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < p + p))
  have hlogD : Real.log ((p + p : ℕ) : ℝ) ≤ 2 * Real.log (p : ℝ) := by
    have hcast : ((p + p : ℕ) : ℝ) = (p : ℝ) + (p : ℝ) := by push_cast; ring
    have hle : ((p + p : ℕ) : ℝ) ≤ (p : ℝ) * (p : ℝ) := by
      rw [hcast]
      nlinarith
    have h1 : Real.log ((p + p : ℕ) : ℝ) ≤ Real.log ((p : ℝ) * (p : ℝ)) :=
      Real.log_le_log (by positivity) hle
    have h2 : Real.log ((p : ℝ) * (p : ℝ)) = Real.log (p : ℝ) + Real.log (p : ℝ) :=
      Real.log_mul (by positivity) (by positivity)
    linarith
  refine ⟨hmax, ?_, ?_, hL n X μX, hL m Y μY, ?_, ?_, ?_, ?_⟩
  · intro Z hZ c lev
    exact htrunc Z hZ c lev
  · intro k Z hZ c lev
    exact ⟨fun i => htrunc (Z i) (hZ i) c lev, hMstatInv k Z hZ c lev⟩
  · intro Z hZ c lev lev' hle hpos
    exact hTruncMono p (by omega) Z hZ c lev lev' hle hpos
  · intro k Z hZ c lev lev' hle hpos
    exact hMstatMono p (by omega) k Z hZ c lev lev' hle hpos
  · intro phi1 hphi1
    have hphi1pos : 0 < phi1 := by linarith
    have hsqrtn : 0 < Real.sqrt (n : ℝ) := by positivity
    let Lp : ℝ := Real.sqrt (n : ℝ) / (4 * phi1 * Real.log (p : ℝ))
    let LD : ℝ := Real.sqrt (n : ℝ) / (4 * (phi1 / 2) * Real.log ((p + p : ℕ) : ℝ))
    have hd1 : 0 < 4 * phi1 * Real.log (p : ℝ) :=
      mul_pos (mul_pos (by norm_num) hphi1pos) hlogp
    have hd2 : 0 < 4 * (phi1 / 2) * Real.log ((p + p : ℕ) : ℝ) :=
      mul_pos (mul_pos (by norm_num) (by linarith)) hlogDpos
    have hlev : Lp ≤ LD := by
      show Real.sqrt (n : ℝ) / (4 * phi1 * Real.log (p : ℝ))
        ≤ Real.sqrt (n : ℝ) / (4 * (phi1 / 2) * Real.log ((p + p : ℕ) : ℝ))
      have hden : 4 * (phi1 / 2) * Real.log ((p + p : ℕ) : ℝ) ≤ 4 * phi1 * Real.log (p : ℝ) := by
        nlinarith [hlogD, hphi1pos]
      exact div_le_div_of_nonneg_left hsqrtn.le hd2 hden
    have hlevpos : 0 < Lp := by
      show 0 < Real.sqrt (n : ℝ) / (4 * phi1 * Real.log (p : ℝ))
      exact div_pos hsqrtn hd1
    simp only [MstatN]
    change Mstat μ (fun i => T ∘ X i) (T μX) LD + Mstat μ (fun i => T ∘ F i) (T μX) LD
      ≤ Mstat μ X μX Lp + Mstat μ F μX Lp
    have hm1 : Mstat μ (fun i => T ∘ X i) (T μX) LD
        ≤ Mstat μ (fun i => T ∘ X i) (T μX) Lp :=
      hMstatMono (p + p) (by omega) n (fun i => T ∘ X i)
        (fun i j => hmeasT n X hXm i j) (T μX) Lp LD hlev hlevpos
    have hm2 : Mstat μ (fun i => T ∘ F i) (T μX) LD
        ≤ Mstat μ (fun i => T ∘ F i) (T μX) Lp :=
      hMstatMono (p + p) (by omega) n (fun i => T ∘ F i)
        (fun i j => hmeasT n F hFm i j) (T μX) Lp LD hlev hlevpos
    have hi1 : Mstat μ (fun i => T ∘ X i) (T μX) Lp = Mstat μ X μX Lp :=
      hMstatInv n X hXm μX Lp
    have hi2 : Mstat μ (fun i => T ∘ F i) (T μX) Lp = Mstat μ F μX Lp :=
      hMstatInv n F hFm μX Lp
    linarith
  · intro phi2 hphi2
    by_cases hd0 : d = 0
    · simp only [MstatM]
      rw [if_pos hd0, if_pos hd0]
    · have hphi2pos : 0 < phi2 := by linarith
      have hdpos : 0 < |d| := abs_pos.mpr hd0
      have hsqrtm : 0 < Real.sqrt (m : ℝ) := by positivity
      let Lp : ℝ := Real.sqrt (m : ℝ) / (4 * |d| * phi2 * Real.log (p : ℝ))
      let LD : ℝ := Real.sqrt (m : ℝ) / (4 * |d| * (phi2 / 2) * Real.log ((p + p : ℕ) : ℝ))
      have hd1 : 0 < 4 * |d| * phi2 * Real.log (p : ℝ) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hdpos) hphi2pos) hlogp
      have hd2 : 0 < 4 * |d| * (phi2 / 2) * Real.log ((p + p : ℕ) : ℝ) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hdpos) (by linarith)) hlogDpos
      have hlev : Lp ≤ LD := by
        show Real.sqrt (m : ℝ) / (4 * |d| * phi2 * Real.log (p : ℝ))
          ≤ Real.sqrt (m : ℝ) / (4 * |d| * (phi2 / 2) * Real.log ((p + p : ℕ) : ℝ))
        have hden : 4 * |d| * (phi2 / 2) * Real.log ((p + p : ℕ) : ℝ)
            ≤ 4 * |d| * phi2 * Real.log (p : ℝ) := by
          have hmain : 2 * phi2 * Real.log ((p + p : ℕ) : ℝ) ≤ 4 * phi2 * Real.log (p : ℝ) := by
            nlinarith [hlogD, hphi2pos]
          have hmul : |d| * (2 * phi2 * Real.log ((p + p : ℕ) : ℝ))
              ≤ |d| * (4 * phi2 * Real.log (p : ℝ)) :=
            mul_le_mul_of_nonneg_left hmain hdpos.le
          nlinarith [hmul]
        exact div_le_div_of_nonneg_left hsqrtm.le hd2 hden
      have hlevpos : 0 < Lp := by
        show 0 < Real.sqrt (m : ℝ) / (4 * |d| * phi2 * Real.log (p : ℝ))
        exact div_pos hsqrtm hd1
      simp only [MstatM, if_neg hd0]
      change Mstat μ (fun i => T ∘ Y i) (T μY) LD + Mstat μ (fun i => T ∘ G i) (T μY) LD
        ≤ Mstat μ Y μY Lp + Mstat μ G μY Lp
      have hm1 : Mstat μ (fun i => T ∘ Y i) (T μY) LD
          ≤ Mstat μ (fun i => T ∘ Y i) (T μY) Lp :=
        hMstatMono (p + p) (by omega) m (fun i => T ∘ Y i)
          (fun i j => hmeasT m Y hYm i j) (T μY) Lp LD hlev hlevpos
      have hm2 : Mstat μ (fun i => T ∘ G i) (T μY) LD
          ≤ Mstat μ (fun i => T ∘ G i) (T μY) Lp :=
        hMstatMono (p + p) (by omega) m (fun i => T ∘ G i)
          (fun i j => hmeasT m G hGm i j) (T μY) Lp LD hlev hlevpos
      have hi1 : Mstat μ (fun i => T ∘ Y i) (T μY) Lp = Mstat μ Y μY Lp :=
        hMstatInv m Y hYm μY Lp
      have hi2 : Mstat μ (fun i => T ∘ G i) (T μY) Lp = Mstat μ G μY Lp :=
        hMstatInv m G hGm μY Lp
      linarith
  /- @proof-region region.target-node.session.8e2c3d6713ea465b end -/

end Statlib.Imported

end

