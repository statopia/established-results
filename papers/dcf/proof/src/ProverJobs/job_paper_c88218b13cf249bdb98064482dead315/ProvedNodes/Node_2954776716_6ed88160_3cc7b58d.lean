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
theorem statopia_math_node_2954776716_6ed88160 : ∀ (n m p : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 2 ≤ p)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
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
      (∀ (Z : Ω → (Fin p → ℝ)), (∀ j : Fin p, Measurable (fun ω => Z ω j)) →
        ∀ (c : Fin p → ℝ) (lev : ℝ),
          truncThird μ (fun ω => T (Z ω)) (T c) lev = truncThird μ Z c lev) ∧
      (∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)),
        (∀ (i : Fin k) (j : Fin p), Measurable (fun ω => Z i ω j)) →
        ∀ (c : Fin p → ℝ) (lev : ℝ),
          (∀ i : Fin k,
              truncThird μ (fun ω => T (Z i ω)) (T c) lev = truncThird μ (Z i) c lev) ∧
            Mstat μ (fun i ω => T (Z i ω)) (T c) lev = Mstat μ Z c lev) ∧
      Lstat μ (fun i ω => T (X i ω)) (T μX) = Lstat μ X μX ∧
      Lstat μ (fun i ω => T (Y i ω)) (T μY) = Lstat μ Y μY ∧
      (∀ (Z : Ω → (Fin p → ℝ)), (∀ j : Fin p, Measurable (fun ω => Z ω j)) →
        ∀ (c : Fin p → ℝ) (lev lev' : ℝ), lev ≤ lev' → 0 < lev →
          truncThird μ Z c lev' ≤ truncThird μ Z c lev) ∧
      (∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)),
        (∀ (i : Fin k) (j : Fin p), Measurable (fun ω => Z i ω j)) →
        ∀ (c : Fin p → ℝ) (lev lev' : ℝ), lev ≤ lev' → 0 < lev →
          Mstat μ Z c lev' ≤ Mstat μ Z c lev) ∧
      (∀ (phi1 : ℝ), 1 ≤ phi1 →
        MstatN μ (fun i ω => T (X i ω)) (fun i ω => T (F i ω)) (T μX) (phi1 / 2)
          ≤ MstatN μ X F μX phi1) ∧
      (∀ (phi2 : ℝ), 1 ≤ phi2 →
        MstatM μ (fun i ω => T (Y i ω)) (fun i ω => T (G i ω)) (T μY) (phi2 / 2) d
          ≤ MstatM μ Y G μY phi2 d) := by
  /- @proof-region region.target-node.session.186b0d9c763d53a9 begin -/
  intro n m p hn hm hp Ω instΩ μ instμ μX μY d X F Y G hX3 hF3 hY3 hG3 hXm hFm hYm hGm
  let T : (Fin p → ℝ) → (Fin (p + p) → ℝ) := fun z j =>
    if h : (j : ℕ) < p then z ⟨(j : ℕ), h⟩
    else -z ⟨(j : ℕ) - p, by have hj := j.isLt; omega⟩
  change ((∀ z c : Fin p → ℝ, maxCoord (T z) (T c) = maxCoord z c) ∧
      (∀ (Z : Ω → (Fin p → ℝ)), (∀ j : Fin p, Measurable (fun ω => Z ω j)) →
        ∀ (c : Fin p → ℝ) (lev : ℝ),
          truncThird μ (fun ω => T (Z ω)) (T c) lev = truncThird μ Z c lev) ∧
      (∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)),
        (∀ (i : Fin k) (j : Fin p), Measurable (fun ω => Z i ω j)) →
        ∀ (c : Fin p → ℝ) (lev : ℝ),
          (∀ i : Fin k,
              truncThird μ (fun ω => T (Z i ω)) (T c) lev = truncThird μ (Z i) c lev) ∧
            Mstat μ (fun i ω => T (Z i ω)) (T c) lev = Mstat μ Z c lev) ∧
      Lstat μ (fun i ω => T (X i ω)) (T μX) = Lstat μ X μX ∧
      Lstat μ (fun i ω => T (Y i ω)) (T μY) = Lstat μ Y μY ∧
      (∀ (Z : Ω → (Fin p → ℝ)), (∀ j : Fin p, Measurable (fun ω => Z ω j)) →
        ∀ (c : Fin p → ℝ) (lev lev' : ℝ), lev ≤ lev' → 0 < lev →
          truncThird μ Z c lev' ≤ truncThird μ Z c lev) ∧
      (∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)),
        (∀ (i : Fin k) (j : Fin p), Measurable (fun ω => Z i ω j)) →
        ∀ (c : Fin p → ℝ) (lev lev' : ℝ), lev ≤ lev' → 0 < lev →
          Mstat μ Z c lev' ≤ Mstat μ Z c lev) ∧
      (∀ (phi1 : ℝ), 1 ≤ phi1 →
        MstatN μ (fun i ω => T (X i ω)) (fun i ω => T (F i ω)) (T μX) (phi1 / 2)
          ≤ MstatN μ X F μX phi1) ∧
      (∀ (phi2 : ℝ), 1 ≤ phi2 →
        MstatM μ (fun i ω => T (Y i ω)) (fun i ω => T (G i ω)) (T μY) (phi2 / 2) d
          ≤ MstatM μ Y G μY phi2 d))
  have hlow : ∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : (j : ℕ) < p),
      T z j = z ⟨(j : ℕ), hj⟩ := by
    intro z j hj
    exact dif_pos hj
  have hhigh : ∀ (z : Fin p → ℝ) (j : Fin (p + p)) (hj : p ≤ (j : ℕ)),
      T z j = -z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ := by
    intro z j hj
    exact dif_neg (by omega)
  have dup_sup : ∀ (F : Fin (p + p) → ℝ) (G : Fin p → ℝ),
      (∀ (j : Fin (p + p)) (hj : (j : ℕ) < p), F j = G ⟨(j : ℕ), hj⟩) →
      (∀ (j : Fin (p + p)) (hj : p ≤ (j : ℕ)),
        F j = G ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩) →
      (⨆ j : Fin (p + p), F j) = ⨆ a : Fin p, G a := by
    intro F G hF1 hF2
    have hset : Set.range F = Set.range G := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        by_cases hj : (j : ℕ) < p
        · exact ⟨⟨(j : ℕ), hj⟩, (hF1 j hj).symm⟩
        · have hj' : p ≤ (j : ℕ) := by omega
          exact ⟨⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩, (hF2 j hj').symm⟩
      · rintro ⟨a, rfl⟩
        exact ⟨⟨(a : ℕ), by have := a.isLt; omega⟩,
          hF1 ⟨(a : ℕ), by have := a.isLt; omega⟩ (by have := a.isLt; omega)⟩
    exact congrArg sSup hset
  have h1 : ∀ z c : Fin p → ℝ, maxCoord (T z) (T c) = maxCoord z c := by
    intro z c
    exact dup_sup (fun j : Fin (p + p) => |T z j - T c j|) (fun a : Fin p => |z a - c a|)
      (fun j hj => by
        simp only []
        rw [hlow z j hj, hlow c j hj])
      (fun j hj => by
        simp only []
        rw [hhigh z j hj, hhigh c j hj]
        rw [show (-z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩) - -c ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩
            = -(z ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ - c ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩) from by ring]
        rw [abs_neg])
  have h2 : ∀ (Z : Ω → (Fin p → ℝ)), (∀ j : Fin p, Measurable (fun ω => Z ω j)) →
      ∀ (c : Fin p → ℝ) (lev : ℝ),
        truncThird μ (fun ω => T (Z ω)) (T c) lev = truncThird μ Z c lev := by
    intro Z hZ c lev
    simp only [truncThird]
    congr 1
    funext ω
    rw [h1 (Z ω) c]
  have h3 : ∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)),
      (∀ (i : Fin k) (j : Fin p), Measurable (fun ω => Z i ω j)) →
      ∀ (c : Fin p → ℝ) (lev : ℝ),
        (∀ i : Fin k, truncThird μ (fun ω => T (Z i ω)) (T c) lev = truncThird μ (Z i) c lev) ∧
          Mstat μ (fun i ω => T (Z i ω)) (T c) lev = Mstat μ Z c lev := by
    intro k Z hZ c lev
    have htri : ∀ i : Fin k, truncThird μ (fun ω => T (Z i ω)) (T c) lev = truncThird μ (Z i) c lev :=
      fun i => h2 (Z i) (fun j => hZ i j) c lev
    refine ⟨htri, ?_⟩
    simp only [Mstat]
    refine congrArg (fun t => (k : ℝ)⁻¹ * t) ?_
    exact Finset.sum_congr rfl fun i _ => htri i
  have h4 : Lstat μ (fun i ω => T (X i ω)) (T μX) = Lstat μ X μX := by
    simp only [Lstat]
    let F : Fin (p + p) → ℝ := fun j => (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, |T (X i ω) j - T μX j| ^ 3 ∂μ
    let G : Fin p → ℝ := fun a => (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, |X i ω a - μX a| ^ 3 ∂μ
    change (⨆ j : Fin (p + p), F j) = ⨆ a : Fin p, G a
    refine dup_sup F G ?_ ?_
    · intro j hj
      dsimp only [F, G]
      rw [show (∑ i : Fin n, ∫ ω, |T (X i ω) j - T μX j| ^ 3 ∂μ)
          = ∑ i : Fin n, ∫ ω, |X i ω ⟨(j : ℕ), hj⟩ - μX ⟨(j : ℕ), hj⟩| ^ 3 ∂μ from by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        funext ω
        rw [hlow (X i ω) j hj, hlow μX j hj]]
    · intro j hj
      dsimp only [F, G]
      rw [show (∑ i : Fin n, ∫ ω, |T (X i ω) j - T μX j| ^ 3 ∂μ)
          = ∑ i : Fin n, ∫ ω, |X i ω ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ - μX ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩| ^ 3 ∂μ from by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        funext ω
        rw [hhigh (X i ω) j hj, hhigh μX j hj]
        rw [show (-X i ω ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩) - -μX ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩
            = -(X i ω ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ - μX ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩) from by ring]
        rw [abs_neg]]
  have h5 : Lstat μ (fun i ω => T (Y i ω)) (T μY) = Lstat μ Y μY := by
    simp only [Lstat]
    let F : Fin (p + p) → ℝ := fun j => (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, |T (Y i ω) j - T μY j| ^ 3 ∂μ
    let G : Fin p → ℝ := fun a => (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ ω, |Y i ω a - μY a| ^ 3 ∂μ
    change (⨆ j : Fin (p + p), F j) = ⨆ a : Fin p, G a
    refine dup_sup F G ?_ ?_
    · intro j hj
      dsimp only [F, G]
      rw [show (∑ i : Fin m, ∫ ω, |T (Y i ω) j - T μY j| ^ 3 ∂μ)
          = ∑ i : Fin m, ∫ ω, |Y i ω ⟨(j : ℕ), hj⟩ - μY ⟨(j : ℕ), hj⟩| ^ 3 ∂μ from by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        funext ω
        rw [hlow (Y i ω) j hj, hlow μY j hj]]
    · intro j hj
      dsimp only [F, G]
      rw [show (∑ i : Fin m, ∫ ω, |T (Y i ω) j - T μY j| ^ 3 ∂μ)
          = ∑ i : Fin m, ∫ ω, |Y i ω ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ - μY ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩| ^ 3 ∂μ from by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        funext ω
        rw [hhigh (Y i ω) j hj, hhigh μY j hj]
        rw [show (-Y i ω ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩) - -μY ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩
            = -(Y i ω ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩ - μY ⟨(j : ℕ) - p, by have hk := j.isLt; omega⟩) from by ring]
        rw [abs_neg]]
  have h6 : ∀ (Z : Ω → (Fin p → ℝ)), (∀ j : Fin p, Measurable (fun ω => Z ω j)) →
      ∀ (c : Fin p → ℝ) (lev lev' : ℝ), lev ≤ lev' → 0 < lev →
        truncThird μ Z c lev' ≤ truncThird μ Z c lev := by
    intro Z hZm c lev lev' hle hpos
    have hmem : ∀ (ω : Ω) (j : Fin p), |Z ω j - c j| ≤ maxCoord (Z ω) c := by
      intro ω j
      refine le_csSup ?_ ⟨j, rfl⟩
      refine ⟨∑ j : Fin p, |Z ω j - c j|, ?_⟩
      rintro x ⟨i, rfl⟩
      exact Finset.single_le_sum (fun j _ => abs_nonneg (Z ω j - c j)) (Finset.mem_univ i)
    have hgm : Measurable (fun ω => maxCoord (Z ω) c) := by
      refine measurable_of_Iic (fun x => ?_)
      have hset : (fun ω => maxCoord (Z ω) c) ⁻¹' Set.Iic x
          = ⋂ j : Fin p, {ω : Ω | |Z ω j - c j| ≤ x} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_setOf_eq]
        exact ⟨fun h j => le_trans (hmem ω j) h,
          fun h => Real.iSup_le h (le_trans (abs_nonneg _) (h ⟨0, by omega⟩))⟩
      rw [hset]
      exact MeasurableSet.iInter
        (fun j => ((hZm j).sub measurable_const).abs measurableSet_Iic)
    have hcube : Measurable (fun ω : Ω => (maxCoord (Z ω) c) ^ 3) := by
      have h2 : Measurable (fun ω : Ω => (maxCoord (Z ω) c) * (maxCoord (Z ω) c)) := hgm.mul hgm
      have h3 : Measurable
          (fun ω : Ω => (maxCoord (Z ω) c) * (maxCoord (Z ω) c) * (maxCoord (Z ω) c)) :=
        h2.mul hgm
      have hfun : (fun ω : Ω => (maxCoord (Z ω) c) * (maxCoord (Z ω) c) * (maxCoord (Z ω) c))
          = fun ω : Ω => (maxCoord (Z ω) c) ^ 3 := by
        funext ω
        ring
      rwa [hfun] at h3
    have htr : ∀ (L : ℝ), Measurable
        (fun ω : Ω => if L < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else (0:ℝ)) := by
      intro L
      refine measurable_of_Iic (fun x => ?_)
      have hset : (fun ω : Ω =>
            if L < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else (0:ℝ)) ⁻¹' Set.Iic x
          = {ω : Ω | L < maxCoord (Z ω) c ∧ maxCoord (Z ω) c ^ 3 ≤ x}
            ∪ ({ω : Ω | maxCoord (Z ω) c ≤ L} ∩ {ω : Ω | (0:ℝ) ≤ x}) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
        by_cases h1 : L < maxCoord (Z ω) c
        · rw [if_pos h1]
          have h2 : ¬ maxCoord (Z ω) c ≤ L := not_le.mpr h1
          simp [h1, h2]
        · rw [if_neg h1]
          have h2 : maxCoord (Z ω) c ≤ L := le_of_not_gt h1
          simp [h1, h2]
      have hconst : MeasurableSet {ω : Ω | (0:ℝ) ≤ x} := by
        by_cases hx : (0:ℝ) ≤ x
        · have hun : {ω : Ω | (0:ℝ) ≤ x} = Set.univ := by
            ext ω
            simp [hx]
          rw [hun]
          exact MeasurableSet.univ
        · have hem : {ω : Ω | (0:ℝ) ≤ x} = ∅ := by
            ext ω
            simp [hx]
          rw [hem]
          exact MeasurableSet.empty
      rw [hset]
      exact MeasurableSet.union
        (MeasurableSet.inter (hgm measurableSet_Ioi) (hcube measurableSet_Iic))
        (MeasurableSet.inter (hgm measurableSet_Iic) hconst)
    have hpt : ∀ ω : Ω, (if lev' < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0)
        ≤ (if lev < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0) := by
      intro ω
      by_cases h1 : lev' < maxCoord (Z ω) c
      · rw [if_pos h1, if_pos (lt_of_le_of_lt hle h1)]
      · rw [if_neg h1]
        by_cases h2 : lev < maxCoord (Z ω) c
        · rw [if_pos h2]
          exact pow_nonneg (le_of_lt (lt_trans hpos h2)) 3
        · rw [if_neg h2]
    have hnn : ∀ ω : Ω, 0 ≤ (if lev' < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0) := by
      intro ω
      by_cases h1 : lev' < maxCoord (Z ω) c
      · rw [if_pos h1]
        exact pow_nonneg (le_of_lt (lt_trans (lt_of_lt_of_le hpos hle) h1)) 3
      · rw [if_neg h1]
    simp only [truncThird]
    by_cases hInt : Integrable
        (fun ω => if lev < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0) μ
    · exact integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hInt
        (Filter.Eventually.of_forall hpt)
    · rw [integral_undef hInt]
      have hzero : ∫ ω, (if lev' < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0) ∂μ = 0 := by
        by_contra hne
        have hfint : Integrable
            (fun ω => if lev' < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0) μ := by
          by_contra hc
          exact hne (integral_undef hc)
        have hmnn : ∀ ω : Ω, 0 ≤ (if lev < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0)
            - (if lev' < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0) := by
          intro ω
          have h1 := hpt ω
          linarith
        have hmbd : ∀ ω : Ω, (if lev < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0)
            - (if lev' < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0) ≤ lev' ^ 3 := by
          intro ω
          by_cases h1 : lev' < maxCoord (Z ω) c
          · have h2 : lev < maxCoord (Z ω) c := lt_of_le_of_lt hle h1
            rw [if_pos h2, if_pos h1]
            have h0 : (0:ℝ) ≤ lev' ^ 3 := pow_nonneg (le_of_lt (lt_of_lt_of_le hpos hle)) 3
            linarith
          · rw [if_neg h1]
            have hgnn : (0:ℝ) ≤ maxCoord (Z ω) c := le_trans (abs_nonneg _) (hmem ω ⟨0, by omega⟩)
            have hgle : maxCoord (Z ω) c ≤ lev' := le_of_not_gt h1
            have hcu : maxCoord (Z ω) c ^ 3 ≤ lev' ^ 3 := by gcongr
            have h0 : (0:ℝ) ≤ lev' ^ 3 := le_trans (pow_nonneg hgnn 3) hcu
            by_cases h2 : lev < maxCoord (Z ω) c
            · rw [if_pos h2]
              linarith
            · rw [if_neg h2]
              linarith
        have hmint : Integrable
            (fun ω => (if lev < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0)
              - (if lev' < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0)) μ := by
          refine Integrable.of_bound ?_ (lev' ^ 3) ?_
          · exact ((htr lev).sub (htr lev')).aestronglyMeasurable
          · filter_upwards with ω
            rw [Real.norm_eq_abs, abs_of_nonneg (hmnn ω)]
            exact hmbd ω
        have hcomb : Integrable
            (fun ω => (if lev' < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0)
              + ((if lev < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0)
                - (if lev' < maxCoord (Z ω) c then maxCoord (Z ω) c ^ 3 else 0))) μ :=
          hfint.add hmint
        exact hInt (hcomb.congr (by filter_upwards with ω; ring))
      rw [hzero]
  have h7 : ∀ (k : ℕ) (Z : Fin k → Ω → (Fin p → ℝ)),
      (∀ (i : Fin k) (j : Fin p), Measurable (fun ω => Z i ω j)) →
      ∀ (c : Fin p → ℝ) (lev lev' : ℝ), lev ≤ lev' → 0 < lev →
        Mstat μ Z c lev' ≤ Mstat μ Z c lev := by
    intro k Z hZ c lev lev' hle hpos
    simp only [Mstat]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Finset.sum_le_sum fun i _ => h6 (Z i) (fun j => hZ i j) c lev lev' hle hpos
  have hPa : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlogpp : Real.log (((p + p : ℕ)) : ℝ) = Real.log 2 + Real.log (p : ℝ) := by
    have hpp : (((p + p : ℕ)) : ℝ) = 2 * (p : ℝ) := by push_cast; ring
    rw [hpp]
    exact Real.log_mul (by norm_num) (ne_of_gt hPa)
  have hlog2 : Real.log 2 ≤ Real.log (p : ℝ) := by
    refine Real.log_le_log (by norm_num) ?_
    have hp' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  have hlogineq : Real.log (((p + p : ℕ)) : ℝ) ≤ 2 * Real.log (p : ℝ) := by
    rw [hlogpp]
    linarith
  have hlogp_pos : (0:ℝ) < Real.log (p : ℝ) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog2
  have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD_pos : (0:ℝ) < Real.log (((p + p : ℕ)) : ℝ) := by
    rw [hlogpp]
    linarith
  have hden_le : ∀ (a phi : ℝ), 0 ≤ a → 1 ≤ phi →
      4 * a * (phi / 2) * Real.log (((p + p : ℕ)) : ℝ) ≤ 4 * a * phi * Real.log (p : ℝ) := by
    intro a phi ha hphi
    have h1 : (0:ℝ) ≤ a * phi := mul_nonneg ha (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hlogineq h1
    nlinarith [h2]
  have hlev_le : ∀ (c a phi : ℝ), 0 < c → 0 < a → 1 ≤ phi →
      c / (4 * a * phi * Real.log (p : ℝ))
        ≤ c / (4 * a * (phi / 2) * Real.log (((p + p : ℕ)) : ℝ)) := by
    intro c a phi hc ha hphi
    have hφ0 : (0:ℝ) < phi := lt_of_lt_of_le zero_lt_one hphi
    have hd : (0:ℝ) < 4 * a * (phi / 2) * Real.log (((p + p : ℕ)) : ℝ) :=
      mul_pos (mul_pos (mul_pos (by norm_num) ha) (by linarith)) hlogD_pos
    have hmain : 4 * a * (phi / 2) * Real.log (((p + p : ℕ)) : ℝ)
        ≤ 4 * a * phi * Real.log (p : ℝ) := hden_le a phi ha.le hphi
    have hinv : (4 * a * phi * Real.log (p : ℝ))⁻¹
        ≤ (4 * a * (phi / 2) * Real.log (((p + p : ℕ)) : ℝ))⁻¹ := by
      gcongr
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hc.le
  have h8 : ∀ (phi1 : ℝ), 1 ≤ phi1 →
      MstatN μ (fun i ω => T (X i ω)) (fun i ω => T (F i ω)) (T μX) (phi1 / 2)
        ≤ MstatN μ X F μX phi1 := by
    intro phi1 hphi1
    let Lp : ℝ := Real.sqrt (n : ℝ) / (4 * phi1 * Real.log (p : ℝ))
    let LD : ℝ := Real.sqrt (n : ℝ) / (4 * (phi1 / 2) * Real.log (((p + p : ℕ)) : ℝ))
    have hsqrtn : (0:ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hlev : Lp ≤ LD := by
      dsimp only [Lp, LD]
      have h := hlev_le (Real.sqrt (n : ℝ)) 1 phi1 hsqrtn zero_lt_one hphi1
      simpa using h
    have hpos : (0:ℝ) < Lp := by
      dsimp only [Lp]
      refine div_pos hsqrtn ?_
      exact mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hphi1)) hlogp_pos
    have hX : Mstat μ (fun i ω => T (X i ω)) (T μX) LD ≤ Mstat μ X μX Lp := by
      rw [(h3 n X hXm μX LD).2]
      exact h7 n X hXm μX Lp LD hlev hpos
    have hF : Mstat μ (fun i ω => T (F i ω)) (T μX) LD ≤ Mstat μ F μX Lp := by
      rw [(h3 n F hFm μX LD).2]
      exact h7 n F hFm μX Lp LD hlev hpos
    simp only [MstatN]
    exact add_le_add hX hF
  have h9 : ∀ (phi2 : ℝ), 1 ≤ phi2 →
      MstatM μ (fun i ω => T (Y i ω)) (fun i ω => T (G i ω)) (T μY) (phi2 / 2) d
        ≤ MstatM μ Y G μY phi2 d := by
    intro phi2 hphi2
    by_cases hd : d = 0
    · simp only [MstatM, if_pos hd]
      exact le_refl 0
    · have hsqrtm : (0:ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
      have hdpos : (0:ℝ) < |d| := abs_pos.mpr hd
      let Lp : ℝ := Real.sqrt (m : ℝ) / (4 * |d| * phi2 * Real.log (p : ℝ))
      let LD : ℝ := Real.sqrt (m : ℝ) / (4 * |d| * (phi2 / 2) * Real.log (((p + p : ℕ)) : ℝ))
      have hlev : Lp ≤ LD := by
        dsimp only [Lp, LD]
        exact hlev_le (Real.sqrt (m : ℝ)) |d| phi2 hsqrtm hdpos hphi2
      have hpos : (0:ℝ) < Lp := by
        dsimp only [Lp]
        refine div_pos hsqrtm ?_
        exact mul_pos (mul_pos (mul_pos (by norm_num) hdpos)
          (lt_of_lt_of_le zero_lt_one hphi2)) hlogp_pos
      have hY : Mstat μ (fun i ω => T (Y i ω)) (T μY) LD ≤ Mstat μ Y μY Lp := by
        rw [(h3 m Y hYm μY LD).2]
        exact h7 m Y hYm μY Lp LD hlev hpos
      have hG : Mstat μ (fun i ω => T (G i ω)) (T μY) LD ≤ Mstat μ G μY Lp := by
        rw [(h3 m G hGm μY LD).2]
        exact h7 m G hGm μY Lp LD hlev hpos
      simp only [MstatM, if_neg hd]
      exact add_le_add hY hG
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  /- @proof-region region.target-node.session.186b0d9c763d53a9 end -/

end Statlib.Imported

end

