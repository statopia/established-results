import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_2d09ea10ba632270c6b5
import ProverJobs.ResidualE2ESupport20261106.M_67308435b5a60e68699f
import ProverJobs.ResidualE2ESupport20261106.ExternalNodes.Node_4e757cd702eee1ecc4cb

namespace PaperProofTasks.ResidualE2ESupport20261106


open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2235047215_a757c0bb : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (p Kt : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hKt : 0 < Kt)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hMeasXi : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hMeasMask : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hIntThird : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun ω => |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3) μ)
    (hbudget : (∑ i : Fin m, ∑ j : Fin n,
        ∫ ω, |maskedScaled p (Xi ω) (Mask ω) i j| ^ 3 ∂μ)
      ≤ ((m : ℝ) + (n : ℝ)) * (24 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹)),
    let Zfm : Fin (m * n) → Ω × (Fin m → Fin n → ℝ) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
      fun k x => Matrix.of fun u v =>
        ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
          (Matrix.of fun i j =>
            if (i, j) = (finProdFinEquiv (m := m) (n := n)).symm k
            then maskedScaled p (Xi x.1) (Mask x.1) i j else 0)
          (Matrix.transpose (Matrix.of fun i j =>
            if (i, j) = (finProdFinEquiv (m := m) (n := n)).symm k
            then maskedScaled p (Xi x.1) (Mask x.1) i j else 0))
          (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
          ((finSumFinEquiv (m := m) (n := n)).symm u)
          ((finSumFinEquiv (m := m) (n := n)).symm v)
    let f : Fin (m * n) → Ω × (Fin m → Fin n → ℝ) → ℝ :=
      fun k x => ((m : ℝ) + (n : ℝ))⁻¹ * ∑ t : Fin (m + n),
        (((Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)).eigenvalues t) ^ ((3 : ℝ) / 2))
    (∀ k, Integrable (f k) (μ.prod (stdNormalMatrixMeasure m n)))
      ∧ (∑ k : Fin (m * n), ∫ x, f k x ∂(μ.prod (stdNormalMatrixMeasure m n)))
          ≤ 48 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ := by
  /- @proof-region region.target-node.session.5d1356f3203f26e0 begin -/
  intro m n hm hn p Kt hp hp1 hKt Ω hΩ μ hμ Xi Mask hMeasXi hMeasMask hIntThird hbudget
  classical
  let Zfm : Fin (m * n) → Ω × (Fin m → Fin n → ℝ) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun k x => Matrix.of fun u v =>
      ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
        (Matrix.of fun i j =>
          if (i, j) = (finProdFinEquiv (m := m) (n := n)).symm k
          then maskedScaled p (Xi x.1) (Mask x.1) i j else 0)
        (Matrix.transpose (Matrix.of fun i j =>
          if (i, j) = (finProdFinEquiv (m := m) (n := n)).symm k
          then maskedScaled p (Xi x.1) (Mask x.1) i j else 0))
        (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
        ((finSumFinEquiv (m := m) (n := n)).symm u)
        ((finSumFinEquiv (m := m) (n := n)).symm v)
  let f : Fin (m * n) → Ω × (Fin m → Fin n → ℝ) → ℝ :=
    fun k x => ((m : ℝ) + (n : ℝ))⁻¹ * ∑ t : Fin (m + n),
      (((Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)).eigenvalues t) ^ ((3 : ℝ) / 2))
  change (∀ k : Fin (m * n), Integrable (f k) (μ.prod (stdNormalMatrixMeasure m n))) ∧
    (∑ k : Fin (m * n), ∫ x, f k x ∂(μ.prod (stdNormalMatrixMeasure m n)))
      ≤ 48 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹
  have hpt : ∀ (k : Fin (m * n)) (x : Ω × (Fin m → Fin n → ℝ)),
      f k x = ((m : ℝ) + (n : ℝ))⁻¹ * 2 *
        (|maskedScaled p (Xi x.1) (Mask x.1)
          ((finProdFinEquiv (m := m) (n := n)).symm k).1
          ((finProdFinEquiv (m := m) (n := n)).symm k).2|) ^ 3 := by
    intro k x
    set i0 : Fin m := ((finProdFinEquiv (m := m) (n := n)).symm k).1 with hi0
    set j0 : Fin n := ((finProdFinEquiv (m := m) (n := n)).symm k).2 with hj0
    set a : ℝ := maskedScaled p (Xi x.1) (Mask x.1) i0 j0 with ha
    set p0 : Fin (m + n) := (finSumFinEquiv (m := m) (n := n)) (Sum.inl i0) with hp0
    set q0 : Fin (m + n) := (finSumFinEquiv (m := m) (n := n)) (Sum.inr j0) with hq0
    have hpq : p0 ≠ q0 := by
      intro h
      have h' := congrArg (finSumFinEquiv (m := m) (n := n)).symm h
      simp only [hp0, hq0, Equiv.symm_apply_apply] at h'
      exact Sum.inl_ne_inr h'
    have he2 : (i0, j0) = (finProdFinEquiv (m := m) (n := n)).symm k := by
      rw [hi0, hj0]
    have hgen : ∀ (su sv : Fin m ⊕ Fin n),
        (Zfm k x) ((finSumFinEquiv (m := m) (n := n)) su)
            ((finSumFinEquiv (m := m) (n := n)) sv)
          = ((if (su = Sum.inl i0 ∧ sv = Sum.inr j0) ∨ (su = Sum.inr j0 ∧ sv = Sum.inl i0)
              then a else 0 : ℝ) : ℂ) := by
      intro su sv
      rcases su with i | i <;> rcases sv with j | j
      · simp [Zfm, Matrix.fromBlocks]
      · simp only [Zfm, Matrix.of_apply, Equiv.symm_apply_apply, Matrix.map_apply,
          Matrix.fromBlocks, Matrix.transpose_apply]
        by_cases hij : (i, j) = (i0, j0)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
          simp [← he2, ← ha]
        · have h2 : ¬ (i = i0 ∧ j = j0) := fun hc => hij (Prod.ext hc.1 hc.2)
          simp [← he2, hij, h2]
      · simp only [Zfm, Matrix.of_apply, Equiv.symm_apply_apply, Matrix.map_apply,
          Matrix.fromBlocks, Matrix.transpose_apply]
        by_cases hij : (j, i) = (i0, j0)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
          simp [← he2, ← ha]
        · have h3 : ¬ (j = i0 ∧ i = j0) := fun hc => hij (by rw [hc.1, hc.2])
          have h2 : ¬ (i = j0 ∧ j = i0) := fun hc => hij (by rw [hc.2, hc.1])
          simp [← he2, h3, h2]
      · simp [Zfm, Matrix.fromBlocks]
    have hZ : ∀ u v : Fin (m + n), (Zfm k x) u v
        = ((if (u = p0 ∧ v = q0) ∨ (u = q0 ∧ v = p0) then a else 0 : ℝ) : ℂ) := by
      have hP : ∀ u : Fin (m + n),
          ((finSumFinEquiv (m := m) (n := n)).symm u = Sum.inl i0) ↔ (u = p0) := by
        intro u
        constructor
        · intro h
          have h2 : (finSumFinEquiv (m := m) (n := n))
              ((finSumFinEquiv (m := m) (n := n)).symm u)
              = (finSumFinEquiv (m := m) (n := n)) (Sum.inl i0) := by rw [h]
          rwa [Equiv.apply_symm_apply] at h2
        · intro h
          rw [h]
          exact Equiv.symm_apply_apply _ _
      have hQ : ∀ u : Fin (m + n),
          ((finSumFinEquiv (m := m) (n := n)).symm u = Sum.inr j0) ↔ (u = q0) := by
        intro u
        constructor
        · intro h
          have h2 : (finSumFinEquiv (m := m) (n := n))
              ((finSumFinEquiv (m := m) (n := n)).symm u)
              = (finSumFinEquiv (m := m) (n := n)) (Sum.inr j0) := by rw [h]
          rwa [Equiv.apply_symm_apply] at h2
        · intro h
          rw [h]
          exact Equiv.symm_apply_apply _ _
      intro u v
      have h1 := hgen ((finSumFinEquiv (m := m) (n := n)).symm u)
        ((finSumFinEquiv (m := m) (n := n)).symm v)
      simp only [Equiv.apply_symm_apply] at h1
      rw [h1]
      simp only [hP u, hP v, hQ u, hQ v]
    have hZconj : (Zfm k x).conjTranspose = (Zfm k x) := by
      ext u v
      rw [Matrix.conjTranspose_apply, hZ v u, hZ u v]
      by_cases hc : (v = p0 ∧ u = q0) ∨ (v = q0 ∧ u = p0)
      · have hc' : (u = p0 ∧ v = q0) ∨ (u = q0 ∧ v = p0) := by tauto
        rw [if_pos hc, if_pos hc']
        exact Complex.conj_ofReal a
      · have hc' : ¬ ((u = p0 ∧ v = q0) ∨ (u = q0 ∧ v = p0)) := by tauto
        rw [if_neg hc, if_neg hc']
        simp
    have hdiag : (Zfm k x).conjTranspose * (Zfm k x)
        = Matrix.diagonal (fun r : Fin (m + n) =>
            ((if r = p0 ∨ r = q0 then a ^ 2 else 0 : ℝ) : ℂ)) := by
      rw [hZconj]
      have hZ0 : ∀ w : Fin (m + n), (Zfm k x) p0 w = ((if w = q0 then a else 0 : ℝ) : ℂ) := by
        intro w
        rw [hZ p0 w]
        simp [hpq]
      have hZ1 : ∀ w : Fin (m + n), (Zfm k x) q0 w = ((if w = p0 then a else 0 : ℝ) : ℂ) := by
        intro w
        rw [hZ q0 w]
        simp [hpq, hpq.symm]
      have hZ2 : ∀ u : Fin (m + n), u ≠ p0 → u ≠ q0 →
          ∀ w : Fin (m + n), (Zfm k x) u w = 0 := by
        intro u hu1 hu2 w
        rw [hZ u w]
        simp [hu1, hu2]
      have hsumq : ∀ (c : ℂ) (t : Fin (m + n)),
          (∑ w : Fin (m + n), (if w = t then c else 0)) = c := by
        intro c t
        simpa using Finset.sum_eq_single (f := fun w : Fin (m + n) => (if w = t then c else 0)) t
          (by intro b _ hb; simp [hb])
          (by intro h; exact absurd (Finset.mem_univ t) h)
      ext u v
      rw [Matrix.mul_apply]
      simp only [Matrix.diagonal, Matrix.of_apply]
      by_cases hu1 : u = p0
      · rw [hu1]
        have hterm : ∀ w : Fin (m + n), (Zfm k x) p0 w * (Zfm k x) w v
            = (if w = q0 then ((a : ℂ) * (Zfm k x) q0 v) else 0) := by
          intro w
          rw [hZ0 w]
          by_cases hw : w = q0
          · rw [hw]
            simp
          · simp [hw]
        rw [Finset.sum_congr rfl (fun w _ => hterm w), hsumq _ q0, hZ1 v]
        by_cases hv : v = p0
        · rw [hv]
          simp [pow_two]
        · simp [hv, Ne.symm hv]
      · by_cases hu2 : u = q0
        · rw [hu2]
          have hterm : ∀ w : Fin (m + n), (Zfm k x) q0 w * (Zfm k x) w v
              = (if w = p0 then ((a : ℂ) * (Zfm k x) p0 v) else 0) := by
            intro w
            rw [hZ1 w]
            by_cases hw : w = p0
            · rw [hw]
              simp
            · simp [hw]
          rw [Finset.sum_congr rfl (fun w _ => hterm w), hsumq _ p0, hZ0 v]
          by_cases hv : v = q0
          · rw [hv]
            simp [pow_two]
          · simp [hv, Ne.symm hv]
        · have hzero : ∀ w : Fin (m + n), (Zfm k x) u w * (Zfm k x) w v = 0 := by
            intro w
            rw [hZ2 u hu1 hu2 w]
            simp
          rw [Finset.sum_congr rfl (fun w _ => hzero w)]
          simp [hu1, hu2]
    have eigrec : ∀ {C D : Matrix (Fin (m + n)) (Fin (m + n)) ℂ} (hh : C = D) (hC : C.IsHermitian)
        (t : Fin (m + n)), ((hh ▸ hC : D.IsHermitian)).eigenvalues t = hC.eigenvalues t := by
      intro C D hh hC t
      cases hh
      rfl
    have hB : (Matrix.diagonal (fun r : Fin (m + n) =>
        ((if r = p0 ∨ r = q0 then a ^ 2 else 0 : ℝ) : ℂ))).IsHermitian :=
      hdiag ▸ Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)
    have hsumB : (∑ t : Fin (m + n), (hB.eigenvalues t) ^ ((3 : ℝ) / 2)) = 2 * (|a|) ^ 3 :=
      statopia_math_node_1840280243_8691960b (m + n) a p0 q0 hpq hB
    have heig : ∀ t : Fin (m + n), hB.eigenvalues t
        = (Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)).eigenvalues t :=
      fun t => eigrec hdiag (Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)) t
    have hsumA : (∑ t : Fin (m + n),
        (((Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)).eigenvalues t) ^ ((3 : ℝ) / 2)))
        = 2 * (|a|) ^ 3 := by
      rw [← hsumB]
      exact Finset.sum_congr rfl (fun t _ => by rw [heig t])
    have hf : f k x = ((m : ℝ) + (n : ℝ))⁻¹ * (∑ t : Fin (m + n),
        (((Matrix.isHermitian_conjTranspose_mul_self (Zfm k x)).eigenvalues t) ^ ((3 : ℝ) / 2))) := rfl
    rw [hf, hsumA, ha, hi0, hj0]
    ring
  refine ⟨?_, ?_⟩
  · intro k
    haveI hinner : IsProbabilityMeasure
        (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    haveI hprob : IsProbabilityMeasure (stdNormalMatrixMeasure m n) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    haveI hfin : IsFiniteMeasure (stdNormalMatrixMeasure m n) := inferInstance
    have hfun : f k = fun x : Ω × (Fin m → Fin n → ℝ) =>
        (((m : ℝ) + (n : ℝ))⁻¹ * 2) *
          (|maskedScaled p (Xi x.1) (Mask x.1)
            ((finProdFinEquiv (m := m) (n := n)).symm k).1
            ((finProdFinEquiv (m := m) (n := n)).symm k).2|) ^ 3 := by
      funext x
      exact hpt k x
    rw [hfun]
    exact (MeasureTheory.Integrable.comp_fst
      (hIntThird ((finProdFinEquiv (m := m) (n := n)).symm k).1
        ((finProdFinEquiv (m := m) (n := n)).symm k).2)
      (stdNormalMatrixMeasure m n)).const_mul (((m : ℝ) + (n : ℝ))⁻¹ * 2)
  · haveI hinner : IsProbabilityMeasure
        (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    haveI hprob : IsProbabilityMeasure (stdNormalMatrixMeasure m n) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    have hν1 : ∀ c : ℝ, ∫ _ : (Fin m → Fin n → ℝ), c ∂(stdNormalMatrixMeasure m n) = c := by
      intro c
      rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
    have hint : ∀ k : Fin (m * n),
        ∫ x, f k x ∂(μ.prod (stdNormalMatrixMeasure m n))
          = (((m : ℝ) + (n : ℝ))⁻¹ * 2) * ∫ ω, (|maskedScaled p (Xi ω) (Mask ω)
              ((finProdFinEquiv (m := m) (n := n)).symm k).1
              ((finProdFinEquiv (m := m) (n := n)).symm k).2|) ^ 3 ∂μ := by
      intro k
      have hfun : f k = fun x : Ω × (Fin m → Fin n → ℝ) =>
          (|maskedScaled p (Xi x.1) (Mask x.1)
            ((finProdFinEquiv (m := m) (n := n)).symm k).1
            ((finProdFinEquiv (m := m) (n := n)).symm k).2|) ^ 3 *
            (((m : ℝ) + (n : ℝ))⁻¹ * 2) := by
        funext x
        rw [hpt k x]
        ring
      rw [hfun, MeasureTheory.integral_prod_mul
        (f := fun ω => (|maskedScaled p (Xi ω) (Mask ω)
            ((finProdFinEquiv (m := m) (n := n)).symm k).1
            ((finProdFinEquiv (m := m) (n := n)).symm k).2|) ^ 3)
        (g := fun _ : (Fin m → Fin n → ℝ) => ((m : ℝ) + (n : ℝ))⁻¹ * 2)]
      rw [hν1 (((m : ℝ) + (n : ℝ))⁻¹ * 2), mul_comm]
    have hreindex : (∑ k : Fin (m * n), ∫ ω, (|maskedScaled p (Xi ω) (Mask ω)
          ((finProdFinEquiv (m := m) (n := n)).symm k).1
          ((finProdFinEquiv (m := m) (n := n)).symm k).2|) ^ 3 ∂μ)
        = ∑ i : Fin m, ∑ j : Fin n, ∫ ω, (|maskedScaled p (Xi ω) (Mask ω) i j|) ^ 3 ∂μ := by
      refine (Equiv.sum_comp (finProdFinEquiv (m := m) (n := n)).symm
        (fun q : Fin m × Fin n =>
          ∫ ω, (|maskedScaled p (Xi ω) (Mask ω) q.1 q.2|) ^ 3 ∂μ)).trans ?_
      exact Fintype.sum_prod_type
        (fun q : Fin m × Fin n => ∫ ω, (|maskedScaled p (Xi ω) (Mask ω) q.1 q.2|) ^ 3 ∂μ)
    have hsum : (∑ k : Fin (m * n), ∫ x, f k x ∂(μ.prod (stdNormalMatrixMeasure m n)))
        = (((m : ℝ) + (n : ℝ))⁻¹ * 2) * (∑ i : Fin m, ∑ j : Fin n,
            ∫ ω, (|maskedScaled p (Xi ω) (Mask ω) i j|) ^ 3 ∂μ) := by
      rw [Finset.sum_congr rfl (fun k _ => hint k), ← Finset.mul_sum, hreindex]
    rw [hsum]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmn : (0 : ℝ) < (m : ℝ) + (n : ℝ) := by linarith
    have hc : (0 : ℝ) ≤ ((m : ℝ) + (n : ℝ))⁻¹ * 2 := by
      have hpos : (0 : ℝ) < ((m : ℝ) + (n : ℝ))⁻¹ := inv_pos.mpr hmn
      linarith
    refine le_trans (mul_le_mul_of_nonneg_left hbudget hc) ?_
    have hmn0 : ((m : ℝ) + (n : ℝ)) ≠ 0 := ne_of_gt hmn
    have hX : ((m : ℝ) + (n : ℝ))⁻¹ * ((m : ℝ) + (n : ℝ)) = 1 := inv_mul_cancel₀ hmn0
    have hcalc : (((m : ℝ) + (n : ℝ))⁻¹ * 2) *
          (((m : ℝ) + (n : ℝ)) * (24 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹))
        = 48 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ := by
      calc (((m : ℝ) + (n : ℝ))⁻¹ * 2) *
            (((m : ℝ) + (n : ℝ)) * (24 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹))
          = 2 * (((m : ℝ) + (n : ℝ))⁻¹ * ((m : ℝ) + (n : ℝ))) *
              (24 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹) := by ring
        _ = 48 * Kt ^ 3 * (Real.sqrt ((m : ℝ) * p))⁻¹ := by rw [hX]; ring
    exact le_of_eq hcalc
  /- @proof-region region.target-node.session.5d1356f3203f26e0 end -/

end Statlib.Imported

