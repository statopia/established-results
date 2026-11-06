import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_da1a210d30be62fec44e
import ProverJobs.ResidualE2ESupport20261106.M_255c3f19f3d661abe31b

namespace PaperProofTasks.ResidualE2ESupport20261106


run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1167625269_02ef4fe3 : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {Ωm : Type*} [MeasurableSpace Ωm] (P : Measure Ωm) [IsProbabilityMeasure P]
    (Om : Fin m → Fin n → Ωm → ℝ)
    (hOm_meas : ∀ i j, Measurable (Om i j))
    (hOm_indep : iIndepFun (fun ij : Fin m × Fin n => Om ij.1 ij.2) P)
    (hOm_bin : ∀ i j, ∀ᵐ ω ∂P, Om i j ω = 0 ∨ Om i j ω = 1)
    (hOm_int : ∀ i j, Integrable (Om i j) P)
    (hOm_mean : ∀ i j, ∫ ω, Om i j ω ∂P = p),
    let xi : Ωm → Fin m → Fin n → ℝ := fun ω i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)
    let gamma : Measure ((Fin m × Fin n) → ℝ) :=
      Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 ((1 - p) / (m : ℝ)).toNNReal)
    let Gmat : Ωm × ((Fin m × Fin n) → ℝ) → Matrix (Fin m) (Fin n) ℝ :=
      fun x => Matrix.of (fun i j => x.2 (i, j))
    let ee := Fintype.equivFin (Fin m × Fin n)
    let Zblk : Fin (Fintype.card (Fin m × Fin n)) →
        (Ωm × ((Fin m × Fin n) → ℝ)) → Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
      fun k x => Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
        (Matrix.of (fun (a : Fin m) (b : Fin n) =>
          ((xi x.1 (ee.symm k).1 (ee.symm k).2 *
            matrixUnit (ee.symm k).1 (ee.symm k).2 a b : ℝ) : ℂ)))
        (Matrix.of (fun (a : Fin m) (b : Fin n) =>
          ((xi x.1 (ee.symm k).1 (ee.symm k).2 *
            matrixUnit (ee.symm k).1 (ee.symm k).2 a b : ℝ) : ℂ))).conjTranspose
        (0 : Matrix (Fin n) (Fin n) ℂ)
    let Zfam : Fin (Fintype.card (Fin m × Fin n)) →
        (Ωm × ((Fin m × Fin n) → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
      fun k x => (Zblk k x).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    let Gblk : (Ωm × ((Fin m × Fin n) → ℝ)) → Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
      fun x => Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
        (Matrix.of (fun (i : Fin m) (j : Fin n) => ((Gmat x i j : ℝ) : ℂ)))
        (Matrix.of (fun (i : Fin m) (j : Fin n) => ((Gmat x i j : ℝ) : ℂ))).conjTranspose
        (0 : Matrix (Fin n) (Fin n) ℂ)
    let Gdil : (Ωm × ((Fin m × Fin n) → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
      fun x => (Gblk x).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    ∀ a b c e : Fin (m + n),
      (∫ x, Gdil x a b * star (Gdil x c e) ∂(Measure.prod P gamma))
        = ∫ x, (((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
              + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x) a b)
            * star (((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
              + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x) c e)
            ∂(Measure.prod P gamma) := by
  /- @proof-region region.target-node.session.91d08e06644933ab begin -/
  intro m n hm hn hnm p hp0 hp1 Ωm _ P _ Om hOm_meas hOm_indep hOm_bin hOm_int hOm_mean
  intro xi gamma Gmat ee Zblk Zfam Gblk Gdil
  intro a b c e
  let pv : Fin (m + n) → Fin (m + n) → Option (Fin m × Fin n) := fun a b =>
    match finSumFinEquiv.symm a, finSumFinEquiv.symm b with
    | Sum.inl i, Sum.inr j => some (i, j)
    | Sum.inr j, Sum.inl i => some (i, j)
    | _, _ => none
  let Dil : (Fin m → Fin n → ℝ) → Fin (m + n) → Fin (m + n) → ℝ := fun M a b =>
    match pv a b with
    | some u => M u.1 u.2
    | none => 0
  have hstar : ∀ r : ℝ, star ((r : ℂ)) = ((r : ℂ)) := by intro r; simp
  have hblk : ∀ (M : Fin m → Fin n → ℝ) (a b : Fin (m + n)),
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
        (Matrix.of (fun (i : Fin m) (j : Fin n) => ((M i j : ℝ) : ℂ)))
        (Matrix.of (fun (i : Fin m) (j : Fin n) => ((M i j : ℝ) : ℂ))).conjTranspose
        (0 : Matrix (Fin n) (Fin n) ℂ)) (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)
      = ((Dil M a b : ℝ) : ℂ) := by
    intro M a b
    rcases ha : finSumFinEquiv.symm a with i | j <;> rcases hb : finSumFinEquiv.symm b with i' | j'
    · simp [ha, hb, Dil, pv, Matrix.fromBlocks]
    · simp [ha, hb, Dil, pv, Matrix.fromBlocks]
    · simp [ha, hb, Dil, pv, Matrix.fromBlocks, Matrix.conjTranspose_apply, hstar]
    · simp [ha, hb, Dil, pv, Matrix.fromBlocks]
  have hcollapse : ∀ (F : Fin (Fintype.card (Fin m × Fin n)) → ℂ)
      (w : Fin (Fintype.card (Fin m × Fin n))), (∀ u, u ≠ w → F u = 0) → ∑ u, F u = F w := by
    intro F w hF
    classical
    have hzero : ∑ u ∈ (Finset.univ.erase w : Finset (Fin (Fintype.card (Fin m × Fin n)))),
        F u = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      exact hF u (Finset.mem_erase.mp hu).1
    have hunion : (insert w (Finset.univ.erase w) :
        Finset (Fin (Fintype.card (Fin m × Fin n)))) = Finset.univ :=
      Finset.insert_erase (Finset.mem_univ w)
    calc ∑ u, F u = ∑ u ∈ (insert w (Finset.univ.erase w) :
            Finset (Fin (Fintype.card (Fin m × Fin n)))), F u := by
          rw [hunion]
      _ = F w + ∑ u ∈ (Finset.univ.erase w :
            Finset (Fin (Fintype.card (Fin m × Fin n)))), F u := by
          rw [Finset.sum_insert (by simp)]
      _ = F w + 0 := by rw [hzero]
      _ = F w := by rw [add_zero]

  have hGent : ∀ (x : Ωm × ((Fin m × Fin n) → ℝ)) (a b : Fin (m + n)),
      Gdil x a b = ((Dil (fun i j => x.2 (i, j)) a b : ℝ) : ℂ) := by
    intro x a b
    rw [show Gdil x a b = (Gblk x) (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) by
      simp [Gdil, Matrix.submatrix_apply]]
    exact hblk (fun i j => x.2 (i, j)) a b
  have hZent : ∀ (x : Ωm × ((Fin m × Fin n) → ℝ)) (a b : Fin (m + n)),
      ((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
        + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x) a b
        = ((Dil (fun i j => xi x.1 i j) a b : ℝ) : ℂ) := by
    intro x a b
    have hsum : ((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
        + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x) a b
        = ∑ k, (Zfam k x) a b := by
      rw [zero_add, Finset.sum_apply, Finset.sum_apply]
    rw [hsum]
    have hstep : ∀ k, (Zfam k x) a b
        = ((Dil (fun i j => xi x.1 (ee.symm k).1 (ee.symm k).2
            * matrixUnit (ee.symm k).1 (ee.symm k).2 i j) a b : ℝ) : ℂ) := by
      intro k
      rw [show (Zfam k x) a b
          = (Zblk k x) (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) by
        simp [Zfam, Matrix.submatrix_apply]]
      exact hblk (fun i j => xi x.1 (ee.symm k).1 (ee.symm k).2
        * matrixUnit (ee.symm k).1 (ee.symm k).2 i j) a b
    simp only [hstep]
    rcases hpu : pv a b with _ | u
    · simp [Dil, hpu]
    · have hz : ∀ k, k ≠ ee u →
          ((Dil (fun i j => xi x.1 (ee.symm k).1 (ee.symm k).2
            * matrixUnit (ee.symm k).1 (ee.symm k).2 i j) a b : ℝ) : ℂ) = 0 := by
        intro k hk
        have hne : u ≠ ee.symm k := by
          intro h
          exact hk (by rw [h, Equiv.apply_symm_apply])
        have hne2 : ¬(u.1 = (ee.symm k).1 ∧ u.2 = (ee.symm k).2) :=
          fun h => hne (Prod.ext h.1 h.2)
        simp [Dil, hpu, matrixUnit, hne2]
      refine (hcollapse (fun (k : Fin (Fintype.card (Fin m × Fin n))) =>
          ((Dil (fun i j => xi x.1 (ee.symm k).1 (ee.symm k).2
            * matrixUnit (ee.symm k).1 (ee.symm k).2 i j) a b : ℝ) : ℂ)) (ee u) hz).trans ?_
      simp [Dil, hpu, matrixUnit]



  have hcolR : ∀ {ι : Type} [Fintype ι] (F : ι → ℝ) (w : ι),
      (∀ u, u ≠ w → F u = 0) → ∑ u, F u = F w := by
    intro ι _ F w hF
    classical
    have hzero : ∑ u ∈ (Finset.univ.erase w : Finset ι), F u = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      exact hF u (Finset.mem_erase.mp hu).1
    have hunion : (insert w (Finset.univ.erase w) : Finset ι) = Finset.univ :=
      Finset.insert_erase (Finset.mem_univ w)
    calc ∑ u, F u = ∑ u ∈ (insert w (Finset.univ.erase w) : Finset ι), F u := by rw [hunion]
      _ = F w + ∑ u ∈ (Finset.univ.erase w : Finset ι), F u := by
            rw [Finset.sum_insert (by simp)]
      _ = F w + 0 := by rw [hzero]
      _ = F w := by rw [add_zero]
  have h2col : ∀ (g : Fin m → Fin n → ℝ) (w : Fin m × Fin n),
      (∀ i j, (i, j) ≠ w → g i j = 0) → (∑ i, ∑ j, g i j) = g w.1 w.2 := by
    intro g w hg
    have hinner : ∀ i : Fin m, (∑ j : Fin n, g i j) = (if i = w.1 then g w.1 w.2 else 0) := by
      intro i
      by_cases hi : i = w.1
      · rw [hi, if_pos rfl]
        exact hcolR (fun j : Fin n => g w.1 j) w.2
          (fun j hj => hg w.1 j (fun h => hj (by simpa using congrArg Prod.snd h)))
      · have hzj : ∀ j : Fin n, g i j = 0 := by
          intro j
          exact hg i j (fun h => hi (by rw [← h]))
        rw [Finset.sum_eq_zero (fun j _ => hzj j), if_neg hi]
    calc ∑ i, ∑ j, g i j = ∑ i, (if i = w.1 then g w.1 w.2 else 0) :=
          Finset.sum_congr rfl (fun i _ => hinner i)
      _ = g w.1 w.2 := by
          have h := hcolR (fun i : Fin m => (if i = w.1 then g w.1 w.2 else 0)) w.1
            (fun i hi => by simp [hi])
          simpa using h
  have hpair : ∀ u v : Fin m × Fin n,
      (∫ ω, xi ω u.1 u.2 * xi ω v.1 v.2 ∂P)
        = if u = v then (1 - p) / (m : ℝ) else 0 := by
    intro u v
    have hmp : (0 : ℝ) < (m : ℝ) * p := by
      have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact mul_pos hm' hp0
    have hsqrt : 0 < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.mpr hmp
    have hmeas : ∀ (i : Fin m) (j : Fin n), Measurable (fun ω : Ωm => xi ω i j) := by
      intro i j
      have h : Measurable (fun ω : Ωm => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) :=
        ((hOm_meas i j).sub measurable_const).div_const _
      simpa [xi] using h
    have hbnd : ∀ (i : Fin m) (j : Fin n),
        ∀ᵐ ω ∂P, ‖xi ω i j‖ ≤ 1 / Real.sqrt ((m : ℝ) * p) := by
      intro i j
      filter_upwards [hOm_bin i j] with ω hω
      have habs : |Om i j ω - p| ≤ 1 := by
        rcases hω with h | h
        · rw [h, zero_sub, abs_neg, abs_of_pos hp0]
          exact hp1
        · rw [h, abs_of_nonneg (by linarith)]
          linarith
      have hxi : xi ω i j = (Om i j ω - p) / Real.sqrt ((m : ℝ) * p) := by simp [xi]
      rw [hxi, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), div_eq_mul_inv, div_eq_mul_inv, one_mul]
      simpa using mul_le_mul_of_nonneg_right habs (le_of_lt (inv_pos.mpr hsqrt))
    have hint : Integrable (fun ω : Ωm => xi ω u.1 u.2 * xi ω v.1 v.2) P := by
      have h1 : Integrable (fun ω : Ωm => xi ω v.1 v.2) P :=
        MeasureTheory.Integrable.of_bound ((hmeas v.1 v.2).aestronglyMeasurable)
          (1 / Real.sqrt ((m : ℝ) * p)) (hbnd v.1 v.2)
      exact MeasureTheory.Integrable.bdd_mul (g := fun ω : Ωm => xi ω v.1 v.2)
        (f := fun ω : Ωm => xi ω u.1 u.2) (c := 1 / Real.sqrt ((m : ℝ) * p))
        h1 ((hmeas u.1 u.2).aestronglyMeasurable) (hbnd u.1 u.2)
    have key : ∀ a : Fin m → Fin n → ℝ,
        (∫ ω, (∑ i, ∑ j, a i j * xi ω i j)^2 ∂P)
          = ((1 - p) / (m : ℝ)) * (∑ i, ∑ j, (a i j)^2) :=
      statopia_math_node_3684688107_efbf5172 m n hm hn p hp0 hp1 P Om hOm_meas hOm_indep
        hOm_bin hOm_int hOm_mean
    have hu : (u.1, u.2) = u := rfl
    have hv : (v.1, v.2) = v := rfl
    have hs : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω : Ωm => xi ω i j * xi ω i j) P := by
      intro i j
      have hC : (0 : ℝ) ≤ 1 / Real.sqrt ((m : ℝ) * p) := le_of_lt (div_pos one_pos hsqrt)
      refine MeasureTheory.Integrable.of_bound
        ((hmeas i j).mul (hmeas i j)).aestronglyMeasurable
        ((1 / Real.sqrt ((m : ℝ) * p)) * (1 / Real.sqrt ((m : ℝ) * p))) ?_
      filter_upwards [hbnd i j] with ω hω
      rw [norm_mul]
      exact mul_le_mul hω hω (norm_nonneg _) hC
    have hSgen : ∀ (a : Fin m → Fin n → ℝ) (w : Fin m × Fin n),
        (∀ i j, (i, j) ≠ w → a i j = 0) → a w.1 w.2 = 1 →
        (∀ ω : Ωm, (∑ i, ∑ j, a i j * xi ω i j) = xi ω w.1 w.2) := by
      intro a w ha ha1 ω
      have h := h2col (fun i j => a i j * xi ω i j) w
        (fun i j hij => by simp [ha i j hij])
      have hb : a w.1 w.2 * xi ω w.1 w.2 = xi ω w.1 w.2 := by rw [ha1, one_mul]
      exact h.trans hb
    have hQgen : ∀ (a : Fin m → Fin n → ℝ) (w : Fin m × Fin n),
        (∀ i j, (i, j) ≠ w → a i j = 0) → a w.1 w.2 = 1 →
        (∑ i, ∑ j, (a i j)^2) = 1 := by
      intro a w ha ha1
      have h := h2col (fun i j => (a i j)^2) w (fun i j hij => by simp [ha i j hij])
      have hb : (a w.1 w.2)^2 = 1 := by rw [ha1, one_pow]

      exact h.trans hb
    have hsq : ∀ (w : Fin m × Fin n),
        (∫ ω, xi ω w.1 w.2 * xi ω w.1 w.2 ∂P) = (1 - p) / (m : ℝ) := by
      intro w
      have ha : ∀ i j, (i, j) ≠ w →
          (fun i j => if (i, j) = w then (1 : ℝ) else 0) i j = 0 :=
        fun i j hij => by simp [hij]
      have ha1 : (fun i j => if (i, j) = w then (1 : ℝ) else 0) w.1 w.2 = 1 := by
        have hw : (w.1, w.2) = w := rfl
        simp [hw]
      have h := key (fun i j => if (i, j) = w then (1 : ℝ) else 0)
      have hQ := hQgen (fun i j => if (i, j) = w then (1 : ℝ) else 0) w ha ha1
      rw [hQ, mul_one] at h
      have h2 : (fun ω : Ωm =>
          (∑ i, ∑ j, (fun i j => if (i, j) = w then (1 : ℝ) else 0) i j * xi ω i j)^2)
          = fun ω : Ωm => xi ω w.1 w.2 * xi ω w.1 w.2 := by
        funext ω
        have hS := hSgen (fun i j => if (i, j) = w then (1 : ℝ) else 0) w ha ha1
        rw [hS ω, pow_two]
      rw [h2] at h
      exact h
    by_cases huv : u = v
    · rw [huv, if_pos rfl]
      exact hsq v
    · rw [if_neg huv]
      let d1 : Fin m → Fin n → ℝ := fun i j => if (i, j) = u then 1 else 0
      let d2 : Fin m → Fin n → ℝ := fun i j => if (i, j) = v then 1 else 0
      let d12 : Fin m → Fin n → ℝ := fun i j => d1 i j + d2 i j
      have hS1 : ∀ ω : Ωm, (∑ i, ∑ j, d1 i j * xi ω i j) = xi ω u.1 u.2 :=
        hSgen d1 u (fun i j hij => by simp [d1, hij]) (by simp [d1, hu])
      have hS2 : ∀ ω : Ωm, (∑ i, ∑ j, d2 i j * xi ω i j) = xi ω v.1 v.2 :=
        hSgen d2 v (fun i j hij => by simp [d2, hij]) (by simp [d2, hv])
      have hQ1 : (∑ i, ∑ j, (d1 i j)^2) = 1 :=
        hQgen d1 u (fun i j hij => by simp [d1, hij]) (by simp [d1, hu])
      have hQ2 : (∑ i, ∑ j, (d2 i j)^2) = 1 :=
        hQgen d2 v (fun i j hij => by simp [d2, hij]) (by simp [d2, hv])
      have hQ12 : (∑ i, ∑ j, (d12 i j)^2) = 2 := by
        have hpt : ∀ i j, (d12 i j)^2 = (d1 i j)^2 + (d2 i j)^2 := by
          intro i j
          by_cases h1 : (i, j) = u
          · have h2 : (i, j) ≠ v := fun hh => huv (h1.symm.trans hh)
            have e1 : d1 i j = 1 := by
              show (if (i, j) = u then (1 : ℝ) else 0) = 1
              rw [if_pos h1]
            have e2 : d2 i j = 0 := by
              show (if (i, j) = v then (1 : ℝ) else 0) = 0
              rw [if_neg h2]
            simp only [d12]
            rw [e1, e2]
            norm_num
          · by_cases h2 : (i, j) = v
            · have e1 : d1 i j = 0 := by
                show (if (i, j) = u then (1 : ℝ) else 0) = 0
                rw [if_neg h1]
              have e2 : d2 i j = 1 := by
                show (if (i, j) = v then (1 : ℝ) else 0) = 1
                rw [if_pos h2]
              simp only [d12]
              rw [e1, e2]
              norm_num
            · have e1 : d1 i j = 0 := by
                show (if (i, j) = u then (1 : ℝ) else 0) = 0
                rw [if_neg h1]
              have e2 : d2 i j = 0 := by
                show (if (i, j) = v then (1 : ℝ) else 0) = 0
                rw [if_neg h2]
              simp only [d12]
              rw [e1, e2]
              norm_num
        simp only [hpt, Finset.sum_add_distrib]
        rw [hQ1, hQ2]
        norm_num
      have hS12 : ∀ ω : Ωm,
          (∑ i, ∑ j, d12 i j * xi ω i j) = xi ω u.1 u.2 + xi ω v.1 v.2 := by
        intro ω
        have hpt : ∀ i j, d12 i j * xi ω i j
            = d1 i j * xi ω i j + d2 i j * xi ω i j := by
          intro i j
          simp only [d12, add_mul]
        simp only [hpt, Finset.sum_add_distrib, hS1 ω, hS2 ω]
      have hA : Integrable (fun ω : Ωm => xi ω u.1 u.2 * xi ω u.1 u.2) P := hs u.1 u.2
      have hC : Integrable (fun ω : Ωm => xi ω v.1 v.2 * xi ω v.1 v.2) P := hs v.1 v.2
      have hlin : (∫ ω, (xi ω u.1 u.2 + xi ω v.1 v.2)^2 ∂P)
          = (∫ ω, xi ω u.1 u.2 * xi ω u.1 u.2 ∂P)
            + 2 * (∫ ω, xi ω u.1 u.2 * xi ω v.1 v.2 ∂P)
            + (∫ ω, xi ω v.1 v.2 * xi ω v.1 v.2 ∂P) := by
        have hAB : Integrable (fun ω : Ωm =>
            xi ω u.1 u.2 * xi ω u.1 u.2
              + (xi ω u.1 u.2 * xi ω v.1 v.2 + xi ω u.1 u.2 * xi ω v.1 v.2)) P :=
          hA.add (hint.add hint)
        have hpt : ∀ ω : Ωm, (xi ω u.1 u.2 + xi ω v.1 v.2)^2
            = (xi ω u.1 u.2 * xi ω u.1 u.2
                + (xi ω u.1 u.2 * xi ω v.1 v.2 + xi ω u.1 u.2 * xi ω v.1 v.2))
              + xi ω v.1 v.2 * xi ω v.1 v.2 := by
          intro ω
          ring
        have e1 : (∫ ω, (xi ω u.1 u.2 * xi ω u.1 u.2
              + (xi ω u.1 u.2 * xi ω v.1 v.2 + xi ω u.1 u.2 * xi ω v.1 v.2))
              + xi ω v.1 v.2 * xi ω v.1 v.2 ∂P)
            = (∫ ω, xi ω u.1 u.2 * xi ω u.1 u.2
                + (xi ω u.1 u.2 * xi ω v.1 v.2 + xi ω u.1 u.2 * xi ω v.1 v.2) ∂P)
              + ∫ ω, xi ω v.1 v.2 * xi ω v.1 v.2 ∂P :=
          MeasureTheory.integral_add (f := fun ω : Ωm => xi ω u.1 u.2 * xi ω u.1 u.2
              + (xi ω u.1 u.2 * xi ω v.1 v.2 + xi ω u.1 u.2 * xi ω v.1 v.2))
            (g := fun ω : Ωm => xi ω v.1 v.2 * xi ω v.1 v.2) hAB hC
        have e2 : (∫ ω, xi ω u.1 u.2 * xi ω u.1 u.2
              + (xi ω u.1 u.2 * xi ω v.1 v.2 + xi ω u.1 u.2 * xi ω v.1 v.2) ∂P)
            = (∫ ω, xi ω u.1 u.2 * xi ω u.1 u.2 ∂P)
              + ∫ ω, xi ω u.1 u.2 * xi ω v.1 v.2 + xi ω u.1 u.2 * xi ω v.1 v.2 ∂P :=
          MeasureTheory.integral_add (f := fun ω : Ωm => xi ω u.1 u.2 * xi ω u.1 u.2)
            (g := fun ω : Ωm => xi ω u.1 u.2 * xi ω v.1 v.2 + xi ω u.1 u.2 * xi ω v.1 v.2)
            hA (hint.add hint)
        have e3 : (∫ ω, xi ω u.1 u.2 * xi ω v.1 v.2 + xi ω u.1 u.2 * xi ω v.1 v.2 ∂P)
            = (∫ ω, xi ω u.1 u.2 * xi ω v.1 v.2 ∂P)
              + ∫ ω, xi ω u.1 u.2 * xi ω v.1 v.2 ∂P :=
          MeasureTheory.integral_add (f := fun ω : Ωm => xi ω u.1 u.2 * xi ω v.1 v.2)
            (g := fun ω : Ωm => xi ω u.1 u.2 * xi ω v.1 v.2) hint hint
        simp only [hpt]
        rw [e1, e2, e3]
        ring
      have hplus := key d12
      rw [hQ12] at hplus
      have h2 : (fun ω : Ωm => (∑ i, ∑ j, d12 i j * xi ω i j)^2)
          = fun ω : Ωm => (xi ω u.1 u.2 + xi ω v.1 v.2)^2 := by
        funext ω
        rw [hS12 ω]
      rw [h2] at hplus
      rw [hlin] at hplus
      rw [hsq u, hsq v] at hplus
      linarith

  have hgauss : (∫ z : (Fin m × Fin n) → ℝ,
      Dil (fun i j => z (i, j)) a b * Dil (fun i j => z (i, j)) c e ∂gamma)
      = (match pv a b, pv c e with
        | some u, some v => if u = v then (1 - p) / (m : ℝ) else 0
        | _, _ => 0) := by
    rcases h1 : pv a b with _ | u <;> rcases h2 : pv c e with _ | v
    · simp [Dil, h1, h2]
    · simp [Dil, h1, h2]
    · simp [Dil, h1, h2]
    · have hz : (fun z : (Fin m × Fin n) → ℝ =>
          Dil (fun i j => z (i, j)) a b * Dil (fun i j => z (i, j)) c e)
          = fun z : (Fin m × Fin n) → ℝ => z u * z v := by
        funext z
        simp [Dil, h1, h2]
      rw [hz, statopia_math_node_318634017_8ba2f28f m n hm p hp1 u v]
  have hbern : (∫ ω : Ωm,
      Dil (fun i j => xi ω i j) a b * Dil (fun i j => xi ω i j) c e ∂P)
      = (match pv a b, pv c e with
        | some u, some v => if u = v then (1 - p) / (m : ℝ) else 0
        | _, _ => 0) := by
    rcases h1 : pv a b with _ | u <;> rcases h2 : pv c e with _ | v
    · simp [Dil, h1, h2]
    · simp [Dil, h1, h2]
    · simp [Dil, h1, h2]
    · have hz : (fun ω : Ωm =>
          Dil (fun i j => xi ω i j) a b * Dil (fun i j => xi ω i j) c e)
          = fun ω : Ωm => xi ω u.1 u.2 * xi ω v.1 v.2 := by
        funext ω
        simp [Dil, h1, h2]
      rw [hz, hpair u v]
  have hL : (∫ x, Gdil x a b * star (Gdil x c e) ∂(Measure.prod P gamma))
      = ((∫ z : (Fin m × Fin n) → ℝ,
          Dil (fun i j => z (i, j)) a b * Dil (fun i j => z (i, j)) c e ∂gamma : ℝ) : ℂ) := by
    let cfun : Ωm → ℂ := fun _ => 1
    let gG : ((Fin m × Fin n) → ℝ) → ℂ := fun z =>
      ((Dil (fun i j => z (i, j)) a b * Dil (fun i j => z (i, j)) c e : ℝ) : ℂ)
    have hpoint : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
        Gdil x a b * star (Gdil x c e) = cfun x.1 * gG x.2 := by
      intro x
      rw [hGent x a b, hGent x c e, hstar, ← Complex.ofReal_mul]
      simp only [cfun, gG, one_mul]
    simp only [hpoint]
    rw [MeasureTheory.integral_prod_mul]
    have hcone : (∫ x : Ωm, cfun x ∂P) = 1 := by simp [cfun]
    have hgG : (∫ y, gG y ∂gamma) = ((∫ z : (Fin m × Fin n) → ℝ,
        Dil (fun i j => z (i, j)) a b * Dil (fun i j => z (i, j)) c e ∂gamma : ℝ) : ℂ) := by
      simpa only [gG] using (integral_ofReal (μ := gamma)
        (f := fun z : (Fin m × Fin n) → ℝ =>
          Dil (fun i j => z (i, j)) a b * Dil (fun i j => z (i, j)) c e))
    rw [hcone, hgG, one_mul]
  have hR : (∫ x, (((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
          + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x) a b)
        * star (((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
          + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x) c e)
        ∂(Measure.prod P gamma))
      = ((∫ ω : Ωm,
          Dil (fun i j => xi ω i j) a b * Dil (fun i j => xi ω i j) c e ∂P : ℝ) : ℂ) := by
    let cone : ((Fin m × Fin n) → ℝ) → ℂ := fun _ => 1
    let gB : Ωm → ℂ := fun ω =>
      ((Dil (fun i j => xi ω i j) a b * Dil (fun i j => xi ω i j) c e : ℝ) : ℂ)
    have hpoint : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
        (((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
            + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x) a b)
          * star (((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
            + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x) c e)
        = gB x.1 * cone x.2 := by
      intro x
      rw [hZent x a b, hZent x c e, hstar, ← Complex.ofReal_mul]
      simp only [gB, cone, mul_one]
    simp only [hpoint]
    rw [MeasureTheory.integral_prod_mul]
    have hgB : (∫ ω : Ωm, gB ω ∂P) = ((∫ ω : Ωm,
        Dil (fun i j => xi ω i j) a b * Dil (fun i j => xi ω i j) c e ∂P : ℝ) : ℂ) := by
      simpa only [gB] using (integral_ofReal (μ := P)
        (f := fun ω : Ωm =>
          Dil (fun i j => xi ω i j) a b * Dil (fun i j => xi ω i j) c e))
    have hcone2 : (∫ y, cone y ∂gamma) = 1 := by simp [cone]
    rw [hgB, hcone2, mul_one]

  rw [hL, hR, hgauss, hbern]



  /- @proof-region region.target-node.session.91d08e06644933ab end -/

end

end Statlib.Imported

