import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_c92e5333e16f0f7ae749

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
theorem statopia_math_node_2677770135_08a2ad00 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : 0 < p)
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
    (let e1 : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
     let e2 : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
     let F : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) → Matrix (Fin m) (Fin n) ℝ :=
       fun k x i j =>
         if (i, j) = e2.symm k then maskedScaled p (Xi x.1) (Mask x.1) i j else 0
     let Z : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) →
         Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
       fun k x u v =>
         ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (F k x)
           (Matrix.transpose (F k x)) (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
           (e1.symm u) (e1.symm v)
     iIndepFun (fun (k : Fin (m * n)) (x : Ω × (Fin m → Fin n → ℝ)) => Z k x)
       (μ.prod (stdNormalMatrixMeasure m n))) := by
  /- @proof-region region.target-node.session.68b756049ddbe3eb begin -/
  intro Ω _ μ _ m n hm p hp Xi Mask hXi_meas hMask_meas hXi_indep hMask_indep hIndep
  let e1 : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  let e2 : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  let F : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) → Matrix (Fin m) (Fin n) ℝ :=
    fun k x i j =>
      if (i, j) = e2.symm k then maskedScaled p (Xi x.1) (Mask x.1) i j else 0
  let Z : Fin (m * n) → (Ω × (Fin m → Fin n → ℝ)) →
      Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun k x u v =>
      ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (F k x)
        (Matrix.transpose (F k x)) (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
        (e1.symm u) (e1.symm v)
  let x0 : Fin m → Fin n → ℝ := fun _ _ => 0
  let singleEntry : (Fin m × Fin n) → ℝ × ℝ → Matrix (Fin m) (Fin n) ℝ :=
    fun a t i j => if (i, j) = a then t.2 * t.1 / Real.sqrt ((m : ℝ) * p) else 0
  let Φ : (Fin m × Fin n) → ℝ × ℝ → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun a t u v =>
      ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (singleEntry a t)
        (Matrix.transpose (singleEntry a t)) (0 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal)
        (e1.symm u) (e1.symm v)
  have hΦmeas : ∀ a, Measurable (Φ a) := by
    intro a
    have hscalar : ∀ (i : Fin m) (j : Fin n),
        Measurable (fun t : ℝ × ℝ => Complex.ofReal (singleEntry a t i j)) := by
      intro i j
      by_cases h : (i, j) = a
      · have he : (fun t : ℝ × ℝ => Complex.ofReal (singleEntry a t i j))
            = fun t => Complex.ofReal (t.2 * t.1 / Real.sqrt ((m : ℝ) * p)) := by
          funext t
          dsimp only [singleEntry]
          rw [if_pos h]
        rw [he]
        have hcont : Continuous
            (fun t : ℝ × ℝ => Complex.ofReal (t.2 * t.1 / Real.sqrt ((m : ℝ) * p))) := by
          continuity
        exact hcont.measurable
      · have he : (fun t : ℝ × ℝ => Complex.ofReal (singleEntry a t i j))
            = fun _ => (0 : ℂ) := by
          funext t
          dsimp only [singleEntry]
          rw [if_neg h]
          simp
        rw [he]
        exact measurable_const
    rw [measurable_pi_iff]
    intro u
    rw [measurable_pi_iff]
    intro v
    have hentry : (fun t : ℝ × ℝ => Φ a t u v)
        = fun t => Complex.ofReal ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (singleEntry a t) (Matrix.transpose (singleEntry a t))
            (0 : Matrix (Fin n) (Fin n) ℝ)) (e1.symm u) (e1.symm v)) := by
      funext t
      rfl
    rw [hentry]
    cases hsu : e1.symm u with
    | inl i =>
      cases hsv : e1.symm v with
      | inl j =>
        show Measurable (fun _ : ℝ × ℝ => (0 : ℂ))
        exact measurable_const
      | inr j =>
        show Measurable (fun t : ℝ × ℝ => Complex.ofReal (singleEntry a t i j))
        exact hscalar i j
    | inr i =>
      cases hsv : e1.symm v with
      | inl j =>
        show Measurable (fun t : ℝ × ℝ => Complex.ofReal (singleEntry a t j i))
        exact hscalar j i
      | inr j =>
        show Measurable (fun _ : ℝ × ℝ => (0 : ℂ))
        exact measurable_const
  have hZeq : (fun k (ω : Ω) => Φ (e2.symm k)
        ((Xi ω (e2.symm k).1 (e2.symm k).2, Mask ω (e2.symm k).1 (e2.symm k).2)))
      = (fun k (ω : Ω) => Z k (ω, x0)) := by
    funext k ω
    have hF : F k (ω, x0) = singleEntry (e2.symm k)
        (Xi ω (e2.symm k).1 (e2.symm k).2, Mask ω (e2.symm k).1 (e2.symm k).2) := by
      funext i j
      dsimp only [F, singleEntry]
      split_ifs with h
      · have h1 : i = (e2.symm k).1 := congrArg Prod.fst h
        have h2 : j = (e2.symm k).2 := congrArg Prod.snd h
        subst h1
        subst h2
        dsimp only [maskedScaled]
      · rfl
    funext u v
    dsimp only [Z, Φ]
    rw [hF]
  have hZ0 : iIndepFun (fun k (ω : Ω) => Z k (ω, x0)) μ := by
    have hpair : iIndepFun
        (fun (a : Fin m × Fin n) (ω : Ω) => (Xi ω a.1 a.2, Mask ω a.1 a.2)) μ :=
      statopia_math_node_1972792747_7490ef34
        (fun (a : Fin m × Fin n) (ω : Ω) => Xi ω a.1 a.2)
        (fun (a : Fin m × Fin n) (ω : Ω) => Mask ω a.1 a.2)
        (fun a => hXi_meas a.1 a.2) (fun a => hMask_meas a.1 a.2)
        hXi_indep hMask_indep hIndep
    have hcomp : iIndepFun (fun a (ω : Ω) => Φ a ((Xi ω a.1 a.2, Mask ω a.1 a.2))) μ :=
      hpair.comp Φ hΦmeas
    have hpre : iIndepFun
        (fun k (ω : Ω) => Φ (e2.symm k)
          ((Xi ω (e2.symm k).1 (e2.symm k).2, Mask ω (e2.symm k).1 (e2.symm k).2))) μ :=
      iIndepFun.precomp (g := ⇑e2.symm) e2.symm.injective hcomp
    rw [hZeq] at hpre
    exact hpre
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    unfold stdNormalMatrixMeasure
    infer_instance
  have hν : (stdNormalMatrixMeasure m n) Set.univ = 1 := measure_univ
  have hmp_map : Measure.map Prod.fst (μ.prod (stdNormalMatrixMeasure m n)) = μ := by
    rw [Measure.map_fst_prod, hν, one_smul]
  have hZmeas : ∀ k, Measurable (fun ω : Ω => Z k (ω, x0)) := by
    intro k
    have hcongr : (fun ω : Ω => Z k (ω, x0))
        = fun ω => Φ (e2.symm k)
            ((Xi ω (e2.symm k).1 (e2.symm k).2, Mask ω (e2.symm k).1 (e2.symm k).2)) := by
      funext ω
      exact (congrFun (congrFun hZeq k) ω).symm
    rw [hcongr]
    exact (hΦmeas (e2.symm k)).comp
      (Measurable.prodMk (hXi_meas (e2.symm k).1 (e2.symm k).2)
        (hMask_meas (e2.symm k).1 (e2.symm k).2))
  have hmain : iIndepFun (fun k (x : Ω × (Fin m → Fin n → ℝ)) => Z k x)
      (μ.prod (stdNormalMatrixMeasure m n)) := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hZ0
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S t ht
    have hset : ∀ i, (fun x : Ω × (Fin m → Fin n → ℝ) => Z i x) ⁻¹' t i
        = Prod.fst ⁻¹' ((fun ω : Ω => Z i (ω, x0)) ⁻¹' t i) := by
      intro i
      ext x
      rfl
    have hBI : MeasurableSet (⋂ i ∈ S, (fun ω : Ω => Z i (ω, x0)) ⁻¹' t i) := by
      apply Finset.measurableSet_biInter
      intro i hi
      exact (hZmeas i) (ht i hi)
    have hmapB : ∀ B : Set Ω, MeasurableSet B →
        (μ.prod (stdNormalMatrixMeasure m n)) (Prod.fst ⁻¹' B) = μ B := by
      intro B hB
      rw [← Measure.map_apply measurable_fst hB, hmp_map]
    have hsetS : (⋂ i ∈ S, (fun x : Ω × (Fin m → Fin n → ℝ) => Z i x) ⁻¹' t i)
        = Prod.fst ⁻¹' (⋂ i ∈ S, (fun ω : Ω => Z i (ω, x0)) ⁻¹' t i) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage]
      constructor
      · exact fun h i hi => h i hi
      · exact fun h i hi => h i hi
    rw [hsetS, hmapB _ hBI]
    have hRHS : ∀ i ∈ S, (μ.prod (stdNormalMatrixMeasure m n))
          ((fun x : Ω × (Fin m → Fin n → ℝ) => Z i x) ⁻¹' t i)
        = μ ((fun ω : Ω => Z i (ω, x0)) ⁻¹' t i) := by
      intro i hi
      rw [hset i, hmapB _ ((hZmeas i) (ht i hi))]
    rw [Finset.prod_congr rfl hRHS]
    exact hZ0 S ht
  exact hmain
  /- @proof-region region.target-node.session.68b756049ddbe3eb end -/

end Statlib.Imported

