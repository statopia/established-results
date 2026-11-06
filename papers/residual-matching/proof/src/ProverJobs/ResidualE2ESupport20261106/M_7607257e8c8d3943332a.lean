import Lean
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
namespace ResidualSparseRepair

/-- Independent Gaussian entries determine the complete matrix law. -/
theorem gaussian_matrix_map {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hG1 : ∀ i j, Measurable fun ω => G ω i j)
    (hG2 : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => G ω ij.1 ij.2) μ)
    (hG3 : ∀ i j, Measure.map (fun ω => G ω i j) μ = gaussianReal 0 1) :
    Measure.map G μ = stdNormalMatrixMeasure m n := by
  have hGmeas : Measurable G := by
    rw [measurable_pi_iff]
    intro i
    rw [measurable_pi_iff]
    intro j
    exact hG1 i j
  have hΦmeas : Measurable (fun ω : Ω => fun s : (i : Fin m) × Fin n => G ω s.1 s.2) := by
    rw [measurable_pi_iff]
    intro s
    exact hG1 s.1 s.2
  have hG2' : iIndepFun (fun (s : (i : Fin m) × Fin n) (ω : Ω) => G ω s.1 s.2) μ := by
    have hinj : Function.Injective (fun s : (i : Fin m) × Fin n => (s.1, s.2)) := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    exact hG2.precomp hinj
  have hmapSigma : Measure.map (fun ω : Ω => fun s : (i : Fin m) × Fin n => G ω s.1 s.2) μ
      = Measure.pi (fun _ : (i : Fin m) × Fin n => gaussianReal 0 1) := by
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (μ := μ)
      (β := fun _ : (i : Fin m) × Fin n => ℝ)
      (f := fun (s : (i : Fin m) × Fin n) (ω : Ω) => G ω s.1 s.2)
      (fun s => Measurable.aemeasurable (hG1 s.1 s.2))).mp hG2'
    have hfun : (fun s : (i : Fin m) × Fin n => Measure.map (fun ω => G ω s.1 s.2) μ)
        = (fun _ : (i : Fin m) × Fin n => gaussianReal 0 1) :=
      funext (fun s => hG3 s.1 s.2)
    rw [hfun] at h
    exact h
  have hpinSigma : Measure.pi (fun _ : (i : Fin m) × Fin n => (gaussianReal 0 1 : Measure ℝ))
      = Measure.infinitePi (fun _ : (i : Fin m) × Fin n => (gaussianReal 0 1 : Measure ℝ)) :=
    (MeasureTheory.Measure.infinitePi_eq_pi
      (μ := fun _ : (i : Fin m) × Fin n => (gaussianReal 0 1 : Measure ℝ))).symm
  have hcurry_measSigma : Measurable
      (⇑(MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ))) :=
    (MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ)).measurable
  have hcomp : (⇑(MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ)) ∘
      (fun ω : Ω => fun s : (i : Fin m) × Fin n => G ω s.1 s.2)) = G := by
    funext ω i j
    rfl
  have hcurry : Measure.map (⇑(MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ)))
      (Measure.infinitePi (fun _ : (i : Fin m) × Fin n => (gaussianReal 0 1 : Measure ℝ)))
      = Measure.infinitePi (fun _ : Fin m => Measure.infinitePi
          (fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ))) :=
    MeasureTheory.Measure.infinitePi_map_piCurry
      (μ := fun (_ : Fin m) (_ : Fin n) => (gaussianReal 0 1 : Measure ℝ))
  have hpi_pi : Measure.infinitePi (fun _ : Fin m => Measure.infinitePi
        (fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ))) = stdNormalMatrixMeasure m n := by
    have hinner : IsProbabilityMeasure (Measure.infinitePi
        (fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ))) := by
      rw [MeasureTheory.Measure.infinitePi_eq_pi
        (μ := fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ))]
      exact inferInstance
    haveI : ∀ _ : Fin m, IsProbabilityMeasure (Measure.infinitePi
        (fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ))) := fun _ => hinner
    rw [MeasureTheory.Measure.infinitePi_eq_pi
      (μ := fun _ : Fin m => Measure.infinitePi (fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ)))]
    have houter : (fun _ : Fin m => Measure.infinitePi
          (fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ)))
        = (fun _ : Fin m => Measure.pi (fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ))) :=
      funext (fun _ => MeasureTheory.Measure.infinitePi_eq_pi
        (μ := fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ)))
    rw [houter]
    rfl
  have hmap : Measure.map G μ = stdNormalMatrixMeasure m n := by
    calc Measure.map G μ
        = Measure.map ((⇑(MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ))) ∘
            (fun ω : Ω => fun s : (i : Fin m) × Fin n => G ω s.1 s.2)) μ := by rw [hcomp]
      _ = Measure.map (⇑(MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ)))
            (Measure.map (fun ω : Ω => fun s : (i : Fin m) × Fin n => G ω s.1 s.2) μ) :=
          (MeasureTheory.Measure.map_map hcurry_measSigma hΦmeas).symm
      _ = Measure.map (⇑(MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ)))
            (Measure.pi (fun _ : (i : Fin m) × Fin n => gaussianReal 0 1)) := by rw [hmapSigma]
      _ = Measure.map (⇑(MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ)))
            (Measure.infinitePi (fun _ : (i : Fin m) × Fin n => gaussianReal 0 1)) := by
          rw [hpinSigma]
      _ = Measure.infinitePi (fun _ : Fin m => Measure.infinitePi
            (fun _ : Fin n => (gaussianReal 0 1 : Measure ℝ))) := hcurry
      _ = stdNormalMatrixMeasure m n := hpi_pi
  exact hmap

/-- The canonical matrix product measure satisfies the entrywise interface. -/
theorem standard_gaussian_coordinates (m n : ℕ) :
    (∀ i j, Measurable fun ω : Matrix (Fin m) (Fin n) ℝ => ω i j) ∧
    iIndepFun (fun (ij : Fin m × Fin n) (ω : Matrix (Fin m) (Fin n) ℝ) => ω ij.1 ij.2)
      (stdNormalMatrixMeasure m n) ∧
    (∀ i j, Measure.map (fun ω : Matrix (Fin m) (Fin n) ℝ => ω i j)
      (stdNormalMatrixMeasure m n) = gaussianReal 0 1) := by
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  have hmeas : ∀ i j, Measurable fun ω : Matrix (Fin m) (Fin n) ℝ => ω i j := by
    intro i j
    have h1 : Measurable fun ω : Matrix (Fin m) (Fin n) ℝ => ω i := measurable_pi_apply i
    have h2 : Measurable fun v : Fin n → ℝ => v j := measurable_pi_apply j
    exact h2.comp h1
  have hmarg : ∀ i j, Measure.map (fun ω : Matrix (Fin m) (Fin n) ℝ => ω i j)
      (stdNormalMatrixMeasure m n) = gaussianReal 0 1 := by
    intro i j
    have hrow : Measure.map (fun ω : Matrix (Fin m) (Fin n) ℝ => ω i)
        (stdNormalMatrixMeasure m n) = Measure.pi (fun _ : Fin n => gaussianReal 0 1) :=
      (MeasureTheory.measurePreserving_eval
        (fun _ : Fin m => Measure.pi (fun _ : Fin n => gaussianReal 0 1)) i).map_eq
    have hcol : Measure.map (fun v : Fin n → ℝ => v j)
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) = gaussianReal 0 1 :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) j).map_eq
    rw [← hcol, ← hrow]
    exact (MeasureTheory.Measure.map_map (measurable_pi_apply j)
      (measurable_pi_apply i)).symm
  have hunc : Measurable (fun ω : Matrix (Fin m) (Fin n) ℝ =>
      fun p : Fin m × Fin n => ω p.1 p.2) :=
    measurable_pi_iff.mpr (fun p => hmeas p.1 p.2)
  have hflat : Measure.map (fun ω : Matrix (Fin m) (Fin n) ℝ =>
      fun p : Fin m × Fin n => ω p.1 p.2) (stdNormalMatrixMeasure m n)
      = Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) := by
    have hbox : ∀ s : (p : Fin m × Fin n) → Set ℝ, (∀ p, MeasurableSet (s p)) →
        (Measure.map (fun ω : Matrix (Fin m) (Fin n) ℝ =>
            fun p : Fin m × Fin n => ω p.1 p.2) (stdNormalMatrixMeasure m n))
            (Set.univ.pi s) = ∏ p, gaussianReal 0 1 (s p) := by
      intro s hs
      have hset : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
      have hpre : (fun f : (i : Fin m) → (Fin n → ℝ) =>
          fun p : Fin m × Fin n => f p.1 p.2) ⁻¹' (Set.univ.pi s)
          = Set.univ.pi (fun i : Fin m => Set.univ.pi (fun j : Fin n => s (i, j))) := by
        ext f
        simp only [Set.mem_preimage, Set.mem_univ_pi, Prod.forall]
      have hinner : (stdNormalMatrixMeasure m n)
          (Set.univ.pi (fun i : Fin m => Set.univ.pi (fun j : Fin n => s (i, j))))
          = ∏ p : Fin m × Fin n, gaussianReal 0 1 (s p) := by
        have hdef : stdNormalMatrixMeasure m n
            = Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := rfl
        rw [hdef]
        rw [MeasureTheory.Measure.pi_pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => gaussianReal 0 1))
          (fun i : Fin m => Set.univ.pi (fun j : Fin n => s (i, j)))]
        rw [Fintype.prod_prod_type]
        exact Finset.prod_congr rfl (fun i _ =>
          MeasureTheory.Measure.pi_pi (fun _ : Fin n => gaussianReal 0 1) (fun j : Fin n => s (i, j)))
      rw [MeasureTheory.Measure.map_apply hunc hset]
      exact (congrArg (stdNormalMatrixMeasure m n) hpre).trans hinner
    exact (MeasureTheory.Measure.pi_eq (μ := fun _ : Fin m × Fin n => gaussianReal 0 1)
      hbox).symm
  have hindep :
      iIndepFun (fun (ij : Fin m × Fin n) (ω : Matrix (Fin m) (Fin n) ℝ) => ω ij.1 ij.2)
        (stdNormalMatrixMeasure m n) := by
    refine (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (f := fun (ij : Fin m × Fin n) (ω : Matrix (Fin m) (Fin n) ℝ) => ω ij.1 ij.2)
      (fun p => (hmeas p.1 p.2).aemeasurable)).mpr ?_
    have hfac : (fun p : Fin m × Fin n => Measure.map
        (fun ω : Matrix (Fin m) (Fin n) ℝ => ω p.1 p.2) (stdNormalMatrixMeasure m n))
        = fun _ => gaussianReal 0 1 := by
      funext p
      exact hmarg p.1 p.2
    rw [hflat, hfac]
  exact ⟨hmeas, hindep, hmarg⟩

/-- Any measurable statistic has the same expectation under the entrywise interface. -/
theorem gaussian_statistic_integral {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hG1 : ∀ i j, Measurable fun ω => G ω i j)
    (hG2 : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => G ω ij.1 ij.2) μ)
    (hG3 : ∀ i j, Measure.map (fun ω => G ω i j) μ = gaussianReal 0 1)
    (f : Matrix (Fin m) (Fin n) ℝ → ℝ) (hf : Measurable f) :
    (∫ ω, f (G ω) ∂μ) = ∫ A, f A ∂stdNormalMatrixMeasure m n := by
  have hG : Measurable G := measurable_pi_iff.mpr fun i =>
    measurable_pi_iff.mpr fun j => hG1 i j
  rw [← gaussian_matrix_map μ G hG1 hG2 hG3]
  exact (integral_map hG.aemeasurable hf.aestronglyMeasurable).symm

#print axioms gaussian_matrix_map
#print axioms standard_gaussian_coordinates
#print axioms gaussian_statistic_integral
end ResidualSparseRepair

