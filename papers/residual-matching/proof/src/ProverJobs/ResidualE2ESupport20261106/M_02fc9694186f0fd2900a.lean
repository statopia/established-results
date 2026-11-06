import Statlib.HighDim.CovarianceMatrix.SampleCovariance
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_5fd4d9e477d6a3241c2c
import ProverJobs.ResidualE2ESupport20261106.M_71771031c80e5d133256
import ProverJobs.ResidualE2ESupport20261106.M_a9c8b1ebca5a72d811ce
import ProverJobs.ResidualE2ESupport20261106.M_ec84b30d1455d4bd76b3
import ProverJobs.ResidualE2ESupport20261106.M_e6124e6b261ca5717075

import ProverJobs.ResidualE2ESupport20261106.M_97bf2c576cc17ed23abb
import ProverJobs.ResidualE2ESupport20261106.M_41404a657eb68a6e78b5
import ProverJobs.ResidualE2ESupport20261106.M_980b891c3f736879830b
import ProverJobs.ResidualE2ESupport20261106.M_4c185f8e948d76caeb7e
import Statlib.HighDim.CovarianceMatrix.SampleCovariance

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option maxHeartbeats 4000000
namespace ResidualMaskRepair20261106
universe u
noncomputable section

theorem mask_norm_vs_gaussian_mean : ∃ C : ℝ, 0 < C ∧
  ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hpStrict : p < 1)
    {Ωm : Type u} [MeasurableSpace Ωm] (P : Measure Ωm) [IsProbabilityMeasure P]
    (Om : Fin m → Fin n → Ωm → ℝ)
    (hOm_meas : ∀ i j, Measurable (Om i j))
    (hOm_indep : iIndepFun (fun ij : Fin m × Fin n => Om ij.1 ij.2) P)
    (hOm_bin : ∀ i j, ∀ᵐ ω ∂P, Om i j ω = 0 ∨ Om i j ω = 1)
    (hOm_int : ∀ i j, Integrable (Om i j) P)
    (hOm_mean : ∀ i j, ∫ ω, Om i j ω ∂P = p)
    (hOm_point : ∀ i j ω, Om i j ω = 0 ∨ Om i j ω = 1)
    (t : ℝ) (ht : 0 ≤ t),
    let γ := Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 ((1-p)/(m:ℝ)).toNNReal)
    (P.prod γ) {x : Ωm × ((Fin m × Fin n) → ℝ) |
      C * (Real.sqrt ((1-p)/(m:ℝ)) * Real.sqrt t +
        (1 / Real.sqrt ((m:ℝ)*p)) ^ ((1:ℝ)/3) * (Real.sqrt (1-p)) ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) +
        (1 / Real.sqrt ((m:ℝ)*p)) * t) <
      |specNorm (fun i j => (Om i j x.1 - p) / Real.sqrt ((m:ℝ)*p)) -
        ∫ y : Ωm × ((Fin m × Fin n) → ℝ), specNorm (fun i j => y.2 (i,j)) ∂(P.prod γ)|}
      ≤ ENNReal.ofReal (((m+n:ℕ):ℝ) * Real.exp (-t)) := by
  obtain ⟨Cbig, hCbig, hmain⟩ := ResidualSparseRepair20261106.bvh_upper_concentration.{u}
  refine ⟨Cbig, hCbig, ?_⟩
  intro m n hm hn hnm p hp0 hp1 hpStrict Ωm _ P _ Om hOm_meas hOm_indep hOm_bin hOm_int hOm_mean hOm_point t ht
  dsimp only
  let xi : Ωm → Fin m → Fin n → ℝ :=
    fun ω i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)
  let Xcheck : Ωm × ((Fin m × Fin n) → ℝ) → Matrix (Fin m) (Fin n) ℝ :=
    fun x => Matrix.of (fun i j => xi x.1 i j)
  let Gmat : Ωm × ((Fin m × Fin n) → ℝ) → Matrix (Fin m) (Fin n) ℝ :=
    fun x => Matrix.of (fun i j => x.2 (i, j))
  let gamma : Measure ((Fin m × Fin n) → ℝ) :=
    Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 ((1 - p) / (m : ℝ)).toNNReal)
  have hd2 : 2 ≤ m + n := Nat.add_le_add (Nat.succ_le_of_lt hm) (Nat.succ_le_of_lt hn)
  have hprob : IsProbabilityMeasure gamma := inferInstance
  haveI := hprob
  have hprob2 : IsProbabilityMeasure (Measure.prod P gamma) := inferInstance
  haveI := hprob2
  obtain ⟨hdep1, hdep2, hdep3, hdep4, hdep5, hdep6, hdep7, hdep8, hdep9, hdep10, hdep11,
    hdep12, hdep13, hdep14, hdep15, hdep16, hdep17, hdep18, hdep19, hdep20, hdep21,
    hdep22, hdep23⟩ :=
    statopia_math_node_2157505147_d4ab740e m n hm hn hnm p hp0 hp1 P Om hOm_meas
      hOm_indep hOm_bin hOm_int hOm_mean
  have hxiProd : ∀ᵐ x ∂(Measure.prod P gamma), ∀ (i : Fin m) (j : Fin n),
      |(Om i j x.1 - p) / Real.sqrt ((m : ℝ) * p)|
        ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p) := by
    rw [MeasureTheory.ae_iff]
    have hnull : P {ω : Ωm | ¬ (∀ (i : Fin m) (j : Fin n),
        |(Om i j ω - p) / Real.sqrt ((m : ℝ) * p)|
          ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p))} = 0 :=
      MeasureTheory.ae_iff.mp hdep17
    have hset : {x : Ωm × ((Fin m × Fin n) → ℝ) | ¬ (∀ (i : Fin m) (j : Fin n),
        |(Om i j x.1 - p) / Real.sqrt ((m : ℝ) * p)|
          ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p))}
        = {ω : Ωm | ¬ (∀ (i : Fin m) (j : Fin n),
            |(Om i j ω - p) / Real.sqrt ((m : ℝ) * p)|
              ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p))} ×ˢ Set.univ := by
      ext x
      simp
    rw [hset, MeasureTheory.Measure.prod_prod, hnull, zero_mul]

  let e := Fintype.equivFin (Fin m × Fin n)
  let Zblk : Fin (Fintype.card (Fin m × Fin n)) →
      (Ωm × ((Fin m × Fin n) → ℝ)) → Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun k x => Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
      (Matrix.of (fun (a : Fin m) (b : Fin n) =>
        ((xi x.1 (e.symm k).1 (e.symm k).2
          * matrixUnit (e.symm k).1 (e.symm k).2 a b : ℝ) : ℂ)))
      (Matrix.of (fun (a : Fin m) (b : Fin n) =>
        ((xi x.1 (e.symm k).1 (e.symm k).2
          * matrixUnit (e.symm k).1 (e.symm k).2 a b : ℝ) : ℂ))).conjTranspose
      (0 : Matrix (Fin n) (Fin n) ℂ)
  let Zfam : Fin (Fintype.card (Fin m × Fin n)) →
      (Ωm × ((Fin m × Fin n) → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun k x => (Zblk k x).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  have hZsa : ∀ (k : Fin (Fintype.card (Fin m × Fin n)))
      (x : Ωm × ((Fin m × Fin n) → ℝ)), (Zfam k x).IsHermitian := by
    intro k x
    exact Matrix.IsHermitian.submatrix
      (Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero rfl Matrix.isHermitian_zero) _
  have hXsa : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
      ((0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
        + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x).IsHermitian := by
    intro x
    have hsum : (∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x).IsHermitian := by
      classical
      refine Finset.induction ?_ ?_ Finset.univ
      · simpa using
          (Matrix.isHermitian_zero : (0 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ).IsHermitian)
      · intro a s ha ih
        rw [Finset.sum_insert ha]
        exact Matrix.IsHermitian.add (hZsa a x) ih
    rw [zero_add]
    exact hsum
  let Gblk : (Ωm × ((Fin m × Fin n) → ℝ)) → Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun x => Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
      (Matrix.of (fun (i : Fin m) (j : Fin n) => ((Gmat x i j : ℝ) : ℂ)))
      (Matrix.of (fun (i : Fin m) (j : Fin n) => ((Gmat x i j : ℝ) : ℂ))).conjTranspose
      (0 : Matrix (Fin n) (Fin n) ℂ)
  let Gdil : (Ωm × ((Fin m × Fin n) → ℝ)) → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun x => (Gblk x).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  have hGsa : ∀ x : Ωm × ((Fin m × Fin n) → ℝ), (Gdil x).IsHermitian := by
    intro x
    exact Matrix.IsHermitian.submatrix
      (Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero rfl Matrix.isHermitian_zero) _
  have hZmeas : ∀ i : Fin (Fintype.card (Fin m × Fin n)), Measurable (Zfam i) := by
    intro i
    refine measurable_pi_iff.mpr (fun a => measurable_pi_iff.mpr (fun b => ?_))
    have hxi : Measurable (fun x : Ωm × ((Fin m × Fin n) → ℝ) =>
        (Om (e.symm i).1 (e.symm i).2 x.1 - p) / Real.sqrt ((m : ℝ) * p)) :=
      Measurable.div_const
        (Measurable.sub ((hOm_meas (e.symm i).1 (e.symm i).2).comp measurable_fst)
          measurable_const) _
    have hxiC : Measurable (fun x : Ωm × ((Fin m × Fin n) → ℝ) =>
        ((xi x.1 (e.symm i).1 (e.symm i).2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp hxi
    cases hv : finSumFinEquiv.symm a with
    | inl u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v => simpa [Zfam, Zblk, hv, hw] using measurable_const
      | inr v =>
        have h2 : Measurable (fun x : Ωm × ((Fin m × Fin n) → ℝ) =>
            ((xi x.1 (e.symm i).1 (e.symm i).2 : ℝ) : ℂ)
              * ((matrixUnit (e.symm i).1 (e.symm i).2 u v : ℝ) : ℂ)) :=
          hxiC.mul_const _
        simpa [Zfam, Zblk, hv, hw] using h2
    | inr u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v =>
        have h2 : Measurable (fun x : Ωm × ((Fin m × Fin n) → ℝ) =>
            ((xi x.1 (e.symm i).1 (e.symm i).2 : ℝ) : ℂ)
              * ((matrixUnit (e.symm i).1 (e.symm i).2 v u : ℝ) : ℂ)) :=
          hxiC.mul_const _
        simpa [Zfam, Zblk, hv, hw] using h2
      | inr v => simpa [Zfam, Zblk, hv, hw] using measurable_const
  have hGmeas : Measurable Gdil := by
    refine measurable_pi_iff.mpr (fun a => measurable_pi_iff.mpr (fun b => ?_))
    cases hv : finSumFinEquiv.symm a with
    | inl u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v => simpa [Gdil, Gblk, hv, hw] using measurable_const
      | inr v =>
        have h1 : Measurable (fun ω : Ωm × ((Fin m × Fin n) → ℝ) => ω.2 (u, v)) :=
          (measurable_pi_apply (u, v)).comp measurable_snd
        have h2 : Measurable (fun ω : Ωm × ((Fin m × Fin n) → ℝ) =>
            ((ω.2 (u, v) : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.measurable.comp h1
        simpa [Gdil, Gblk, hv, hw] using h2
    | inr u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v =>
        have h1 : Measurable (fun ω : Ωm × ((Fin m × Fin n) → ℝ) => ω.2 (v, u)) :=
          (measurable_pi_apply (v, u)).comp measurable_snd
        have h2 : Measurable (fun ω : Ωm × ((Fin m × Fin n) → ℝ) =>
            star (((ω.2 (v, u) : ℝ)) : ℂ)) :=
          continuous_star.measurable.comp (Complex.continuous_ofReal.measurable.comp h1)
        simpa [Gdil, Gblk, hv, hw] using h2
      | inr v => simpa [Gdil, Gblk, hv, hw] using measurable_const
  have hZint : ∀ (i : Fin (Fintype.card (Fin m × Fin n))) (a b : Fin (m + n)),
      Integrable (fun x : Ωm × ((Fin m × Fin n) → ℝ) => (Zfam i x) a b)
        (Measure.prod P gamma) := by
    intro i a b
    refine MeasureTheory.Integrable.of_bound ?_ (max p (1 - p) / Real.sqrt ((m : ℝ) * p)) ?_
    · exact ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hZmeas i))).aestronglyMeasurable
    · have hR0 : (0 : ℝ) ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p) := hdep19.le
      have hcn : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := fun r => by simp
      have hkey : ∀ (r c : ℝ), |r| ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p) → |c| ≤ 1 →
          ‖((r : ℂ) * (c : ℂ))‖ ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p) := by
        intro r c hr hc
        rw [norm_mul, hcn r, hcn c]
        calc |r| * |c| ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p) * 1 :=
              mul_le_mul hr hc (abs_nonneg c) hR0
          _ = max p (1 - p) / Real.sqrt ((m : ℝ) * p) := mul_one _
      have hmunit : ∀ (u : Fin m) (v : Fin n) (s : Fin m) (t : Fin n),
          |matrixUnit u v s t| ≤ 1 := by
        intro u v s t
        simp only [matrixUnit]
        split_ifs <;> simp
      filter_upwards [hxiProd] with x hx
      have hr : |xi x.1 (e.symm i).1 (e.symm i).2| ≤
          max p (1 - p) / Real.sqrt ((m : ℝ) * p) := by
        simpa [xi] using hx (e.symm i).1 (e.symm i).2
      cases hv : finSumFinEquiv.symm a with
      | inl u =>
        cases hw : finSumFinEquiv.symm b with
        | inl v => simpa [Zfam, Zblk, hv, hw] using hR0
        | inr v =>
          have h := hkey (xi x.1 (e.symm i).1 (e.symm i).2)
            (matrixUnit (e.symm i).1 (e.symm i).2 u v) hr (hmunit _ _ _ _)
          simpa [Zfam, Zblk, hv, hw] using h
      | inr u =>
        cases hw : finSumFinEquiv.symm b with
        | inl v =>
          have h := hkey (xi x.1 (e.symm i).1 (e.symm i).2)
            (matrixUnit (e.symm i).1 (e.symm i).2 v u) hr (hmunit _ _ _ _)
          simpa [Zfam, Zblk, hv, hw] using h
        | inr v => simpa [Zfam, Zblk, hv, hw] using hR0
  have hZfamD : ∀ (k : Fin (Fintype.card (Fin m × Fin n)))
      (x : Ωm × ((Fin m × Fin n) → ℝ)) (a b : Fin (m + n)),
      (Zfam k x) a b =
        Complex.ofReal (((Om (e.symm k).1 (e.symm k).2 x.1 - p) /
            Real.sqrt ((m : ℝ) * p)) *
          (Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (matrixUnit (e.symm k).1 (e.symm k).2)
              (matrixUnit (e.symm k).1 (e.symm k).2).transpose
              (0 : Matrix (Fin n) (Fin n) ℝ))) a b) := by
    intro k x a b
    cases hv : finSumFinEquiv.symm a with
    | inl u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v =>
        simp [Zfam, Zblk, xi, hv, hw, Matrix.reindex_apply]
      | inr v =>
        simp [Zfam, Zblk, xi, hv, hw, Matrix.reindex_apply, Matrix.transpose_apply]
    | inr u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v =>
        simp [Zfam, Zblk, xi, hv, hw, Matrix.reindex_apply, Matrix.transpose_apply,
          Complex.conj_ofReal]
      | inr v =>
        simp [Zfam, Zblk, xi, hv, hw, Matrix.reindex_apply]
  have hsndInt : ∀ (f : ((Fin m × Fin n) → ℝ) → ℂ),
      AEStronglyMeasurable f gamma →
      ∫ x : Ωm × ((Fin m × Fin n) → ℝ), f x.2 ∂(Measure.prod P gamma) = ∫ z, f z ∂gamma := by
    intro f hf
    have hmap : Measure.map Prod.snd (Measure.prod P gamma) = gamma :=
      (MeasureTheory.measurePreserving_snd (μ := P) (ν := gamma)).map_eq
    have hf' : AEStronglyMeasurable f (Measure.map Prod.snd (Measure.prod P gamma)) := by
      rw [hmap]
      exact hf
    have h := MeasureTheory.integral_map (μ := Measure.prod P gamma) (φ := Prod.snd)
      measurable_snd.aemeasurable (f := f) hf'
    rw [hmap] at h
    exact h.symm
  have hfstInt : ∀ (f : Ωm → ℝ), AEStronglyMeasurable f P →
      ∫ x : Ωm × ((Fin m × Fin n) → ℝ), f x.1 ∂(Measure.prod P gamma) = ∫ ω, f ω ∂P := by
    intro f hf
    have hmap : Measure.map Prod.fst (Measure.prod P gamma) = P :=
      (MeasureTheory.measurePreserving_fst (μ := P) (ν := gamma)).map_eq
    have hf' : AEStronglyMeasurable f (Measure.map Prod.fst (Measure.prod P gamma)) := by
      rw [hmap]
      exact hf
    have h := MeasureTheory.integral_map (μ := Measure.prod P gamma) (φ := Prod.fst)
      measurable_fst.aemeasurable (f := f) hf'
    rw [hmap] at h
    exact h.symm

  have hGdilMat : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
      Gdil x = Matrix.of (fun a b : Fin (m + n) =>
        ((Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (Gmat x) (Gmat x).transpose
            (0 : Matrix (Fin n) (Fin n) ℝ)) a b : ℝ) : ℂ)) := by
    intro x
    ext a b
    cases hv : finSumFinEquiv.symm a with
    | inl u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v => simp [Gdil, Gblk, Gmat, hv, hw, Matrix.reindex_apply]
      | inr v =>
        simp [Gdil, Gblk, Gmat, hv, hw, Matrix.reindex_apply, Matrix.transpose_apply]
    | inr u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v =>
        simp [Gdil, Gblk, Gmat, hv, hw, Matrix.reindex_apply, Matrix.transpose_apply,
          Complex.conj_ofReal]
      | inr v => simp [Gdil, Gblk, Gmat, hv, hw, Matrix.reindex_apply]
  have hGsig : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
      (⨆ a : Fin (m + n), |(Matrix.IsHermitian.eigenvalues (hGsa x) a)|)
        = specNorm (Gmat x) := by
    intro x
    have heigG : ∀ (M N : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) (h : M = N)
        (hM : M.IsHermitian) (a : Fin (m + n)),
        Matrix.IsHermitian.eigenvalues (h ▸ hM) a = Matrix.IsHermitian.eigenvalues hM a := by
      rintro M N rfl hM a
      rfl
    have hchild := statopia_math_node_740990000_94fc0980 m n
      (lt_of_lt_of_le (show (0 : ℕ) < 2 by norm_num) hd2)
      (Gmat x) (hGdilMat x ▸ hGsa x)
    rw [show (⨆ a : Fin (m + n), |(Matrix.IsHermitian.eigenvalues (hGsa x) a)|)
        = (⨆ a : Fin (m + n),
            |(Matrix.IsHermitian.eigenvalues (hGdilMat x ▸ hGsa x) a)|) from
      iSup_congr (fun a => by rw [heigG (Gdil x) _ (hGdilMat x) (hGsa x) a])]
    rw [hchild]
    exact statopia_math_node_992664654_dad774ce m n (Gmat x)

  have hZmean : ∀ (i : Fin (Fintype.card (Fin m × Fin n))) (a b : Fin (m + n)),
      ∫ ω, Zfam i ω a b ∂(Measure.prod P gamma) = 0 := by
    intro i a b
    have hmeasR : Measurable (fun ω : Ωm =>
        (Om (e.symm i).1 (e.symm i).2 ω - p) / Real.sqrt ((m : ℝ) * p)) :=
      Measurable.div_const (Measurable.sub (hOm_meas (e.symm i).1 (e.symm i).2)
        measurable_const) _
    have hIxi : Integrable (fun x : Ωm × ((Fin m × Fin n) → ℝ) =>
        (Om (e.symm i).1 (e.symm i).2 x.1 - p) / Real.sqrt ((m : ℝ) * p))
        (Measure.prod P gamma) := by
      refine MeasureTheory.Integrable.of_bound ?_ (max p (1 - p) / Real.sqrt ((m : ℝ) * p)) ?_
      · exact (hmeasR.comp measurable_fst).aestronglyMeasurable
      · filter_upwards [hxiProd] with x hx
        have hr : |xi x.1 (e.symm i).1 (e.symm i).2| ≤
            max p (1 - p) / Real.sqrt ((m : ℝ) * p) := by
          simpa [xi] using hx (e.symm i).1 (e.symm i).2
        rw [Real.norm_eq_abs]
        exact hr
    have hbridgeCLM : (∫ x : Ωm × ((Fin m × Fin n) → ℝ),
        Complex.ofRealCLM ((Om (e.symm i).1 (e.symm i).2 x.1 - p) /
          Real.sqrt ((m : ℝ) * p)) ∂(Measure.prod P gamma)) = 0 := by
      rw [ContinuousLinearMap.integral_comp_comm (μ := Measure.prod P gamma)
        (φ := fun x : Ωm × ((Fin m × Fin n) → ℝ) =>
          (Om (e.symm i).1 (e.symm i).2 x.1 - p) / Real.sqrt ((m : ℝ) * p))
        Complex.ofRealCLM hIxi]
      rw [hfstInt (fun ω => (Om (e.symm i).1 (e.symm i).2 ω - p) /
        Real.sqrt ((m : ℝ) * p)) hmeasR.aestronglyMeasurable]
      rw [hdep10 (e.symm i).1 (e.symm i).2]
      simp
    have hbridge : (∫ x : Ωm × ((Fin m × Fin n) → ℝ),
        Complex.ofReal ((Om (e.symm i).1 (e.symm i).2 x.1 - p) / Real.sqrt ((m : ℝ) * p))
          ∂(Measure.prod P gamma)) = 0 := by
      rw [show (∫ x : Ωm × ((Fin m × Fin n) → ℝ),
          Complex.ofReal ((Om (e.symm i).1 (e.symm i).2 x.1 - p) /
            Real.sqrt ((m : ℝ) * p)) ∂(Measure.prod P gamma))
          = (∫ x : Ωm × ((Fin m × Fin n) → ℝ),
              Complex.ofRealCLM ((Om (e.symm i).1 (e.symm i).2 x.1 - p) /
                Real.sqrt ((m : ℝ) * p)) ∂(Measure.prod P gamma)) from by
        refine integral_congr_ae ?_
        filter_upwards with x
        rfl]
      exact hbridgeCLM

    have hEq : ∫ x : Ωm × ((Fin m × Fin n) → ℝ), Zfam i x a b ∂(Measure.prod P gamma)
        = (∫ x : Ωm × ((Fin m × Fin n) → ℝ),
            Complex.ofReal ((Om (e.symm i).1 (e.symm i).2 x.1 - p) /
              Real.sqrt ((m : ℝ) * p)) ∂(Measure.prod P gamma)) *
          (((Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (matrixUnit (e.symm i).1 (e.symm i).2)
              (matrixUnit (e.symm i).1 (e.symm i).2).transpose
              (0 : Matrix (Fin n) (Fin n) ℝ))) a b : ℝ) : ℂ) := by
      rw [← MeasureTheory.integral_mul_const
        ((((Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (matrixUnit (e.symm i).1 (e.symm i).2)
              (matrixUnit (e.symm i).1 (e.symm i).2).transpose
              (0 : Matrix (Fin n) (Fin n) ℝ))) a b : ℝ) : ℂ))
        (fun x : Ωm × ((Fin m × Fin n) → ℝ) =>
          Complex.ofReal ((Om (e.symm i).1 (e.symm i).2 x.1 - p) /
            Real.sqrt ((m : ℝ) * p)))]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [hZfamD i x a b]
      push_cast
      ring
    rw [hEq, hbridge, zero_mul]
  have hxiInt : ∀ (u : Fin m) (v : Fin n),
      (∫ x : Ωm × ((Fin m × Fin n) → ℝ),
        Complex.ofReal ((Om u v x.1 - p) / Real.sqrt ((m : ℝ) * p))
          ∂(Measure.prod P gamma)) = 0 := by
    intro u v
    have hmeasR : Measurable (fun ω : Ωm => (Om u v ω - p) / Real.sqrt ((m : ℝ) * p)) :=
      Measurable.div_const (Measurable.sub (hOm_meas u v) measurable_const) _
    have hIxi : Integrable (fun x : Ωm × ((Fin m × Fin n) → ℝ) =>
        (Om u v x.1 - p) / Real.sqrt ((m : ℝ) * p)) (Measure.prod P gamma) := by
      refine MeasureTheory.Integrable.of_bound ?_ (max p (1 - p) / Real.sqrt ((m : ℝ) * p)) ?_
      · exact (hmeasR.comp measurable_fst).aestronglyMeasurable
      · filter_upwards [hxiProd] with x hx
        have hr : |xi x.1 u v| ≤ max p (1 - p) / Real.sqrt ((m : ℝ) * p) := by
          simpa [xi] using hx u v
        rw [Real.norm_eq_abs]
        exact hr
    have hbridgeCLM : (∫ x : Ωm × ((Fin m × Fin n) → ℝ),
        Complex.ofRealCLM ((Om u v x.1 - p) / Real.sqrt ((m : ℝ) * p))
          ∂(Measure.prod P gamma)) = 0 := by
      rw [ContinuousLinearMap.integral_comp_comm (μ := Measure.prod P gamma)
        (φ := fun x : Ωm × ((Fin m × Fin n) → ℝ) =>
          (Om u v x.1 - p) / Real.sqrt ((m : ℝ) * p))
        Complex.ofRealCLM hIxi]
      rw [hfstInt (fun ω => (Om u v ω - p) / Real.sqrt ((m : ℝ) * p))
        hmeasR.aestronglyMeasurable]
      rw [hdep10 u v]
      simp
    rw [show (∫ x : Ωm × ((Fin m × Fin n) → ℝ),
        Complex.ofReal ((Om u v x.1 - p) / Real.sqrt ((m : ℝ) * p))
          ∂(Measure.prod P gamma))
        = (∫ x : Ωm × ((Fin m × Fin n) → ℝ),
            Complex.ofRealCLM ((Om u v x.1 - p) / Real.sqrt ((m : ℝ) * p))
              ∂(Measure.prod P gamma)) from by
      refine integral_congr_ae ?_
      filter_upwards with x
      rfl]
    exact hbridgeCLM
  have hIdInt : Integrable (fun y : ℝ => y)
      (gaussianReal 0 (Real.toNNReal ((1 - p) / (m : ℝ)))) :=
    MeasureTheory.MemLp.integrable (le_refl (1 : ENNReal))
      (ProbabilityTheory.memLp_id_gaussianReal' (1 : ENNReal) (by norm_num))

  have hXsum : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
      (0 + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x)
        = Matrix.of (fun a b : Fin (m + n) =>
            ((Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (Xcheck x) (Xcheck x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ)) a b : ℝ) : ℂ)) := by
    intro x
    have hR : Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Xcheck x)
          (Xcheck x).transpose (0 : Matrix (Fin n) (Fin n) ℝ))
        = ∑ ij : Fin m × Fin n, xi x.1 ij.1 ij.2 •
            Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (matrixUnit ij.1 ij.2) (matrixUnit ij.1 ij.2).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ)) := hdep13 x.1
    ext a b
    show (0 + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x) a b
        = ((Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Xcheck x)
              (Xcheck x).transpose (0 : Matrix (Fin n) (Fin n) ℝ)) a b : ℝ) : ℂ)
    rw [Matrix.add_apply, Matrix.zero_apply, zero_add, Matrix.sum_apply, hR,
      Matrix.sum_apply, Complex.ofReal_sum]
    have hL : (∑ k : Fin (Fintype.card (Fin m × Fin n)), (Zfam k x) a b)
        = ∑ k : Fin (Fintype.card (Fin m × Fin n)),
            (((xi x.1 (e.symm k).1 (e.symm k).2 •
              Matrix.reindex finSumFinEquiv finSumFinEquiv
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                  (matrixUnit (e.symm k).1 (e.symm k).2)
                  (matrixUnit (e.symm k).1 (e.symm k).2).transpose
                  (0 : Matrix (Fin n) (Fin n) ℝ))) a b : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simpa [xi, Matrix.smul_apply] using hZfamD k x a b
    refine Eq.trans hL ?_
    exact Fintype.sum_equiv e.symm _ _ (fun k => by simp)
  have hXsig : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
      (⨆ a : Fin (m + n), |(Matrix.IsHermitian.eigenvalues (hXsa x) a)|)
        = specNorm (Xcheck x) := by
    intro x
    have heigX : ∀ (M N : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) (h : M = N)
        (hM : M.IsHermitian) (a : Fin (m + n)),
        Matrix.IsHermitian.eigenvalues (h ▸ hM) a = Matrix.IsHermitian.eigenvalues hM a := by
      rintro M N rfl hM a
      rfl
    have hchild := statopia_math_node_740990000_94fc0980 m n
      (lt_of_lt_of_le (show (0 : ℕ) < 2 by norm_num) hd2)
      (Xcheck x) (hXsum x ▸ hXsa x)
    rw [show (⨆ a : Fin (m + n), |(Matrix.IsHermitian.eigenvalues (hXsa x) a)|)
        = (⨆ a : Fin (m + n),
            |(Matrix.IsHermitian.eigenvalues (hXsum x ▸ hXsa x) a)|) from
      iSup_congr (fun a => by
        rw [heigX (0 + ∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x)
          _ (hXsum x) (hXsa x) a])]
    rw [hchild]
    exact statopia_math_node_992664654_dad774ce m n (Xcheck x)
  have hcoordIntC : ∀ (u : Fin m) (v : Fin n),
      (∫ x : Ωm × ((Fin m × Fin n) → ℝ), ((x.2 (u, v) : ℝ) : ℂ)
        ∂(Measure.prod P gamma)) = 0 := by
    intro u v
    have hmeasC : AEStronglyMeasurable
        (fun z : (Fin m × Fin n) → ℝ => ((z (u, v) : ℝ) : ℂ)) gamma :=
      (Complex.continuous_ofReal.measurable.comp (measurable_pi_apply (u, v))).aestronglyMeasurable
    rw [hsndInt (fun z : (Fin m × Fin n) → ℝ => ((z (u, v) : ℝ) : ℂ)) hmeasC]
    have hmap : Measure.map (fun z : (Fin m × Fin n) → ℝ => z (u, v)) gamma
        = gaussianReal 0 (Real.toNNReal ((1 - p) / (m : ℝ))) :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin m × Fin n =>
        gaussianReal 0 (Real.toNNReal ((1 - p) / (m : ℝ)))) (u, v)).map_eq
    have hstep : (∫ z : (Fin m × Fin n) → ℝ, ((z (u, v) : ℝ) : ℂ) ∂gamma)
        = ∫ y : ℝ, ((y : ℝ) : ℂ)
            ∂(gaussianReal 0 (Real.toNNReal ((1 - p) / (m : ℝ)))) := by
      have hf : AEStronglyMeasurable (fun t : ℝ => ((t : ℝ) : ℂ))
          (Measure.map (fun z : (Fin m × Fin n) → ℝ => z (u, v)) gamma) := by
        rw [hmap]
        exact Complex.continuous_ofReal.measurable.aestronglyMeasurable
      have h := MeasureTheory.integral_map (μ := gamma)
        (φ := fun z : (Fin m × Fin n) → ℝ => z (u, v))
        (measurable_pi_apply (u, v)).aemeasurable
        (f := fun t : ℝ => ((t : ℝ) : ℂ)) hf
      rw [hmap] at h
      exact h.symm
    rw [hstep]
    rw [show (∫ y : ℝ, ((y : ℝ) : ℂ)
          ∂(gaussianReal 0 (Real.toNNReal ((1 - p) / (m : ℝ)))))
        = ∫ y : ℝ, Complex.ofRealCLM y
            ∂(gaussianReal 0 (Real.toNNReal ((1 - p) / (m : ℝ)))) from by
      refine integral_congr_ae ?_
      filter_upwards with y
      rfl]
    rw [ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hIdInt]
    rw [ProbabilityTheory.integral_id_gaussianReal]
    simp
  have hGint0 : ∀ (a b : Fin (m + n)),
      (∫ x : Ωm × ((Fin m × Fin n) → ℝ), Gdil x a b ∂(Measure.prod P gamma)) = 0 := by
    intro a b
    have hbase : (∫ x : Ωm × ((Fin m × Fin n) → ℝ), Gdil x a b
          ∂(Measure.prod P gamma))
        = ∫ x : Ωm × ((Fin m × Fin n) → ℝ),
            Complex.ofReal ((Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (Gmat x) (Gmat x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ)) a b)) ∂(Measure.prod P gamma) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      have h1 := congrArg (fun M : Matrix (Fin (m + n)) (Fin (m + n)) ℂ => M a b) (hGdilMat x)
      simpa using h1
    rw [hbase]
    cases hv : finSumFinEquiv.symm a with
    | inl u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v =>
        have hentry : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
            (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Gmat x) (Gmat x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ))) a b = 0 := by
          intro x
          simp [Matrix.reindex_apply, hv, hw]
        simp only [hentry]
        simp
      | inr v =>
        have hentry : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
            (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Gmat x) (Gmat x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ))) a b = x.2 (u, v) := by
          intro x
          simp [Matrix.reindex_apply, hv, hw, Matrix.transpose_apply, Gmat]
        simp only [hentry]
        exact hcoordIntC u v
    | inr u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v =>
        have hentry : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
            (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Gmat x) (Gmat x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ))) a b = x.2 (v, u) := by
          intro x
          simp [Matrix.reindex_apply, hv, hw, Matrix.transpose_apply, Gmat]
        simp only [hentry]
        exact hcoordIntC v u
      | inr v =>
        have hentry : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
            (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Gmat x) (Gmat x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ))) a b = 0 := by
          intro x
          simp [Matrix.reindex_apply, hv, hw]
        simp only [hentry]
        simp
  have hZint0 : ∀ (a b : Fin (m + n)),
      (∫ x : Ωm × ((Fin m × Fin n) → ℝ), (0 + ∑ k, Zfam k x) a b
        ∂(Measure.prod P gamma)) = 0 := by
    intro a b
    have hbase : (∫ x : Ωm × ((Fin m × Fin n) → ℝ), (0 + ∑ k, Zfam k x) a b
          ∂(Measure.prod P gamma))
        = ∫ x : Ωm × ((Fin m × Fin n) → ℝ),
            Complex.ofReal ((Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (Xcheck x) (Xcheck x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ)) a b)) ∂(Measure.prod P gamma) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      have h1 := congrArg (fun M : Matrix (Fin (m + n)) (Fin (m + n)) ℂ => M a b) (hXsum x)
      simpa using h1
    rw [hbase]
    cases hv : finSumFinEquiv.symm a with
    | inl u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v =>
        have hentry : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
            (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Xcheck x) (Xcheck x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ))) a b = 0 := by
          intro x
          simp [Matrix.reindex_apply, hv, hw]
        simp only [hentry]
        simp
      | inr v =>
        have hentry : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
            (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Xcheck x) (Xcheck x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ))) a b = xi x.1 u v := by
          intro x
          simp [Matrix.reindex_apply, hv, hw, Matrix.transpose_apply, Xcheck]
        simp only [hentry]
        simpa [xi] using hxiInt u v
    | inr u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v =>
        have hentry : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
            (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Xcheck x) (Xcheck x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ))) a b = xi x.1 v u := by
          intro x
          simp [Matrix.reindex_apply, hv, hw, Matrix.transpose_apply, Xcheck]
        simp only [hentry]
        simpa [xi] using hxiInt v u
      | inr v =>
        have hentry : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
            (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Xcheck x) (Xcheck x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ))) a b = 0 := by
          intro x
          simp [Matrix.reindex_apply, hv, hw]
        simp only [hentry]
        simp
  have hGmean : ∀ (a b : Fin (m + n)),
      (∫ x : Ωm × ((Fin m × Fin n) → ℝ), Gdil x a b ∂(Measure.prod P gamma))
        = ∫ x : Ωm × ((Fin m × Fin n) → ℝ), (0 + ∑ k, Zfam k x) a b
            ∂(Measure.prod P gamma) := by
    intro a b
    rw [hGint0 a b, hZint0 a b]
  have hindep : iIndepFun Zfam (Measure.prod P gamma) := by
    let f : Fin (Fintype.card (Fin m × Fin n)) → Ωm →
        Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
      fun k ω => Matrix.of (fun a b => Complex.ofReal
        (((xi ω (e.symm k).1 (e.symm k).2) •
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (matrixUnit (e.symm k).1 (e.symm k).2)
              (matrixUnit (e.symm k).1 (e.symm k).2).transpose
              (0 : Matrix (Fin n) (Fin n) ℝ))) a b))
    have hf : iIndepFun f P := by
      have h1 : iIndepFun (fun k : Fin (Fintype.card (Fin m × Fin n)) => fun ω : Ωm =>
          xi ω (e.symm k).1 (e.symm k).2 •
            Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (matrixUnit (e.symm k).1 (e.symm k).2)
                (matrixUnit (e.symm k).1 (e.symm k).2).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ))) P :=
        ProbabilityTheory.iIndepFun.precomp
          (f := fun ij : Fin m × Fin n => fun ω : Ωm =>
            xi ω ij.1 ij.2 •
              Matrix.reindex finSumFinEquiv finSumFinEquiv
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                  (matrixUnit ij.1 ij.2) (matrixUnit ij.1 ij.2).transpose
                  (0 : Matrix (Fin n) (Fin n) ℝ)))
          (g := e.symm) e.symm.injective (by simpa [xi] using hdep12)
      have hcastMeas : ∀ _ : Fin (Fintype.card (Fin m × Fin n)),
          Measurable (fun M : Matrix (Fin (m + n)) (Fin (m + n)) ℝ =>
            Matrix.of (fun a b => ((M a b : ℝ) : ℂ))) := fun _ =>
        measurable_pi_iff.mpr (fun a => measurable_pi_iff.mpr (fun b =>
          Complex.continuous_ofReal.measurable.comp
            ((measurable_pi_apply b).comp (measurable_pi_apply a))))
      exact h1.comp (fun (_ : Fin (Fintype.card (Fin m × Fin n)))
          (M : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =>
            Matrix.of (fun a b => ((M a b : ℝ) : ℂ))) hcastMeas
    have hfun : (fun (k : Fin (Fintype.card (Fin m × Fin n)))
          (x : Ωm × ((Fin m × Fin n) → ℝ)) => f k x.1) = Zfam := by
      funext k x
      ext a b
      rw [hZfamD k x a b]
      simp only [f, Matrix.of_apply, Matrix.smul_apply, xi, smul_eq_mul]
    have h2 := statopia_math_node_3089955232_110a7522 P gamma f hf
    rw [hfun] at h2
    exact h2
  let Xt : Ωm → Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
    fun ω => Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
        (Matrix.of (fun i j => xi ω i j)) (Matrix.of (fun i j => xi ω i j)).transpose
        (0 : Matrix (Fin n) (Fin n) ℝ))
  let cov : Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
    Matrix.of (fun a b => ∫ ω, (Xt ω * Xt ω) a b ∂P)
  have hspecCov : specNorm cov = 1 - p := by
    simpa [cov, Xt, xi] using hdep4
  let M : ℝ := max p (1 - p) / Real.sqrt ((m : ℝ) * p)
  have hMnn : 0 ≤ M := hdep19.le
  have hZsum : ∀ x : Ωm × ((Fin m × Fin n) → ℝ),
      (∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x)
        = Matrix.of (fun a b : Fin (m + n) =>
            ((Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Xcheck x) (Xcheck x).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ)) a b : ℝ) : ℂ)) := by
    intro x
    rw [← zero_add (∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x)]
    exact hXsum x
  have hXtMeas : ∀ a c : Fin (m + n), Measurable (fun ω : Ωm => Xt ω a c) := by
    intro a c
    cases hv : finSumFinEquiv.symm a with
    | inl u =>
      cases hw : finSumFinEquiv.symm c with
      | inl v => simpa [Xt, hv, hw, Matrix.reindex_apply] using measurable_const
      | inr v =>
        have h : Measurable (fun ω : Ωm => xi ω u v) :=
          Measurable.div_const (Measurable.sub (hOm_meas u v) measurable_const) _
        simpa [Xt, xi, hv, hw, Matrix.reindex_apply, Matrix.transpose_apply] using h
    | inr u =>
      cases hw : finSumFinEquiv.symm c with
      | inl v =>
        have h : Measurable (fun ω : Ωm => xi ω v u) :=
          Measurable.div_const (Measurable.sub (hOm_meas v u) measurable_const) _
        simpa [Xt, xi, hv, hw, Matrix.reindex_apply, Matrix.transpose_apply] using h
      | inr v => simpa [Xt, hv, hw, Matrix.reindex_apply] using measurable_const
  have hXtBnd : ∀ᵐ x ∂(Measure.prod P gamma), ∀ a c : Fin (m + n), |Xt x.1 a c| ≤ M := by
    filter_upwards [hxiProd] with x hx
    intro a c
    cases hv : finSumFinEquiv.symm a with
    | inl u =>
      cases hw : finSumFinEquiv.symm c with
      | inl v => simpa [Xt, hv, hw, Matrix.reindex_apply] using hMnn
      | inr v =>
        have h := hx u v
        simpa [Xt, xi, M, hv, hw, Matrix.reindex_apply, Matrix.transpose_apply] using h
    | inr u =>
      cases hw : finSumFinEquiv.symm c with
      | inl v =>
        have h := hx v u
        simpa [Xt, xi, M, hv, hw, Matrix.reindex_apply, Matrix.transpose_apply] using h
      | inr v => simpa [Xt, hv, hw, Matrix.reindex_apply] using hMnn
  have hXtMul : ∀ a b : Fin (m + n), Measurable (fun ω : Ωm => (Xt ω * Xt ω) a b) := by
    intro a b
    have hsum : ∀ s : Finset (Fin (m + n)),
        Measurable (fun ω : Ωm => ∑ c ∈ s, Xt ω a c * Xt ω c b) := by
      intro s
      classical
      refine Finset.induction ?_ ?_ s
      · simpa using measurable_const
      · intro c t hc ih
        have hstep : (fun ω : Ωm => ∑ c' ∈ insert c t, Xt ω a c' * Xt ω c' b)
            = fun ω => Xt ω a c * Xt ω c b + ∑ c' ∈ t, Xt ω a c' * Xt ω c' b := by
          funext ω
          rw [Finset.sum_insert hc]
        rw [hstep]
        exact ((hXtMeas a c).mul (hXtMeas c b)).add ih
    rw [show (fun ω : Ωm => (Xt ω * Xt ω) a b)
        = fun ω => ∑ c : Fin (m + n), Xt ω a c * Xt ω c b from by
      funext ω
      rw [Matrix.mul_apply]]
    exact hsum Finset.univ
  have hXtSqMeas : ∀ a b : Fin (m + n),
      AEStronglyMeasurable (fun ω : Ωm => (Xt ω * Xt ω) a b) P :=
    fun a b => (hXtMul a b).aestronglyMeasurable
  have hXtSqInt : ∀ a b : Fin (m + n),
      Integrable (fun x : Ωm × ((Fin m × Fin n) → ℝ) => (Xt x.1 * Xt x.1) a b)
        (Measure.prod P gamma) := by
    intro a b
    refine MeasureTheory.Integrable.of_bound ?_ (((m : ℝ) + (n : ℝ)) * M ^ 2) ?_
    · exact ((hXtMul a b).comp measurable_fst).aestronglyMeasurable
    · filter_upwards [hXtBnd] with x hx
      have hpt : ∀ c : Fin (m + n), |Xt x.1 a c * Xt x.1 c b| ≤ M * M := by
        intro c
        rw [abs_mul]
        exact mul_le_mul (hx a c) (hx c b) (abs_nonneg _) hMnn
      rw [Real.norm_eq_abs, Matrix.mul_apply]
      calc |∑ c : Fin (m + n), Xt x.1 a c * Xt x.1 c b|
          ≤ ∑ c : Fin (m + n), |Xt x.1 a c * Xt x.1 c b| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _c : Fin (m + n), M * M := Finset.sum_le_sum (fun c _ => hpt c)
        _ = ((m : ℝ) + (n : ℝ)) * M ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
  have hptSq : ∀ (x : Ωm × ((Fin m × Fin n) → ℝ)) (a b : Fin (m + n)),
      ((∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x)
        * (∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x)) a b
        = ((Xt x.1 * Xt x.1) a b : ℂ) := by
    intro x a b
    have hX : Xt x.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Xcheck x) (Xcheck x).transpose
          (0 : Matrix (Fin n) (Fin n) ℝ)) := rfl
    rw [hZsum x, hX, Matrix.mul_apply, Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Matrix.of_apply]
    push_cast
    ring
  have hcov : ∀ a b : Fin (m + n),
      (∫ x, ((∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x)
        * (∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x)) a b
        ∂(Measure.prod P gamma)) = ((cov a b : ℝ) : ℂ) := by
    intro a b
    have h1 : (∫ x, ((∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x)
          * (∑ k : Fin (Fintype.card (Fin m × Fin n)), Zfam k x)) a b
          ∂(Measure.prod P gamma))
        = ∫ x, ((Xt x.1 * Xt x.1) a b : ℂ) ∂(Measure.prod P gamma) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      exact hptSq x a b
    rw [h1]
    have h2 : (∫ x : Ωm × ((Fin m × Fin n) → ℝ), ((Xt x.1 * Xt x.1) a b : ℂ)
          ∂(Measure.prod P gamma))
        = ∫ x : Ωm × ((Fin m × Fin n) → ℝ),
            Complex.ofRealCLM ((Xt x.1 * Xt x.1) a b) ∂(Measure.prod P gamma) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      rfl
    rw [h2, ContinuousLinearMap.integral_comp_comm (μ := Measure.prod P gamma)
      (φ := fun x : Ωm × ((Fin m × Fin n) → ℝ) => (Xt x.1 * Xt x.1) a b)
      Complex.ofRealCLM (hXtSqInt a b),
      hfstInt (fun ω => (Xt ω * Xt ω) a b) (hXtSqMeas a b)]
    rfl
  have hcovEq : cov = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ))
        (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin m) ℝ)
        ((1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
    simpa [cov, Xt, xi] using hdep3
  have hcovSymm : cov.IsSymm := by
    rw [hcovEq]
    ext a b
    rw [Matrix.transpose_apply]
    cases hv : finSumFinEquiv.symm a with
    | inl u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v =>
        by_cases h : u = v
        · subst h
          simp [Matrix.reindex_apply, hv, hw]
        · have h' : v ≠ u := fun hvu => h hvu.symm
          simp [Matrix.reindex_apply, hv, hw, Matrix.smul_apply, Matrix.one_apply, h, h']
      | inr v => simp [Matrix.reindex_apply, hv, hw]
    | inr u =>
      cases hw : finSumFinEquiv.symm b with
      | inl v => simp [Matrix.reindex_apply, hv, hw]
      | inr v =>
        by_cases h : u = v
        · subst h
          simp [Matrix.reindex_apply, hv, hw]
        · have h' : v ≠ u := fun hvu => h hvu.symm
          simp [Matrix.reindex_apply, hv, hw, Matrix.smul_apply, Matrix.one_apply, h, h']

  have hRpoint : ∀ (x : Ωm × ((Fin m × Fin n) → ℝ)) (k : Fin (Fintype.card (Fin m × Fin n))),
      sSup (Set.range fun a : Fin (m+n) => |(hZsa k x).eigenvalues a|) ≤
        1 / Real.sqrt ((m:ℝ)*p) := by
    have hDmat : ∀ (k : Fin (Fintype.card (Fin m × Fin n)))
        (x : Ωm × ((Fin m × Fin n) → ℝ)),
        Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (Matrix.of (fun (a : Fin m) (b : Fin n) =>
                xi x.1 (e.symm k).1 (e.symm k).2
                  * matrixUnit (e.symm k).1 (e.symm k).2 a b))
              (Matrix.of (fun (a : Fin m) (b : Fin n) =>
                xi x.1 (e.symm k).1 (e.symm k).2
                  * matrixUnit (e.symm k).1 (e.symm k).2 a b)).transpose
              (0 : Matrix (Fin n) (Fin n) ℝ))
          = xi x.1 (e.symm k).1 (e.symm k).2 •
            (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                (matrixUnit (e.symm k).1 (e.symm k).2)
                (matrixUnit (e.symm k).1 (e.symm k).2).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ))) := by
      intro k x
      ext a b
      cases hv : finSumFinEquiv.symm a with
      | inl u =>
        cases hw : finSumFinEquiv.symm b with
        | inl v => simp [hv, hw, Matrix.reindex_apply, Matrix.smul_apply]
        | inr v =>
          simp [hv, hw, Matrix.reindex_apply, Matrix.smul_apply, Matrix.transpose_apply]
      | inr u =>
        cases hw : finSumFinEquiv.symm b with
        | inl v =>
          simp [hv, hw, Matrix.reindex_apply, Matrix.smul_apply, Matrix.transpose_apply]
        | inr v => simp [hv, hw, Matrix.reindex_apply, Matrix.smul_apply]
    have hmat : ∀ (k : Fin (Fintype.card (Fin m × Fin n)))
        (x : Ωm × ((Fin m × Fin n) → ℝ)),
        Zfam k x = Matrix.of (fun a b : Fin (m + n) =>
          ((Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
              (Matrix.of (fun (a : Fin m) (b : Fin n) =>
                xi x.1 (e.symm k).1 (e.symm k).2
                  * matrixUnit (e.symm k).1 (e.symm k).2 a b))
              (Matrix.of (fun (a : Fin m) (b : Fin n) =>
                xi x.1 (e.symm k).1 (e.symm k).2
                  * matrixUnit (e.symm k).1 (e.symm k).2 a b)).transpose
              (0 : Matrix (Fin n) (Fin n) ℝ)) a b : ℝ) : ℂ)) := by
      intro k x
      ext a b
      cases hv : finSumFinEquiv.symm a with
      | inl u =>
        cases hw : finSumFinEquiv.symm b with
        | inl v => simp [Zfam, Zblk, xi, hv, hw, Matrix.reindex_apply]
        | inr v =>
          simp [Zfam, Zblk, xi, hv, hw, Matrix.reindex_apply, Matrix.transpose_apply]
      | inr u =>
        cases hw : finSumFinEquiv.symm b with
        | inl v =>
          simp [Zfam, Zblk, xi, hv, hw, Matrix.reindex_apply, Matrix.transpose_apply,
            Complex.conj_ofReal]
        | inr v => simp [Zfam, Zblk, xi, hv, hw, Matrix.reindex_apply]
    have heig : ∀ (M N : Matrix (Fin (m + n)) (Fin (m + n)) ℂ) (h : M = N)
        (hM : M.IsHermitian) (a : Fin (m + n)),
        Matrix.IsHermitian.eigenvalues (h ▸ hM) a = Matrix.IsHermitian.eigenvalues hM a := by
      rintro M N rfl hM a
      rfl
    intro x k
    have hchild := statopia_math_node_740990000_94fc0980 m n
      (lt_of_lt_of_le (show (0 : ℕ) < 2 by norm_num) hd2)
      (Matrix.of (fun (a : Fin m) (b : Fin n) =>
        xi x.1 (e.symm k).1 (e.symm k).2 * matrixUnit (e.symm k).1 (e.symm k).2 a b))
      (hmat k x ▸ hZsa k x)
    have hsup :
        (⨆ a : Fin (m + n), |(Matrix.IsHermitian.eigenvalues (hZsa k x) a)|)
          = specNorm (xi x.1 (e.symm k).1 (e.symm k).2 •
              (Matrix.reindex finSumFinEquiv finSumFinEquiv
                (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                  (matrixUnit (e.symm k).1 (e.symm k).2)
                  (matrixUnit (e.symm k).1 (e.symm k).2).transpose
                  (0 : Matrix (Fin n) (Fin n) ℝ)))) := by
      rw [show (⨆ a : Fin (m + n), |(Matrix.IsHermitian.eigenvalues (hZsa k x) a)|)
          = (⨆ a : Fin (m + n),
              |(Matrix.IsHermitian.eigenvalues (hmat k x ▸ hZsa k x) a)|) from
        iSup_congr (fun a => by rw [heig (Zfam k x) _ (hmat k x) (hZsa k x) a])]
      rw [hchild, hDmat k x]
    have hspec : specNorm (xi x.1 (e.symm k).1 (e.symm k).2 •
        (Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
            (matrixUnit (e.symm k).1 (e.symm k).2)
            (matrixUnit (e.symm k).1 (e.symm k).2).transpose
            (0 : Matrix (Fin n) (Fin n) ℝ))))
        = |xi x.1 (e.symm k).1 (e.symm k).2| := by
      simpa [xi] using hdep16 (e.symm k).1 (e.symm k).2 x.1
    change (⨆ a : Fin (m+n), |(hZsa k x).eigenvalues a|) ≤ _
    rw [hsup, hspec]
    have hb : |Om (e.symm k).1 (e.symm k).2 x.1 - p| ≤ 1 := by
      rcases hOm_point (e.symm k).1 (e.symm k).2 x.1 with hz | ho
      · rw [hz, zero_sub, abs_neg, abs_of_pos hp0]
        exact hp1
      · rw [ho, abs_of_nonneg (sub_nonneg.mpr hp1)]
        linarith
    simpa [xi, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)] using
      div_le_div_of_nonneg_right hb (Real.sqrt_nonneg ((m:ℝ)*p))

  have hXreal : ∀ x a b, ((0 + ∑ k, Zfam k x) a b).im = 0 := by
    intro x a b
    rw [hXsum x]
    simp
  have hGreal : ∀ x a b, (Gdil x a b).im = 0 := by
    intro x a b
    rw [hGdilMat x]
    simp
  have hstarX : ∀ x a b, star ((0 + ∑ k, Zfam k x) a b) = (0 + ∑ k, Zfam k x) a b := by
    intro x a b
    rw [hXsum x]
    simp
  have hstarG : ∀ x a b, star (Gdil x a b) = Gdil x a b := by
    intro x a b
    rw [hGdilMat x]
    simp
  have hGcov : ∀ a b c d,
      (∫ x, (Gdil x a b - ∫ y, Gdil y a b ∂(P.prod gamma)) *
        (Gdil x c d - ∫ y, Gdil y c d ∂(P.prod gamma)) ∂(P.prod gamma)) =
      ∫ x, ((0 + ∑ k, Zfam k x) a b - ∫ y, (0 + ∑ k, Zfam k y) a b ∂(P.prod gamma)) *
        ((0 + ∑ k, Zfam k x) c d - ∫ y, (0 + ∑ k, Zfam k y) c d ∂(P.prod gamma)) ∂(P.prod gamma) := by
    intro a b c d
    have hh := statopia_math_node_1167625269_02ef4fe3 m n hm hn hnm p hp0 hp1 P Om
      hOm_meas hOm_indep hOm_bin hOm_int hOm_mean a b c d
    change (∫ x, Gdil x a b * star (Gdil x c d) ∂(P.prod gamma)) =
      ∫ x, (0 + ∑ k, Zfam k x) a b * star ((0 + ∑ k, Zfam k x) c d) ∂(P.prod gamma) at hh
    simp only [hGint0, hZint0, sub_zero]
    simpa only [hstarG, hstarX] using hh
  let S2 : Matrix (Fin (m+n)) (Fin (m+n)) ℂ := Matrix.of (fun a b => (cov a b : ℂ))
  have hS2herm : S2.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro a b
    change star (cov b a : ℂ) = (cov a b : ℂ)
    simpa using congrArg (fun r : ℝ => (r:ℂ)) (congrFun (congrFun hcovSymm a) b)
  have hS2 : ∀ a b, S2 a b = ∫ x, ∑ c : Fin (m+n),
      ((0 + ∑ k, Zfam k x) a c - ∫ y, (0 + ∑ k, Zfam k y) a c ∂(P.prod gamma)) *
      ((0 + ∑ k, Zfam k x) c b - ∫ y, (0 + ∑ k, Zfam k y) c b ∂(P.prod gamma)) ∂(P.prod gamma) := by
    intro a b
    simp only [hZint0, sub_zero]
    change (cov a b : ℂ) = _
    simpa only [zero_add, Matrix.mul_apply] using (hcov a b).symm
  haveI : Nonempty (Fin (m+n)) := ⟨⟨0, by omega⟩⟩
  have hcovHerm : cov.IsHermitian :=
    Statlib.HighDim.CovarianceMatrix.real_isHermitian_of_isSymm hcovSymm
  have hcovNorm : (⨆ a, |hcovHerm.eigenvalues a|) = specNorm cov := by
    have heq : specNorm cov = ‖cov‖ := (Matrix.l2_opNorm_def cov).symm
    rw [heq, Statlib.HighDim.CovarianceMatrix.hermitian_norm_eq_sup_abs_eigenvalues cov hcovHerm]
    apply le_antisymm
    · refine Real.iSup_le (fun i => Finset.le_sup' (fun a => |hcovHerm.eigenvalues a|) (Finset.mem_univ i)) ?_
      exact (abs_nonneg (hcovHerm.eigenvalues (⟨0, by omega⟩ : Fin (m+n)))).trans (Finset.le_sup' (fun a => |hcovHerm.eigenvalues a|) (Finset.mem_univ (⟨0, by omega⟩ : Fin (m+n))))
    · rw [Finset.sup'_le_iff]
      intro i _
      exact le_csSup (Set.finite_range _ |>.bddAbove) (Set.mem_range_self i)
  have hsigmaXdef : Real.sqrt (1-p) =
      Real.sqrt (sSup (Set.range fun a : Fin (m+n) => |hS2herm.eigenvalues a|)) := by
    congr 1
    change 1-p = ⨆ a, |hS2herm.eigenvalues a|
    rw [statopia_math_node_4153628898_515516f4 (m+n) cov hcovHerm hS2herm, hcovNorm, hspecCov]

  let v : ℝ := (1-p)/(m:ℝ)
  have hv : 0 < v := div_pos (sub_pos.mpr hpStrict) (by exact_mod_cast hm)
  have hroot : Real.sqrt v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  let D : (Fin m × Fin n) → Matrix (Fin (m+n)) (Fin (m+n)) ℝ := fun q =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (matrixUnit q.1 q.2)
        (matrixUnit q.1 q.2).transpose (0 : Matrix (Fin n) (Fin n) ℝ))
  let Dc : (Fin m × Fin n) → Matrix (Fin (m+n)) (Fin (m+n)) ℂ :=
    fun q => Matrix.of (fun a b => (D q a b : ℂ))
  have hDcher : ∀ q, (Dc q).IsHermitian := by
    intro q
    apply Matrix.IsHermitian.ext
    intro a b
    change star (D q b a : ℂ) = (D q a b : ℂ)
    have he := congrFun (congrFun (hdep14 q.1 q.2) a) b
    simpa only [Matrix.transpose_apply, Complex.star_def, Complex.conj_ofReal] using
      congrArg (fun r : ℝ => (r:ℂ)) he
  have hGsum : ∀ x, Gdil x = ∑ q : Fin m × Fin n, (x.2 q : ℂ) • Dc q := by
    intro x
    ext a b
    rw [hGdilMat x]
    have hh := congrArg (fun M : Matrix (Fin (m+n)) (Fin (m+n)) ℝ => (M a b : ℂ))
      (dilation_matrixUnit_sum (Gmat x))
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sum,
      Complex.ofReal_mul, D, Dc, Matrix.of_apply, Gmat] using hh.symm
  have hGaussian : ResidualSparseRepair20261106.HasStandardGaussianRepresentation
      (P.prod gamma) (0 : Matrix (Fin (m+n)) (Fin (m+n)) ℂ) Gdil := by
    obtain ⟨hgmeas, hgind, hglaw⟩ := normalized_product_gaussian (I := Fin m × Fin n) P v hv
    let gg : Fin (Fintype.card (Fin m × Fin n)) → (Ωm × ((Fin m × Fin n) → ℝ)) → ℝ :=
      fun k x => x.2 (e.symm k) / Real.sqrt v
    let BB : Fin (Fintype.card (Fin m × Fin n)) → Matrix (Fin (m+n)) (Fin (m+n)) ℂ :=
      fun k => (Real.sqrt v : ℂ) • Dc (e.symm k)
    refine ⟨Fintype.card (Fin m × Fin n), gg, BB, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      exact hgmeas (e.symm k)
    · exact iIndepFun.precomp e.symm.injective hgind
    · intro k
      exact hglaw (e.symm k)
    · intro k
      apply Matrix.IsHermitian.ext
      intro a b
      have hh := congrFun (congrFun (hDcher (e.symm k)).eq a) b
      change star ((Real.sqrt v : ℂ) * Dc (e.symm k) b a) =
        (Real.sqrt v : ℂ) * Dc (e.symm k) a b
      rw [star_mul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      simpa only [Matrix.conjTranspose_apply, Complex.star_def, mul_comm] using
        congrArg (fun z : ℂ => (Real.sqrt v : ℂ) * z) hh
    · intro x
      rw [zero_add, hGsum x, ← Equiv.sum_comp e.symm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      dsimp only [gg, BB]
      rw [smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hroot]

  let sigSet : Set ℝ := {y | ∃ vw : (Fin (m+n) → ℝ) × (Fin (m+n) → ℝ),
    (∑ a, (vw.1 a)^2 = 1 ∧ ∑ b, (vw.2 b)^2 = 1) ∧
      y = Real.sqrt (∫ x, ‖∑ a, ∑ b,
        (vw.1 a : ℂ) * ((0 + ∑ k, Zfam k x) a b -
          ∫ y, (0 + ∑ k, Zfam k y) a b ∂(P.prod gamma)) * (vw.2 b : ℂ)‖^2 ∂(P.prod gamma))}
  have hbilinear_eq : ∀ (vv ww : Fin (m+n) → ℝ) x,
      ‖∑ a, ∑ b, (vv a : ℂ) * ((0 + ∑ k, Zfam k x) a b -
        ∫ y, (0 + ∑ k, Zfam k y) a b ∂(P.prod gamma)) * (ww b : ℂ)‖^2 =
      (∑ a, ∑ b, vv a * Xt x.1 a b * ww b)^2 := by
    intro vv ww x
    simp only [hZint0, sub_zero]
    rw [hXsum x]
    change ‖∑ a, ∑ b, (vv a : ℂ) * (Xt x.1 a b : ℂ) * (ww b : ℂ)‖^2 = _
    have hh : (∑ a, ∑ b, (vv a : ℂ) * (Xt x.1 a b : ℂ) * (ww b : ℂ)) =
        ((∑ a, ∑ b, vv a * Xt x.1 a b * ww b : ℝ) : ℂ) := by push_cast; rfl
    rw [hh, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hbilinear_bound : ∀ (vv ww : Fin (m+n) → ℝ),
      (∑ a, (vv a)^2)=1 → (∑ b, (ww b)^2)=1 →
      (∫ x, ‖∑ a, ∑ b, (vv a : ℂ) * ((0 + ∑ k, Zfam k x) a b -
        ∫ y, (0 + ∑ k, Zfam k y) a b ∂(P.prod gamma)) * (ww b : ℂ)‖^2 ∂(P.prod gamma)) ≤ v := by
    intro vv ww hvv hww
    simp_rw [hbilinear_eq]
    have hbm : Measurable (fun ω : Ωm => (∑ a, ∑ b, vv a * Xt ω a b * ww b)^2) := by
      exact (Finset.measurable_sum _ (fun a _ =>
        Finset.measurable_sum _ (fun b _ => ((hXtMeas a b).const_mul _).mul_const _))).pow_const 2
    rw [hfstInt _ hbm.aestronglyMeasurable]
    have hvv' := (split_norm_square (m:=m) (n:=n) vv).symm.trans hvv
    have hww' := (split_norm_square (m:=m) (n:=n) ww).symm.trans hww
    have hh := (hdep7 (fun i => vv (finSumFinEquiv (Sum.inl i)))
      (fun i => ww (finSumFinEquiv (Sum.inl i)))
      (fun j => vv (finSumFinEquiv (Sum.inr j)))
      (fun j => ww (finSumFinEquiv (Sum.inr j))) hvv' hww').2
    have heq : ∀ ω : Ωm, (∑ a, ∑ b, vv a * Xt ω a b * ww b) =
      (∑ i : Fin m, ∑ j : Fin n, vv (finSumFinEquiv (Sum.inl i)) * xi ω i j * ww (finSumFinEquiv (Sum.inr j))) +
      (∑ j : Fin n, ∑ i : Fin m, vv (finSumFinEquiv (Sum.inr j)) * xi ω i j * ww (finSumFinEquiv (Sum.inl i))) := by
      intro ω
      exact dilation_bilinear (Matrix.of (fun i j => xi ω i j)) vv ww
    simpa only [heq, xi, v] using hh
  have hsigUpper : ∀ y ∈ sigSet, y ≤ Real.sqrt v := by
    rintro y ⟨⟨vv, ww⟩, ⟨hvv, hww⟩, rfl⟩
    exact Real.sqrt_le_sqrt (hbilinear_bound vv ww hvv hww)
  have hsigNonempty : sigSet.Nonempty := by
    let vv : Fin (m+n) → ℝ := Pi.single (⟨0, by omega⟩ : Fin (m+n)) 1
    have hvv : ∑ a, (vv a)^2 = 1 := by simp [vv, Pi.single_apply]
    exact ⟨_, ⟨(vv,vv), ⟨hvv,hvv⟩, rfl⟩⟩
  let sigmaStar : ℝ := sSup sigSet
  have hsigmaStarNonneg : 0 ≤ sigmaStar := by
    apply Real.sSup_nonneg
    rintro y ⟨vw, hunit, rfl⟩
    exact Real.sqrt_nonneg _
  have hsigmaStarSharp : sigmaStar ≤ Real.sqrt v := csSup_le hsigNonempty hsigUpper
  have hsigmaStarBound : sigmaStar ≤ Real.sqrt (1-p) := by
    apply hsigmaStarSharp.trans
    apply Real.sqrt_le_sqrt
    dsimp [v]
    have hm0 : (0:ℝ) < m := by exact_mod_cast hm
    apply (div_le_iff₀ hm0).2
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [sub_nonneg.mpr hp1]

  have hXmeas : ∀ a b : Fin (m+n), Measurable (fun x => (0 + ∑ k, Zfam k x) a b) := by
    intro a b
    simp only [zero_add, Matrix.sum_apply]
    exact Finset.measurable_sum _ (fun k _ =>
      (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hZmeas k)))
  have hdev := hmain (m+n) (Fintype.card (Fin m × Fin n)) hd2 (P.prod gamma)
    (0 : Matrix (Fin (m+n)) (Fin (m+n)) ℂ) Zfam (fun x => 0 + ∑ k, Zfam k x) Gdil
    Matrix.isHermitian_zero hZsa
    (fun k a b => (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hZmeas k)))
    hZint hZmean hindep hXmeas
    (fun a b => (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hGmeas))
    hXsa hGsa hXreal hGreal hGaussian
    (fun x a b => by simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.zero_apply])
    hGmean hGcov (1 / Real.sqrt ((m:ℝ)*p)) (Real.sqrt (1-p)) sigmaStar
    (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) hRpoint S2 hS2herm hS2 hsigmaXdef
    rfl hsigmaStarNonneg hsigmaStarBound t ht
  change (P.prod gamma) {x | Cbig * (sigmaStar * Real.sqrt t +
      (1 / Real.sqrt ((m:ℝ)*p)) ^ ((1:ℝ)/3) * (Real.sqrt (1-p)) ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) +
      (1 / Real.sqrt ((m:ℝ)*p)) * t) <
      |(⨆ a, |(hXsa x).eigenvalues a|) - ∫ y, (⨆ a, |(hGsa y).eigenvalues a|) ∂(P.prod gamma)|} ≤ _ at hdev
  simp only [hXsig, hGsig] at hdev
  apply le_trans (measure_mono ?_) hdev
  intro x hx
  change Cbig * (sigmaStar * Real.sqrt t + _ + _) < _
  apply lt_of_le_of_lt _ hx
  apply mul_le_mul_of_nonneg_left _ hCbig.le
  have hh := mul_le_mul_of_nonneg_right hsigmaStarSharp (Real.sqrt_nonneg t)
  dsimp only [v] at hh
  linarith

end
#print axioms mask_norm_vs_gaussian_mean
end ResidualMaskRepair20261106

