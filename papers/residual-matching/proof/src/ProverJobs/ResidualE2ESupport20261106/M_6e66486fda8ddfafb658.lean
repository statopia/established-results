import Statlib.HighDim.MatrixAnalysis.FrobeniusNormSvdRelation
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SoftThresholdDenoisingHelpers
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.StatFoundation.RandomVariable.Gaussian.LipschitzConcentration
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
universe u

set_option autoImplicit false in
theorem statopia_math_node_3461429018_ebf22525 : ∀ (D : ℝ) (hD : 0 < D) (m n T : ℕ) (hn : 2 ≤ n) (hnm : n ≤ m) (hT : 1 ≤ T)
    (OmF : Matrix (Fin m) (Fin n) ℝ)
    (hbin : ∀ (i : Fin m) (j : Fin n), OmF i j = 0 ∨ OmF i j = 1)
    (μG : Measure (Matrix (Fin m) (Fin n) ℝ)) [instMuG : IsProbabilityMeasure μG]
    (hgauss : Statlib.Imported.IsStdGaussianMatrixLaw μG)
    (Ωg : Type u) [instOg : MeasurableSpace Ωg] (μg : Measure Ωg) [instMug : IsProbabilityMeasure μg]
    (G : Ωg → Fin T → Matrix (Fin m) (Fin n) ℝ)
    (hdraws : Statlib.Imported.IsGaussianDrawsLaw μg G)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t),
    μg {s : Ωg |
        t ≤ |Statlib.Imported.lambdaHat hnm OmF (G s) i
              - Statlib.Imported.lambdaCirc hnm μG OmF i|} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2 * ((m : ℝ) * (T : ℝ))) / 2)) := by
  /- @proof-region region.target-node.session.55ec3ff5c903a60b begin -/
  intro D hD m n T hn hnm hT OmF hbin μG instMuG hgauss Ωg instOg μg instMug G hdraws i t ht
  classical
  have hm2 : 2 ≤ m := le_trans hn hnm
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have h : (0 : ℕ) < m := lt_of_lt_of_le (by norm_num) hm2
    exact_mod_cast h
  have hTR : (0 : ℝ) < (T : ℝ) := by
    have h : (0 : ℕ) < T := lt_of_lt_of_le (by norm_num) hT
    exact_mod_cast h
  have hmT : (0 : ℝ) < (m : ℝ) * (T : ℝ) := mul_pos hmR hTR
  set φ : Matrix (Fin m) (Fin n) ℝ → ℝ :=
    fun A => sv hnm (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)) i
  have hlam : ∀ (G' : Fin T → Matrix (Fin m) (Fin n) ℝ),
      lambdaHat hnm OmF G' i = (T : ℝ)⁻¹ * ∑ tt, φ (G' tt) := fun G' => rfl
  have hcirc : lambdaCirc hnm μG OmF i = ∫ A, φ A ∂μG := rfl
  set L : NNReal := ⟨Real.sqrt (((m : ℝ) * (T : ℝ))⁻¹), Real.sqrt_nonneg _⟩ with hL
  have hLpos : 0 < L := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_zero]
    simpa [hL] using (Real.sqrt_pos.mpr (inv_pos.mpr hmT))
  have hL2 : (L : ℝ) ^ 2 = ((m : ℝ) * (T : ℝ))⁻¹ := by
    simpa [hL] using (Real.sq_sqrt (le_of_lt (inv_pos.mpr hmT)))
  have hexp : ∀ (t' : ℝ),
      -(t' ^ 2) / (2 * (L : ℝ) ^ 2) = -(t' ^ 2 * ((m : ℝ) * (T : ℝ))) / 2 := by
    intro t'
    rw [hL2]
    have hne : ((m : ℝ) * (T : ℝ)) ≠ 0 := ne_of_gt hmT
    field_simp [hne]
  let N : ℕ := T * (m * n)
  let e : Fin N ≃ (Fin T × Fin m × Fin n) :=
    ((finProdFinEquiv : Fin T × Fin (m * n) ≃ Fin (T * (m * n))).symm.trans
      (Equiv.prodCongr (Equiv.refl (Fin T))
        (finProdFinEquiv.symm : Fin (m * n) ≃ (Fin m × Fin n))))
  let block : EuclideanSpace ℝ (Fin N) → Fin T → Matrix (Fin m) (Fin n) ℝ :=
    fun x tt ii jj => x.ofLp (e.symm (tt, ii, jj))
  let f : EuclideanSpace ℝ (Fin N) → ℝ :=
    fun x => (T : ℝ)⁻¹ * ∑ tt, φ (block x tt)
  let X : Ωg → EuclideanSpace ℝ (Fin N) :=
    fun s => WithLp.toLp 2 (fun k : Fin N => let y := e k; G s y.1 y.2.1 y.2.2)
  have hXblock : ∀ (s : Ωg) (tt : Fin T) (ii : Fin m) (jj : Fin n),
      block (X s) tt ii jj = G s tt ii jj := by
    intro s tt ii jj
    simp [block, X, PiLp.toLp_apply]
  have hfX : ∀ s : Ωg, f (X s) = lambdaHat hnm OmF (G s) i := by
    intro s
    rw [hlam (G s)]
    have hblk : ∀ tt : Fin T, block (X s) tt = G s tt := fun tt => by
      ext ii jj
      exact hXblock s tt ii jj
    change (T : ℝ)⁻¹ * ∑ tt, φ (block (X s) tt) = (T : ℝ)⁻¹ * ∑ tt, φ (G s tt)
    rw [funext hblk]
  have hmn_pos : 0 < min m n :=
    Nat.lt_min.mpr ⟨lt_of_lt_of_le (by norm_num) hm2, lt_of_lt_of_le (by norm_num) hn⟩
  have hFrob : ∀ E : Matrix (Fin m) (Fin n) ℝ,
      Statlib.HighDim.MatrixAnalysis.opNorm E
        ≤ Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, E ii jj ^ 2) := by
    intro E
    have hne : Nonempty (Fin m) ∨ Nonempty (Fin n) :=
      Or.inl ⟨⟨0, lt_of_lt_of_le (by norm_num) hm2⟩⟩
    have h0 := (Statlib.HighDim.MatrixAnalysis.singular_value_properties E hne).1 hmn_pos
    have hnonneg := (Statlib.HighDim.MatrixAnalysis.singular_value_properties E hne).2.1
    have hsq : Statlib.HighDim.MatrixAnalysis.singularValues E ⟨0, hmn_pos⟩ ^ 2
        ≤ ∑ k : Fin (min m n), Statlib.HighDim.MatrixAnalysis.singularValues E k ^ 2 :=
      Finset.single_le_sum
        (f := fun k : Fin (min m n) =>
          Statlib.HighDim.MatrixAnalysis.singularValues E k ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ _)
    have hfrob := (Statlib.HighDim.MatrixAnalysis.frobenius_norm_svd_relation E).1
    have hop : Statlib.HighDim.MatrixAnalysis.opNorm E
        = Statlib.HighDim.MatrixAnalysis.singularValues E ⟨0, hmn_pos⟩ :=
      (Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 E).trans h0.symm
    calc Statlib.HighDim.MatrixAnalysis.opNorm E
        = Statlib.HighDim.MatrixAnalysis.singularValues E ⟨0, hmn_pos⟩ := hop
      _ = Real.sqrt (Statlib.HighDim.MatrixAnalysis.singularValues E ⟨0, hmn_pos⟩ ^ 2) :=
          (Real.sqrt_sq (hnonneg ⟨0, hmn_pos⟩)).symm
      _ ≤ Real.sqrt (∑ k : Fin (min m n),
            Statlib.HighDim.MatrixAnalysis.singularValues E k ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, E ii jj ^ 2) := by rw [hfrob]
  have hsv_frob : ∀ (A E : Matrix (Fin m) (Fin n) ℝ) (k : Fin n),
      |sv hnm (A + E) k - sv hnm A k|
        ≤ Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, E ii jj ^ 2) := by
    intro A E k
    have h1 : sv hnm (A + E) k ≤ sv hnm A k
        + Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, E ii jj ^ 2) := by
      have h := Statlib.HighDim.MatrixAnalysis.rectangular_singularValues_weyl_upper A E
        (Fin.castLE (le_min hnm le_rfl) k)
      have hb := hFrob E
      simp only [sv] at h ⊢
      linarith
    have h2 : sv hnm A k ≤ sv hnm (A + E) k
        + Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, E ii jj ^ 2) := by
      have h := Statlib.HighDim.MatrixAnalysis.rectangular_singularValues_weyl_upper (A + E) (-E)
        (Fin.castLE (le_min hnm le_rfl) k)
      have hAE : A + E + -E = A := by abel
      rw [hAE] at h
      have hb := hFrob (-E)
      have hsq : (∑ ii : Fin m, ∑ jj : Fin n, (-E) ii jj ^ 2)
          = (∑ ii : Fin m, ∑ jj : Fin n, E ii jj ^ 2) := by simp
      rw [hsq] at hb
      simp only [sv] at h ⊢
      linarith
    rw [abs_le]
    constructor <;> linarith
  have hmask_term : ∀ (ii : Fin m) (jj : Fin n) (E : Matrix (Fin m) (Fin n) ℝ),
      (maskOp OmF E) ii jj ^ 2 ≤ E ii jj ^ 2 := by
    intro ii jj E
    change (OmF ii jj * E ii jj) ^ 2 ≤ E ii jj ^ 2
    rcases hbin ii jj with h | h
    · rw [h, zero_mul]
      simpa using sq_nonneg (E ii jj)
    · rw [h, one_mul]
  have hmask_frob : ∀ E : Matrix (Fin m) (Fin n) ℝ,
      (∑ ii : Fin m, ∑ jj : Fin n, (maskOp OmF E) ii jj ^ 2)
        ≤ (∑ ii : Fin m, ∑ jj : Fin n, E ii jj ^ 2) := by
    intro E
    exact Finset.sum_le_sum (fun ii _ => Finset.sum_le_sum (fun jj _ => hmask_term ii jj E))
  have hsmul_frob : ∀ (c : ℝ) (E : Matrix (Fin m) (Fin n) ℝ),
      (∑ ii : Fin m, ∑ jj : Fin n, (c • E) ii jj ^ 2)
        = c ^ 2 * (∑ ii : Fin m, ∑ jj : Fin n, E ii jj ^ 2) := by
    intro c E
    have h1 : ∀ ii : Fin m, (∑ jj : Fin n, (c • E) ii jj ^ 2)
        = c ^ 2 * (∑ jj : Fin n, E ii jj ^ 2) := by
      intro ii
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun jj _ => by
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, mul_pow])
    calc (∑ ii : Fin m, ∑ jj : Fin n, (c • E) ii jj ^ 2)
        = ∑ ii : Fin m, c ^ 2 * (∑ jj : Fin n, E ii jj ^ 2) :=
          Finset.sum_congr rfl (fun ii _ => h1 ii)
      _ = c ^ 2 * ∑ ii : Fin m, ∑ jj : Fin n, E ii jj ^ 2 := by rw [Finset.mul_sum]
  have hsv_pair : ∀ (A B : Matrix (Fin m) (Fin n) ℝ) (k : Fin n),
      |sv hnm A k - sv hnm B k|
        ≤ Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, (A - B) ii jj ^ 2) := by
    intro A B k
    have h := hsv_frob B (A - B) k
    have hBA : B + (A - B) = A := by abel
    rw [hBA] at h
    exact h
  have hφ_lip : ∀ (A B : Matrix (Fin m) (Fin n) ℝ),
      |φ A - φ B| ≤ (Real.sqrt (m : ℝ))⁻¹
        * Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, (A - B) ii jj ^ 2) := by
    intro A B
    have hc0 : (0:ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ :=
      le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hmR))
    have hsub_eq : maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A)
        - maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • B)
        = maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (A - B)) := by
      ext ii jj
      show OmF ii jj * ((Real.sqrt (m : ℝ))⁻¹ * A ii jj)
          - OmF ii jj * ((Real.sqrt (m : ℝ))⁻¹ * B ii jj)
        = OmF ii jj * ((Real.sqrt (m : ℝ))⁻¹ * (A ii jj - B ii jj))
      ring
    have hstep := hsv_pair (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • A))
      (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • B)) i
    rw [hsub_eq] at hstep
    have hbound : Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n,
          (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (A - B))) ii jj ^ 2)
        ≤ (Real.sqrt (m : ℝ))⁻¹
          * Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, (A - B) ii jj ^ 2) := by
      have h1 : (∑ ii : Fin m, ∑ jj : Fin n,
            (maskOp OmF ((Real.sqrt (m : ℝ))⁻¹ • (A - B))) ii jj ^ 2)
          ≤ ((Real.sqrt (m : ℝ))⁻¹) ^ 2
            * (∑ ii : Fin m, ∑ jj : Fin n, (A - B) ii jj ^ 2) := by
        refine le_trans (hmask_frob ((Real.sqrt (m : ℝ))⁻¹ • (A - B))) ?_
        rw [hsmul_frob]
      refine le_trans (Real.sqrt_le_sqrt h1) ?_
      rw [Real.sqrt_mul (sq_nonneg ((Real.sqrt (m : ℝ))⁻¹)), Real.sqrt_sq hc0]
    exact le_trans hstep hbound


  have hofLp : ∀ (ω : Ωg) (k : Fin N), (X ω).ofLp k = G ω (e k).1 (e k).2.1 (e k).2.2 := by
    intro ω k
    simp [X, PiLp.toLp_apply]
  have hXmeas : Measurable X := by
    have hg : Measurable (fun s : Ωg => fun k : Fin N => G s (e k).1 (e k).2.1 (e k).2.2) := by
      rw [measurable_pi_iff]
      intro k
      exact hdraws.1 (e k).1 (e k).2.1 (e k).2.2
    exact (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp hg
  have hlaw : ∀ k : Fin N, Measure.map (fun ω => (X ω).ofLp k) μg = gaussianReal 0 1 := by
    intro k
    have hof : (fun ω => (X ω).ofLp k) = fun ω => G ω (e k).1 (e k).2.1 (e k).2.2 := by
      funext ω
      exact hofLp ω k
    rw [hof]
    exact hdraws.2.1 (e k).1 (e k).2.1 (e k).2.2
  have hindep : iIndepFun (fun k ω => (X ω).ofLp k) μg := by
    set F : Ωg → ((Fin T × Fin m × Fin n) → ℝ) :=
      fun ω p => G ω p.1 p.2.1 p.2.2 with hF_def
    set g : ((Fin T × Fin m × Fin n) → ℝ) → (Fin N → ℝ) :=
      fun x k => x (e k) with hg_def
    have hFmeas : Measurable F := by
      rw [measurable_pi_iff]
      intro p
      exact hdraws.1 p.1 p.2.1 p.2.2
    have hFae : ∀ p : Fin T × Fin m × Fin n, AEMeasurable (fun ω : Ωg => F ω p) μg :=
      fun p => (hdraws.1 p.1 p.2.1 p.2.2).aemeasurable
    have hZlaw : Measure.map F μg
        = Measure.pi (fun _ : Fin T × Fin m × Fin n => gaussianReal 0 1) := by
      have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (f := fun p : Fin T × Fin m × Fin n => fun ω : Ωg => F ω p) hFae).mp hdraws.2.2
      have hfac : (fun p : Fin T × Fin m × Fin n => Measure.map (fun ω : Ωg => F ω p) μg)
          = fun _ => gaussianReal 0 1 := by
        funext p
        exact hdraws.2.1 p.1 p.2.1 p.2.2
      rw [hfac] at h
      exact h
    have hgmeas : Measurable g := by
      rw [measurable_pi_iff]
      intro k
      exact measurable_pi_apply (e k)
    have hpi : Measure.map g (Measure.pi (fun _ : Fin T × Fin m × Fin n => gaussianReal 0 1))
        = Measure.pi (fun _ : Fin N => gaussianReal 0 1) := by
      have hcoe : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) e.symm)) = g := by
        funext x k
        have h := MeasurableEquiv.piCongrLeft_apply_apply (e := e.symm)
          (β := fun _ : Fin N => ℝ) x (e k)
        rw [Equiv.symm_apply_apply] at h
        exact h
      have h := MeasureTheory.Measure.pi_map_piCongrLeft (e := e.symm)
        (β := fun _ : Fin N => ℝ) (μ := fun _ : Fin N => gaussianReal 0 1)
      rw [← hcoe]
      exact h
    have hcomp : (fun ω k => (X ω).ofLp k) = g ∘ F := by
      funext ω k
      show (X ω).ofLp k = g (F ω) k
      exact hofLp ω k
    have hXNae : ∀ k : Fin N, AEMeasurable (fun ω : Ωg => (X ω).ofLp k) μg := by
      intro k
      have heq : (fun ω : Ωg => (X ω).ofLp k) = fun ω => F ω (e k) := by
        funext ω
        exact hofLp ω k
      rw [heq]
      exact hFae (e k)
    refine (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (f := fun k : Fin N => fun ω : Ωg => (X ω).ofLp k) hXNae).mpr ?_
    have hfac2 : (fun k : Fin N => Measure.map (fun ω : Ωg => (X ω).ofLp k) μg)
        = fun _ => gaussianReal 0 1 := by
      funext k
      exact hlaw k
    rw [hfac2]
    show Measure.map (fun ω k => (X ω).ofLp k) μg
      = Measure.pi (fun _ : Fin N => gaussianReal 0 1)
    rw [hcomp, ← Measure.map_map (μ := μg) hgmeas hFmeas, hZlaw]
    exact hpi
  have hLip : LipschitzWith L f := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hc0 : (0:ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ :=
      le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hmR))
    have hTinv : (0:ℝ) < (T : ℝ)⁻¹ := inv_pos.mpr hTR
    have hdiff : f x - f y
        = (T : ℝ)⁻¹ * ∑ tt : Fin T, (φ (block x tt) - φ (block y tt)) := by
      have hx : f x = (T : ℝ)⁻¹ * ∑ tt : Fin T, φ (block x tt) := rfl
      have hy : f y = (T : ℝ)⁻¹ * ∑ tt : Fin T, φ (block y tt) := rfl
      rw [hx, hy, Finset.sum_sub_distrib, mul_sub]
    have hA : |f x - f y| ≤ (T : ℝ)⁻¹ * ((Real.sqrt (m : ℝ))⁻¹
        * ∑ tt : Fin T, Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n,
            (block x tt - block y tt) ii jj ^ 2)) := by
      rw [hdiff, abs_mul, abs_of_pos hTinv]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hTinv)
      have habs : |∑ tt : Fin T, (φ (block x tt) - φ (block y tt))|
          ≤ ∑ tt : Fin T, |φ (block x tt) - φ (block y tt)| := by
        rw [abs_le]
        constructor
        · have h1 : (∑ tt : Fin T, -(|φ (block x tt) - φ (block y tt)|))
              ≤ ∑ tt : Fin T, (φ (block x tt) - φ (block y tt)) :=
            Finset.sum_le_sum (fun tt _ => neg_abs_le _)
          rw [Finset.sum_neg_distrib] at h1
          exact h1
        · exact Finset.sum_le_sum (fun tt _ => le_abs_self _)
      refine le_trans habs ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun tt _ => hφ_lip (block x tt) (block y tt))
    have hSnn : ∀ tt : Fin T, 0 ≤ (∑ ii : Fin m, ∑ jj : Fin n,
        (block x tt - block y tt) ii jj ^ 2) := fun tt =>
      Finset.sum_nonneg (fun ii _ => Finset.sum_nonneg (fun jj _ => sq_nonneg _))
    have hCS : (∑ tt : Fin T, Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n,
          (block x tt - block y tt) ii jj ^ 2))
        ≤ Real.sqrt (T : ℝ) * Real.sqrt (∑ tt : Fin T, ∑ ii : Fin m, ∑ jj : Fin n,
          (block x tt - block y tt) ii jj ^ 2) := by
      have hnn : 0 ≤ ∑ tt : Fin T, Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n,
          (block x tt - block y tt) ii jj ^ 2) :=
        Finset.sum_nonneg (fun tt _ => Real.sqrt_nonneg _)
      have hcs : (∑ tt : Fin T, Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n,
            (block x tt - block y tt) ii jj ^ 2)) ^ 2
          ≤ (T : ℝ) * ∑ tt : Fin T, ∑ ii : Fin m, ∑ jj : Fin n,
              (block x tt - block y tt) ii jj ^ 2 := by
        have h : (∑ tt : Fin T, Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n,
            (block x tt - block y tt) ii jj ^ 2)) ^ 2
            ≤ ((Finset.univ : Finset (Fin T)).card : ℝ)
              * ∑ tt : Fin T, (Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n,
                (block x tt - block y tt) ii jj ^ 2)) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        rw [Finset.card_univ, Fintype.card_fin] at h
        have hsq : (∑ tt : Fin T, (Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n,
            (block x tt - block y tt) ii jj ^ 2)) ^ 2)
            = ∑ tt : Fin T, ∑ ii : Fin m, ∑ jj : Fin n,
              (block x tt - block y tt) ii jj ^ 2 :=
          Finset.sum_congr rfl (fun tt _ => Real.sq_sqrt (hSnn tt))
        rwa [hsq] at h
      rw [← Real.sqrt_sq hnn]
      refine le_trans (Real.sqrt_le_sqrt hcs) ?_
      rw [Real.sqrt_mul (le_of_lt hTR)]
    have hdist : (∑ tt : Fin T, ∑ ii : Fin m, ∑ jj : Fin n,
          (block x tt - block y tt) ii jj ^ 2) = dist x y ^ 2 := by
      have hblock : ∀ (tt : Fin T) (ii : Fin m) (jj : Fin n),
          (block x tt - block y tt) ii jj
            = x.ofLp (e.symm (tt, ii, jj)) - y.ofLp (e.symm (tt, ii, jj)) := by
        intro tt ii jj
        show block x tt ii jj - block y tt ii jj
          = x.ofLp (e.symm (tt, ii, jj)) - y.ofLp (e.symm (tt, ii, jj))
        rfl
      have hsum_eq : (∑ tt : Fin T, ∑ ii : Fin m, ∑ jj : Fin n,
            (block x tt - block y tt) ii jj ^ 2)
          = ∑ tt : Fin T, ∑ ii : Fin m, ∑ jj : Fin n,
              (x.ofLp (e.symm (tt, ii, jj)) - y.ofLp (e.symm (tt, ii, jj))) ^ 2 := by
        refine Finset.sum_congr rfl (fun tt _ => Finset.sum_congr rfl (fun ii _ =>
          Finset.sum_congr rfl (fun jj _ => ?_)))
        rw [hblock]
      have h2 : (∑ tt : Fin T, ∑ ii : Fin m, ∑ jj : Fin n,
            (x.ofLp (e.symm (tt, ii, jj)) - y.ofLp (e.symm (tt, ii, jj))) ^ 2)
          = ∑ tt : Fin T, ∑ q : Fin m × Fin n,
              (x.ofLp (e.symm (tt, q)) - y.ofLp (e.symm (tt, q))) ^ 2 := by
        refine Finset.sum_congr rfl (fun tt _ => ?_)
        have h := (Finset.sum_product (Finset.univ : Finset (Fin m))
          (Finset.univ : Finset (Fin n))
          (fun (p : Fin m × Fin n) =>
            (x.ofLp (e.symm (tt, p)) - y.ofLp (e.symm (tt, p))) ^ 2)).symm
        rw [Finset.univ_product_univ] at h
        exact h
      have h3 : (∑ tt : Fin T, ∑ q : Fin m × Fin n,
            (x.ofLp (e.symm (tt, q)) - y.ofLp (e.symm (tt, q))) ^ 2)
          = ∑ p : Fin T × Fin m × Fin n,
              (x.ofLp (e.symm p) - y.ofLp (e.symm p)) ^ 2 := by
        have h := (Finset.sum_product (Finset.univ : Finset (Fin T))
          (Finset.univ : Finset (Fin m × Fin n))
          (fun (p : Fin T × Fin m × Fin n) =>
            (x.ofLp (e.symm p) - y.ofLp (e.symm p)) ^ 2)).symm
        rw [Finset.univ_product_univ] at h
        exact h
      have h4 : (∑ p : Fin T × Fin m × Fin n,
            (x.ofLp (e.symm p) - y.ofLp (e.symm p)) ^ 2)
          = ∑ k : Fin N, (x.ofLp k - y.ofLp k) ^ 2 := by
        have hcomp := Equiv.sum_comp e
          (fun p : Fin T × Fin m × Fin n =>
            (x.ofLp (e.symm p) - y.ofLp (e.symm p)) ^ 2)
        have hsimp : (∑ k : Fin N,
            (x.ofLp (e.symm (e k)) - y.ofLp (e.symm (e k))) ^ 2)
            = ∑ k : Fin N, (x.ofLp k - y.ofLp k) ^ 2 := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          simp
        rw [hsimp] at hcomp
        exact hcomp.symm
      have h5 : (∑ k : Fin N, (x.ofLp k - y.ofLp k) ^ 2) = dist x y ^ 2 := by
        rw [EuclideanSpace.dist_sq_eq]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Real.dist_eq, sq_abs]
      rw [hsum_eq, h2, h3, h4, h5]
    have hb1 : (T : ℝ)⁻¹ * ((Real.sqrt (m : ℝ))⁻¹
          * ∑ tt : Fin T, Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n,
              (block x tt - block y tt) ii jj ^ 2))
        ≤ (T : ℝ)⁻¹ * ((Real.sqrt (m : ℝ))⁻¹
          * (Real.sqrt (T : ℝ) * dist x y)) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hTinv)
      refine mul_le_mul_of_nonneg_left ?_ hc0
      refine le_trans hCS ?_
      rw [hdist, Real.sqrt_sq dist_nonneg]
    have hconst : (T : ℝ)⁻¹ * ((Real.sqrt (m : ℝ))⁻¹ * Real.sqrt (T : ℝ)) = (L : ℝ) := by
      have hnn : (0:ℝ) ≤ (T : ℝ)⁻¹ * ((Real.sqrt (m : ℝ))⁻¹ * Real.sqrt (T : ℝ)) :=
        mul_nonneg (le_of_lt (inv_pos.mpr hTR))
          (mul_nonneg (le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hmR))) (Real.sqrt_nonneg _))
      have hsq : ((T : ℝ)⁻¹ * ((Real.sqrt (m : ℝ))⁻¹ * Real.sqrt (T : ℝ))) ^ 2
          = (L : ℝ) ^ 2 := by
        have hneT : (T : ℝ) ≠ 0 := ne_of_gt hTR
        have hnem : (m : ℝ) ≠ 0 := ne_of_gt hmR
        have hne : ((m : ℝ) * (T : ℝ)) ≠ 0 := ne_of_gt hmT
        rw [hL2, mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt (le_of_lt hmR),
          Real.sq_sqrt (le_of_lt hTR)]
        field_simp
      calc (T : ℝ)⁻¹ * ((Real.sqrt (m : ℝ))⁻¹ * Real.sqrt (T : ℝ))
          = Real.sqrt (((T : ℝ)⁻¹ * ((Real.sqrt (m : ℝ))⁻¹ * Real.sqrt (T : ℝ))) ^ 2) :=
            (Real.sqrt_sq hnn).symm
        _ = Real.sqrt ((L : ℝ) ^ 2) := by rw [hsq]
        _ = (L : ℝ) := Real.sqrt_sq (le_of_lt hLpos)
    have hb2 : (T : ℝ)⁻¹ * ((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (T : ℝ) * dist x y))
        = (L : ℝ) * dist x y := by
      rw [← hconst]
      ring
    rw [Real.dist_eq]
    exact le_trans hA (le_trans hb1 (le_of_eq hb2))
  have hInt : Integrable (fun ω => f (X ω)) μg := by
    have hcoord : ∀ k : Fin N, Integrable (fun ω : Ωg => ((X ω).ofLp k) ^ 2) μg := by
      intro k
      have hmeas : Measurable (fun ω : Ωg => (X ω).ofLp k) := by
        have heq : (fun ω : Ωg => (X ω).ofLp k)
            = fun ω => G ω (e k).1 (e k).2.1 (e k).2.2 := by
          funext ω
          exact hofLp ω k
        rw [heq]
        exact hdraws.1 (e k).1 (e k).2.1 (e k).2.2
      have hgs : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
        memLp_one_iff_integrable.mp
          (Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal
            (μ₀ := 0) (v := 1) 2 1 (by simp))
      refine (MeasureTheory.integrable_map_measure
        (f := fun ω : Ωg => (X ω).ofLp k) (g := fun x : ℝ => x ^ 2) ?_ ?_).mp ?_
      · exact (continuous_pow 2).aestronglyMeasurable
      · exact hmeas.aemeasurable
      · rw [hlaw k]
        exact hgs
    have hXnormsq : Integrable (fun ω : Ωg => ‖X ω‖ ^ 2) μg := by
      have hEq : (fun ω : Ωg => ‖X ω‖ ^ 2)
          = fun ω => ∑ k : Fin N, ((X ω).ofLp k) ^ 2 := by
        funext ω
        rw [EuclideanSpace.norm_sq_eq]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Real.norm_eq_abs, sq_abs]
      rw [hEq]
      exact MeasureTheory.integrable_finset_sum (Finset.univ : Finset (Fin N))
        (f := fun k ω => ((X ω).ofLp k) ^ 2) (fun k _ => hcoord k)
    have hInt_norm : Integrable (fun ω : Ωg => ‖X ω‖) μg := by
      have hb : ∀ ω : Ωg, ‖‖X ω‖‖ ≤ (1/2 : ℝ) * (1 + ‖X ω‖ ^ 2) := by
        intro ω
        rw [norm_norm]
        nlinarith [sq_nonneg (‖X ω‖ - 1)]
      have hint : Integrable (fun ω : Ωg => (1/2 : ℝ) * (1 + ‖X ω‖ ^ 2)) μg :=
        (Integrable.add (integrable_const (1:ℝ)) hXnormsq).const_mul (1/2 : ℝ)
      exact Integrable.mono' hint (hXmeas.norm).aestronglyMeasurable
        (Filter.Eventually.of_forall hb)
    have hbdd : ∀ ω : Ωg, ‖f (X ω)‖ ≤ ‖f 0‖ + (L : ℝ) * ‖X ω‖ := by
      intro ω
      have h1 : |f (X ω) - f 0| ≤ (L : ℝ) * ‖X ω‖ := by
        have h2 := hLip.dist_le_mul (X ω) 0
        rwa [Real.dist_eq, dist_eq_norm, sub_zero] at h2
      have h3 : |f (X ω)| ≤ |f (X ω) - f 0| + ‖f 0‖ := by
        have h := abs_add_le (f (X ω) - f 0) (f 0)
        rw [sub_add_cancel] at h
        simpa [Real.norm_eq_abs] using h
      rw [Real.norm_eq_abs]
      linarith
    have hint2 : Integrable (fun ω : Ωg => ‖f 0‖ + (L : ℝ) * ‖X ω‖) μg :=
      Integrable.add (integrable_const ‖f 0‖) (hInt_norm.const_mul (L : ℝ))
    exact Integrable.mono' hint2
      (hLip.continuous.measurable.comp hXmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  have hφmeas : Measurable φ := by
    have hYmeas : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
        WithLp.toLp 2 (fun k : Fin N => A (e k).2.1 (e k).2.2)) := by
      refine (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp ?_
      rw [measurable_pi_iff]
      intro k
      exact (measurable_pi_apply (e k).2.2).comp (measurable_pi_apply (e k).2.1)
    have hφeq : ∀ A : Matrix (Fin m) (Fin n) ℝ,
        φ A = f (WithLp.toLp 2 (fun k : Fin N => A (e k).2.1 (e k).2.2)) := by
      intro A
      have hblk : ∀ tt : Fin T,
          block (WithLp.toLp 2 (fun k : Fin N => A (e k).2.1 (e k).2.2)) tt = A := by
        intro tt
        ext ii jj
        show (WithLp.toLp 2 (fun k : Fin N => A (e k).2.1 (e k).2.2)).ofLp
          (e.symm (tt, ii, jj)) = A ii jj
        rw [PiLp.toLp_apply, Equiv.apply_symm_apply]
      show φ A = (T : ℝ)⁻¹ * ∑ tt,
        φ (block (WithLp.toLp 2 (fun k : Fin N => A (e k).2.1 (e k).2.2)) tt)
      rw [funext hblk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hneT : (T : ℝ) ≠ 0 := ne_of_gt hTR
      field_simp
    have h2 : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
        f (WithLp.toLp 2 (fun k : Fin N => A (e k).2.1 (e k).2.2))) :=
      hLip.continuous.measurable.comp hYmeas
    have hfun : (fun A : Matrix (Fin m) (Fin n) ℝ =>
        f (WithLp.toLp 2 (fun k : Fin N => A (e k).2.1 (e k).2.2))) = φ :=
      funext (fun A => (hφeq A).symm)
    rw [hfun] at h2
    exact h2
  have hμGent : Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ =>
      fun p : Fin m × Fin n => A p.1 p.2) μG
      = Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) := by
    have hae : ∀ p : Fin m × Fin n,
        AEMeasurable (fun A : Matrix (Fin m) (Fin n) ℝ => A p.1 p.2) μG :=
      fun p => ((measurable_pi_apply p.2).comp (measurable_pi_apply p.1)).aemeasurable
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (f := fun p : Fin m × Fin n => fun A : Matrix (Fin m) (Fin n) ℝ => A p.1 p.2)
      hae).mp hgauss.2
    have hfac : (fun p : Fin m × Fin n =>
        Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => A p.1 p.2) μG)
        = fun _ => gaussianReal 0 1 := by
      funext p
      exact hgauss.1 p.1 p.2
    rwa [hfac] at h
  have hZlaw2 : Measure.map (fun ω : Ωg => fun p : Fin T × Fin m × Fin n =>
      G ω p.1 p.2.1 p.2.2) μg
      = Measure.pi (fun _ : Fin T × Fin m × Fin n => gaussianReal 0 1) := by
    have hae : ∀ p : Fin T × Fin m × Fin n,
        AEMeasurable (fun ω : Ωg => G ω p.1 p.2.1 p.2.2) μg :=
      fun p => (hdraws.1 p.1 p.2.1 p.2.2).aemeasurable
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (f := fun p : Fin T × Fin m × Fin n => fun ω : Ωg => G ω p.1 p.2.1 p.2.2)
      hae).mp hdraws.2.2
    have hfac : (fun p : Fin T × Fin m × Fin n =>
        Measure.map (fun ω : Ωg => G ω p.1 p.2.1 p.2.2) μg) = fun _ => gaussianReal 0 1 := by
      funext p
      exact hdraws.2.1 p.1 p.2.1 p.2.2
    rwa [hfac] at h
  have hblock_entry : ∀ tt : Fin T,
      Measure.map (fun ω : Ωg => fun p : Fin m × Fin n => G ω tt p.1 p.2) μg
        = Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) := by
    intro tt
    have hBmeas : Measurable (fun ω : Ωg => fun p : Fin m × Fin n => G ω tt p.1 p.2) := by
      rw [measurable_pi_iff]
      intro p
      exact hdraws.1 tt p.1 p.2
    have hFmeas2 : Measurable (fun ω : Ωg => fun p : Fin T × Fin m × Fin n =>
        G ω p.1 p.2.1 p.2.2) := by
      rw [measurable_pi_iff]
      intro p
      exact hdraws.1 p.1 p.2.1 p.2.2
    refine (MeasureTheory.Measure.pi_eq (μ := fun _ : Fin m × Fin n => gaussianReal 0 1)
      (μ' := Measure.map (fun ω : Ωg => fun p : Fin m × Fin n => G ω tt p.1 p.2) μg) ?_).symm
    intro s hs
    have hpre : (fun ω : Ωg => fun p : Fin m × Fin n => G ω tt p.1 p.2) ⁻¹' Set.univ.pi s
        = (fun ω : Ωg => fun q : Fin T × Fin m × Fin n => G ω q.1 q.2.1 q.2.2) ⁻¹'
            Set.univ.pi (fun q : Fin T × Fin m × Fin n =>
              if q.1 = tt then s q.2 else Set.univ) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      constructor
      · intro h q
        by_cases hq : q.1 = tt
        · rw [if_pos hq, hq]
          exact h q.2
        · rw [if_neg hq]
          exact Set.mem_univ _
      · intro h p
        have hp := h (tt, p)
        simpa using hp
    have hfill : MeasurableSet (Set.univ.pi (fun q : Fin T × Fin m × Fin n =>
        if q.1 = tt then s q.2 else Set.univ) : Set ((Fin T × Fin m × Fin n) → ℝ)) := by
      refine MeasurableSet.univ_pi (fun q => ?_)
      by_cases hq : q.1 = tt
      · rw [if_pos hq]; exact hs q.2
      · rw [if_neg hq]; exact MeasurableSet.univ
    rw [MeasureTheory.Measure.map_apply hBmeas (MeasurableSet.univ_pi hs), hpre,
      ← MeasureTheory.Measure.map_apply hFmeas2 hfill, hZlaw2,
      MeasureTheory.Measure.pi_pi]
    have hprod : (∏ q : Fin T × Fin m × Fin n,
        (gaussianReal 0 1) (if q.1 = tt then s q.2 else Set.univ))
        = ∏ p : Fin m × Fin n, (gaussianReal 0 1) (s p) := by
      have h1 : ∀ t : Fin T, (∏ p : Fin m × Fin n,
          (gaussianReal 0 1) (if t = tt then s p else Set.univ))
          = (if t = tt then ∏ p : Fin m × Fin n, (gaussianReal 0 1) (s p) else 1) := by
        intro t
        by_cases ht : t = tt
        · rw [if_pos ht]
          exact Finset.prod_congr rfl (fun p _ => by simp [ht])
        · rw [if_neg ht]
          exact Finset.prod_eq_one (fun p _ => by simp [ht])
      rw [← Finset.univ_product_univ, Finset.prod_product]
      rw [Finset.prod_congr rfl (fun t _ => h1 t)]
      rw [Finset.prod_ite_eq']
      simp
    exact hprod
  have hmean : ∫ ω, f (X ω) ∂μg = lambdaCirc hnm μG OmF i := by
    rw [hcirc]
    set Fb : ((Fin m × Fin n) → ℝ) → ℝ := fun x => φ (fun i j => x (i, j)) with hFb
    have hFbmeas : Measurable Fb := by
      refine hφmeas.comp ?_
      rw [measurable_pi_iff]
      intro ii
      rw [measurable_pi_iff]
      intro jj
      exact measurable_pi_apply (ii, jj)
    set S : ℝ := ∫ x : (Fin m × Fin n) → ℝ, Fb x
      ∂(Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1)) with hS
    have hFb_apply : ∀ A : Matrix (Fin m) (Fin n) ℝ,
        Fb (fun p : Fin m × Fin n => A p.1 p.2) = φ A := by
      intro A
      show φ (fun i j => (fun p : Fin m × Fin n => A p.1 p.2) (i, j)) = φ A
      congr 1
    have hmuGs : ∫ A : Matrix (Fin m) (Fin n) ℝ, φ A ∂μG = S := by
      have hcmeas : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
          fun p : Fin m × Fin n => A p.1 p.2) := by
        rw [measurable_pi_iff]
        exact fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
      have hstep : ∫ x : (Fin m × Fin n) → ℝ, Fb x
            ∂(Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ =>
              fun p : Fin m × Fin n => A p.1 p.2) μG)
          = ∫ A : Matrix (Fin m) (Fin n) ℝ,
              Fb (fun p : Fin m × Fin n => A p.1 p.2) ∂μG :=
        MeasureTheory.integral_map
          (φ := fun A : Matrix (Fin m) (Fin n) ℝ => fun p : Fin m × Fin n => A p.1 p.2)
          (f := Fb) hcmeas.aemeasurable hFbmeas.aestronglyMeasurable
      have hcong : ∫ A : Matrix (Fin m) (Fin n) ℝ,
            Fb (fun p : Fin m × Fin n => A p.1 p.2) ∂μG
          = ∫ A : Matrix (Fin m) (Fin n) ℝ, φ A ∂μG := by
        have hfe : (fun A : Matrix (Fin m) (Fin n) ℝ =>
            Fb (fun p : Fin m × Fin n => A p.1 p.2)) = φ := funext hFb_apply
        rw [hfe]
      rw [hS, ← hμGent]
      exact (hstep.trans hcong).symm
    have hblockInt : ∀ tt : Fin T, Integrable (fun ω : Ωg => φ (G ω tt)) μg := by
      intro tt
      have hBm1 : Measurable (fun ω : Ωg => G ω tt) := by
        rw [measurable_pi_iff]
        intro ii
        rw [measurable_pi_iff]
        intro jj
        exact hdraws.1 tt ii jj
      have hcoord : Integrable (fun ω : Ωg =>
          ∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2) μg := by
        refine MeasureTheory.integrable_finset_sum (Finset.univ : Finset (Fin m))
          (f := fun ii ω => ∑ jj : Fin n, (G ω tt ii jj) ^ 2) (fun ii _ => ?_)
        refine MeasureTheory.integrable_finset_sum (Finset.univ : Finset (Fin n))
          (f := fun jj ω => (G ω tt ii jj) ^ 2) (fun jj _ => ?_)
        have hgs : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
          memLp_one_iff_integrable.mp
            (Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal
              (μ₀ := 0) (v := 1) 2 1 (by simp))
        refine (MeasureTheory.integrable_map_measure
          (f := fun ω : Ωg => G ω tt ii jj) (g := fun x : ℝ => x ^ 2) ?_ ?_).mp ?_
        · exact (continuous_pow 2).aestronglyMeasurable
        · exact (hdraws.1 tt ii jj).aemeasurable
        · rw [hdraws.2.1 tt ii jj]
          exact hgs
      have hbdd : ∀ ω : Ωg, ‖φ (G ω tt)‖ ≤ |φ 0| + (Real.sqrt (m : ℝ))⁻¹
          * (1 + ∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2) := by
        intro ω
        have hc0 : (0:ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ :=
          le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hmR))
        have h1 : |φ (G ω tt) - φ 0| ≤ (Real.sqrt (m : ℝ))⁻¹
            * Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2) := by
          have h := hφ_lip (G ω tt) 0
          simp only [sub_zero] at h
          exact h
        have hSnn : (0:ℝ) ≤ ∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2 :=
          Finset.sum_nonneg (fun ii _ => Finset.sum_nonneg (fun jj _ => sq_nonneg _))
        have hsq : Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2)
            ≤ 1 + ∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2 := by
          nlinarith [Real.sq_sqrt hSnn,
            Real.sqrt_nonneg (∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2),
            sq_nonneg (Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2) - 1)]
        have h3 : |φ (G ω tt)| ≤ |φ (G ω tt) - φ 0| + |φ 0| := by
          have h := abs_add_le (φ (G ω tt) - φ 0) (φ 0)
          rwa [sub_add_cancel] at h
        have h4 : (Real.sqrt (m : ℝ))⁻¹
              * Real.sqrt (∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2)
            ≤ (Real.sqrt (m : ℝ))⁻¹
              * (1 + ∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hc0
        rw [Real.norm_eq_abs]
        linarith
      have hbdInt : Integrable (fun ω : Ωg => |φ 0| + (Real.sqrt (m : ℝ))⁻¹
          * (1 + ∑ ii : Fin m, ∑ jj : Fin n, (G ω tt ii jj) ^ 2)) μg :=
        Integrable.add (integrable_const |φ 0|)
          ((Integrable.add (integrable_const (1:ℝ)) hcoord).const_mul
            ((Real.sqrt (m : ℝ))⁻¹))
      exact Integrable.mono' hbdInt (hφmeas.comp hBm1).aestronglyMeasurable
        (Filter.Eventually.of_forall hbdd)
    have hblockVal : ∀ tt : Fin T, ∫ ω : Ωg, φ (G ω tt) ∂μg = S := by
      intro tt
      have hBm2 : Measurable (fun ω : Ωg => fun p : Fin m × Fin n => G ω tt p.1 p.2) := by
        rw [measurable_pi_iff]
        intro p
        exact hdraws.1 tt p.1 p.2
      have hstep : ∫ x : (Fin m × Fin n) → ℝ, Fb x
            ∂(Measure.map (fun ω : Ωg => fun p : Fin m × Fin n => G ω tt p.1 p.2) μg)
          = ∫ ω : Ωg, Fb (fun p : Fin m × Fin n => G ω tt p.1 p.2) ∂μg :=
        MeasureTheory.integral_map
          (φ := fun ω : Ωg => fun p : Fin m × Fin n => G ω tt p.1 p.2)
          (f := Fb) hBm2.aemeasurable hFbmeas.aestronglyMeasurable
      have hcong : ∫ ω : Ωg, Fb (fun p : Fin m × Fin n => G ω tt p.1 p.2) ∂μg
          = ∫ ω : Ωg, φ (G ω tt) ∂μg := by
        have hfe : (fun ω : Ωg => Fb (fun p : Fin m × Fin n => G ω tt p.1 p.2))
            = fun ω => φ (G ω tt) := by
          funext ω
          exact hFb_apply (G ω tt)
        rw [hfe]
      rw [hS, ← hblock_entry tt]
      exact (hstep.trans hcong).symm
    have hfe : (fun ω : Ωg => f (X ω))
        = fun ω => (T : ℝ)⁻¹ * ∑ tt : Fin T, φ (G ω tt) := by
      funext ω
      exact (hfX ω).trans (hlam (G ω))
    have hstep2 : ∫ ω : Ωg, (∑ tt : Fin T, φ (G ω tt)) ∂μg
        = ∑ tt : Fin T, ∫ ω : Ωg, φ (G ω tt) ∂μg :=
      MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin T))
        (f := fun tt ω => φ (G ω tt)) (fun tt _ => hblockInt tt)
    have hsum : (∑ tt : Fin T, ∫ ω : Ωg, φ (G ω tt) ∂μg) = ∑ _ : Fin T, S :=
      Finset.sum_congr rfl (fun tt _ => hblockVal tt)
    have hneT : (T : ℝ) ≠ 0 := ne_of_gt hTR
    rw [hmuGs, hfe, MeasureTheory.integral_const_mul, hstep2, hsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hmain := Statlib.StatFoundation.RandomVariable.Gaussian.gaussian_lipschitz_concentration
    μg X hXmeas hindep hlaw f L hLpos hLip hInt ht
  have hset : {s : Ωg | t ≤ |lambdaHat hnm OmF (G s) i - lambdaCirc hnm μG OmF i|}
      = {ω : Ωg | t ≤ |f (X ω) - ∫ (ω' : Ωg), f (X ω') ∂μg|} := by
    ext s
    simp only [Set.mem_setOf_eq]
    rw [hfX s, hmean]
  rw [hset, ← hexp t]
  exact hmain
  /- @proof-region region.target-node.session.55ec3ff5c903a60b end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3461429018_ebf22525


