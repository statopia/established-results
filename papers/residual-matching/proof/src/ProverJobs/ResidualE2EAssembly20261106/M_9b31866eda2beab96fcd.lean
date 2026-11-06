import Statlib.HighDim.MatrixAnalysis.KyFan
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48
import ProverJobs.ResidualE2EAssembly20261106.M_261740b4974fe54a555a
import ProverJobs.ResidualE2EAssembly20261106.M_5eacf8ccb7ff44b13edc
import ProverJobs.ResidualE2EAssembly20261106.M_6ab257f44c787db196fd
import ProverJobs.ResidualE2EAssembly20261106.M_5d1852be792d69517477
import ProverJobs.ResidualE2EAssembly20261106.M_ced546ad79605d62353f

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656





run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2464956088_5e15ab10 : ∀ (m n r : ℕ) (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ)
    (sig0 : Fin r → ℝ) (mu0 mu1 CM : ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (hm : 0 < m) (hn : 0 < n) (hr : 1 ≤ r) (hCM : 1 ≤ CM)
    (hmu : mu0 ≤ mu1) (hmu0 : 0 ≤ mu0)
    (hU0 : Matrix.transpose U0 * U0 = 1) (hV0 : Matrix.transpose V0 * V0 = 1)
    (hanti : Antitone sig0) (hsmin : 0 < SMin sig0)
    (hM : InLowRankClass r mu1 M) (hspec : spectralNorm M ≤ CM * SMax sig0),
    ∃ X : Matrix (Fin m) (Fin r) ℝ, ∃ Y : Matrix (Fin n) (Fin r) ℝ,
      X * Matrix.transpose Y = M ∧
      twoInfNorm X ≤
        Real.sqrt (CM * SMax sig0) *
          Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) ∧
      twoInfNorm Y ≤
        Real.sqrt (CM * SMax sig0) *
          Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) ∧
      frobSq (X - U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t))) +
          frobSq (Y - V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t))) ≤
        2 * frobSq (X * Matrix.transpose Y -
            (U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t))) *
              Matrix.transpose (V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)))) /
          ((Real.sqrt 2 - 1) * SMin sig0) := by
  /- @proof-region region.target-node.session.8951dd66e5c94bc0 begin -/
  intro m n r U0 V0 sig0 mu0 mu1 CM M hm hn hr hCM hmu hmu0 hU0 hV0 hanti hsmin hM hspec
  have hsle : ∀ t : Fin r, SMin sig0 ≤ sig0 t := fun t =>
    ciInf_le (Set.finite_range sig0).bddBelow t
  have hs0 : ∀ t : Fin r, 0 < sig0 t := fun t => lt_of_lt_of_le hsmin (hsle t)
  have hb0 : 0 ≤ barMuOf mu0 mu1 := le_trans hmu0 (le_max_left mu0 mu1)
  have hbmu1 : mu1 ≤ barMuOf mu0 mu1 := le_max_right mu0 mu1
  rcases hM with hMzero | ⟨k, U, V, s, hk1, hkr, hU, hV, hMfac, hUbound, hVbound⟩
  · rw [hMzero]
    exact statopia_math_node_913401766_3b0eb21b m n r U0 V0 sig0 mu0 mu1 CM hU0 hV0 hsmin
  · have hsgnn : ∀ t : Fin r, 0 ≤ sig0 t := fun t => le_of_lt (hs0 t)
    obtain ⟨X₁, Y₁, hMfac₁, hbal, hspecX₁, hspecY₁, h2X₁, h2Y₁⟩ :=
      statopia_math_node_290215883_e35c90a8 m n r hm hn hr sig0 hsgnn mu1 (barMuOf mu0 mu1)
        hbmu1 hb0 CM hCM M
        (Or.inr ⟨k, U, V, s, hk1, hkr, hU, hV, hMfac, hUbound, hVbound⟩) hspec
    have hle_gram : ∀ {N : ℕ} (A : Matrix (Fin N) (Fin r) ℝ),
        Matrix.transpose A * A = 1 → r ≤ N := by
      intro N A hA
      have hone : (Matrix.toLin' (Matrix.transpose A)).comp (Matrix.toLin' A) = LinearMap.id := by
        rw [← Matrix.toLin'_mul, hA, Matrix.toLin'_one]
      have hinj : Function.Injective (Matrix.toLin' A) := by
        intro v w hvw
        have h1 : ((Matrix.toLin' (Matrix.transpose A)).comp (Matrix.toLin' A)) v
            = ((Matrix.toLin' (Matrix.transpose A)).comp (Matrix.toLin' A)) w := by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, hvw]
        rwa [hone, LinearMap.id_apply, LinearMap.id_apply] at h1
      have h := LinearMap.finrank_le_finrank_of_injective (f := Matrix.toLin' A) hinj
      simpa using h
    have hrm : r ≤ m := hle_gram U0 hU0
    have hrn : r ≤ n := hle_gram V0 hV0
    have hmn : r ≤ m + n := by omega
    set X₀ : Matrix (Fin m) (Fin r) ℝ := U0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)) with hX₀
    set Y₀ : Matrix (Fin n) (Fin r) ℝ := V0 * Matrix.diagonal (fun t => Real.sqrt (sig0 t)) with hY₀
    have hDT : Matrix.transpose (Matrix.diagonal (fun t => Real.sqrt (sig0 t)))
        = Matrix.diagonal (fun t => Real.sqrt (sig0 t)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.diagonal, hij, Ne.symm hij]
    have hX0gram : Matrix.transpose X₀ * X₀ = Matrix.diagonal sig0 := by
      rw [hX₀, Matrix.transpose_mul, hDT]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Matrix.transpose U0) U0
          (Matrix.diagonal (fun t => Real.sqrt (sig0 t))),
        hU0, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
      congr 1
      funext t
      exact Real.mul_self_sqrt (le_of_lt (hs0 t))
    have hY0gram : Matrix.transpose Y₀ * Y₀ = Matrix.diagonal sig0 := by
      rw [hY₀, Matrix.transpose_mul, hDT]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Matrix.transpose V0) V0
          (Matrix.diagonal (fun t => Real.sqrt (sig0 t))),
        hV0, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
      congr 1
      funext t
      exact Real.mul_self_sqrt (le_of_lt (hs0 t))
    have hX0Y0 : Matrix.transpose X₀ * X₀ = Matrix.transpose Y₀ * Y₀ :=
      hX0gram.trans hY0gram.symm
    let F : Matrix (Fin (m + n)) (Fin r) ℝ := Fin.append (fun a => X₁ a) (fun b => Y₁ b)
    let F0 : Matrix (Fin (m + n)) (Fin r) ℝ := Fin.append (fun a => X₀ a) (fun b => Y₀ b)
    let Δ : Matrix (Fin m) (Fin n) ℝ := X₁ * Matrix.transpose Y₁ - X₀ * Matrix.transpose Y₀
    have hF0gram : Matrix.transpose F0 * F0 = (2 : ℝ) • Matrix.diagonal sig0 := by
      ext t t'
      have hsplit : (∑ i : Fin (m + n), F0 i t * F0 i t')
          = (∑ a : Fin m, X₀ a t * X₀ a t') + ∑ b : Fin n, Y₀ b t * Y₀ b t' := by
        rw [Fin.sum_univ_add]
        congr 1
        · exact Finset.sum_congr rfl (fun a _ => by simp [F0, Fin.append_left])
        · exact Finset.sum_congr rfl (fun b _ => by simp [F0, Fin.append_right])
      have hX : (∑ a : Fin m, X₀ a t * X₀ a t') = Matrix.diagonal sig0 t t' := by
        have h1 : (Matrix.transpose X₀ * X₀) t t' = ∑ a : Fin m, X₀ a t * X₀ a t' := by
          rw [Matrix.mul_apply]
          simp [Matrix.transpose_apply]
        rw [← h1, hX0gram]
      have hY : (∑ b : Fin n, Y₀ b t * Y₀ b t') = Matrix.diagonal sig0 t t' := by
        have h2 : (Matrix.transpose Y₀ * Y₀) t t' = ∑ b : Fin n, Y₀ b t * Y₀ b t' := by
          rw [Matrix.mul_apply]
          simp [Matrix.transpose_apply]
        rw [← h2, hY0gram]
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply]
      rw [hsplit, hX, hY]
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    have hF0gram2 : Matrix.transpose F0 * F0 = Matrix.diagonal (fun t => 2 * sig0 t) := by
      rw [hF0gram]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.smul_apply, Matrix.diagonal]
      · simp [Matrix.smul_apply, Matrix.diagonal, hij]
    obtain ⟨hsig2, hsigma⟩ :=
      statopia_math_node_3063245539_44590815 r (m + n) hr hmn sig0 hsmin F0 hF0gram2
    have hSMin_eq : SMin (fun i : Fin r =>
        Statlib.HighDim.MatrixAnalysis.singularValues F0
          (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i))
        = Statlib.HighDim.MatrixAnalysis.singularValues F0 ⟨r - 1, by omega⟩ := by
      haveI : Nonempty (Fin r) := ⟨⟨r - 1, by omega⟩⟩
      refine le_antisymm ?_ ?_
      · exact ciInf_le (f := fun i : Fin r =>
            Statlib.HighDim.MatrixAnalysis.singularValues F0
              (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i))
          (Set.finite_range _).bddBelow (⟨r - 1, by omega⟩ : Fin r)
      · refine le_ciInf (fun i => ?_)
        have h2 : Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i
            ≤ Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) (⟨r - 1, by omega⟩ : Fin r) := by
          show i.val ≤ r - 1
          omega
        exact Statlib.HighDim.MatrixAnalysis.singularValues_antitone F0 h2
    have hpos : 0 < SMin (fun i : Fin r =>
        Statlib.HighDim.MatrixAnalysis.singularValues F0
          (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i)) := by
      rw [hSMin_eq]
      exact hsigma
    have hΔ0 : 0 ≤ frobSq Δ := by
      simp only [frobSq]
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have hsq : (Real.sqrt (frobSq Δ)) ^ 2 = frobSq Δ := Real.sq_sqrt hΔ0
    have hgram : frobSq (F * Matrix.transpose F - F0 * Matrix.transpose F0) ≤ 8 * frobSq Δ :=
      statopia_math_node_1316590956_d1ca58c8 m n r hm hn hr X₁ X₀ Y₁ Y₀ hbal hX0Y0
    have hgram' : frobSq (F * Matrix.transpose F - F0 * Matrix.transpose F0)
        ≤ 8 * (Real.sqrt (frobSq Δ)) ^ 2 := by
      rw [hsq]
      exact hgram
    obtain ⟨O, hOrth, _, _, hfour⟩ :=
      statopia_math_node_3282353922_3efb933f m n r hr hmn (Real.sqrt (frobSq Δ))
        (Real.sqrt_nonneg _) X₁ X₀ Y₁ Y₀ hpos hgram'
    have hOO : O * Matrix.transpose O = 1 :=
      Statlib.HighDim.MatrixAnalysis.orth_square_mul_transpose O hOrth
    have hprod : (X₁ * O) * Matrix.transpose (Y₁ * O) = X₁ * Matrix.transpose Y₁ := by
      rw [Matrix.transpose_mul,
        ← Matrix.mul_assoc (X₁ * O) (Matrix.transpose O) (Matrix.transpose Y₁),
        Matrix.mul_assoc X₁ O (Matrix.transpose O), hOO, Matrix.mul_one]
    have hrowX : ∀ i : Fin m, (∑ j : Fin r, (X₁ * O) i j ^ 2) = ∑ j : Fin r, X₁ i j ^ 2 := by
      intro i
      have hp : (X₁ * O) * Matrix.transpose (X₁ * O) = X₁ * Matrix.transpose X₁ := by
        rw [Matrix.transpose_mul,
          ← Matrix.mul_assoc (X₁ * O) (Matrix.transpose O) (Matrix.transpose X₁),
          Matrix.mul_assoc X₁ O (Matrix.transpose O), hOO, Matrix.mul_one]
      have e1 : ((X₁ * O) * Matrix.transpose (X₁ * O)) i i
          = ∑ j : Fin r, (X₁ * O) i j ^ 2 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun j _ => by rw [Matrix.transpose_apply]; ring)
      have e2 : (X₁ * Matrix.transpose X₁) i i = ∑ j : Fin r, X₁ i j ^ 2 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun j _ => by rw [Matrix.transpose_apply]; ring)
      rw [← e1, ← e2]
      exact congrFun (congrFun hp i) i
    have hrowY : ∀ i : Fin n, (∑ j : Fin r, (Y₁ * O) i j ^ 2) = ∑ j : Fin r, Y₁ i j ^ 2 := by
      intro i
      have hp : (Y₁ * O) * Matrix.transpose (Y₁ * O) = Y₁ * Matrix.transpose Y₁ := by
        rw [Matrix.transpose_mul,
          ← Matrix.mul_assoc (Y₁ * O) (Matrix.transpose O) (Matrix.transpose Y₁),
          Matrix.mul_assoc Y₁ O (Matrix.transpose O), hOO, Matrix.mul_one]
      have e1 : ((Y₁ * O) * Matrix.transpose (Y₁ * O)) i i
          = ∑ j : Fin r, (Y₁ * O) i j ^ 2 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun j _ => by rw [Matrix.transpose_apply]; ring)
      have e2 : (Y₁ * Matrix.transpose Y₁) i i = ∑ j : Fin r, Y₁ i j ^ 2 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun j _ => by rw [Matrix.transpose_apply]; ring)
      rw [← e1, ← e2]
      exact congrFun (congrFun hp i) i
    have htwoX : twoInfNorm (X₁ * O) = twoInfNorm X₁ := by
      have hfun : (fun i : Fin m => Real.sqrt (∑ j : Fin r, (X₁ * O) i j ^ 2))
          = (fun i : Fin m => Real.sqrt (∑ j : Fin r, X₁ i j ^ 2)) := by
        funext i
        rw [hrowX i]
      simp only [twoInfNorm, hfun]
    have htwoY : twoInfNorm (Y₁ * O) = twoInfNorm Y₁ := by
      have hfun : (fun i : Fin n => Real.sqrt (∑ j : Fin r, (Y₁ * O) i j ^ 2))
          = (fun i : Fin n => Real.sqrt (∑ j : Fin r, Y₁ i j ^ 2)) := by
        funext i
        rw [hrowY i]
      simp only [twoInfNorm, hfun]
    have hkey : 4 * (Real.sqrt (frobSq Δ)) ^ 2 /
        ((Real.sqrt 2 - 1) *
          (SMin (fun i : Fin r =>
            Statlib.HighDim.MatrixAnalysis.singularValues F0
              (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i))) ^ 2)
        = 2 * frobSq Δ / ((Real.sqrt 2 - 1) * SMin sig0) := by
      rw [hSMin_eq, hsq, hsig2]
      have hc : Real.sqrt 2 - 1 ≠ 0 := by
        have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hp : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        intro h0
        nlinarith
      have hs : SMin sig0 ≠ 0 := ne_of_gt hsmin
      field_simp
      ring
    refine ⟨X₁ * O, Y₁ * O, ?_, ?_, ?_, ?_⟩
    · rw [hprod]
      exact hMfac₁.symm
    · rw [htwoX]
      exact h2X₁
    · rw [htwoY]
      exact h2Y₁
    · rw [hprod]
      have hinter : (SMin (fun i : Fin r =>
          Statlib.HighDim.MatrixAnalysis.singularValues F0
            (Fin.castLE (Nat.le_min.mpr ⟨hmn, le_refl r⟩) i))) ^ 2 = 2 * SMin sig0 := by
        rw [hSMin_eq]
        exact hsig2
      have hmain := hfour sig0 hinter
      rw [hsq] at hmain
      exact hmain
  /- @proof-region region.target-node.session.8951dd66e5c94bc0 end -/

end

end Statlib.Imported

