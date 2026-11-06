import Lean
import ProverJobs.ResidualE2ESupport20261106.M_93faf7a69d5e2ba5d8e6
import ProverJobs.ResidualE2ESupport20261106.M_e317ebe39f07aa48afdc

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
namespace ResidualSparseRepair20261106.Completed
universe u

set_option maxHeartbeats 4000000 in
theorem sparse_cdf_comparison : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus) (h_rhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (hAlpha0 : 15 < alpha0),
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ m1 : ℕ,
      ∀ (m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hm1 : m1 ≤ m)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p),
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ),
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0) →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1) →
          (∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
            μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt))) →
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
          (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
          (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
          IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
            (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
          sSup (Set.range fun x : {y : ℝ // 0 ≤ y} =>
              |(∫ ω, (n : ℝ)⁻¹ *
                  ((Finset.univ.filter
                    (fun i : Fin n =>
                      svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ (x : ℝ))).card : ℝ) ∂μ) -
                (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..((x : ℝ)),
                    rootedMPDensity ((n : ℝ) / (m : ℝ)) u)|)
            ≤ c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
  exact Statlib.Imported.sparse_cdf_comparison_of_polynomial_rate.{u} (1 / 9) (by norm_num)
    DenseGaussian.denseSymmetricPolynomialRate_one_ninth

set_option maxHeartbeats 4000000 in
theorem sparse_cdf_small : ∀ (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (hrhoMinus_pos : 0 < rhoMinus) (hrhoMinus_le : rhoMinus ≤ 1)
    (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (halpha0 : 15 < alpha0),
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ M2 : ℕ,
      ∀ (m n : ℕ), 1 ≤ n → n ≤ m → M2 ≤ m →
        rhoMinus ≤ (n : ℝ) / (m : ℝ) → (n : ℝ) / (m : ℝ) ≤ 1 →
        ∀ (p : ℝ), 0 < p → p ≤ 1 →
          Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p →
          ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ),
            (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j) →
            (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ) →
            (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ) →
            iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ →
            (∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0) →
            (∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1) →
            (∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
              μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt))) →
            (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
            (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
            (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
            iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
            IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
              (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
            ∀ tau : ℝ, 0 ≤ tau → ∃ G1 : Set Ω,
              MeasurableSet G1 ∧
                μ G1ᶜ ≤ ENNReal.ofReal (4 * Real.rpow (n : ℝ) (-(D0 + 2))) ∧
                  ∀ ω ∈ G1, ∀ i : Fin n,
                    |(n : ℝ)⁻¹ *
                        (((Finset.univ.filter (fun j : Fin n =>
                            svals (maskedScaled p (Xi ω) (Mask ω)) j ≤
                              mpQuantile ((n : ℝ) / (m : ℝ)) n i + tau)).card : ℝ)) -
                      (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..(mpQuantile ((n : ℝ) / (m : ℝ)) n i + tau),
                        rootedMPDensity ((n : ℝ) / (m : ℝ)) u)| ≤
                    2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) ∧
                    |(n : ℝ)⁻¹ *
                        (((Finset.univ.filter (fun j : Fin n =>
                            svals (maskedScaled p (Xi ω) (Mask ω)) j ≤
                              mpQuantile ((n : ℝ) / (m : ℝ)) n i - tau)).card : ℝ)) -
                      (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..(mpQuantile ((n : ℝ) / (m : ℝ)) n i - tau),
                        rootedMPDensity ((n : ℝ) / (m : ℝ)) u)| ≤
                    2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
  exact Statlib.Imported.sparse_cdf_small_of_polynomial_rate.{u} (1 / 9) (by norm_num)
    DenseGaussian.denseSymmetricPolynomialRate_one_ninth

set_option maxHeartbeats 4000000 in
theorem empirical_cdf : ∀ (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus) (h_rhoMinus_le : rhoMinus ≤ 1)
    (alpha0 : ℝ) (hAlpha0 : 15 < alpha0)
    (Kt : ℝ) (hKt : 0 < Kt)
    (D0 : ℝ) (hD0 : 0 < D0)
    (c0 : ℝ) (hc0 : 0 < c0),
    ∃ m1 : ℕ,
      ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hm1 : m1 ≤ m)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        (t : ℝ) (ht : 0 ≤ t),
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ),
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0) →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1) →
          (∀ (i : Fin m) (j : Fin n) (s : ℝ), 0 < s →
            μ {ω | s < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-s / Kt))) →
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
          (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
          (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
          IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
            (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
          sSup (Set.range fun x : {y : ℝ // 0 ≤ y} =>
              |(∫ ω, (n : ℝ)⁻¹ *
                  ((Finset.univ.filter
                    (fun i : Fin n =>
                      svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ (x : ℝ))).card : ℝ) ∂μ) -
                (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..((x : ℝ)),
                    rootedMPDensity ((n : ℝ) / (m : ℝ)) u)|)
            ≤ c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) →
          ∃ G1 : Set Ω,
            μ (G1ᶜ) ≤ ENNReal.ofReal (4 * Real.rpow (n : ℝ) (-(D0 + 2))) ∧
              ∀ ω ∈ G1, ∀ i : Fin n,
                |(n : ℝ)⁻¹ *
                    ((Finset.univ.filter
                      (fun j : Fin n =>
                        svals (maskedScaled p (Xi ω) (Mask ω)) j ≤
                          mpQuantile ((n : ℝ) / (m : ℝ)) n i + t)).card : ℝ) -
                  (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..
                      (mpQuantile ((n : ℝ) / (m : ℝ)) n i + t),
                    rootedMPDensity ((n : ℝ) / (m : ℝ)) u)| ≤
                  2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) ∧
                |(n : ℝ)⁻¹ *
                    ((Finset.univ.filter
                      (fun j : Fin n =>
                        svals (maskedScaled p (Xi ω) (Mask ω)) j ≤
                          mpQuantile ((n : ℝ) / (m : ℝ)) n i - t)).card : ℝ) -
                  (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..
                      (mpQuantile ((n : ℝ) / (m : ℝ)) n i - t),
                    rootedMPDensity ((n : ℝ) / (m : ℝ)) u)| ≤
                  2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
  exact Statlib.Imported.empirical_cdf_of_polynomial_rate.{u} (1 / 9) (by norm_num)
    DenseGaussian.denseSymmetricPolynomialRate_one_ninth

set_option maxHeartbeats 4000000 in
theorem quantile : ∀ (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus) (h_rhoMinus_le : rhoMinus ≤ 1)
    (alpha0 : ℝ) (hAlpha0 : 15 < alpha0)
    (Kt : ℝ) (hKt : 0 < Kt)
    (D0 : ℝ) (hD0 : 0 < D0)
    (c0 : ℝ) (hc0 : 0 < c0)
    (Ce : ℝ) (hCe : 0 < Ce)
    (cRho : ℝ) (hcRho : 0 < cRho)
    (tRho : ℝ) (htRho : 0 < tRho),
    ∃ mStar : ℕ,
      ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hmStar : mStar ≤ m)
        (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
        (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
        (hdelta : deltaM m ≤
          min 1 (tRho / (Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1))),
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ),
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ) →
          (∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0) →
          (∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1) →
          (∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
            μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt))) →
          (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j) →
          (∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1) →
          (∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p) →
          iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ →
          IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
            (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ →
          (∀ (tau : ℝ), 0 ≤ tau →
            ∃ G1 : Set Ω,
              μ G1ᶜ ≤ ENNReal.ofReal (4 * Real.rpow (n : ℝ) (-(D0 + 2))) ∧
                ∀ ω ∈ G1, ∀ i : Fin n,
                  |(n : ℝ)⁻¹ *
                      ((Finset.univ.filter
                        (fun j : Fin n =>
                          svals (maskedScaled p (Xi ω) (Mask ω)) j ≤
                            mpQuantile ((n : ℝ) / (m : ℝ)) n i + tau)).card : ℝ) -
                    (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..
                        (mpQuantile ((n : ℝ) / (m : ℝ)) n i + tau),
                      rootedMPDensity ((n : ℝ) / (m : ℝ)) u)| ≤
                    2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) ∧
                  |(n : ℝ)⁻¹ *
                      ((Finset.univ.filter
                        (fun j : Fin n =>
                          svals (maskedScaled p (Xi ω) (Mask ω)) j ≤
                            mpQuantile ((n : ℝ) / (m : ℝ)) n i - tau)).card : ℝ) -
                    (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..
                        (mpQuantile ((n : ℝ) / (m : ℝ)) n i - tau),
                      rootedMPDensity ((n : ℝ) / (m : ℝ)) u)| ≤
                    2 * c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2)) →
          (∃ G2 : Set Ω,
              μ G2ᶜ ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 2))) ∧
                ∀ ω ∈ G2,
                  svals (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩ ≤
                    mpLambdaPlus ((n : ℝ) / (m : ℝ)) + Ce * deltaM m ∧
                  mpLambdaMinus ((n : ℝ) / (m : ℝ)) - Ce * deltaM m ≤
                    svals (maskedScaled p (Xi ω) (Mask ω)) ⟨n - 1, by omega⟩) →
          ((∀ i : Fin n,
              mpLambdaMinus ((n : ℝ) / (m : ℝ)) ≤
                  mpQuantile ((n : ℝ) / (m : ℝ)) n i ∧
                mpQuantile ((n : ℝ) / (m : ℝ)) n i ≤
                  mpLambdaPlus ((n : ℝ) / (m : ℝ)) ∧
                (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..
                    (mpQuantile ((n : ℝ) / (m : ℝ)) n i),
                  rootedMPDensity ((n : ℝ) / (m : ℝ)) u) =
                  1 - (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ)) ∧
            (∀ x : ℝ, mpLambdaMinus ((n : ℝ) / (m : ℝ)) ≤ x →
              x ≤ mpLambdaPlus ((n : ℝ) / (m : ℝ)) →
                ∀ t : ℝ, 0 < t → t ≤ tRho →
                  (x + t ≤ mpLambdaPlus ((n : ℝ) / (m : ℝ)) →
                    cRho * t ^ ((3 : ℝ) / 2) ≤
                      (∫ u in x..(x + t), rootedMPDensity ((n : ℝ) / (m : ℝ)) u)) ∧
                  (mpLambdaMinus ((n : ℝ) / (m : ℝ)) ≤ x - t →
                    cRho * t ^ ((3 : ℝ) / 2) ≤
                      (∫ u in (x - t)..x,
                        rootedMPDensity ((n : ℝ) / (m : ℝ)) u)))) →
          ∃ G : Set Ω,
            μ Gᶜ ≤ ENNReal.ofReal (5 * Real.rpow (n : ℝ) (-(D0 + 2))) ∧
              ∀ ω ∈ G,
                (∀ i : Fin n,
                  |svals (maskedScaled p (Xi ω) (Mask ω)) i -
                      mpQuantile ((n : ℝ) / (m : ℝ)) n i| ≤
                    (Ce + (Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1)) * deltaM m) ∧
                maxDeviation (svals (maskedScaled p (Xi ω) (Mask ω)))
                    (mpQuantile ((n : ℝ) / (m : ℝ)) n) ≤
                  (Ce + (Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3) + 1)) * deltaM m := by
  exact Statlib.Imported.quantile_of_polynomial_rate.{u} (1 / 9) (by norm_num)
    DenseGaussian.denseSymmetricPolynomialRate_one_ninth

set_option maxHeartbeats 4000000 in
theorem sparse_coarse_rigidity
    (D0 : ℝ) (hD0 : 0 < D0)
    (rhoMinus : ℝ) (h_rhoMinus : 0 < rhoMinus)
    (Kt : ℝ) (hKt : 0 < Kt) :
    ∃ alpha1 : ℝ, 15 < alpha1 ∧
      ∀ (alpha0 : ℝ), alpha1 ≤ alpha0 →
        ∃ M0 : ℕ, 2 ≤ M0 ∧
          ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
            ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmM : M0 ≤ m)
              (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ))
              (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
              (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
              (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
              {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
              (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
              (hXi_meas : ∀ i j, Measurable fun ω => Xi ω i j)
              (hXi_int : ∀ i j, Integrable (fun ω => Xi ω i j) μ)
              (hXi_sq_int : ∀ i j, Integrable (fun ω => (Xi ω i j) ^ 2) μ)
              (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
              (hXi_mean : ∀ i j, ∫ ω, Xi ω i j ∂μ = 0)
              (hXi_var : ∀ i j, ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
              (hXi_tail : ∀ i j (t : ℝ), 0 < t →
                μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
              (hMask_meas : ∀ i j, Measurable fun ω => Mask ω i j)
              (hMask_val : ∀ i j ω, Mask ω i j = 0 ∨ Mask ω i j = 1)
              (hMask_law : ∀ i j, μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
              (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
              (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
                (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ),
            (μ {ω | C * deltaM m <
                  maxDeviation (svals (maskedScaled p (Xi ω) (Mask ω)))
                    (mpQuantile ((n : ℝ) / (m : ℝ)) n)} ≤
                ENNReal.ofReal (c * Real.rpow (n : ℝ) (-D0))) ∧
              (∀ ω, maxDeviation (svals (maskedScaled p (Xi ω) (Mask ω)))
                    (mpQuantile ((n : ℝ) / (m : ℝ)) n) ≤ C * deltaM m →
                  svals (maskedScaled p (Xi ω) (Mask ω)) ⟨0, by omega⟩ ≤
                    1 + Real.sqrt ((n : ℝ) / (m : ℝ)) + C * deltaM m) := by
  exact Statlib.Imported.sparse_coarse_rigidity_of_polynomial_rate.{u} (1 / 9) (by norm_num)
    DenseGaussian.denseSymmetricPolynomialRate_one_ninth D0 hD0 rhoMinus h_rhoMinus Kt hKt

end ResidualSparseRepair20261106.Completed

#print axioms ResidualSparseRepair20261106.Completed.sparse_cdf_comparison
#print axioms ResidualSparseRepair20261106.Completed.sparse_cdf_small
#print axioms ResidualSparseRepair20261106.Completed.empirical_cdf
#print axioms ResidualSparseRepair20261106.Completed.quantile
#print axioms ResidualSparseRepair20261106.Completed.sparse_coarse_rigidity

