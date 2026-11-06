import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_639d5a54c5a150872e4f
import ProverJobs.ResidualE2ESupport20261106.M_847e99766d997626bb33
import ProverJobs.ResidualE2ESupport20261106.M_2e445e9d131a16ed6935
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
universe u

set_option maxHeartbeats 4000000 in
set_option autoImplicit false in
theorem quantile_of_polynomial_rate (beta : ℝ) (hbeta : 1 / 10 < beta)
    (h_dense : DenseSymmetricPolynomialRate beta) : ∀ (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus) (h_rhoMinus_le : rhoMinus ≤ 1)
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
  /- @proof-region region.target-node.session.effc5a9ed69aa8ca begin -/
  have statopia_math_node_353613729_cdc60966 := empirical_cdf_of_polynomial_rate.{u} beta hbeta h_dense

  intro rhoMinus h_rhoMinus_pos h_rhoMinus_le alpha0 halpha0 Kt hKt D0 hD0 c0 hc0 Ce hCe cRho hcRho tRho htRho
  let Al : ℝ := Real.rpow (2 * c0 / cRho) ((2 : ℝ) / 3)
  let Dst : ℝ := Al + 1
  have h2c0 : (0:ℝ) < 2 * c0 := by linarith
  have hbase : (0:ℝ) ≤ 2 * c0 / cRho := le_of_lt (div_pos h2c0 hcRho)
  have hAl_nonneg : 0 ≤ Al := Real.rpow_nonneg hbase _
  have hDst_pos : 0 < Dst := by simp only [Dst]; linarith
  have hAl_lt : Al < Dst := by simp only [Dst]; linarith
  have hAl32 : Al ^ ((3:ℝ)/2) = 2 * c0 / cRho := by
    have hmul : (2*c0/cRho) ^ (((2:ℝ)/3) * ((3:ℝ)/2)) = ((2*c0/cRho)^((2:ℝ)/3)) ^ ((3:ℝ)/2) :=
      Real.rpow_mul hbase ((2:ℝ)/3) ((3:ℝ)/2)
    rw [show ((2:ℝ)/3) * ((3:ℝ)/2) = 1 by norm_num, Real.rpow_one] at hmul
    simp only [Al]
    exact hmul.symm
  have hkey : 2 * c0 ≤ cRho * Dst ^ ((3:ℝ)/2) := by
    have h1 : Al ^ ((3:ℝ)/2) < Dst ^ ((3:ℝ)/2) := Real.rpow_lt_rpow hAl_nonneg hAl_lt (by norm_num)
    have h2 : cRho * Al ^ ((3:ℝ)/2) < cRho * Dst ^ ((3:ℝ)/2) := mul_lt_mul_of_pos_left h1 hcRho
    have h3 : cRho * Al ^ ((3:ℝ)/2) = 2 * c0 := by rw [hAl32]; field_simp
    linarith
  let c : ℝ := min 1 (tRho / Dst)
  have hc : 0 < c := by
    simp only [c]
    exact lt_min (by norm_num) (div_pos htRho hDst_pos)
  let N : ℕ := max 2 (Nat.floor (Real.exp (1 / c)) + 1)
  have hN : ∀ k : ℕ, N ≤ k → deltaM k ≤ min 1 (tRho / Dst) := by
    intro k hk
    have hk2 : Nat.floor (Real.exp (1 / c)) + 1 ≤ k :=
      le_trans (le_max_right 2 (Nat.floor (Real.exp (1 / c)) + 1)) hk
    have hexp_lt : Real.exp (1 / c) < (k : ℝ) := by
      have h1 : Real.exp (1 / c) < (Nat.floor (Real.exp (1 / c)) : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ((Nat.floor (Real.exp (1 / c)) + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      push_cast at h2
      linarith
    have hexp_pos : 0 < Real.exp (1 / c) := Real.exp_pos _
    have hcinvpos : (0:ℝ) < 1 / c := by rw [one_div]; exact inv_pos.mpr hc
    have hlog_gt : 1 / c < Real.log (k : ℝ) := by
      have h := Real.log_lt_log hexp_pos hexp_lt
      rw [Real.log_exp] at h
      exact h
    have hlogpos : 0 < Real.log (k : ℝ) := lt_trans hcinvpos hlog_gt
    have hcinv : (1 / c)⁻¹ = c := by rw [one_div, inv_inv]
    have hlt : (Real.log (k : ℝ))⁻¹ < c := by
      have h := (inv_lt_inv₀ hlogpos hcinvpos).mpr hlog_gt
      rw [hcinv] at h
      exact h
    simp only [deltaM]
    exact le_of_lt hlt
  refine ⟨N, ?_⟩
  intro m n hm hn hnm hmStar hrho_lo hrho_hi p hp0 hp1 hsparse hdelta
  intro Omega _ mu _ Xi Mask
    hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
    hMask_meas hMask_val hMask_law hMask_indep hIndep hgrid hedge hmp
  obtain ⟨hquant, hmass⟩ := hmp
  let d : ℝ := deltaM m
  let t : ℝ := Dst * d
  let C1 : ℝ := Ce + Dst
  have hCD : C1 = Ce + Dst := rfl
  have hdl_nonneg : 0 ≤ d := by
    simp only [d, deltaM]
    exact inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast hm))
  have hd_le_tRho : d ≤ tRho / Dst := le_trans hdelta (min_le_right 1 _)
  have ht_nonneg : 0 ≤ t := by simp only [t]; exact mul_nonneg (le_of_lt hDst_pos) hdl_nonneg
  have ht_le : t ≤ tRho := by
    simp only [t]
    calc Dst * d ≤ Dst * (tRho / Dst) := mul_le_mul_of_nonneg_left hd_le_tRho (le_of_lt hDst_pos)
      _ = tRho := by field_simp
  have hmass_rpow : 2 * c0 * d ^ ((3:ℝ)/2) ≤ cRho * t ^ ((3:ℝ)/2) := by
    have hd32 : 0 ≤ d ^ ((3:ℝ)/2) := Real.rpow_nonneg hdl_nonneg _
    have ht_eq : t ^ ((3:ℝ)/2) = Dst ^ ((3:ℝ)/2) * d ^ ((3:ℝ)/2) := by
      simp only [t]
      exact Real.mul_rpow (le_of_lt hDst_pos) hdl_nonneg
    calc 2 * c0 * d ^ ((3:ℝ)/2) ≤ (cRho * Dst ^ ((3:ℝ)/2)) * d ^ ((3:ℝ)/2) :=
          mul_le_mul_of_nonneg_right hkey hd32
      _ = cRho * (Dst ^ ((3:ℝ)/2) * d ^ ((3:ℝ)/2)) := by ring
      _ = cRho * t ^ ((3:ℝ)/2) := by rw [ht_eq]
  obtain ⟨G1, hG1mu, hG1⟩ := hgrid t ht_nonneg
  obtain ⟨G2, hG2mu, hG2⟩ := hedge
  refine ⟨G1 ∩ G2, ?_, ?_⟩

  · have hcompl : (G1 ∩ G2)ᶜ = G1ᶜ ∪ G2ᶜ := by
      ext x; simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff]; tauto
    rw [hcompl]
    refine le_trans (measure_union_le G1ᶜ G2ᶜ) ?_
    refine le_trans (add_le_add hG1mu hG2mu) ?_
    have hr : 0 ≤ Real.rpow (n:ℝ) (-(D0+2)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 4 * Real.rpow (n:ℝ) (-(D0+2))) hr]
    have heq : 4 * Real.rpow (n:ℝ) (-(D0+2)) + Real.rpow (n:ℝ) (-(D0+2)) = 5 * Real.rpow (n:ℝ) (-(D0+2)) := by ring
    rw [heq]
  · intro om hom
    obtain ⟨_, _, _, _, hD⟩ :=
      statopia_math_node_2026933490_bd269a1d rhoMinus h_rhoMinus_pos h_rhoMinus_le
    obtain ⟨_, _, _, _, _, hQAll, _⟩ := hD ((n:ℝ)/(m:ℝ)) hrho_lo hrho_hi
    have hsv : svals (maskedScaled p (Xi om) (Mask om)) =
        (fun k : Fin n => Statlib.HighDim.MatrixAnalysis.singularValues
          (maskedScaled p (Xi om) (Mask om)) (Fin.cast (Nat.min_eq_right hnm).symm k)) := by
      funext k
      rfl
    have hanti : Antitone (svals (maskedScaled p (Xi om) (Mask om))) := by
      intro a b hab
      simp only [hsv]
      have hle : (Fin.cast (Nat.min_eq_right hnm).symm a : Fin (min m n)) ≤
          Fin.cast (Nat.min_eq_right hnm).symm b := by
        have hva : (Fin.cast (Nat.min_eq_right hnm).symm a : Fin (min m n)).val = a.val := rfl
        have hvb : (Fin.cast (Nat.min_eq_right hnm).symm b : Fin (min m n)).val = b.val := rfl
        have hlt := a.isLt
        have hlt' := b.isLt
        omega
      exact Statlib.HighDim.MatrixAnalysis.singularValues_antitone _ hle
    have hTcard : ∀ i : Fin n,
        (Finset.univ.filter (fun k : Fin n => k ≤ i)).card = i.val + 1 := by
      intro i
      let e : Fin (i.val + 1) ↪ Fin n :=
        ⟨fun j => ⟨j.val, by have := j.isLt; omega⟩, fun a b h => by
          have hh : a.val = b.val := congrArg (fun z : Fin n => z.val) h
          exact Fin.ext hh⟩
      have himg : (Finset.univ : Finset (Fin (i.val + 1))).map e
          = Finset.univ.filter (fun k : Fin n => k ≤ i) := by
        ext k
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, rfl⟩
          have hv : (e j).val ≤ i.val := by
            show j.val ≤ i.val
            have := j.isLt
            omega
          omega
        · intro hk
          refine ⟨⟨k.val, by have := k.isLt; omega⟩, ?_⟩
          exact Fin.ext rfl
      rw [← himg, Finset.card_map]
      simp
    have hTcard_dn : ∀ i : Fin n,
        (Finset.univ.filter (fun k : Fin n => i ≤ k)).card = n - i.val := by
      intro i
      let e : Fin (n - i.val) ↪ Fin n :=
        ⟨fun j => ⟨i.val + j.val, by have := j.isLt; have := i.isLt; omega⟩, fun a b h => by
          have hh : i.val + a.val = i.val + b.val := congrArg (fun z : Fin n => z.val) h
          exact Fin.ext (by omega)⟩
      have himg : (Finset.univ : Finset (Fin (n - i.val))).map e
          = Finset.univ.filter (fun k : Fin n => i ≤ k) := by
        ext k
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, rfl⟩
          have hv : i.val ≤ (e j).val := by
            show i.val ≤ i.val + j.val
            have := j.isLt
            omega
          omega
        · intro hk
          have hk' : i.val ≤ k.val := by omega
          refine ⟨⟨k.val - i.val, by have := k.isLt; omega⟩, ?_⟩
          apply Fin.ext
          show i.val + (k.val - i.val) = k.val
          omega
      rw [← himg, Finset.card_map]
      simp
    have hcount_up : ∀ (i : Fin n) (x : ℝ),
        x < svals (maskedScaled p (Xi om) (Mask om)) i →
        ((Finset.univ.filter (fun k : Fin n =>
            svals (maskedScaled p (Xi om) (Mask om)) k ≤ x)).card : ℝ)
          ≤ ((n - (i.val + 1) : ℕ) : ℝ) := by
      intro i x hx
      set S := Finset.univ.filter (fun k : Fin n => svals (maskedScaled p (Xi om) (Mask om)) k ≤ x) with hS
      set T := Finset.univ.filter (fun k : Fin n => k ≤ i) with hT
      have hdisj : Disjoint S T := by
        rw [Finset.disjoint_left]
        intro k hkS hkT
        simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and] at hkS hkT
        have hki : svals (maskedScaled p (Xi om) (Mask om)) i ≤
            svals (maskedScaled p (Xi om) (Mask om)) k := hanti hkT
        linarith
      have hunion : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hdisj
      have hle : (S ∪ T).card ≤ n := by
        have h := Finset.card_le_card (Finset.subset_univ (S ∪ T))
        simpa using h
      have hTcard_i : T.card = i.val + 1 := by rw [hT]; exact hTcard i
      have hSn : S.card ≤ n - (i.val + 1) := by
        rw [hunion, hTcard_i] at hle
        omega
      exact_mod_cast hSn
    have hcount_dn : ∀ (i : Fin n) (x : ℝ),
        svals (maskedScaled p (Xi om) (Mask om)) i < x →
        ((n - i.val : ℕ) : ℝ)
          ≤ ((Finset.univ.filter (fun k : Fin n =>
              svals (maskedScaled p (Xi om) (Mask om)) k ≤ x)).card : ℝ) := by
      intro i x hx
      set S := Finset.univ.filter (fun k : Fin n => svals (maskedScaled p (Xi om) (Mask om)) k ≤ x) with hS
      set T := Finset.univ.filter (fun k : Fin n => i ≤ k) with hT
      have hTsub : T ⊆ S := by
        intro k hk
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
        have hki : svals (maskedScaled p (Xi om) (Mask om)) k ≤
            svals (maskedScaled p (Xi om) (Mask om)) i := hanti hk
        linarith
      have hcard : T.card ≤ S.card := Finset.card_le_card hTsub
      have hTcard_i : T.card = n - i.val := by rw [hT]; exact hTcard_dn i
      rw [hTcard_i] at hcard
      exact_mod_cast hcard
    have hmain : ∀ i : Fin n, |svals (maskedScaled p (Xi om) (Mask om)) i - mpQuantile ((n:ℝ)/(m:ℝ)) n i| ≤ C1 * d := by
      intro i
      have hom1 : om ∈ G1 := hom.1
      have hom2 : om ∈ G2 := hom.2
      obtain ⟨hgrid_up, hgrid_dn⟩ := hG1 om hom1 i
      obtain ⟨hs0_le, hsn_ge⟩ := hG2 om hom2
      obtain ⟨hγmem, -, hInt_eq, hadd_up, hadd_dn⟩ := hQAll n hn i
      have hlam_minus : mpLambdaMinus ((n:ℝ)/(m:ℝ)) = 1 - Real.sqrt ((n:ℝ)/(m:ℝ)) := rfl
      have hlam_plus : mpLambdaPlus ((n:ℝ)/(m:ℝ)) = 1 + Real.sqrt ((n:ℝ)/(m:ℝ)) := rfl
      have hC1d : C1 * d = Ce * d + t := by rw [hCD]; simp only [t]; ring
      have hCe_d_nonneg : 0 ≤ Ce * d := mul_nonneg (le_of_lt hCe) hdl_nonneg
      have hnn : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnn
      have hninv : (0:ℝ) ≤ (n:ℝ)⁻¹ := le_of_lt (inv_pos.mpr hnn)
      rw [abs_le]
      constructor
      · by_contra hcon
        rw [not_le] at hcon
        have hsi : svals (maskedScaled p (Xi om) (Mask om)) i < mpQuantile ((n:ℝ)/(m:ℝ)) n i - C1 * d := by linarith
        by_cases hcase : mpLambdaMinus ((n:ℝ)/(m:ℝ)) ≤ mpQuantile ((n:ℝ)/(m:ℝ)) n i - t
        · have hlt : svals (maskedScaled p (Xi om) (Mask om)) i < mpQuantile ((n:ℝ)/(m:ℝ)) n i - t := by
            have hle : mpQuantile ((n:ℝ)/(m:ℝ)) n i - C1 * d ≤ mpQuantile ((n:ℝ)/(m:ℝ)) n i - t := by rw [hC1d]; linarith
            linarith
          have hFA_ge : ((n - i.val : ℕ) : ℝ) / (n:ℝ) ≤ (n:ℝ)⁻¹ * ((Finset.univ.filter (fun k : Fin n => svals (maskedScaled p (Xi om) (Mask om)) k ≤ mpQuantile ((n:ℝ)/(m:ℝ)) n i - t)).card : ℝ) := by
            have hcount := hcount_dn i (mpQuantile ((n:ℝ)/(m:ℝ)) n i - t) hlt
            have hmul := mul_le_mul_of_nonneg_left hcount hninv
            have heq : (n:ℝ)⁻¹ * ((n - i.val : ℕ) : ℝ) = ((n - i.val : ℕ) : ℝ) / (n:ℝ) := by rw [div_eq_inv_mul]
            rwa [heq] at hmul
          have hFρ_le : (∫ u in (mpLambdaMinus ((n:ℝ)/(m:ℝ)))..(mpQuantile ((n:ℝ)/(m:ℝ)) n i - t), rootedMPDensity ((n:ℝ)/(m:ℝ)) u) ≤ 1 - (((i:ℕ):ℝ) + 1/2) / (n:ℝ) - cRho * t ^ ((3:ℝ)/2) := by
            rcases lt_or_eq_of_le ht_nonneg with htpos | ht0
            · have hmass_dn : cRho * t ^ ((3:ℝ)/2) ≤ (∫ u in (mpQuantile ((n:ℝ)/(m:ℝ)) n i - t)..(mpQuantile ((n:ℝ)/(m:ℝ)) n i), rootedMPDensity ((n:ℝ)/(m:ℝ)) u) := (hmass (mpQuantile ((n:ℝ)/(m:ℝ)) n i) hγmem.1 hγmem.2 t htpos ht_le).2 hcase
              rw [hadd_dn t htpos, hInt_eq]
              linarith
            · have ht_eq0 : t = 0 := ht0.symm
              have h0 : cRho * (0:ℝ) ^ ((3:ℝ)/2) = 0 := by
                rw [Real.zero_rpow (by norm_num : ((3:ℝ)/2) ≠ 0), mul_zero]
              simp only [ht_eq0, h0, sub_zero, hInt_eq, le_refl]
          have hGr'dn : (n:ℝ)⁻¹ * ((Finset.univ.filter (fun k : Fin n => svals (maskedScaled p (Xi om) (Mask om)) k ≤ mpQuantile ((n:ℝ)/(m:ℝ)) n i - t)).card : ℝ) - (∫ u in (mpLambdaMinus ((n:ℝ)/(m:ℝ)))..(mpQuantile ((n:ℝ)/(m:ℝ)) n i - t), rootedMPDensity ((n:ℝ)/(m:ℝ)) u) ≤ 2 * c0 * d ^ ((3:ℝ)/2) := (abs_le.mp hgrid_dn).2
          have hgap2 : ((n - i.val : ℕ) : ℝ) / (n:ℝ) - (1 - (((i:ℕ):ℝ) + 1/2)/(n:ℝ)) = 1/(2*(n:ℝ)) := by
            have hnc : ((n - i.val : ℕ) : ℝ) = (n:ℝ) - (i.val:ℝ) := by
              rw [Nat.cast_sub (by omega : i.val ≤ n)]
            have hiv : (((i:ℕ):ℝ)) = (i.val : ℝ) := by simp
            rw [hnc, hiv]
            field_simp
            ring
          have hpos : (0:ℝ) < 1/(2*(n:ℝ)) := by rw [one_div]; exact inv_pos.mpr (by linarith)
          linarith [hFA_ge, hFρ_le, hGr'dn, hgap2, hmass_rpow, hpos]
        · push_neg at hcase
          rw [hlam_minus] at hcase
          have hile : i ≤ (⟨n - 1, by omega⟩ : Fin n) := by
            have hv : (⟨n - 1, by omega⟩ : Fin n).val = n - 1 := rfl
            have hi := i.isLt
            omega
          have hsn_i : (1 - Real.sqrt ((n:ℝ)/(m:ℝ)) - Ce * d) ≤ svals (maskedScaled p (Xi om) (Mask om)) i := by
            have h2 : (1 - Real.sqrt ((n:ℝ)/(m:ℝ)) - Ce * d) ≤ svals (maskedScaled p (Xi om) (Mask om)) ⟨n - 1, by omega⟩ := hsn_ge
            have h3 := hanti hile
            linarith
          rw [hC1d] at hsi
          linarith
      · by_contra hcon
        rw [not_le] at hcon
        have hsi : mpQuantile ((n:ℝ)/(m:ℝ)) n i + C1 * d < svals (maskedScaled p (Xi om) (Mask om)) i := by linarith
        by_cases hcase : mpQuantile ((n:ℝ)/(m:ℝ)) n i + t ≤ mpLambdaPlus ((n:ℝ)/(m:ℝ))
        · have hgt : mpQuantile ((n:ℝ)/(m:ℝ)) n i + t < svals (maskedScaled p (Xi om) (Mask om)) i := by
            have hle : mpQuantile ((n:ℝ)/(m:ℝ)) n i + t ≤ mpQuantile ((n:ℝ)/(m:ℝ)) n i + C1 * d := by rw [hC1d]; linarith
            linarith
          have hFA_le : (n:ℝ)⁻¹ * ((Finset.univ.filter (fun k : Fin n => svals (maskedScaled p (Xi om) (Mask om)) k ≤ mpQuantile ((n:ℝ)/(m:ℝ)) n i + t)).card : ℝ) ≤ 1 - (((i:ℕ):ℝ) + 1) / (n:ℝ) := by
            have hi1 : i.val + 1 ≤ n := by have := i.isLt; omega
            have hcast : ((n - (i.val+1) : ℕ) : ℝ) = (n:ℝ) - ((i.val : ℝ) + 1) := by
              rw [Nat.cast_sub hi1]; push_cast; ring
            have hcount := hcount_up i (mpQuantile ((n:ℝ)/(m:ℝ)) n i + t) hgt
            have hmul := mul_le_mul_of_nonneg_left hcount hninv
            rw [hcast] at hmul
            have hiv : (((i:ℕ):ℝ)) = (i.val : ℝ) := by simp
            have hstep : (n:ℝ)⁻¹ * ((n:ℝ) - ((i.val:ℝ) + 1)) = 1 - (((i:ℕ):ℝ) + 1) / (n:ℝ) := by
              rw [hiv]
              field_simp
            rw [hstep] at hmul
            exact hmul
          have hFρ_ge : 1 - (((i:ℕ):ℝ) + 1/2) / (n:ℝ) + cRho * t ^ ((3:ℝ)/2) ≤ (∫ u in (mpLambdaMinus ((n:ℝ)/(m:ℝ)))..(mpQuantile ((n:ℝ)/(m:ℝ)) n i + t), rootedMPDensity ((n:ℝ)/(m:ℝ)) u) := by
            rcases lt_or_eq_of_le ht_nonneg with htpos | ht0
            · have hmass_up : cRho * t ^ ((3:ℝ)/2) ≤ (∫ u in (mpQuantile ((n:ℝ)/(m:ℝ)) n i)..(mpQuantile ((n:ℝ)/(m:ℝ)) n i + t), rootedMPDensity ((n:ℝ)/(m:ℝ)) u) := (hmass (mpQuantile ((n:ℝ)/(m:ℝ)) n i) hγmem.1 hγmem.2 t htpos ht_le).1 hcase
              rw [hadd_up t htpos, hInt_eq]
              linarith [hmass_up]
            · have ht_eq0 : t = 0 := ht0.symm
              have h0 : cRho * (0:ℝ) ^ ((3:ℝ)/2) = 0 := by
                rw [Real.zero_rpow (by norm_num : ((3:ℝ)/2) ≠ 0), mul_zero]
              simp only [ht_eq0, h0, add_zero]
              exact le_of_eq hInt_eq.symm
          have hGr' : (∫ u in (mpLambdaMinus ((n:ℝ)/(m:ℝ)))..(mpQuantile ((n:ℝ)/(m:ℝ)) n i + t), rootedMPDensity ((n:ℝ)/(m:ℝ)) u) - (n:ℝ)⁻¹ * ((Finset.univ.filter (fun k : Fin n => svals (maskedScaled p (Xi om) (Mask om)) k ≤ mpQuantile ((n:ℝ)/(m:ℝ)) n i + t)).card : ℝ) ≤ 2 * c0 * d ^ ((3:ℝ)/2) := by
            have h1 : -(2 * c0 * d ^ ((3:ℝ)/2)) ≤ (n:ℝ)⁻¹ * ((Finset.univ.filter (fun k : Fin n => svals (maskedScaled p (Xi om) (Mask om)) k ≤ mpQuantile ((n:ℝ)/(m:ℝ)) n i + t)).card : ℝ) - (∫ u in (mpLambdaMinus ((n:ℝ)/(m:ℝ)))..(mpQuantile ((n:ℝ)/(m:ℝ)) n i + t), rootedMPDensity ((n:ℝ)/(m:ℝ)) u) := (abs_le.mp hgrid_up).1
            linarith
          have hgap : (((i:ℕ):ℝ) + 1) / (n:ℝ) - (((i:ℕ):ℝ) + 1/2) / (n:ℝ) = 1/(2*(n:ℝ)) := by
            field_simp
            ring
          have hpos : (0:ℝ) < 1/(2*(n:ℝ)) := by rw [one_div]; exact inv_pos.mpr (by linarith)
          linarith [hFA_le, hFρ_ge, hGr', hgap, hmass_rpow, hpos]
        · push_neg at hcase
          rw [hlam_plus] at hcase
          have h0le : (⟨0, by omega⟩ : Fin n) ≤ i := by
            have hv : (⟨0, by omega⟩ : Fin n).val = 0 := rfl
            omega
          have hs0_i : svals (maskedScaled p (Xi om) (Mask om)) i ≤ 1 + Real.sqrt ((n:ℝ)/(m:ℝ)) + Ce * d := by
            have h2 : svals (maskedScaled p (Xi om) (Mask om)) ⟨0, by omega⟩ ≤ 1 + Real.sqrt ((n:ℝ)/(m:ℝ)) + Ce * d := hs0_le
            have h3 := hanti h0le
            linarith
          rw [hC1d] at hsi
          linarith
    refine ⟨hmain, ?_⟩
    unfold maxDeviation
    refine Real.sSup_le (fun a ha => ?_) ?_
    · obtain ⟨i, rfl⟩ := ha
      exact hmain i
    · have hDstnn : (0:ℝ) ≤ Ce + Dst := by linarith
      exact mul_nonneg hDstnn hdl_nonneg
  /- @proof-region region.target-node.session.effc5a9ed69aa8ca end -/

end Statlib.Imported

#print axioms Statlib.Imported.quantile_of_polynomial_rate

