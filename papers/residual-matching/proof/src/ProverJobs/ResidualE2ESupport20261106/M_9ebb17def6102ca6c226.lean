import Lean
import ProverJobs.ResidualE2ESupport20261106.M_19397ecf43739ad33005
import ProverJobs.ResidualE2ESupport20261106.ExternalNodes.Node_610ef984489599a94e55
import ProverJobs.ResidualE2ESupport20261106.M_2bc3eb410430a5b6fbb6
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_603be9b01d60bdf91269
import ProverJobs.ResidualE2ESupport20261106.M_71b77c9e423ac8b670cf
import ProverJobs.ResidualE2ESupport20261106.M_afb5bd83d519f929fd03
import ProverJobs.ResidualE2ESupport20261106.M_639d5a54c5a150872e4f
import ProverJobs.ResidualE2ESupport20261106.M_f623b618cad841a0fbf7
import ProverJobs.ResidualE2ESupport20261106.M_6a1ae14d38a9be2d42cf
import ProverJobs.ResidualE2ESupport20261106.M_ed5e33926b5e2204f3f1
import ProverJobs.ResidualE2ESupport20261106.M_6cfb38dfcc790cb55efd
import ProverJobs.ResidualE2ESupport20261106.M_23dc062aaeba48e456ab
import ProverJobs.ResidualE2ESupport20261106.M_2e445e9d131a16ed6935
import ProverJobs.ResidualE2ESupport20261106.M_573763e32e6cc361a26d
import ProverJobs.ResidualE2ESupport20261106.M_24e4399710401de9771f
import ProverJobs.ResidualE2ESupport20261106.M_442f8e8866630bca7674

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
theorem sparse_cdf_comparison_of_polynomial_rate (beta : ℝ) (hbeta : 1 / 10 < beta)
    (h_dense : DenseSymmetricPolynomialRate beta) : ∀ (D0 : ℝ) (hD0 : 0 < D0)
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
  /- @proof-region region.target-node.session.f62f707a2e2311de begin -/

  intro D0 hD0 rhoMinus h_rhoMinus_pos h_rhoMinus_le Kt hKt alpha0 h_alpha0
  classical
  obtain ⟨Csm, hCsm_ge, hCsm⟩ :=
    ResidualSparseRepair20261106.bai_smoothing (2 / (Real.pi * rhoMinus)) (by positivity)

  obtain ⟨C_e, _, Me, hEdge⟩ :=
    statopia_math_node_790018995_867172dc D0 hD0 rhoMinus h_rhoMinus_pos
      h_rhoMinus_le Kt hKt alpha0 h_alpha0 (Kt * (D0 + 12)) le_rfl


  obtain ⟨cRho, tRho, hcRho, htRho, hMPall⟩ :=
    statopia_math_node_2026933490_bd269a1d rhoMinus h_rhoMinus_pos h_rhoMinus_le
  obtain ⟨c1, hc1, hRes⟩ := statopia_math_node_2849745169_758d55f9.{u}


  obtain ⟨C4, hC4, mG, hGauss⟩ :=
    h_dense rhoMinus h_rhoMinus_pos h_rhoMinus_le

  set a1 : ℝ := c1 * (1 + Kt) ^ 3 * ((1 + 1 / rhoMinus) / 2) with ha1_def
  have ha1_pos : 0 < a1 := by
    have h1 : 0 < (1 + Kt) ^ 3 := pow_pos (by linarith : (0 : ℝ) < 1 + Kt) 3
    have h3 : 0 < 1 / rhoMinus := one_div_pos.mpr h_rhoMinus_pos
    have h2 : 0 < (1 + 1 / rhoMinus) / 2 := by linarith
    rw [ha1_def]
    exact mul_pos (mul_pos hc1 h1) h2
  have hc0 : 0 < 2 * Csm * (40 * a1 + 40 * Real.pi * C4 + 2) + 1 := by
    have hpi4 : 0 < 40 * Real.pi * C4 := mul_pos (mul_pos (by norm_num) Real.pi_pos) hC4
    have hinner : 0 < 40 * a1 + 40 * Real.pi * C4 + 2 := by linarith
    have hCsm_pos : 0 < Csm := lt_of_lt_of_le zero_lt_one hCsm_ge
    have hpos : 0 < 2 * Csm * (40 * a1 + 40 * Real.pi * C4 + 2) :=
      mul_pos (by linarith) hinner
    linarith
  have hpoly : ∀ (c K A : ℝ), 0 < c → 0 < K → 0 < A →
      ∃ M : ℕ, ∀ x : ℝ, (M : ℝ) ≤ x → 1 ≤ x →
        A * x ^ (-c) * (Real.log x) ^ K ≤ 1 := by
    intro c K A hc hK hA
    have hlo : (fun x : ℝ => (Real.log x) ^ K) =o[Filter.atTop]
        (fun x : ℝ => x ^ (c / 2)) :=
      isLittleO_log_rpow_rpow_atTop (s := c / 2) K (by linarith : (0 : ℝ) < c / 2)
    have hev : ∀ᶠ x : ℝ in Filter.atTop, (Real.log x) ^ K ≤ |x ^ (c / 2)| := by
      filter_upwards [hlo.eventuallyLE] with x hx
      simp only [Real.norm_eq_abs] at hx
      exact le_trans (le_abs_self _) hx
    obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max ⌈M0⌉₊ ⌈A ^ (2 / c)⌉₊, ?_⟩
    intro x hx hx1
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hMx : M0 ≤ x := by
      have h1 : M0 ≤ ((⌈M0⌉₊ : ℕ) : ℝ) := Nat.le_ceil M0
      have h2 : ((⌈M0⌉₊ : ℕ) : ℝ) ≤ ((max ⌈M0⌉₊ ⌈A ^ (2 / c)⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_max_left (⌈M0⌉₊) (⌈A ^ (2 / c)⌉₊)
      linarith
    have hxa : A ^ (2 / c) ≤ x := by
      have h1 : A ^ (2 / c) ≤ ((⌈A ^ (2 / c)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈A ^ (2 / c)⌉₊ : ℕ) : ℝ) ≤ ((max ⌈M0⌉₊ ⌈A ^ (2 / c)⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_max_right (⌈M0⌉₊) (⌈A ^ (2 / c)⌉₊)
      linarith
    have hle1 : (Real.log x) ^ K ≤ x ^ (c / 2) := by
      have h := hM0 x hMx
      rwa [abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at h
    have h2c : 2 / c * (c / 2) = 1 := by
      have hc0 : c ≠ 0 := ne_of_gt hc
      field_simp
    have hAc : A = (A ^ (2 / c)) ^ (c / 2) := by
      rw [← Real.rpow_mul hA.le, h2c, show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, pow_one]
    have hle2 : A ≤ x ^ (c / 2) := by
      rw [hAc]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hA.le _) hxa (by linarith : (0 : ℝ) ≤ c / 2)
    have hxpos : 0 < x ^ (c / 2) := Real.rpow_pos_of_pos hx0 _
    have hstep : A * x ^ (-c / 2) ≤ 1 := by
      have hneg : x ^ (-c / 2) = (x ^ (c / 2))⁻¹ := by
        rw [show -c / 2 = -(c / 2) by ring]
        exact Real.rpow_neg hx0.le (c / 2)
      rw [hneg]
      calc A * (x ^ (c / 2))⁻¹ ≤ x ^ (c / 2) * (x ^ (c / 2))⁻¹ :=
            mul_le_mul_of_nonneg_right hle2 (le_of_lt (inv_pos.mpr hxpos))
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hxpos)

    calc A * x ^ (-c) * (Real.log x) ^ K
        ≤ A * x ^ (-c) * x ^ (c / 2) :=
          mul_le_mul_of_nonneg_left hle1 (mul_nonneg hA.le (Real.rpow_nonneg hx0.le _))
      _ = A * (x ^ (-c) * x ^ (c / 2)) := by rw [mul_assoc]
      _ = A * x ^ (-c / 2) := by
          rw [← Real.rpow_add hx0, show -c + c / 2 = -c / 2 by ring]
      _ ≤ 1 := hstep
  obtain ⟨M3, hM3⟩ := hpoly (beta - 1 / 10) (3 / 2) 1 (by linarith) (by norm_num) (by norm_num)
  obtain ⟨M4, hM4⟩ := hpoly (D0 / 2 + 9 / 10) ((3 : ℝ) / 2)
    (2 * Csm * rhoMinus ^ (-(D0 + 2) / 2)) (by linarith) (by norm_num)
    (mul_pos (by linarith) (Real.rpow_pos_of_pos h_rhoMinus_pos _))
  refine ⟨2 * Csm * (40 * a1 + 40 * Real.pi * C4 + 2) + 1, hc0,
    max (max (max Me mG) 3) (max M3 M4), ?_⟩
  intro m n hn hnm hm1 hrho_lo hrho_hi p hp0 hp1 hsparse Ω _ μ _ Xi Mask
    hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail
    hMask_meas hMask_val hMask_law hMask_indep hIndep
  have hm : 1 ≤ m := by omega
  have hmaxm : max Me mG ≤ m :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm1)
  have hMe : Me ≤ m := le_trans (le_max_left _ _) hmaxm
  have hMG : mG ≤ m := le_trans (le_max_right _ _) hmaxm
  have h3m : 3 ≤ m := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm1)
  have hM3m : M3 ≤ m := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hm1)
  have hM4m : M4 ≤ m := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hm1)

  have hm1' : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos hm1'
  have hδnonneg : (0 : ℝ) ≤ Real.rpow (deltaM m) ((3 : ℝ) / 2) :=
    Real.rpow_nonneg (le_of_lt (by rw [deltaM]; exact inv_pos.mpr hmlog)) _
  refine csSup_le ⟨_, ⟨⟨0, le_rfl⟩, rfl⟩⟩ ?_
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℕ) < n := by omega
    exact_mod_cast h
  have hsvals_nonneg :
      ∀ (ω : Ω) (i : Fin n), 0 ≤ svals (maskedScaled p (Xi ω) (Mask ω)) i :=
    fun _ _ => Real.sqrt_nonneg _
  have hnegcount : ∀ (ω : Ω) (x : ℝ), 0 ≤ x →
      (Finset.univ.filter
        (fun i : Fin n => -svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card = n := by
    intro ω x hx
    have hmem : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        -svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x := by
      intro i _
      linarith [hsvals_nonneg ω i]
    rw [Finset.filter_true_of_mem hmem, Finset.card_univ, Fintype.card_fin]
  have hcount_le : ∀ (ω : Ω) (x : ℝ),
      (Finset.univ.filter
        (fun i : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card ≤ n := by
    intro ω x
    simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
      (p := fun i : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x))
  have hsym_count : ∀ (ω : Ω) (x : ℝ), 0 ≤ x →
      (2 * (n : ℝ))⁻¹ *
          (((Finset.univ.filter
              (fun i : Fin n =>
                svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ) +
            ((Finset.univ.filter
              (fun i : Fin n =>
                -svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ))
        = ((1 : ℝ) +
            (n : ℝ)⁻¹ *
              ((Finset.univ.filter
                (fun i : Fin n =>
                  svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ)) / 2 := by
    intro ω x hx
    rw [hnegcount ω x hx]
    have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    field_simp
    ring
  have hlog_ge_one : 1 ≤ Real.log (m : ℝ) := by
    have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3m
    rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (m : ℝ))]
    linarith [Real.exp_one_lt_three]

  have hFA_nonneg : ∀ (ω : Ω) (x : ℝ),
      0 ≤ (n : ℝ)⁻¹ *
        ((Finset.univ.filter
          (fun i : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ) := by
    intro ω x
    exact mul_nonneg (le_of_lt (inv_pos.mpr hnpos)) (by positivity)
  have hFA_le_one : ∀ (ω : Ω) (x : ℝ),
      (n : ℝ)⁻¹ *
        ((Finset.univ.filter
          (fun i : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ) ≤ 1 := by
    intro ω x
    have hc : ((Finset.univ.filter
        (fun i : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hcount_le ω x
    have hinv : 0 ≤ (n : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hnpos)
    calc (n : ℝ)⁻¹ *
          ((Finset.univ.filter
            (fun i : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ)
        ≤ (n : ℝ)⁻¹ * (n : ℝ) := mul_le_mul_of_nonneg_left hc hinv
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hnpos)
  have hFA_eq : ∀ (ω : Ω) (x : ℝ), 0 ≤ x →
      (n : ℝ)⁻¹ *
          ((Finset.univ.filter
            (fun i : Fin n => svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ)
        = 2 * ((2 * (n : ℝ))⁻¹ *
              (((Finset.univ.filter
                  (fun i : Fin n =>
                    svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ) +
                ((Finset.univ.filter
                  (fun i : Fin n =>
                    -svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ))) - 1 := by
    intro ω x hx
    rw [hsym_count ω x hx]
    ring
  have hm_repos : (0 : ℝ) < (m : ℝ) := by
    have h : (0 : ℕ) < m := by omega
    exact_mod_cast h
  have hρpos : (0 : ℝ) < (n : ℝ) / (m : ℝ) := div_pos hnpos hm_repos
  obtain ⟨hmass, _, _, _, _, _, _⟩ :=
    hMPall ((n : ℝ) / (m : ℝ)) hrho_lo hrho_hi
  have hSymMP :
      (∫ u in Set.Iic (x : ℝ),
          (rootedMPDensity ((n : ℝ) / (m : ℝ)) u +
            rootedMPDensity ((n : ℝ) / (m : ℝ)) (-u)) / 2)
        = (1 + (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..(x : ℝ),
              rootedMPDensity ((n : ℝ) / (m : ℝ)) u)) / 2 :=
    statopia_math_node_1589508588_b622d3e8 ((n : ℝ) / (m : ℝ)) (x : ℝ) hρpos hrho_hi x.2 hmass
  obtain ⟨F1, hF1⟩ : ∃ F1 : Ω → ℝ, ∀ ω : Ω, F1 ω =
      ((Finset.univ.filter (fun i : Fin n =>
        svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ (x : ℝ))).card : ℝ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : Ω → ℝ, ∀ ω : Ω, F2 ω =
      ((Finset.univ.filter (fun i : Fin n =>
        -svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ (x : ℝ))).card : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hStep1 :
      Integrable (fun ω => (2 * (n : ℝ))⁻¹ * (F1 ω + F2 ω)) μ →
        (∫ ω, (n : ℝ)⁻¹ * F1 ω ∂μ)
          = 2 * (∫ ω, (2 * (n : ℝ))⁻¹ * (F1 ω + F2 ω) ∂μ) - 1 := by
    intro hint
    have hpt : ∀ ω : Ω, (n : ℝ)⁻¹ * F1 ω = 2 * ((2 * (n : ℝ))⁻¹ * (F1 ω + F2 ω)) - 1 := by
      intro ω
      rw [hF1 ω, hF2 ω]
      exact hFA_eq ω (x : ℝ) x.2
    simp_rw [hpt]
    rw [integral_sub (hint.const_mul 2) (integrable_const (1 : ℝ)), integral_const_mul]
    have hone : (∫ _ : Ω, (1 : ℝ) ∂μ) = 1 := by simp
    rw [hone]
  have hF2_eq : ∀ ω : Ω, F2 ω = (n : ℝ) := by
    intro ω
    rw [hF2 ω, hnegcount ω (x : ℝ) x.2]

  have hF1_meas : (∀ k : Fin n, Measurable fun ω => svals (maskedScaled p (Xi ω) (Mask ω)) k) →
      Measurable F1 := by
    intro hmeas
    have hEq : F1 = fun ω : Ω => ∑ i : Fin n,
        (if svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ (x : ℝ) then (1 : ℝ) else 0) := by
      funext ω
      rw [hF1 ω, Finset.card_filter]
      push_cast
      simp
    rw [hEq]
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      Measurable.ite (measurableSet_le (hmeas i) measurable_const) measurable_const measurable_const)
  have hF2_meas : (∀ k : Fin n, Measurable fun ω => svals (maskedScaled p (Xi ω) (Mask ω)) k) →
      Measurable F2 := by
    intro hmeas
    have hEq : F2 = fun ω : Ω => ∑ i : Fin n,
        (if -svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ (x : ℝ) then (1 : ℝ) else 0) := by
      funext ω
      rw [hF2 ω, Finset.card_filter]
      push_cast
      simp
    rw [hEq]
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      Measurable.ite (measurableSet_le (hmeas i).neg measurable_const) measurable_const
        measurable_const)
  have hInt : (∀ k : Fin n, Measurable fun ω => svals (maskedScaled p (Xi ω) (Mask ω)) k) →
      Integrable (fun ω => (2 * (n : ℝ))⁻¹ * (F1 ω + F2 ω)) μ := by
    intro hmeas
    have h1 := hF1_meas hmeas
    have h2 := hF2_meas hmeas
    have hm : Measurable fun ω : Ω => (2 * (n : ℝ))⁻¹ * (F1 ω + F2 ω) :=
      (h1.add h2).const_mul _
    refine MeasureTheory.Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hfa : (n : ℝ)⁻¹ * F1 ω = 2 * ((2 * (n : ℝ))⁻¹ * (F1 ω + F2 ω)) - 1 := by
      rw [hF1 ω, hF2 ω]
      exact hFA_eq ω (x : ℝ) x.2
    have hlo : 0 ≤ (n : ℝ)⁻¹ * F1 ω := by
      rw [hF1 ω]
      exact hFA_nonneg ω (x : ℝ)
    have hhi : (n : ℝ)⁻¹ * F1 ω ≤ 1 := by
      rw [hF1 ω]
      exact hFA_le_one ω (x : ℝ)
    have hval : (2 * (n : ℝ))⁻¹ * (F1 ω + F2 ω) = ((n : ℝ)⁻¹ * F1 ω + 1) / 2 := by
      rw [hF2_eq ω]
      field_simp
    rw [Real.norm_eq_abs, hval, abs_le]
    constructor <;> linarith
  have hsvals_meas :
      ∀ k : Fin n, Measurable fun ω => svals (maskedScaled p (Xi ω) (Mask ω)) k :=
    fun k => statopia_math_node_760072556_5eef0e48 m n
      (fun ω => maskedScaled p (Xi ω) (Mask ω))
      (fun i j => ((hMask_meas i j).mul (hXi_meas i j)).div_const _) k
  obtain ⟨nuA, hnuA_fin, hnuA_mass, hnuA_cdf⟩ :=
    statopia_math_node_2968987631_02201a7a m n hn p μ Xi Mask hsvals_meas
  have hnuA_eq : (nuA (Set.Iic (x : ℝ))).toReal
      = ∫ ω, (2 * (n : ℝ))⁻¹ * (F1 ω + F2 ω) ∂μ := by
    rw [hnuA_cdf (x : ℝ)]
    simp only [hF1, hF2]
  have hStep1' : (∫ ω, (n : ℝ)⁻¹ * F1 ω ∂μ)
      = 2 * (nuA (Set.Iic (x : ℝ))).toReal - 1 := by
    rw [hStep1 (hInt hsvals_meas)]
    rw [hnuA_eq]
  have hrewrite : (∫ ω, (n : ℝ)⁻¹ *
        ((Finset.univ.filter (fun i : Fin n =>
          svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ (x : ℝ))).card : ℝ) ∂μ)
      = ∫ ω, (n : ℝ)⁻¹ * F1 ω ∂μ := by
    simp only [hF1]
  have hMPrewrite : (∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..(x : ℝ),
        rootedMPDensity ((n : ℝ) / (m : ℝ)) u)
      = 2 * (∫ u in Set.Iic (x : ℝ),
          (rootedMPDensity ((n : ℝ) / (m : ℝ)) u +
            rootedMPDensity ((n : ℝ) / (m : ℝ)) (-u)) / 2) - 1 := by
    linarith [hSymMP]
  dsimp only
  rw [hrewrite, hStep1', hMPrewrite]
  set c0 : ℝ := 2 * Csm * (40 * a1 + 40 * Real.pi * C4 + 2) + 1 with hc0_def
  have hdiff : 2 * (nuA (Set.Iic (x : ℝ))).toReal - 1 -
      (2 * (∫ u in Set.Iic (x : ℝ),
        (rootedMPDensity ((n : ℝ) / (m : ℝ)) u +
          rootedMPDensity ((n : ℝ) / (m : ℝ)) (-u)) / 2) - 1)
      = 2 * ((nuA (Set.Iic (x : ℝ))).toReal -
        ∫ u in Set.Iic (x : ℝ),
          (rootedMPDensity ((n : ℝ) / (m : ℝ)) u +
            rootedMPDensity ((n : ℝ) / (m : ℝ)) (-u)) / 2) := by
    ring
  rw [hdiff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]


  obtain ⟨nuRho, hnuRho_fin, hnuRho_mass, hnuRho_cdf⟩ :=
    statopia_math_node_374445652_127c785c ((n : ℝ) / (m : ℝ)) hρpos hrho_hi hmass
  have hnuRho_at : (∫ u in Set.Iic (x : ℝ),
        (rootedMPDensity ((n : ℝ) / (m : ℝ)) u +
          rootedMPDensity ((n : ℝ) / (m : ℝ)) (-u)) / 2)
      = (nuRho (Set.Iic (x : ℝ))).toReal := (hnuRho_cdf (x : ℝ)).symm
  rw [hnuRho_at]
  have hnuRho_mass_eq : nuA Set.univ = nuRho Set.univ := by
    rw [hnuA_mass, hnuRho_mass]
  have hnuA_cdf_le : ∀ t : ℝ, (nuA (Set.Iic t)).toReal ≤ 1 := by
    intro t
    have h1 : nuA (Set.Iic t) ≤ nuA Set.univ := measure_mono (Set.subset_univ _)
    have h2 : nuA Set.univ ≠ ⊤ := by rw [hnuA_mass]; exact ENNReal.one_ne_top
    have h3 := ENNReal.toReal_mono h2 h1
    rwa [hnuA_mass, ENNReal.toReal_one] at h3
  have hnuRho_cdf_le : ∀ t : ℝ, (nuRho (Set.Iic t)).toReal ≤ 1 := by
    intro t
    have h1 : nuRho (Set.Iic t) ≤ nuRho Set.univ := measure_mono (Set.subset_univ _)
    have h2 : nuRho Set.univ ≠ ⊤ := by rw [hnuRho_mass]; exact ENNReal.one_ne_top
    have h3 := ENNReal.toReal_mono h2 h1
    rwa [hnuRho_mass, ENNReal.toReal_one] at h3
  have hcdf_abs_le : ∀ t : ℝ,
      |(nuA (Set.Iic t)).toReal - (nuRho (Set.Iic t)).toReal| ≤ 1 := by
    intro t
    have h1 := hnuA_cdf_le t
    have h2 := hnuRho_cdf_le t
    have h3 := ENNReal.toReal_nonneg (a := nuA (Set.Iic t))
    have h4 := ENNReal.toReal_nonneg (a := nuRho (Set.Iic t))
    rw [abs_le]
    constructor <;> linarith
  have hBddAbove : BddAbove (Set.range fun t : ℝ =>
      |(nuA (Set.Iic t)).toReal - (nuRho (Set.Iic t)).toReal|) :=
    ⟨1, by rintro _ ⟨t, rfl⟩; exact hcdf_abs_le t⟩
  have hsup_ge : |(nuA (Set.Iic (x : ℝ))).toReal - (nuRho (Set.Iic (x : ℝ))).toReal|
      ≤ sSup (Set.range fun t : ℝ =>
          |(nuA (Set.Iic t)).toReal - (nuRho (Set.Iic t)).toReal|) :=
    le_csSup hBddAbove ⟨(x : ℝ), rfl⟩


  have heta_pos : 0 < ((m : ℝ) * p) ^ (-(1 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (mul_pos hm_repos hp0) _
  have hnuA_stieltjes : ∀ z : ℂ, 0 < z.im →
      (∫ x, ((x : ℂ) - z)⁻¹ ∂nuA)
        = ∫ ω, symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z ∂μ :=
    fun z hz => statopia_math_node_1754775907_87353225 n hn μ
      (fun ω i => svals (maskedScaled p (Xi ω) (Mask ω)) i) hsvals_meas nuA hnuA_fin
      hnuA_cdf z hz
  have hres_apply : ∀ z : ℂ, 0 < z.im →
      ‖(∫ ω, symStieltjesSvals (svals (maskedScaled p (Xi ω) (Mask ω))) z ∂μ) -
          ∫ g : Matrix (Fin m) (Fin n) ℝ,
            symStieltjesSvals (svals (fun i j => (Real.sqrt (m : ℝ))⁻¹ * g i j)) z
              ∂(stdNormalMatrixMeasure m n)‖
        ≤ a1 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (z.im ^ 4)⁻¹ := by
    intro z hz
    have h := hRes m n hm hn rhoMinus h_rhoMinus_pos h_rhoMinus_le hrho_lo hrho_hi
      p hp0 hp1 Kt hKt μ Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var
      hXi_tail hMask_meas hMask_val hMask_law hMask_indep hIndep z hz
    rw [ha1_def]
    simp only [one_div]
    exact h













  have hSvBdd : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      BddAbove (Set.range fun i : Fin n => svals A i) := by
    intro A
    exact ⟨_, by rintro _ ⟨i, rfl⟩; exact statopia_math_node_3837097212_a755865c m n A i⟩
  have hvanish : ∀ ω : Ω, (⨆ i : Fin n, svals (maskedScaled p (Xi ω) (Mask ω)) i) ≤ 4 →
      ∀ i : Fin n, svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ 4 :=
    fun ω h i => le_trans (le_ciSup (hSvBdd (maskedScaled p (Xi ω) (Mask ω))) i) h
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨_, hnorm⟩ :=
    hEdge m n hm hn hnm hMe hrho_lo hrho_hi p hp0 hp1 hsparse μ Xi Mask hXi_meas
      hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val
      hMask_law hMask_indep hIndep
  have hbad : μ {ω : Ω | 4 < (⨆ i : Fin n, svals (maskedScaled p (Xi ω) (Mask ω)) i)}
      ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 2))) := by
    refine le_trans (measure_mono ?_) hnorm.2.2.2

    intro ω hω
    exact lt_of_lt_of_le hω
      (ciSup_le (fun i => statopia_math_node_3837097212_a755865c m n _ i))

  obtain ⟨hTailInt, hTailBd⟩ :=
    statopia_math_node_2592890691_3a10a58c D0 hD0 Kt hKt alpha0 h_alpha0 rhoMinus
      h_rhoMinus_pos h_rhoMinus_le m n hn hnm p hp0 hp1 hsparse hrho_lo hrho_hi μ Xi Mask
      hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean hXi_var hXi_tail hMask_meas hMask_val
      hMask_law hMask_indep hIndep hbad hvanish nuA nuRho hnuA_cdf hnuRho_cdf hmass



  have hCsm_pos : (0 : ℝ) < Csm := lt_of_lt_of_le zero_lt_one hCsm_ge

  have hmsk : ∀ g : Matrix (Fin m) (Fin n) ℝ,
      maskedScaled 1 g (fun _ _ => 1) = fun a b => (Real.sqrt (m : ℝ))⁻¹ * g a b := by
    intro g
    funext a b
    simp only [maskedScaled, mul_one, div_eq_inv_mul, mul_comm]
  have hGauss_entry : ∀ (i : Fin m) (j : Fin n),
      Measurable fun g : Matrix (Fin m) (Fin n) ℝ => (Real.sqrt (m : ℝ))⁻¹ * g i j := by
    intro i j
    exact ((measurable_pi_apply (X := fun _ : Fin n => ℝ) j).comp
      (measurable_pi_apply (X := fun _ : Fin m => Fin n → ℝ) i)).const_mul _
  have hGauss_meas : ∀ k : Fin n,
      Measurable fun g : Matrix (Fin m) (Fin n) ℝ =>
        svals (maskedScaled 1 g (fun _ _ => 1)) k := by
    intro k
    have h := statopia_math_node_760072556_5eef0e48 m n
      (fun g : Matrix (Fin m) (Fin n) ℝ => fun a b => (Real.sqrt (m : ℝ))⁻¹ * g a b)
      hGauss_entry k
    simpa only [hmsk] using h
  haveI hprobG : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    simp only [stdNormalMatrixMeasure]
    infer_instance
  obtain ⟨nuG, hnuG_fin, hnuG_mass, hnuG_cdf_raw⟩ :=
    statopia_math_node_2968987631_02201a7a m n hn 1
      (show Measure (Matrix (Fin m) (Fin n) ℝ) from stdNormalMatrixMeasure m n)
      (fun g => g) (fun _ _ _ => 1) hGauss_meas
  have hnuG_cdf : ∀ x : ℝ, (nuG (Set.Iic x)).toReal =
      ∫ g : Matrix (Fin m) (Fin n) ℝ, (2 * (n : ℝ))⁻¹ *
        (((Finset.univ.filter (fun i : Fin n =>
            svals (fun a b => (Real.sqrt (m : ℝ))⁻¹ * g a b) i ≤ x)).card : ℝ) +
          ((Finset.univ.filter (fun i : Fin n =>
            -(svals (fun a b => (Real.sqrt (m : ℝ))⁻¹ * g a b) i) ≤ x)).card : ℝ))
        ∂(show Measure (Matrix (Fin m) (Fin n) ℝ) from stdNormalMatrixMeasure m n) := by
    intro x
    rw [hnuG_cdf_raw x]
    simp only [hmsk]
  have hnuG_stieltjes : ∀ z : ℂ, 0 < z.im →
      (∫ x, ((x : ℂ) - z)⁻¹ ∂nuG) =
        ∫ g : Matrix (Fin m) (Fin n) ℝ,
          symStieltjesSvals (svals (fun a b => (Real.sqrt (m : ℝ))⁻¹ * g a b)) z
          ∂(show Measure (Matrix (Fin m) (Fin n) ℝ) from stdNormalMatrixMeasure m n) :=
    fun z hz => statopia_math_node_1754775907_87353225 n hn
      (show Measure (Matrix (Fin m) (Fin n) ℝ) from stdNormalMatrixMeasure m n)
      (fun g i => svals (fun a b => (Real.sqrt (m : ℝ))⁻¹ * g a b) i)
      (fun i => by simpa only [hmsk] using hGauss_meas i) nuG hnuG_fin hnuG_cdf z hz
  have hFnuG : ∀ x : ℝ,
      |(nuG (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|
        ≤ C4 * Real.rpow (m : ℝ) (-beta) := by
    intro x
    have h1 := hGauss m n hMG hn hnm hrho_lo hrho_hi x
    rw [hnuG_cdf x, hnuRho_cdf x]

    exact h1
  have hStieltjes_rho : ∀ z : ℂ, 0 < z.im →
      ‖(∫ x, ((x : ℂ) - z)⁻¹ ∂nuG) - (∫ x, ((x : ℂ) - z)⁻¹ ∂nuRho)‖
        ≤ (C4 * Real.rpow (m : ℝ) (-beta)) * (Real.pi / z.im) := by
    intro z hz
    haveI hGfin : IsFiniteMeasure nuG := hnuG_fin
    haveI hRfin : IsFiniteMeasure nuRho := hnuRho_fin
    exact statopia_math_node_606857656_cfd8aebb nuG nuRho (by rw [hnuG_mass, hnuRho_mass])
      (C4 * Real.rpow (m : ℝ) (-beta)) hFnuG z hz
  set eta : ℝ := ((m : ℝ) * p) ^ (-(1 : ℝ) / 10) with heta_def
  have hpt : ∀ u : ℝ,
      ‖(∫ x, ((x : ℂ) - ((u : ℂ) + (eta : ℂ) * Complex.I))⁻¹ ∂nuA)
          - (∫ x, ((x : ℂ) - ((u : ℂ) + (eta : ℂ) * Complex.I))⁻¹ ∂nuRho)‖
        ≤ a1 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (eta ^ 4)⁻¹
          + (C4 * Real.rpow (m : ℝ) (-beta)) * (Real.pi / eta) := by
    intro u
    set z : ℂ := (u : ℂ) + (eta : ℂ) * Complex.I with hzdef
    have hzim : z.im = eta := by
      rw [hzdef]
      simp
    have hz : 0 < z.im := by
      rw [hzim, heta_def]
      exact Real.rpow_pos_of_pos (mul_pos hm_repos hp0) _
    have hAG := hres_apply z hz
    rw [← hnuA_stieltjes z hz, ← hnuG_stieltjes z hz] at hAG
    have hG := hStieltjes_rho z hz
    rw [hzim] at hAG hG
    have hsplit : (∫ x, ((x : ℂ) - z)⁻¹ ∂nuA) - (∫ x, ((x : ℂ) - z)⁻¹ ∂nuRho)
        = ((∫ x, ((x : ℂ) - z)⁻¹ ∂nuA) - (∫ x, ((x : ℂ) - z)⁻¹ ∂nuG))
          + ((∫ x, ((x : ℂ) - z)⁻¹ ∂nuG) - (∫ x, ((x : ℂ) - z)⁻¹ ∂nuRho)) := by
      ring
    rw [hsplit]
    exact le_trans (norm_add_le _ _) (add_le_add hAG hG)
  have hL1 :
      (∫ u in (-20 : ℝ)..20,
          ‖(∫ x, ((x : ℂ) - ((u : ℂ) + (eta : ℂ) * Complex.I))⁻¹ ∂nuA)
            - (∫ x, ((x : ℂ) - ((u : ℂ) + (eta : ℂ) * Complex.I))⁻¹ ∂nuRho)‖)
        ≤ (a1 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (eta ^ 4)⁻¹
            + (C4 * Real.rpow (m : ℝ) (-beta)) * (Real.pi / eta)) * 40 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun u : ℝ =>
        ‖(∫ x, ((x : ℂ) - ((u : ℂ) + (eta : ℂ) * Complex.I))⁻¹ ∂nuA)
          - (∫ x, ((x : ℂ) - ((u : ℂ) + (eta : ℂ) * Complex.I))⁻¹ ∂nuRho)‖)
      (a := (-20 : ℝ)) (b := 20)
      (C := a1 * (Real.sqrt ((m : ℝ) * p))⁻¹ * (eta ^ 4)⁻¹
            + (C4 * Real.rpow (m : ℝ) (-beta)) * (Real.pi / eta))
      (by
        intro u _
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hpt u)

    rw [show |(20 : ℝ) - (-20)| = 40 by norm_num, Real.norm_eq_abs] at h
    exact le_trans (le_abs_self _) h

  have hlog_gt_one : 1 < Real.log (m : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by linarith : (0 : ℝ) < (m : ℝ))]
    have h3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3m
    linarith [Real.exp_one_lt_three]
  have hmp_gt_one : 1 < (m : ℝ) * p := by
    have hlone : 1 < (Real.log (m : ℝ)) ^ alpha0 :=
      Real.one_lt_rpow hlog_gt_one (by linarith : (0 : ℝ) < alpha0)
    exact lt_of_lt_of_le hlone hsparse

  have heta_lt_one : eta < 1 := by
    rw [heta_def]
    exact (Real.rpow_lt_one_iff_of_pos (mul_pos hm_repos hp0)).mpr
      (Or.inl ⟨hmp_gt_one, by norm_num⟩)

  have heta_ident : (Real.sqrt ((m : ℝ) * p))⁻¹ * (eta ^ 4)⁻¹ = eta := by
    have hu : 0 < (m : ℝ) * p := mul_pos hm_repos hp0
    have hs : (Real.sqrt ((m : ℝ) * p))⁻¹ = ((m : ℝ) * p) ^ (-(1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hu.le]
      congr 1
      ring
    have ht : (eta ^ 4)⁻¹ = ((m : ℝ) * p) ^ ((2 : ℝ) / 5) := by
      have h4 : (eta ^ 4)⁻¹ = (eta⁻¹) ^ 4 := (inv_pow eta 4).symm
      rw [h4, heta_def, show -(1 : ℝ) / 10 = -((1 : ℝ) / 10) by ring,
        Real.rpow_neg hu.le, inv_inv, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
      congr 1
      norm_num
    rw [hs, ht, heta_def, show -(1 : ℝ) / 10 = -((1 : ℝ) / 10) by ring,
      ← Real.rpow_add hu]
    congr 1
    norm_num
  have heta_le_sharp : eta ≤ (deltaM m) ^ ((3 : ℝ) / 2) := by
    have hLpos : 0 < Real.log (m : ℝ) := hmlog
    have hmp1 : 0 < (m : ℝ) * p := mul_pos hm_repos hp0
    have hP : 0 < (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hLpos _
    have hQ : 0 < ((m : ℝ) * p) ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hmp1 _
    have hpow_le : (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) ≤ ((m : ℝ) * p) ^ ((1 : ℝ) / 10) := by
      have hmono : (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) ≤ (Real.log (m : ℝ)) ^ (alpha0 / 10) :=
        Real.rpow_le_rpow_of_exponent_le (x := Real.log (m : ℝ)) (y := (3 : ℝ) / 2)
          (z := alpha0 / 10) hlog_ge_one (by linarith)
      have hbase : (Real.log (m : ℝ)) ^ (alpha0 / 10) ≤ ((m : ℝ) * p) ^ ((1 : ℝ) / 10) := by
        have h := Real.rpow_le_rpow (Real.rpow_nonneg hLpos.le alpha0) hsparse
          (by norm_num : (0 : ℝ) ≤ 1 / 10)
        rwa [← Real.rpow_mul hLpos.le,
          show alpha0 * ((1 : ℝ) / 10) = alpha0 / 10 by ring] at h
      exact le_trans hmono hbase
    have hkey : (((m : ℝ) * p) ^ ((1 : ℝ) / 10))⁻¹ * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) ≤ 1 := by
      have hQinv : 0 ≤ (((m : ℝ) * p) ^ ((1 : ℝ) / 10))⁻¹ := (inv_pos.mpr hQ).le
      have h := mul_le_mul_of_nonneg_left hpow_le hQinv
      have hone : (((m : ℝ) * p) ^ ((1 : ℝ) / 10))⁻¹ * ((m : ℝ) * p) ^ ((1 : ℝ) / 10) = 1 :=
        inv_mul_cancel₀ (ne_of_gt hQ)
      rwa [hone] at h
    have hstep : (((m : ℝ) * p) ^ ((1 : ℝ) / 10))⁻¹
        ≤ ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ := by
      have hPinv : 0 ≤ ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ := (inv_pos.mpr hP).le
      have hZ : (((m : ℝ) * p) ^ ((1 : ℝ) / 10))⁻¹
          = ((((m : ℝ) * p) ^ ((1 : ℝ) / 10))⁻¹ * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))
              * ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hP), mul_one]
      rw [hZ]
      simpa using mul_le_mul_of_nonneg_right hkey hPinv
    have hneg : eta = (((m : ℝ) * p) ^ ((1 : ℝ) / 10))⁻¹ := by
      rw [heta_def, show -(1 : ℝ) / 10 = -((1 : ℝ) / 10) by ring]
      exact Real.rpow_neg (le_of_lt hmp1) ((1 : ℝ) / 10)
    have hdelta : (deltaM m) ^ ((3 : ℝ) / 2) = ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ := by
      rw [deltaM]
      exact Real.inv_rpow hLpos.le ((3 : ℝ) / 2)
    rw [hneg, hdelta]
    exact hstep

  have hL1' : (∫ u in (-20 : ℝ)..20,
        ‖(∫ x, ((x : ℂ) - (u : ℂ) - (eta : ℂ) * Complex.I)⁻¹ ∂nuA)
          - (∫ x, ((x : ℂ) - (u : ℂ) - (eta : ℂ) * Complex.I)⁻¹ ∂nuRho)‖)
      ≤ (a1 * eta + (C4 * Real.rpow (m : ℝ) (-beta)) * (Real.pi / eta)) * 40 := by
    have h := hL1
    rw [mul_assoc, heta_ident] at h
    simpa only [sub_sub] using h
  haveI : IsProbabilityMeasure nuA := ⟨hnuA_mass⟩
  haveI : IsProbabilityMeasure nuRho := ⟨hnuRho_mass⟩
  have hnuRho_lipschitz :=
    ResidualSparseRepair20261106.CDFRegularity.symmetrized_rootedMP_cdf_lipschitz
      rhoMinus ((n : ℝ) / (m : ℝ)) h_rhoMinus_pos hrho_lo hrho_hi nuRho hnuRho_cdf
  have hCsm_app : sSup (Set.range fun t : ℝ =>
        |(nuA (Set.Iic t)).toReal - (nuRho (Set.Iic t)).toReal|)
      ≤ Csm * ((∫ u in (-20 : ℝ)..20,
            ‖(∫ x, ((x : ℂ) - (u : ℂ) - (eta : ℂ) * Complex.I)⁻¹ ∂nuA)
              - (∫ x, ((x : ℂ) - (u : ℂ) - (eta : ℂ) * Complex.I)⁻¹ ∂nuRho)‖)
          + eta + eta⁻¹ * (∫ x in {x : ℝ | 4 < |x|},
              |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|)) :=
    hCsm nuA nuRho hnuRho_lipschitz hTailInt eta heta_pos heta_lt_one








  have hcanc_rpow : ∀ (y : ℝ), 0 < y → ∀ (a : ℝ), y ^ a * y ^ (-a) = 1 := by
    intro y hy a
    rw [← Real.rpow_add hy, show a + -a = (0 : ℝ) by ring,
      show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_zero]
  have heta_inv_eq : eta⁻¹ = ((m : ℝ) * p) ^ ((1 : ℝ) / 10) := by
    rw [heta_def, show -(1 : ℝ) / 10 = -((1 : ℝ) / 10) by ring,
      Real.rpow_neg (le_of_lt (mul_pos hm_repos hp0)), inv_inv]
  have heta_inv_le : eta⁻¹ ≤ (m : ℝ) ^ ((1 : ℝ) / 10) := by
    rw [heta_inv_eq]
    refine Real.rpow_le_rpow (le_of_lt (mul_pos hm_repos hp0)) ?_ (by norm_num)
    have hmul : (m : ℝ) * p ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left hp1 (le_of_lt hm_repos)
    simpa using hmul
  have hL3pos : (0 : ℝ) < (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hmlog _
  have hL3ne : (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) ≠ 0 := ne_of_gt hL3pos
  have hdd_eq : Real.rpow (deltaM m) ((3 : ℝ) / 2)
      = ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [deltaM]
    exact Real.inv_rpow hmlog.le ((3 : ℝ) / 2)
  have hT1 : Real.rpow (m : ℝ) (-beta) * eta⁻¹
      ≤ Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
    have hk := hM3 (m : ℝ) (by exact_mod_cast hM3m) hm1'.le
    rw [one_mul] at hk
    have hkey : (m : ℝ) ^ (-(beta - 1 / 10))
        ≤ Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
      rw [hdd_eq]
      have hh : (m : ℝ) ^ (-(beta - 1 / 10)) ≤
          1 / ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2)) :=
        (le_div_iff₀ hL3pos).2 hk
      simpa only [one_div] using hh
    calc Real.rpow (m : ℝ) (-beta) * eta⁻¹
        ≤ Real.rpow (m : ℝ) (-beta) * (m : ℝ) ^ ((1 : ℝ) / 10) :=
          mul_le_mul_of_nonneg_left heta_inv_le (Real.rpow_nonneg hm_repos.le _)
      _ = (m : ℝ) ^ (-(beta - 1 / 10)) := by
          calc Real.rpow (m : ℝ) (-beta) * (m : ℝ) ^ ((1 : ℝ) / 10)
              = (m : ℝ) ^ (-beta + (1 : ℝ) / 10) :=
                (Real.rpow_add hm_repos (-beta) ((1 : ℝ) / 10)).symm
            _ = (m : ℝ) ^ (-(beta - 1 / 10)) := by congr 1 <;> ring
      _ ≤ Real.rpow (deltaM m) ((3 : ℝ) / 2) := hkey
  have hB4 : (C4 * Real.rpow (m : ℝ) (-beta)) * (Real.pi / eta)
      ≤ C4 * Real.pi * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
    have heq : (C4 * Real.rpow (m : ℝ) (-beta)) * (Real.pi / eta)
        = C4 * Real.pi * (Real.rpow (m : ℝ) (-beta) * eta⁻¹) := by
      rw [div_eq_mul_inv]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hT1 (mul_nonneg hC4.le Real.pi_pos.le)
  have hT2 : 2 * Csm * eta⁻¹ * (n : ℝ) ^ (-(D0 + 2) / 2)
      ≤ Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
    have hk := hM4 (m : ℝ) (by exact_mod_cast hM4m) hm1'.le
    have hR1 : rhoMinus ^ ((D0 + 2) / 2) * rhoMinus ^ (-(D0 + 2) / 2) = 1 := by
      rw [show -(D0 + 2) / 2 = -((D0 + 2) / 2) by ring]
      exact hcanc_rpow rhoMinus h_rhoMinus_pos ((D0 + 2) / 2)
    have hR2 : (m : ℝ) ^ (D0 / 2 + 9 / 10) * (m : ℝ) ^ (-(D0 / 2 + 9 / 10)) = 1 :=
      hcanc_rpow (m : ℝ) hm_repos (D0 / 2 + 9 / 10)
    have hb : 2 * Csm * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2)
        ≤ rhoMinus ^ ((D0 + 2) / 2) * (m : ℝ) ^ (D0 / 2 + 9 / 10) := by
      have hfac : 0 < rhoMinus ^ (-(D0 + 2) / 2) * (m : ℝ) ^ (-(D0 / 2 + 9 / 10)) :=
        mul_pos (Real.rpow_pos_of_pos h_rhoMinus_pos _) (Real.rpow_pos_of_pos hm_repos _)
      refine le_of_mul_le_mul_right ?_ hfac
      have hR : rhoMinus ^ ((D0 + 2) / 2) * (m : ℝ) ^ (D0 / 2 + 9 / 10)
          * (rhoMinus ^ (-(D0 + 2) / 2) * (m : ℝ) ^ (-(D0 / 2 + 9 / 10))) = 1 := by
        calc rhoMinus ^ ((D0 + 2) / 2) * (m : ℝ) ^ (D0 / 2 + 9 / 10)
              * (rhoMinus ^ (-(D0 + 2) / 2) * (m : ℝ) ^ (-(D0 / 2 + 9 / 10)))
            = (rhoMinus ^ ((D0 + 2) / 2) * rhoMinus ^ (-(D0 + 2) / 2))
              * ((m : ℝ) ^ (D0 / 2 + 9 / 10) * (m : ℝ) ^ (-(D0 / 2 + 9 / 10))) := by ring
          _ = 1 := by rw [hR1, hR2, mul_one]
      have hL : (2 * Csm * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))
            * (rhoMinus ^ (-(D0 + 2) / 2) * (m : ℝ) ^ (-(D0 / 2 + 9 / 10)))
          = 2 * Csm * rhoMinus ^ (-(D0 + 2) / 2) * (m : ℝ) ^ (-(D0 / 2 + 9 / 10))
            * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) := by ring
      rw [hR, hL]
      exact hk
    have hstep1 : 2 * Csm * eta⁻¹ * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2)
        ≤ (n : ℝ) ^ ((D0 + 2) / 2) := by
      have h1 : 2 * Csm * eta⁻¹ * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2)
          ≤ 2 * Csm * (m : ℝ) ^ ((1 : ℝ) / 10) * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left heta_inv_le (by linarith : (0 : ℝ) ≤ 2 * Csm)) hL3pos.le
      refine le_trans h1 ?_
      have h3 : 2 * Csm * (m : ℝ) ^ ((1 : ℝ) / 10) * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2)
          = (2 * Csm * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2)) * (m : ℝ) ^ ((1 : ℝ) / 10) := by
        ring
      rw [h3]
      refine le_trans (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hm_repos.le _)) ?_
      have h4 : (rhoMinus ^ ((D0 + 2) / 2) * (m : ℝ) ^ (D0 / 2 + 9 / 10))
            * (m : ℝ) ^ ((1 : ℝ) / 10)
          = rhoMinus ^ ((D0 + 2) / 2) * (m : ℝ) ^ ((D0 + 2) / 2) := by
        rw [mul_assoc, ← Real.rpow_add hm_repos,
          show D0 / 2 + 9 / 10 + 1 / 10 = (D0 + 2) / 2 by ring]
      rw [h4]
      have h5 : rhoMinus ^ ((D0 + 2) / 2) * (m : ℝ) ^ ((D0 + 2) / 2)
          = (rhoMinus * (m : ℝ)) ^ ((D0 + 2) / 2) :=
        (Real.mul_rpow h_rhoMinus_pos.le hm_repos.le).symm
      rw [h5]
      have h6 : rhoMinus * (m : ℝ) ≤ (n : ℝ) := by
        have h7 := mul_le_mul_of_nonneg_right hrho_lo hm_repos.le
        rwa [div_mul_cancel₀ (n : ℝ) (ne_of_gt hm_repos)] at h7
      exact Real.rpow_le_rpow (mul_nonneg h_rhoMinus_pos.le hm_repos.le) h6
        (by linarith : (0 : ℝ) ≤ (D0 + 2) / 2)
    have hnp : (0 : ℝ) < (n : ℝ) ^ (-(D0 + 2) / 2) := Real.rpow_pos_of_pos hnpos _
    have h2 : (n : ℝ) ^ ((D0 + 2) / 2) * (n : ℝ) ^ (-(D0 + 2) / 2) = 1 := by
      rw [show -(D0 + 2) / 2 = -((D0 + 2) / 2) by ring]
      exact hcanc_rpow (n : ℝ) hnpos ((D0 + 2) / 2)
    have h1 := mul_le_mul_of_nonneg_right hstep1 hnp.le
    rw [h2] at h1
    have h3 : ((2 * Csm * eta⁻¹ * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))
          * (n : ℝ) ^ (-(D0 + 2) / 2)) * ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹
        = 2 * Csm * eta⁻¹ * (n : ℝ) ^ (-(D0 + 2) / 2) := by
      have hz : (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2)
          * ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ = 1 := mul_inv_cancel₀ hL3ne
      calc ((2 * Csm * eta⁻¹ * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))
              * (n : ℝ) ^ (-(D0 + 2) / 2)) * ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹
          = 2 * Csm * eta⁻¹
            * ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2)
              * ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹)
            * (n : ℝ) ^ (-(D0 + 2) / 2) := by ring
        _ = 2 * Csm * eta⁻¹ * (n : ℝ) ^ (-(D0 + 2) / 2) := by rw [hz, mul_one]
    calc 2 * Csm * eta⁻¹ * (n : ℝ) ^ (-(D0 + 2) / 2)
        = ((2 * Csm * eta⁻¹ * (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))
            * (n : ℝ) ^ (-(D0 + 2) / 2)) * ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ := h3.symm
      _ ≤ 1 * ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.mpr hL3pos))
      _ = Real.rpow (deltaM m) ((3 : ℝ) / 2) := by rw [one_mul, hdd_eq]



  have hKolmogorov :
      2 * |(nuA (Set.Iic (x : ℝ))).toReal - (nuRho (Set.Iic (x : ℝ))).toReal| ≤
        c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
    obtain ⟨I1, hI1⟩ : ∃ I1 : ℝ,
        (∫ u in (-20 : ℝ)..20,
          ‖(∫ x, ((x : ℂ) - (u : ℂ) - (eta : ℂ) * Complex.I)⁻¹ ∂nuA)
            - (∫ x, ((x : ℂ) - (u : ℂ) - (eta : ℂ) * Complex.I)⁻¹ ∂nuRho)‖) = I1 :=
      ⟨_, rfl⟩
    obtain ⟨T4, hT4⟩ : ∃ T4 : ℝ,
        (∫ x in {x : ℝ | 4 < |x|},
          |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|) = T4 := ⟨_, rfl⟩
    have hA : I1 ≤ (a1 * eta + (C4 * Real.rpow (m : ℝ) (-beta)) *
        (Real.pi / eta)) * 40 := by
      rw [← hI1]
      exact hL1'
    have hB : eta⁻¹ * T4 ≤ eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2) := by
      rw [← hT4]
      exact mul_le_mul_of_nonneg_left hTailBd (le_of_lt (inv_pos.mpr heta_pos))
    have h2 : sSup (Set.range fun t : ℝ =>
          |(nuA (Set.Iic t)).toReal - (nuRho (Set.Iic t)).toReal|)
        ≤ Csm * (I1 + eta + eta⁻¹ * T4) := by
      rw [← hI1, ← hT4]

      exact hCsm_app
    have h3 : I1 + eta + eta⁻¹ * T4
        ≤ (a1 * eta + (C4 * Real.rpow (m : ℝ) (-beta)) *
            (Real.pi / eta)) * 40 + eta + eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2) :=
      add_le_add (add_le_add hA le_rfl) hB
    have h4 : 2 * (Csm * (I1 + eta + eta⁻¹ * T4))
        ≤ 2 * (Csm * ((a1 * eta + (C4 * Real.rpow (m : ℝ) (-beta)) *
            (Real.pi / eta)) * 40 + eta + eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (le_of_lt hCsm_pos))
        (by norm_num : (0 : ℝ) ≤ 2)
    have h1 : 2 * |(nuA (Set.Iic (x : ℝ))).toReal - (nuRho (Set.Iic (x : ℝ))).toReal|
        ≤ 2 * sSup (Set.range fun t : ℝ =>
            |(nuA (Set.Iic t)).toReal - (nuRho (Set.Iic t)).toReal|) :=
      mul_le_mul_of_nonneg_left hsup_ge (by norm_num : (0 : ℝ) ≤ 2)
    have hnum : 2 * (Csm * ((a1 * eta +
          (C4 * Real.rpow (m : ℝ) (-beta)) * (Real.pi / eta)) * 40 +
          eta + eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2)))
        ≤ c0 * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
      rw [hc0_def]
      have hA : a1 * eta ≤ a1 * Real.rpow (deltaM m) ((3 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left heta_le_sharp ha1_pos.le
      have hD2 : eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2)
          ≤ Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
        have h1 : (1 : ℝ) ≤ 2 * Csm := by linarith
        refine le_trans ?_ hT2
        calc eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2)
            = 1 * (eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2)) := (one_mul _).symm
          _ ≤ (2 * Csm) * (eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2)) :=
              mul_le_mul_of_nonneg_right h1
                (mul_nonneg (le_of_lt (inv_pos.mpr heta_pos)) (Real.rpow_nonneg hnpos.le _))
          _ = 2 * Csm * eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2) := by ring
      have hinner : (a1 * eta + (C4 * Real.rpow (m : ℝ) (-beta)) *
            (Real.pi / eta)) * 40 + eta + eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2)
          ≤ (40 * a1 + 40 * Real.pi * C4 + 2) * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
        have hAB : a1 * eta + (C4 * Real.rpow (m : ℝ) (-beta)) *
              (Real.pi / eta)
            ≤ a1 * Real.rpow (deltaM m) ((3 : ℝ) / 2)
              + C4 * Real.pi * Real.rpow (deltaM m) ((3 : ℝ) / 2) := add_le_add hA hB4
        have h1 : (a1 * eta + (C4 * Real.rpow (m : ℝ) (-beta)) *
              (Real.pi / eta)) * 40
            ≤ (a1 * Real.rpow (deltaM m) ((3 : ℝ) / 2)
              + C4 * Real.pi * Real.rpow (deltaM m) ((3 : ℝ) / 2)) * 40 :=
          mul_le_mul_of_nonneg_right hAB (by norm_num)
        have h2 : (a1 * eta + (C4 * Real.rpow (m : ℝ) (-beta)) *
              (Real.pi / eta)) * 40 + eta
            ≤ (a1 * Real.rpow (deltaM m) ((3 : ℝ) / 2)
              + C4 * Real.pi * Real.rpow (deltaM m) ((3 : ℝ) / 2)) * 40
              + Real.rpow (deltaM m) ((3 : ℝ) / 2) := add_le_add h1 heta_le_sharp
        have h3 : (a1 * eta + (C4 * Real.rpow (m : ℝ) (-beta)) *
              (Real.pi / eta)) * 40 + eta + eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2)
            ≤ ((a1 * Real.rpow (deltaM m) ((3 : ℝ) / 2)
              + C4 * Real.pi * Real.rpow (deltaM m) ((3 : ℝ) / 2)) * 40
              + Real.rpow (deltaM m) ((3 : ℝ) / 2)) + Real.rpow (deltaM m) ((3 : ℝ) / 2) :=
          add_le_add h2 hD2
        have heq : ((a1 * Real.rpow (deltaM m) ((3 : ℝ) / 2)
              + C4 * Real.pi * Real.rpow (deltaM m) ((3 : ℝ) / 2)) * 40
              + Real.rpow (deltaM m) ((3 : ℝ) / 2)) + Real.rpow (deltaM m) ((3 : ℝ) / 2)
            = (40 * a1 + 40 * Real.pi * C4 + 2) * Real.rpow (deltaM m) ((3 : ℝ) / 2) := by ring
        rw [heq] at h3
        exact h3
      have hstep : 2 * (Csm * ((a1 * eta + (C4 * Real.rpow (m : ℝ) (-beta)) *
            (Real.pi / eta)) * 40 + eta + eta⁻¹ * Real.rpow (n : ℝ) (-(D0 + 2) / 2)))
          ≤ 2 * (Csm * ((40 * a1 + 40 * Real.pi * C4 + 2) *
              Real.rpow (deltaM m) ((3 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hCsm_pos.le)
          (by norm_num : (0 : ℝ) ≤ 2)
      refine le_trans hstep ?_
      have heq2 : (2 * Csm * (40 * a1 + 40 * Real.pi * C4 + 2) + 1) *
            Real.rpow (deltaM m) ((3 : ℝ) / 2)
          = 2 * (Csm * ((40 * a1 + 40 * Real.pi * C4 + 2) *
              Real.rpow (deltaM m) ((3 : ℝ) / 2))) + Real.rpow (deltaM m) ((3 : ℝ) / 2) := by
        ring
      rw [heq2]
      exact le_add_of_nonneg_right hδnonneg
    exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2))
      (le_trans h4 hnum))

  exact hKolmogorov
  /- @proof-region region.target-node.session.f62f707a2e2311de end -/

end Statlib.Imported

#print axioms Statlib.Imported.sparse_cdf_comparison_of_polynomial_rate

