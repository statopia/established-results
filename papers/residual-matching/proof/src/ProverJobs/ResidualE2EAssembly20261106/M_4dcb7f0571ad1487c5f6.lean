import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_dbb958be849abd47ad79
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
noncomputable section

theorem paper_165f462a7e494b7a9c0f4fb377733656 (rho : ℝ) (hrho : 0 < rho)
    (C_Lam C_thet : ℝ) (hCLam : 1 ≤ C_Lam) (hCthet : 1 ≤ C_thet) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (alpha0 : ℝ), 15 < alpha0 → ∃ N0 : ℕ,
      ∀ (CM : ℝ), 1 ≤ CM → ∃ CCM : ℝ, 0 < CCM ∧
      ∀ (m n : ℕ), N0 ≤ m → 0 < m → 0 < n → n ≤ m →
        rho ≤ (n : ℝ) / (m : ℝ) → (n : ℝ) / (m : ℝ) ≤ 1 →
      ∀ (r : ℕ), 1 ≤ r → 12 * r ≤ n →
      ∀ (p : ℝ), 0 < p → p ≤ 1 → Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p →

      ∀ (mu0 mu1 : ℝ), mu0 ≤ mu1 →
      ∀ (U0 : Matrix (Fin m) (Fin r) ℝ) (V0 : Matrix (Fin n) (Fin r) ℝ) (sig0 : Fin r → ℝ)
        (M0 : Matrix (Fin m) (Fin n) ℝ),

        Matrix.transpose U0 * U0 = 1 → Matrix.transpose V0 * V0 = 1 →
        M0 = U0 * Matrix.diagonal sig0 * Matrix.transpose V0 →
        Antitone sig0 →
        0 < SMin sig0 →

        twoInfNorm U0 ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) →
        twoInfNorm V0 ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) →
      ∀ {Ωs : Type*} [MeasurableSpace Ωs] (mu : Measure Ωs) [IsProbabilityMeasure mu]
        (Om : Ωs → Matrix (Fin m) (Fin n) ℝ),
        (∀ (i : Fin m) (j : Fin n), Measurable fun ω => Om ω i j) →
        iIndepFun (fun (ij : Fin m × Fin n) (ω : Ωs) => Om ω ij.1 ij.2) mu →
        (∀ (i : Fin m) (j : Fin n), mu {ω | Om ω i j = 1} = ENNReal.ofReal p) →
        (∀ (i : Fin m) (j : Fin n) (ω : Ωs), Om ω i j = 0 ∨ Om ω i j = 1) →
        C * mu0 * (r : ℝ) * Real.log (m : ℝ) ≤ (n : ℝ) * p →
        (∀ (Lambda theta : ℝ), 0 ≤ Lambda → 0 ≤ theta →
          Lambda ≤ C_Lam * Real.sqrt ((m : ℝ) / p) →
          theta ≤ C_thet * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) →
          ∀ (ω : Ωs),
          MaskEvent Lambda theta p (Om ω) (tangentSpace U0 V0) →
          (∀ (M : Matrix (Fin m) (Fin n) ℝ), InLowRankClass r mu1 M →
              spectralNorm M ≤ CM * SMax sig0 →
              |p⁻¹ * frobSq (projMask (Om ω) (M - M0)) - frobSq (M - M0)|
                ≤ agMain C mu0 mu1 sig0 CM Lambda theta m n * frobSq (M - M0)) ∧
          agMain C mu0 mu1 sig0 CM Lambda theta m n ≤ agUpper CCM mu0 mu1 sig0 p m n ∧
          (npCondition CCM mu0 mu1 sig0 p m n →
            ∀ (M : Matrix (Fin m) (Fin n) ℝ), InLowRankClass r mu1 M →
              spectralNorm M ≤ CM * SMax sig0 →
              p / 2 * frobSq (M - M0) ≤ frobSq (projMask (Om ω) (M - M0)) ∧
              frobSq (projMask (Om ω) (M - M0)) ≤ 3 * p / 2 * frobSq (M - M0)))
:= by
  /- @proof-region region.root.8f6b4c1d5ce7 begin -/
  classical
  have hsqrt2 : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hCs0pos : (0 : ℝ) < 12 / (Real.sqrt 2 - 1) := by
    apply div_pos (by norm_num)
    linarith
  refine ⟨max (12 / (Real.sqrt 2 - 1)) (max C_Lam C_thet), 1,
    lt_of_lt_of_le hCs0pos (le_max_left _ _), one_pos, ?_⟩
  intro alpha0 halpha0
  refine ⟨0, ?_⟩
  intro CM hCM
  have hCMpos : (0 : ℝ) < 1 + CM := by linarith
  have hCMone : (1 : ℝ) ≤ 1 + CM := by linarith
  have hCLampos : (0 : ℝ) < C_Lam := lt_of_lt_of_le one_pos hCLam
  have hCthetpos : (0 : ℝ) < C_thet := lt_of_lt_of_le one_pos hCthet
  refine ⟨16 * (max (12 / (Real.sqrt 2 - 1)) (max C_Lam C_thet)) ^ 4 * (1 + CM) ^ 2,
    mul_pos (mul_pos (by norm_num)
      (pow_pos (lt_of_lt_of_le hCs0pos (le_max_left _ _)) 4)) (pow_pos hCMpos 2), ?_⟩
  intro m n hmN hm hn hnm hratio hratio1
  intro r hr hrn
  intro p hp hp1 hpcond
  intro mu0 mu1 hmu
  intro U0 V0 sig0 M0 hU0 hV0 hM0 hanti hsmin hlevU hlevV
  intro Ωs _ mu _ Om hmeas hindep hprob hbinary hCcond
  intro Lambda theta hLam_nn htheta_nn hLam_le htheta_le
  intro ω hmask
  set Cs : ℝ := max (12 / (Real.sqrt 2 - 1)) (max C_Lam C_thet) with hCs
  have hCspos : (0 : ℝ) < Cs := by
    rw [hCs]
    exact lt_of_lt_of_le hCs0pos (le_max_left _ _)
  have hCsone : (1 : ℝ) ≤ Cs := by
    rw [hCs]
    exact le_trans hCLam (le_trans (le_max_left _ _) (le_max_right _ _))
  have hCsge : 12 / (Real.sqrt 2 - 1) ≤ Cs := by
    rw [hCs]
    exact le_max_left _ _
  have hCsLam : C_Lam ≤ Cs := by
    rw [hCs]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCsThet : C_thet ≤ Cs := by
    rw [hCs]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrpos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hr
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
  have hm1 : 1 ≤ m := hm
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  have hnp_pos : (0 : ℝ) < (n : ℝ) * p := mul_pos hnR hp
  have hmn_pos : (0 : ℝ) < (m : ℝ) * (n : ℝ) := mul_pos hmR hnR
  have hnpne : Real.sqrt ((n : ℝ) * p) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnp_pos)
  have hmnne : Real.sqrt ((m : ℝ) * (n : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hmn_pos)
  have hbddBelow_sig : BddBelow (Set.range sig0) := by
    refine ⟨-∑ j, |sig0 j|, ?_⟩
    rintro x ⟨i, rfl⟩
    have h1 : |sig0 i| ≤ ∑ j, |sig0 j| :=
      Finset.single_le_sum (f := fun j => |sig0 j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    exact le_trans (neg_le_neg h1) (neg_abs_le _)
  have hbddAbove_sig : BddAbove (Set.range sig0) := by
    refine ⟨∑ j, |sig0 j|, ?_⟩
    rintro x ⟨i, rfl⟩
    have h1 : |sig0 i| ≤ ∑ j, |sig0 j| :=
      Finset.single_le_sum (f := fun j => |sig0 j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    exact le_trans (le_abs_self _) h1
  have hsig_ge_SMin : ∀ t : Fin r, SMin sig0 ≤ sig0 t := by
    intro t
    simpa [SMin] using ciInf_le hbddBelow_sig t
  have hsig_le_SMax : ∀ t : Fin r, sig0 t ≤ SMax sig0 := by
    intro t
    simpa [SMax] using le_ciSup hbddAbove_sig t
  have hSMax_nonneg : 0 ≤ SMax sig0 :=
    le_trans (le_of_lt hsmin)
      (le_trans (hsig_ge_SMin ⟨0, hrpos⟩) (hsig_le_SMax ⟨0, hrpos⟩))
  have hkappa_nonneg : 0 ≤ kappaOf sig0 := by
    simp only [kappaOf]
    exact div_nonneg hSMax_nonneg (le_of_lt hsmin)
  have hcol : ∀ t : Fin r, ∑ i : Fin m, U0 i t ^ 2 = 1 := by
    intro t
    have h := congrFun (congrFun hU0 t) t
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  have htwoInfU0pos : 0 < twoInfNorm U0 := by
    have hex : ∃ i : Fin m, U0 i ⟨0, hrpos⟩ ≠ 0 := by
      by_contra hc
      push_neg at hc
      have hzero : (∑ i : Fin m, U0 i ⟨0, hrpos⟩ ^ 2) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hc i]; ring
      rw [hcol ⟨0, hrpos⟩] at hzero
      exact one_ne_zero hzero
    obtain ⟨i0, hi0⟩ := hex
    have hterm : 0 < U0 i0 ⟨0, hrpos⟩ ^ 2 := by
      rcases lt_or_gt_of_ne hi0 with h | h
      · have hp := mul_pos (neg_pos.mpr h) (neg_pos.mpr h)
        simpa [pow_two] using hp
      · have hp := mul_pos h h
        simpa [pow_two] using hp
    have hrow : 0 < ∑ j : Fin r, U0 i0 j ^ 2 :=
      lt_of_lt_of_le hterm (Finset.single_le_sum (f := fun j : Fin r => U0 i0 j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ _))
    have hbdd : BddAbove (Set.range fun i : Fin m => Real.sqrt (∑ j : Fin r, U0 i j ^ 2)) := by
      refine ⟨Real.sqrt (∑ i : Fin m, ∑ j : Fin r, U0 i j ^ 2), ?_⟩
      rintro x ⟨i, rfl⟩
      exact Real.sqrt_le_sqrt (Finset.single_le_sum
        (f := fun i' : Fin m => ∑ j : Fin r, U0 i' j ^ 2)
        (fun i' _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i))
    have hle : Real.sqrt (∑ j : Fin r, U0 i0 j ^ 2) ≤ twoInfNorm U0 := by
      simpa [twoInfNorm] using le_ciSup hbdd i0
    exact lt_of_lt_of_le (Real.sqrt_pos.2 hrow) hle
  have hmu0_nonneg : 0 ≤ mu0 := by
    have h1 : 0 < Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) := lt_of_lt_of_le htwoInfU0pos hlevU
    have h2 : 0 < mu0 * (r : ℝ) / (m : ℝ) := Real.sqrt_pos.1 h1
    have h3 : mu0 * (r : ℝ) / (m : ℝ) * (m : ℝ) = mu0 * (r : ℝ) := by field_simp
    have h4 : 0 < mu0 * (r : ℝ) := by
      rw [← h3]
      exact mul_pos h2 hmR
    by_contra hneg
    rw [not_le] at hneg
    exact absurd (mul_neg_of_neg_of_pos hneg hrR) (not_lt.mpr (le_of_lt h4))
  have hmu1_nonneg : 0 ≤ mu1 := le_trans hmu0_nonneg hmu
  have hbarMu_eq : barMuOf mu0 mu1 = mu1 := by
    simp only [barMuOf]
    exact max_eq_right hmu
  have hbarMu_nonneg : 0 ≤ barMuOf mu0 mu1 := by
    rw [hbarMu_eq]
    exact hmu1_nonneg
  have hmu0_le_barMu : mu0 ≤ barMuOf mu0 mu1 := by
    simp only [barMuOf]
    exact le_max_left _ _
  
  
  clear hmeas hindep hprob hCcond hratio hratio1 hmN hpcond halpha0 alpha0
  set K : ℝ := 16 * Cs ^ 4 * (1 + CM) ^ 2 with hK
  set S : ℝ := barMuOf mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p) with hS
  set T : ℝ := barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((n : ℝ) * p) with hT
  have hKpos : (0 : ℝ) < K := by
    rw [hK]
    exact mul_pos (mul_pos (by norm_num) (pow_pos hCspos 4)) (pow_pos hCMpos 2)
  have hKsqrt : Real.sqrt K = 4 * Cs ^ 2 * (1 + CM) := by
    rw [hK]
    have hnn : (0 : ℝ) ≤ 4 * Cs ^ 2 * (1 + CM) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Cs)) (le_of_lt hCMpos)
    have hsq : 16 * Cs ^ 4 * (1 + CM) ^ 2 = (4 * Cs ^ 2 * (1 + CM)) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq hnn]
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact div_nonneg (mul_nonneg (mul_nonneg hbarMu_nonneg (le_of_lt hrR)) hlog)
      (le_of_lt hnp_pos)
  have hTnn : 0 ≤ T := by
    rw [hT]
    exact div_nonneg (mul_nonneg hbarMu_nonneg (le_of_lt hrR)) (Real.sqrt_nonneg _)
  have hbase : Real.sqrt ((m : ℝ) / p) * Real.sqrt ((n : ℝ) * p) =
      Real.sqrt ((m : ℝ) * (n : ℝ)) := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hmR hp))]
    congr 1
    field_simp
  have hsa : Real.sqrt ((m : ℝ) / p) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (div_pos hmR hp))
  have hdivsqrt : Real.sqrt ((m : ℝ) / p) / Real.sqrt ((m : ℝ) * (n : ℝ)) =
      1 / Real.sqrt ((n : ℝ) * p) := by
    rw [← hbase]
    field_simp
  have htheta_bound : theta ≤ C_thet * Real.sqrt S := by
    rw [hS]
    refine le_trans htheta_le (mul_le_mul_of_nonneg_left ?_ (le_of_lt hCthetpos))
    apply Real.sqrt_le_sqrt
    have h1 : mu0 * (r : ℝ) * Real.log (m : ℝ) ≤
        barMuOf mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmu0_le_barMu (le_of_lt hrR)) hlog
    have hinv : (0 : ℝ) ≤ ((n : ℝ) * p)⁻¹ := le_of_lt (inv_pos.mpr hnp_pos)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 hinv
  have hLam_bound : Lambda * (barMuOf mu0 mu1 * (r : ℝ)) / Real.sqrt ((m : ℝ) * (n : ℝ)) ≤
      C_Lam * T := by
    rw [hT]
    have hpos : (0 : ℝ) ≤ barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) :=
      div_nonneg (mul_nonneg hbarMu_nonneg (le_of_lt hrR)) (Real.sqrt_nonneg _)
    have h1 : Lambda * (barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) ≤
        (C_Lam * Real.sqrt ((m : ℝ) / p)) *
          (barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hLam_le hpos
    calc Lambda * (barMuOf mu0 mu1 * (r : ℝ)) / Real.sqrt ((m : ℝ) * (n : ℝ))
        = Lambda * (barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) := by ring
      _ ≤ (C_Lam * Real.sqrt ((m : ℝ) / p)) *
            (barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) := h1
      _ = C_Lam * ((barMuOf mu0 mu1 * (r : ℝ)) *
            (Real.sqrt ((m : ℝ) / p) / Real.sqrt ((m : ℝ) * (n : ℝ)))) := by ring
      _ = C_Lam * ((barMuOf mu0 mu1 * (r : ℝ)) * (1 / Real.sqrt ((n : ℝ) * p))) := by
            rw [hdivsqrt]
      _ = C_Lam * (barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((n : ℝ) * p)) := by ring
  have hagMain : agMain Cs mu0 mu1 sig0 CM Lambda theta m n =
      Cs * kappaOf sig0 *
        (theta + (1 + CM) * Lambda *
          (barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)))) := by
    simp only [agMain]
    ring
  have hBnn : 0 ≤ theta + (1 + CM) * Lambda *
        (barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) :=
    add_nonneg htheta_nn
      (mul_nonneg (mul_nonneg (le_of_lt hCMpos) hLam_nn)
        (div_nonneg (mul_nonneg hbarMu_nonneg (le_of_lt hrR)) (Real.sqrt_nonneg _)))
  have hbracket_step : theta + (1 + CM) * Lambda *
        (barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)))
      ≤ C_thet * Real.sqrt S + (1 + CM) * C_Lam * T := by
    have hL : (1 + CM) * Lambda *
          (barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)))
        = (1 + CM) *
          (Lambda * (barMuOf mu0 mu1 * (r : ℝ)) / Real.sqrt ((m : ℝ) * (n : ℝ))) := by ring
    have hR : (1 + CM) * C_Lam * T = (1 + CM) * (C_Lam * T) := by ring
    rw [hL, hR]
    exact add_le_add htheta_bound (mul_le_mul_of_nonneg_left hLam_bound (le_of_lt hCMpos))
  have hagSharp : agMain Cs mu0 mu1 sig0 CM Lambda theta m n ≤
      Cs * kappaOf sig0 * (C_thet * Real.sqrt S + (1 + CM) * C_Lam * T) := by
    rw [hagMain]
    exact mul_le_mul_of_nonneg_left hbracket_step (mul_nonneg (le_of_lt hCspos) hkappa_nonneg)
  have hrn' : r ≤ n := by omega
  have hrm : r ≤ m := by omega
  have hcl1 : ∀ (M : Matrix (Fin m) (Fin n) ℝ), InLowRankClass r mu1 M →
      spectralNorm M ≤ CM * SMax sig0 →
      |p⁻¹ * frobSq (projMask (Om ω) (M - M0)) - frobSq (M - M0)| ≤
        agMain Cs mu0 mu1 sig0 CM Lambda theta m n * frobSq (M - M0) := by
    intro M hM hspec
    obtain ⟨X0, X, Y0, Y, hX0, hY0, hX0Y0, hXY, hspecX0, hspecY0, hrowX0, hrowY0,
      hrowX, hrowY, hdist⟩ :=
      statopia_math_node_3691428624_182dbd31 m n r U0 V0 sig0 mu0 mu1 CM M
        hm hn hr hCM hmu hmu0_nonneg hU0 hV0 hanti hsmin hlevU hlevV hM hspec
    have hnode := statopia_math_node_3113149870_e08e141b m n r hm hn hr hrn' hnm hrm
      p hp (Om ω) (fun i j => hbinary i j ω) U0 V0 hU0 hV0 sig0 hanti hsmin Lambda theta
      hLam_nn htheta_nn hmask (barMuOf mu0 mu1) hbarMu_nonneg CM hCM X0 X Y0 Y
      hX0 hY0 hX0Y0 hspecX0 hspecY0 hrowX0 hrowY0 hrowX hrowY hdist
    rw [hXY, hX0Y0, ← hM0] at hnode
    have hbr : Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) *
        Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) =
        barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)) := by
      have hb : 0 ≤ barMuOf mu0 mu1 * (r : ℝ) := mul_nonneg hbarMu_nonneg (le_of_lt hrR)
      have hA : 0 ≤ barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ) := div_nonneg hb (le_of_lt hmR)
      have hB : 0 ≤ barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ) := div_nonneg hb (le_of_lt hnR)
      have hprod : Real.sqrt ((barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) *
            (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ))) * Real.sqrt ((m : ℝ) * (n : ℝ)) =
          barMuOf mu0 mu1 * (r : ℝ) := by
        rw [← Real.sqrt_mul (mul_nonneg hA hB)]
        have harg : (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) *
            (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) * ((m : ℝ) * (n : ℝ)) =
            (barMuOf mu0 mu1 * (r : ℝ)) ^ 2 := by
          field_simp
        rw [harg, Real.sqrt_sq hb]
      rw [← Real.sqrt_mul hA]
      exact (eq_div_iff (ne_of_gt (Real.sqrt_pos.2 hmn_pos))).2 hprod
    have hbrk : theta + (1 + CM) * Lambda *
          Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) *
          Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ))
        = theta + (1 + CM) * Lambda *
          (barMuOf mu0 mu1 * (r : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) := by
      have h1 : (1 + CM) * Lambda * Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) *
          Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ)) =
          (1 + CM) * Lambda * (Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (m : ℝ)) *
            Real.sqrt (barMuOf mu0 mu1 * (r : ℝ) / (n : ℝ))) := by ring
      rw [h1, hbr]
    refine le_trans hnode ?_
    rw [hbrk, hagMain]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsge hkappa_nonneg) hBnn)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  refine ⟨hcl1, ?_, ?_⟩
  · have hCs2one : (1 : ℝ) ≤ Cs ^ 2 := by
      have h := mul_le_mul hCsone hCsone (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hCspos)
      simpa [pow_two] using h
    have hprod1 : (1 : ℝ) ≤ Cs ^ 2 * (1 + CM) := by
      have h := mul_le_mul hCs2one hCMone (by norm_num : (0 : ℝ) ≤ 1)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) hCs2one)
      simpa using h
    have hbig : (1 : ℝ) ≤ 16 * Cs ^ 2 * (1 + CM) := by
      have h := mul_le_mul (by norm_num : (1 : ℝ) ≤ 16) hprod1 (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (0 : ℝ) ≤ 16)
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 16 * (Cs ^ 2 * (1 + CM)) := h
        _ = 16 * Cs ^ 2 * (1 + CM) := by ring
    have hCssq : Cs ^ 2 * (1 + CM) ≤ K := by
      rw [hK]
      have hsplit : Cs ^ 2 * (1 + CM) * (16 * Cs ^ 2 * (1 + CM)) =
          16 * Cs ^ 4 * (1 + CM) ^ 2 := by ring
      calc Cs ^ 2 * (1 + CM) = Cs ^ 2 * (1 + CM) * 1 := by ring
        _ ≤ Cs ^ 2 * (1 + CM) * (16 * Cs ^ 2 * (1 + CM)) :=
            mul_le_mul_of_nonneg_left hbig (mul_nonneg (sq_nonneg Cs) (le_of_lt hCMpos))
        _ = 16 * Cs ^ 4 * (1 + CM) ^ 2 := hsplit
    have hCCM_theta : Cs * C_thet ≤ K := by
      refine le_trans ?_ hCssq
      calc Cs * C_thet ≤ Cs * Cs := mul_le_mul_of_nonneg_left hCsThet (le_of_lt hCspos)
        _ = Cs ^ 2 := by ring
        _ ≤ Cs ^ 2 * (1 + CM) := by
            have h := mul_le_mul_of_nonneg_left hCMone (sq_nonneg Cs)
            simpa using h
    have hCCM_Lam : Cs * (1 + CM) * C_Lam ≤ K := by
      refine le_trans ?_ hCssq
      calc Cs * (1 + CM) * C_Lam ≤ Cs * (1 + CM) * Cs :=
            mul_le_mul_of_nonneg_left hCsLam (mul_nonneg (le_of_lt hCspos) (le_of_lt hCMpos))
        _ = Cs ^ 2 * (1 + CM) := by ring
    have hkey : Cs * kappaOf sig0 * (C_thet * Real.sqrt S + (1 + CM) * C_Lam * T)
        = (Cs * C_thet) * (kappaOf sig0 * Real.sqrt S) +
          (Cs * (1 + CM) * C_Lam) * (kappaOf sig0 * T) := by ring
    have hstep : Cs * kappaOf sig0 * (C_thet * Real.sqrt S + (1 + CM) * C_Lam * T)
        ≤ K * (kappaOf sig0 * Real.sqrt S) + K * (kappaOf sig0 * T) := by
      rw [hkey]
      exact add_le_add
        (mul_le_mul_of_nonneg_right hCCM_theta (mul_nonneg hkappa_nonneg (Real.sqrt_nonneg S)))
        (mul_le_mul_of_nonneg_right hCCM_Lam (mul_nonneg hkappa_nonneg hTnn))
    refine le_trans hagSharp (le_trans hstep (le_of_eq ?_))
    simp only [agUpper]
    rw [← hS, ← hT]
    ring
  
  
  · intro hnp M hM hspec
    have hnp0 : K * kappaOf sig0 ^ 2 *
        (barMuOf mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + barMuOf mu0 mu1 ^ 2 * (r : ℝ) ^ 2) ≤
        (n : ℝ) * p := hnp
    have hPPnn : (0 : ℝ) ≤ barMuOf mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) :=
      mul_nonneg (mul_nonneg hbarMu_nonneg (le_of_lt hrR)) hlog
    have hGGnn : (0 : ℝ) ≤ barMuOf mu0 mu1 ^ 2 * (r : ℝ) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsplitP : K * kappaOf sig0 ^ 2 *
        (barMuOf mu0 mu1 * (r : ℝ) * Real.log (m : ℝ) + barMuOf mu0 mu1 ^ 2 * (r : ℝ) ^ 2)
        = K * kappaOf sig0 ^ 2 * (barMuOf mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)) +
          K * kappaOf sig0 ^ 2 * (barMuOf mu0 mu1 ^ 2 * (r : ℝ) ^ 2) := by ring
    have hk1 : K * kappaOf sig0 ^ 2 * (barMuOf mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)) ≤
        (n : ℝ) * p := by
      rw [hsplitP] at hnp0
      exact le_trans (le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (le_of_lt hKpos) (sq_nonneg _)) hGGnn)) hnp0
    have hk2 : K * kappaOf sig0 ^ 2 * (barMuOf mu0 mu1 ^ 2 * (r : ℝ) ^ 2) ≤ (n : ℝ) * p := by
      rw [hsplitP] at hnp0
      exact le_trans (le_add_of_nonneg_left
        (mul_nonneg (mul_nonneg (le_of_lt hKpos) (sq_nonneg _)) hPPnn)) hnp0
    have hden : (0 : ℝ) < K * ((n : ℝ) * p) := mul_pos hKpos hnp_pos
    have harg1 : kappaOf sig0 ^ 2 * S ≤ 1 / K := by
      have hnum : (0 : ℝ) ≤ (n : ℝ) * p -
          K * kappaOf sig0 ^ 2 * (barMuOf mu0 mu1 * (r : ℝ) * Real.log (m : ℝ)) :=
        sub_nonneg.mpr hk1
      have hEq : 1 / K - kappaOf sig0 ^ 2 * S =
          ((n : ℝ) * p -
            K * kappaOf sig0 ^ 2 * (barMuOf mu0 mu1 * (r : ℝ) * Real.log (m : ℝ))) /
            (K * ((n : ℝ) * p)) := by
        rw [hS]
        field_simp
      have hdnn : (0 : ℝ) ≤ ((n : ℝ) * p -
          K * kappaOf sig0 ^ 2 * (barMuOf mu0 mu1 * (r : ℝ) * Real.log (m : ℝ))) /
            (K * ((n : ℝ) * p)) := div_nonneg hnum (le_of_lt hden)
      have hzero : (0 : ℝ) ≤ 1 / K - kappaOf sig0 ^ 2 * S := by
        rw [hEq]
        exact hdnn
      exact sub_nonneg.mp hzero
    have hTsq : T ^ 2 = barMuOf mu0 mu1 ^ 2 * (r : ℝ) ^ 2 / ((n : ℝ) * p) := by
      rw [hT, div_pow, Real.sq_sqrt (le_of_lt hnp_pos)]
      ring
    have harg2 : kappaOf sig0 ^ 2 * T ^ 2 ≤ 1 / K := by
      have hnum : (0 : ℝ) ≤ (n : ℝ) * p -
          K * kappaOf sig0 ^ 2 * (barMuOf mu0 mu1 ^ 2 * (r : ℝ) ^ 2) :=
        sub_nonneg.mpr hk2
      have hEq : 1 / K - kappaOf sig0 ^ 2 * T ^ 2 =
          ((n : ℝ) * p - K * kappaOf sig0 ^ 2 * (barMuOf mu0 mu1 ^ 2 * (r : ℝ) ^ 2)) /
            (K * ((n : ℝ) * p)) := by
        rw [hTsq]
        field_simp
      have hdnn : (0 : ℝ) ≤ ((n : ℝ) * p -
          K * kappaOf sig0 ^ 2 * (barMuOf mu0 mu1 ^ 2 * (r : ℝ) ^ 2)) /
            (K * ((n : ℝ) * p)) := div_nonneg hnum (le_of_lt hden)
      have hzero : (0 : ℝ) ≤ 1 / K - kappaOf sig0 ^ 2 * T ^ 2 := by
        rw [hEq]
        exact hdnn
      exact sub_nonneg.mp hzero
    have hone_divK : 1 / Real.sqrt K = Real.sqrt (1 / K) := by
      have hKne : K ≠ 0 := ne_of_gt hKpos
      have hinv : (1 / K) * K = 1 := by field_simp
      have hprod : Real.sqrt (1 / K) * Real.sqrt K = 1 := by
        rw [← Real.sqrt_mul (le_of_lt (div_pos one_pos hKpos)), hinv, Real.sqrt_one]
      calc 1 / Real.sqrt K = 1 * (Real.sqrt K)⁻¹ := by ring
        _ = (Real.sqrt (1 / K) * Real.sqrt K) * (Real.sqrt K)⁻¹ := by rw [hprod]
        _ = Real.sqrt (1 / K) := by
            rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hKpos)), mul_one]
    have hA1eq : kappaOf sig0 * Real.sqrt S = Real.sqrt (kappaOf sig0 ^ 2 * S) := by
      rw [Real.sqrt_mul (sq_nonneg (kappaOf sig0)), Real.sqrt_sq hkappa_nonneg]
    have hA2eq : kappaOf sig0 * T = Real.sqrt (kappaOf sig0 ^ 2 * T ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg (kappaOf sig0)), Real.sqrt_sq hkappa_nonneg,
        Real.sqrt_sq hTnn]
    have hb1 : kappaOf sig0 * Real.sqrt S ≤ 1 / Real.sqrt K := by
      calc kappaOf sig0 * Real.sqrt S = Real.sqrt (kappaOf sig0 ^ 2 * S) := hA1eq
        _ ≤ Real.sqrt (1 / K) := Real.sqrt_le_sqrt harg1
        _ = 1 / Real.sqrt K := hone_divK.symm
    have hb2 : kappaOf sig0 * T ≤ 1 / Real.sqrt K := by
      calc kappaOf sig0 * T = Real.sqrt (kappaOf sig0 ^ 2 * T ^ 2) := hA2eq
        _ ≤ Real.sqrt (1 / K) := Real.sqrt_le_sqrt harg2
        _ = 1 / Real.sqrt K := hone_divK.symm
    have hag12 : agMain Cs mu0 mu1 sig0 CM Lambda theta m n ≤ 1 / 2 := by
      have hsum : Cs * kappaOf sig0 * (C_thet * Real.sqrt S + (1 + CM) * C_Lam * T) ≤
          Cs * ((C_thet + (1 + CM) * C_Lam) * (1 / Real.sqrt K)) := by
        have h1 : Cs * (C_thet * (kappaOf sig0 * Real.sqrt S)) ≤
            Cs * (C_thet * (1 / Real.sqrt K)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hb1 (le_of_lt hCthetpos)) (le_of_lt hCspos)
        have h2 : Cs * ((1 + CM) * C_Lam * (kappaOf sig0 * T)) ≤
            Cs * ((1 + CM) * C_Lam * (1 / Real.sqrt K)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hb2 (mul_nonneg (le_of_lt hCMpos) (le_of_lt hCLampos)))
            (le_of_lt hCspos)
        calc Cs * kappaOf sig0 * (C_thet * Real.sqrt S + (1 + CM) * C_Lam * T)
            = Cs * (C_thet * (kappaOf sig0 * Real.sqrt S)) +
              Cs * ((1 + CM) * C_Lam * (kappaOf sig0 * T)) := by ring
          _ ≤ Cs * (C_thet * (1 / Real.sqrt K)) +
              Cs * ((1 + CM) * C_Lam * (1 / Real.sqrt K)) := add_le_add h1 h2
          _ = Cs * ((C_thet + (1 + CM) * C_Lam) * (1 / Real.sqrt K)) := by ring
      refine le_trans hagSharp (le_trans hsum ?_)
      rw [hKsqrt]
      have hb : C_thet + (1 + CM) * C_Lam ≤ Cs + (1 + CM) * Cs :=
        add_le_add hCsThet (mul_le_mul_of_nonneg_left hCsLam (le_of_lt hCMpos))
      have hpos4 : (0 : ℝ) < 4 * Cs ^ 2 * (1 + CM) :=
        mul_pos (mul_pos (by norm_num) (pow_pos hCspos 2)) hCMpos
      have hstep : Cs * ((C_thet + (1 + CM) * C_Lam) * (1 / (4 * Cs ^ 2 * (1 + CM)))) ≤
          Cs * ((Cs + (1 + CM) * Cs) * (1 / (4 * Cs ^ 2 * (1 + CM)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (le_of_lt (div_pos one_pos hpos4)))
          (le_of_lt hCspos)
      have heq : Cs * ((Cs + (1 + CM) * Cs) * (1 / (4 * Cs ^ 2 * (1 + CM)))) =
          (2 + CM) / (4 * (1 + CM)) := by
        field_simp
        ring
      have hle : (2 + CM) / (4 * (1 + CM)) ≤ 1 / 2 := by
        have hEq : 1 / 2 - (2 + CM) / (4 * (1 + CM)) = CM / (4 * (1 + CM)) := by
          field_simp
          ring
        have hnn2 : (0 : ℝ) ≤ CM / (4 * (1 + CM)) :=
          div_nonneg (le_trans zero_le_one hCM) (mul_nonneg (by norm_num) (le_of_lt hCMpos))
        rw [← sub_nonneg]
        rw [hEq]
        exact hnn2
      calc Cs * ((C_thet + (1 + CM) * C_Lam) * (1 / (4 * Cs ^ 2 * (1 + CM))))
          ≤ Cs * ((Cs + (1 + CM) * Cs) * (1 / (4 * Cs ^ 2 * (1 + CM)))) := hstep
        _ = (2 + CM) / (4 * (1 + CM)) := heq
        _ ≤ 1 / 2 := hle
    have hbound := hcl1 M hM hspec
    have hf2nn : 0 ≤ frobSq (M - M0) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hhalf : |p⁻¹ * frobSq (projMask (Om ω) (M - M0)) - frobSq (M - M0)| ≤
        1 / 2 * frobSq (M - M0) :=
      le_trans hbound (mul_le_mul_of_nonneg_right hag12 hf2nn)
    have hpne : p ≠ 0 := ne_of_gt hp
    have hcancel : ∀ x : ℝ, p * (p⁻¹ * x) = x := by
      intro x
      field_simp
    have hsplit := abs_le.mp hhalf
    constructor
    · have hlow : 1 / 2 * frobSq (M - M0) ≤ p⁻¹ * frobSq (projMask (Om ω) (M - M0)) := by
        have h := add_le_add_right hsplit.1 (frobSq (M - M0))
        have e1 : frobSq (M - M0) + -(1 / 2 * frobSq (M - M0)) =
            1 / 2 * frobSq (M - M0) := by ring
        have e2 : frobSq (M - M0) + (p⁻¹ * frobSq (projMask (Om ω) (M - M0)) -
            frobSq (M - M0)) = p⁻¹ * frobSq (projMask (Om ω) (M - M0)) := by ring
        rw [e1, e2] at h
        exact h
      have h1 : p * (1 / 2 * frobSq (M - M0)) ≤
          p * (p⁻¹ * frobSq (projMask (Om ω) (M - M0))) :=
        mul_le_mul_of_nonneg_left hlow (le_of_lt hp)
      have h2 : p * (p⁻¹ * frobSq (projMask (Om ω) (M - M0))) =
          frobSq (projMask (Om ω) (M - M0)) := hcancel _
      calc p / 2 * frobSq (M - M0) = p * (1 / 2 * frobSq (M - M0)) := by ring
        _ ≤ p * (p⁻¹ * frobSq (projMask (Om ω) (M - M0))) := h1
        _ = frobSq (projMask (Om ω) (M - M0)) := h2
    · have hhigh : p⁻¹ * frobSq (projMask (Om ω) (M - M0)) ≤ 3 / 2 * frobSq (M - M0) := by
        have h := add_le_add_right hsplit.2 (frobSq (M - M0))
        have e1 : frobSq (M - M0) + (p⁻¹ * frobSq (projMask (Om ω) (M - M0)) -
            frobSq (M - M0)) = p⁻¹ * frobSq (projMask (Om ω) (M - M0)) := by ring
        have e2 : frobSq (M - M0) + 1 / 2 * frobSq (M - M0) =
            3 / 2 * frobSq (M - M0) := by ring
        rw [e1, e2] at h
        exact h
      have h1 : p * (p⁻¹ * frobSq (projMask (Om ω) (M - M0))) ≤
          p * (3 / 2 * frobSq (M - M0)) :=
        mul_le_mul_of_nonneg_left hhigh (le_of_lt hp)
      have h2 : p * (p⁻¹ * frobSq (projMask (Om ω) (M - M0))) =
          frobSq (projMask (Om ω) (M - M0)) := hcancel _
      calc frobSq (projMask (Om ω) (M - M0)) =
            p * (p⁻¹ * frobSq (projMask (Om ω) (M - M0))) := h2.symm
        _ ≤ p * (3 / 2 * frobSq (M - M0)) := h1
        _ = 3 * p / 2 * frobSq (M - M0) := by ring
  /- @proof-region region.root.8f6b4c1d5ce7 end -/

end

end Statlib.Imported

-- Paper root revision 6f3305e4-7388-41f4-be61-05d1b0d5dc29

