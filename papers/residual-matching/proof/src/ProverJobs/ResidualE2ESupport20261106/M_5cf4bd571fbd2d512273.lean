import Lean
import ProverJobs.ResidualE2ESupport20261106.M_a929832207c6a6a2d500
import ProverJobs.ResidualE2ESupport20261106.M_3fe2264c95c16f803f47
import ProverJobs.ResidualE2ESupport20261106.M_a82f7f6c36dfdb5854b8
import ProverJobs.ResidualE2ESupport20261106.M_d1ec8ba46fbba75594f7

namespace PaperProofTasks.ResidualE2ESupport20261106

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

theorem completed_mask_geometry_e2e :
    ∀ rho : ℝ, 0 < rho → ∀ alpha0 : ℝ, 15 < alpha0 →
    ∃ N0 : ℕ, ∃ Cs CL Cth c : ℝ,
      0 < Cs ∧ 0 < CL ∧ 0 < Cth ∧ 0 < c ∧
      ∀ (m n r : ℕ) (p mu0 sigma : ℝ),
        0 < m → 0 < n → N0 ≤ m → n ≤ m →
        0 ≤ p → p ≤ 1 →
        rho ≤ (n : ℝ) / (m : ℝ) → (n : ℝ) / (m : ℝ) ≤ 1 →
        0 < sigma → 12 * r ≤ n →
        (m : ℝ) * p ≥ Real.rpow (Real.log (m : ℝ)) alpha0 →
        (n : ℝ) * p ≥ Cs * mu0 * (r : ℝ) * Real.log (m : ℝ) →
        ∀ (M0 : Matrix (Fin m) (Fin n) ℝ) (U0 : Matrix (Fin m) (Fin r) ℝ)
          (V0 : Matrix (Fin n) (Fin r) ℝ) (s0 : Fin r → ℝ),
          M0.rank = r →
          U0.transpose * U0 = 1 →
          V0.transpose * V0 = 1 →
          (∀ i, 0 < s0 i) →
          M0 = U0 * Matrix.diagonal s0 * V0.transpose →
          rowNorm U0 ≤ Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) →
          rowNorm V0 ≤ Real.sqrt (mu0 * (r : ℝ) / (n : ℝ)) →
          ∀ {Ωm : Type*} [MeasurableSpace Ωm] (P : Measure Ωm) [IsProbabilityMeasure P]
            (H : Fin m → Fin n → Ωm → ℝ) (Om : Fin m → Fin n → Ωm → ℝ),
            (∀ i j, Measurable (H i j)) →
            (∀ i j, Integrable (H i j) P) →
            iIndepFun (fun (ij : Fin m × Fin n) => H ij.1 ij.2) P →
            (∀ i j, ∫ omega, H i j omega ∂P = 0) →
            (∀ i j, ∫ omega, (H i j omega) ^ 2 ∂P = sigma ^ 2) →
            (∃ KH : ℝ, 0 < KH ∧ ∀ i j (t : ℝ), 0 ≤ t →
              P {omega | t ≤ |H i j omega|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / KH)))) →
            (∀ i j, Measurable (Om i j)) →
            iIndepFun (fun (ij : Fin m × Fin n) => Om ij.1 ij.2) P →
            (∀ i j, ∀ᵐ omega ∂P, Om i j omega = 0 ∨ Om i j omega = 1) →
            (∀ i j, P {omega | Om i j omega = 1} = ENNReal.ofReal p) →
            (∀ i j, Integrable (Om i j) P) →
            (∀ i j, ∫ omega, Om i j omega ∂P = p) →
            IndepFun (fun omega (ij : Fin m × Fin n) => Om ij.1 ij.2 omega)
              (fun omega (ij : Fin m × Fin n) => H ij.1 ij.2 omega) P →
            1 - ENNReal.ofReal (c / (n : ℝ) ^ 4) ≤
              P {omega |
                
                specNorm (Wmask p (fun i j => Om i j omega))
                    ≤ CL * Real.sqrt ((m : ℝ) / p) ∧
                
                (∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
                  specNorm (Tmask p (fun i j => Om i j omega) (L * R.transpose))
                    ≤ CL * Real.sqrt ((m : ℝ) / p) * rowNorm L * rowNorm R) ∧
                
                (∀ A B : Matrix (Fin m) (Fin n) ℝ,
                  MemTangentRect U0 V0 A → MemTangentRect U0 V0 B →
                  |frobInner (Tmask p (fun i j => Om i j omega) A) B|
                    ≤ Cth * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                      * frobNorm A * frobNorm B) ∧
                
                (∀ (k l : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
                    (C1 : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
                  |frobInner (Tmask p (fun i j => Om i j omega) (A * B.transpose))
                      (C1 * D.transpose)|
                    ≤ CL * Real.sqrt ((m : ℝ) / p) * bFactor A C1 * bFactor B D)}
:= by
  intro rho hrho alpha0 halpha0
  obtain ⟨CL, hCL, N1, _, hspec_all⟩ :=
    statopia_math_node_1118446036_e2b0a0d7 rho hrho alpha0 halpha0
  obtain ⟨N2, hN2, hbern_all⟩ :=
    statopia_math_node_2830626271_c12488ac rho 12 hrho (by norm_num)
  refine ⟨N1 + N2 + 3, (12 : ℝ) ^ 2, CL, 12, 1, by norm_num, hCL, by norm_num, by norm_num, ?_⟩
  intro m n r p mu0 sigma hm hn hN0m hnm hp0 hp1 hrhonm hnm1 hsigma h12r hmp hnp
  intro M0 U0 V0 s0 hrank hU hV hs0 hM hrowU hrowV
  intro Ωm _ P _ H Om hHmeas hHint hHindep hHmean hHvar hHsubg hOmmeas hOmindep hOm01 hOmprob
    hOmint hOmmean hOmHdep
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm3 : 3 ≤ m := by omega
  have hm1 : (1 : ℝ) < (m : ℝ) := by
    have h3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    linarith
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have hrpow : 0 < Real.rpow (Real.log (m : ℝ)) alpha0 := Real.rpow_pos_of_pos hlog alpha0
  have hmp_pos : 0 < (m : ℝ) * p := lt_of_lt_of_le hrpow hmp
  have hp : 0 < p := by nlinarith [hmpos, hmp_pos]
  have hn1 : 1 ≤ n := by omega
  have hN1m : N1 ≤ m := by omega
  have hN2m : N2 ≤ m := by omega
  have hmu0r : 0 ≤ mu0 * (r : ℝ) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · subst hr0
      simp
    · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      have hU0ne : U0 ≠ 0 := by
        intro h0
        have h1 : U0.transpose * U0 = 0 := by rw [h0]; simp
        rw [h1] at hU
        have hk : (0 : ℝ) = 1 := by
          simpa using congrFun (congrFun hU (⟨0, hrpos⟩ : Fin r)) ⟨0, hrpos⟩
        exact zero_ne_one hk
      have hex : ∃ i j, U0 i j ≠ 0 := by
        obtain ⟨i, hi⟩ : ∃ i, U0 i ≠ 0 := by
          by_contra h
          push_neg at h
          exact hU0ne (funext h)
        obtain ⟨j, hj⟩ : ∃ j, U0 i j ≠ 0 := by
          by_contra h
          push_neg at h
          exact hi (funext h)
        exact ⟨i, j, hj⟩
      obtain ⟨i, j, hij⟩ := hex
      have hterm : 0 < Real.sqrt (∑ k : Fin r, (U0 i k) ^ 2) := by
        rw [Real.sqrt_pos]
        refine Finset.sum_pos' (fun k _ => by positivity) ⟨j, Finset.mem_univ j, ?_⟩
        rw [pow_two]
        exact mul_self_pos.mpr hij
      have hle : Real.sqrt (∑ k : Fin r, (U0 i k) ^ 2) ≤ rowNorm U0 :=
        le_ciSup (Finite.bddAbove_range (fun i : Fin m => Real.sqrt (∑ k : Fin r, (U0 i k) ^ 2))) i
      have hrowpos : 0 < rowNorm U0 := lt_of_lt_of_le hterm hle
      have hsqrtpos : 0 < Real.sqrt (mu0 * (r : ℝ) / (m : ℝ)) := lt_of_lt_of_le hrowpos hrowU
      have hquot : 0 < mu0 * (r : ℝ) / (m : ℝ) := Real.sqrt_pos.mp hsqrtpos
      have hmul : 0 < (mu0 * (r : ℝ) / (m : ℝ)) * (m : ℝ) := mul_pos hquot hmpos
      rw [div_mul_cancel₀ _ (ne_of_gt hmpos)] at hmul
      exact le_of_lt hmul
  have hnp' : (n : ℝ) * p ≥ (12 : ℝ) ^ 2 * mu0 * (r : ℝ) * Real.log (m : ℝ) := hnp
  let E1 : Set Ωm := {ω : Ωm | specNorm (Wmask p (fun i j => Om i j ω)) ≤ CL * Real.sqrt ((m : ℝ) / p)}
  let E2 : Set Ωm := {ω : Ωm | ∀ A B : Matrix (Fin m) (Fin n) ℝ,
      MemTangentRect U0 V0 A → MemTangentRect U0 V0 B →
      |frobInner (Tmask p (fun i j => Om i j ω) A) B| ≤
        12 * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p)) * frobNorm A * frobNorm B}
  let G : Set Ωm := {ω : Ωm |
    specNorm (Wmask p (fun i j => Om i j ω)) ≤ CL * Real.sqrt ((m : ℝ) / p) ∧
    (∀ (k : ℕ) (L : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin n) (Fin k) ℝ),
      specNorm (Tmask p (fun i j => Om i j ω) (L * R.transpose))
        ≤ CL * Real.sqrt ((m : ℝ) / p) * rowNorm L * rowNorm R) ∧
    (∀ A B : Matrix (Fin m) (Fin n) ℝ,
      MemTangentRect U0 V0 A → MemTangentRect U0 V0 B →
      |frobInner (Tmask p (fun i j => Om i j ω) A) B|
        ≤ 12 * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
          * frobNorm A * frobNorm B) ∧
    (∀ (k l : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
      (C1 : Matrix (Fin m) (Fin l) ℝ) (D : Matrix (Fin n) (Fin l) ℝ),
      |frobInner (Tmask p (fun i j => Om i j ω) (A * B.transpose)) (C1 * D.transpose)|
        ≤ CL * Real.sqrt ((m : ℝ) / p) * bFactor A C1 * bFactor B D)}
  let a : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4)
  have hspec_eq : ENNReal.ofReal ((1 / 2 : ℝ) * (n : ℝ) ^ (-4 : ℤ)) = a := by
    show ENNReal.ofReal ((1 / 2 : ℝ) * (n : ℝ) ^ (-4 : ℤ))
      = ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4)
    exact congrArg ENNReal.ofReal (by rw [div_eq_mul_inv, zpow_neg] <;> rfl)
  have hspec : 1 - a ≤ P E1 := by
    rw [← hspec_eq]
    exact hspec_all m n hn1 hnm hN1m hrhonm hnm1 p hp0 hp1 hmp P Om hOmmeas hOmindep hOm01
      hOmint hOmmean
  have hbern : 1 - a ≤ P E2 :=
    hbern_all m n r p mu0 hm hn1 hnm h12r hrhonm hnm1 hp hp1 hmu0r hN2m hnp' U0 V0 hU hV
      hrowU hrowV P Om hOmmeas hOmindep hOm01 hOmprob hOmint hOmmean
  have hLam_nonneg : (0 : ℝ) ≤ CL * Real.sqrt ((m : ℝ) / p) :=
    mul_nonneg (le_of_lt hCL) (Real.sqrt_nonneg ((m : ℝ) / p))
  have hsub : E1 ∩ E2 ⊆ G := by
    intro ω hω
    obtain ⟨h1, h2⟩ := hω
    exact ⟨h1,
      fun k L R =>
        statopia_math_node_3027807291_2d8bfe45 m n p (CL * Real.sqrt ((m : ℝ) / p))
          (fun i j => Om i j ω) hp hLam_nonneg h1 k L R,
      h2,
      fun k l A B C D =>
        statopia_math_node_3715382306_6ae91894 m n p hp (fun i j => Om i j ω)
          (CL * Real.sqrt ((m : ℝ) / p)) hLam_nonneg h1 k l A B C D⟩
  have hE1meas : MeasurableSet E1 := by
    have hAmeas : Measurable (fun ω : Ωm => Wmask p (fun i j => Om i j ω)) := by
      apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      have hbase : Measurable (fun ω : Ωm => (p⁻¹ : ℝ) * Om i j ω) :=
        measurable_const.mul (hOmmeas i j)
      exact hbase.sub_const 1
    have hcont : Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => specNorm A) := by
      let f : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ]
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
        (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap).toLinearMap
      have hcoe : Continuous ⇑f := LinearMap.continuous_of_finiteDimensional f
      exact continuous_norm.comp hcoe
    exact measurableSet_le (hcont.measurable.comp hAmeas) measurable_const
  have hcompl : P E1ᶜ ≤ a := by
    have hEq : P E1ᶜ = 1 - P E1 := by
      rw [measure_compl hE1meas (measure_ne_top P E1), measure_univ]
    rw [hEq, tsub_le_iff_left]
    have h := tsub_le_iff_left.mp hspec
    rw [add_comm] at h
    exact h
  have hsplit : P E2 ≤ P (E1 ∩ E2) + P (E2 \ E1) :=
    calc P E2 ≤ P ((E1 ∩ E2) ∪ (E2 \ E1)) :=
          measure_mono (by
            intro x hx
            by_cases h : x ∈ E1
            · exact Or.inl ⟨h, hx⟩
            · exact Or.inr ⟨hx, h⟩)
      _ ≤ P (E1 ∩ E2) + P (E2 \ E1) := measure_union_le _ _
  have hdiff : P (E2 \ E1) ≤ a :=
    le_trans (measure_mono (by intro x hx; exact hx.2)) hcompl
  have hfin : (1 : ℝ≥0∞) ≤ P (E1 ∩ E2) + (a + a) :=
    calc (1 : ℝ≥0∞) ≤ P E2 + a := tsub_le_iff_right.mp hbern
      _ ≤ (P (E1 ∩ E2) + P (E2 \ E1)) + a := add_le_add hsplit (le_refl a)
      _ ≤ (P (E1 ∩ E2) + a) + a :=
            add_le_add (add_le_add (le_refl (P (E1 ∩ E2))) hdiff) (le_refl a)
      _ = P (E1 ∩ E2) + (a + a) := add_assoc _ _ _
  have hmain : (1 : ℝ≥0∞) - (a + a) ≤ P (E1 ∩ E2) := by
    rw [tsub_le_iff_right]
    exact hfin
  have hPG : (1 : ℝ≥0∞) - (a + a) ≤ P G := le_trans hmain (measure_mono hsub)
  have haa : a + a = ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
    show ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4) + ENNReal.ofReal ((1 / 2 : ℝ) / (n : ℝ) ^ 4)
      = ENNReal.ofReal (1 / (n : ℝ) ^ 4)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    have h2 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
    rw [← add_div, h2]
  show (1 : ℝ≥0∞) - ENNReal.ofReal (1 / (n : ℝ) ^ 4) ≤ P G
  rw [← haa]
  exact hPG

end

end Statlib.Imported

-- Paper root revision 4a664b26-ec41-4554-b0df-a7811701a889

#print axioms Statlib.Imported.completed_mask_geometry_e2e

