import Lean
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

set_option autoImplicit false in
theorem statopia_math_node_341608398_1b1c7b47 : ∀ (a b : ℝ) (ha : 0 < a) (hab : a ≤ b),
    (∫ u in Real.sqrt a..Real.sqrt b, Real.sqrt ((b - u ^ 2) * (u ^ 2 - a)) / u)
      = Real.pi / 2 * ((a + b) / 2 - Real.sqrt (a * b)) := by
  /- @proof-region region.target-node.session.53b0bf7372734a6c begin -/
  intro a b ha hab
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hab0 : 0 ≤ a * b := le_of_lt (mul_pos ha hb)
  set c : ℝ := (a + b) / 2 with hc
  set s : ℝ := (b - a) / 2 with hs
  set k : ℝ := Real.sqrt (a * b) with hk
  have hksq : k ^ 2 = a * b := by rw [hk]; exact Real.sq_sqrt hab0
  have hkpos : 0 < k := by rw [hk]; positivity
  have hcsk : c ^ 2 - s ^ 2 = k ^ 2 := by rw [hksq, hc, hs]; ring
  have hcs : c - s = a := by rw [hc, hs]; ring
  have hcsp : c + s = b := by rw [hc, hs]; ring
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsc : s < c := by linarith [hcs, ha]
  have hgcont : Continuous
      (fun y : ℝ => Real.sqrt (max 0 (b - y) * max 0 (y - a)) / max y a) := by
    refine Continuous.div ?_ ?_ ?_
    · exact Real.continuous_sqrt.comp
        ((continuous_const.max (continuous_const.sub continuous_id)).mul
          (continuous_const.max (continuous_id.sub continuous_const)))
    · exact continuous_id.max continuous_const
    · intro y
      have h2 : 0 < max y a := lt_of_lt_of_le ha (le_max_right y a)
      linarith
  have hagree : (∫ y in a..b, Real.sqrt (max 0 (b - y) * max 0 (y - a)) / max y a)
      = ∫ y in a..b, Real.sqrt ((b - y) * (y - a)) / y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hm1 : max 0 (b - y) = b - y :=
      le_antisymm (max_le (by linarith) le_rfl) (le_max_right 0 (b - y))
    have hm2 : max 0 (y - a) = y - a :=
      le_antisymm (max_le (by linarith) le_rfl) (le_max_right 0 (y - a))
    have hm3 : max y a = y := le_antisymm (max_le le_rfl hy1) (le_max_left y a)
    show Real.sqrt (max 0 (b - y) * max 0 (y - a)) / max y a
      = Real.sqrt ((b - y) * (y - a)) / y
    rw [hm1, hm2, hm3]
  have hpos : ∀ θ : ℝ, 0 < c - s * Real.cos θ := by
    intro θ
    have h1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    nlinarith [h1, hs0, hcs, ha]
  have hkey : (∫ y in a..b, Real.sqrt ((b - y) * (y - a)) / y) = Real.pi * (c - k) := by
    have hpt : ∀ θ ∈ Set.uIcc (0:ℝ) Real.pi,
        (Real.sqrt (max 0 (b - (c - s * Real.cos θ)) * max 0 ((c - s * Real.cos θ) - a)) /
            max (c - s * Real.cos θ) a) * (s * Real.sin θ)
          = s ^ 2 * Real.sin θ ^ 2 / (c - s * Real.cos θ) := by
      intro θ hθ
      rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
      have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
      have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
      have hcos2 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
      have hby : b - (c - s * Real.cos θ) = s * (1 + Real.cos θ) := by
        rw [← hcsp]; ring
      have hya : (c - s * Real.cos θ) - a = s * (1 - Real.cos θ) := by
        rw [← hcs]; ring
      have hp1 : 0 ≤ s * (1 - Real.cos θ) := mul_nonneg hs0 (by linarith)
      have hp2 : 0 ≤ s * (1 + Real.cos θ) := mul_nonneg hs0 (by linarith)
      have hle : a ≤ c - s * Real.cos θ := by linarith [hya, hp1]
      have hne : c - s * Real.cos θ ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hle)
      have hm1 : max 0 (b - (c - s * Real.cos θ)) = b - (c - s * Real.cos θ) :=
        le_antisymm (max_le (by linarith) le_rfl) (le_max_right 0 _)
      have hm2 : max 0 ((c - s * Real.cos θ) - a) = (c - s * Real.cos θ) - a :=
        le_antisymm (max_le (by linarith) le_rfl) (le_max_right 0 _)
      have hm3 : max (c - s * Real.cos θ) a = c - s * Real.cos θ :=
        le_antisymm (max_le le_rfl hle) (le_max_left _ _)
      have hsq : s * (1 + Real.cos θ) * (s * (1 - Real.cos θ)) = (s * Real.sin θ) ^ 2 := by
        nlinarith [Real.sin_sq θ]
      have hsqi : Real.sqrt (s * (1 + Real.cos θ) * (s * (1 - Real.cos θ))) = s * Real.sin θ := by
        rw [hsq, Real.sqrt_sq (mul_nonneg hs0 hsin)]
      have hvalp : Real.sqrt (max 0 (b - (c - s * Real.cos θ)) *
            max 0 ((c - s * Real.cos θ) - a)) /
          max (c - s * Real.cos θ) a = s * Real.sin θ / (c - s * Real.cos θ) := by
        rw [hm1, hm2, hm3, hby, hya, hsqi]
      rw [hvalp]
      field_simp
    have hsub : (∫ y in a..b, Real.sqrt (max 0 (b - y) * max 0 (y - a)) / max y a)
        = ∫ θ in (0:ℝ)..Real.pi, s ^ 2 * Real.sin θ ^ 2 / (c - s * Real.cos θ) := by
      have hderivc : ∀ θ ∈ Set.uIcc (0:ℝ) Real.pi,
          HasDerivAt (fun θ : ℝ => c - s * Real.cos θ) (s * Real.sin θ) θ := by
        intro θ _
        have h1 : HasDerivAt (fun θ : ℝ => s * Real.cos θ) (s * -Real.sin θ) θ :=
          (Real.hasDerivAt_cos θ).const_mul s
        have h2 : HasDerivAt (fun θ : ℝ => c - s * Real.cos θ) (0 - s * -Real.sin θ) θ :=
          (hasDerivAt_const θ c).sub h1
        convert h2 using 1
        ring
      have hcontc : ContinuousOn (fun θ : ℝ => s * Real.sin θ) (Set.uIcc (0:ℝ) Real.pi) :=
        (continuous_const.mul Real.continuous_sin).continuousOn
      have hcomp := intervalIntegral.integral_comp_mul_deriv
        (f := fun θ : ℝ => c - s * Real.cos θ) (f' := fun θ : ℝ => s * Real.sin θ)
        (a := (0:ℝ)) (b := Real.pi)
        (g := fun y : ℝ => Real.sqrt (max 0 (b - y) * max 0 (y - a)) / max y a)
        hderivc hcontc hgcont
      simp only [Real.cos_zero, Real.cos_pi, mul_one, mul_neg, sub_neg_eq_add] at hcomp
      rw [hcs, hcsp] at hcomp
      rw [← hcomp]
      exact intervalIntegral.integral_congr hpt
    have hsplit : (∫ θ in (0:ℝ)..Real.pi, s ^ 2 * Real.sin θ ^ 2 / (c - s * Real.cos θ))
        = ∫ θ in (0:ℝ)..Real.pi,
            (c + s * Real.cos θ - (c ^ 2 - s ^ 2) / (c - s * Real.cos θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      have hne : c - s * Real.cos θ ≠ 0 := ne_of_gt (hpos θ)
      field_simp
      nlinarith [Real.sin_sq θ]
    have hval2 : (∫ θ in (0:ℝ)..Real.pi,
          (c + s * Real.cos θ - (c ^ 2 - s ^ 2) / (c - s * Real.cos θ)))
        = Real.pi * (c - k) := by
      have hcont : Continuous fun θ : ℝ =>
          c + s * Real.cos θ - (c ^ 2 - s ^ 2) / (c - s * Real.cos θ) :=
        (continuous_const.add (continuous_const.mul Real.continuous_cos)).sub
          (continuous_const.div (continuous_const.sub (continuous_const.mul Real.continuous_cos))
            (fun θ => ne_of_gt (hpos θ)))
      have hint : IntervalIntegrable
          (fun θ : ℝ => c + s * Real.cos θ - (c ^ 2 - s ^ 2) / (c - s * Real.cos θ))
          volume 0 Real.pi := hcont.intervalIntegrable 0 Real.pi
      have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) Real.pi,
          HasDerivAt (fun θ : ℝ => c * θ + s * Real.sin θ
              - k * (θ + 2 * Real.arctan (s * Real.sin θ / (c - s * Real.cos θ + k))))
            (c + s * Real.cos θ - (c ^ 2 - s ^ 2) / (c - s * Real.cos θ)) θ := by
        intro θ _
        have hd : c - s * Real.cos θ ≠ 0 := ne_of_gt (hpos θ)
        have hD : 0 < c - s * Real.cos θ + k := by linarith [hpos θ, hkpos]
        have hDne : c - s * Real.cos θ + k ≠ 0 := ne_of_gt hD
        have hck : 0 < c + k := by linarith [hsc, hs0, hkpos]
        have hk2 : k ^ 2 = c ^ 2 - s ^ 2 := by linarith [hcsk]
        have hS : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ
        have hone : 1 + (s * Real.sin θ / (c - s * Real.cos θ + k)) ^ 2
            = ((c - s * Real.cos θ + k) ^ 2 + s ^ 2 * Real.sin θ ^ 2)
              / (c - s * Real.cos θ + k) ^ 2 := by
          field_simp
        have hF1 : (c - s * Real.cos θ + k) ^ 2 + s ^ 2 * Real.sin θ ^ 2
            = 2 * (c + k) * (c - s * Real.cos θ) := by
          rw [hS]
          ring_nf
          rw [hk2]
          ring
        have hP : s * Real.sin θ * (s * Real.sin θ) = s ^ 2 * Real.sin θ ^ 2 := by ring
        have hA2 : s * Real.cos θ * (c - s * Real.cos θ + k) - s ^ 2 * Real.sin θ ^ 2
            = s * (Real.cos θ * (c + k) - s) := by
          rw [hS]
          ring
        have hid : (1 : ℝ) + 2 * (1 / (1 + (s * Real.sin θ / (c - s * Real.cos θ + k)) ^ 2) *
            ((s * Real.cos θ * (c - s * Real.cos θ + k) - s * Real.sin θ * (s * Real.sin θ)) /
              (c - s * Real.cos θ + k) ^ 2)) = k / (c - s * Real.cos θ) := by
          rw [hone, hF1, hP, hA2]
          field_simp
          ring_nf
          rw [hk2]
        have hnum : HasDerivAt (fun θ : ℝ => s * Real.sin θ) (s * Real.cos θ) θ :=
          (Real.hasDerivAt_sin θ).const_mul s
        have hden : HasDerivAt (fun θ : ℝ => c - s * Real.cos θ + k) (s * Real.sin θ) θ := by
          have h1 : HasDerivAt (fun θ : ℝ => s * Real.cos θ) (s * -Real.sin θ) θ :=
            (Real.hasDerivAt_cos θ).const_mul s
          have h2 : HasDerivAt (fun θ : ℝ => c - s * Real.cos θ) (0 - s * -Real.sin θ) θ :=
            (hasDerivAt_const θ c).sub h1
          have h3 : HasDerivAt (fun θ : ℝ => c - s * Real.cos θ + k) (0 - s * -Real.sin θ) θ :=
            h2.add_const k
          convert h3 using 1
          ring
        have hA := hnum.div hden hDne
        have harc := (Real.hasDerivAt_arctan
          (s * Real.sin θ / (c - s * Real.cos θ + k))).comp θ hA
        have hlin : HasDerivAt (fun θ : ℝ => c * θ) c θ := by
          simpa using (hasDerivAt_id θ).const_mul c
        have hfirst := hlin.add hnum
        have hinner := (hasDerivAt_id θ).add (harc.const_mul 2)
        have hkk := hinner.const_mul k
        have hfull : HasDerivAt (fun θ : ℝ => c * θ + s * Real.sin θ
            - k * (θ + 2 * Real.arctan (s * Real.sin θ / (c - s * Real.cos θ + k)))) _ θ :=
          hfirst.sub hkk
        convert hfull using 1
        simp only [hid]
        field_simp
        ring_nf
        rw [hk2]
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      simp [Real.sin_pi, Real.sin_zero, Real.arctan_zero]
      ring
    rw [← hagree, hsub, hsplit, hval2]
  have hcv : (∫ u in Real.sqrt a..Real.sqrt b, Real.sqrt ((b - u ^ 2) * (u ^ 2 - a)) / u)
      = (1 / 2) * ∫ y in a..b, Real.sqrt ((b - y) * (y - a)) / y := by
    have hderiv : ∀ x ∈ Set.uIcc (Real.sqrt a) (Real.sqrt b),
        HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      intro x _
      simpa using hasDerivAt_pow 2 x
    have hcont2 : ContinuousOn (fun x : ℝ => 2 * x) (Set.uIcc (Real.sqrt a) (Real.sqrt b)) :=
      (continuous_const.mul continuous_id).continuousOn
    have hcomp := intervalIntegral.integral_comp_mul_deriv
      (f := fun x : ℝ => x ^ 2) (f' := fun x : ℝ => 2 * x)
      (a := Real.sqrt a) (b := Real.sqrt b)
      (g := fun y : ℝ => Real.sqrt (max 0 (b - y) * max 0 (y - a)) / max y a)
      hderiv hcont2 hgcont
    simp only [Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hb), Function.comp_apply]
      at hcomp
    have hsb0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have hpt : ∀ u ∈ Set.uIcc (Real.sqrt a) (Real.sqrt b),
        (Real.sqrt (max 0 (b - u ^ 2) * max 0 (u ^ 2 - a)) / max (u ^ 2) a) * (2 * u)
          = 2 * (Real.sqrt ((b - u ^ 2) * (u ^ 2 - a)) / u) := by
      intro u hu
      rw [Set.uIcc_of_le (Real.sqrt_le_sqrt hab)] at hu
      obtain ⟨hu1, hu2⟩ := hu
      have hsqa : 0 < Real.sqrt a := by positivity
      have hu0 : 0 < u := lt_of_lt_of_le hsqa hu1
      have hlow : a ≤ u ^ 2 := by
        nlinarith [hu1, hsqa, hu0, Real.sq_sqrt (le_of_lt ha)]
      have hhigh : u ^ 2 ≤ b := by
        nlinarith [hu2, hu0, hsb0, Real.sq_sqrt (le_of_lt hb)]
      have hm1 : max 0 (b - u ^ 2) = b - u ^ 2 :=
        le_antisymm (max_le (by linarith) le_rfl) (le_max_right 0 (b - u ^ 2))
      have hm2 : max 0 (u ^ 2 - a) = u ^ 2 - a :=
        le_antisymm (max_le (by linarith) le_rfl) (le_max_right 0 (u ^ 2 - a))
      have hm3 : max (u ^ 2) a = u ^ 2 :=
        le_antisymm (max_le le_rfl hlow) (le_max_left (u ^ 2) a)
      rw [hm1, hm2, hm3]
      field_simp
    have hpull : (∫ u in Real.sqrt a..Real.sqrt b,
          2 * (Real.sqrt ((b - u ^ 2) * (u ^ 2 - a)) / u))
        = 2 * (∫ u in Real.sqrt a..Real.sqrt b,
            Real.sqrt ((b - u ^ 2) * (u ^ 2 - a)) / u) := by
      rw [intervalIntegral.integral_const_mul]
    have hconv : (∫ y in a..b, Real.sqrt (max 0 (b - y) * max 0 (y - a)) / max y a)
        = 2 * (∫ u in Real.sqrt a..Real.sqrt b,
            Real.sqrt ((b - u ^ 2) * (u ^ 2 - a)) / u) := by
      have hc2 : (∫ x in Real.sqrt a..Real.sqrt b,
          Real.sqrt (max 0 (b - x ^ 2) * max 0 (x ^ 2 - a)) / max (x ^ 2) a * (2 * x))
          = ∫ y in a..b, Real.sqrt (max 0 (b - y) * max 0 (y - a)) / max y a := hcomp
      rw [← hc2, intervalIntegral.integral_congr hpt, hpull]
    rw [hagree] at hconv
    linarith
  rw [hcv, hkey]
  ring
  /- @proof-region region.target-node.session.53b0bf7372734a6c end -/

end Statlib.Imported

