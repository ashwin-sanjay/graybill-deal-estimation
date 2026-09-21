import GD.Module0171

set_option autoImplicit false
set_option warningAsError true











open MeasureTheory
open scoped SchwartzMap LineDeriv

namespace GD.N0227.N0545

noncomputable section

open _root_.GD.N0232.N0720.N1230
open _root_.GD.N0232.N0720.N1233

variable (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]

inductive d002018 where
  | input : d002018
  | add : d002018 → d002018 → d002018
  | neg : d002018 → d002018
  | mul : 𝓢(D, ℝ) → d002018 → d002018
  | deriv : D → d002018 → d002018

variable {D}

namespace d002018

def d002019 : _root_.GD.N0227.N0545.d002018 D → ℕ
  | .input => 0
  | .add a b => max a.d002019 b.d002019
  | .neg a => a.d002019
  | .mul _ a => a.d002019
  | .deriv _ a => a.d002019 + 1

def d002020 (error : 𝓢(D, ℝ)) : _root_.GD.N0227.N0545.d002018 D → 𝓢(D, ℝ)
  | .input => error
  | .add a b => d002020 error a + d002020 error b
  | .neg a => -d002020 error a
  | .mul c a => _root_.GD.N0232.N0720.N1230.d001994 c (d002020 error a)
  | .deriv v a => ∂_{v} (d002020 error a)

def d002021 : _root_.GD.N0227.N0545.d002018 D → 𝓢(D, ℝ) → 𝓢(D, ℝ)
  | .input, test => test
  | .add a b, test => d002021 a test + d002021 b test
  | .neg a, test => -d002021 a test
  | .mul c a, test => d002021 a (_root_.GD.N0232.N0720.N1230.d001994 test c)
  | .deriv v a, test => -d002021 a (∂_{v} test)

theorem d002022 (a : _root_.GD.N0227.N0545.d002018 D) (test : 𝓢(D, ℝ)) :
    tsupport (_root_.GD.N0227.N0545.d002018.d002021 a test : D → ℝ) ⊆ tsupport (test : D → ℝ) := by
  induction a generalizing test with
  | input => exact Set.Subset.rfl
  | add a b iha ihb =>
      exact (tsupport_add _ _).trans (Set.union_subset (iha test) (ihb test))
  | neg a ih =>
      change tsupport (-(_root_.GD.N0227.N0545.d002018.d002021 a test : D → ℝ)) ⊆ _
      rw [tsupport_neg]
      exact ih test
  | mul c a ih =>
      exact (ih (_root_.GD.N0232.N0720.N1230.d001994 test c)).trans (tsupport_mul_subset_left
        (f := (test : D → ℝ)) (g := (c : D → ℝ)))
  | deriv v a ih =>
      change tsupport (-(_root_.GD.N0227.N0545.d002018.d002021 a (∂_{v} test) : D → ℝ)) ⊆ _
      rw [tsupport_neg]
      exact (ih (∂_{v} test)).trans (SchwartzMap.tsupport_lineDerivOp_subset v test)

theorem d002023
    (a : _root_.GD.N0227.N0545.d002018 D) (χ : 𝓢(D, ℝ)) (n m : ℕ) (hm : a.d002019 ≤ m)
    (f : 𝓢(D, ℝ)) :
    ∃ r : 𝓢(D, ℝ), _root_.GD.N0227.N0545.d002018.d002021 a (_root_.GD.N0232.N0720.N1233.d002008 χ (n + m) f) = _root_.GD.N0232.N0720.N1233.d002008 χ n r := by
  induction a generalizing m f with
  | input =>
      refine ⟨_root_.GD.N0232.N0720.N1233.d002008 χ m f, ?_⟩
      ext x
      simp only [_root_.GD.N0227.N0545.d002018.d002021, _root_.GD.N0232.N0720.N1233.d002009, pow_add]
      ring
  | add a b iha ihb =>
      obtain ⟨ra, ha⟩ := iha m (le_trans (le_max_left _ _) hm) f
      obtain ⟨rb, hb⟩ := ihb m (le_trans (le_max_right _ _) hm) f
      refine ⟨ra + rb, ?_⟩
      rw [_root_.GD.N0227.N0545.d002018.d002021, ha, hb]
      ext x
      simp only [add_apply, _root_.GD.N0232.N0720.N1233.d002009, mul_add]
  | neg a ih =>
      obtain ⟨r, hr⟩ := ih m hm f
      refine ⟨-r, ?_⟩
      rw [_root_.GD.N0227.N0545.d002018.d002021, hr]
      ext x
      simp only [neg_apply, _root_.GD.N0232.N0720.N1233.d002009, mul_neg]
  | mul c a ih =>
      obtain ⟨r, hr⟩ := ih m hm (_root_.GD.N0232.N0720.N1230.d001994 f c)
      refine ⟨r, ?_⟩
      rw [_root_.GD.N0227.N0545.d002018.d002021]
      convert hr using 1
      congr 1
      ext x
      simp only [_root_.GD.N0232.N0720.N1230.d001995, _root_.GD.N0232.N0720.N1233.d002009]
      ring
  | deriv v a ih =>
      cases m with
      | zero => simp only [_root_.GD.N0227.N0545.d002018.d002019] at hm; omega
      | succ m =>
          have ham : a.d002019 ≤ m := by simpa only [_root_.GD.N0227.N0545.d002018.d002019, Nat.add_le_add_iff_right] using hm
          let g : 𝓢(D, ℝ) := ((n + m + 1 : ℕ) : ℝ) • _root_.GD.N0232.N0720.N1230.d001994 (∂_{v} χ) f +
            _root_.GD.N0232.N0720.N1230.d001994 χ (∂_{v} f)
          obtain ⟨r, hr⟩ := ih m ham g
          refine ⟨-r, ?_⟩
          rw [_root_.GD.N0227.N0545.d002018.d002021, Nat.add_succ, _root_.GD.N0232.N0720.N1233.d002011, hr]
          ext x
          simp only [neg_apply, _root_.GD.N0232.N0720.N1233.d002009, mul_neg]

def d002024 (χ : 𝓢(D, ℝ)) : 𝓢(D, ℝ) := _root_.GD.N0232.N0720.N1233.d002008 χ 9 χ

@[simp] theorem d002025 (χ : 𝓢(D, ℝ)) (x : D) : _root_.GD.N0227.N0545.d002018.d002024 χ x = χ x ^ 10 := by
  simp only [_root_.GD.N0227.N0545.d002018.d002024, _root_.GD.N0232.N0720.N1233.d002009]
  ring



theorem d002026
    (a : _root_.GD.N0227.N0545.d002018 D) (ha : a.d002019 ≤ 4) (χ : 𝓢(D, ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ x,
      (_root_.GD.N0227.N0545.d002018.d002021 a (_root_.GD.N0227.N0545.d002018.d002024 χ) x)^2 ≤ K * χ x ^ 10 := by
  obtain ⟨r, hr⟩ := _root_.GD.N0227.N0545.d002018.d002023 a χ 5 4 ha χ
  have he : _root_.GD.N0227.N0545.d002018.d002021 a (_root_.GD.N0227.N0545.d002018.d002024 χ) = _root_.GD.N0232.N0720.N1233.d002008 χ 5 r := hr
  let M := SchwartzMap.seminorm ℝ 0 0 r
  have hb (x : D) : |r x| ≤ M := SchwartzMap.norm_le_seminorm ℝ r x
  have hM : 0 ≤ M := (abs_nonneg (r 0)).trans (hb 0)
  refine ⟨M^2 + 1, by positivity, ?_⟩
  intro x
  have hx := abs_le.mp (hb x)
  have hs : (r x)^2 ≤ M^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ M + r x by linarith [hx.1])]
  rw [he, _root_.GD.N0232.N0720.N1233.d002009]
  calc
    _ = χ x ^ 10 * (r x)^2 := by ring
    _ ≤ χ x ^ 10 * M^2 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (M^2 + 1) * χ x ^ 10 := by nlinarith [show 0 ≤ χ x ^ 10 by positivity]

section Integral

variable [MeasurableSpace D] [BorelSpace D] [FiniteDimensional ℝ D]
  {μ : Measure D} [μ.IsAddHaarMeasure]


theorem d002027
    (a : _root_.GD.N0227.N0545.d002018 D) (error test : 𝓢(D, ℝ)) :
    (∫ x, test x * _root_.GD.N0227.N0545.d002018.d002020 error a x ∂μ) =
      ∫ x, error x * _root_.GD.N0227.N0545.d002018.d002021 a test x ∂μ := by
  induction a generalizing test with
  | input => simp only [_root_.GD.N0227.N0545.d002018.d002020, _root_.GD.N0227.N0545.d002018.d002021, mul_comm]
  | add a b iha ihb =>
      have hi (f g : 𝓢(D, ℝ)) : Integrable (fun x => f x * g x) μ :=
        (_root_.GD.N0232.N0720.N1230.d001994 f g).integrable
      simp only [_root_.GD.N0227.N0545.d002018.d002020, _root_.GD.N0227.N0545.d002018.d002021, add_apply, mul_add]
      rw [integral_add (hi test (_root_.GD.N0227.N0545.d002018.d002020 error a)) (hi test (_root_.GD.N0227.N0545.d002018.d002020 error b)),
        integral_add (hi error (_root_.GD.N0227.N0545.d002018.d002021 a test)) (hi error (_root_.GD.N0227.N0545.d002018.d002021 b test)), iha, ihb]
  | neg a ih =>
      simp only [_root_.GD.N0227.N0545.d002018.d002020, _root_.GD.N0227.N0545.d002018.d002021, neg_apply, mul_neg, integral_neg]
      rw [ih]
  | mul c a ih =>
      calc
        _ = ∫ x, _root_.GD.N0232.N0720.N1230.d001994 test c x * _root_.GD.N0227.N0545.d002018.d002020 error a x ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [_root_.GD.N0227.N0545.d002018.d002020, _root_.GD.N0232.N0720.N1230.d001995]
          ring
        _ = _ := ih _
  | deriv v a ih =>
      rw [_root_.GD.N0227.N0545.d002018.d002020, SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left, ih]
      simp only [_root_.GD.N0227.N0545.d002018.d002021, neg_apply, mul_neg, integral_neg]

end Integral
end d002018
end
end GD.N0227.N0545
