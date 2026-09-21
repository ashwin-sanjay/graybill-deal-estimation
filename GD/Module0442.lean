import GD.Module0365
import GD.Module0371



















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1551
noncomputable section

open MeasureTheory Filter Set Complex ContinuousMap TopologicalSpace
open _root_.GD.N0106.N0428.N0765.N1550 _root_.GD.N0106.N0428.N0765.N1522 _root_.GD.N0106.N0428.N0765.N1613
open scoped Topology FourierTransform



theorem d006791 {f : ℂ → ℂ} {d : ℝ}
    (hc : ContinuousOn f {z : ℂ | |z.im| ≤ d})
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, |z.im| ≤ d → ‖f z‖ ≤ M := by
  obtain ⟨R, hR⟩ := hdecay 1 zero_lt_one
  let r : ℝ := max R 0
  let box : Set (ℝ × ℝ) := Icc (-r) r ×ˢ Icc (-d) d
  let K : Set ℂ := (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 p.1 p.2) '' box
  have hpoint : Continuous (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 p.1 p.2) := by
    unfold _root_.GD.N0106.N0428.N0765.N1550.d005473
    fun_prop
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hK : IsCompact K := hbox.image hpoint
  have hsubset : K ⊆ {z : ℂ | |z.im| ≤ d} := by
    rintro z ⟨p, hp, rfl⟩
    simpa only [mem_setOf_eq, _root_.GD.N0106.N0428.N0765.N1550.d005477] using abs_le.mpr hp.2
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hc.norm.mono hsubset)
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  have hpointz : _root_.GD.N0106.N0428.N0765.N1550.d005473 z.re z.im = z := by
    apply Complex.ext <;> simp only [_root_.GD.N0106.N0428.N0765.N1550.d005476, _root_.GD.N0106.N0428.N0765.N1550.d005477]
  by_cases hfar : R ≤ |z.re|
  · have hbound := hR z.re z.im hfar hz
    rw [hpointz] at hbound
    exact hbound.trans (le_max_right _ _)
  · have hx : |z.re| ≤ r := (lt_of_not_ge hfar).le.trans (le_max_left _ _)
    have hzK : z ∈ K := by
      exact ⟨(z.re, z.im), ⟨abs_le.mp hx, abs_le.mp hz⟩, hpointz⟩
    exact (hB ⟨z, hzK, rfl⟩).trans (le_max_left _ _)


theorem d006792 {f : ℂ → ℂ} {d y : ℝ}
    (hd : 0 < d) (hy : |y| ≤ d)
    (hc : ContinuousOn f {z : ℂ | |z.im| ≤ d})
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.im| < d})
    (h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0))
    (hyint : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f y))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε) (xi : ℝ) :
    ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0) xi‖ ≤
      Real.exp (2 * Real.pi * xi * y) * ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 f y x‖ := by
  have hec : Continuous (fun z : ℂ =>
      Complex.exp (((-2 * Real.pi * xi : ℝ) : ℂ) * (z * Complex.I))) := by
    fun_prop
  have htc : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) {z : ℂ | |z.im| ≤ d} :=
    hec.continuousOn.mul hc
  have htd : DifferentiableOn ℂ (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) {z : ℂ | |z.im| < d} := by
    intro z hz
    have he : DifferentiableAt ℂ (fun z : ℂ =>
        Complex.exp (((-2 * Real.pi * xi : ℝ) : ℂ) * (z * Complex.I))) z := by
      fun_prop
    exact he.differentiableWithinAt.mul (hf z hz)
  have htdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε := by
    intro ε hε
    let C : ℝ := Real.exp (2 * Real.pi * |xi| * d)
    have hC : 0 < C := Real.exp_pos _
    obtain ⟨R, hR⟩ := hdecay (ε / C) (div_pos hε hC)
    refine ⟨R, ?_⟩
    intro x s hx hs
    calc
      _ ≤ C * ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ :=
        _root_.GD.N0106.N0428.N0765.N1550.d005485 xi (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hs)
      _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_left (hR x s hx hs) hC.le
      _ = ε := by field_simp [hC.ne']
  have hshift := _root_.GD.N0106.N0428.N0765.N1522.d005494 hd hy htc htd
    (_root_.GD.N0106.N0428.N0765.N1550.d005487 xi h0) (_root_.GD.N0106.N0428.N0765.N1550.d005487 xi hyint) htdecay
  rw [_root_.GD.N0106.N0428.N0765.N1550.d005488, hshift]
  calc
    _ ≤ ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) y x‖ := norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, Real.exp (2 * Real.pi * xi * y) * ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 f y x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005477] using _root_.GD.N0106.N0428.N0765.N1550.d005484 xi f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x y)
    _ = _ := integral_const_mul _ _


theorem d006793 {s : ℤ → ℂ} {Cpos Cneg k : ℝ}
    (hk : 0 < k)
    (hpos : ∀ n : ℕ, ‖s ((n : ℤ) + 1)‖ ≤ Cpos * Real.exp (-k * (n + 1)))
    (hneg : ∀ n : ℕ, ‖s (-((n : ℤ) + 1))‖ ≤ Cneg * Real.exp (-k * (n + 1))) :
    Summable s := by
  exact Summable.of_add_one_of_neg_add_one
    ((_root_.GD.N0106.N0428.N0765.N1613.d005629 hk Cpos).summable.of_norm_bounded hpos)
    ((_root_.GD.N0106.N0428.N0765.N1613.d005629 hk Cneg).summable.of_norm_bounded hneg)



theorem d006794 {s : ℤ → ℂ} {Cpos Cneg k : ℝ}
    (hk : 0 < k)
    (hpos : ∀ n : ℕ, ‖s ((n : ℤ) + 1)‖ ≤ Cpos * Real.exp (-k * (n + 1)))
    (hneg : ∀ n : ℕ, ‖s (-((n : ℤ) + 1))‖ ≤ Cneg * Real.exp (-k * (n + 1))) :
    ‖(∑' n : ℤ, s n) - s 0‖ ≤ (Cpos + Cneg) / (Real.exp k - 1) := by
  have hp : Summable (fun n : ℕ => s ((n : ℤ) + 1)) :=
    (_root_.GD.N0106.N0428.N0765.N1613.d005629 hk Cpos).summable.of_norm_bounded hpos
  have hn : Summable (fun n : ℕ => s (-((n : ℤ) + 1))) :=
    (_root_.GD.N0106.N0428.N0765.N1613.d005629 hk Cneg).summable.of_norm_bounded hneg
  have hsplit : (∑' n : ℤ, s n) - s 0 =
      (∑' n : ℕ, s ((n : ℤ) + 1)) + ∑' n : ℕ, s (-((n : ℤ) + 1)) := by
    rw [tsum_of_add_one_of_neg_add_one hp hn]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖∑' n : ℕ, s ((n : ℤ) + 1)‖ +
        ‖∑' n : ℕ, s (-((n : ℤ) + 1))‖ := norm_add_le _ _
    _ ≤ Cpos / (Real.exp k - 1) + Cneg / (Real.exp k - 1) :=
      add_le_add (tsum_of_norm_bounded (_root_.GD.N0106.N0428.N0765.N1613.d005629 hk Cpos) hpos)
        (tsum_of_norm_bounded (_root_.GD.N0106.N0428.N0765.N1613.d005629 hk Cneg) hneg)
    _ = _ := by ring



theorem d006795 {f : C(ℝ, ℂ)} {Cpos Cneg k : ℝ}
    (hk : 0 < k)
    (hnorm : ∀ K : Compacts ℝ, Summable fun n : ℤ =>
      ‖(f.comp (ContinuousMap.addRight n)).restrict K‖)
    (hpos : ∀ n : ℕ, ‖𝓕 (f : ℝ → ℂ) ((n : ℝ) + 1)‖ ≤
      Cpos * Real.exp (-k * (n + 1)))
    (hneg : ∀ n : ℕ, ‖𝓕 (f : ℝ → ℂ) (-((n : ℝ) + 1))‖ ≤
      Cneg * Real.exp (-k * (n + 1))) (x : ℝ) :
    ‖(∑' n : ℤ, f (x + n)) - ∫ t : ℝ, f t‖ ≤
      (Cpos + Cneg) / (Real.exp k - 1) := by
  have hp : ∀ n : ℕ, ‖𝓕 (f : ℝ → ℂ) (((n : ℤ) + 1) : ℤ)‖ ≤
      Cpos * Real.exp (-k * (n + 1)) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hpos
  have hn : ∀ n : ℕ, ‖𝓕 (f : ℝ → ℂ) (-((n : ℤ) + 1) : ℤ)‖ ≤
      Cneg * Real.exp (-k * (n + 1)) := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one] using hneg
  have hF : Summable (fun n : ℤ => 𝓕 (f : ℝ → ℂ) n) :=
    _root_.GD.N0106.N0428.N0765.N1551.d006793 hk hp hn
  have hpoisson := Real.tsum_eq_tsum_fourier hnorm hF x
  let mode (n : ℤ) : ℂ := 𝓕 (f : ℝ → ℂ) n * fourier n (x : UnitAddCircle)
  have hphase : ∀ n : ℤ, ‖mode n‖ = ‖𝓕 (f : ℝ → ℂ) n‖ := by
    intro n
    have hphase_norm : ‖fourier n (x : UnitAddCircle)‖ = 1 := Circle.norm_coe _
    simp only [mode, norm_mul, hphase_norm, mul_one]
  have hzero : mode 0 = ∫ t : ℝ, f t := by
    simp only [mode, Int.cast_zero, fourier_zero, mul_one, _root_.GD.N0106.N0428.N0765.N1613.d005632]
  have he := _root_.GD.N0106.N0428.N0765.N1551.d006794 hk
    (fun n => (hphase _).le.trans (hp n)) (fun n => (hphase _).le.trans (hn n))
  rw [hzero] at he
  change (∑' n : ℤ, f (x + n)) = ∑' n : ℤ, mode n at hpoisson
  rw [← hpoisson] at he
  exact he



theorem d006796 {error h d Bplus Bminus : ℝ}
    {r bp bm : ℕ → ℝ} (hh : 0 < h) (hd : 0 < d)
    (hr : Tendsto r atTop (𝓝 d))
    (hp : Tendsto bp atTop (𝓝 Bplus)) (hm : Tendsto bm atTop (𝓝 Bminus))
    (hb : ∀ n : ℕ, error ≤ (bp n + bm n) /
      (Real.exp (2 * Real.pi * r n / h) - 1)) :
    error ≤ (Bplus + Bminus) / (Real.exp (2 * Real.pi * d / h) - 1) := by
  have he : Tendsto (fun n : ℕ => Real.exp (2 * Real.pi * r n / h) - 1)
      atTop (𝓝 (Real.exp (2 * Real.pi * d / h) - 1)) :=
    ((Real.continuous_exp.tendsto _).comp
      ((hr.const_mul (2 * Real.pi)).div_const h)).sub_const 1
  have hden : Real.exp (2 * Real.pi * d / h) - 1 ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    apply Real.one_lt_exp_iff.mpr
    positivity
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ((hp.add hm).div he hden)
    (Eventually.of_forall hb)

end
end GD.N0106.N0428.N0765.N1551

#print axioms _root_.GD.N0106.N0428.N0765.N1551.d006792
#print axioms _root_.GD.N0106.N0428.N0765.N1551.d006791
#print axioms _root_.GD.N0106.N0428.N0765.N1551.d006794
#print axioms _root_.GD.N0106.N0428.N0765.N1551.d006795
#print axioms _root_.GD.N0106.N0428.N0765.N1551.d006796
