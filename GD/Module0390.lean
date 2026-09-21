import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic











namespace GD.N0232.N0720.N1104

open Set

noncomputable section

def d005988 (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (x + h) - f x

private theorem d005989
    {f f' : ℝ → ℝ} {x h : ℝ}
    (hx : HasDerivAt f (f' x) x)
    (hxh : HasDerivAt f (f' (x + h)) (x + h)) :
    HasDerivAt (_root_.GD.N0232.N0720.N1104.d005988 h f) (_root_.GD.N0232.N0720.N1104.d005988 h f' x) x := by
  change HasDerivAt (fun z : ℝ => f (z + h) - f z) (f' (x + h) - f' x) x
  convert! (hxh.comp x ((hasDerivAt_id x).add_const h)).sub hx using 1
  simp



theorem d005990
    {f f' : ℝ → ℝ} {x h : ℝ} (hh : 0 < h)
    (hf : ∀ y ∈ Icc x (x + h), HasDerivAt f (f' y) y) :
    ∃ y ∈ Ioo x (x + h), _root_.GD.N0232.N0720.N1104.d005988 h f x = h * f' y := by
  have hcont : ContinuousOn f (Icc x (x + h)) :=
    fun y hy => (hf y hy).continuousAt.continuousWithinAt
  obtain ⟨y, hy, heq⟩ := exists_hasDerivAt_eq_slope f f'
    (a := x) (b := x + h) (by linarith) hcont
    (fun y hy => hf y ⟨hy.1.le, hy.2.le⟩)
  refine ⟨y, hy, ?_⟩
  have heq' : f' y = _root_.GD.N0232.N0720.N1104.d005988 h f x / h := by
    simpa [_root_.GD.N0232.N0720.N1104.d005988] using heq
  have hmul := (eq_div_iff hh.ne').mp heq'
  simpa [mul_comm] using hmul.symm



theorem d005991
    {f f' f'' : ℝ → ℝ} {x a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hf : ∀ y ∈ Icc x (x + a + b), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc x (x + a + b), HasDerivAt f' (f'' y) y) :
    ∃ y ∈ Ioo x (x + a + b),
      _root_.GD.N0232.N0720.N1104.d005988 a (_root_.GD.N0232.N0720.N1104.d005988 b f) x = a * b * f'' y := by
  have hg : ∀ z ∈ Icc x (x + a),
      HasDerivAt (_root_.GD.N0232.N0720.N1104.d005988 b f) (_root_.GD.N0232.N0720.N1104.d005988 b f' z) z := by
    intro z hz
    apply _root_.GD.N0232.N0720.N1104.d005989
    · exact hf z ⟨hz.1, by linarith [hz.2]⟩
    · exact hf (z + b) ⟨by linarith [hz.1], by linarith [hz.2]⟩
  obtain ⟨u, hu, huEq⟩ := _root_.GD.N0232.N0720.N1104.d005990 ha hg
  obtain ⟨v, hv, hvEq⟩ := _root_.GD.N0232.N0720.N1104.d005990 (f := f')
    (f' := f'') (x := u) hb (by
      intro z hz
      exact hf' z ⟨by linarith [hu.1, hz.1], by linarith [hu.2, hz.2]⟩)
  refine ⟨v, ⟨by linarith [hu.1, hv.1], by linarith [hu.2, hv.2]⟩, ?_⟩
  rw [hvEq] at huEq
  simpa [mul_assoc] using huEq


theorem d005992
    {f f' f'' f''' : ℝ → ℝ} {x a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hf : ∀ y ∈ Icc x (x + a + b + c), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc x (x + a + b + c), HasDerivAt f' (f'' y) y)
    (hf'' : ∀ y ∈ Icc x (x + a + b + c), HasDerivAt f'' (f''' y) y) :
    ∃ y ∈ Ioo x (x + a + b + c),
      _root_.GD.N0232.N0720.N1104.d005988 a (_root_.GD.N0232.N0720.N1104.d005988 b (_root_.GD.N0232.N0720.N1104.d005988 c f)) x =
        a * b * c * f''' y := by
  have hg : ∀ z ∈ Icc x (x + a + b),
      HasDerivAt (_root_.GD.N0232.N0720.N1104.d005988 c f) (_root_.GD.N0232.N0720.N1104.d005988 c f' z) z := by
    intro z hz
    apply _root_.GD.N0232.N0720.N1104.d005989
    · exact hf z ⟨hz.1, by linarith [hz.2]⟩
    · exact hf (z + c) ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hg' : ∀ z ∈ Icc x (x + a + b),
      HasDerivAt (_root_.GD.N0232.N0720.N1104.d005988 c f') (_root_.GD.N0232.N0720.N1104.d005988 c f'' z) z := by
    intro z hz
    apply _root_.GD.N0232.N0720.N1104.d005989
    · exact hf' z ⟨hz.1, by linarith [hz.2]⟩
    · exact hf' (z + c) ⟨by linarith [hz.1], by linarith [hz.2]⟩
  obtain ⟨u, hu, huEq⟩ := _root_.GD.N0232.N0720.N1104.d005991 ha hb hg hg'
  obtain ⟨v, hv, hvEq⟩ := _root_.GD.N0232.N0720.N1104.d005990 (f := f'')
    (f' := f''') (x := u) hc (by
      intro z hz
      exact hf'' z ⟨by linarith [hu.1, hz.1], by linarith [hu.2, hz.2]⟩)
  refine ⟨v, ⟨by linarith [hu.1, hv.1], by linarith [hu.2, hv.2]⟩, ?_⟩
  rw [hvEq] at huEq
  simpa [mul_assoc] using huEq


theorem d005993
    {f f' : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hf : ∀ y ∈ Icc (-h) h, HasDerivAt f (f' y) y) :
    ∃ y ∈ Ioo (-h) h, (f h - f (-h)) / (2 * h) = f' y := by
  have hend : -h + 2 * h = h := by ring
  obtain ⟨y, hy, heq⟩ := _root_.GD.N0232.N0720.N1104.d005990
    (f := f) (f' := f') (x := -h) (h := 2 * h) (by positivity)
    (by simpa only [hend] using hf)
  refine ⟨y, by simpa only [hend] using hy, ?_⟩
  have heq' : f h - f (-h) = (2 * h) * f' y := by
    simpa only [_root_.GD.N0232.N0720.N1104.d005988, hend] using heq
  rw [heq']
  field_simp


theorem d005994
    {f f' f'' : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hf : ∀ y ∈ Icc (-h) h, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (-h) h, HasDerivAt f' (f'' y) y) :
    ∃ y ∈ Ioo (-h) h,
      (f h - 2 * f 0 + f (-h)) / h ^ 2 = f'' y := by
  have hend : -h + h + h = h := by ring
  obtain ⟨y, hy, heq⟩ := _root_.GD.N0232.N0720.N1104.d005991
    (f := f) (f' := f') (f'' := f'') (x := -h) hh hh
    (by simpa only [hend] using hf) (by simpa only [hend] using hf')
  refine ⟨y, by simpa only [hend] using hy, ?_⟩
  have hexpand : _root_.GD.N0232.N0720.N1104.d005988 h (_root_.GD.N0232.N0720.N1104.d005988 h f) (-h) =
      f h - 2 * f 0 + f (-h) := by
    simp only [_root_.GD.N0232.N0720.N1104.d005988, neg_add_cancel, zero_add]
    ring
  rw [hexpand] at heq
  have heq' : f h - 2 * f 0 + f (-h) = h ^ 2 * f'' y := by
    exact heq.trans (by ring)
  rw [heq']
  field_simp



theorem d005995
    {f f' f'' f''' : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hf : ∀ y ∈ Icc (-2 * h) (2 * h), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (-2 * h) (2 * h), HasDerivAt f' (f'' y) y)
    (hf'' : ∀ y ∈ Icc (-2 * h) (2 * h), HasDerivAt f'' (f''' y) y) :
    ∃ y ∈ Ioo (-2 * h) (2 * h),
      (f (2 * h) - 2 * f h + 2 * f (-h) - f (-2 * h)) /
        (2 * h ^ 3) = f''' y := by
  have hend : -2 * h + h + h + 2 * h = 2 * h := by ring
  obtain ⟨y, hy, heq⟩ := _root_.GD.N0232.N0720.N1104.d005992
    (f := f) (f' := f') (f'' := f'') (f''' := f''') (x := -2 * h)
    hh hh (show 0 < 2 * h by positivity)
    (by simpa only [hend] using hf) (by simpa only [hend] using hf')
    (by simpa only [hend] using hf'')
  refine ⟨y, by simpa only [hend] using hy, ?_⟩
  have h1 : -2 * h + h = -h := by ring
  have h4 : -2 * h + 2 * h = 0 := by ring
  have hexpand :
      _root_.GD.N0232.N0720.N1104.d005988 h (_root_.GD.N0232.N0720.N1104.d005988 h (_root_.GD.N0232.N0720.N1104.d005988 (2 * h) f)) (-2 * h) =
        f (2 * h) - 2 * f h + 2 * f (-h) - f (-2 * h) := by
    simp only [_root_.GD.N0232.N0720.N1104.d005988, h1, h4]
    ring
  rw [hexpand] at heq
  have heq' : f (2 * h) - 2 * f h + 2 * f (-h) - f (-2 * h) =
      (2 * h ^ 3) * f''' y := heq.trans (by ring)
  rw [heq']
  field_simp



theorem d005996
    {f fs fst : ℝ → ℝ → ℝ} {h eta : ℝ}
    (hh : 0 < h) (heta : 0 < eta)
    (hfs : ∀ s ∈ Icc (-h) h, ∀ t ∈ Icc eta (2 * eta),
      HasDerivAt (fun u => f u t) (fs s t) s)
    (hfst : ∀ s ∈ Icc (-h) h, ∀ t ∈ Icc eta (2 * eta),
      HasDerivAt (fs s) (fst s t) t) :
    ∃ s ∈ Ioo (-h) h, ∃ t ∈ Ioo eta (2 * eta),
      ((f h (2 * eta) - f (-h) (2 * eta)) -
        (f h eta - f (-h) eta)) / (2 * h * eta) = fst s t := by
  have ht0 : eta ∈ Icc eta (2 * eta) := ⟨le_rfl, by linarith⟩
  have ht1 : 2 * eta ∈ Icc eta (2 * eta) := ⟨by linarith, le_rfl⟩
  obtain ⟨s, hs, hsEq⟩ := _root_.GD.N0232.N0720.N1104.d005993
    (f := fun u => f u (2 * eta) - f u eta)
    (f' := fun u => fs u (2 * eta) - fs u eta) hh
    (fun u hu => (hfs u hu (2 * eta) ht1).sub (hfs u hu eta ht0))
  have hend : eta + eta = 2 * eta := by ring
  obtain ⟨t, ht, htEq⟩ := _root_.GD.N0232.N0720.N1104.d005990
    (f := fs s) (f' := fst s) (x := eta) heta (by
      simpa only [hend] using hfst s ⟨hs.1.le, hs.2.le⟩)
  refine ⟨s, hs, t, by simpa only [hend] using ht, ?_⟩
  have htEq' : fs s (2 * eta) - fs s eta = eta * fst s t := by
    simpa only [_root_.GD.N0232.N0720.N1104.d005988, hend] using htEq
  rw [htEq'] at hsEq
  have hsMul := (div_eq_iff (show 2 * h ≠ 0 by positivity)).mp hsEq
  apply (div_eq_iff (show 2 * h * eta ≠ 0 by positivity)).mpr
  nlinarith [hsMul]




theorem d005997
    {f ft : ℝ → ℝ → ℝ} {h eta : ℝ}
    (hh : 0 < h) (heta : 0 < eta)
    (hftPlus : ∀ t ∈ Icc eta (2 * eta), HasDerivAt (f h) (ft h t) t)
    (hftMinus : ∀ t ∈ Icc eta (2 * eta), HasDerivAt (f (-h)) (ft (-h) t) t) :
    ∃ t ∈ Ioo eta (2 * eta),
      ((f h (2 * eta) - f (-h) (2 * eta)) -
        (f h eta - f (-h) eta)) / (2 * h * eta) =
          (ft h t - ft (-h) t) / (2 * h) := by
  have hend : eta + eta = 2 * eta := by ring
  obtain ⟨t, ht, htEq⟩ := _root_.GD.N0232.N0720.N1104.d005990
    (f := fun v => f h v - f (-h) v)
    (f' := fun v => ft h v - ft (-h) v) (x := eta) heta (by
      intro v hv
      have hv' : v ∈ Icc eta (2 * eta) := by simpa only [hend] using hv
      exact (hftPlus v hv').sub (hftMinus v hv'))
  refine ⟨t, by simpa only [hend] using ht, ?_⟩
  have htEq' : (f h (2 * eta) - f (-h) (2 * eta)) -
      (f h eta - f (-h) eta) = eta * (ft h t - ft (-h) t) := by
    simpa only [_root_.GD.N0232.N0720.N1104.d005988, hend] using htEq
  rw [htEq']
  field_simp

end

end GD.N0232.N0720.N1104

#print axioms _root_.GD.N0232.N0720.N1104.d005995
#print axioms _root_.GD.N0232.N0720.N1104.d005994
#print axioms _root_.GD.N0232.N0720.N1104.d005993
#print axioms _root_.GD.N0232.N0720.N1104.d005996
#print axioms _root_.GD.N0232.N0720.N1104.d005997
