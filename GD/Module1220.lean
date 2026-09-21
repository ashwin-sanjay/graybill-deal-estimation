import GD.Module0667
import GD.Module1217











open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0232.N0719.N0976

open _root_.GD.N0232.N0719.N0977 _root_.GD.N0232.N0719.N0985
open _root_.GD.N0230.N0615
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1314

noncomputable section

abbrev d019733 (k : ℕ) := {tau : _root_.GD.N0232.N0719.N0977.d009764 k // ∀ i, 0 < tau i}

variable {k : ℕ}

def d019734 (tau : _root_.GD.N0232.N0719.N0976.d019733 k) (u : _root_.GD.N0232.N0720.N1341.d004415 k) : ℝ :=
  _root_.GD.N0230.N0615.d000152 tau.val (_root_.GD.N0232.N0719.N0977.d009773 k u)

def d019735 (tau : _root_.GD.N0232.N0719.N0976.d019733 k) (u : _root_.GD.N0232.N0720.N1341.d004415 k) : ℝ :=
  Real.sqrt (2 * Real.pi * (1 / _root_.GD.N0230.N0615.d000151 tau.val)) *
    _root_.GD.N0232.N0719.N0985.d009755 ((k : ℝ) + 2) (_root_.GD.N0232.N0719.N0977.d009778 k tau.val u)

theorem d019736 (tau : _root_.GD.N0232.N0719.N0976.d019733 k) (u : _root_.GD.N0232.N0720.N1341.d004415 k) : 0 < _root_.GD.N0232.N0719.N0976.d019735 tau u := by
  have hT := _root_.GD.N0232.N0719.N0977.d009779 k tau.val tau.property
  apply mul_pos
  · apply Real.sqrt_pos.2
    positivity
  · exact _root_.GD.N0232.N0719.N0985.d009758 (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith)
      (_root_.GD.N0232.N0719.N0977.d009780 k tau.val tau.property u)

@[fun_prop]
theorem d019737 : Continuous (_root_.GD.N0232.N0719.N0977.d009773 k) := by
  apply continuous_pi
  intro i
  cases i using Fin.cases <;> simp [_root_.GD.N0232.N0719.N0977.d009773] <;> fun_prop

@[fun_prop]
theorem d019738 : Continuous (fun p : _root_.GD.N0232.N0719.N0976.d019733 k × _root_.GD.N0232.N0720.N1341.d004415 k => _root_.GD.N0232.N0719.N0976.d019734 p.1 p.2) := by
  unfold _root_.GD.N0232.N0719.N0976.d019734 _root_.GD.N0230.N0615.d000152
  apply Continuous.div
  · apply continuous_finsetSum
    intro i hi
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply i).comp (_root_.GD.N0232.N0719.N0976.d019737.comp continuous_snd))
  · unfold _root_.GD.N0230.N0615.d000151
    fun_prop
  · intro p
    exact (_root_.GD.N0232.N0719.N0977.d009779 k p.1.val p.1.property).ne'

@[fun_prop]
theorem d019739 :
    Continuous (fun p : _root_.GD.N0232.N0719.N0976.d019733 k × _root_.GD.N0232.N0720.N1341.d004415 k => _root_.GD.N0232.N0719.N0977.d009778 k p.1.val p.2) := by
  unfold _root_.GD.N0232.N0719.N0977.d009778
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i hi
  exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).mul
    ((((continuous_apply i).comp (_root_.GD.N0232.N0719.N0976.d019737.comp continuous_snd)).sub
      _root_.GD.N0232.N0719.N0976.d019738).pow 2)

@[fun_prop]
theorem d019740 :
    Continuous (fun p : _root_.GD.N0232.N0719.N0976.d019733 k × _root_.GD.N0232.N0720.N1341.d004415 k => _root_.GD.N0232.N0719.N0976.d019735 p.1 p.2) := by
  have hT : Continuous (fun p : _root_.GD.N0232.N0719.N0976.d019733 k × _root_.GD.N0232.N0720.N1341.d004415 k => _root_.GD.N0230.N0615.d000151 p.1.val) := by
    unfold _root_.GD.N0230.N0615.d000151
    fun_prop
  have hinvT := (continuous_const (y := (1 : ℝ))).div hT
    (fun p => (_root_.GD.N0232.N0719.N0977.d009779 k p.1.val p.1.property).ne')
  have hinvQ := (continuous_const (y := (1 : ℝ))).div _root_.GD.N0232.N0719.N0976.d019739
    (fun p => (_root_.GD.N0232.N0719.N0977.d009780 k p.1.val p.1.property p.2).ne')
  have hp := hinvQ.rpow_const (p := ((k : ℝ) + 2 + 1) / 2)
    (fun p => Or.inl (one_div_ne_zero (_root_.GD.N0232.N0719.N0977.d009780 k p.1.val p.1.property p.2).ne'))
  unfold _root_.GD.N0232.N0719.N0976.d019735 _root_.GD.N0232.N0719.N0985.d009755
  exact (Real.continuous_sqrt.comp ((continuous_const.mul continuous_const).mul hinvT)).mul
    ((continuous_const.mul hp).mul continuous_const)

def d019741 (tau : _root_.GD.N0232.N0719.N0976.d019733 k) : C(_root_.GD.N0232.N0720.N1341.d004415 k, ℝ) where
  toFun := _root_.GD.N0232.N0719.N0976.d019734 tau
  continuous_toFun := _root_.GD.N0232.N0719.N0976.d019738.comp (continuous_const.prodMk continuous_id)

def d019742 (tau : _root_.GD.N0232.N0719.N0976.d019733 k) : C(_root_.GD.N0232.N0720.N1341.d004415 k, ℝ) where
  toFun := _root_.GD.N0232.N0719.N0976.d019735 tau
  continuous_toFun := _root_.GD.N0232.N0719.N0976.d019740.comp (continuous_const.prodMk continuous_id)

theorem d019743 : Continuous (_root_.GD.N0232.N0719.N0976.d019741 (k := k)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ _root_.GD.N0232.N0719.N0976.d019738

theorem d019744 : Continuous (_root_.GD.N0232.N0719.N0976.d019742 (k := k)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ _root_.GD.N0232.N0719.N0976.d019740

def d019745 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 k) : C(_root_.GD.N0232.N0720.N1341.d004415 k, ℝ) where
  toFun u := _root_.GD.N0232.N0719.N0976.d019735 tau u / _root_.GD.N0232.N0719.N0976.d019735 ref u
  continuous_toFun := (_root_.GD.N0232.N0719.N0976.d019742 tau).continuous.div (_root_.GD.N0232.N0719.N0976.d019742 ref).continuous
    (fun u => (_root_.GD.N0232.N0719.N0976.d019736 ref u).ne')

def d019746 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 k) : C(_root_.GD.N0232.N0720.N1341.d004415 k, ℝ) where
  toFun u := _root_.GD.N0232.N0719.N0976.d019745 ref tau u * Real.sqrt (_root_.GD.N0232.N0719.N0976.d019735 ref u) *
    (_root_.GD.N0232.N0719.N0976.d019734 tau u - _root_.GD.N0232.N0719.N0976.d019734 ref u)
  continuous_toFun := ((_root_.GD.N0232.N0719.N0976.d019745 ref tau).continuous.mul
    (Real.continuous_sqrt.comp (_root_.GD.N0232.N0719.N0976.d019742 ref).continuous)).mul
    ((_root_.GD.N0232.N0719.N0976.d019741 tau).continuous.sub (_root_.GD.N0232.N0719.N0976.d019741 ref).continuous)

def d019747 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 k) (h : _root_.GD.N0232.N0720.N1341.d004417 k) : ℝ :=
  _root_.GD.N0232.N0720.N1314.d019689 (_root_.GD.N0232.N0719.N0976.d019745 ref tau) (_root_.GD.N0232.N0719.N0976.d019746 ref tau) h

def d019748 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (u : _root_.GD.N0232.N0720.N1341.d004415 k) (h : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0976.d019734 ref u + h / Real.sqrt (_root_.GD.N0232.N0719.N0976.d019735 ref u)

theorem d019749 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 k) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    0 < _root_.GD.N0232.N0719.N0976.d019745 ref tau u := div_pos (_root_.GD.N0232.N0719.N0976.d019736 tau u) (_root_.GD.N0232.N0719.N0976.d019736 ref u)

theorem d019750 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) : _root_.GD.N0232.N0719.N0976.d019745 ref ref = 1 := by
  ext u
  exact div_self (_root_.GD.N0232.N0719.N0976.d019736 ref u).ne'

theorem d019751 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) : _root_.GD.N0232.N0719.N0976.d019746 ref ref = 0 := by
  ext u
  simp [_root_.GD.N0232.N0719.N0976.d019746]



theorem d019752 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 k) (u : _root_.GD.N0232.N0720.N1341.d004415 k) (h : ℝ) :
    _root_.GD.N0232.N0719.N0976.d019745 ref tau u * h ^ 2 - 2 * _root_.GD.N0232.N0719.N0976.d019746 ref tau u * h =
      _root_.GD.N0232.N0719.N0976.d019735 tau u * (_root_.GD.N0232.N0719.N0976.d019748 ref u h - _root_.GD.N0232.N0719.N0976.d019734 tau u) ^ 2 -
        _root_.GD.N0232.N0719.N0976.d019735 tau u * (_root_.GD.N0232.N0719.N0976.d019734 ref u - _root_.GD.N0232.N0719.N0976.d019734 tau u) ^ 2 := by
  have hr := Real.sq_sqrt (_root_.GD.N0232.N0719.N0976.d019736 ref u).le
  have hs : Real.sqrt (_root_.GD.N0232.N0719.N0976.d019735 ref u) ≠ 0 := (Real.sqrt_pos.2 (_root_.GD.N0232.N0719.N0976.d019736 ref u)).ne'
  change _root_.GD.N0232.N0719.N0976.d019735 tau u / _root_.GD.N0232.N0719.N0976.d019735 ref u * h ^ 2 -
    2 * (_root_.GD.N0232.N0719.N0976.d019735 tau u / _root_.GD.N0232.N0719.N0976.d019735 ref u * Real.sqrt (_root_.GD.N0232.N0719.N0976.d019735 ref u) *
      (_root_.GD.N0232.N0719.N0976.d019734 tau u - _root_.GD.N0232.N0719.N0976.d019734 ref u)) * h = _
  unfold _root_.GD.N0232.N0719.N0976.d019748
  generalize hv : Real.sqrt (_root_.GD.N0232.N0719.N0976.d019735 ref u) = v at hr hs ⊢
  rw [← hr]
  field_simp
  ring

theorem d019753 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    _root_.GD.N0232.N0719.N0976.d019747 ref ref h = ‖h‖ ^ 2 := by
  unfold _root_.GD.N0232.N0719.N0976.d019747 _root_.GD.N0232.N0720.N1314.d019689
  rw [_root_.GD.N0232.N0719.N0976.d019750, _root_.GD.N0232.N0719.N0976.d019751]
  have hweighted : _root_.GD.N0232.N0720.N1316.d004471 (1 : C(_root_.GD.N0232.N0720.N1341.d004415 k, ℝ)) h = h := by
    apply Lp.ext
    filter_upwards [_root_.GD.N0232.N0720.N1316.d004472 (1 : C(_root_.GD.N0232.N0720.N1341.d004415 k, ℝ)) h] with u hu
    simpa using hu
  simp [_root_.GD.N0232.N0720.N1316.d004474, hweighted, _root_.GD.N0232.N0720.N1316.d004475]

theorem d019754 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) : Continuous (_root_.GD.N0232.N0719.N0976.d019745 ref) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact _root_.GD.N0232.N0719.N0976.d019740.div
    ((_root_.GD.N0232.N0719.N0976.d019742 ref).continuous.comp continuous_snd)
    (fun p => (_root_.GD.N0232.N0719.N0976.d019736 ref p.2).ne')

theorem d019755 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) : Continuous (_root_.GD.N0232.N0719.N0976.d019746 ref) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have ha := ContinuousMap.continuous_uncurry_of_continuous
    ⟨_root_.GD.N0232.N0719.N0976.d019745 ref, _root_.GD.N0232.N0719.N0976.d019754 ref⟩
  exact (ha.mul (Real.continuous_sqrt.comp
    ((_root_.GD.N0232.N0719.N0976.d019742 ref).continuous.comp continuous_snd))).mul
    (_root_.GD.N0232.N0719.N0976.d019738.sub ((_root_.GD.N0232.N0719.N0976.d019741 ref).continuous.comp continuous_snd))

theorem d019756 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 k) :
    Continuous (_root_.GD.N0232.N0719.N0976.d019747 ref tau) := by
  unfold _root_.GD.N0232.N0719.N0976.d019747 _root_.GD.N0232.N0720.N1314.d019689
  exact (_root_.GD.N0232.N0720.N1316.d004478.comp (continuous_const.prodMk continuous_id)).sub
    (continuous_const.mul (_root_.GD.N0232.N0720.N1316.d004479.comp (continuous_const.prodMk continuous_id)))

theorem d019757 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    Continuous (fun tau => _root_.GD.N0232.N0719.N0976.d019747 ref tau h) := by
  unfold _root_.GD.N0232.N0719.N0976.d019747 _root_.GD.N0232.N0720.N1314.d019689
  exact (_root_.GD.N0232.N0720.N1316.d004478.comp
    ((_root_.GD.N0232.N0719.N0976.d019754 ref).prodMk continuous_const)).sub
      (continuous_const.mul (_root_.GD.N0232.N0720.N1316.d004479.comp
        ((_root_.GD.N0232.N0719.N0976.d019755 ref).prodMk continuous_const)))

theorem d019758 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 k) :
    ConvexOn ℝ univ (_root_.GD.N0232.N0719.N0976.d019747 ref tau) := by
  let ell : _root_.GD.N0232.N0720.N1341.d004417 k →ₗ[ℝ] ℝ :=
    (-2 : ℝ) • (innerSL ℝ (ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ
      (_root_.GD.N0232.N0719.N0976.d019746 ref tau))).toLinearMap
  have hc := (_root_.GD.N0232.N0720.N1316.d004487 (_root_.GD.N0232.N0719.N0976.d019745 ref tau)
    (fun u => (_root_.GD.N0232.N0719.N0976.d019749 ref tau u).le)).add (ell.convexOn convex_univ)
  have heq : _root_.GD.N0232.N0719.N0976.d019747 ref tau = _root_.GD.N0232.N0720.N1316.d004474 (_root_.GD.N0232.N0719.N0976.d019745 ref tau) + ell := by
    funext h
    change _root_.GD.N0232.N0720.N1316.d004474 (_root_.GD.N0232.N0719.N0976.d019745 ref tau) h -
      2 * inner ℝ (ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ (_root_.GD.N0232.N0719.N0976.d019746 ref tau)) h =
      _root_.GD.N0232.N0720.N1316.d004474 (_root_.GD.N0232.N0719.N0976.d019745 ref tau) h +
        (-2) * inner ℝ (ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ (_root_.GD.N0232.N0719.N0976.d019746 ref tau)) h
    ring
  rwa [← heq] at hc

end
end GD.N0232.N0719.N0976

#print axioms _root_.GD.N0232.N0719.N0976.d019752
#print axioms _root_.GD.N0232.N0719.N0976.d019753
#print axioms _root_.GD.N0232.N0719.N0976.d019757
#print axioms _root_.GD.N0232.N0719.N0976.d019758
