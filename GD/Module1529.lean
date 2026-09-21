import GD.Module1528
import GD.Module0482
import GD.Module1526
import GD.Module1525
import GD.Module1297









set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace GD.N0106.N0428.N0765.N1572
open _root_.GD.N0106.N0428.N0765.N1579 _root_.GD.N0106.N0428.N0765.N1581 _root_.GD.N0106.N0428.N0765.N1634
  _root_.GD.N0106.N0428.N0765.N1616 _root_.GD.N0106.N0428.N0765.N1548
open MeasureTheory

noncomputable def d023746 : ℝ :=
  (_root_.GD.N0106.N0428.N0765.N1582.d007418 : ℝ) / (_root_.GD.N0106.N0428.N0765.N1582.d007419 : ℝ)

theorem d023747 : 0 < _root_.GD.N0106.N0428.N0765.N1572.d023746 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1572.d023746, _root_.GD.N0106.N0428.N0765.N1582.d007418, _root_.GD.N0106.N0428.N0765.N1582.d007419]

theorem d023748 : _root_.GD.N0106.N0428.N0765.N1579.d007458.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1572.d023746 :=
  _root_.GD.N0106.N0428.N0765.N1548.d006926.d006964 _root_.GD.N0106.N0428.N0765.N1573.d022632
    (by decide : (0 : ℤ) < _root_.GD.N0106.N0428.N0765.N1582.d007419) _root_.GD.N0106.N0428.N0765.N1582.d007418

theorem d023749 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1579.d007457}
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 s I J).valid = true) : I.valid = true ∧ J.valid = true := by
  have h := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv
  exact ⟨h.1, (Bool.and_eq_true_iff.mp h.2).1⟩

def d023750 (sums : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457) : Prop := sums.1.valid = true ∧ sums.2.valid = true

def d023751 (eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457) (r : _root_.GD.N0106.N0428.N0765.N1579.d007461) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007442
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 eb r.complement)
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1579.d007458 r.lam))
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 kcoef r.common)

def d023752 (eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457) (r : _root_.GD.N0106.N0428.N0765.N1579.d007461) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 r.baseC
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007450 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1572.d023751 eb kcoef r) 10)
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007452 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1572.d023751 eb kcoef r)))

theorem d023753 (eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457) (sums : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457) (r : _root_.GD.N0106.N0428.N0765.N1579.d007461) :
    _root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef sums r =
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 sums.1 (_root_.GD.N0106.N0428.N0765.N1572.d023752 eb kcoef r),
       _root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 sums.2 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 r.lam (_root_.GD.N0106.N0428.N0765.N1572.d023752 eb kcoef r))) := rfl

theorem d023754 {eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457} {sums : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457} {r : _root_.GD.N0106.N0428.N0765.N1579.d007461}
    (hv : _root_.GD.N0106.N0428.N0765.N1572.d023750 (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef sums r)) : _root_.GD.N0106.N0428.N0765.N1572.d023750 sums := by
  exact ⟨(Bool.and_eq_true_iff.mp hv.1).1, (Bool.and_eq_true_iff.mp hv.2).1⟩


theorem d023755 {eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457} {sums : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457} {r : _root_.GD.N0106.N0428.N0765.N1579.d007461}
    {u v c s₀ s₁ : ℝ} (hu : 0 ≤ u) (hv : 0 < v)
    (heb : eb.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 v) (hkcoef : kcoef.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 ((1 + _root_.GD.N0106.N0428.N0765.N1572.d023746) * u))
    (hr : _root_.GD.N0106.N0428.N0765.N1581.d023723 r c) (hs₀ : sums.1.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 s₀) (hs₁ : sums.2.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 s₁)
    (hvalid : _root_.GD.N0106.N0428.N0765.N1572.d023750 (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef sums r)) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef sums r).1.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (s₀ + _root_.GD.N0106.N0428.N0765.N1616.d020957 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c) ∧
    (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef sums r).2.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (s₁ + _root_.GD.N0106.N0428.N0765.N1616.d020958 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c) := by
  have hF0valid : (_root_.GD.N0106.N0428.N0765.N1572.d023752 eb kcoef r).valid = true := (Bool.and_eq_true_iff.mp hvalid.1).2
  have hF1valid : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 r.lam (_root_.GD.N0106.N0428.N0765.N1572.d023752 eb kcoef r)).valid = true :=
    (Bool.and_eq_true_iff.mp hvalid.2).2
  have hden := (_root_.GD.N0106.N0428.N0765.N1572.d023749 hF0valid).2
  have hdenparts := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hden
  have hPvalid : (_root_.GD.N0106.N0428.N0765.N1572.d023751 eb kcoef r).valid = true := (Bool.and_eq_true_iff.mp hdenparts.1).1
  have hPparts := Bool.and_eq_true_iff.mp hPvalid
  have hPleft := Bool.and_eq_true_iff.mp hPparts.1
  have hPexpr := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007732
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hPleft.1 heb hr.2.1)
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hPleft.2 _root_.GD.N0106.N0428.N0765.N1572.d023748 hr.1))
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hPparts.2 hkcoef hr.2.2.1)
  have hPeq : v * _root_.GD.N0106.N0428.N0765.N1634.d023648 c + _root_.GD.N0106.N0428.N0765.N1572.d023746 * _root_.GD.N0106.N0428.N0765.N1634.d023649 c +
      ((1 + _root_.GD.N0106.N0428.N0765.N1572.d023746) * u) * _root_.GD.N0106.N0428.N0765.N1634.d023650 c = _root_.GD.N0106.N0428.N0765.N1634.d023651 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c := by
    unfold _root_.GD.N0106.N0428.N0765.N1634.d023651
    ring
  have hP : (_root_.GD.N0106.N0428.N0765.N1572.d023751 eb kcoef r).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1634.d023651 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c) := hPeq ▸ hPexpr
  have hdenMeaning := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hden
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007741 10 hdenparts.1 hP)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007742 hdenparts.2 hP)
  have hF0expr := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hF0valid hr.2.2.2 hdenMeaning
  have hF0eq : (_root_.GD.N0106.N0428.N0765.N1634.d023650 c ^ 5 * Real.sqrt (_root_.GD.N0106.N0428.N0765.N1634.d023650 c)) /
      (_root_.GD.N0106.N0428.N0765.N1634.d023651 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c ^ 10 * Real.sqrt (_root_.GD.N0106.N0428.N0765.N1634.d023651 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c)) =
      _root_.GD.N0106.N0428.N0765.N1634.d023652 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c := by
    unfold _root_.GD.N0106.N0428.N0765.N1634.d023652
    rw [div_eq_mul_inv, one_div]
  have hF0 : (_root_.GD.N0106.N0428.N0765.N1572.d023752 eb kcoef r).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1634.d023652 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c) := hF0eq ▸ hF0expr
  have hF1 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hF1valid hr.1 hF0
  have hF0actual : (_root_.GD.N0106.N0428.N0765.N1572.d023752 eb kcoef r).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1616.d020957 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c) :=
    _root_.GD.N0106.N0428.N0765.N1634.d023662 _root_.GD.N0106.N0428.N0765.N1572.d023747 hu hv one_pos c ▸ hF0
  have hF1actual : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 r.lam (_root_.GD.N0106.N0428.N0765.N1572.d023752 eb kcoef r)).d007727
      _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1616.d020958 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c) :=
    _root_.GD.N0106.N0428.N0765.N1634.d023663 _root_.GD.N0106.N0428.N0765.N1572.d023747 hu hv one_pos c ▸ hF1
  exact ⟨_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 hs₀ hF0actual, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 hs₁ hF1actual⟩

def d023756 (eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457) (rows : List (_root_.GD.N0106.N0428.N0765.N1579.d007461 × ℝ)) (sums : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457) : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  rows.foldl (fun acc r => _root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef acc r.1) sums

theorem d023757 (eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457) (rows : List (_root_.GD.N0106.N0428.N0765.N1579.d007461 × ℝ))
    (sums : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457) (hv : _root_.GD.N0106.N0428.N0765.N1572.d023750 (_root_.GD.N0106.N0428.N0765.N1572.d023756 eb kcoef rows sums)) : _root_.GD.N0106.N0428.N0765.N1572.d023750 sums := by
  induction rows generalizing sums with
  | nil => exact hv
  | cons r rows ih =>
    exact _root_.GD.N0106.N0428.N0765.N1572.d023754 (ih (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef sums r.1) hv)



theorem d023758 (eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457) (rows : List (_root_.GD.N0106.N0428.N0765.N1579.d007461 × ℝ))
    {u v s₀ s₁ : ℝ} (hu : 0 ≤ u) (hv : 0 < v)
    (heb : eb.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 v) (hkcoef : kcoef.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 ((1 + _root_.GD.N0106.N0428.N0765.N1572.d023746) * u))
    (hrows : ∀ r, r ∈ rows → _root_.GD.N0106.N0428.N0765.N1581.d023723 r.1 r.2)
    (sums : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457) (hs₀ : sums.1.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 s₀) (hs₁ : sums.2.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 s₁)
    (hvalid : _root_.GD.N0106.N0428.N0765.N1572.d023750 (_root_.GD.N0106.N0428.N0765.N1572.d023756 eb kcoef rows sums)) :
    (_root_.GD.N0106.N0428.N0765.N1572.d023756 eb kcoef rows sums).1.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (s₀ + (rows.map (fun r => _root_.GD.N0106.N0428.N0765.N1616.d020957 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 r.2)).sum) ∧
    (_root_.GD.N0106.N0428.N0765.N1572.d023756 eb kcoef rows sums).2.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (s₁ + (rows.map (fun r => _root_.GD.N0106.N0428.N0765.N1616.d020958 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 r.2)).sum) := by
  induction rows generalizing sums s₀ s₁ with
  | nil => simpa only [_root_.GD.N0106.N0428.N0765.N1572.d023756, List.foldl_nil, List.map_nil, List.sum_nil, add_zero] using
      And.intro hs₀ hs₁
  | cons r rows ih =>
    have hstepvalid := _root_.GD.N0106.N0428.N0765.N1572.d023757 eb kcoef rows (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef sums r.1) hvalid
    have hstep := _root_.GD.N0106.N0428.N0765.N1572.d023755 hu hv heb hkcoef (hrows r (by simp)) hs₀ hs₁ hstepvalid
    have h := ih (fun q hq => hrows q (by simp only [List.mem_cons]; exact Or.inr hq))
      (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef sums r.1) hstep.1 hstep.2 hvalid
    simpa only [_root_.GD.N0106.N0428.N0765.N1572.d023756, List.foldl_cons, List.map_cons, List.sum_cons, add_assoc] using h

noncomputable def d023759 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : List (_root_.GD.N0106.N0428.N0765.N1579.d007461 × ℝ) :=
  List.ofFn (fun i : Fin 129 => (_root_.GD.N0106.N0428.N0765.N1581.d023710 cache i.val, _root_.GD.N0106.N0428.N0765.N1581.d023722 i.val))

theorem d023760 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hsize : cache.innerRows.size = 129) :
    (_root_.GD.N0106.N0428.N0765.N1572.d023759 cache).map Prod.fst = cache.innerRows.toList := by
  apply List.ext_getElem
  · simp only [_root_.GD.N0106.N0428.N0765.N1572.d023759, List.length_map, List.length_ofFn, Array.length_toList, hsize]
  · intro i hi hj
    have hI : i < cache.innerRows.size := by simpa only [Array.length_toList] using hj
    simp only [_root_.GD.N0106.N0428.N0765.N1572.d023759, List.getElem_map, List.getElem_ofFn]
    change _root_.GD.N0106.N0428.N0765.N1581.d023710 cache i = cache.innerRows[i]'hI
    unfold _root_.GD.N0106.N0428.N0765.N1581.d023710
    rw [getElem?_pos cache.innerRows i hI]
    rfl

theorem d023761 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hsize : cache.innerRows.size = 129)
    (eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457) (sums : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457) :
    _root_.GD.N0106.N0428.N0765.N1572.d023756 eb kcoef (_root_.GD.N0106.N0428.N0765.N1572.d023759 cache) sums =
      cache.innerRows.foldl (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef) sums := by
  have h := congrArg (fun rows : List _root_.GD.N0106.N0428.N0765.N1579.d007461 => rows.foldl (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef) sums)
    (_root_.GD.N0106.N0428.N0765.N1572.d023760 hsize)
  simpa only [_root_.GD.N0106.N0428.N0765.N1572.d023756, List.foldl_map, Array.foldl_toList] using h

theorem d023762 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (f : ℝ → ℝ) :
    ((_root_.GD.N0106.N0428.N0765.N1572.d023759 cache).map (fun r => f r.2)).sum =
      ∑ i ∈ Finset.range 129, f (_root_.GD.N0106.N0428.N0765.N1581.d023722 i) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1572.d023759, List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  exact (Finset.sum_range (fun i => f (_root_.GD.N0106.N0428.N0765.N1581.d023722 i))).symm



theorem d023763 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hcache : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true)
    (eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v)
    (heb : eb.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 v) (hkcoef : kcoef.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 ((1 + _root_.GD.N0106.N0428.N0765.N1572.d023746) * u))
    (hvalid : _root_.GD.N0106.N0428.N0765.N1572.d023750 (cache.innerRows.foldl (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef)
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007439, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439))) :
    (cache.innerRows.foldl (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef) (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007439, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439)).1.d007727
      _root_.GD.N0106.N0428.N0765.N1579.d007456 (∑ i ∈ Finset.range 129, _root_.GD.N0106.N0428.N0765.N1616.d020957 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 (_root_.GD.N0106.N0428.N0765.N1581.d023722 i)) ∧
    (cache.innerRows.foldl (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef) (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007439, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439)).2.d007727
      _root_.GD.N0106.N0428.N0765.N1579.d007456 (∑ i ∈ Finset.range 129, _root_.GD.N0106.N0428.N0765.N1616.d020958 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 (_root_.GD.N0106.N0428.N0765.N1581.d023722 i)) := by
  have hc := _root_.GD.N0106.N0428.N0765.N1581.d023726 hcache
  have hrows : ∀ r, r ∈ _root_.GD.N0106.N0428.N0765.N1572.d023759 cache → _root_.GD.N0106.N0428.N0765.N1581.d023723 r.1 r.2 := by
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hc.2.2.1 i
  have heq := _root_.GD.N0106.N0428.N0765.N1572.d023761 hc.2.1 eb kcoef (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007439, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439)
  have hv' : _root_.GD.N0106.N0428.N0765.N1572.d023750 (_root_.GD.N0106.N0428.N0765.N1572.d023756 eb kcoef (_root_.GD.N0106.N0428.N0765.N1572.d023759 cache)
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007439, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439)) := (congrArg _root_.GD.N0106.N0428.N0765.N1572.d023750 heq).mpr hvalid
  have h := _root_.GD.N0106.N0428.N0765.N1572.d023758 eb kcoef (_root_.GD.N0106.N0428.N0765.N1572.d023759 cache) hu hv heb hkcoef hrows
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007439, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439) (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007729 _root_.GD.N0106.N0428.N0765.N1579.d007456)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007729 _root_.GD.N0106.N0428.N0765.N1579.d007456) hv'
  rw [heq, _root_.GD.N0106.N0428.N0765.N1572.d023762, _root_.GD.N0106.N0428.N0765.N1572.d023762, zero_add, zero_add] at h
  exact h

theorem d023764 {n d : ℤ} (hd : 0 < d) : (_root_.GD.N0106.N0428.N0765.N1579.d007460 n d).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 ((n : ℝ) / (d : ℝ)) :=
  _root_.GD.N0106.N0428.N0765.N1548.d006926.d006964 _root_.GD.N0106.N0428.N0765.N1573.d022632 hd n

theorem d023765 : (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 4).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (1 / 4 : ℝ) := by
  simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 1) (d := 4) (by decide))

def d023766 (I : _root_.GD.N0106.N0428.N0765.N1579.d007457) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007448 _root_.GD.N0106.N0428.N0765.N1579.d007456
  (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007450 _root_.GD.N0106.N0428.N0765.N1579.d007456 I 10) (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007452 _root_.GD.N0106.N0428.N0765.N1579.d007456 I))

theorem d023767 {I : _root_.GD.N0106.N0428.N0765.N1579.d007457} {r : ℝ} (hr : 0 < r)
    (hv : (_root_.GD.N0106.N0428.N0765.N1572.d023766 I).valid = true) (hI : I.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 r) :
    (_root_.GD.N0106.N0428.N0765.N1572.d023766 I).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (r ^ (-((21 : ℝ) / 2))) := by
  have hmvalid := (Bool.and_eq_true_iff.mp hv).1
  have hm := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hmvalid
  have hden := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hmvalid
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007741 10 hm.1 hI) (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007742 hm.2 hI)
  have hout := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007739 hv hden
  exact _root_.GD.N0106.N0428.N0765.N1634.d023661 hr ▸ hout

def d023768 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (base : _root_.GD.N0106.N0428.N0765.N1579.d007457) (power : ℕ) (exponent denominator : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
        (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 4) (_root_.GD.N0106.N0428.N0765.N1572.d023766 base))
        (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007450 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 _root_.GD.N0106.N0428.N0765.N1579.d007459 (cache.d007468 (-260))) power))
      (cache.d007468 exponent))
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007444 _root_.GD.N0106.N0428.N0765.N1579.d007459 (cache.d007468 denominator))

noncomputable def d023769 (base : ℝ) (power : ℕ) (exponent denominator : ℤ) : ℝ :=
  ((1 / 4 : ℝ) * base ^ (-((21 : ℝ) / 2)) *
    (1 + Real.exp ((-260 : ℝ) / 16)) ^ power * Real.exp ((exponent : ℝ) / 16)) /
      (1 - Real.exp ((denominator : ℝ) / 16))

theorem d023770 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true)
    {base : _root_.GD.N0106.N0428.N0765.N1579.d007457} {r : ℝ} (hr : 0 < r) (hbase : base.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 r)
    (power : ℕ) (exponent denominator : ℤ)
    (he : -1690 ≤ exponent ∧ exponent ≤ 1690)
    (hd : -1690 ≤ denominator ∧ denominator ≤ 1690)
    (hvalid : (_root_.GD.N0106.N0428.N0765.N1572.d023768 cache base power exponent denominator).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1572.d023768 cache base power exponent denominator).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1572.d023769 r power exponent denominator) := by
  have hcache := (_root_.GD.N0106.N0428.N0765.N1581.d023726 hc).1
  have hparts := _root_.GD.N0106.N0428.N0765.N1572.d023749 hvalid
  have hnum := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hparts.1
  have hnum' := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hnum.1
  have hnum'' := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hnum'.1
  have hbasepow := _root_.GD.N0106.N0428.N0765.N1572.d023767 hr hnum''.2 hbase
  have hcommon := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 (hcache (-260) (by constructor <;> decide))
  have hpower := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007741 power hnum'.2 hcommon
  have hproduct := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hparts.1
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hnum.1
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hnum'.1 _root_.GD.N0106.N0428.N0765.N1572.d023765 hbasepow) hpower)
    (hcache exponent he)
  simpa only [_root_.GD.N0106.N0428.N0765.N1572.d023769, _root_.GD.N0106.N0428.N0765.N1572.d023768, Int.cast_neg, Int.cast_ofNat] using
    _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hvalid hproduct
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007734 _root_.GD.N0106.N0428.N0765.N1581.d023717 (hcache denominator hd))

noncomputable def d023771 (u v : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 129, (1 / 4 : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 (_root_.GD.N0106.N0428.N0765.N1581.d023722 i)
noncomputable def d023772 (u v : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 129, (1 / 4 : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020958 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 (_root_.GD.N0106.N0428.N0765.N1581.d023722 i)
noncomputable def d023773 (u v : ℝ) : ℝ := ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c
noncomputable def d023774 (u v : ℝ) : ℝ := ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 c
noncomputable def d023775 : ℝ := _root_.GD.N0106.N0428.N0765.N1562.d021061 (11 / 10) (1 / 4)

theorem d023776 (v : ℝ) : _root_.GD.N0106.N0428.N0765.N1619.d021056 _root_.GD.N0106.N0428.N0765.N1572.d023746 v 1 (-16) (1 / 4) 129 =
    _root_.GD.N0106.N0428.N0765.N1572.d023769 v 10 (-1430) (-22) + _root_.GD.N0106.N0428.N0765.N1572.d023769 _root_.GD.N0106.N0428.N0765.N1572.d023746 10 (-1430) (-22) := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1619.d021056, _root_.GD.N0106.N0428.N0765.N1568.d005509,
    _root_.GD.N0106.N0428.N0765.N1568.d005510, _root_.GD.N0106.N0428.N0765.N1572.d023769]
  ring

theorem d023777 (v : ℝ) : _root_.GD.N0106.N0428.N0765.N1619.d021057 _root_.GD.N0106.N0428.N0765.N1572.d023746 v 1 (-16) (1 / 4) 129 =
    _root_.GD.N0106.N0428.N0765.N1572.d023769 v 9 (-1690) (-26) + _root_.GD.N0106.N0428.N0765.N1572.d023769 _root_.GD.N0106.N0428.N0765.N1572.d023746 9 (-1430) (-22) := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1619.d021057, _root_.GD.N0106.N0428.N0765.N1568.d005509,
    _root_.GD.N0106.N0428.N0765.N1568.d005510, _root_.GD.N0106.N0428.N0765.N1572.d023769]
  ring

theorem d023778 (i : ℕ) : (-16 : ℝ) + (i : ℝ) * (1 / 4) = _root_.GD.N0106.N0428.N0765.N1581.d023722 i := by
  unfold _root_.GD.N0106.N0428.N0765.N1581.d023722
  ring

theorem d023779 {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) :
    _root_.GD.N0106.N0428.N0765.N1572.d023771 u v / (1 + _root_.GD.N0106.N0428.N0765.N1572.d023775) ≤ _root_.GD.N0106.N0428.N0765.N1572.d023773 u v ∧
    _root_.GD.N0106.N0428.N0765.N1572.d023773 u v ≤ (_root_.GD.N0106.N0428.N0765.N1572.d023771 u v +
      (_root_.GD.N0106.N0428.N0765.N1572.d023769 v 10 (-1430) (-22) + _root_.GD.N0106.N0428.N0765.N1572.d023769 _root_.GD.N0106.N0428.N0765.N1572.d023746 10 (-1430) (-22))) / (1 - _root_.GD.N0106.N0428.N0765.N1572.d023775) := by
  have hdpi : (11 / 10 : ℝ) < Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  have hrel := _root_.GD.N0106.N0428.N0765.N1562.d021065 _root_.GD.N0106.N0428.N0765.N1572.d023747 hu hv one_pos
    (by norm_num : (0 : ℝ) < 11 / 10) hdpi (by norm_num : (0 : ℝ) < 1 / 4) (-16)
  have hsum : (∑ i ∈ Finset.range 129, (1 / 4 : ℝ) *
      _root_.GD.N0106.N0428.N0765.N1616.d020957 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 (-16 + (i : ℝ) * (1 / 4))) = _root_.GD.N0106.N0428.N0765.N1572.d023771 u v := by
    simp only [_root_.GD.N0106.N0428.N0765.N1572.d023778, _root_.GD.N0106.N0428.N0765.N1572.d023771]
  have h := _root_.GD.N0106.N0428.N0765.N1569.d021054 _root_.GD.N0106.N0428.N0765.N1572.d023747 hu hv one_pos
    (by norm_num : (0 : ℝ) < 1 / 4) _root_.GD.N0106.N0428.N0765.N1560.d021075.1.le
    _root_.GD.N0106.N0428.N0765.N1560.d021075.2 hrel hsum.ge hsum.le
  change _root_.GD.N0106.N0428.N0765.N1572.d023771 u v / (1 + _root_.GD.N0106.N0428.N0765.N1572.d023775) ≤ _root_.GD.N0106.N0428.N0765.N1572.d023773 u v ∧
    _root_.GD.N0106.N0428.N0765.N1572.d023773 u v ≤ (_root_.GD.N0106.N0428.N0765.N1572.d023771 u v +
      _root_.GD.N0106.N0428.N0765.N1619.d021056 _root_.GD.N0106.N0428.N0765.N1572.d023746 v 1 (-16) (1 / 4) 129) / (1 - _root_.GD.N0106.N0428.N0765.N1572.d023775) at h
  rw [_root_.GD.N0106.N0428.N0765.N1572.d023776] at h
  exact h

theorem d023780 {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) :
    _root_.GD.N0106.N0428.N0765.N1572.d023772 u v / (1 + _root_.GD.N0106.N0428.N0765.N1572.d023775) ≤ _root_.GD.N0106.N0428.N0765.N1572.d023774 u v ∧
    _root_.GD.N0106.N0428.N0765.N1572.d023774 u v ≤ (_root_.GD.N0106.N0428.N0765.N1572.d023772 u v +
      (_root_.GD.N0106.N0428.N0765.N1572.d023769 v 9 (-1690) (-26) + _root_.GD.N0106.N0428.N0765.N1572.d023769 _root_.GD.N0106.N0428.N0765.N1572.d023746 9 (-1430) (-22))) / (1 - _root_.GD.N0106.N0428.N0765.N1572.d023775) := by
  have hdpi : (11 / 10 : ℝ) < Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  have hrel := _root_.GD.N0106.N0428.N0765.N1562.d021066 _root_.GD.N0106.N0428.N0765.N1572.d023747 hu hv one_pos
    (by norm_num : (0 : ℝ) < 11 / 10) hdpi (by norm_num : (0 : ℝ) < 1 / 4) (-16)
  have hsum : (∑ i ∈ Finset.range 129, (1 / 4 : ℝ) *
      _root_.GD.N0106.N0428.N0765.N1616.d020958 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 (-16 + (i : ℝ) * (1 / 4))) = _root_.GD.N0106.N0428.N0765.N1572.d023772 u v := by
    simp only [_root_.GD.N0106.N0428.N0765.N1572.d023778, _root_.GD.N0106.N0428.N0765.N1572.d023772]
  have h := _root_.GD.N0106.N0428.N0765.N1569.d021055 _root_.GD.N0106.N0428.N0765.N1572.d023747 hu hv one_pos
    (by norm_num : (0 : ℝ) < 1 / 4) _root_.GD.N0106.N0428.N0765.N1560.d021075.1.le
    _root_.GD.N0106.N0428.N0765.N1560.d021075.2 hrel hsum.ge hsum.le
  change _root_.GD.N0106.N0428.N0765.N1572.d023772 u v / (1 + _root_.GD.N0106.N0428.N0765.N1572.d023775) ≤ _root_.GD.N0106.N0428.N0765.N1572.d023774 u v ∧
    _root_.GD.N0106.N0428.N0765.N1572.d023774 u v ≤ (_root_.GD.N0106.N0428.N0765.N1572.d023772 u v +
      _root_.GD.N0106.N0428.N0765.N1619.d021057 _root_.GD.N0106.N0428.N0765.N1572.d023746 v 1 (-16) (1 / 4) 129) / (1 - _root_.GD.N0106.N0428.N0765.N1572.d023775) at h
  rw [_root_.GD.N0106.N0428.N0765.N1572.d023777] at h
  exact h

def d023781 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (S TL TR : _root_.GD.N0106.N0428.N0765.N1579.d007457) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007455
  (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 S (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 _root_.GD.N0106.N0428.N0765.N1579.d007459 cache.epsilon))
  (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 S TL) TR)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007444 _root_.GD.N0106.N0428.N0765.N1579.d007459 cache.epsilon))

theorem d023782 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} {S TL TR : _root_.GD.N0106.N0428.N0765.N1579.d007457}
    (hv : (_root_.GD.N0106.N0428.N0765.N1572.d023781 cache S TL TR).valid = true) : TL.valid = true ∧ TR.valid = true := by
  have hjoin := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1
  have hsum := (_root_.GD.N0106.N0428.N0765.N1572.d023749 hjoin.2).1
  have hparts := Bool.and_eq_true_iff.mp hsum
  exact ⟨(Bool.and_eq_true_iff.mp hparts.1).2, hparts.2⟩

theorem d023783 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true)
    {S TL TR : _root_.GD.N0106.N0428.N0765.N1579.d007457} {s tl tr I : ℝ}
    (hS : S.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 s) (hTL : TL.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 tl) (hTR : TR.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 tr)
    (hb : s / (1 + _root_.GD.N0106.N0428.N0765.N1572.d023775) ≤ I ∧ I ≤ (s + (tl + tr)) / (1 - _root_.GD.N0106.N0428.N0765.N1572.d023775))
    (hv : (_root_.GD.N0106.N0428.N0765.N1572.d023781 cache S TL TR).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1572.d023781 cache S TL TR).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 I := by
  have hjoin := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1
  have heps := (_root_.GD.N0106.N0428.N0765.N1581.d023726 hc).2.2.2
  have hlo := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hjoin.1 hS (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 heps)
  have hhi := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hjoin.2
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 hS hTL) hTR)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007734 _root_.GD.N0106.N0428.N0765.N1581.d023717 heps)
  have hb' : I ≤ ((s + tl) + tr) / (1 - _root_.GD.N0106.N0428.N0765.N1572.d023775) := by
    simpa only [add_assoc] using hb.2
  exact _root_.GD.N0106.N0428.N0765.N1579.d007436.d007746 hlo hhi hb.1 hb'

theorem d023784 {eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457} {sums : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457} {r : _root_.GD.N0106.N0428.N0765.N1579.d007461}
    (hv : _root_.GD.N0106.N0428.N0765.N1572.d023750 (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef sums r)) : eb.valid = true ∧ kcoef.valid = true := by
  have hF0valid : (_root_.GD.N0106.N0428.N0765.N1572.d023752 eb kcoef r).valid = true := (Bool.and_eq_true_iff.mp hv.1).2
  have hden := (_root_.GD.N0106.N0428.N0765.N1572.d023749 hF0valid).2
  have hpow := (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hden).1
  have hP : (_root_.GD.N0106.N0428.N0765.N1572.d023751 eb kcoef r).valid = true := (Bool.and_eq_true_iff.mp hpow).1
  have hparts := Bool.and_eq_true_iff.mp hP
  have hleft := Bool.and_eq_true_iff.mp hparts.1
  exact ⟨(_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hleft.1).1,
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hparts.2).1⟩

theorem d023785 (eb kcoef : _root_.GD.N0106.N0428.N0765.N1579.d007457) (rows : List (_root_.GD.N0106.N0428.N0765.N1579.d007461 × ℝ))
    (sums : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457) (hn : rows ≠ []) (hv : _root_.GD.N0106.N0428.N0765.N1572.d023750 (_root_.GD.N0106.N0428.N0765.N1572.d023756 eb kcoef rows sums)) :
    eb.valid = true ∧ kcoef.valid = true := by
  cases rows with
  | nil => exact False.elim (hn rfl)
  | cons r rows =>
    exact _root_.GD.N0106.N0428.N0765.N1572.d023784
      (_root_.GD.N0106.N0428.N0765.N1572.d023757 eb kcoef rows (_root_.GD.N0106.N0428.N0765.N1579.d007469 eb kcoef sums r.1) hv)

def d023786 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
  (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 _root_.GD.N0106.N0428.N0765.N1579.d007459 _root_.GD.N0106.N0428.N0765.N1579.d007458) (cache.d007468 a))
  (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 _root_.GD.N0106.N0428.N0765.N1579.d007459 (cache.d007468 b))
def d023787 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 × _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  cache.innerRows.foldl (_root_.GD.N0106.N0428.N0765.N1579.d007469 (cache.d007468 b) (_root_.GD.N0106.N0428.N0765.N1572.d023786 cache a b))
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007439, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439)
def d023788 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
  ⟨(_root_.GD.N0106.N0428.N0765.N1572.d023787 cache a b).1.interval,
    (_root_.GD.N0106.N0428.N0765.N1572.d023787 cache a b).1.valid && decide (cache.innerRows.size = 129)⟩ (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 4)
def d023789 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
  ⟨(_root_.GD.N0106.N0428.N0765.N1572.d023787 cache a b).2.interval,
    (_root_.GD.N0106.N0428.N0765.N1572.d023787 cache a b).2.valid && decide (cache.innerRows.size = 129)⟩ (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 4)
def d023790 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1572.d023781 cache (_root_.GD.N0106.N0428.N0765.N1572.d023788 cache a b)
  (_root_.GD.N0106.N0428.N0765.N1572.d023768 cache (cache.d007468 b) 10 (-1430) (-22))
  (_root_.GD.N0106.N0428.N0765.N1572.d023768 cache _root_.GD.N0106.N0428.N0765.N1579.d007458 10 (-1430) (-22))
def d023791 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1572.d023781 cache (_root_.GD.N0106.N0428.N0765.N1572.d023789 cache a b)
  (_root_.GD.N0106.N0428.N0765.N1572.d023768 cache (cache.d007468 b) 9 (-1690) (-26))
  (_root_.GD.N0106.N0428.N0765.N1572.d023768 cache _root_.GD.N0106.N0428.N0765.N1579.d007458 9 (-1430) (-22))
def d023792 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007454 _root_.GD.N0106.N0428.N0765.N1579.d007456
  (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1572.d023791 cache a b) (_root_.GD.N0106.N0428.N0765.N1572.d023790 cache a b))

theorem d023793 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).finite0 = _root_.GD.N0106.N0428.N0765.N1572.d023788 cache a b := rfl
theorem d023794 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).finite1 = _root_.GD.N0106.N0428.N0765.N1572.d023789 cache a b := rfl
theorem d023795 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).integral0 = _root_.GD.N0106.N0428.N0765.N1572.d023790 cache a b := rfl
theorem d023796 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).integral1 = _root_.GD.N0106.N0428.N0765.N1572.d023791 cache a b := rfl
theorem d023797 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) : (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).haar = _root_.GD.N0106.N0428.N0765.N1572.d023792 cache a b := rfl

theorem d023798 {r : _root_.GD.N0106.N0428.N0765.N1579.d007472} (hv : r.d007473 = true) :
    r.finite0.valid = true ∧ r.finite1.valid = true ∧
    r.integral0.valid = true ∧ r.integral1.valid = true ∧
    r.haar.valid = true ∧ r.risk.valid = true ∧
    0 < r.finite0.interval.lo ∧ 0 ≤ r.finite1.interval.lo ∧ 0 < r.integral0.interval.lo := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1579.d007472.d007473, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv

theorem d023799 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} {a b : ℤ}
    (hv0 : (_root_.GD.N0106.N0428.N0765.N1572.d023788 cache a b).valid = true)
    (hv1 : (_root_.GD.N0106.N0428.N0765.N1572.d023789 cache a b).valid = true) : _root_.GD.N0106.N0428.N0765.N1572.d023750 (_root_.GD.N0106.N0428.N0765.N1572.d023787 cache a b) := by
  exact ⟨(Bool.and_eq_true_iff.mp (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv0).1).1,
    (Bool.and_eq_true_iff.mp (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv1).1).1⟩

theorem d023800 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true) {a b : ℤ}
    (ha : -1690 ≤ a ∧ a ≤ 1690) (hb : -1690 ≤ b ∧ b ≤ 1690)
    (hv : (_root_.GD.N0106.N0428.N0765.N1572.d023786 cache a b).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1572.d023786 cache a b).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      ((1 + _root_.GD.N0106.N0428.N0765.N1572.d023746) * (Real.exp ((a : ℝ) / 16) * (1 + Real.exp ((b : ℝ) / 16)))) := by
  have hparts := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv
  have h := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hparts.1 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 _root_.GD.N0106.N0428.N0765.N1572.d023748)
      ((_root_.GD.N0106.N0428.N0765.N1581.d023726 hc).1 a ha))
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 ((_root_.GD.N0106.N0428.N0765.N1581.d023726 hc).1 b hb))
  have heq : (1 + _root_.GD.N0106.N0428.N0765.N1572.d023746) * Real.exp ((a : ℝ) / 16) * (1 + Real.exp ((b : ℝ) / 16)) =
      (1 + _root_.GD.N0106.N0428.N0765.N1572.d023746) * (Real.exp ((a : ℝ) / 16) * (1 + Real.exp ((b : ℝ) / 16))) := by ring
  exact heq ▸ h

theorem d023801 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true) {a b : ℤ}
    (ha : -1690 ≤ a ∧ a ≤ 1690) (hb : -1690 ≤ b ∧ b ≤ 1690)
    (hv0 : (_root_.GD.N0106.N0428.N0765.N1572.d023788 cache a b).valid = true) (hv1 : (_root_.GD.N0106.N0428.N0765.N1572.d023789 cache a b).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1572.d023788 cache a b).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1572.d023771 (Real.exp ((a : ℝ) / 16) * (1 + Real.exp ((b : ℝ) / 16))) (Real.exp ((b : ℝ) / 16))) ∧
    (_root_.GD.N0106.N0428.N0765.N1572.d023789 cache a b).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1572.d023772 (Real.exp ((a : ℝ) / 16) * (1 + Real.exp ((b : ℝ) / 16))) (Real.exp ((b : ℝ) / 16))) := by
  have hmeaning := _root_.GD.N0106.N0428.N0765.N1581.d023726 hc
  have hsvalid := _root_.GD.N0106.N0428.N0765.N1572.d023799 hv0 hv1
  have heq := _root_.GD.N0106.N0428.N0765.N1572.d023761 hmeaning.2.1 (cache.d007468 b) (_root_.GD.N0106.N0428.N0765.N1572.d023786 cache a b)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007439, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439)
  have hvfold : _root_.GD.N0106.N0428.N0765.N1572.d023750 (_root_.GD.N0106.N0428.N0765.N1572.d023756 (cache.d007468 b) (_root_.GD.N0106.N0428.N0765.N1572.d023786 cache a b) (_root_.GD.N0106.N0428.N0765.N1572.d023759 cache)
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007439, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439)) := (congrArg _root_.GD.N0106.N0428.N0765.N1572.d023750 heq).mpr hsvalid
  have hn : _root_.GD.N0106.N0428.N0765.N1572.d023759 cache ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    have hbad : (129 : ℕ) = 0 := by
      simpa only [_root_.GD.N0106.N0428.N0765.N1572.d023759, List.length_ofFn, List.length_nil] using hlen
    omega
  have hkvalid := (_root_.GD.N0106.N0428.N0765.N1572.d023785 (cache.d007468 b) (_root_.GD.N0106.N0428.N0765.N1572.d023786 cache a b) (_root_.GD.N0106.N0428.N0765.N1572.d023759 cache)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007439, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439) hn hvfold).2
  have hsums := _root_.GD.N0106.N0428.N0765.N1572.d023763 hc (cache.d007468 b) (_root_.GD.N0106.N0428.N0765.N1572.d023786 cache a b)
    (by positivity) (Real.exp_pos _) (hmeaning.1 b hb) (_root_.GD.N0106.N0428.N0765.N1572.d023800 hc ha hb hkvalid) hsvalid
  have h0 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv0 hsums.1 _root_.GD.N0106.N0428.N0765.N1572.d023765
  have h1 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv1 hsums.2 _root_.GD.N0106.N0428.N0765.N1572.d023765
  have sum0_eq (u v : ℝ) :
      (∑ i ∈ Finset.range 129, _root_.GD.N0106.N0428.N0765.N1616.d020957 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 (_root_.GD.N0106.N0428.N0765.N1581.d023722 i)) * (1 / 4 : ℝ) =
        _root_.GD.N0106.N0428.N0765.N1572.d023771 u v := by
    rw [_root_.GD.N0106.N0428.N0765.N1572.d023771, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have sum1_eq (u v : ℝ) :
      (∑ i ∈ Finset.range 129, _root_.GD.N0106.N0428.N0765.N1616.d020958 _root_.GD.N0106.N0428.N0765.N1572.d023746 u v 1 (_root_.GD.N0106.N0428.N0765.N1581.d023722 i)) * (1 / 4 : ℝ) =
        _root_.GD.N0106.N0428.N0765.N1572.d023772 u v := by
    rw [_root_.GD.N0106.N0428.N0765.N1572.d023772, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [sum0_eq] at h0
  rw [sum1_eq] at h1
  exact ⟨h0, h1⟩




theorem d023802 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true) {a b : ℤ}
    (ha : -1690 ≤ a ∧ a ≤ 1690) (hb : -1690 ≤ b ∧ b ≤ 1690)
    (hr : (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).d007473 = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).integral0.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1572.d023773 (Real.exp ((a : ℝ) / 16) * (1 + Real.exp ((b : ℝ) / 16)))
        (Real.exp ((b : ℝ) / 16))) ∧
    (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).integral1.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1572.d023774 (Real.exp ((a : ℝ) / 16) * (1 + Real.exp ((b : ℝ) / 16)))
        (Real.exp ((b : ℝ) / 16))) ∧
    (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).haar.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1529.d020799 _root_.GD.N0106.N0428.N0765.N1572.d023746 (_root_.GD.N0106.N0428.N0765.N1521.d020862 ((a : ℝ) / 16, (b : ℝ) / 16))) := by
  let u : ℝ := Real.exp ((a : ℝ) / 16) * (1 + Real.exp ((b : ℝ) / 16))
  let v : ℝ := Real.exp ((b : ℝ) / 16)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 < v := Real.exp_pos _
  have hr' := _root_.GD.N0106.N0428.N0765.N1572.d023798 hr
  have hfin := _root_.GD.N0106.N0428.N0765.N1572.d023801 hc ha hb hr'.1 hr'.2.1
  have hi0valid : (_root_.GD.N0106.N0428.N0765.N1572.d023790 cache a b).valid = true := hr'.2.2.1
  have hi1valid : (_root_.GD.N0106.N0428.N0765.N1572.d023791 cache a b).valid = true := hr'.2.2.2.1
  have hHvalid : (_root_.GD.N0106.N0428.N0765.N1572.d023792 cache a b).valid = true := hr'.2.2.2.2.1
  have hbgrid : (cache.d007468 b).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 v := (_root_.GD.N0106.N0428.N0765.N1581.d023726 hc).1 b hb
  have ht0valid := _root_.GD.N0106.N0428.N0765.N1572.d023782 hi0valid
  have ht1valid := _root_.GD.N0106.N0428.N0765.N1572.d023782 hi1valid
  have ht0L := _root_.GD.N0106.N0428.N0765.N1572.d023770 hc hv hbgrid 10 (-1430) (-22)
    (by constructor <;> decide) (by constructor <;> decide) ht0valid.1
  have ht0R := _root_.GD.N0106.N0428.N0765.N1572.d023770 hc _root_.GD.N0106.N0428.N0765.N1572.d023747 _root_.GD.N0106.N0428.N0765.N1572.d023748 10 (-1430) (-22)
    (by constructor <;> decide) (by constructor <;> decide) ht0valid.2
  have ht1L := _root_.GD.N0106.N0428.N0765.N1572.d023770 hc hv hbgrid 9 (-1690) (-26)
    (by constructor <;> decide) (by constructor <;> decide) ht1valid.1
  have ht1R := _root_.GD.N0106.N0428.N0765.N1572.d023770 hc _root_.GD.N0106.N0428.N0765.N1572.d023747 _root_.GD.N0106.N0428.N0765.N1572.d023748 9 (-1430) (-22)
    (by constructor <;> decide) (by constructor <;> decide) ht1valid.2
  have hi0 : (_root_.GD.N0106.N0428.N0765.N1572.d023790 cache a b).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1572.d023773 u v) :=
    _root_.GD.N0106.N0428.N0765.N1572.d023783 hc hfin.1 ht0L ht0R (_root_.GD.N0106.N0428.N0765.N1572.d023779 hu hv) hi0valid
  have hi1 : (_root_.GD.N0106.N0428.N0765.N1572.d023791 cache a b).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1572.d023774 u v) :=
    _root_.GD.N0106.N0428.N0765.N1572.d023783 hc hfin.2 ht1L ht1R (_root_.GD.N0106.N0428.N0765.N1572.d023780 hu hv) hi1valid
  have hdivvalid : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1572.d023791 cache a b) (_root_.GD.N0106.N0428.N0765.N1572.d023790 cache a b)).valid = true :=
    (Bool.and_eq_true_iff.mp hHvalid).1
  have hratio := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hdivvalid hi1 hi0
  have hmem := _root_.GD.N0106.N0428.N0765.N1534.d005345 _root_.GD.N0106.N0428.N0765.N1572.d023747 hu hv one_pos
  rw [_root_.GD.N0106.N0428.N0765.N1616.d020964 _root_.GD.N0106.N0428.N0765.N1572.d023747 hu hv one_pos] at hmem
  have hH := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007744 hHvalid hratio hmem.1.le hmem.2.le
  have heq : _root_.GD.N0106.N0428.N0765.N1572.d023774 u v / _root_.GD.N0106.N0428.N0765.N1572.d023773 u v =
      _root_.GD.N0106.N0428.N0765.N1529.d020799 _root_.GD.N0106.N0428.N0765.N1572.d023746 (_root_.GD.N0106.N0428.N0765.N1521.d020862 ((a : ℝ) / 16, (b : ℝ) / 16)) := by
    rw [_root_.GD.N0106.N0428.N0765.N1634.d023666 _root_.GD.N0106.N0428.N0765.N1572.d023747, _root_.GD.N0106.N0428.N0765.N1616.d020964 _root_.GD.N0106.N0428.N0765.N1572.d023747 hu hv one_pos]
    rfl
  exact ⟨hi0, hi1, heq ▸ hH⟩

theorem d023803 (a : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 a =
      (4849845 / 131072 : ℝ) * Real.sigmoid a * Real.sqrt (Real.sigmoid a) *
        (1 - Real.sigmoid a) ^ 10 := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005376 (by norm_num) (by norm_num),
    abs_of_pos (mul_pos (Real.sigmoid_pos a) (sub_pos.mpr (Real.sigmoid_lt_one a))),
    ProbabilityTheory.betaPDFReal,
    if_pos (And.intro (Real.sigmoid_pos a) (Real.sigmoid_lt_one a)),
    _root_.GD.N0106.N0428.N0765.N1539.d005359]
  norm_num only [show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num,
    show (10 : ℝ) - 1 = (9 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_ofNat]
  rw [← Real.sqrt_eq_rpow]
  ring

theorem d023804 (b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 b =
      630 * Real.sigmoid b ^ 5 * (1 - Real.sigmoid b) ^ 5 := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005376 (by norm_num) (by norm_num),
    abs_of_pos (mul_pos (Real.sigmoid_pos b) (sub_pos.mpr (Real.sigmoid_lt_one b))),
    _root_.GD.N0106.N0428.N0765.N1521.d020857 ⟨Real.sigmoid_pos b, Real.sigmoid_lt_one b⟩]
  ring



theorem d023805 {ea : _root_.GD.N0106.N0428.N0765.N1579.d007457} {a : ℝ}
    (hea : ea.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (Real.exp a)) (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007470 ea).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007470 ea).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 a) := by
  have hparts := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv
  have hleft := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hparts.1
  have hleft' := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hleft.1
  have ht := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hleft'.2 hea
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 hea)
  have ht' : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 ea (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 _root_.GD.N0106.N0428.N0765.N1579.d007459 ea)).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (Real.sigmoid a) := (_root_.GD.N0106.N0428.N0765.N1539.d005369 a).symm ▸ ht
  have hc : (_root_.GD.N0106.N0428.N0765.N1579.d007460 4849845 131072).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (4849845 / 131072 : ℝ) := by
    simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 4849845) (d := 131072) (by decide))
  have h := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hparts.1
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hleft.1 hc ht')
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007742 hleft.2 ht'))
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007741 10 hparts.2
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007734 _root_.GD.N0106.N0428.N0765.N1581.d023717 ht'))
  exact (_root_.GD.N0106.N0428.N0765.N1572.d023803 a).symm ▸ h


theorem d023806 {eb : _root_.GD.N0106.N0428.N0765.N1579.d007457} {b : ℝ}
    (heb : eb.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (Real.exp b)) (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007471 eb).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007471 eb).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 b) := by
  have hparts := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv
  have hleft := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hparts.1
  have htvalid := (Bool.and_eq_true_iff.mp hleft.2).1
  have ht := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 htvalid heb
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 heb)
  have ht' : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 eb (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 _root_.GD.N0106.N0428.N0765.N1579.d007459 eb)).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (Real.sigmoid b) := (_root_.GD.N0106.N0428.N0765.N1539.d005369 b).symm ▸ ht
  have hc : (_root_.GD.N0106.N0428.N0765.N1579.d007460 630 1).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (630 : ℝ) := by
    simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 630) (d := 1) (by decide))
  have h := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hparts.1 hc
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007741 5 hleft.2 ht'))
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007741 5 hparts.2
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007734 _root_.GD.N0106.N0428.N0765.N1581.d023717 ht'))
  exact (_root_.GD.N0106.N0428.N0765.N1572.d023804 b).symm ▸ h

def d023807 : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007448 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 _root_.GD.N0106.N0428.N0765.N1579.d007459 _root_.GD.N0106.N0428.N0765.N1579.d007458)
def d023808 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (b : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 (cache.d007468 b) (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 (cache.d007468 b) _root_.GD.N0106.N0428.N0765.N1579.d007458)
def d023809 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007444
  (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007453 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007444 (_root_.GD.N0106.N0428.N0765.N1572.d023808 cache b) _root_.GD.N0106.N0428.N0765.N1572.d023807))
  (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007453 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007444 (_root_.GD.N0106.N0428.N0765.N1572.d023792 cache a b) _root_.GD.N0106.N0428.N0765.N1572.d023807))
def d023810 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
  (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 _root_.GD.N0106.N0428.N0765.N1579.d007459 _root_.GD.N0106.N0428.N0765.N1579.d007458) (_root_.GD.N0106.N0428.N0765.N1579.d007460 11 1))
      (_root_.GD.N0106.N0428.N0765.N1579.d007470 (cache.d007468 a)))
    (_root_.GD.N0106.N0428.N0765.N1579.d007471 (cache.d007468 b))) (_root_.GD.N0106.N0428.N0765.N1572.d023809 cache a b)

theorem d023811 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (a b : ℤ) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).risk = _root_.GD.N0106.N0428.N0765.N1572.d023810 cache a b := by
  unfold _root_.GD.N0106.N0428.N0765.N1572.d023810 _root_.GD.N0106.N0428.N0765.N1572.d023809 _root_.GD.N0106.N0428.N0765.N1572.d023807 _root_.GD.N0106.N0428.N0765.N1572.d023808
  rw [← _root_.GD.N0106.N0428.N0765.N1572.d023797 cache a b]
  simp only [_root_.GD.N0106.N0428.N0765.N1579.d007474]




theorem d023812 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true) {a b : ℤ}
    (ha : -1690 ≤ a ∧ a ≤ 1690) (hb : -1690 ≤ b ∧ b ≤ 1690)
    (hr : (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).d007473 = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache a b).risk.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1549.d023700 _root_.GD.N0106.N0428.N0765.N1572.d023746 ((a : ℝ) / 16, (b : ℝ) / 16)) := by
  have hrisk : (_root_.GD.N0106.N0428.N0765.N1572.d023810 cache a b).valid = true := (_root_.GD.N0106.N0428.N0765.N1572.d023798 hr).2.2.2.2.2.1
  have hparts := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hrisk
  have hdparts := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hparts.1
  have hvparts := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hdparts.1
  have hgrid := (_root_.GD.N0106.N0428.N0765.N1581.d023726 hc).1
  have hda := _root_.GD.N0106.N0428.N0765.N1572.d023805 (hgrid a ha) hvparts.2
  have hdb := _root_.GD.N0106.N0428.N0765.N1572.d023806 (hgrid b hb) hdparts.2
  have h11 : (_root_.GD.N0106.N0428.N0765.N1579.d007460 11 1).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (11 : ℝ) := by
    simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 11) (d := 1) (by decide))
  have hV := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hvparts.1
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 _root_.GD.N0106.N0428.N0765.N1572.d023748) h11
  have hsq := Bool.and_eq_true_iff.mp hparts.2
  have hGsub := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hsq.1).1
  have hO : _root_.GD.N0106.N0428.N0765.N1572.d023807.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1607.d012678 _root_.GD.N0106.N0428.N0765.N1572.d023746) :=
    _root_.GD.N0106.N0428.N0765.N1579.d007436.d007739 hGsub.2 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 _root_.GD.N0106.N0428.N0765.N1572.d023748)
  have hGexpr := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hGsub.1 (hgrid b hb)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 (hgrid b hb) _root_.GD.N0106.N0428.N0765.N1572.d023748)
  have hG : (_root_.GD.N0106.N0428.N0765.N1572.d023808 cache b).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1529.d020800 _root_.GD.N0106.N0428.N0765.N1572.d023746
        (_root_.GD.N0106.N0428.N0765.N1521.d020862 ((a : ℝ) / 16, (b : ℝ) / 16))) :=
    (_root_.GD.N0106.N0428.N0765.N1549.d023702 _root_.GD.N0106.N0428.N0765.N1572.d023747 _ _).symm ▸ hGexpr
  have hH := (_root_.GD.N0106.N0428.N0765.N1572.d023802 hc ha hb hr).2.2
  have hgap : (_root_.GD.N0106.N0428.N0765.N1572.d023809 cache a b).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1529.d020802 _root_.GD.N0106.N0428.N0765.N1572.d023746
        (_root_.GD.N0106.N0428.N0765.N1521.d020862 ((a : ℝ) / 16, (b : ℝ) / 16))) :=
    _root_.GD.N0106.N0428.N0765.N1579.d007436.d007734
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007743 hsq.1 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007734 hG hO))
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007743 hsq.2 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007734 hH hO))
  have hout := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hrisk
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hparts.1
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hdparts.1 hV hda) hdb) hgap
  have heq : ((1 + _root_.GD.N0106.N0428.N0765.N1572.d023746) / 11 *
      _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 ((a : ℝ) / 16) *
      _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 ((b : ℝ) / 16)) *
      _root_.GD.N0106.N0428.N0765.N1529.d020802 _root_.GD.N0106.N0428.N0765.N1572.d023746 (_root_.GD.N0106.N0428.N0765.N1521.d020862 ((a : ℝ) / 16, (b : ℝ) / 16)) =
      _root_.GD.N0106.N0428.N0765.N1549.d023700 _root_.GD.N0106.N0428.N0765.N1572.d023746 ((a : ℝ) / 16, (b : ℝ) / 16) := by
    unfold _root_.GD.N0106.N0428.N0765.N1549.d023700 _root_.GD.N0106.N0428.N0765.N1521.d020868
    ring
  exact heq ▸ hout

noncomputable def d023813 (k : ℕ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1549.d023700 _root_.GD.N0106.N0428.N0765.N1572.d023746
    ((_root_.GD.N0106.N0428.N0765.N1579.d007476 k).1 / 16, (_root_.GD.N0106.N0428.N0765.N1579.d007476 k).2 / 16)

theorem d023814 {k : ℕ} (hk : k < _root_.GD.N0106.N0428.N0765.N1579.d007475) :
    (-1690 ≤ (_root_.GD.N0106.N0428.N0765.N1579.d007476 k).1 ∧ (_root_.GD.N0106.N0428.N0765.N1579.d007476 k).1 ≤ 1690) ∧
    (-1690 ≤ (_root_.GD.N0106.N0428.N0765.N1579.d007476 k).2 ∧ (_root_.GD.N0106.N0428.N0765.N1579.d007476 k).2 ≤ 1690) := by
  have hdiv : k / 161 < 281 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hk
  have hmod : k % 161 < 161 := Nat.mod_lt k (by decide)
  simp only [_root_.GD.N0106.N0428.N0765.N1579.d007476]
  omega

def d023815 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (first : ℕ) (offsets : List ℕ) (state : _root_.GD.N0106.N0428.N0765.N1579.d007477) : _root_.GD.N0106.N0428.N0765.N1579.d007477 :=
  offsets.foldl (fun acc offset =>
    let ab := _root_.GD.N0106.N0428.N0765.N1579.d007476 (first + offset)
    _root_.GD.N0106.N0428.N0765.N1579.d007479 acc (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache ab.1 ab.2)) state

theorem d023816 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (first : ℕ) (offsets : List ℕ)
    (state : _root_.GD.N0106.N0428.N0765.N1579.d007477) (hv : (_root_.GD.N0106.N0428.N0765.N1572.d023815 cache first offsets state).valid = true) :
    state.valid = true := by
  induction offsets generalizing state with
  | nil => exact hv
  | cons k offsets ih =>
    have h := ih (_root_.GD.N0106.N0428.N0765.N1579.d007479 state (_root_.GD.N0106.N0428.N0765.N1579.d007474 cache (_root_.GD.N0106.N0428.N0765.N1579.d007476 (first + k)).1
      (_root_.GD.N0106.N0428.N0765.N1579.d007476 (first + k)).2)) hv
    exact (Bool.and_eq_true_iff.mp h).1



theorem d023817 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true)
    (first : ℕ) (offsets : List ℕ)
    (hb : ∀ k, k ∈ offsets → first + k < _root_.GD.N0106.N0428.N0765.N1579.d007475)
    (state : _root_.GD.N0106.N0428.N0765.N1579.d007477) {s : ℝ} (hs : state.sum.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 s)
    (hv : (_root_.GD.N0106.N0428.N0765.N1572.d023815 cache first offsets state).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1572.d023815 cache first offsets state).sum.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (s + (offsets.map (fun k => _root_.GD.N0106.N0428.N0765.N1572.d023813 (first + k))).sum) := by
  induction offsets generalizing state s with
  | nil => simpa only [_root_.GD.N0106.N0428.N0765.N1572.d023815, List.foldl_nil, List.map_nil, List.sum_nil, add_zero] using hs
  | cons k offsets ih =>
    let r := _root_.GD.N0106.N0428.N0765.N1579.d007474 cache (_root_.GD.N0106.N0428.N0765.N1579.d007476 (first + k)).1 (_root_.GD.N0106.N0428.N0765.N1579.d007476 (first + k)).2
    have hvstep : (_root_.GD.N0106.N0428.N0765.N1579.d007479 state r).valid = true :=
      _root_.GD.N0106.N0428.N0765.N1572.d023816 cache first offsets (_root_.GD.N0106.N0428.N0765.N1579.d007479 state r) hv
    have hrv : r.d007473 = true := (Bool.and_eq_true_iff.mp hvstep).2
    have hab := _root_.GD.N0106.N0428.N0765.N1572.d023814 (hb k (by simp))
    have hrow : r.risk.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1572.d023813 (first + k)) :=
      _root_.GD.N0106.N0428.N0765.N1572.d023812 hc hab.1 hab.2 hrv
    have hacc : (_root_.GD.N0106.N0428.N0765.N1579.d007479 state r).sum.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (s + _root_.GD.N0106.N0428.N0765.N1572.d023813 (first + k)) :=
      _root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 hs hrow
    have h := ih (fun j hj => hb j (by simp only [List.mem_cons]; exact Or.inr hj))
      (_root_.GD.N0106.N0428.N0765.N1579.d007479 state r) hacc hv
    simpa only [_root_.GD.N0106.N0428.N0765.N1572.d023815, List.foldl_cons, List.map_cons, List.sum_cons, add_assoc] using h

theorem d023818 (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, Finset.sum_range_succ, ih]



theorem d023819 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true)
    (first count : ℕ) (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007480 cache first count).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007480 cache first count).sum.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (∑ i ∈ Finset.range count, _root_.GD.N0106.N0428.N0765.N1572.d023813 (first + i)) := by
  let initial : _root_.GD.N0106.N0428.N0765.N1579.d007477 := { _root_.GD.N0106.N0428.N0765.N1579.d007478 with valid := decide (first + count ≤ _root_.GD.N0106.N0428.N0765.N1579.d007475) }
  have hi : initial.valid = true := _root_.GD.N0106.N0428.N0765.N1572.d023816 cache first (List.range count) initial hv
  have hrange : first + count ≤ _root_.GD.N0106.N0428.N0765.N1579.d007475 := of_decide_eq_true hi
  have hb : ∀ k, k ∈ List.range count → first + k < _root_.GD.N0106.N0428.N0765.N1579.d007475 := by
    intro k hk
    have hk' := List.mem_range.mp hk
    omega
  have h := _root_.GD.N0106.N0428.N0765.N1572.d023817 hc first (List.range count) hb initial
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007729 _root_.GD.N0106.N0428.N0765.N1579.d007456) hv
  rw [zero_add, _root_.GD.N0106.N0428.N0765.N1572.d023818] at h
  exact h

theorem d023820 {I : _root_.GD.N0106.N0428.N0765.N1579.d007457} {s : ℝ} (hI : I.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 s)
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007481 I).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007481 I).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 ((1 / 16 : ℝ) ^ 2 * s) := by
  have hmesh : (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 256).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (1 / 256 : ℝ) := by
    simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 1) (d := 256) (by decide))
  have h := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv hI hmesh
  have heq : s * (1 / 256 : ℝ) = (1 / 16 : ℝ) ^ 2 * s := by ring
  exact heq ▸ h

theorem d023821 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true)
    (first count : ℕ) (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007480 cache first count).valid = true)
    (hf : (_root_.GD.N0106.N0428.N0765.N1579.d007481 (_root_.GD.N0106.N0428.N0765.N1579.d007480 cache first count).sum).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007481 (_root_.GD.N0106.N0428.N0765.N1579.d007480 cache first count).sum).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      ((1 / 16 : ℝ) ^ 2 * ∑ i ∈ Finset.range count, _root_.GD.N0106.N0428.N0765.N1572.d023813 (first + i)) :=
  _root_.GD.N0106.N0428.N0765.N1572.d023820 (_root_.GD.N0106.N0428.N0765.N1572.d023819 hc first count hv) hf



theorem d023822 {I : _root_.GD.N0106.N0428.N0765.N1579.d007457} {s x t p : ℝ}
    (hI : I.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 s)
    (ht : _root_.GD.N0106.N0428.N0765.N1582.d007423.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456 t)
    (hp : _root_.GD.N0106.N0428.N0765.N1582.d007424.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456 p)
    (herr : |x - s| ≤ t + p) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007482 I).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 x := by
  have he := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007732
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007728 ht) (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007728 hp)
  have hupper : t + p ≤
      ((_root_.GD.N0106.N0428.N0765.N1582.d007423.hi + _root_.GD.N0106.N0428.N0765.N1582.d007424.hi : ℤ) : ℝ) / (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) := he.2
  have hab := abs_le.mp herr
  have hlo : (I.interval.lo : ℝ) / (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) -
      ((_root_.GD.N0106.N0428.N0765.N1582.d007423.hi + _root_.GD.N0106.N0428.N0765.N1582.d007424.hi : ℤ) : ℝ) / (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) ≤ x := by
    linarith [hupper, hI.1, hab.1]
  have hhi : x ≤ (I.interval.hi : ℝ) / (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) +
      ((_root_.GD.N0106.N0428.N0765.N1582.d007423.hi + _root_.GD.N0106.N0428.N0765.N1582.d007424.hi : ℤ) : ℝ) / (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) := by
    linarith [hupper, hI.2, hab.2]
  change (((I.interval.lo - (_root_.GD.N0106.N0428.N0765.N1582.d007423.hi + _root_.GD.N0106.N0428.N0765.N1582.d007424.hi) : ℤ) : ℝ) /
      (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) ≤ x) ∧
    (x ≤ ((I.interval.hi + (_root_.GD.N0106.N0428.N0765.N1582.d007423.hi + _root_.GD.N0106.N0428.N0765.N1582.d007424.hi) : ℤ) : ℝ) /
      (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ))
  simpa only [Int.cast_sub, Int.cast_add, sub_div, add_div] using And.intro hlo hhi

end GD.N0106.N0428.N0765.N1572

#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023755
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023758
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023763
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023802
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023805
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023806
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023812
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023819
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023821
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023822











set_option autoImplicit false
set_option warningAsError true

namespace GD.N0106.N0428.N0765.N1572
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1579 _root_.GD.N0106.N0428.N0765.N1572 _root_.GD.N0106.N0428.N0765.N1582 _root_.GD.N0106.N0428.N0765.N1548

def d023823 : _root_.GD.N0106.N0428.N0765.N1579.d007472 := _root_.GD.N0106.N0428.N0765.N1579.d007474 _root_.GD.N0106.N0428.N0765.N1575.d007495 (-224) (-80)


theorem d023824 :
    _root_.GD.N0106.N0428.N0765.N1572.d023823.d007473 = true ∧
    _root_.GD.N0106.N0428.N0765.N1572.d023823.risk.interval = _root_.GD.N0106.N0428.N0765.N1579.d007487 ∧
    _root_.GD.N0106.N0428.N0765.N1572.d023823.finite0.interval = _root_.GD.N0106.N0428.N0765.N1579.d007489 ∧
    _root_.GD.N0106.N0428.N0765.N1572.d023823.finite1.interval = _root_.GD.N0106.N0428.N0765.N1579.d007490 := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1572.d023823, _root_.GD.N0106.N0428.N0765.N1579.d007491, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    using _root_.GD.N0106.N0428.N0765.N1576.d007496

theorem d023825 : _root_.GD.N0106.N0428.N0765.N1572.d023823.d007473 = true := _root_.GD.N0106.N0428.N0765.N1572.d023824.1


theorem d023826 :
    0 < _root_.GD.N0106.N0428.N0765.N1572.d023823.finite0.interval.lo ∧
    0 ≤ _root_.GD.N0106.N0428.N0765.N1572.d023823.finite1.interval.lo ∧
    0 < _root_.GD.N0106.N0428.N0765.N1572.d023823.integral0.interval.lo := by
  have h := _root_.GD.N0106.N0428.N0765.N1572.d023798 _root_.GD.N0106.N0428.N0765.N1572.d023825
  exact h.2.2.2.2.2.2

private theorem d023827 : (((-224 : ℤ) : ℝ) / 16) = -14 := by norm_num
private theorem d023828 : (((-80 : ℤ) : ℝ) / 16) = -5 := by norm_num



theorem d023829 :
    _root_.GD.N0106.N0428.N0765.N1572.d023823.integral0.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1572.d023773 (Real.exp (-14) * (1 + Real.exp (-5))) (Real.exp (-5))) ∧
    _root_.GD.N0106.N0428.N0765.N1572.d023823.integral1.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1572.d023774 (Real.exp (-14) * (1 + Real.exp (-5))) (Real.exp (-5))) ∧
    _root_.GD.N0106.N0428.N0765.N1572.d023823.haar.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1529.d020799 _root_.GD.N0106.N0428.N0765.N1572.d023746 (_root_.GD.N0106.N0428.N0765.N1521.d020862 (-14, -5))) := by
  have h := _root_.GD.N0106.N0428.N0765.N1572.d023802
    (cache := _root_.GD.N0106.N0428.N0765.N1575.d007495) _root_.GD.N0106.N0428.N0765.N1574.d023744
    (a := -224) (b := -80) (by constructor <;> norm_num)
    (by constructor <;> norm_num) _root_.GD.N0106.N0428.N0765.N1572.d023825
  simpa only [_root_.GD.N0106.N0428.N0765.N1572.d023823, _root_.GD.N0106.N0428.N0765.N1572.d023827, _root_.GD.N0106.N0428.N0765.N1572.d023828] using h


theorem d023830 :
    _root_.GD.N0106.N0428.N0765.N1579.d007487.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1549.d023700 _root_.GD.N0106.N0428.N0765.N1572.d023746 (-14, -5)) := by
  have h := _root_.GD.N0106.N0428.N0765.N1572.d023812
    (cache := _root_.GD.N0106.N0428.N0765.N1575.d007495) _root_.GD.N0106.N0428.N0765.N1574.d023744
    (a := -224) (b := -80) (by constructor <;> norm_num)
    (by constructor <;> norm_num) _root_.GD.N0106.N0428.N0765.N1572.d023825
  have hrow : _root_.GD.N0106.N0428.N0765.N1572.d023823.risk.interval.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1549.d023700 _root_.GD.N0106.N0428.N0765.N1572.d023746 (-14, -5)) := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1572.d023823, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007727, _root_.GD.N0106.N0428.N0765.N1572.d023827, _root_.GD.N0106.N0428.N0765.N1572.d023828] using h
  rw [_root_.GD.N0106.N0428.N0765.N1572.d023824.2.1] at hrow
  exact hrow



theorem d023831 :
    (544103433241753981386274152422214958247 : ℝ) / (2 : ℝ) ^ 192 ≤
      _root_.GD.N0106.N0428.N0765.N1549.d023700
        ((11530470130408281 : ℝ) / 10000000000000000) (-14, -5) ∧
    _root_.GD.N0106.N0428.N0765.N1549.d023700
        ((11530470130408281 : ℝ) / 10000000000000000) (-14, -5) ≤
      (544103497945438993474793380755872535319 : ℝ) / (2 : ℝ) ^ 192 := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1548.d006926.d006928, _root_.GD.N0106.N0428.N0765.N1579.d007487, _root_.GD.N0106.N0428.N0765.N1579.d007456, _root_.GD.N0106.N0428.N0765.N1582.d007417, _root_.GD.N0106.N0428.N0765.N1582.d007416,
    _root_.GD.N0106.N0428.N0765.N1572.d023746, _root_.GD.N0106.N0428.N0765.N1582.d007418, _root_.GD.N0106.N0428.N0765.N1582.d007419, Int.cast_pow, Int.cast_ofNat]
    using _root_.GD.N0106.N0428.N0765.N1572.d023830

end
end GD.N0106.N0428.N0765.N1572

#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023824
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023826
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023829
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023830
#print axioms _root_.GD.N0106.N0428.N0765.N1572.d023831
