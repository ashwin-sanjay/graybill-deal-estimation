import GD.Module1284
import GD.Module0905

















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0106.N0428.N0765.N1529
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1611 _root_.GD.N0106.N0428.N0765.N1606 _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1610 _root_.GD.N0106.N0428.N0765.N1633
open _root_.GD.N0235
open _root_.GD.N0228.N0547.N0791

abbrev d020796 := _root_.GD.N0106.N0428.N0765.N1611.d012588
abbrev d020797 := Fin 3 → ℝ
abbrev d020798 : Measure _root_.GD.N0106.N0428.N0765.N1529.d020797 := _root_.GD.N0235.d004250 ((3 : ℝ) / 2) 5 5


def d020799 (eta : ℝ) (p : _root_.GD.N0106.N0428.N0765.N1529.d020797) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1534.d005330 eta (p 0) (p 1) (p 2)

def d020800 (eta : ℝ) (p : _root_.GD.N0106.N0428.N0765.N1529.d020797) : ℝ := p 1 / (p 1 + eta * p 2)

def d020801 (eta : ℝ) (p : _root_.GD.N0106.N0428.N0765.N1529.d020797) : ℝ :=
  10 * (1 + eta) * p 0 / (p 1 + eta * p 2)


def d020802 (eta : ℝ) (p : _root_.GD.N0106.N0428.N0765.N1529.d020797) : ℝ :=
  (_root_.GD.N0106.N0428.N0765.N1529.d020800 eta p - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 -
    (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2


def d020803 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (p : _root_.GD.N0106.N0428.N0765.N1529.d020797) : ℝ :=
  if j.2 = 1 then _root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p) * _root_.GD.N0106.N0428.N0765.N1529.d020801 eta p
  else -_root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p)

def d020804 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (p : _root_.GD.N0106.N0428.N0765.N1529.d020797) : ℝ :=
  (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1529.d020803 j eta p

def d020805 (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (p : _root_.GD.N0106.N0428.N0765.N1529.d020797) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1529.d020803 i eta p * _root_.GD.N0106.N0428.N0765.N1529.d020803 j eta p


def d020806 (eta : ℝ) : ℝ :=
  ((1 + eta) / 11) * ∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020802 eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798

def d020807 (eta : ℝ) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) : ℝ :=
  ((1 + eta) / 11) * ∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020804 j eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798

def d020808 (eta : ℝ) (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) : ℝ :=
  ((1 + eta) / 11) * ∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020805 i j eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798



@[fun_prop] theorem d020809 (eta : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta) := by
  have hk : Measurable fun q : _root_.GD.N0106.N0428.N0765.N1529.d020797 × ℝ =>
      _root_.GD.N0106.N0428.N0765.N1534.d005329 eta (q.1 0) (q.1 1) (q.1 2) q.2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005329 _root_.GD.N0106.N0428.N0765.N1534.d005328
    fun_prop
  have hd : Measurable fun p : _root_.GD.N0106.N0428.N0765.N1529.d020797 =>
      ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1534.d005329 eta (p 0) (p 1) (p 2) l := by
    simp_rw [intervalIntegral.integral_of_le zero_le_one]
    exact hk.stronglyMeasurable.integral_prod_right'.measurable
  have hn : Measurable fun p : _root_.GD.N0106.N0428.N0765.N1529.d020797 =>
      ∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta (p 0) (p 1) (p 2) l := by
    simp_rw [intervalIntegral.integral_of_le zero_le_one]
    exact (measurable_snd.mul hk).stronglyMeasurable.integral_prod_right'.measurable
  exact hn.div hd

@[fun_prop] theorem d020810 (eta : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1529.d020800 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020800
  fun_prop

@[fun_prop] theorem d020811 (eta : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1529.d020801 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020801
  fun_prop

@[fun_prop] theorem d020812 (eta : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1529.d020802 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020802
  fun_prop

@[fun_prop] theorem d020813 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1529.d020803 j eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020803 _root_.GD.N0106.N0428.N0765.N1607.d012644
  split_ifs <;> fun_prop

@[fun_prop] theorem d020814 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1529.d020804 j eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020804
  fun_prop

@[fun_prop] theorem d020815 (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1529.d020805 i j eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020805
  fun_prop


theorem d020816 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1529.d020796) :
    _root_.GD.N0106.N0428.N0765.N1633.d014080 eta x 0 =
      _root_.GD.N0106.N0428.N0765.N1534.d005333 eta (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012591 x) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1633.d014080, _root_.GD.N0106.N0428.N0765.N1633.d014077, _root_.GD.N0106.N0428.N0765.N1606.d012619, _root_.GD.N0228.N0547.N0791.d012866,
    _root_.GD.N0228.N0547.N0791.d012864, Matrix.cons_val_zero, _root_.GD.N0106.N0428.N0765.N1534.d005333, _root_.GD.N0106.N0428.N0765.N1534.d005332,
    _root_.GD.N0106.N0428.N0765.N1633.d014073, _root_.GD.N0106.N0428.N0765.N1534.d005331, add_assoc]

theorem d020817 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1529.d020796) :
    _root_.GD.N0106.N0428.N0765.N1633.d014080 eta x 1 =
      _root_.GD.N0106.N0428.N0765.N1534.d005334 eta (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012591 x) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1633.d014080, _root_.GD.N0106.N0428.N0765.N1633.d014077, _root_.GD.N0106.N0428.N0765.N1606.d012619, _root_.GD.N0228.N0547.N0791.d012866,
    _root_.GD.N0228.N0547.N0791.d012864, Matrix.cons_val_one, Matrix.cons_val_zero, _root_.GD.N0106.N0428.N0765.N1534.d005334, _root_.GD.N0106.N0428.N0765.N1534.d005332,
    _root_.GD.N0106.N0428.N0765.N1633.d014073, _root_.GD.N0106.N0428.N0765.N1534.d005331, add_assoc]

theorem d020818 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1529.d020796) :
    _root_.GD.N0106.N0428.N0765.N1633.d014080 eta x 2 =
      _root_.GD.N0106.N0428.N0765.N1534.d005335 eta (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012591 x) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1633.d014080, _root_.GD.N0106.N0428.N0765.N1633.d014077, _root_.GD.N0106.N0428.N0765.N1606.d012619, _root_.GD.N0228.N0547.N0791.d012866,
    _root_.GD.N0228.N0547.N0791.d012864, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    _root_.GD.N0106.N0428.N0765.N1534.d005335, _root_.GD.N0106.N0428.N0765.N1534.d005332,
    _root_.GD.N0106.N0428.N0765.N1633.d014073, _root_.GD.N0106.N0428.N0765.N1534.d005331, add_assoc]



theorem d020819 (eta : ℝ) (heta : 0 < eta)
    (x : _root_.GD.N0106.N0428.N0765.N1529.d020796) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) = _root_.GD.N0106.N0428.N0765.N1607.d012641 x := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020799, _root_.GD.N0106.N0428.N0765.N1529.d020816, _root_.GD.N0106.N0428.N0765.N1529.d020817, _root_.GD.N0106.N0428.N0765.N1529.d020818]
  exact (_root_.GD.N0106.N0428.N0765.N1534.d005340 heta (hx 0) (hx 1)).symm

theorem d020820 (eta : ℝ) (heta : 0 < eta)
    (x : _root_.GD.N0106.N0428.N0765.N1529.d020796) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1529.d020800 eta (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) = _root_.GD.N0106.N0428.N0765.N1610.d020749 x := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020800, _root_.GD.N0106.N0428.N0765.N1529.d020817, _root_.GD.N0106.N0428.N0765.N1529.d020818]
  exact (_root_.GD.N0106.N0428.N0765.N1534.d005342 (Δ := _root_.GD.N0106.N0428.N0765.N1611.d012591 x) heta (hx 0) (hx 1)).symm

theorem d020821 (eta : ℝ) (heta : 0 < eta)
    (x : _root_.GD.N0106.N0428.N0765.N1529.d020796) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) = _root_.GD.N0106.N0428.N0765.N1607.d012642 x := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020801, _root_.GD.N0106.N0428.N0765.N1529.d020816, _root_.GD.N0106.N0428.N0765.N1529.d020817, _root_.GD.N0106.N0428.N0765.N1529.d020818]
  exact (_root_.GD.N0106.N0428.N0765.N1534.d005343 heta (hx 0) (hx 1)).symm

theorem d020822 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (heta : 0 < eta)
    (x : _root_.GD.N0106.N0428.N0765.N1529.d020796) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1529.d020803 j eta (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) = _root_.GD.N0106.N0428.N0765.N1607.d012645 j x := by
  simp only [_root_.GD.N0106.N0428.N0765.N1529.d020803, _root_.GD.N0106.N0428.N0765.N1529.d020819 eta heta x hx,
    _root_.GD.N0106.N0428.N0765.N1529.d020821 eta heta x hx, _root_.GD.N0106.N0428.N0765.N1607.d012645]

theorem d020823 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (heta : 0 < eta)
    (x : _root_.GD.N0106.N0428.N0765.N1529.d020796) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1529.d020804 j eta (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) =
      (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020804, _root_.GD.N0106.N0428.N0765.N1529.d020819 eta heta x hx,
    _root_.GD.N0106.N0428.N0765.N1529.d020822 j eta heta x hx]

theorem d020824 (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (heta : 0 < eta)
    (x : _root_.GD.N0106.N0428.N0765.N1529.d020796) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1529.d020805 i j eta (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) = _root_.GD.N0106.N0428.N0765.N1607.d012645 i x * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020805, _root_.GD.N0106.N0428.N0765.N1529.d020822 i eta heta x hx,
    _root_.GD.N0106.N0428.N0765.N1529.d020822 j eta heta x hx]

theorem d020825 (eta : ℝ) (heta : 0 < eta)
    (x : _root_.GD.N0106.N0428.N0765.N1529.d020796) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1529.d020802 eta (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) =
      (_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020802, _root_.GD.N0106.N0428.N0765.N1529.d020820 eta heta x hx,
    _root_.GD.N0106.N0428.N0765.N1529.d020819 eta heta x hx]




theorem d020826 (location eta : ℝ) (heta : 0 < eta)
    (f : _root_.GD.N0106.N0428.N0765.N1529.d020797 → ℝ) (hf : Measurable f) (g : _root_.GD.N0106.N0428.N0765.N1529.d020796 → ℝ)
    (hfg : ∀ x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594, f (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) = g x)
    (hg : Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * g x) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta)) :
    Integrable f _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  have hc : Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * f (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x))
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    apply hg.congr
    filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
    rw [hfg x hx]
  have hs : Integrable (fun x => f (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x)) (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta) :=
    (_root_.GD.N0106.N0428.N0765.N1633.d014098 location eta heta _).2 hc
  have hm := (integrable_map_measure hf.aestronglyMeasurable
    (_root_.GD.N0106.N0428.N0765.N1633.d014085 eta).aemeasurable).2 hs
  rw [_root_.GD.N0106.N0428.N0765.N1633.d014101 location eta heta] at hm
  exact hm


theorem d020827 (location eta : ℝ) (heta : 0 < eta)
    (f : _root_.GD.N0106.N0428.N0765.N1529.d020797 → ℝ) (hf : Measurable f) (g : _root_.GD.N0106.N0428.N0765.N1529.d020796 → ℝ)
    (hfg : ∀ x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594, f (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) = g x)
    (hg : Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * g x) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta)) :
    (∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * g x ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) =
      ((1 + eta) / 11) * ∫ p, f p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  have hi := _root_.GD.N0106.N0428.N0765.N1529.d020826 location eta heta f hf g hfg hg
  calc
    (∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * g x ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) =
        ∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * f (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
      rw [hfg x hx]
    _ = ((1 + eta) / 11) * ∫ p, f p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 :=
      (_root_.GD.N0106.N0428.N0765.N1633.d014104 location eta heta f hi).2


theorem d020828 (location eta : ℝ) (heta : 0 < eta) :
    Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 *
      ((_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2))
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1610.d020785 location eta heta).integrable_sq.sub'
    (_root_.GD.N0106.N0428.N0765.N1607.d012681 location eta heta).integrable_sq
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020783 _root_.GD.N0106.N0428.N0765.N1607.d012679
  ring


theorem d020829 (eta : ℝ) (heta : 0 < eta) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1529.d020802 eta) _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
  _root_.GD.N0106.N0428.N0765.N1529.d020826 0 eta heta _ (_root_.GD.N0106.N0428.N0765.N1529.d020812 eta) _
    (_root_.GD.N0106.N0428.N0765.N1529.d020825 eta heta) (_root_.GD.N0106.N0428.N0765.N1529.d020828 0 eta heta)


theorem d020830 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (heta : 0 < eta) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1529.d020804 j eta) _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  apply _root_.GD.N0106.N0428.N0765.N1529.d020826 0 eta heta _ (_root_.GD.N0106.N0428.N0765.N1529.d020814 j eta) _
    (_root_.GD.N0106.N0428.N0765.N1529.d020823 j eta heta)
  convert _root_.GD.N0106.N0428.N0765.N1607.d012682 0 eta heta j using 1 <;> simp only [mul_assoc]

theorem d020831 (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (heta : 0 < eta) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1529.d020805 i j eta) _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  apply _root_.GD.N0106.N0428.N0765.N1529.d020826 0 eta heta _ (_root_.GD.N0106.N0428.N0765.N1529.d020815 i j eta) _
    (_root_.GD.N0106.N0428.N0765.N1529.d020824 i j eta heta)
  convert _root_.GD.N0106.N0428.N0765.N1607.d012676 0 eta heta i j using 1 <;> simp only [mul_assoc]


theorem d020832 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) -
        _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 =
      ((1 + eta) / 11) * ∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020802 eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  have heq := _root_.GD.N0106.N0428.N0765.N1529.d020827 location eta heta _
    (_root_.GD.N0106.N0428.N0765.N1529.d020812 eta) _ (_root_.GD.N0106.N0428.N0765.N1529.d020825 eta heta)
    (_root_.GD.N0106.N0428.N0765.N1529.d020828 location eta heta)
  have hr := _root_.GD.N0106.N0428.N0765.N1610.d020793 location eta heta
  have hneg : (∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 *
      ((_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2)
      ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) =
      -(∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 *
        ((_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2)
        ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  rw [hneg] at heq
  linarith only [heq, hr]


theorem d020833 (location eta : ℝ) (heta : 0 < eta)
    (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    _root_.GD.N0106.N0428.N0765.N1607.d012683 location eta j =
      ((1 + eta) / 11) * ∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020804 j eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  have hi : Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 *
      ((_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x)) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    convert _root_.GD.N0106.N0428.N0765.N1607.d012682 location eta heta j using 1 <;> simp only [mul_assoc]
  have h := _root_.GD.N0106.N0428.N0765.N1529.d020827 location eta heta _
    (_root_.GD.N0106.N0428.N0765.N1529.d020814 j eta) _ (_root_.GD.N0106.N0428.N0765.N1529.d020823 j eta heta) hi
  simpa only [_root_.GD.N0106.N0428.N0765.N1607.d012683, mul_assoc] using h

theorem d020834 (location eta : ℝ) (heta : 0 < eta)
    (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    _root_.GD.N0106.N0428.N0765.N1607.d012677 location eta i j =
      ((1 + eta) / 11) * ∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020805 i j eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  have hi : Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * (_root_.GD.N0106.N0428.N0765.N1607.d012645 i x * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x))
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    convert _root_.GD.N0106.N0428.N0765.N1607.d012676 location eta heta i j using 1 <;> simp only [mul_assoc]
  have h := _root_.GD.N0106.N0428.N0765.N1529.d020827 location eta heta _
    (_root_.GD.N0106.N0428.N0765.N1529.d020815 i j eta) _ (_root_.GD.N0106.N0428.N0765.N1529.d020824 i j eta heta) hi
  simpa only [_root_.GD.N0106.N0428.N0765.N1607.d012677, mul_assoc] using h


theorem d020835 (location eta : ℝ) (heta : 0 < eta) (a : Fin 5) :
    _root_.GD.N0106.N0428.N0765.N1607.d012683 location eta (a, 1) = ((1 + eta) / 11) *
      ∫ p, (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) *
        _root_.GD.N0106.N0428.N0765.N1607.d012644 a (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p) * _root_.GD.N0106.N0428.N0765.N1529.d020801 eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020833 location eta heta]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    simp only [_root_.GD.N0106.N0428.N0765.N1529.d020804, _root_.GD.N0106.N0428.N0765.N1529.d020803, if_pos rfl, ite_true]
    ring


theorem d020836 (location eta : ℝ) (heta : 0 < eta) (a : Fin 5) :
    _root_.GD.N0106.N0428.N0765.N1607.d012683 location eta (a, 0) = -((1 + eta) / 11) *
      ∫ p, (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1607.d012644 a (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p)
        ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020833 location eta heta]
  have hf : (fun p => _root_.GD.N0106.N0428.N0765.N1529.d020804 (a, 0) eta p) =
      fun p => -((_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1607.d012644 a (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p)) := by
    funext p
    simp only [_root_.GD.N0106.N0428.N0765.N1529.d020804, _root_.GD.N0106.N0428.N0765.N1529.d020803, if_neg (by decide : (0 : Fin 2) ≠ 1)]
    ring
  rw [hf, integral_neg]
  ring


theorem d020837 (location eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) - _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 =
      2 * (∑ j, b j * _root_.GD.N0106.N0428.N0765.N1529.d020807 eta j) +
        ∑ i, ∑ j, b i * b j * _root_.GD.N0106.N0428.N0765.N1529.d020808 eta i j := by
  rw [_root_.GD.N0106.N0428.N0765.N1610.d020779 location eta heta]
  simp only [_root_.GD.N0106.N0428.N0765.N1529.d020807, _root_.GD.N0106.N0428.N0765.N1529.d020808,
    _root_.GD.N0106.N0428.N0765.N1529.d020833 location eta heta, _root_.GD.N0106.N0428.N0765.N1529.d020834 location eta heta]


theorem d020838 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) -
        _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 = _root_.GD.N0106.N0428.N0765.N1529.d020806 eta :=
  _root_.GD.N0106.N0428.N0765.N1529.d020832 location eta heta



theorem d020839 (location eta : ℝ) (heta : 0 < eta) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1529.d020802 eta) _root_.GD.N0106.N0428.N0765.N1529.d020798 ∧
    (∀ j, Integrable (_root_.GD.N0106.N0428.N0765.N1529.d020804 j eta) _root_.GD.N0106.N0428.N0765.N1529.d020798) ∧
    (∀ i j, Integrable (_root_.GD.N0106.N0428.N0765.N1529.d020805 i j eta) _root_.GD.N0106.N0428.N0765.N1529.d020798) ∧
    (_root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) -
      _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 = _root_.GD.N0106.N0428.N0765.N1529.d020806 eta) ∧
    (∀ j, _root_.GD.N0106.N0428.N0765.N1607.d012683 location eta j = _root_.GD.N0106.N0428.N0765.N1529.d020807 eta j) ∧
    (∀ i j, _root_.GD.N0106.N0428.N0765.N1607.d012677 location eta i j = _root_.GD.N0106.N0428.N0765.N1529.d020808 eta i j) ∧
    (∀ x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594,
      _root_.GD.N0106.N0428.N0765.N1607.d012641 x = _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) ∧
      _root_.GD.N0106.N0428.N0765.N1610.d020749 x = _root_.GD.N0106.N0428.N0765.N1529.d020800 eta (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x) ∧
      _root_.GD.N0106.N0428.N0765.N1607.d012642 x = _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1633.d014080 eta x)) ∧
    (∀ b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ,
      _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) - _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 =
        2 * (∑ j, b j * _root_.GD.N0106.N0428.N0765.N1529.d020807 eta j) +
          ∑ i, ∑ j, b i * b j * _root_.GD.N0106.N0428.N0765.N1529.d020808 eta i j) := by
  exact ⟨_root_.GD.N0106.N0428.N0765.N1529.d020829 eta heta,
    fun j => _root_.GD.N0106.N0428.N0765.N1529.d020830 j eta heta,
    fun i j => _root_.GD.N0106.N0428.N0765.N1529.d020831 i j eta heta,
    _root_.GD.N0106.N0428.N0765.N1529.d020838 location eta heta,
    fun j => _root_.GD.N0106.N0428.N0765.N1529.d020833 location eta heta j,
    fun i j => _root_.GD.N0106.N0428.N0765.N1529.d020834 location eta heta i j,
    fun x hx => ⟨(_root_.GD.N0106.N0428.N0765.N1529.d020819 eta heta x hx).symm,
      (_root_.GD.N0106.N0428.N0765.N1529.d020820 eta heta x hx).symm,
      (_root_.GD.N0106.N0428.N0765.N1529.d020821 eta heta x hx).symm⟩,
    _root_.GD.N0106.N0428.N0765.N1529.d020837 location eta heta⟩

end
end GD.N0106.N0428.N0765.N1529

#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020809
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020819
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020820
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020821
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020826
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020827
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020829
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020830
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020831
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020832
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020833
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020835
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020836
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020834
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020837
#print axioms _root_.GD.N0106.N0428.N0765.N1529.d020839
