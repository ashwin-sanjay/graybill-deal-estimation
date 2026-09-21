import Mathlib






















namespace GD
namespace N0232
namespace N0720
namespace N1437

noncomputable section




def d002996 (vx vy : ℝ) : ℝ :=
  vy / (vx + vy)


def d002997 (xbar ybar vx vy : ℝ) : ℝ :=
  (xbar - ybar) ^ 2 / (vx + vy)


def d002998
    (g : ℝ → ℝ → ℝ) (xbar ybar vx vy : ℝ) : ℝ :=
  ybar + (xbar - ybar) *
    g (_root_.GD.N0232.N0720.N1437.d002996 vx vy)
      (_root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy)


def d002999
    (shift dilation : ℝ) (xbar ybar vx vy : ℝ) :
    ℝ × ℝ × ℝ × ℝ :=
  (shift + dilation * xbar,
    shift + dilation * ybar,
    dilation ^ 2 * vx,
    dilation ^ 2 * vy)


def d003000
    (d : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ shift dilation xbar ybar vx vy,
    0 < dilation →
      d (shift + dilation * xbar) (shift + dilation * ybar)
          (dilation ^ 2 * vx) (dilation ^ 2 * vy) =
        shift + dilation * d xbar ybar vx vy


theorem d003001
    (dilation vx vy : ℝ) (hdilation : dilation ≠ 0) :
    _root_.GD.N0232.N0720.N1437.d002996 (dilation ^ 2 * vx) (dilation ^ 2 * vy) =
      _root_.GD.N0232.N0720.N1437.d002996 vx vy := by
  unfold _root_.GD.N0232.N0720.N1437.d002996
  have hdilationSq : dilation ^ 2 ≠ 0 := pow_ne_zero 2 hdilation
  rw [← mul_add]
  exact mul_div_mul_left vy (vx + vy) hdilationSq



theorem d003002
    (shift dilation xbar ybar vx vy : ℝ)
    (hdilation : dilation ≠ 0) :
    _root_.GD.N0232.N0720.N1437.d002997
        (shift + dilation * xbar) (shift + dilation * ybar)
        (dilation ^ 2 * vx) (dilation ^ 2 * vy) =
      _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy := by
  unfold _root_.GD.N0232.N0720.N1437.d002997
  have hdilationSq : dilation ^ 2 ≠ 0 := pow_ne_zero 2 hdilation
  have hmean :
      (shift + dilation * xbar) - (shift + dilation * ybar) =
        dilation * (xbar - ybar) := by ring
  rw [hmean, mul_pow, ← mul_add]
  exact mul_div_mul_left ((xbar - ybar) ^ 2) (vx + vy) hdilationSq



theorem d003003
    (g : ℝ → ℝ → ℝ) :
    _root_.GD.N0232.N0720.N1437.d003000 (_root_.GD.N0232.N0720.N1437.d002998 g) := by
  intro shift dilation xbar ybar vx vy hdilation
  unfold _root_.GD.N0232.N0720.N1437.d002998
  rw [_root_.GD.N0232.N0720.N1437.d003001 dilation vx vy hdilation.ne',
    _root_.GD.N0232.N0720.N1437.d003002 shift dilation xbar ybar vx vy hdilation.ne']
  ring





def d003004 (vx vy : ℝ) : Prop :=
  0 < vx ∧ 0 < vy


theorem d003005
    (dilation vx vy : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0720.N1437.d003004 (dilation ^ 2 * vx) (dilation ^ 2 * vy) ↔
      _root_.GD.N0232.N0720.N1437.d003004 vx vy := by
  have hsquare : 0 < dilation ^ 2 := sq_pos_of_pos hdilation
  unfold _root_.GD.N0232.N0720.N1437.d003004
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : 0 < vx := by
      rcases (mul_pos_iff.mp hx) with hpos | hneg
      · exact hpos.2
      · exact False.elim ((not_lt_of_ge hsquare.le) hneg.1)
    have hy' : 0 < vy := by
      rcases (mul_pos_iff.mp hy) with hpos | hneg
      · exact hpos.2
      · exact False.elim ((not_lt_of_ge hsquare.le) hneg.1)
    exact ⟨hx', hy'⟩
  · rintro ⟨hx, hy⟩
    exact ⟨mul_pos hsquare hx, mul_pos hsquare hy⟩



def d003006
    (g : ℝ → ℝ → ℝ)
    (fallback : ℝ → ℝ → ℝ → ℝ → ℝ)
    (xbar ybar vx vy : ℝ) : ℝ :=
  by
    classical
    exact if _root_.GD.N0232.N0720.N1437.d003004 vx vy then
      _root_.GD.N0232.N0720.N1437.d002998 g xbar ybar vx vy
    else
      fallback xbar ybar vx vy




theorem d003007
    (g : ℝ → ℝ → ℝ)
    (fallback : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hfallback : _root_.GD.N0232.N0720.N1437.d003000 fallback) :
    _root_.GD.N0232.N0720.N1437.d003000
      (_root_.GD.N0232.N0720.N1437.d003006 g fallback) := by
  intro shift dilation xbar ybar vx vy hdilation
  have hstratum :=
    _root_.GD.N0232.N0720.N1437.d003005 dilation vx vy hdilation
  by_cases hpositive : _root_.GD.N0232.N0720.N1437.d003004 vx vy
  · have hpositive' :
        _root_.GD.N0232.N0720.N1437.d003004 (dilation ^ 2 * vx) (dilation ^ 2 * vy) :=
      hstratum.mpr hpositive
    simp only [_root_.GD.N0232.N0720.N1437.d003006, if_pos hpositive,
      if_pos hpositive']
    exact _root_.GD.N0232.N0720.N1437.d003003 g shift dilation xbar ybar vx vy hdilation
  · have hpositive' :
        ¬ _root_.GD.N0232.N0720.N1437.d003004
          (dilation ^ 2 * vx) (dilation ^ 2 * vy) := by
      exact fun h ↦ hpositive (hstratum.mp h)
    simp only [_root_.GD.N0232.N0720.N1437.d003006, if_neg hpositive,
      if_neg hpositive']
    exact hfallback shift dilation xbar ybar vx vy hdilation


def d003008 (_xbar ybar _vx _vy : ℝ) : ℝ :=
  ybar

theorem d003009 :
    _root_.GD.N0232.N0720.N1437.d003000 _root_.GD.N0232.N0720.N1437.d003008 := by
  intro shift dilation xbar ybar vx vy hdilation
  rfl



def d003010
    (g : ℝ → ℝ → ℝ) (xbar ybar vx vy : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1437.d003006 g _root_.GD.N0232.N0720.N1437.d003008 xbar ybar vx vy



theorem d003011
    (g : ℝ → ℝ → ℝ) :
    _root_.GD.N0232.N0720.N1437.d003000 (_root_.GD.N0232.N0720.N1437.d003010 g) :=
  _root_.GD.N0232.N0720.N1437.d003007 g _root_.GD.N0232.N0720.N1437.d003008
    _root_.GD.N0232.N0720.N1437.d003009





def d003012 (vx vy : ℝ) : Prop :=
  vx + vy ≠ 0



theorem d003013
    (dilation vx vy : ℝ) (hdilation : dilation ≠ 0) :
    _root_.GD.N0232.N0720.N1437.d003012 (dilation ^ 2 * vx) (dilation ^ 2 * vy) ↔
      _root_.GD.N0232.N0720.N1437.d003012 vx vy := by
  unfold _root_.GD.N0232.N0720.N1437.d003012
  rw [← mul_add]
  exact mul_ne_zero_iff_left (pow_ne_zero 2 hdilation)



def d003014 (xbar ybar _vx _vy : ℝ) : ℝ :=
  (xbar + ybar) / 2

theorem d003015 :
    _root_.GD.N0232.N0720.N1437.d003000 _root_.GD.N0232.N0720.N1437.d003014 := by
  intro shift dilation xbar ybar vx vy hdilation
  unfold _root_.GD.N0232.N0720.N1437.d003014
  ring




noncomputable def d003016
    (g : ℝ → ℝ → ℝ) (xbar ybar vx vy : ℝ) : ℝ := by
  classical
  exact if _root_.GD.N0232.N0720.N1437.d003012 vx vy then
    _root_.GD.N0232.N0720.N1437.d002998 g xbar ybar vx vy
  else
    _root_.GD.N0232.N0720.N1437.d003014 xbar ybar vx vy


theorem d003017
    (g : ℝ → ℝ → ℝ) :
    _root_.GD.N0232.N0720.N1437.d003000 (_root_.GD.N0232.N0720.N1437.d003016 g) := by
  intro shift dilation xbar ybar vx vy hdilation
  have hstratum :=
    _root_.GD.N0232.N0720.N1437.d003013 dilation vx vy hdilation.ne'
  by_cases hnonzero : _root_.GD.N0232.N0720.N1437.d003012 vx vy
  · have hnonzero' :
        _root_.GD.N0232.N0720.N1437.d003012 (dilation ^ 2 * vx) (dilation ^ 2 * vy) :=
      hstratum.mpr hnonzero
    simp only [_root_.GD.N0232.N0720.N1437.d003016, if_pos hnonzero,
      if_pos hnonzero']
    exact _root_.GD.N0232.N0720.N1437.d003003 g shift dilation xbar ybar vx vy hdilation
  · have hnonzero' :
        ¬ _root_.GD.N0232.N0720.N1437.d003012
          (dilation ^ 2 * vx) (dilation ^ 2 * vy) := by
      exact fun h ↦ hnonzero (hstratum.mp h)
    simp only [_root_.GD.N0232.N0720.N1437.d003016, if_neg hnonzero,
      if_neg hnonzero']
    exact _root_.GD.N0232.N0720.N1437.d003015 shift dilation xbar ybar vx vy hdilation



theorem d003018
    (g : ℝ → ℝ → ℝ) (xbar ybar vx vy : ℝ)
    (hnonzero : _root_.GD.N0232.N0720.N1437.d003012 vx vy) :
    _root_.GD.N0232.N0720.N1437.d003016 g xbar ybar vx vy =
      _root_.GD.N0232.N0720.N1437.d002998 g xbar ybar vx vy := by
  simp [_root_.GD.N0232.N0720.N1437.d003016, hnonzero]



theorem d003019
    (g : ℝ → ℝ → ℝ) (xbar ybar vx vy : ℝ)
    (hzero : ¬ _root_.GD.N0232.N0720.N1437.d003012 vx vy) :
    _root_.GD.N0232.N0720.N1437.d003016 g xbar ybar vx vy =
      (xbar + ybar) / 2 := by
  simp [_root_.GD.N0232.N0720.N1437.d003016, hzero, _root_.GD.N0232.N0720.N1437.d003014]



theorem d003020
    (g : ℝ → ℝ → ℝ)
    (hcomplement : ∀ r s, g (1 - r) s = 1 - g r s)
    (xbar ybar vx vy : ℝ) :
    _root_.GD.N0232.N0720.N1437.d003016 g ybar xbar vy vx =
      _root_.GD.N0232.N0720.N1437.d003016 g xbar ybar vx vy := by
  by_cases hnonzero : _root_.GD.N0232.N0720.N1437.d003012 vx vy
  · have hnonzeroSwap : _root_.GD.N0232.N0720.N1437.d003012 vy vx := by
      unfold _root_.GD.N0232.N0720.N1437.d003012 at ⊢ hnonzero
      simpa [add_comm] using hnonzero
    rw [_root_.GD.N0232.N0720.N1437.d003018
        g ybar xbar vy vx hnonzeroSwap,
      _root_.GD.N0232.N0720.N1437.d003018
        g xbar ybar vx vy hnonzero]
    unfold _root_.GD.N0232.N0720.N1437.d002998 _root_.GD.N0232.N0720.N1437.d002996 _root_.GD.N0232.N0720.N1437.d002997
    have hsum : vx + vy ≠ 0 := hnonzero
    have hfrac : vx / (vy + vx) = 1 - vy / (vx + vy) := by
      rw [add_comm vy vx]
      calc
        vx / (vx + vy) = (vx + vy) / (vx + vy) - vy / (vx + vy) := by
          ring
        _ = 1 - vy / (vx + vy) := by rw [div_self hsum]
    have hratio :
        (ybar - xbar) ^ 2 / (vy + vx) =
          (xbar - ybar) ^ 2 / (vx + vy) := by
      rw [add_comm vy vx]
      congr 1
      ring
    rw [hratio, hfrac, hcomplement]
    ring
  · have hzeroSwap : ¬ _root_.GD.N0232.N0720.N1437.d003012 vy vx := by
      unfold _root_.GD.N0232.N0720.N1437.d003012 at ⊢ hnonzero
      simpa [add_comm] using hnonzero
    rw [_root_.GD.N0232.N0720.N1437.d003019
        g ybar xbar vy vx hzeroSwap,
      _root_.GD.N0232.N0720.N1437.d003019
        g xbar ybar vx vy hnonzero]
    ring


theorem d003021
    (g : ℝ → ℝ → ℝ) (xbar ybar vx vy : ℝ)
    (hpositive : _root_.GD.N0232.N0720.N1437.d003004 vx vy) :
    _root_.GD.N0232.N0720.N1437.d003010 g xbar ybar vx vy =
      _root_.GD.N0232.N0720.N1437.d002998 g xbar ybar vx vy := by
  simp [_root_.GD.N0232.N0720.N1437.d003010, _root_.GD.N0232.N0720.N1437.d003006, hpositive]


@[simp] theorem d003022
    (g : ℝ → ℝ → ℝ) (xbar ybar vy : ℝ) :
    _root_.GD.N0232.N0720.N1437.d003010 g xbar ybar 0 vy = ybar := by
  simp [_root_.GD.N0232.N0720.N1437.d003010, _root_.GD.N0232.N0720.N1437.d003006,
    _root_.GD.N0232.N0720.N1437.d003004, _root_.GD.N0232.N0720.N1437.d003008]


@[simp] theorem d003023
    (g : ℝ → ℝ → ℝ) (xbar ybar vx : ℝ) :
    _root_.GD.N0232.N0720.N1437.d003010 g xbar ybar vx 0 = ybar := by
  simp [_root_.GD.N0232.N0720.N1437.d003010, _root_.GD.N0232.N0720.N1437.d003006,
    _root_.GD.N0232.N0720.N1437.d003004, _root_.GD.N0232.N0720.N1437.d003008]

end

end N1437
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1437.d003001
#print axioms _root_.GD.N0232.N0720.N1437.d003002
#print axioms _root_.GD.N0232.N0720.N1437.d003003
#print axioms _root_.GD.N0232.N0720.N1437.d003007
#print axioms _root_.GD.N0232.N0720.N1437.d003011
