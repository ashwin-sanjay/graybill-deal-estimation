import GD.Module1814

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0248

noncomputable section

def d030118 (A v : ℝ) : ℝ := Real.log v + A/v

theorem d030119 {A v : ℝ} (hA : 0 < A) (hv : 0 < v) :
    _root_.GD.N0005.N0248.d030118 A A ≤ _root_.GD.N0005.N0248.d030118 A v := by
  have h := Real.log_le_sub_one_of_pos (div_pos hA hv)
  rw [Real.log_div hA.ne' hv.ne'] at h
  dsimp [_root_.GD.N0005.N0248.d030118]
  rw [div_self hA.ne']
  linarith

theorem d030120 {A v : ℝ} (hA : 0 < A) (hv : 0 < v)
    (hne : v ≠ A) : _root_.GD.N0005.N0248.d030118 A A < _root_.GD.N0005.N0248.d030118 A v := by
  have hne' : A/v ≠ 1 := by
    intro h
    have := (div_eq_one_iff_eq hv.ne').1 h
    exact hne this.symm
  have h := Real.log_lt_sub_one_of_pos (div_pos hA hv) hne'
  rw [Real.log_div hA.ne' hv.ne'] at h
  dsimp [_root_.GD.N0005.N0248.d030118]
  rw [div_self hA.ne']
  linarith

theorem d030121 {A v : ℝ} (hA : 0 < A) (hv : 0 < v) :
    _root_.GD.N0005.N0248.d030118 A A = _root_.GD.N0005.N0248.d030118 A v ↔ v = A := by
  constructor
  · intro h
    by_contra hne
    exact (ne_of_lt (_root_.GD.N0005.N0248.d030120 hA hv hne)) h
  · rintro rfl
    rfl

def d030122 (m n a b x y u v w : ℝ) : ℝ :=
  -(m * _root_.GD.N0005.N0248.d030118 (_root_.GD.N0005.N0248.d030070 a x u) v +
    n * _root_.GD.N0005.N0248.d030118 (_root_.GD.N0005.N0248.d030070 b y u) w) / 2

theorem d030123 (m n a b x y u : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    _root_.GD.N0005.N0248.d030122 m n a b x y u
      (_root_.GD.N0005.N0248.d030070 a x u) (_root_.GD.N0005.N0248.d030070 b y u) =
        _root_.GD.N0005.N0248.d030071 m n a b x y u - (m+n)/2 := by
  dsimp [_root_.GD.N0005.N0248.d030122, _root_.GD.N0005.N0248.d030118, _root_.GD.N0005.N0248.d030071]
  rw [div_self (_root_.GD.N0005.N0248.d030074 ha x u).ne',
    div_self (_root_.GD.N0005.N0248.d030074 hb y u).ne']
  ring

theorem d030124 {m n a b x y u v w : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (ha : 0 < a) (hb : 0 < b)
    (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0005.N0248.d030122 m n a b x y u v w ≤
      _root_.GD.N0005.N0248.d030071 m n a b x y u - (m+n)/2 := by
  rw [← _root_.GD.N0005.N0248.d030123 m n a b x y u ha hb]
  have h1 := mul_le_mul_of_nonneg_left
    (_root_.GD.N0005.N0248.d030119 (_root_.GD.N0005.N0248.d030074 ha x u) hv) hm
  have h2 := mul_le_mul_of_nonneg_left
    (_root_.GD.N0005.N0248.d030119 (_root_.GD.N0005.N0248.d030074 hb y u) hw) hn
  dsimp [_root_.GD.N0005.N0248.d030122]
  linarith

theorem d030125 {m n a b x y u v w : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0005.N0248.d030122 m n a b x y u v w =
      _root_.GD.N0005.N0248.d030071 m n a b x y u - (m+n)/2 ↔
        v = _root_.GD.N0005.N0248.d030070 a x u ∧ w = _root_.GD.N0005.N0248.d030070 b y u := by
  rw [← _root_.GD.N0005.N0248.d030123 m n a b x y u ha hb]
  constructor
  · intro heq
    have hA := _root_.GD.N0005.N0248.d030074 ha x u
    have hB := _root_.GD.N0005.N0248.d030074 hb y u
    have h1 := _root_.GD.N0005.N0248.d030119 hA hv
    have h2 := _root_.GD.N0005.N0248.d030119 hB hw
    dsimp [_root_.GD.N0005.N0248.d030122] at heq
    constructor
    · by_contra hne
      have hlt := mul_lt_mul_of_pos_left (_root_.GD.N0005.N0248.d030120 hA hv hne) hm
      have hle := mul_le_mul_of_nonneg_left h2 hn.le
      linarith
    · by_contra hne
      have hlt := mul_lt_mul_of_pos_left (_root_.GD.N0005.N0248.d030120 hB hw hne) hn
      have hle := mul_le_mul_of_nonneg_left h1 hm.le
      linarith
  · rintro ⟨rfl, rfl⟩
    rfl

theorem d030126 {m n a b x y u v w : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (hv : 0 < v) (hw : 0 < w) :
    (∀ u' v' w' : ℝ, 0 < v' → 0 < w' →
      _root_.GD.N0005.N0248.d030122 m n a b x y u' v' w' ≤
        _root_.GD.N0005.N0248.d030122 m n a b x y u v w) ↔
      v = _root_.GD.N0005.N0248.d030070 a x u ∧ w = _root_.GD.N0005.N0248.d030070 b y u ∧
        ∀ u' : ℝ, _root_.GD.N0005.N0248.d030071 m n a b x y u' ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u := by
  constructor
  · intro hmax
    have heq : _root_.GD.N0005.N0248.d030122 m n a b x y u v w =
        _root_.GD.N0005.N0248.d030071 m n a b x y u - (m+n)/2 := by
      apply le_antisymm (_root_.GD.N0005.N0248.d030124 hm.le hn.le ha hb hv hw)
      rw [← _root_.GD.N0005.N0248.d030123 m n a b x y u ha hb]
      exact hmax u (_root_.GD.N0005.N0248.d030070 a x u) (_root_.GD.N0005.N0248.d030070 b y u)
        (_root_.GD.N0005.N0248.d030074 ha x u) (_root_.GD.N0005.N0248.d030074 hb y u)
    obtain ⟨hvEq, hwEq⟩ := (_root_.GD.N0005.N0248.d030125 hm hn ha hb hv hw).1 heq
    refine ⟨hvEq, hwEq, ?_⟩
    intro u'
    have h := hmax u' (_root_.GD.N0005.N0248.d030070 a x u') (_root_.GD.N0005.N0248.d030070 b y u')
      (_root_.GD.N0005.N0248.d030074 ha x u') (_root_.GD.N0005.N0248.d030074 hb y u')
    rw [_root_.GD.N0005.N0248.d030123 m n a b x y u' ha hb, heq] at h
    linarith
  · rintro ⟨rfl, rfl, hmax⟩ u' v' w' hv' hw'
    rw [_root_.GD.N0005.N0248.d030123 m n a b x y u ha hb]
    apply (_root_.GD.N0005.N0248.d030124 hm.le hn.le ha hb hv' hw').trans
    linarith [hmax u']

end
end GD.N0005.N0248

#print axioms _root_.GD.N0005.N0248.d030121
#print axioms _root_.GD.N0005.N0248.d030125
#print axioms _root_.GD.N0005.N0248.d030126
