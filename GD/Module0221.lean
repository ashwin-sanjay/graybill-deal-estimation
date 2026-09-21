import GD.Module0219


















namespace GD
namespace N0232
namespace N0720
namespace N1462

noncomputable section

open _root_.GD.N0232.N0720.N1463



def d003109 (alpha beta : ℝ) : ℝ :=
  alpha + beta + 3 / 2


def d003110
    (alpha beta p l f : ℝ) : ℝ :=
  alpha * p * (1 - l) + beta * (1 - p) * l +
    f * p * (1 - p) / 2


def d003111
    (alpha beta p l s : ℝ) : ℝ :=
  alpha * p * (1 - l) + beta * (1 - p) * l +
    s * (1 - p) / 2


theorem d003112
    {p : ℝ} (hp : p ≠ 0) (alpha beta l s : ℝ) :
    _root_.GD.N0232.N0720.N1462.d003110 alpha beta p l (s / p) =
      _root_.GD.N0232.N0720.N1462.d003111 alpha beta p l s := by
  unfold _root_.GD.N0232.N0720.N1462.d003110 _root_.GD.N0232.N0720.N1462.d003111
  field_simp [hp]


def d003113 (beta l s : ℝ) : ℝ :=
  beta * l + s / 2

@[simp] theorem d003114
    (alpha beta l s : ℝ) :
    _root_.GD.N0232.N0720.N1462.d003111 alpha beta 0 l s =
      _root_.GD.N0232.N0720.N1462.d003113 beta l s := by
  unfold _root_.GD.N0232.N0720.N1462.d003111 _root_.GD.N0232.N0720.N1462.d003113
  ring


theorem d003115
    (alpha beta p l s : ℝ) :
    _root_.GD.N0232.N0720.N1462.d003111 alpha beta p l s =
      _root_.GD.N0232.N0720.N1462.d003113 beta l s +
        p * (alpha * (1 - l) - beta * l - s / 2) := by
  unfold _root_.GD.N0232.N0720.N1462.d003111 _root_.GD.N0232.N0720.N1462.d003113
  ring



def d003116
    (alpha beta p l s : ℝ) : ℝ :=
  alpha * (1 - p) * (1 - l) + beta * p * l +
    s * (1 - p) / 2


theorem d003117
    {p : ℝ} (hp : p ≠ 0) (alpha beta l s : ℝ) :
    _root_.GD.N0232.N0720.N1462.d003110 alpha beta (1 - p) l (s / p) =
      _root_.GD.N0232.N0720.N1462.d003116 alpha beta p l s := by
  unfold _root_.GD.N0232.N0720.N1462.d003110 _root_.GD.N0232.N0720.N1462.d003116
  field_simp [hp]
  ring


def d003118 (alpha l s : ℝ) : ℝ :=
  alpha * (1 - l) + s / 2

@[simp] theorem d003119
    (alpha beta l s : ℝ) :
    _root_.GD.N0232.N0720.N1462.d003116 alpha beta 0 l s =
      _root_.GD.N0232.N0720.N1462.d003118 alpha l s := by
  unfold _root_.GD.N0232.N0720.N1462.d003116 _root_.GD.N0232.N0720.N1462.d003118
  ring


theorem d003120
    (alpha beta p l s : ℝ) :
    _root_.GD.N0232.N0720.N1462.d003116 alpha beta p l s =
      _root_.GD.N0232.N0720.N1462.d003118 alpha l s +
        p * (-alpha * (1 - l) + beta * l - s / 2) := by
  unfold _root_.GD.N0232.N0720.N1462.d003116 _root_.GD.N0232.N0720.N1462.d003118
  ring


noncomputable def d003121
    (alpha beta l s : ℝ) : ℝ :=
  l ^ (beta - 1) * (1 - l) ^ (alpha - 1) * s ^ (1 / 2 : ℝ)



noncomputable def d003122
    (alpha beta l s : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1462.d003121 alpha beta l s *
    (_root_.GD.N0232.N0720.N1462.d003113 beta l s) ^
      (-_root_.GD.N0232.N0720.N1462.d003109 alpha beta)



noncomputable def d003123
    (alpha beta l s : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1462.d003121 alpha beta l s *
    (_root_.GD.N0232.N0720.N1462.d003118 alpha l s) ^
      (-_root_.GD.N0232.N0720.N1462.d003109 alpha beta)

theorem d003124
    {alpha beta l s : ℝ}
    (_halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) :
    0 < _root_.GD.N0232.N0720.N1462.d003122 alpha beta l s := by
  have hden : 0 < _root_.GD.N0232.N0720.N1462.d003113 beta l s := by
    unfold _root_.GD.N0232.N0720.N1462.d003113
    have hl0 : 0 < l := hl.1
    positivity
  unfold _root_.GD.N0232.N0720.N1462.d003122 _root_.GD.N0232.N0720.N1462.d003121
  have hl0 : 0 < l := hl.1
  have h1l : 0 < 1 - l := sub_pos.mpr hl.2
  positivity

theorem d003125
    {alpha beta l s : ℝ}
    (halpha : 0 < alpha) (_hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) :
    0 < _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s := by
  have hden : 0 < _root_.GD.N0232.N0720.N1462.d003118 alpha l s := by
    unfold _root_.GD.N0232.N0720.N1462.d003118
    have h1l : 0 < 1 - l := sub_pos.mpr hl.2
    positivity
  unfold _root_.GD.N0232.N0720.N1462.d003123 _root_.GD.N0232.N0720.N1462.d003121
  have hl0 : 0 < l := hl.1
  have h1l : 0 < 1 - l := sub_pos.mpr hl.2
  positivity


noncomputable def d003126
    (alpha beta l s action : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1462.d003122 alpha beta l s * action ^ 2 +
    _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s * (action - 1) ^ 2


noncomputable def d003127
    (alpha beta l s : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s /
    (_root_.GD.N0232.N0720.N1462.d003122 alpha beta l s +
      _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s)




theorem d003128
    {alpha beta l s : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) :
    _root_.GD.N0232.N0720.N1462.d003127 alpha beta l s =
      (_root_.GD.N0232.N0720.N1462.d003113 beta l s) ^
          (_root_.GD.N0232.N0720.N1462.d003109 alpha beta) /
        ((_root_.GD.N0232.N0720.N1462.d003113 beta l s) ^
            (_root_.GD.N0232.N0720.N1462.d003109 alpha beta) +
          (_root_.GD.N0232.N0720.N1462.d003118 alpha l s) ^
            (_root_.GD.N0232.N0720.N1462.d003109 alpha beta)) := by
  have hleftDen : 0 < _root_.GD.N0232.N0720.N1462.d003113 beta l s := by
    unfold _root_.GD.N0232.N0720.N1462.d003113
    have hl0 : 0 < l := hl.1
    positivity
  have hrightDen : 0 < _root_.GD.N0232.N0720.N1462.d003118 alpha l s := by
    unfold _root_.GD.N0232.N0720.N1462.d003118
    have h1l : 0 < 1 - l := sub_pos.mpr hl.2
    positivity
  have hmono : 0 < _root_.GD.N0232.N0720.N1462.d003121 alpha beta l s := by
    unfold _root_.GD.N0232.N0720.N1462.d003121
    have hl0 : 0 < l := hl.1
    have h1l : 0 < 1 - l := sub_pos.mpr hl.2
    positivity
  have hleftPow :
      0 < (_root_.GD.N0232.N0720.N1462.d003113 beta l s) ^
        (_root_.GD.N0232.N0720.N1462.d003109 alpha beta) :=
    Real.rpow_pos_of_pos hleftDen _
  have hrightPow :
      0 < (_root_.GD.N0232.N0720.N1462.d003118 alpha l s) ^
        (_root_.GD.N0232.N0720.N1462.d003109 alpha beta) :=
    Real.rpow_pos_of_pos hrightDen _
  unfold _root_.GD.N0232.N0720.N1462.d003127 _root_.GD.N0232.N0720.N1462.d003122 _root_.GD.N0232.N0720.N1462.d003123
  rw [Real.rpow_neg hleftDen.le, Real.rpow_neg hrightDen.le]
  field_simp [hmono.ne', hleftPow.ne', hrightPow.ne']
  ring



noncomputable def d003129
    (r a b s : ℝ) : ℝ :=
  (a + s / 2) ^ r /
    ((a + s / 2) ^ r + (b + s / 2) ^ r)



theorem d003130
    {r a b s t : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (ht : 0 < t) :
    _root_.GD.N0232.N0720.N1462.d003129 r a b s = _root_.GD.N0232.N0720.N1462.d003129 r a b t ↔
      s = t ∨ a = b := by
  have has : 0 < a + s / 2 := by positivity
  have hbs : 0 < b + s / 2 := by positivity
  have hat : 0 < a + t / 2 := by positivity
  have hbt : 0 < b + t / 2 := by positivity
  have hpas : 0 < (a + s / 2) ^ r := Real.rpow_pos_of_pos has r
  have hpbs : 0 < (b + s / 2) ^ r := Real.rpow_pos_of_pos hbs r
  have hpat : 0 < (a + t / 2) ^ r := Real.rpow_pos_of_pos hat r
  have hpbt : 0 < (b + t / 2) ^ r := Real.rpow_pos_of_pos hbt r
  constructor
  · intro hweight
    have hsumS :
        (a + s / 2) ^ r + (b + s / 2) ^ r ≠ 0 :=
      (add_pos hpas hpbs).ne'
    have hsumT :
        (a + t / 2) ^ r + (b + t / 2) ^ r ≠ 0 :=
      (add_pos hpat hpbt).ne'
    have hratio := (div_eq_div_iff hsumS hsumT).mp hweight
    have hcross :
        (a + s / 2) ^ r * (b + t / 2) ^ r =
          (a + t / 2) ^ r * (b + s / 2) ^ r := by
      linear_combination hratio
    have hpower :
        ((a + s / 2) * (b + t / 2)) ^ r =
          ((a + t / 2) * (b + s / 2)) ^ r := by
      rw [Real.mul_rpow has.le hbt.le, Real.mul_rpow hat.le hbs.le]
      exact hcross
    have hprod :
        (a + s / 2) * (b + t / 2) =
          (a + t / 2) * (b + s / 2) := by
      have h₁ : 0 ≤ (a + s / 2) * (b + t / 2) :=
        (mul_pos has hbt).le
      have h₂ : 0 ≤ (a + t / 2) * (b + s / 2) :=
        (mul_pos hat hbs).le
      apply le_antisymm
      · exact (Real.rpow_le_rpow_iff h₁ h₂ hr).mp hpower.le
      · exact (Real.rpow_le_rpow_iff h₂ h₁ hr).mp hpower.symm.le
    by_cases hst : s = t
    · exact Or.inl hst
    · right
      have hfactor : (a - b) * (t - s) = 0 := by
        linarith
      rcases mul_eq_zero.mp hfactor with hab | hts
      · linarith
      · exfalso
        apply hst
        linarith
  · rintro (rfl | rfl)
    · rfl
    · unfold _root_.GD.N0232.N0720.N1462.d003129
      field_simp [hpas.ne', hpat.ne']




theorem d003131
    {r a b s t : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (hst : s < t) :
    _root_.GD.N0232.N0720.N1462.d003129 r a b s < _root_.GD.N0232.N0720.N1462.d003129 r a b t ↔
      a < b := by
  have ht : 0 < t := hs.trans hst
  have has : 0 < a + s / 2 := by positivity
  have hbs : 0 < b + s / 2 := by positivity
  have hat : 0 < a + t / 2 := by positivity
  have hbt : 0 < b + t / 2 := by positivity
  have hpas : 0 < (a + s / 2) ^ r := Real.rpow_pos_of_pos has r
  have hpbs : 0 < (b + s / 2) ^ r := Real.rpow_pos_of_pos hbs r
  have hpat : 0 < (a + t / 2) ^ r := Real.rpow_pos_of_pos hat r
  have hpbt : 0 < (b + t / 2) ^ r := Real.rpow_pos_of_pos hbt r
  unfold _root_.GD.N0232.N0720.N1462.d003129
  rw [div_lt_div_iff₀ (add_pos hpas hpbs) (add_pos hpat hpbt)]
  have hpow :
      (a + s / 2) ^ r * (b + t / 2) ^ r <
          (a + t / 2) ^ r * (b + s / 2) ^ r ↔
        (a + s / 2) * (b + t / 2) <
          (a + t / 2) * (b + s / 2) := by
    rw [← Real.mul_rpow has.le hbt.le,
      ← Real.mul_rpow hat.le hbs.le,
      Real.rpow_lt_rpow_iff
        (mul_pos has hbt).le (mul_pos hat hbs).le hr]
  constructor
  · intro h
    have hcross :
        (a + s / 2) ^ r * (b + t / 2) ^ r <
          (a + t / 2) ^ r * (b + s / 2) ^ r := by
      nlinarith
    have hproduct := hpow.mp hcross
    nlinarith
  · intro hab
    have hproduct :
        (a + s / 2) * (b + t / 2) <
          (a + t / 2) * (b + s / 2) := by
      nlinarith
    have hcross := hpow.mpr hproduct
    nlinarith


theorem d003132
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1462.d003109 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1462.d003109
  linarith



theorem d003133
    {alpha beta l s : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) :
    _root_.GD.N0232.N0720.N1462.d003127 alpha beta l s =
      _root_.GD.N0232.N0720.N1462.d003129 (_root_.GD.N0232.N0720.N1462.d003109 alpha beta)
        (beta * l) (alpha * (1 - l)) s := by
  rw [_root_.GD.N0232.N0720.N1462.d003128 halpha hbeta hl hs]
  unfold _root_.GD.N0232.N0720.N1462.d003129 _root_.GD.N0232.N0720.N1462.d003113 _root_.GD.N0232.N0720.N1462.d003118
  rfl




theorem d003134
    {alpha beta l s t : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) (ht : 0 < t) :
    _root_.GD.N0232.N0720.N1462.d003127 alpha beta l s =
        _root_.GD.N0232.N0720.N1462.d003127 alpha beta l t ↔
      s = t ∨ beta * l = alpha * (1 - l) := by
  rw [_root_.GD.N0232.N0720.N1462.d003133 halpha hbeta hl hs,
    _root_.GD.N0232.N0720.N1462.d003133 halpha hbeta hl ht]
  exact _root_.GD.N0232.N0720.N1462.d003130
    (_root_.GD.N0232.N0720.N1462.d003132 halpha hbeta)
    (mul_pos hbeta hl.1)
    (mul_pos halpha (sub_pos.mpr hl.2)) hs ht



theorem d003135
    {alpha beta l s t : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) (hst : s < t) :
    _root_.GD.N0232.N0720.N1462.d003127 alpha beta l s <
        _root_.GD.N0232.N0720.N1462.d003127 alpha beta l t ↔
      beta * l < alpha * (1 - l) := by
  rw [_root_.GD.N0232.N0720.N1462.d003133 halpha hbeta hl hs,
    _root_.GD.N0232.N0720.N1462.d003133 halpha hbeta hl
      (hs.trans hst)]
  exact _root_.GD.N0232.N0720.N1462.d003131
    (_root_.GD.N0232.N0720.N1462.d003132 halpha hbeta)
    (mul_pos hbeta hl.1)
    (mul_pos halpha (sub_pos.mpr hl.2)) hs hst



theorem d003136
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1)
    (hoff : beta * l ≠ alpha * (1 - l)) :
    _root_.GD.N0232.N0720.N1462.d003127 alpha beta l 1 ≠
      _root_.GD.N0232.N0720.N1462.d003127 alpha beta l 2 := by
  intro heq
  have hcases :=
    (_root_.GD.N0232.N0720.N1462.d003134 halpha hbeta hl
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)).mp heq
  rcases hcases with h12 | hbalance
  · norm_num at h12
  · exact hoff hbalance




theorem d003137
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ c s : ℝ, 0 < c → 0 < s →
      _root_.GD.N0232.N0720.N1462.d003127 alpha beta l (c * s) =
        _root_.GD.N0232.N0720.N1462.d003127 alpha beta l s) ↔
      beta * l = alpha * (1 - l) := by
  constructor
  · intro hinv
    have heq := hinv 2 1 (by norm_num) (by norm_num)
    have hcases :=
      (_root_.GD.N0232.N0720.N1462.d003134 halpha hbeta hl
        (by norm_num : (0 : ℝ) < 2 * 1)
        (by norm_num : (0 : ℝ) < 1)).mp heq
    rcases hcases with h21 | hbalance
    · norm_num at h21
    · exact hbalance
  · intro hbalance c s hc hs
    exact (_root_.GD.N0232.N0720.N1462.d003134 halpha hbeta hl
      (mul_pos hc hs) hs).mpr (Or.inr hbalance)



theorem d003138
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    beta * l = alpha * (1 - l) ↔
      l = alpha / (alpha + beta) := by
  have hab : alpha + beta ≠ 0 := (add_pos halpha hbeta).ne'
  constructor
  · intro hbalance
    apply (eq_div_iff hab).2
    linarith
  · intro hl
    rw [hl]
    field_simp [hab]
    ring


theorem d003139
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ c s : ℝ, 0 < c → 0 < s →
      _root_.GD.N0232.N0720.N1462.d003127 alpha beta l (c * s) =
        _root_.GD.N0232.N0720.N1462.d003127 alpha beta l s) ↔
      l = alpha / (alpha + beta) := by
  rw [_root_.GD.N0232.N0720.N1462.d003137 halpha hbeta hl,
    _root_.GD.N0232.N0720.N1462.d003138 halpha hbeta]


theorem d003140
    {alpha beta l s : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s)
    (action : ℝ) :
    _root_.GD.N0232.N0720.N1462.d003126 alpha beta l s action =
      (_root_.GD.N0232.N0720.N1462.d003122 alpha beta l s *
          _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s) /
        (_root_.GD.N0232.N0720.N1462.d003122 alpha beta l s +
          _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s) +
      (_root_.GD.N0232.N0720.N1462.d003122 alpha beta l s +
          _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s) *
        (action - _root_.GD.N0232.N0720.N1462.d003127 alpha beta l s) ^ 2 := by
  have hleft := _root_.GD.N0232.N0720.N1462.d003124 halpha hbeta hl hs
  have hright := _root_.GD.N0232.N0720.N1462.d003125 halpha hbeta hl hs
  simpa [_root_.GD.N0232.N0720.N1462.d003126, _root_.GD.N0232.N0720.N1462.d003127,
    _root_.GD.N0232.N0720.N1463.d003047, _root_.GD.N0232.N0720.N1463.d003048] using
    (_root_.GD.N0232.N0720.N1463.d003049
      (left := _root_.GD.N0232.N0720.N1462.d003122 alpha beta l s)
      (right := _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s)
      (add_pos hleft hright).ne' action)



theorem d003141
    (alpha beta l s : ℝ) :
    _root_.GD.N0232.N0720.N1462.d003122 beta alpha (1 - l) s =
      _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s := by
  unfold _root_.GD.N0232.N0720.N1462.d003122 _root_.GD.N0232.N0720.N1462.d003123 _root_.GD.N0232.N0720.N1462.d003121
    _root_.GD.N0232.N0720.N1462.d003113 _root_.GD.N0232.N0720.N1462.d003118 _root_.GD.N0232.N0720.N1462.d003109
  rw [show 1 - (1 - l) = l by ring]
  ring

theorem d003142
    (alpha beta l s : ℝ) :
    _root_.GD.N0232.N0720.N1462.d003123 beta alpha (1 - l) s =
      _root_.GD.N0232.N0720.N1462.d003122 alpha beta l s := by
  unfold _root_.GD.N0232.N0720.N1462.d003122 _root_.GD.N0232.N0720.N1462.d003123 _root_.GD.N0232.N0720.N1462.d003121
    _root_.GD.N0232.N0720.N1462.d003113 _root_.GD.N0232.N0720.N1462.d003118 _root_.GD.N0232.N0720.N1462.d003109
  rw [show 1 - (1 - l) = l by ring]
  ring



theorem d003143
    (alpha beta l s action : ℝ) :
    _root_.GD.N0232.N0720.N1462.d003126 beta alpha (1 - l) s (1 - action) =
      _root_.GD.N0232.N0720.N1462.d003126 alpha beta l s action := by
  unfold _root_.GD.N0232.N0720.N1462.d003126
  rw [_root_.GD.N0232.N0720.N1462.d003141, _root_.GD.N0232.N0720.N1462.d003142]
  ring



theorem d003144
    {alpha beta l s : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) :
    _root_.GD.N0232.N0720.N1462.d003127 beta alpha (1 - l) s =
      1 - _root_.GD.N0232.N0720.N1462.d003127 alpha beta l s := by
  unfold _root_.GD.N0232.N0720.N1462.d003127
  rw [_root_.GD.N0232.N0720.N1462.d003141, _root_.GD.N0232.N0720.N1462.d003142]
  have hleft := _root_.GD.N0232.N0720.N1462.d003124 halpha hbeta hl hs
  have hright := _root_.GD.N0232.N0720.N1462.d003125 halpha hbeta hl hs
  have hden :
      _root_.GD.N0232.N0720.N1462.d003122 alpha beta l s +
          _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s ≠ 0 :=
    (add_pos hleft hright).ne'
  field_simp [hden]
  ring





theorem d003145
    (profile : ℝ → ℝ)
    (hinv : ∀ c s : ℝ, 0 < c → 0 < s →
      profile (c * s) = profile s)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    profile t = profile s := by
  have hc : 0 < t / s := div_pos ht hs
  have h := hinv (t / s) s hc hs
  have hmul : (t / s) * s = t := by
    field_simp [hs.ne']
  simpa [hmul] using h

end

end N1462
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1462.d003112
#print axioms _root_.GD.N0232.N0720.N1462.d003117
#print axioms _root_.GD.N0232.N0720.N1462.d003124
#print axioms _root_.GD.N0232.N0720.N1462.d003125
#print axioms _root_.GD.N0232.N0720.N1462.d003128
#print axioms _root_.GD.N0232.N0720.N1462.d003130
#print axioms _root_.GD.N0232.N0720.N1462.d003134
#print axioms _root_.GD.N0232.N0720.N1462.d003135
#print axioms _root_.GD.N0232.N0720.N1462.d003136
#print axioms _root_.GD.N0232.N0720.N1462.d003137
#print axioms _root_.GD.N0232.N0720.N1462.d003138
#print axioms _root_.GD.N0232.N0720.N1462.d003139
#print axioms _root_.GD.N0232.N0720.N1462.d003140
#print axioms _root_.GD.N0232.N0720.N1462.d003143
#print axioms _root_.GD.N0232.N0720.N1462.d003144
#print axioms _root_.GD.N0232.N0720.N1462.d003145
