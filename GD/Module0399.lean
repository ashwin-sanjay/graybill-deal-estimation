import Mathlib


















noncomputable section

namespace GD.N0111

def d006136 (c d h s t : ℝ) : ℝ :=
  c + d * s + h * t

def d006137 (a c d h r s t : ℝ) : ℝ :=
  (a + s) * _root_.GD.N0111.d006136 c d h s t ^ (-r)





def d006138 (r : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => d006138 r k * (-r - k)


def d006139 (r : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => d006139 r k * (r + k)


def d006140 (c d h r s t : ℝ) (p q : ℕ) : ℝ :=
  _root_.GD.N0111.d006138 r (p + q) * d ^ p * h ^ q *
    _root_.GD.N0111.d006136 c d h s t ^ (-r - (p + q : ℕ))


def d006141 (a c d h r s t : ℝ) (p q : ℕ) : ℝ :=
  (a + s) * _root_.GD.N0111.d006140 c d h r s t p q +
    (p : ℝ) * _root_.GD.N0111.d006140 c d h r s t (p - 1) q

theorem d006142 (c d h s t : ℝ) :
    HasDerivAt (fun x => _root_.GD.N0111.d006136 c d h x t) d s := by
  simpa [_root_.GD.N0111.d006136] using
    ((hasDerivAt_const s c).add
      ((hasDerivAt_id s).const_mul d)).add_const (h * t)

theorem d006143 (c d h s t : ℝ) :
    HasDerivAt (fun y => _root_.GD.N0111.d006136 c d h s y) h t := by
  simpa [_root_.GD.N0111.d006136, add_assoc] using
    ((hasDerivAt_id t).const_mul h).const_add (c + d * s)

theorem d006144
    (c d h r s t : ℝ) (p q : ℕ)
    (hN : _root_.GD.N0111.d006136 c d h s t ≠ 0) :
    HasDerivAt
      (fun x => _root_.GD.N0111.d006140 c d h r x t p q)
      (_root_.GD.N0111.d006140 c d h r s t (p + 1) q) s := by
  have hp :=
    (_root_.GD.N0111.d006142 c d h s t).rpow_const
      (p := -r - (p + q : ℕ)) (Or.inl hN)
  have hc :=
    hp.const_mul
      (_root_.GD.N0111.d006138 r (p + q) * d ^ p * h ^ q)
  have hc' :
      HasDerivAt
        (fun x => _root_.GD.N0111.d006140 c d h r x t p q)
        (_root_.GD.N0111.d006138 r (p + q) * d ^ p * h ^ q *
          (d * (-r - (p + q : ℕ)) *
            _root_.GD.N0111.d006136 c d h s t ^ (-r - (p + q : ℕ) - 1))) s := by
    simpa only [_root_.GD.N0111.d006140] using hc
  apply hc'.congr_deriv
  unfold _root_.GD.N0111.d006140
  rw [show p + 1 + q = (p + q) + 1 by omega]
  simp only [_root_.GD.N0111.d006138, Nat.cast_add, Nat.cast_one,
    pow_succ]
  have hexp :
      -r - ((p : ℝ) + (q : ℝ)) - 1 =
        -r - ((p : ℝ) + (q : ℝ) + 1) := by ring
  rw [← hexp]
  ring

theorem d006145
    (c d h r s t : ℝ) (p q : ℕ)
    (hN : _root_.GD.N0111.d006136 c d h s t ≠ 0) :
    HasDerivAt
      (fun y => _root_.GD.N0111.d006140 c d h r s y p q)
      (_root_.GD.N0111.d006140 c d h r s t p (q + 1)) t := by
  have hp :=
    (_root_.GD.N0111.d006143 c d h s t).rpow_const
      (p := -r - (p + q : ℕ)) (Or.inl hN)
  have hc :=
    hp.const_mul
      (_root_.GD.N0111.d006138 r (p + q) * d ^ p * h ^ q)
  have hc' :
      HasDerivAt
        (fun y => _root_.GD.N0111.d006140 c d h r s y p q)
        (_root_.GD.N0111.d006138 r (p + q) * d ^ p * h ^ q *
          (h * (-r - (p + q : ℕ)) *
            _root_.GD.N0111.d006136 c d h s t ^ (-r - (p + q : ℕ) - 1))) t := by
    simpa only [_root_.GD.N0111.d006140] using hc
  apply hc'.congr_deriv
  unfold _root_.GD.N0111.d006140
  rw [show p + (q + 1) = (p + q) + 1 by omega]
  simp only [_root_.GD.N0111.d006138, Nat.cast_add, Nat.cast_one,
    pow_succ]
  have hexp :
      -r - ((p : ℝ) + (q : ℝ)) - 1 =
        -r - ((p : ℝ) + (q : ℝ) + 1) := by ring
  rw [← hexp]
  ring

theorem d006146
    (a c d h r s t : ℝ) (p q : ℕ)
    (hN : _root_.GD.N0111.d006136 c d h s t ≠ 0) :
    deriv (fun x => _root_.GD.N0111.d006141 a c d h r x t p q) s =
      _root_.GD.N0111.d006141 a c d h r s t (p + 1) q := by
  have hn : HasDerivAt (fun x : ℝ => a + x) 1 s := by
    simpa [add_comm] using (hasDerivAt_id s).add_const a
  have hp :=
    _root_.GD.N0111.d006144 c d h r s t p q hN
  have hp' :=
    _root_.GD.N0111.d006144 c d h r s t (p - 1) q hN
  have hmain := hn.mul hp
  have htail := hp'.const_mul (p : ℝ)
  have hfun :
      (fun x => _root_.GD.N0111.d006141 a c d h r x t p q) =
        (((fun x : ℝ => a + x) *
          fun x => _root_.GD.N0111.d006140 c d h r x t p q) +
          fun x => (p : ℝ) * _root_.GD.N0111.d006140 c d h r x t (p - 1) q) := by
    funext x
    rfl
  rw [hfun, (hmain.add htail).deriv]
  simp only [_root_.GD.N0111.d006141, Nat.cast_add, Nat.cast_one]
  rw [show p + 1 - 1 = p by omega]
  by_cases hp0 : p = 0
  · subst p
    simp [_root_.GD.N0111.d006140]
    ring
  · have hpred : p - 1 + 1 = p :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hp0)
    rw [hpred]
    ring

theorem d006147
    (a c d h r s t : ℝ) (p q : ℕ)
    (hN : _root_.GD.N0111.d006136 c d h s t ≠ 0) :
    deriv (fun y => _root_.GD.N0111.d006141 a c d h r s y p q) t =
      _root_.GD.N0111.d006141 a c d h r s t p (q + 1) := by
  have hp :=
    _root_.GD.N0111.d006145 c d h r s t p q hN
  have hp' :=
    _root_.GD.N0111.d006145 c d h r s t (p - 1) q hN
  have hmain := hp.const_mul (a + s)
  have htail := hp'.const_mul (p : ℝ)
  have hfun :
      (fun y => _root_.GD.N0111.d006141 a c d h r s y p q) =
        ((fun y => (a + s) * _root_.GD.N0111.d006140 c d h r s y p q) +
          fun y => (p : ℝ) * _root_.GD.N0111.d006140 c d h r s y (p - 1) q) := by
    funext y
    rfl
  rw [hfun, (hmain.add htail).deriv]
  rfl

theorem d006148 (a c d h r s t : ℝ) :
    _root_.GD.N0111.d006141 a c d h r s t 0 0 = _root_.GD.N0111.d006137 a c d h r s t := by
  simp [_root_.GD.N0111.d006141, _root_.GD.N0111.d006140, _root_.GD.N0111.d006138, _root_.GD.N0111.d006137]



theorem d006149
    (a c d h r s : ℝ) (q : ℕ)
    (hpos : ∀ y : ℝ, _root_.GD.N0111.d006136 c d h s y ≠ 0) :
    ∀ t : ℝ,
      iteratedDeriv q (fun y => _root_.GD.N0111.d006137 a c d h r s y) t =
        _root_.GD.N0111.d006141 a c d h r s t 0 q := by
  induction q with
  | zero =>
      intro t
      simp [_root_.GD.N0111.d006148]
  | succ q ih =>
      intro t
      rw [iteratedDeriv_succ]
      have hfun :
          (fun y =>
            iteratedDeriv q (fun z => _root_.GD.N0111.d006137 a c d h r s z) y) =
          (fun y => _root_.GD.N0111.d006141 a c d h r s y 0 q) := by
        funext y
        exact ih y
      change
        deriv
          (fun y =>
            iteratedDeriv q (fun z => _root_.GD.N0111.d006137 a c d h r s z) y) t =
          _
      rw [hfun]
      exact _root_.GD.N0111.d006147 a c d h r s t 0 q (hpos t)

theorem d006150
    (a c d h r t : ℝ) (p q : ℕ)
    (hpos : ∀ x : ℝ, _root_.GD.N0111.d006136 c d h x t ≠ 0) :
    ∀ s : ℝ,
      iteratedDeriv p (fun x => _root_.GD.N0111.d006141 a c d h r x t 0 q) s =
        _root_.GD.N0111.d006141 a c d h r s t p q := by
  induction p with
  | zero =>
      intro s
      simp
  | succ p ih =>
      intro s
      rw [iteratedDeriv_succ]
      have hfun :
          (fun x =>
            iteratedDeriv p
              (fun z => _root_.GD.N0111.d006141 a c d h r z t 0 q) x) =
          (fun x => _root_.GD.N0111.d006141 a c d h r x t p q) := by
        funext x
        exact ih x
      change
        deriv
          (fun x =>
            iteratedDeriv p
              (fun z => _root_.GD.N0111.d006141 a c d h r z t 0 q) x) s =
          _
      rw [hfun]
      exact _root_.GD.N0111.d006146 a c d h r s t p q (hpos s)



theorem d006151 (r : ℝ) (hr : 0 ≤ r) :
    ∀ k : ℕ, 0 ≤ _root_.GD.N0111.d006139 r k := by
  intro k
  induction k with
  | zero => simp [_root_.GD.N0111.d006139]
  | succ k ih =>
      simp only [_root_.GD.N0111.d006139]
      exact mul_nonneg ih (add_nonneg hr (Nat.cast_nonneg k))

theorem d006152 (r : ℝ) (hr : 0 ≤ r) :
    ∀ k : ℕ, |_root_.GD.N0111.d006138 r k| = _root_.GD.N0111.d006139 r k := by
  intro k
  induction k with
  | zero => simp [_root_.GD.N0111.d006138, _root_.GD.N0111.d006139]
  | succ k ih =>
      rw [_root_.GD.N0111.d006138, _root_.GD.N0111.d006139, abs_mul, ih]
      have : |-r - (k : ℝ)| = r + k := by
        have hnonpos : -r - (k : ℝ) ≤ 0 := by
          have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        rw [abs_of_nonpos hnonpos]
        ring
      rw [this]







def d006153 (L r : ℝ) (k : ℕ) : ℝ :=
  if 1 ≤ L then
    (L ^ Nat.floor (r + k))⁻¹
  else
    (L ^ Nat.ceil (r + k))⁻¹

theorem d006154
    {L N r : ℝ} {k : ℕ}
    (hL0 : 0 < L) (hL1 : 1 ≤ L) (hLN : L ≤ N)
  (hr : 0 ≤ r) :
    N ^ (-r - (k : ℕ)) ≤
      (L ^ Nat.floor (r + k))⁻¹ := by
  have hz : -r - (k : ℝ) ≤ 0 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hfloor :
      ((Nat.floor (r + (k : ℝ)) : ℕ) : ℝ) ≤ r + (k : ℝ) :=
    Nat.floor_le (add_nonneg hr (Nat.cast_nonneg k))
  calc
    N ^ (-r - (k : ℕ))
        ≤ L ^ (-r - (k : ℕ)) :=
          Real.rpow_le_rpow_of_nonpos hL0 hLN hz
    _ ≤ L ^ (-(Nat.floor (r + k) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    _ = (L ^ Nat.floor (r + k))⁻¹ := by
      rw [Real.rpow_neg hL0.le, Real.rpow_natCast]

theorem d006155
    {L N r : ℝ} {k : ℕ}
    (hL0 : 0 < L) (hL1 : L ≤ 1) (hLN : L ≤ N)
  (hr : 0 ≤ r) :
    N ^ (-r - (k : ℕ)) ≤
      (L ^ Nat.ceil (r + k))⁻¹ := by
  have hz : -r - (k : ℝ) ≤ 0 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hceil :
      r + (k : ℝ) ≤ (Nat.ceil (r + (k : ℝ)) : ℕ) :=
    Nat.le_ceil _
  calc
    N ^ (-r - (k : ℕ))
        ≤ L ^ (-r - (k : ℕ)) :=
          Real.rpow_le_rpow_of_nonpos hL0 hLN hz
    _ ≤ L ^ (-(Nat.ceil (r + k) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hL0 hL1 (by linarith)
    _ = (L ^ Nat.ceil (r + k))⁻¹ := by
      rw [Real.rpow_neg hL0.le, Real.rpow_natCast]

theorem d006156
    {L N r : ℝ} {k : ℕ}
    (hL0 : 0 < L) (hLN : L ≤ N) (hr : 0 ≤ r) :
    N ^ (-r - (k : ℕ)) ≤ _root_.GD.N0111.d006153 L r k := by
  unfold _root_.GD.N0111.d006153
  split_ifs with hL1
  · exact _root_.GD.N0111.d006154 hL0 hL1 hLN hr
  · exact _root_.GD.N0111.d006155 hL0 (le_of_not_ge hL1) hLN hr

theorem d006157
    {c d h r s t D H P : ℝ} {p q : ℕ}
    (hr : 0 ≤ r) (hd : |d| ≤ D) (hh : |h| ≤ H)
    (hpow : |_root_.GD.N0111.d006136 c d h s t ^ (-r - (p + q : ℕ))| ≤ P)
    (hD : 0 ≤ D) (hH : 0 ≤ H) :
    |_root_.GD.N0111.d006140 c d h r s t p q| ≤
      _root_.GD.N0111.d006139 r (p + q) * D ^ p * H ^ q * P := by
  rw [_root_.GD.N0111.d006140, abs_mul, abs_mul, abs_mul, _root_.GD.N0111.d006152 r hr,
    abs_pow, abs_pow]
  have hdp : |d| ^ p ≤ D ^ p :=
    pow_le_pow_left₀ (abs_nonneg d) hd p
  have hhp : |h| ^ q ≤ H ^ q :=
    pow_le_pow_left₀ (abs_nonneg h) hh q
  have h₁ :
      _root_.GD.N0111.d006139 r (p + q) * |d| ^ p ≤
        _root_.GD.N0111.d006139 r (p + q) * D ^ p :=
    mul_le_mul_of_nonneg_left hdp (_root_.GD.N0111.d006151 r hr _)
  have h₂ :
      _root_.GD.N0111.d006139 r (p + q) * |d| ^ p * |h| ^ q ≤
        _root_.GD.N0111.d006139 r (p + q) * D ^ p * H ^ q :=
    by
      have hRD : 0 ≤ _root_.GD.N0111.d006139 r (p + q) * D ^ p :=
        mul_nonneg (_root_.GD.N0111.d006151 r hr _) (pow_nonneg hD _)
      calc
        _root_.GD.N0111.d006139 r (p + q) * |d| ^ p * |h| ^ q
            ≤ _root_.GD.N0111.d006139 r (p + q) * D ^ p * |h| ^ q :=
              mul_le_mul_of_nonneg_right h₁
                (pow_nonneg (abs_nonneg h) _)
        _ ≤ _root_.GD.N0111.d006139 r (p + q) * D ^ p * H ^ q := by
              exact mul_le_mul_of_nonneg_left hhp hRD
  have hRDH : 0 ≤ _root_.GD.N0111.d006139 r (p + q) * D ^ p * H ^ q :=
    mul_nonneg
      (mul_nonneg (_root_.GD.N0111.d006151 r hr _) (pow_nonneg hD _))
      (pow_nonneg hH _)
  calc
    _root_.GD.N0111.d006139 r (p + q) * |d| ^ p * |h| ^ q *
        |_root_.GD.N0111.d006136 c d h s t ^ (-r - (p + q : ℕ))|
        ≤ _root_.GD.N0111.d006139 r (p + q) * D ^ p * H ^ q *
          |_root_.GD.N0111.d006136 c d h s t ^ (-r - (p + q : ℕ))| := by
            exact mul_le_mul_of_nonneg_right h₂ (abs_nonneg _)
    _ ≤ _root_.GD.N0111.d006139 r (p + q) * D ^ p * H ^ q * P := by
          exact mul_le_mul_of_nonneg_left hpow hRDH


theorem d006158
    {a c d h r s t A D H P₀ P₁ : ℝ} {p q : ℕ}
    (hr : 0 ≤ r) (ha : |a + s| ≤ A)
    (hd : |d| ≤ D) (hh : |h| ≤ H)
    (hpow₀ :
      |_root_.GD.N0111.d006136 c d h s t ^ (-r - (p + q : ℕ))| ≤ P₀)
    (hpow₁ :
      |_root_.GD.N0111.d006136 c d h s t ^
        (-r - ((p - 1) + q : ℕ))| ≤ P₁)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hH : 0 ≤ H) :
    |_root_.GD.N0111.d006141 a c d h r s t p q| ≤
      A * _root_.GD.N0111.d006139 r (p + q) * D ^ p * H ^ q * P₀ +
      (p : ℝ) * _root_.GD.N0111.d006139 r ((p - 1) + q) *
        D ^ (p - 1) * H ^ q * P₁ := by
  rw [_root_.GD.N0111.d006141]
  calc
    |(a + s) * _root_.GD.N0111.d006140 c d h r s t p q +
        (p : ℝ) * _root_.GD.N0111.d006140 c d h r s t (p - 1) q|
        ≤ |a + s| * |_root_.GD.N0111.d006140 c d h r s t p q| +
          (p : ℝ) * |_root_.GD.N0111.d006140 c d h r s t (p - 1) q| := by
            calc
              |(a + s) * _root_.GD.N0111.d006140 c d h r s t p q +
                  (p : ℝ) * _root_.GD.N0111.d006140 c d h r s t (p - 1) q|
                  ≤ |(a + s) * _root_.GD.N0111.d006140 c d h r s t p q| +
                    |(p : ℝ) *
                      _root_.GD.N0111.d006140 c d h r s t (p - 1) q| :=
                    abs_add_le _ _
              _ = |a + s| * |_root_.GD.N0111.d006140 c d h r s t p q| +
                    (p : ℝ) *
                      |_root_.GD.N0111.d006140 c d h r s t (p - 1) q| := by
                    have hpabs : |(p : ℝ)| = (p : ℝ) :=
                      abs_of_nonneg (Nat.cast_nonneg p)
                    rw [abs_mul, abs_mul, hpabs]
    _ ≤ A * (_root_.GD.N0111.d006139 r (p + q) * D ^ p * H ^ q * P₀) +
          (p : ℝ) *
            (_root_.GD.N0111.d006139 r ((p - 1) + q) * D ^ (p - 1) * H ^ q * P₁) := by
      gcongr
      · exact _root_.GD.N0111.d006157 hr hd hh hpow₀ hD hH
      · exact _root_.GD.N0111.d006157 hr hd hh hpow₁ hD hH
    _ = A * _root_.GD.N0111.d006139 r (p + q) * D ^ p * H ^ q * P₀ +
          (p : ℝ) * _root_.GD.N0111.d006139 r ((p - 1) + q) *
            D ^ (p - 1) * H ^ q * P₁ := by ring



def d006159 (α β : ℝ) : ℝ :=
  3 * (α * β / (α + β)) / 4

def d006160
    (α β r : ℝ) (p q : ℕ) : ℝ :=
  (9 / 8 : ℝ) * _root_.GD.N0111.d006139 r (p + q) *
      max α β ^ p * (1 / 8 : ℝ) ^ q *
      _root_.GD.N0111.d006153 (_root_.GD.N0111.d006159 α β) r (p + q) +
    (p : ℝ) * _root_.GD.N0111.d006139 r ((p - 1) + q) *
      max α β ^ (p - 1) * (1 / 8 : ℝ) ^ q *
      _root_.GD.N0111.d006153 (_root_.GD.N0111.d006159 α β) r ((p - 1) + q)

theorem d006161
    {α β e : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    |β - (α + β) * e| ≤ max α β := by
  rw [abs_le]
  constructor
  · calc
      -(max α β) ≤ -α := neg_le_neg (le_max_left α β)
      _ ≤ β - (α + β) * e := by nlinarith
  · calc
      β - (α + β) * e ≤ β := by nlinarith
      _ ≤ max α β := le_max_right α β

theorem d006162
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 ≤ e * (1 - e) / 2 ∧ e * (1 - e) / 2 ≤ 1 / 8 := by
  constructor
  · exact div_nonneg (mul_nonneg he0 (sub_nonneg.mpr he1)) (by norm_num)
  · nlinarith [sq_nonneg (e - 1 / 2)]

theorem d006163
    {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hs : |s| ≤ min α β / (4 * (α + β))) :
    |s| ≤ 1 / 8 := by
  have hν : 0 < α + β := add_pos hα hβ
  have hmin2 : 2 * min α β ≤ α + β := by
    calc
      2 * min α β = min α β + min α β := by ring
      _ ≤ α + β :=
        add_le_add (min_le_left α β) (min_le_right α β)
  refine hs.trans ?_
  apply (div_le_iff₀ (mul_pos (by norm_num) hν)).2
  nlinarith

theorem d006164
    {α β e s : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ min α β / (4 * (α + β))) :
    |α / (α + β) - e + s| ≤ 9 / 8 := by
  have hν : 0 < α + β := add_pos hα hβ
  have hell0 : 0 ≤ α / (α + β) := div_nonneg hα.le hν.le
  have hell1 : α / (α + β) ≤ 1 :=
    (div_le_one hν).2 (by linarith)
  have ha : |α / (α + β) - e| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |α / (α + β) - e + s|
        ≤ |α / (α + β) - e| + |s| := abs_add_le _ _
    _ ≤ 1 + 1 / 8 :=
      add_le_add ha (_root_.GD.N0111.d006163 hα hβ hs)
    _ = 9 / 8 := by ring

theorem d006165 (α β : ℝ) :
    max α β * min α β = α * β := by
  rcases le_total α β with hab | hba
  · simp [max_eq_right hab, min_eq_left hab, mul_comm]
  · simp [max_eq_left hba, min_eq_right hba]

theorem d006166
    {α β e s t : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ min α β / (4 * (α + β)))
    (ht : 0 ≤ t) :
    _root_.GD.N0111.d006159 α β ≤
      _root_.GD.N0111.d006136 (α * β / (α + β)) (β - (α + β) * e)
        (e * (1 - e) / 2) s t := by
  have hν : 0 < α + β := add_pos hα hβ
  have hd :=
    _root_.GD.N0111.d006161 hα.le hβ.le he0 he1
  have hds :
      |β - (α + β) * e| * |s| ≤
        (α * β / (α + β)) / 4 := by
    calc
      |β - (α + β) * e| * |s|
          ≤ max α β * (min α β / (4 * (α + β))) :=
            mul_le_mul hd hs (abs_nonneg _)
              (hα.le.trans (le_max_left α β))
      _ = (α * β / (α + β)) / 4 := by
        rw [← _root_.GD.N0111.d006165 α β]
        field_simp
  have hmul :
      -(α * β / (α + β) / 4) ≤
        (β - (α + β) * e) * s := by
    have habs :
        |(β - (α + β) * e) * s| ≤
          (α * β / (α + β)) / 4 := by
      simpa [abs_mul] using hds
    exact (abs_le.mp habs).1
  have hh := (_root_.GD.N0111.d006162 he0 he1).1
  dsimp [_root_.GD.N0111.d006159, _root_.GD.N0111.d006136]
  nlinarith [mul_nonneg hh ht]

theorem d006167
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 < _root_.GD.N0111.d006159 α β := by
  dsimp [_root_.GD.N0111.d006159]
  positivity




theorem d006168
    {α β e s t r : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ min α β / (4 * (α + β)))
    (ht : 0 ≤ t) (hr : 0 ≤ r) :
    |_root_.GD.N0111.d006141
        (α / (α + β) - e)
        (α * β / (α + β))
        (β - (α + β) * e)
        (e * (1 - e) / 2)
        r s t p q| ≤
      _root_.GD.N0111.d006160 α β r p q := by
  let c := α * β / (α + β)
  let d := β - (α + β) * e
  let h := e * (1 - e) / 2
  let a := α / (α + β) - e
  let N := _root_.GD.N0111.d006136 c d h s t
  let L := _root_.GD.N0111.d006159 α β
  have hLN : L ≤ N := by
    simpa [L, N, c, d, h] using
      _root_.GD.N0111.d006166 hα hβ he0 he1 hs ht
  have hL0 : 0 < L := by
    simpa [L] using _root_.GD.N0111.d006167 hα hβ
  have hN0 : 0 ≤ N := hL0.le.trans hLN
  have hpow₀ :
      |N ^ (-r - (p + q : ℕ))| ≤
        _root_.GD.N0111.d006153 L r (p + q) := by
    rw [abs_of_nonneg (Real.rpow_nonneg hN0 _)]
    exact _root_.GD.N0111.d006156 hL0 hLN hr
  have hpow₁ :
      |N ^ (-r - ((p - 1) + q : ℕ))| ≤
        _root_.GD.N0111.d006153 L r ((p - 1) + q) := by
    rw [abs_of_nonneg (Real.rpow_nonneg hN0 _)]
    exact _root_.GD.N0111.d006156 hL0 hLN hr
  have ha : |a + s| ≤ 9 / 8 := by
    simpa [a] using _root_.GD.N0111.d006164 hα hβ he0 he1 hs
  have hd : |d| ≤ max α β := by
    simpa [d] using
      _root_.GD.N0111.d006161 hα.le hβ.le he0 he1
  have hh : |h| ≤ 1 / 8 := by
    have hb := _root_.GD.N0111.d006162 he0 he1
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hmain :=
    _root_.GD.N0111.d006158
      (a := a) (c := c) (d := d) (h := h) (r := r)
      (s := s) (t := t) (A := 9 / 8) (D := max α β)
      (H := 1 / 8)
      (P₀ := _root_.GD.N0111.d006153 L r (p + q))
      (P₁ := _root_.GD.N0111.d006153 L r ((p - 1) + q))
      hr ha hd hh hpow₀ hpow₁
      (by norm_num)
      (hα.le.trans (le_max_left α β))
      (by norm_num)
  simpa [a, c, d, h, N, L, _root_.GD.N0111.d006160] using hmain





theorem d006169 :
    List.Forall
      (fun pq : ℕ × ℕ => pq.1 + pq.2 ≤ 5)
      [(0, 1), (1, 1), (3, 0), (2, 1), (4, 0),
        (0, 2), (3, 1), (5, 0), (1, 2)] := by
  norm_num

end GD.N0111
