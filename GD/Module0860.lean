import GD.Module0837






































open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1436

noncomputable section




def d013207 (m : ℕ) : ℝ :=
  (((m - 1 : ℕ) : ℝ) / 2)


def d013208 (n : ℕ) : ℝ :=
  (((n - 1 : ℕ) : ℝ) / 2)


def d013209 : ℝ := (3 : ℝ) / 2


def d013210 (m n : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1436.d013207 m + _root_.GD.N0232.N0720.N1436.d013208 n + _root_.GD.N0232.N0720.N1436.d013209

theorem d013211
    {m : ℕ} (hm : 2 ≤ m) :
    0 < _root_.GD.N0232.N0720.N1436.d013207 m := by
  unfold _root_.GD.N0232.N0720.N1436.d013207
  have hm1 : 0 < m - 1 := by omega
  positivity

theorem d013212
    {n : ℕ} (hn : 2 ≤ n) :
    0 < _root_.GD.N0232.N0720.N1436.d013208 n := by
  unfold _root_.GD.N0232.N0720.N1436.d013208
  have hn1 : 0 < n - 1 := by omega
  positivity

theorem d013213 : 0 < _root_.GD.N0232.N0720.N1436.d013209 := by
  norm_num [_root_.GD.N0232.N0720.N1436.d013209]



theorem d013214 :
    _root_.GD.N0232.N0720.N1436.d013209 = (1 : ℝ) / 2 + 1 := by
  norm_num [_root_.GD.N0232.N0720.N1436.d013209]



theorem d013215 :
    2 * _root_.GD.N0232.N0720.N1436.d013209 = 3 := by
  norm_num [_root_.GD.N0232.N0720.N1436.d013209]

theorem d013216
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    0 < _root_.GD.N0232.N0720.N1436.d013210 m n := by
  unfold _root_.GD.N0232.N0720.N1436.d013210
  exact add_pos
    (add_pos (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn))
    _root_.GD.N0232.N0720.N1436.d013213




abbrev d013217 := ℝ × ℝ


def d013218 : Set _root_.GD.N0232.N0720.N1436.d013217 :=
  Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)

theorem d013219 :
    MeasurableSet _root_.GD.N0232.N0720.N1436.d013218 := by
  exact measurableSet_Ioo.prod measurableSet_Ioi


def d013220 (A B : ℝ) : ℝ := A + B


def d013221 (A B : ℝ) : ℝ := B / (A + B)


def d013222 (A B C : ℝ) : ℝ := C / (A + B)


def d013223 (L : ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) :
    ℝ × (ℝ × ℝ) :=
  (L * (1 - x.1), (L * x.1, L * x.2))

@[fun_prop]
theorem d013224 :
    Measurable (fun p : ℝ × ℝ ↦ _root_.GD.N0232.N0720.N1436.d013221 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1436.d013221
  fun_prop

@[fun_prop]
theorem d013225 :
    Measurable
      (fun p : ℝ × (ℝ × ℝ) ↦
        _root_.GD.N0232.N0720.N1436.d013222 p.1 p.2.1 p.2.2) := by
  unfold _root_.GD.N0232.N0720.N1436.d013222
  fun_prop

@[fun_prop]
theorem d013226 :
    Measurable
      (fun p : ℝ × _root_.GD.N0232.N0720.N1436.d013217 ↦
        _root_.GD.N0232.N0720.N1436.d013223 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1436.d013223
  fun_prop


theorem d013227
    {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    (_root_.GD.N0232.N0720.N1436.d013221 A B, _root_.GD.N0232.N0720.N1436.d013222 A B C) ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
  have hAB : 0 < A + B := add_pos hA hB
  constructor
  · constructor
    · exact div_pos hB hAB
    · rw [_root_.GD.N0232.N0720.N1436.d013221, div_lt_one hAB]
      linarith
  · exact div_pos hC hAB



theorem d013228
    {L : ℝ} {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hL : 0 < L) (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < (_root_.GD.N0232.N0720.N1436.d013223 L x).1 ∧
      0 < (_root_.GD.N0232.N0720.N1436.d013223 L x).2.1 ∧
      0 < (_root_.GD.N0232.N0720.N1436.d013223 L x).2.2 := by
  unfold _root_.GD.N0232.N0720.N1436.d013223 _root_.GD.N0232.N0720.N1436.d013218 at *
  exact ⟨mul_pos hL (sub_pos.mpr hx.1.2),
    mul_pos hL hx.1.1, mul_pos hL hx.2⟩


@[simp]
theorem d013229
    (L : ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1436.d013220
        (_root_.GD.N0232.N0720.N1436.d013223 L x).1
        (_root_.GD.N0232.N0720.N1436.d013223 L x).2.1 = L := by
  unfold _root_.GD.N0232.N0720.N1436.d013220 _root_.GD.N0232.N0720.N1436.d013223
  ring


@[simp]
theorem d013230
    {L : ℝ} (hL : L ≠ 0) (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1436.d013221
        (_root_.GD.N0232.N0720.N1436.d013223 L x).1
        (_root_.GD.N0232.N0720.N1436.d013223 L x).2.1 = x.1 := by
  unfold _root_.GD.N0232.N0720.N1436.d013221 _root_.GD.N0232.N0720.N1436.d013223
  field_simp [hL]
  ring


@[simp]
theorem d013231
    {L : ℝ} (hL : L ≠ 0) (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1436.d013222
        (_root_.GD.N0232.N0720.N1436.d013223 L x).1
        (_root_.GD.N0232.N0720.N1436.d013223 L x).2.1
        (_root_.GD.N0232.N0720.N1436.d013223 L x).2.2 = x.2 := by
  unfold _root_.GD.N0232.N0720.N1436.d013222 _root_.GD.N0232.N0720.N1436.d013223
  field_simp [hL]
  ring



theorem d013232
    {A B C : ℝ} (hAB : A + B ≠ 0) :
    _root_.GD.N0232.N0720.N1436.d013223 (A + B)
      (_root_.GD.N0232.N0720.N1436.d013221 A B, _root_.GD.N0232.N0720.N1436.d013222 A B C) = (A, (B, C)) := by
  unfold _root_.GD.N0232.N0720.N1436.d013223 _root_.GD.N0232.N0720.N1436.d013221 _root_.GD.N0232.N0720.N1436.d013222
  ext <;> field_simp [hAB] <;> ring





theorem d013233
    {lambda A B : ℝ} (hlambda : lambda ≠ 0) :
    _root_.GD.N0232.N0720.N1436.d013221 (lambda * A) (lambda * B) = _root_.GD.N0232.N0720.N1436.d013221 A B := by
  unfold _root_.GD.N0232.N0720.N1436.d013221
  by_cases hAB : A + B = 0
  · have hscale : lambda * A + lambda * B = 0 := by
      rw [← mul_add, hAB, mul_zero]
    simp [hAB, hscale]
  · field_simp [hlambda, hAB]



theorem d013234
    {lambda A B C : ℝ} (hlambda : lambda ≠ 0) :
    _root_.GD.N0232.N0720.N1436.d013222 (lambda * A) (lambda * B) (lambda * C) =
      _root_.GD.N0232.N0720.N1436.d013222 A B C := by
  unfold _root_.GD.N0232.N0720.N1436.d013222
  by_cases hAB : A + B = 0
  · have hscale : lambda * A + lambda * B = 0 := by
      rw [← mul_add, hAB, mul_zero]
    simp [hAB, hscale]
  · field_simp [hlambda, hAB]

theorem d013235
    (lambda A B : ℝ) :
    _root_.GD.N0232.N0720.N1436.d013220 (lambda * A) (lambda * B) =
      lambda * _root_.GD.N0232.N0720.N1436.d013220 A B := by
  unfold _root_.GD.N0232.N0720.N1436.d013220
  ring


def d013236 (c t u : ℝ) : ℝ := c * (1 - t) * u


def d013237 (c t v : ℝ) : ℝ := c * t * v


def d013238 (c w : ℝ) : ℝ := c * w


def d013239 (t u v : ℝ) : ℝ :=
  (1 - t) * u + t * v

theorem d013240
    (c t u v : ℝ) :
    _root_.GD.N0232.N0720.N1436.d013236 c t u + _root_.GD.N0232.N0720.N1436.d013237 c t v =
      c * _root_.GD.N0232.N0720.N1436.d013239 t u v := by
  unfold _root_.GD.N0232.N0720.N1436.d013236 _root_.GD.N0232.N0720.N1436.d013237 _root_.GD.N0232.N0720.N1436.d013239
  ring



theorem d013241
    {c t u v : ℝ}
    (hc : c ≠ 0) (hden : _root_.GD.N0232.N0720.N1436.d013239 t u v ≠ 0) :
    _root_.GD.N0232.N0720.N1436.d013221 (_root_.GD.N0232.N0720.N1436.d013236 c t u) (_root_.GD.N0232.N0720.N1436.d013237 c t v) =
      t * v / _root_.GD.N0232.N0720.N1436.d013239 t u v := by
  unfold _root_.GD.N0232.N0720.N1436.d013221
  rw [_root_.GD.N0232.N0720.N1436.d013240]
  unfold _root_.GD.N0232.N0720.N1436.d013237
  field_simp [hc, hden]



theorem d013242
    {c t u v w : ℝ}
    (hc : c ≠ 0) (hden : _root_.GD.N0232.N0720.N1436.d013239 t u v ≠ 0) :
    _root_.GD.N0232.N0720.N1436.d013222 (_root_.GD.N0232.N0720.N1436.d013236 c t u) (_root_.GD.N0232.N0720.N1436.d013237 c t v) (_root_.GD.N0232.N0720.N1436.d013238 c w) =
      w / _root_.GD.N0232.N0720.N1436.d013239 t u v := by
  unfold _root_.GD.N0232.N0720.N1436.d013222
  rw [_root_.GD.N0232.N0720.N1436.d013240]
  unfold _root_.GD.N0232.N0720.N1436.d013238
  field_simp [hc, hden]

theorem d013243
    {t u v : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hu : 0 < u) (hv : 0 < v) :
    0 < _root_.GD.N0232.N0720.N1436.d013239 t u v := by
  unfold _root_.GD.N0232.N0720.N1436.d013239
  positivity


theorem d013244
    {c t u v w : ℝ}
    (hc : 0 < c) (ht0 : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    (_root_.GD.N0232.N0720.N1436.d013221 (_root_.GD.N0232.N0720.N1436.d013236 c t u) (_root_.GD.N0232.N0720.N1436.d013237 c t v),
      _root_.GD.N0232.N0720.N1436.d013222 (_root_.GD.N0232.N0720.N1436.d013236 c t u) (_root_.GD.N0232.N0720.N1436.d013237 c t v) (_root_.GD.N0232.N0720.N1436.d013238 c w))
        ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
  apply _root_.GD.N0232.N0720.N1436.d013227
  · unfold _root_.GD.N0232.N0720.N1436.d013236
    positivity
  · unfold _root_.GD.N0232.N0720.N1436.d013237
    positivity
  · unfold _root_.GD.N0232.N0720.N1436.d013238
    positivity



theorem d013245
    (A B : ℝ) :
    B / (A + B) = _root_.GD.N0232.N0720.N1436.d013221 A B := by
  rfl



theorem d013246
    {c t u v : ℝ}
    (hc : c ≠ 0) (hden : _root_.GD.N0232.N0720.N1436.d013239 t u v ≠ 0) :
    _root_.GD.N0232.N0720.N1436.d013237 c t v / (_root_.GD.N0232.N0720.N1436.d013236 c t u + _root_.GD.N0232.N0720.N1436.d013237 c t v) =
      t * v / ((1 - t) * u + t * v) := by
  simpa [_root_.GD.N0232.N0720.N1436.d013221, _root_.GD.N0232.N0720.N1436.d013239] using
    (_root_.GD.N0232.N0720.N1436.d013241 (c := c) (t := t) (u := u) (v := v) hc hden)



theorem d013247
    {A B C : ℝ} (hAB : A + B ≠ 0) (hC : C ≠ 0) :
    _root_.GD.N0232.N0720.N1436.d013221 A B =
      (A / (A + B)) * (B / C) +
        (B / (A + B)) * (1 - A / C) := by
  unfold _root_.GD.N0232.N0720.N1436.d013221
  field_simp [hAB, hC]
  ring




def d013248 (c t : ℝ) : ℝ := c * (1 - t)

def d013249 (c t : ℝ) : ℝ := c * t

theorem d013250
    (c t : ℝ) :
    _root_.GD.N0232.N0720.N1436.d013248 c t + _root_.GD.N0232.N0720.N1436.d013249 c t = c := by
  unfold _root_.GD.N0232.N0720.N1436.d013248 _root_.GD.N0232.N0720.N1436.d013249
  ring


theorem d013251
    {c t : ℝ} (hc : c ≠ 0) :
    _root_.GD.N0144.d006699
      (_root_.GD.N0232.N0720.N1436.d013248 c t) (_root_.GD.N0232.N0720.N1436.d013249 c t) = t := by
  unfold _root_.GD.N0144.d006699
  rw [_root_.GD.N0232.N0720.N1436.d013250]
  unfold _root_.GD.N0232.N0720.N1436.d013249
  field_simp [hc]


theorem d013252
    {c t : ℝ} (hc : c ≠ 0) :
    _root_.GD.N0144.d006699
          (_root_.GD.N0232.N0720.N1436.d013248 c t) (_root_.GD.N0232.N0720.N1436.d013249 c t) ^ 2 *
        _root_.GD.N0232.N0720.N1436.d013248 c t +
      (1 - _root_.GD.N0144.d006699
          (_root_.GD.N0232.N0720.N1436.d013248 c t) (_root_.GD.N0232.N0720.N1436.d013249 c t)) ^ 2 *
        _root_.GD.N0232.N0720.N1436.d013249 c t =
      c * t * (1 - t) := by
  rw [_root_.GD.N0232.N0720.N1436.d013251 hc]
  unfold _root_.GD.N0232.N0720.N1436.d013248 _root_.GD.N0232.N0720.N1436.d013249
  ring




def d013253 (A B t : ℝ) : ℝ :=
  A / (1 - t) + B / t


def d013254 (x y : ℝ) : ℝ :=
  y / (x + y)


theorem d013255
    {x y t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    _root_.GD.N0232.N0720.N1436.d013253 (x ^ 2) (y ^ 2) t - (x + y) ^ 2 =
      (x * t - y * (1 - t)) ^ 2 / (t * (1 - t)) := by
  unfold _root_.GD.N0232.N0720.N1436.d013253
  field_simp [ht0, sub_ne_zero.mpr ht1.symm]
  ring



theorem d013256
    {x y t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (x + y) ^ 2 ≤ _root_.GD.N0232.N0720.N1436.d013253 (x ^ 2) (y ^ 2) t := by
  have hcompletion := _root_.GD.N0232.N0720.N1436.d013255
    (x := x) (y := y) (t := t) ht0.ne' ht1.ne
  have hquot : 0 ≤
      (x * t - y * (1 - t)) ^ 2 / (t * (1 - t)) := by
    exact div_nonneg (sq_nonneg _) (mul_nonneg ht0.le (sub_pos.mpr ht1).le)
  linarith



theorem d013257
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    _root_.GD.N0232.N0720.N1436.d013254 x y ∈ Ioo (0 : ℝ) 1 := by
  have hsum : 0 < x + y := add_pos hx hy
  constructor
  · exact div_pos hy hsum
  · unfold _root_.GD.N0232.N0720.N1436.d013254
    rw [div_lt_one hsum]
    linarith


theorem d013258
    {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1436.d013253 (x ^ 2) (y ^ 2) t = (x + y) ^ 2 ↔
      t = _root_.GD.N0232.N0720.N1436.d013254 x y := by
  have hsum : x + y ≠ 0 := (add_pos hx hy).ne'
  constructor
  · intro hmin
    have hzero :
        _root_.GD.N0232.N0720.N1436.d013253 (x ^ 2) (y ^ 2) t - (x + y) ^ 2 = 0 := by
      linarith
    rw [_root_.GD.N0232.N0720.N1436.d013255 ht0.ne' ht1.ne] at hzero
    have hden : t * (1 - t) ≠ 0 :=
      mul_ne_zero ht0.ne' (sub_pos.mpr ht1).ne'
    have hnumsq : (x * t - y * (1 - t)) ^ 2 = 0 := by
      have hmul := congrArg (fun z : ℝ ↦ z * (t * (1 - t))) hzero
      simpa [hden] using hmul
    have hlinear : x * t - y * (1 - t) = 0 := by
      nlinarith [sq_nonneg (x * t - y * (1 - t))]
    unfold _root_.GD.N0232.N0720.N1436.d013254
    apply (eq_div_iff hsum).2
    nlinarith
  · intro ht
    rw [ht]
    unfold _root_.GD.N0232.N0720.N1436.d013254 _root_.GD.N0232.N0720.N1436.d013253
    field_simp [hsum, hx.ne', hy.ne']
    ring



def d013259 (alpha r : ℝ) : ℝ :=
  Real.sqrt (alpha * (1 - r))


def d013260 (beta r : ℝ) : ℝ :=
  Real.sqrt (beta * r)

theorem d013261
    {alpha r : ℝ} (halpha : 0 < alpha) (hr1 : r < 1) :
    0 < _root_.GD.N0232.N0720.N1436.d013259 alpha r := by
  unfold _root_.GD.N0232.N0720.N1436.d013259
  exact Real.sqrt_pos.2 (mul_pos halpha (sub_pos.mpr hr1))

theorem d013262
    {beta r : ℝ} (hbeta : 0 < beta) (hr0 : 0 < r) :
    0 < _root_.GD.N0232.N0720.N1436.d013260 beta r := by
  unfold _root_.GD.N0232.N0720.N1436.d013260
  exact Real.sqrt_pos.2 (mul_pos hbeta hr0)

theorem d013263
    {alpha r : ℝ} (halpha : 0 ≤ alpha) (hr1 : r ≤ 1) :
    _root_.GD.N0232.N0720.N1436.d013259 alpha r ^ 2 = alpha * (1 - r) := by
  unfold _root_.GD.N0232.N0720.N1436.d013259
  exact Real.sq_sqrt (mul_nonneg halpha (sub_nonneg.mpr hr1))

theorem d013264
    {beta r : ℝ} (hbeta : 0 ≤ beta) (hr0 : 0 ≤ r) :
    _root_.GD.N0232.N0720.N1436.d013260 beta r ^ 2 = beta * r := by
  unfold _root_.GD.N0232.N0720.N1436.d013260
  exact Real.sq_sqrt (mul_nonneg hbeta hr0)



def d013265 (alpha beta r : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1436.d013254
    (_root_.GD.N0232.N0720.N1436.d013259 alpha r) (_root_.GD.N0232.N0720.N1436.d013260 beta r)





theorem d013266
    {alpha beta r : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hr0 : 0 < r) (hr1 : r < 1) :
    _root_.GD.N0232.N0720.N1436.d013265 alpha beta r = r ↔
      r = beta / (alpha + beta) := by
  let x := _root_.GD.N0232.N0720.N1436.d013259 alpha r
  let y := _root_.GD.N0232.N0720.N1436.d013260 beta r
  have hx : 0 < x := _root_.GD.N0232.N0720.N1436.d013261 halpha hr1
  have hy : 0 < y := _root_.GD.N0232.N0720.N1436.d013262 hbeta hr0
  have hx2 : x ^ 2 = alpha * (1 - r) :=
    _root_.GD.N0232.N0720.N1436.d013263 halpha.le hr1.le
  have hy2 : y ^ 2 = beta * r :=
    _root_.GD.N0232.N0720.N1436.d013264 hbeta.le hr0.le
  have hsum : x + y ≠ 0 := (add_pos hx hy).ne'
  have hab : alpha + beta ≠ 0 := (add_pos halpha hbeta).ne'
  change y / (x + y) = r ↔ r = beta / (alpha + beta)
  constructor
  · intro hshare
    have hlinear : y * (1 - r) = r * x := by
      have hcross := (div_eq_iff hsum).mp hshare
      nlinarith
    have hsquare := congrArg (fun z : ℝ ↦ z ^ 2) hlinear
    have hfactor :
        (r * (1 - r)) * (beta * (1 - r)) =
          (r * (1 - r)) * (alpha * r) := by
      rw [mul_pow, mul_pow, hy2, hx2] at hsquare
      nlinarith
    have hrprod : r * (1 - r) ≠ 0 :=
      mul_ne_zero hr0.ne' (sub_pos.mpr hr1).ne'
    have hratio : beta * (1 - r) = alpha * r :=
      mul_left_cancel₀ hrprod hfactor
    apply (eq_div_iff hab).2
    nlinarith
  · intro hratioValue
    have hratio : beta * (1 - r) = alpha * r := by
      have hcross := (eq_div_iff hab).mp hratioValue
      nlinarith
    have hsquare : (y * (1 - r)) ^ 2 = (r * x) ^ 2 := by
      rw [mul_pow, mul_pow, hy2, hx2]
      nlinarith
    have hleft : 0 < y * (1 - r) := mul_pos hy (sub_pos.mpr hr1)
    have hright : 0 < r * x := mul_pos hr0 hx
    have hlinear : y * (1 - r) = r * x := by
      nlinarith
    apply (div_eq_iff hsum).2
    nlinarith





def d013267
    (m n : ℕ) (t : ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  x.2 +
    ((m - 1 : ℕ) : ℝ) * (1 - x.1) / (1 - t) +
    ((n - 1 : ℕ) : ℝ) * x.1 / t


def d013268
    (m n : ℕ) (t : ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1436.d013267 m n t x / 2


def d013269
    (m n : ℕ) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  (1 - x.1) ^ (_root_.GD.N0232.N0720.N1436.d013207 m - 1) *
    x.1 ^ (_root_.GD.N0232.N0720.N1436.d013208 n - 1) *
    x.2 ^ (_root_.GD.N0232.N0720.N1436.d013209 - 1)


def d013270
    (m n : ℕ) (t : ℝ) : ℝ :=
  (1 - t) ^ (-_root_.GD.N0232.N0720.N1436.d013207 m) *
    t ^ (-_root_.GD.N0232.N0720.N1436.d013208 n)


def d013271 (m n : ℕ) : ℝ :=
  (_root_.GD.N0232.N0720.N1436.d013207 m) ^ (_root_.GD.N0232.N0720.N1436.d013207 m) /
      Real.Gamma (_root_.GD.N0232.N0720.N1436.d013207 m) *
    ((_root_.GD.N0232.N0720.N1436.d013208 n) ^ (_root_.GD.N0232.N0720.N1436.d013208 n) /
      Real.Gamma (_root_.GD.N0232.N0720.N1436.d013208 n)) *
    (((1 : ℝ) / 2) ^ _root_.GD.N0232.N0720.N1436.d013209 / Real.Gamma _root_.GD.N0232.N0720.N1436.d013209)



def d013272
    (m n : ℕ) (t : ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) (L : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1436.d013271 m n *
    _root_.GD.N0232.N0720.N1436.d013270 m n t *
    _root_.GD.N0232.N0720.N1436.d013269 m n x *
    (L ^ (_root_.GD.N0232.N0720.N1436.d013210 m n - 1) *
      Real.exp (-(L * _root_.GD.N0232.N0720.N1436.d013268 m n t x)))


def d013273
    (m n : ℕ) (t : ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1436.d013271 m n *
    _root_.GD.N0232.N0720.N1436.d013270 m n t *
    _root_.GD.N0232.N0720.N1436.d013269 m n x *
    ((1 / _root_.GD.N0232.N0720.N1436.d013268 m n t x) ^ (_root_.GD.N0232.N0720.N1436.d013210 m n) *
      Real.Gamma (_root_.GD.N0232.N0720.N1436.d013210 m n))



def d013274
    (m n : ℕ) (t : ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1436.d013269 m n x *
    _root_.GD.N0232.N0720.N1436.d013270 m n t *
    (_root_.GD.N0232.N0720.N1436.d013267 m n t x) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n)

private theorem d013275 (p : ℝ) :
    Measurable (fun x : ℝ ↦ x ^ p) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const fun x hx ↦ Or.inl hx

@[fun_prop]
theorem d013276
    (m n : ℕ) (t : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1436.d013267 m n t) := by
  unfold _root_.GD.N0232.N0720.N1436.d013267
  fun_prop

@[fun_prop]
theorem d013277
    (m n : ℕ) (t : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1436.d013268 m n t) := by
  unfold _root_.GD.N0232.N0720.N1436.d013268
  fun_prop

@[fun_prop]
theorem d013278
    (m n : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1436.d013269 m n) := by
  unfold _root_.GD.N0232.N0720.N1436.d013269
  exact
    (((_root_.GD.N0232.N0720.N1436.d013275 (_root_.GD.N0232.N0720.N1436.d013207 m - 1)).comp
      (measurable_const.sub measurable_fst)).mul
      ((_root_.GD.N0232.N0720.N1436.d013275 (_root_.GD.N0232.N0720.N1436.d013208 n - 1)).comp
        measurable_fst)).mul
      ((_root_.GD.N0232.N0720.N1436.d013275 (_root_.GD.N0232.N0720.N1436.d013209 - 1)).comp measurable_snd)

@[fun_prop]
theorem d013279
    (m n : ℕ) (t : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1436.d013273 m n t) := by
  unfold _root_.GD.N0232.N0720.N1436.d013273
  exact
    (measurable_const.mul (_root_.GD.N0232.N0720.N1436.d013278 m n)).mul
      (((_root_.GD.N0232.N0720.N1436.d013275 (_root_.GD.N0232.N0720.N1436.d013210 m n)).comp
        (measurable_const.div (_root_.GD.N0232.N0720.N1436.d013277 m n t))).mul
        measurable_const)

theorem d013280
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0232.N0720.N1436.d013267 m n t x := by
  have hm1N : 0 < m - 1 := by omega
  have hn1N : 0 < n - 1 := by omega
  have hm1 : 0 < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hm1N
  have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hn1N
  unfold _root_.GD.N0232.N0720.N1436.d013267 _root_.GD.N0232.N0720.N1436.d013218 at *
  have hleft : 0 <
      ((m - 1 : ℕ) : ℝ) * (1 - x.1) / (1 - t) := by
    exact div_pos (mul_pos hm1 (sub_pos.mpr hx.1.2)) (sub_pos.mpr ht1)
  have hright : 0 <
      ((n - 1 : ℕ) : ℝ) * x.1 / t := by
    exact div_pos (mul_pos hn1 hx.1.1) ht0
  exact add_pos (add_pos hx.2 hleft) hright

theorem d013281
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0232.N0720.N1436.d013268 m n t x := by
  unfold _root_.GD.N0232.N0720.N1436.d013268
  exact div_pos (_root_.GD.N0232.N0720.N1436.d013280 hm hn ht0 ht1 hx) (by norm_num)

theorem d013282
    {m n : ℕ} {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0232.N0720.N1436.d013269 m n x := by
  unfold _root_.GD.N0232.N0720.N1436.d013269 _root_.GD.N0232.N0720.N1436.d013218 at *
  exact mul_pos
    (mul_pos
      (Real.rpow_pos_of_pos (sub_pos.mpr hx.1.2) _)
      (Real.rpow_pos_of_pos hx.1.1 _))
    (Real.rpow_pos_of_pos hx.2 _)

theorem d013283
    {m n : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    0 < _root_.GD.N0232.N0720.N1436.d013270 m n t := by
  unfold _root_.GD.N0232.N0720.N1436.d013270
  exact mul_pos
    (Real.rpow_pos_of_pos (sub_pos.mpr ht1) _)
    (Real.rpow_pos_of_pos ht0 _)

theorem d013284
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    0 < _root_.GD.N0232.N0720.N1436.d013271 m n := by
  unfold _root_.GD.N0232.N0720.N1436.d013271
  exact mul_pos
    (mul_pos
      (div_pos
        (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1436.d013211 hm) _)
        (Real.Gamma_pos_of_pos (_root_.GD.N0232.N0720.N1436.d013211 hm)))
      (div_pos
        (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1436.d013212 hn) _)
        (Real.Gamma_pos_of_pos (_root_.GD.N0232.N0720.N1436.d013212 hn))))
    (div_pos
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) _)
      (Real.Gamma_pos_of_pos _root_.GD.N0232.N0720.N1436.d013213))



theorem d013285
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    (∫ L : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1436.d013272 m n t x L) =
      _root_.GD.N0232.N0720.N1436.d013273 m n t x := by
  have hshape : 0 < _root_.GD.N0232.N0720.N1436.d013210 m n :=
    _root_.GD.N0232.N0720.N1436.d013216 hm hn
  have hrate : 0 < _root_.GD.N0232.N0720.N1436.d013268 m n t x :=
    _root_.GD.N0232.N0720.N1436.d013281 hm hn ht0 ht1 hx
  unfold _root_.GD.N0232.N0720.N1436.d013272 _root_.GD.N0232.N0720.N1436.d013273
  rw [show
      (fun L : ℝ ↦
        _root_.GD.N0232.N0720.N1436.d013271 m n *
            _root_.GD.N0232.N0720.N1436.d013270 m n t *
            _root_.GD.N0232.N0720.N1436.d013269 m n x *
            (L ^ (_root_.GD.N0232.N0720.N1436.d013210 m n - 1) *
              Real.exp (-(L * _root_.GD.N0232.N0720.N1436.d013268 m n t x)))) =
        fun L : ℝ ↦
          (_root_.GD.N0232.N0720.N1436.d013271 m n *
            _root_.GD.N0232.N0720.N1436.d013270 m n t *
            _root_.GD.N0232.N0720.N1436.d013269 m n x) *
          (L ^ (_root_.GD.N0232.N0720.N1436.d013210 m n - 1) *
            Real.exp (-(L * _root_.GD.N0232.N0720.N1436.d013268 m n t x))) by
      funext L
      ring]
  rw [integral_const_mul]
  have hradial :
      (∫ L : ℝ in Ioi 0,
        L ^ (_root_.GD.N0232.N0720.N1436.d013210 m n - 1) *
          Real.exp (-(L * _root_.GD.N0232.N0720.N1436.d013268 m n t x))) =
        (1 / _root_.GD.N0232.N0720.N1436.d013268 m n t x) ^ (_root_.GD.N0232.N0720.N1436.d013210 m n) *
          Real.Gamma (_root_.GD.N0232.N0720.N1436.d013210 m n) := by
    simpa [mul_comm] using
      (Real.integral_rpow_mul_exp_neg_mul_Ioi hshape hrate)
  rw [hradial]

theorem d013286
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0232.N0720.N1436.d013273 m n t x := by
  unfold _root_.GD.N0232.N0720.N1436.d013273
  exact mul_pos
    (mul_pos
      (mul_pos
        (_root_.GD.N0232.N0720.N1436.d013284 hm hn)
        (_root_.GD.N0232.N0720.N1436.d013283 ht0 ht1))
      (_root_.GD.N0232.N0720.N1436.d013282 hx))
    (mul_pos
      (Real.rpow_pos_of_pos
        (one_div_pos.mpr (_root_.GD.N0232.N0720.N1436.d013281 hm hn ht0 ht1 hx)) _)
      (Real.Gamma_pos_of_pos (_root_.GD.N0232.N0720.N1436.d013216 hm hn)))

theorem d013287
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0232.N0720.N1436.d013274 m n t x := by
  unfold _root_.GD.N0232.N0720.N1436.d013274
  exact mul_pos
    (mul_pos
      (_root_.GD.N0232.N0720.N1436.d013282 hx)
      (_root_.GD.N0232.N0720.N1436.d013283 ht0 ht1))
    (Real.rpow_pos_of_pos
      (_root_.GD.N0232.N0720.N1436.d013280 hm hn ht0 ht1 hx) _)




def d013288 : Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  volume.restrict _root_.GD.N0232.N0720.N1436.d013218


def d013289
    (m n : ℕ) (t : ℝ) : Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  _root_.GD.N0232.N0720.N1436.d013288.withDensity
    (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 m n t x))



theorem d013290
    (m n : ℕ) (t : ℝ) :
    _root_.GD.N0232.N0720.N1436.d013289 m n t ≪ _root_.GD.N0232.N0720.N1436.d013288 := by
  unfold _root_.GD.N0232.N0720.N1436.d013289
  exact withDensity_absolutelyContinuous _ _



theorem d013291
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1436.d013288 ≪ _root_.GD.N0232.N0720.N1436.d013289 m n t := by
  unfold _root_.GD.N0232.N0720.N1436.d013289
  apply withDensity_absolutelyContinuous'
  · exact (_root_.GD.N0232.N0720.N1436.d013279 m n t).ennreal_ofReal.aemeasurable
  · unfold _root_.GD.N0232.N0720.N1436.d013288
    filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219]
      with x hx
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (_root_.GD.N0232.N0720.N1436.d013286 hm hn ht0 ht1 hx)



theorem d013292
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t u : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hu0 : 0 < u) (hu1 : u < 1) :
    _root_.GD.N0232.N0720.N1436.d013289 m n t ≪ _root_.GD.N0232.N0720.N1436.d013289 m n u := by
  exact
    (_root_.GD.N0232.N0720.N1436.d013290 m n t).trans
      (_root_.GD.N0232.N0720.N1436.d013291
        hm hn hu0 hu1)

theorem d013293
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t u : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hu0 : 0 < u) (hu1 : u < 1) :
    (_root_.GD.N0232.N0720.N1436.d013289 m n t ≪ _root_.GD.N0232.N0720.N1436.d013289 m n u) ∧
      (_root_.GD.N0232.N0720.N1436.d013289 m n u ≪ _root_.GD.N0232.N0720.N1436.d013289 m n t) := by
  exact ⟨
    _root_.GD.N0232.N0720.N1436.d013292 hm hn ht0 ht1 hu0 hu1,
    _root_.GD.N0232.N0720.N1436.d013292 hm hn hu0 hu1 ht0 ht1⟩



theorem d013294
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t u : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hu0 : 0 < u) (hu1 : u < 1)
    {f g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} :
    f =ᵐ[_root_.GD.N0232.N0720.N1436.d013289 m n t] g ↔
      f =ᵐ[_root_.GD.N0232.N0720.N1436.d013289 m n u] g := by
  let h := _root_.GD.N0232.N0720.N1436.d013293
    hm hn ht0 ht1 hu0 hu1
  exact ⟨fun hfg ↦ h.2.ae_eq hfg, fun hfg ↦ h.1.ae_eq hfg⟩

end

end N1436
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1436.d013232
#print axioms _root_.GD.N0232.N0720.N1436.d013233
#print axioms _root_.GD.N0232.N0720.N1436.d013234
#print axioms _root_.GD.N0232.N0720.N1436.d013241
#print axioms _root_.GD.N0232.N0720.N1436.d013247
#print axioms _root_.GD.N0232.N0720.N1436.d013251
#print axioms _root_.GD.N0232.N0720.N1436.d013255
#print axioms _root_.GD.N0232.N0720.N1436.d013266
#print axioms _root_.GD.N0232.N0720.N1436.d013285
#print axioms _root_.GD.N0232.N0720.N1436.d013287
#print axioms _root_.GD.N0232.N0720.N1436.d013293
#print axioms _root_.GD.N0232.N0720.N1436.d013294
