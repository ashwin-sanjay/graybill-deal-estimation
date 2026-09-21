import GD.Module0860
import GD.Module0221













namespace GD
namespace N0232
namespace N0720
namespace N1430

noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1462


def d013369 (t x : ℝ) : ℝ :=
  1 - t + t * x



def d013370 (t : ℝ) (z : ℝ × ℝ) : _root_.GD.N0232.N0720.N1436.d013217 :=
  (t * z.1 / _root_.GD.N0232.N0720.N1430.d013369 t z.1,
    z.2 / _root_.GD.N0232.N0720.N1430.d013369 t z.1)


def d013371 (t : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  (1 - t) * z.1 / (t * (1 - z.1))


def d013372 (t : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  (1 - t) * z.2 / (1 - z.1)

theorem d013373
    {t x : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hx : 0 < x) :
    0 < _root_.GD.N0232.N0720.N1430.d013369 t x := by
  unfold _root_.GD.N0232.N0720.N1430.d013369
  positivity

theorem d013374
    {t x : ℝ} (hden : _root_.GD.N0232.N0720.N1430.d013369 t x ≠ 0) (y : ℝ) :
    1 - (_root_.GD.N0232.N0720.N1430.d013370 t (x, y)).1 =
      (1 - t) / _root_.GD.N0232.N0720.N1430.d013369 t x := by
  unfold _root_.GD.N0232.N0720.N1430.d013370
  dsimp
  calc
    1 - t * x / _root_.GD.N0232.N0720.N1430.d013369 t x =
        _root_.GD.N0232.N0720.N1430.d013369 t x / _root_.GD.N0232.N0720.N1430.d013369 t x -
          t * x / _root_.GD.N0232.N0720.N1430.d013369 t x := by
            rw [div_self hden]
    _ = (_root_.GD.N0232.N0720.N1430.d013369 t x - t * x) /
          _root_.GD.N0232.N0720.N1430.d013369 t x := by rw [sub_div]
    _ = (1 - t) / _root_.GD.N0232.N0720.N1430.d013369 t x := by
      congr 1
      unfold _root_.GD.N0232.N0720.N1430.d013369
      ring

theorem d013375
    {t x : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hden : _root_.GD.N0232.N0720.N1430.d013369 t x ≠ 0) (y : ℝ) :
    _root_.GD.N0232.N0720.N1430.d013371 t (_root_.GD.N0232.N0720.N1430.d013370 t (x, y)) = x := by
  unfold _root_.GD.N0232.N0720.N1430.d013371
  rw [_root_.GD.N0232.N0720.N1430.d013374 hden y]
  unfold _root_.GD.N0232.N0720.N1430.d013370
  dsimp
  field_simp [ht0, sub_ne_zero.mpr ht1, hden]

theorem d013376
    {t x : ℝ} (ht1 : t ≠ 1)
    (hden : _root_.GD.N0232.N0720.N1430.d013369 t x ≠ 0) (y : ℝ) :
    _root_.GD.N0232.N0720.N1430.d013372 t (_root_.GD.N0232.N0720.N1430.d013370 t (x, y)) = y := by
  unfold _root_.GD.N0232.N0720.N1430.d013372
  rw [_root_.GD.N0232.N0720.N1430.d013374 hden y]
  unfold _root_.GD.N0232.N0720.N1430.d013370
  dsimp
  field_simp [sub_ne_zero.mpr ht1, hden]

theorem d013377
    {t x y : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hx : 0 < x) (hy : 0 < y) :
    _root_.GD.N0232.N0720.N1430.d013370 t (x, y) ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
  have hden : 0 < _root_.GD.N0232.N0720.N1430.d013369 t x :=
    _root_.GD.N0232.N0720.N1430.d013373 ht0 ht1 hx
  constructor
  · constructor
    · unfold _root_.GD.N0232.N0720.N1430.d013370
      dsimp
      positivity
    · apply sub_pos.mp
      rw [_root_.GD.N0232.N0720.N1430.d013374 hden.ne' y]
      exact div_pos (sub_pos.mpr ht1) hden
  · unfold _root_.GD.N0232.N0720.N1430.d013370
    dsimp
    exact div_pos hy hden




theorem d013378
    {c t u v w : ℝ}
    (hc : c ≠ 0) (ht0 : t ≠ 0)
    (hu : u ≠ 0) (hden : _root_.GD.N0232.N0720.N1436.d013239 t u v ≠ 0) :
    (_root_.GD.N0232.N0720.N1436.d013221 (_root_.GD.N0232.N0720.N1436.d013236 c t u) (_root_.GD.N0232.N0720.N1436.d013237 c t v),
        _root_.GD.N0232.N0720.N1436.d013222 (_root_.GD.N0232.N0720.N1436.d013236 c t u) (_root_.GD.N0232.N0720.N1436.d013237 c t v) (_root_.GD.N0232.N0720.N1436.d013238 c w)) =
      _root_.GD.N0232.N0720.N1430.d013370 t (v / u, w / u) := by
  rw [_root_.GD.N0232.N0720.N1436.d013241 hc hden, _root_.GD.N0232.N0720.N1436.d013242 hc hden]
  unfold _root_.GD.N0232.N0720.N1430.d013370 _root_.GD.N0232.N0720.N1430.d013369 _root_.GD.N0232.N0720.N1436.d013239
  ext <;> dsimp <;> field_simp [hu, ht0, hden]




def d013379 (t x : ℝ) : ℝ :=
  t * (1 - t) / (_root_.GD.N0232.N0720.N1430.d013369 t x) ^ 3

theorem d013380
    {t x : ℝ} (hden : _root_.GD.N0232.N0720.N1430.d013369 t x ≠ 0) :
    (t * (1 - t) / (_root_.GD.N0232.N0720.N1430.d013369 t x) ^ 2) *
        (1 / _root_.GD.N0232.N0720.N1430.d013369 t x) =
      _root_.GD.N0232.N0720.N1430.d013379 t x := by
  unfold _root_.GD.N0232.N0720.N1430.d013379
  field_simp [hden]



theorem d013381
    {m n : ℕ} {t x y : ℝ}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hden : _root_.GD.N0232.N0720.N1430.d013369 t x ≠ 0) :
    _root_.GD.N0232.N0720.N1436.d013267 m n t (_root_.GD.N0232.N0720.N1430.d013370 t (x, y)) =
      (y + ((m - 1 : ℕ) : ℝ) + ((n - 1 : ℕ) : ℝ) * x) /
        _root_.GD.N0232.N0720.N1430.d013369 t x := by
  unfold _root_.GD.N0232.N0720.N1436.d013267
  rw [_root_.GD.N0232.N0720.N1430.d013374 hden y]
  unfold _root_.GD.N0232.N0720.N1430.d013370
  dsimp
  field_simp [ht0, sub_ne_zero.mpr ht1, hden]



theorem d013382
    {m n : ℕ} {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1462.d003110
        (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t z.1 z.2 =
      t * (1 - t) / 2 * _root_.GD.N0232.N0720.N1436.d013267 m n t z := by
  unfold _root_.GD.N0232.N0720.N1462.d003110 _root_.GD.N0232.N0720.N1436.d013267
  unfold _root_.GD.N0232.N0720.N1436.d013207 _root_.GD.N0232.N0720.N1436.d013208
  field_simp [ht0, sub_ne_zero.mpr ht1]
  ring



noncomputable def d013383
    (alpha beta t r s : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1462.d003121 alpha beta r s *
    _root_.GD.N0232.N0720.N1462.d003110 alpha beta t r s ^
      (-_root_.GD.N0232.N0720.N1462.d003109 alpha beta)



noncomputable def d013384
    (m n : ℕ) (t : ℝ) : ℝ :=
  (t * (1 - t) / 2) ^ (_root_.GD.N0232.N0720.N1436.d013210 m n) *
    _root_.GD.N0232.N0720.N1436.d013270 m n t



theorem d013385
    (m n : ℕ) (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1436.d013269 m n z =
      _root_.GD.N0232.N0720.N1462.d003121 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)
        z.1 z.2 := by
  unfold _root_.GD.N0232.N0720.N1436.d013269 _root_.GD.N0232.N0720.N1462.d003121 _root_.GD.N0232.N0720.N1436.d013209
  have hexp : (3 : ℝ) / 2 - 1 = 1 / 2 := by norm_num
  rw [hexp]
  ac_rfl


theorem d013386
    (m n : ℕ) :
    _root_.GD.N0232.N0720.N1436.d013210 m n =
      _root_.GD.N0232.N0720.N1462.d003109 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) := by
  rfl




theorem d013387
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {z : _root_.GD.N0232.N0720.N1436.d013217} (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1436.d013274 m n t z =
      _root_.GD.N0232.N0720.N1430.d013384 m n t *
        _root_.GD.N0232.N0720.N1430.d013383
          (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t z.1 z.2 := by
  let scale : ℝ := t * (1 - t) / 2
  let rate : ℝ := _root_.GD.N0232.N0720.N1436.d013267 m n t z
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  have hrate : 0 < rate := by
    exact _root_.GD.N0232.N0720.N1436.d013280 hm hn ht0 ht1 hz
  have hden :
      _root_.GD.N0232.N0720.N1462.d003110
          (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t z.1 z.2 =
        scale * rate := by
    simpa [scale, rate] using
      (_root_.GD.N0232.N0720.N1430.d013382
        (m := m) (n := n) ht0.ne' ht1.ne z)
  unfold _root_.GD.N0232.N0720.N1436.d013274 _root_.GD.N0232.N0720.N1430.d013384 _root_.GD.N0232.N0720.N1430.d013383
  rw [_root_.GD.N0232.N0720.N1430.d013385, hden,
    _root_.GD.N0232.N0720.N1430.d013386,
    Real.mul_rpow hscale.le hrate.le]
  have hcancel :
      scale ^ _root_.GD.N0232.N0720.N1462.d003109 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) *
          scale ^ (-_root_.GD.N0232.N0720.N1462.d003109
            (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)) = 1 := by
    rw [← Real.rpow_add hscale]
    simp
  change
    _root_.GD.N0232.N0720.N1462.d003121 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) z.1 z.2 *
          _root_.GD.N0232.N0720.N1436.d013270 m n t *
          rate ^ (-_root_.GD.N0232.N0720.N1462.d003109
            (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)) = _
  calc
    _ = (scale ^ _root_.GD.N0232.N0720.N1462.d003109
            (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) *
          scale ^ (-_root_.GD.N0232.N0720.N1462.d003109
            (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n))) *
        (_root_.GD.N0232.N0720.N1462.d003121 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)
          z.1 z.2 * _root_.GD.N0232.N0720.N1436.d013270 m n t *
          rate ^ (-_root_.GD.N0232.N0720.N1462.d003109
            (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n))) := by
          rw [hcancel, one_mul]
    _ = _ := by ring



theorem d013388
    {m n : ℕ} {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (r S : ℝ) :
    t * (1 - t) / 2 *
        _root_.GD.N0232.N0720.N1436.d013267 m n t (r, S / t) =
      _root_.GD.N0232.N0720.N1462.d003111
        (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t r S := by
  rw [← _root_.GD.N0232.N0720.N1430.d013382
    (m := m) (n := n) ht0 ht1 (r, S / t)]
  exact _root_.GD.N0232.N0720.N1462.d003112 ht0
    (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) r S



theorem d013389
    {m n : ℕ} {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (r S : ℝ) :
    t * (1 - t) / 2 *
        _root_.GD.N0232.N0720.N1436.d013267 m n t (r, S / t) =
      _root_.GD.N0232.N0720.N1462.d003113 (_root_.GD.N0232.N0720.N1436.d013208 n) r S +
        t * (_root_.GD.N0232.N0720.N1436.d013207 m * (1 - r) -
          _root_.GD.N0232.N0720.N1436.d013208 n * r - S / 2) := by
  rw [_root_.GD.N0232.N0720.N1430.d013388 ht0 ht1]
  exact _root_.GD.N0232.N0720.N1462.d003115
    (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t r S

end

end N1430
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1430.d013378
#print axioms _root_.GD.N0232.N0720.N1430.d013380
#print axioms _root_.GD.N0232.N0720.N1430.d013381
#print axioms _root_.GD.N0232.N0720.N1430.d013382
#print axioms _root_.GD.N0232.N0720.N1430.d013387
#print axioms _root_.GD.N0232.N0720.N1430.d013389
