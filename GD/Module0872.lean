import GD.Module0870









open MeasureTheory Set

namespace GD.N0232.N0720.N1336

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1271 (d013403 d013408)

variable (m n : ℕ)

def d013420 (x : _root_.GD.N0232.N0720.N1436.d013217) (t : _root_.GD.N0232.N0720.N1290.d004131) : ℝ :=
  ((n - 1 : ℕ) : ℝ) * x.1 * (1 - (t : ℝ)) +
    ((m - 1 : ℕ) : ℝ) * (1 - x.1) * (t : ℝ) + x.2 * _root_.GD.N0232.N0720.N1271.d013403 t

@[fun_prop] theorem d013421 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1436.d013217 × _root_.GD.N0232.N0720.N1290.d004131 ↦ _root_.GD.N0232.N0720.N1336.d013420 m n p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1336.d013420 _root_.GD.N0232.N0720.N1271.d013403
  fun_prop

theorem d013422
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1290.d004131) :
    min (((n - 1 : ℕ) : ℝ) * x.1) (((m - 1 : ℕ) : ℝ) * (1 - x.1)) ≤
      _root_.GD.N0232.N0720.N1336.d013420 m n x t := by
  have h1 := mul_le_mul_of_nonneg_right
    (min_le_left (((n - 1 : ℕ) : ℝ) * x.1) (((m - 1 : ℕ) : ℝ) * (1 - x.1)))
    (sub_nonneg.mpr t.2.2)
  have h2 := mul_le_mul_of_nonneg_right
    (min_le_right (((n - 1 : ℕ) : ℝ) * x.1) (((m - 1 : ℕ) : ℝ) * (1 - x.1))) t.2.1
  have h3 : 0 ≤ x.2 * _root_.GD.N0232.N0720.N1271.d013403 t :=
    mul_nonneg hx.2.le (mul_nonneg t.2.1 (sub_nonneg.mpr t.2.2))
  unfold _root_.GD.N0232.N0720.N1336.d013420
  nlinarith

theorem d013423 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1290.d004131) :
    0 < _root_.GD.N0232.N0720.N1336.d013420 m n x t := by
  have hm1 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hn1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  exact (lt_min (mul_pos hn1 hx.1.1) (mul_pos hm1 (sub_pos.mpr hx.1.2))).trans_le
    (_root_.GD.N0232.N0720.N1336.d013422 m n hx t)

theorem d013424 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1436.d013210 m n = ((m : ℝ) + n + 1) / 2 := by
  unfold _root_.GD.N0232.N0720.N1436.d013210 _root_.GD.N0232.N0720.N1436.d013207 _root_.GD.N0232.N0720.N1436.d013208 _root_.GD.N0232.N0720.N1436.d013209
  rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

theorem d013425 (x : _root_.GD.N0232.N0720.N1436.d013217)
    (t : _root_.GD.N0232.N0720.N1290.d004131) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    _root_.GD.N0232.N0720.N1271.d013403 t * _root_.GD.N0232.N0720.N1436.d013267 m n t x = _root_.GD.N0232.N0720.N1336.d013420 m n x t := by
  unfold _root_.GD.N0232.N0720.N1336.d013420 _root_.GD.N0232.N0720.N1436.d013267 _root_.GD.N0232.N0720.N1271.d013403
  field_simp [ht0.ne', (sub_pos.mpr ht1).ne']
  ring

def d013426 (t : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1436.d013270 m n t * (_root_.GD.N0232.N0720.N1271.d013403 t) ^ _root_.GD.N0232.N0720.N1436.d013210 m n

theorem d013427 {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < _root_.GD.N0232.N0720.N1336.d013426 m n t :=
  mul_pos (_root_.GD.N0232.N0720.N1436.d013283 ht0 ht1)
    (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1271.d013408 ht0 ht1) _)

@[fun_prop] theorem d013428 :
    Continuous (fun t : Ioo (0 : ℝ) 1 ↦ _root_.GD.N0232.N0720.N1336.d013426 m n t.1) := by
  unfold _root_.GD.N0232.N0720.N1336.d013426 _root_.GD.N0232.N0720.N1436.d013270
  apply Continuous.mul
  · apply Continuous.mul
    · exact (continuous_const.sub continuous_subtype_val).rpow_const
        (fun t ↦ Or.inl (sub_pos.mpr t.2.2).ne')
    · exact continuous_subtype_val.rpow_const (fun t ↦ Or.inl t.2.1.ne')
  · exact (by unfold _root_.GD.N0232.N0720.N1271.d013403; fun_prop :
      Continuous (fun t : Ioo (0 : ℝ) 1 ↦ _root_.GD.N0232.N0720.N1271.d013403 t.1)).rpow_const
      (fun t ↦ Or.inl (_root_.GD.N0232.N0720.N1271.d013408 t.2.1 t.2.2).ne')

def d013429 (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1436.d013271 m n * _root_.GD.N0232.N0720.N1436.d013269 m n x *
    (2 : ℝ) ^ _root_.GD.N0232.N0720.N1436.d013210 m n * Real.Gamma (_root_.GD.N0232.N0720.N1436.d013210 m n)

theorem d013430 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0232.N0720.N1336.d013429 m n x :=
  mul_pos (mul_pos
    (mul_pos (_root_.GD.N0232.N0720.N1436.d013284 hm hn) (_root_.GD.N0232.N0720.N1436.d013282 hx))
    (Real.rpow_pos_of_pos (by norm_num) _))
    (Real.Gamma_pos_of_pos (_root_.GD.N0232.N0720.N1436.d013216 hm hn))

theorem d013431 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218)
    (t : _root_.GD.N0232.N0720.N1290.d004131) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    _root_.GD.N0232.N0720.N1436.d013273 m n t x = _root_.GD.N0232.N0720.N1336.d013429 m n x *
      _root_.GD.N0232.N0720.N1336.d013426 m n t * (_root_.GD.N0232.N0720.N1336.d013420 m n x t) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n) := by
  have hv := _root_.GD.N0232.N0720.N1271.d013408 ht0 ht1
  have hp := _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx t
  have hrate : 1 / _root_.GD.N0232.N0720.N1436.d013268 m n t x =
      2 * _root_.GD.N0232.N0720.N1271.d013403 t / _root_.GD.N0232.N0720.N1336.d013420 m n x t := by
    unfold _root_.GD.N0232.N0720.N1436.d013268
    have h := _root_.GD.N0232.N0720.N1336.d013425 m n x t ht0 ht1
    have hr := _root_.GD.N0232.N0720.N1436.d013280 hm hn ht0 ht1 hx
    field_simp [hp.ne', hr.ne']
    nlinarith
  unfold _root_.GD.N0232.N0720.N1436.d013273 _root_.GD.N0232.N0720.N1336.d013429 _root_.GD.N0232.N0720.N1336.d013426
  rw [hrate, Real.div_rpow (mul_pos (by norm_num) hv).le hp.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hv.le, Real.rpow_neg hp.le]
  ring

end
end GD.N0232.N0720.N1336

#print axioms _root_.GD.N0232.N0720.N1336.d013431
