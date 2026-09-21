import GD.Module0860
import GD.Module0216






















open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1432

noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1422





def d013390
    (m n : ℕ) (x : _root_.GD.N0232.N0720.N1436.d013217) (t : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1422.d002985
    (_root_.GD.N0232.N0720.N1436.d013207 m)
    (_root_.GD.N0232.N0720.N1436.d013208 n)
    (_root_.GD.N0232.N0720.N1436.d013210 m n)
    (((m - 1 : ℕ) : ℝ))
    (((n - 1 : ℕ) : ℝ))
    x.1 x.2 t



theorem d013391
    (m n : ℕ) (x : _root_.GD.N0232.N0720.N1436.d013217) (t : ℝ) :
    x.2 + _root_.GD.N0232.N0720.N1422.d002977
        (((m - 1 : ℕ) : ℝ)) (((n - 1 : ℕ) : ℝ)) x.1 t =
      _root_.GD.N0232.N0720.N1436.d013267 m n t x := by
  unfold _root_.GD.N0232.N0720.N1422.d002977 _root_.GD.N0232.N0720.N1436.d013267
  ring



theorem d013392
    (m n : ℕ) (x : _root_.GD.N0232.N0720.N1436.d013217) (t : ℝ) :
    _root_.GD.N0232.N0720.N1432.d013390 m n x t =
      _root_.GD.N0232.N0720.N1436.d013270 m n t *
        (_root_.GD.N0232.N0720.N1436.d013267 m n t x) ^
          (-_root_.GD.N0232.N0720.N1436.d013210 m n) := by
  unfold _root_.GD.N0232.N0720.N1432.d013390 _root_.GD.N0232.N0720.N1422.d002985
    _root_.GD.N0232.N0720.N1436.d013270
  rw [_root_.GD.N0232.N0720.N1432.d013391]
  ring



theorem d013393
    (m n : ℕ) (x : _root_.GD.N0232.N0720.N1436.d013217) (t : ℝ) :
    _root_.GD.N0232.N0720.N1436.d013274 m n t x =
      _root_.GD.N0232.N0720.N1436.d013269 m n x *
        _root_.GD.N0232.N0720.N1432.d013390 m n x t := by
  rw [_root_.GD.N0232.N0720.N1432.d013392]
  unfold _root_.GD.N0232.N0720.N1436.d013274
  ring



theorem d013394
    {m n : ℕ} {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0232.N0720.N1436.d013269 m n x :=
  _root_.GD.N0232.N0720.N1436.d013282 hx



theorem d013395
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < _root_.GD.N0232.N0720.N1432.d013390 m n x t := by
  rw [_root_.GD.N0232.N0720.N1432.d013392]
  exact mul_pos
    (_root_.GD.N0232.N0720.N1436.d013283 ht0 ht1)
    (Real.rpow_pos_of_pos
      (_root_.GD.N0232.N0720.N1436.d013280 hm hn ht0 ht1 hx) _)






theorem d013396
    (prior : Measure ℝ) (likelihood : ℝ → ℝ) (action factor : ℝ) :
    _root_.GD.N0232.N0720.N1422.d002989 prior
        (fun t ↦ factor * likelihood t) action =
      factor * _root_.GD.N0232.N0720.N1422.d002989 prior likelihood action := by
  unfold _root_.GD.N0232.N0720.N1422.d002989
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring



theorem d013397
    (prior : Measure ℝ) (m n : ℕ)
    (x : _root_.GD.N0232.N0720.N1436.d013217) (action : ℝ) :
    _root_.GD.N0232.N0720.N1422.d002989 prior
        (fun t ↦ _root_.GD.N0232.N0720.N1436.d013274 m n t x) action =
      _root_.GD.N0232.N0720.N1436.d013269 m n x *
        _root_.GD.N0232.N0720.N1422.d002989 prior
          (_root_.GD.N0232.N0720.N1432.d013390 m n x) action := by
  have hfun :
      (fun t ↦ _root_.GD.N0232.N0720.N1436.d013274 m n t x) =
        fun t ↦ _root_.GD.N0232.N0720.N1436.d013269 m n x *
          _root_.GD.N0232.N0720.N1432.d013390 m n x t := by
    funext t
    exact _root_.GD.N0232.N0720.N1432.d013393
      m n x t
  rw [hfun, _root_.GD.N0232.N0720.N1432.d013396]



theorem d013398
    (prior : Measure ℝ) (m n : ℕ)
    {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (action : ℝ) :
    _root_.GD.N0232.N0720.N1422.d002989 prior
        (fun t ↦ _root_.GD.N0232.N0720.N1436.d013274 m n t x) action = 0 ↔
      _root_.GD.N0232.N0720.N1422.d002989 prior
        (_root_.GD.N0232.N0720.N1432.d013390 m n x) action = 0 := by
  rw [_root_.GD.N0232.N0720.N1432.d013397]
  exact mul_eq_zero.trans (or_iff_right (_root_.GD.N0232.N0720.N1432.d013394 hx).ne')




theorem d013399
    (prior : Measure ℝ) (likelihood : ℝ → ℝ) (factor : ℝ) :
    _root_.GD.N0232.N0720.N1422.d002986 prior (fun t ↦ factor * likelihood t) =
      factor * _root_.GD.N0232.N0720.N1422.d002986 prior likelihood := by
  unfold _root_.GD.N0232.N0720.N1422.d002986
  exact integral_const_mul factor likelihood



theorem d013400
    (prior : Measure ℝ) (likelihood : ℝ → ℝ) (factor : ℝ) :
    _root_.GD.N0232.N0720.N1422.d002987 prior (fun t ↦ factor * likelihood t) =
      factor * _root_.GD.N0232.N0720.N1422.d002987 prior likelihood := by
  unfold _root_.GD.N0232.N0720.N1422.d002987
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring




theorem d013401
    (prior : Measure ℝ) (likelihood : ℝ → ℝ) (factor : ℝ)
    (hfactor : factor ≠ 0) :
    _root_.GD.N0232.N0720.N1422.d002988 prior (fun t ↦ factor * likelihood t) =
      _root_.GD.N0232.N0720.N1422.d002988 prior likelihood := by
  unfold _root_.GD.N0232.N0720.N1422.d002988
  rw [_root_.GD.N0232.N0720.N1432.d013400, _root_.GD.N0232.N0720.N1432.d013399]
  exact mul_div_mul_left _ _ hfactor



theorem d013402
    (prior : Measure ℝ) (m n : ℕ)
    {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1422.d002988 prior
        (fun t ↦ _root_.GD.N0232.N0720.N1436.d013274 m n t x) =
      _root_.GD.N0232.N0720.N1422.d002988 prior (_root_.GD.N0232.N0720.N1432.d013390 m n x) := by
  have hfun :
      (fun t ↦ _root_.GD.N0232.N0720.N1436.d013274 m n t x) =
        fun t ↦ _root_.GD.N0232.N0720.N1436.d013269 m n x *
          _root_.GD.N0232.N0720.N1432.d013390 m n x t := by
    funext t
    exact _root_.GD.N0232.N0720.N1432.d013393
      m n x t
  rw [hfun]
  exact _root_.GD.N0232.N0720.N1432.d013401 prior (_root_.GD.N0232.N0720.N1432.d013390 m n x)
    (_root_.GD.N0232.N0720.N1436.d013269 m n x) (_root_.GD.N0232.N0720.N1432.d013394 hx).ne'

end

end N1432
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1432.d013393
#print axioms _root_.GD.N0232.N0720.N1432.d013395
#print axioms _root_.GD.N0232.N0720.N1432.d013398
#print axioms _root_.GD.N0232.N0720.N1432.d013402
