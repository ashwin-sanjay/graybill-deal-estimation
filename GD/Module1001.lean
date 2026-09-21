import GD.Module0917
import GD.Module1000
























open Set

namespace GD
namespace N0232
namespace N0720
namespace N1172

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1498
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229


abbrev d015905 := _root_.GD.N0232.N0720.N1486.d015856


def d015906 (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) : _root_.GD.N0232.N0720.N1172.d015905 :=
  (g.shift + g.d009239 * theta.1,
    (⟨g.d009239 ^ 2 * (theta.2.1 : ℝ),
        mul_pos (sq_pos_of_pos g.d009240) theta.2.1.property⟩,
      theta.2.2))

@[simp] theorem d015907
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    (_root_.GD.N0232.N0720.N1172.d015906 g theta).1 =
      g.shift + g.d009239 * theta.1 := rfl

@[simp] theorem d015908
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    ((_root_.GD.N0232.N0720.N1172.d015906 g theta).2.1 : ℝ) =
      g.d009239 ^ 2 * (theta.2.1 : ℝ) := rfl

@[simp] theorem d015909
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    (_root_.GD.N0232.N0720.N1172.d015906 g theta).2.2 = theta.2.2 := rfl

@[simp] theorem d015910 (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1172.d015906 1 theta = theta := by
  apply Prod.ext
  · simp [_root_.GD.N0232.N0720.N1172.d015906]
  · apply Prod.ext
    · apply Subtype.ext
      simp [_root_.GD.N0232.N0720.N1172.d015906]
    · rfl



theorem d015911
    (g h : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1172.d015906 g (_root_.GD.N0232.N0720.N1172.d015906 h theta) =
      _root_.GD.N0232.N0720.N1172.d015906 (g * h) theta := by
  apply Prod.ext
  · change
      g.shift + g.d009239 * (h.shift + h.d009239 * theta.1) =
        (g * h).shift + (g * h).d009239 * theta.1
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009235, _root_.GD.N0232.N0719.N0946.d009229.d009243]
    simp only [_root_.GD.N0232.N0719.N0946.d009229.d009239]
    ring
  · apply Prod.ext
    · apply Subtype.ext
      simp only [_root_.GD.N0232.N0720.N1172.d015908, _root_.GD.N0232.N0719.N0946.d009229.d009243]
      ring
    · rfl

@[simp] theorem d015912
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1172.d015906 g (_root_.GD.N0232.N0720.N1172.d015906 g⁻¹ theta) = theta := by
  rw [_root_.GD.N0232.N0720.N1172.d015911]
  simp

@[simp] theorem d015913
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1172.d015906 g⁻¹ (_root_.GD.N0232.N0720.N1172.d015906 g theta) = theta := by
  rw [_root_.GD.N0232.N0720.N1172.d015911]
  simp



private theorem d015914
    (m : ℕ) (g : _root_.GD.N0232.N0719.N0946.d009229) (q : Set.Ioi (0 : ℝ))
    (z : Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1498.d012567 m
        (g.d009239 ^ 2 * (q : ℝ)) (z : ℝ) =
      g.d009239 * _root_.GD.N0232.N0720.N1498.d012567 m (q : ℝ) (z : ℝ) := by
  have ha : 0 < g.d009239 := g.d009240
  unfold _root_.GD.N0232.N0720.N1498.d012567
  rw [show
      (m : ℝ) * (g.d009239 ^ 2 * (q : ℝ)) / (z : ℝ) =
        g.d009239 ^ 2 * ((m : ℝ) * (q : ℝ) / (z : ℝ)) by ring,
    Real.sqrt_mul (sq_nonneg g.d009239), Real.sqrt_sq_eq_abs,
    abs_of_pos ha]

private theorem d015915
    (n : ℕ) (g : _root_.GD.N0232.N0719.N0946.d009229) (q : Set.Ioi (0 : ℝ))
    (z : Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1498.d012568 n
        (g.d009239 ^ 2 * (q : ℝ)) (z : ℝ) =
      g.d009239 * _root_.GD.N0232.N0720.N1498.d012568 n (q : ℝ) (z : ℝ) := by
  have ha : 0 < g.d009239 := g.d009240
  unfold _root_.GD.N0232.N0720.N1498.d012568
  rw [show
      (n : ℝ) * (g.d009239 ^ 2 * (q : ℝ)) / (1 - (z : ℝ)) =
        g.d009239 ^ 2 *
          ((n : ℝ) * (q : ℝ) / (1 - (z : ℝ))) by ring,
    Real.sqrt_mul (sq_nonneg g.d009239), Real.sqrt_sq_eq_abs,
    abs_of_pos ha]



theorem d015916
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1486.d015873 m n hm hn (_root_.GD.N0232.N0720.N1172.d015906 g theta) =
      _root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1486.d015873 m n hm hn theta) := by
  apply _root_.GD.N0232.N0720.N1215.d014277
  · rfl
  · exact _root_.GD.N0232.N0720.N1172.d015914 m g theta.2.1 theta.2.2
  · exact _root_.GD.N0232.N0720.N1172.d015915 n g theta.2.1 theta.2.2




def d015917 (theta eta : _root_.GD.N0232.N0720.N1172.d015905) : ℝ :=
  (eta.2.1 : ℝ) / (theta.2.1 : ℝ)


def d015918 (theta eta : _root_.GD.N0232.N0720.N1172.d015905) : ℝ :=
  Real.sqrt (_root_.GD.N0232.N0720.N1172.d015917 theta eta)


def d015919 (theta eta : _root_.GD.N0232.N0720.N1172.d015905) : ℝ :=
  (eta.1 - theta.1) / Real.sqrt (theta.2.1 : ℝ)

theorem d015920 (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    0 < _root_.GD.N0232.N0720.N1172.d015917 theta eta := by
  exact div_pos eta.2.1.property theta.2.1.property

theorem d015921 (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    0 < _root_.GD.N0232.N0720.N1172.d015918 theta eta := by
  exact Real.sqrt_pos.2 (_root_.GD.N0232.N0720.N1172.d015920 theta eta)


@[simp] theorem d015922
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1172.d015917 (_root_.GD.N0232.N0720.N1172.d015906 g theta)
        (_root_.GD.N0232.N0720.N1172.d015906 g eta) = _root_.GD.N0232.N0720.N1172.d015917 theta eta := by
  have htheta : 0 < (theta.2.1 : ℝ) :=
    show 0 < (theta.2.1 : ℝ) from theta.2.1.property
  unfold _root_.GD.N0232.N0720.N1172.d015917
  simp only [_root_.GD.N0232.N0720.N1172.d015908]
  field_simp [g.d009240.ne', htheta.ne']


@[simp] theorem d015923
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1172.d015918 (_root_.GD.N0232.N0720.N1172.d015906 g theta)
        (_root_.GD.N0232.N0720.N1172.d015906 g eta) = _root_.GD.N0232.N0720.N1172.d015918 theta eta := by
  simp [_root_.GD.N0232.N0720.N1172.d015918]


@[simp] theorem d015924
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1172.d015919 (_root_.GD.N0232.N0720.N1172.d015906 g theta)
        (_root_.GD.N0232.N0720.N1172.d015906 g eta) = _root_.GD.N0232.N0720.N1172.d015919 theta eta := by
  have ha : 0 < g.d009239 := g.d009240
  have hsqrt : Real.sqrt (theta.2.1 : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 theta.2.1.property).ne'
  unfold _root_.GD.N0232.N0720.N1172.d015919
  simp only [_root_.GD.N0232.N0720.N1172.d015907, _root_.GD.N0232.N0720.N1172.d015908]
  rw [Real.sqrt_mul (sq_nonneg g.d009239), Real.sqrt_sq_eq_abs,
    abs_of_pos ha]
  field_simp [ha.ne', hsqrt]
  ring


theorem d015925
    (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1172.d015917 theta eta * (theta.2.1 : ℝ) = (eta.2.1 : ℝ) := by
  have htheta : (theta.2.1 : ℝ) ≠ 0 :=
    (show 0 < (theta.2.1 : ℝ) from theta.2.1.property).ne'
  unfold _root_.GD.N0232.N0720.N1172.d015917
  field_simp [htheta]


theorem d015926 (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1172.d015918 theta eta ^ 2 = _root_.GD.N0232.N0720.N1172.d015917 theta eta := by
  unfold _root_.GD.N0232.N0720.N1172.d015918
  exact Real.sq_sqrt (_root_.GD.N0232.N0720.N1172.d015920 theta eta).le


theorem d015927
    (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1172.d015918 theta eta ^ 2 * (theta.2.1 : ℝ) =
      (eta.2.1 : ℝ) := by
  rw [_root_.GD.N0232.N0720.N1172.d015926, _root_.GD.N0232.N0720.N1172.d015925]


theorem d015928
    (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    theta.1 + Real.sqrt (theta.2.1 : ℝ) *
        _root_.GD.N0232.N0720.N1172.d015919 theta eta = eta.1 := by
  unfold _root_.GD.N0232.N0720.N1172.d015919
  have hsqrt : Real.sqrt (theta.2.1 : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 theta.2.1.property).ne'
  field_simp [hsqrt]
  ring




def d015929 (g : _root_.GD.N0232.N0719.N0946.d009229) : ℝ :=
  g.d009239 ^ 3

theorem d015930
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1486.d015857 (_root_.GD.N0232.N0720.N1172.d015906 g theta).2.1 *
        _root_.GD.N0232.N0720.N1172.d015929 g =
      g.d009239 ^ (-(2 : ℝ)) *
        _root_.GD.N0232.N0720.N1486.d015857 theta.2.1 := by
  have ha : 0 < g.d009239 := g.d009240
  have hq : 0 < (theta.2.1 : ℝ) := theta.2.1.property
  unfold _root_.GD.N0232.N0720.N1486.d015857 _root_.GD.N0232.N0720.N1172.d015929
  simp only [_root_.GD.N0232.N0720.N1172.d015908]
  rw [Real.mul_rpow (sq_nonneg g.d009239) hq.le]
  have hcomm :
      ((g.d009239 ^ 2) ^ (-(5 / 2 : ℝ)) *
          (theta.2.1 : ℝ) ^ (-(5 / 2 : ℝ))) * g.d009239 ^ 3 =
        ((g.d009239 ^ 2) ^ (-(5 / 2 : ℝ)) * g.d009239 ^ 3) *
          (theta.2.1 : ℝ) ^ (-(5 / 2 : ℝ)) := by
    ring
  rw [hcomm]
  have hpow2 : g.d009239 ^ 2 = g.d009239 ^ (2 : ℝ) :=
    (Real.rpow_two g.d009239).symm
  have hpow3 : g.d009239 ^ 3 = g.d009239 ^ (3 : ℝ) :=
    (Real.rpow_natCast g.d009239 3).symm
  rw [hpow2, hpow3, ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
  congr 1
  ring_nf



theorem d015931
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    ((_root_.GD.N0232.N0720.N1172.d015906 g eta).1 - (_root_.GD.N0232.N0720.N1172.d015906 g theta).1) ^ 2 =
      g.d009239 ^ 2 * (eta.1 - theta.1) ^ 2 := by
  simp only [_root_.GD.N0232.N0720.N1172.d015907]
  ring





theorem d015932
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta eta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1486.d015857 (_root_.GD.N0232.N0720.N1172.d015906 g theta).2.1 *
        _root_.GD.N0232.N0720.N1172.d015929 g *
          ((_root_.GD.N0232.N0720.N1172.d015906 g eta).1 -
            (_root_.GD.N0232.N0720.N1172.d015906 g theta).1) ^ 2 =
      _root_.GD.N0232.N0720.N1486.d015857 theta.2.1 * (eta.1 - theta.1) ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1172.d015930,
    _root_.GD.N0232.N0720.N1172.d015931]
  have ha : 0 < g.d009239 := g.d009240
  calc
    (g.d009239 ^ (-(2 : ℝ)) * _root_.GD.N0232.N0720.N1486.d015857 theta.2.1) *
          (g.d009239 ^ 2 * (eta.1 - theta.1) ^ 2) =
        (g.d009239 ^ (-(2 : ℝ)) * g.d009239 ^ (2 : ℝ)) *
          (_root_.GD.N0232.N0720.N1486.d015857 theta.2.1 * (eta.1 - theta.1) ^ 2) := by
      rw [show g.d009239 ^ 2 = g.d009239 ^ (2 : ℝ) by
        simp]
      ring
    _ = _root_.GD.N0232.N0720.N1486.d015857 theta.2.1 * (eta.1 - theta.1) ^ 2 := by
      rw [← Real.rpow_add ha]
      norm_num

end

end N1172
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1172.d015916
#print axioms _root_.GD.N0232.N0720.N1172.d015923
#print axioms _root_.GD.N0232.N0720.N1172.d015924
#print axioms _root_.GD.N0232.N0720.N1172.d015932
