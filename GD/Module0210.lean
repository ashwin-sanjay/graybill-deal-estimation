import GD.Module0209















open Set

namespace GD.N0232.N0720.N1376

open _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1379

noncomputable section

def d002892 (t X Y z w : ℝ) : ℝ :=
  (1 - t) * (X ^ 2 + 2 * z) + t * (Y ^ 2 + 2 * w)

def d002893 (t X Y : ℝ) : ℝ := (1 - t) * X + t * Y


def d002894 (kappa t X Y z w : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1377.d002852 5 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w) (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) / 8


def d002895 (kappa t X Y z w : ℝ) : ℝ :=
  kappa * _root_.GD.N0232.N0720.N1377.d002852 4 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w) (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) / 8



theorem d002896 (t X Y z w : ℝ) :
    _root_.GD.N0232.N0720.N1376.d002892 t X Y z w - _root_.GD.N0232.N0720.N1376.d002893 t X Y ^ 2 =
      t * (1 - t) * (X - Y) ^ 2 + 2 * (1 - t) * z + 2 * t * w := by
  unfold _root_.GD.N0232.N0720.N1376.d002892 _root_.GD.N0232.N0720.N1376.d002893
  ring

theorem d002897
    {t z w : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hz : 0 < z) (hw : 0 < w)
    (X Y : ℝ) :
    0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w - _root_.GD.N0232.N0720.N1376.d002893 t X Y ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1376.d002896]
  have hquad : 0 ≤ t * (1 - t) * (X - Y) ^ 2 :=
    mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg _)
  have hzterm : 0 ≤ 2 * (1 - t) * z :=
    mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ht.2)) hz.le
  rcases eq_or_lt_of_le ht.1 with htzero | htpos
  · rw [← htzero]
    nlinarith
  · have hwterm : 0 < 2 * t * w := mul_pos (mul_pos (by norm_num) htpos) hw
    linarith

theorem d002898
    {t z w : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hz : 0 < z) (hw : 0 < w)
    (X Y : ℝ) :
    0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w := by
  have hgap := _root_.GD.N0232.N0720.N1376.d002897 ht hz hw X Y
  linarith [sq_nonneg (_root_.GD.N0232.N0720.N1376.d002893 t X Y)]

theorem d002899
    {t z w : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hz : 0 < z) (hw : 0 < w)
    (X Y : ℝ) :
    _root_.GD.N0232.N0720.N1376.d002893 t X Y ^ 2 / (2 * _root_.GD.N0232.N0720.N1376.d002892 t X Y z w) < (1 / 2 : ℝ) := by
  have hA := _root_.GD.N0232.N0720.N1376.d002898 ht hz hw X Y
  have hgap := _root_.GD.N0232.N0720.N1376.d002897 ht hz hw X Y
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hA)).2
  linarith

theorem d002900
    (kappa : ℝ) {t z w : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hz : 0 < z) (hw : 0 < w) (X Y : ℝ) :
    0 < _root_.GD.N0232.N0720.N1376.d002894 kappa t X Y z w := by
  exact div_pos (_root_.GD.N0232.N0720.N1377.d002861 5 (_root_.GD.N0232.N0720.N1376.d002898 ht hz hw X Y)
    (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa)) (by norm_num)

theorem d002901
    {kappa t z w : ℝ} (hkappa : 0 ≤ kappa) (ht : t ∈ Icc (0 : ℝ) 1)
    (hz : 0 < z) (hw : 0 < w) (X Y : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1376.d002895 kappa t X Y z w := by
  exact div_nonneg (mul_nonneg hkappa
    (_root_.GD.N0232.N0720.N1377.d002861 4 (_root_.GD.N0232.N0720.N1376.d002898 ht hz hw X Y)
      (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa)).le) (by norm_num)

theorem d002902 (t X Y z w s : ℝ) :
    _root_.GD.N0232.N0720.N1376.d002892 t (s * X) (s * Y) (s ^ 2 * z) (s ^ 2 * w) =
      s ^ 2 * _root_.GD.N0232.N0720.N1376.d002892 t X Y z w := by
  unfold _root_.GD.N0232.N0720.N1376.d002892
  ring

theorem d002903 (t X Y s : ℝ) :
    _root_.GD.N0232.N0720.N1376.d002893 t (s * X) (s * Y) = s * _root_.GD.N0232.N0720.N1376.d002893 t X Y := by
  unfold _root_.GD.N0232.N0720.N1376.d002893
  ring


theorem d002904 (kappa t X Y z w : ℝ) {s : ℝ} (hs : 0 < s) :
    _root_.GD.N0232.N0720.N1376.d002894 kappa t (s * X) (s * Y) (s ^ 2 * z) (s ^ 2 * w) =
      (s ^ 6)⁻¹ * _root_.GD.N0232.N0720.N1376.d002894 kappa t X Y z w := by
  unfold _root_.GD.N0232.N0720.N1376.d002894
  rw [_root_.GD.N0232.N0720.N1376.d002902, _root_.GD.N0232.N0720.N1376.d002903]
  rw [show (s * _root_.GD.N0232.N0720.N1376.d002893 t X Y) * kappa = s * (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) by ring]
  rw [_root_.GD.N0232.N0720.N1377.d002866 5 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w) (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) hs]
  ring


theorem d002905 (kappa t X Y z w : ℝ) {s : ℝ} (hs : 0 < s) :
    _root_.GD.N0232.N0720.N1376.d002895 kappa t (s * X) (s * Y) (s ^ 2 * z) (s ^ 2 * w) =
      (s ^ 5)⁻¹ * _root_.GD.N0232.N0720.N1376.d002895 kappa t X Y z w := by
  unfold _root_.GD.N0232.N0720.N1376.d002895
  rw [_root_.GD.N0232.N0720.N1376.d002902, _root_.GD.N0232.N0720.N1376.d002903]
  rw [show (s * _root_.GD.N0232.N0720.N1376.d002893 t X Y) * kappa = s * (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) by ring]
  rw [_root_.GD.N0232.N0720.N1377.d002866 4 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w) (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) hs]
  ring

theorem d002906 (t X Y z w : ℝ) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002892 t X Y q w) (2 * (1 - t)) z := by
  have heq : (fun q : ℝ ↦ _root_.GD.N0232.N0720.N1376.d002892 t X Y q w) =
      (fun q ↦ (2 * (1 - t)) * q + ((1 - t) * X ^ 2 + t * (Y ^ 2 + 2 * w))) := by
    funext q
    unfold _root_.GD.N0232.N0720.N1376.d002892
    ring
  rw [heq]
  simpa using! ((hasDerivAt_id z).const_mul (2 * (1 - t))).add_const
    ((1 - t) * X ^ 2 + t * (Y ^ 2 + 2 * w))

theorem d002907 (t X Y z w : ℝ) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002892 t X Y z q) (2 * t) w := by
  have heq : (fun q : ℝ ↦ _root_.GD.N0232.N0720.N1376.d002892 t X Y z q) =
      (fun q ↦ (2 * t) * q + ((1 - t) * (X ^ 2 + 2 * z) + t * Y ^ 2)) := by
    funext q
    unfold _root_.GD.N0232.N0720.N1376.d002892
    ring
  rw [heq]
  simpa using! ((hasDerivAt_id w).const_mul (2 * t)).add_const
    ((1 - t) * (X ^ 2 + 2 * z) + t * Y ^ 2)

theorem d002908 (t X Y z w : ℝ) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002892 t q Y z w) (2 * (1 - t) * X) X := by
  have h : HasDerivAt (fun q : ℝ ↦ q ^ 2 + 2 * z) (2 * X) X := by
    simpa using! ((hasDerivAt_id X).pow 2).add_const (2 * z)
  convert! (h.const_mul (1 - t)).add_const (t * (Y ^ 2 + 2 * w)) using 1 <;>
    (try simp only [_root_.GD.N0232.N0720.N1376.d002892]) <;> ring

theorem d002909 (t X Y z w : ℝ) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002892 t X q z w) (2 * t * Y) Y := by
  have h : HasDerivAt (fun q : ℝ ↦ q ^ 2 + 2 * w) (2 * Y) Y := by
    simpa using! ((hasDerivAt_id Y).pow 2).add_const (2 * w)
  convert! (h.const_mul t).const_add ((1 - t) * (X ^ 2 + 2 * z)) using 1 <;>
    (try simp only [_root_.GD.N0232.N0720.N1376.d002892]) <;> ring

theorem d002910 (t X Y : ℝ) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002893 t q Y) (1 - t) X := by
  simpa only [_root_.GD.N0232.N0720.N1376.d002893, mul_one] using!
    ((hasDerivAt_id X).const_mul (1 - t)).add_const (t * Y)

theorem d002911 (t X Y : ℝ) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002893 t X q) t Y := by
  simpa only [_root_.GD.N0232.N0720.N1376.d002893, mul_one] using!
    ((hasDerivAt_id Y).const_mul t).const_add ((1 - t) * X)

theorem d002912 (kappa t X Y z w : ℝ)
    (hA : 0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002894 kappa t X Y q w)
      (-(1 - t) * _root_.GD.N0232.N0720.N1377.d002852 7 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w)
        (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) / 8) z := by
  have h := (_root_.GD.N0232.N0720.N1377.d002865 5 hA (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa)).comp z
    (_root_.GD.N0232.N0720.N1376.d002906 t X Y z w)
  convert! h.div_const 8 using 1 <;> (try simp only [_root_.GD.N0232.N0720.N1376.d002894, Function.comp_def]) <;> ring

theorem d002913 (kappa t X Y z w : ℝ)
    (hA : 0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002894 kappa t X Y z q)
      (-t * _root_.GD.N0232.N0720.N1377.d002852 7 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w)
        (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) / 8) w := by
  have h := (_root_.GD.N0232.N0720.N1377.d002865 5 hA (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa)).comp w
    (_root_.GD.N0232.N0720.N1376.d002907 t X Y z w)
  convert! h.div_const 8 using 1 <;> (try simp only [_root_.GD.N0232.N0720.N1376.d002894, Function.comp_def]) <;> ring

theorem d002914 (kappa t X Y z w : ℝ)
    (hA : 0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002895 kappa t X Y q w)
      (-kappa * (1 - t) * _root_.GD.N0232.N0720.N1377.d002852 6 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w)
        (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) / 8) z := by
  have h := (_root_.GD.N0232.N0720.N1377.d002865 4 hA (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa)).comp z
    (_root_.GD.N0232.N0720.N1376.d002906 t X Y z w)
  convert! (h.const_mul kappa).div_const 8 using 1 <;>
    (try simp only [_root_.GD.N0232.N0720.N1376.d002895, Function.comp_def]) <;> ring

theorem d002915 (kappa t X Y z w : ℝ)
    (hA : 0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002895 kappa t X Y z q)
      (-kappa * t * _root_.GD.N0232.N0720.N1377.d002852 6 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w)
        (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) / 8) w := by
  have h := (_root_.GD.N0232.N0720.N1377.d002865 4 hA (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa)).comp w
    (_root_.GD.N0232.N0720.N1376.d002907 t X Y z w)
  convert! (h.const_mul kappa).div_const 8 using 1 <;>
    (try simp only [_root_.GD.N0232.N0720.N1376.d002895, Function.comp_def]) <;> ring

theorem d002916 (kappa t X Y z w : ℝ)
    (hA : 0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002894 kappa t q Y z w)
      ((1 - t) *
        (-X * _root_.GD.N0232.N0720.N1377.d002852 7 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w) (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) +
          kappa * _root_.GD.N0232.N0720.N1377.d002852 6 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w) (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa)) / 8) X := by
  have h := _root_.GD.N0232.N0720.N1379.d002890 5
    (A := fun q : ℝ ↦ _root_.GD.N0232.N0720.N1376.d002892 t q Y z w)
    (b := fun q : ℝ ↦ _root_.GD.N0232.N0720.N1376.d002893 t q Y * kappa) (x := X) hA
    (_root_.GD.N0232.N0720.N1376.d002908 t X Y z w)
    ((_root_.GD.N0232.N0720.N1376.d002910 t X Y).mul_const kappa)
  convert! h.div_const 8 using 1 <;> (try simp only [_root_.GD.N0232.N0720.N1376.d002894]) <;> ring

theorem d002917 (kappa t X Y z w : ℝ)
    (hA : 0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w) :
    HasDerivAt (fun q ↦ _root_.GD.N0232.N0720.N1376.d002894 kappa t X q z w)
      (t *
        (-Y * _root_.GD.N0232.N0720.N1377.d002852 7 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w) (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa) +
          kappa * _root_.GD.N0232.N0720.N1377.d002852 6 (_root_.GD.N0232.N0720.N1376.d002892 t X Y z w) (_root_.GD.N0232.N0720.N1376.d002893 t X Y * kappa)) / 8) Y := by
  have h := _root_.GD.N0232.N0720.N1379.d002890 5
    (A := fun q : ℝ ↦ _root_.GD.N0232.N0720.N1376.d002892 t X q z w)
    (b := fun q : ℝ ↦ _root_.GD.N0232.N0720.N1376.d002893 t X q * kappa) (x := Y) hA
    (_root_.GD.N0232.N0720.N1376.d002909 t X Y z w)
    ((_root_.GD.N0232.N0720.N1376.d002911 t X Y).mul_const kappa)
  convert! h.div_const 8 using 1 <;> (try simp only [_root_.GD.N0232.N0720.N1376.d002894]) <;> ring



theorem d002918 (kappa t X Y z w : ℝ)
    (hA : 0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w) :
    deriv (fun q ↦ _root_.GD.N0232.N0720.N1376.d002895 kappa t X Y q w) z =
      X * deriv (fun q ↦ _root_.GD.N0232.N0720.N1376.d002894 kappa t X Y q w) z -
        deriv (fun q ↦ _root_.GD.N0232.N0720.N1376.d002894 kappa t q Y z w) X := by
  rw [(_root_.GD.N0232.N0720.N1376.d002914 kappa t X Y z w hA).deriv,
    (_root_.GD.N0232.N0720.N1376.d002912 kappa t X Y z w hA).deriv,
    (_root_.GD.N0232.N0720.N1376.d002916 kappa t X Y z w hA).deriv]
  ring


theorem d002919 (kappa t X Y z w : ℝ)
    (hA : 0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w) :
    deriv (fun q ↦ _root_.GD.N0232.N0720.N1376.d002895 kappa t X Y z q) w =
      Y * deriv (fun q ↦ _root_.GD.N0232.N0720.N1376.d002894 kappa t X Y z q) w -
        deriv (fun q ↦ _root_.GD.N0232.N0720.N1376.d002894 kappa t X q z w) Y := by
  rw [(_root_.GD.N0232.N0720.N1376.d002915 kappa t X Y z w hA).deriv,
    (_root_.GD.N0232.N0720.N1376.d002913 kappa t X Y z w hA).deriv,
    (_root_.GD.N0232.N0720.N1376.d002917 kappa t X Y z w hA).deriv]
  ring

end

end GD.N0232.N0720.N1376

#print axioms _root_.GD.N0232.N0720.N1376.d002896
#print axioms _root_.GD.N0232.N0720.N1376.d002898
#print axioms _root_.GD.N0232.N0720.N1376.d002900
#print axioms _root_.GD.N0232.N0720.N1376.d002904
#print axioms _root_.GD.N0232.N0720.N1376.d002905
#print axioms _root_.GD.N0232.N0720.N1376.d002912
#print axioms _root_.GD.N0232.N0720.N1376.d002915
#print axioms _root_.GD.N0232.N0720.N1376.d002918
#print axioms _root_.GD.N0232.N0720.N1376.d002919
