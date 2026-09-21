import GD.Module0217






























namespace GD
namespace N0232
namespace N0720
namespace N1460

noncomputable section

open _root_.GD.N0232.N0720.N1437





def d003024 (s t : ℝ) : ℝ :=
  Real.sqrt (s + t)



def d003025 (u v s t : ℝ) : ℝ :=
  (u - v) / _root_.GD.N0232.N0720.N1460.d003024 s t


def d003026 (s t : ℝ) : ℝ :=
  s / (s + t)



def d003027
    (f : ℝ → ℝ → ℝ) (u v s t : ℝ) : ℝ :=
  v + _root_.GD.N0232.N0720.N1460.d003024 s t *
    f (_root_.GD.N0232.N0720.N1460.d003025 u v s t) (_root_.GD.N0232.N0720.N1460.d003026 s t)


def d003028 (z q : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (z, 0, q, 1 - q)


def d003029
    (d : ℝ → ℝ → ℝ → ℝ → ℝ) (z q : ℝ) : ℝ :=
  d z 0 q (1 - q)




theorem d003030
    (dilation s t : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0720.N1460.d003024 (dilation ^ 2 * s) (dilation ^ 2 * t) =
      dilation * _root_.GD.N0232.N0720.N1460.d003024 s t := by
  unfold _root_.GD.N0232.N0720.N1460.d003024
  rw [← mul_add, Real.sqrt_mul (sq_nonneg dilation),
    Real.sqrt_sq_eq_abs, abs_of_pos hdilation]



theorem d003031
    (shift dilation u v s t : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0720.N1460.d003025
        (shift + dilation * u) (shift + dilation * v)
        (dilation ^ 2 * s) (dilation ^ 2 * t) =
      _root_.GD.N0232.N0720.N1460.d003025 u v s t := by
  unfold _root_.GD.N0232.N0720.N1460.d003025
  rw [_root_.GD.N0232.N0720.N1460.d003030 dilation s t hdilation]
  have hdilation0 : dilation ≠ 0 := hdilation.ne'
  field_simp
  ring


theorem d003032
    (dilation s t : ℝ) (hdilation : dilation ≠ 0) :
    _root_.GD.N0232.N0720.N1460.d003026 (dilation ^ 2 * s) (dilation ^ 2 * t) =
      _root_.GD.N0232.N0720.N1460.d003026 s t := by
  unfold _root_.GD.N0232.N0720.N1460.d003026
  rw [← mul_add]
  exact mul_div_mul_left s (s + t) (pow_ne_zero 2 hdilation)



theorem d003033
    (f : ℝ → ℝ → ℝ) :
    _root_.GD.N0232.N0720.N1437.d003000 (_root_.GD.N0232.N0720.N1460.d003027 f) := by
  intro shift dilation u v s t hdilation
  unfold _root_.GD.N0232.N0720.N1460.d003027
  rw [_root_.GD.N0232.N0720.N1460.d003030 dilation s t hdilation,
    _root_.GD.N0232.N0720.N1460.d003031 shift dilation u v s t hdilation,
    _root_.GD.N0232.N0720.N1460.d003032 dilation s t hdilation.ne']
  ring





theorem d003034
    {s t : ℝ} (hst : 0 < s + t) :
    0 < _root_.GD.N0232.N0720.N1460.d003024 s t := by
  exact Real.sqrt_pos.2 hst


theorem d003035
    {s t : ℝ} (hst : s + t ≠ 0) (hnonneg : 0 ≤ s + t) :
    _root_.GD.N0232.N0720.N1460.d003024 s t ^ 2 * _root_.GD.N0232.N0720.N1460.d003026 s t = s := by
  unfold _root_.GD.N0232.N0720.N1460.d003024 _root_.GD.N0232.N0720.N1460.d003026
  rw [Real.sq_sqrt hnonneg]
  field_simp


theorem d003036
    {s t : ℝ} (hst : s + t ≠ 0) (hnonneg : 0 ≤ s + t) :
    _root_.GD.N0232.N0720.N1460.d003024 s t ^ 2 * (1 - _root_.GD.N0232.N0720.N1460.d003026 s t) = t := by
  unfold _root_.GD.N0232.N0720.N1460.d003024 _root_.GD.N0232.N0720.N1460.d003026
  rw [Real.sq_sqrt hnonneg]
  field_simp
  ring



theorem d003037
    {u v s t : ℝ} (hscale : _root_.GD.N0232.N0720.N1460.d003024 s t ≠ 0) :
    v + _root_.GD.N0232.N0720.N1460.d003024 s t * _root_.GD.N0232.N0720.N1460.d003025 u v s t = u := by
  unfold _root_.GD.N0232.N0720.N1460.d003025
  field_simp
  ring






theorem d003038
    (d : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hd : _root_.GD.N0232.N0720.N1437.d003000 d)
    {u v s t : ℝ} (hst : 0 < s + t) :
    d u v s t =
      _root_.GD.N0232.N0720.N1460.d003027 (_root_.GD.N0232.N0720.N1460.d003029 d) u v s t := by
  let a := _root_.GD.N0232.N0720.N1460.d003024 s t
  let z := _root_.GD.N0232.N0720.N1460.d003025 u v s t
  let q := _root_.GD.N0232.N0720.N1460.d003026 s t
  have ha : 0 < a := _root_.GD.N0232.N0720.N1460.d003034 hst
  have hfirst : v + a * z = u := by
    exact _root_.GD.N0232.N0720.N1460.d003037 ha.ne'
  have hsquare : a ^ 2 * q = s := by
    exact _root_.GD.N0232.N0720.N1460.d003035 hst.ne' hst.le
  have hsecond : a ^ 2 * (1 - q) = t := by
    exact _root_.GD.N0232.N0720.N1460.d003036 hst.ne' hst.le
  have hcov := hd v a z 0 q (1 - q) ha
  simp only [mul_zero, add_zero] at hcov
  rw [hfirst, hsquare, hsecond] at hcov
  unfold _root_.GD.N0232.N0720.N1460.d003027 _root_.GD.N0232.N0720.N1460.d003029
  exact hcov




def d003039
    (d : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ u v s t, d (-u) (-v) s t = -d u v s t


def d003040 (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ z q, f (-z) q = -f z q



theorem d003041
    (d : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hd : _root_.GD.N0232.N0720.N1460.d003039 d) (z q : ℝ) :
    _root_.GD.N0232.N0720.N1460.d003029 d (-z) q =
      -_root_.GD.N0232.N0720.N1460.d003029 d z q := by
  unfold _root_.GD.N0232.N0720.N1460.d003029
  simpa only [neg_zero] using hd z 0 q (1 - q)


theorem d003042 (u v s t : ℝ) :
    _root_.GD.N0232.N0720.N1460.d003025 (-u) (-v) s t = -_root_.GD.N0232.N0720.N1460.d003025 u v s t := by
  unfold _root_.GD.N0232.N0720.N1460.d003025
  ring



theorem d003043
    (f : ℝ → ℝ → ℝ) (hf : _root_.GD.N0232.N0720.N1460.d003040 f) :
    _root_.GD.N0232.N0720.N1460.d003039 (_root_.GD.N0232.N0720.N1460.d003027 f) := by
  intro u v s t
  unfold _root_.GD.N0232.N0720.N1460.d003027
  rw [_root_.GD.N0232.N0720.N1460.d003042, hf]
  ring





@[simp] theorem d003044
    (f : ℝ → ℝ → ℝ) (u v : ℝ) :
    _root_.GD.N0232.N0720.N1460.d003027 f u v 0 0 = v := by
  simp [_root_.GD.N0232.N0720.N1460.d003027, _root_.GD.N0232.N0720.N1460.d003024]


theorem d003045 :
    _root_.GD.N0232.N0720.N1437.d003000 (fun u _v _s _t : ℝ ↦ u) := by
  intro shift dilation u v s t hdilation
  rfl




theorem d003046 :
    ∀ f : ℝ → ℝ → ℝ,
      _root_.GD.N0232.N0720.N1460.d003027 f 1 0 0 0 ≠
        (fun u _v _s _t : ℝ ↦ u) 1 0 0 0 := by
  intro f
  norm_num

end
end N1460
end N0720
end N0232
end GD
