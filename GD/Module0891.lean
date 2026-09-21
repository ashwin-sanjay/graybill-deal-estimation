import GD.Module0890
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure










open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0720.N1307

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1312 _root_.GD.N0232.N0720.N1337
open _root_.GD.N0232.N0720.N1266 (d013712 d013726)

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
variable {I : Type*} [Fintype I]

def d013837 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) :=
  ∑ i, w i • _root_.GD.N0232.N0720.N1312.d013800 m n hm hn (q i)

def d013838 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) :=
  ∑ i, (w i * _root_.GD.N0232.N0720.N1441.d013680 (q i)) • _root_.GD.N0232.N0720.N1312.d013800 m n hm hn (q i)

theorem d013839 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1266.d013712) :
    _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w u = ∑ i, w i * _root_.GD.N0232.N0720.N1312.d013797 m n (q i) u := by
  simp [_root_.GD.N0232.N0720.N1307.d013837, _root_.GD.N0232.N0720.N1312.d013800, smul_eq_mul]

theorem d013840 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1266.d013712) :
    _root_.GD.N0232.N0720.N1307.d013838 m n hm hn q w u = ∑ i, w i * _root_.GD.N0232.N0720.N1312.d013797 m n (q i) u * _root_.GD.N0232.N0720.N1441.d013680 (q i) := by
  simp [_root_.GD.N0232.N0720.N1307.d013838, _root_.GD.N0232.N0720.N1312.d013800, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

theorem d013841 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (u : _root_.GD.N0232.N0720.N1266.d013712) :
    0 < _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w u := by
  rw [_root_.GD.N0232.N0720.N1307.d013839 m n hm hn]
  obtain ⟨j, hj⟩ := hpositive
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hw i) (_root_.GD.N0232.N0720.N1312.d013798 m n hm hn (q i) u).le
  · exact ⟨j, Finset.mem_univ j, mul_pos hj (_root_.GD.N0232.N0720.N1312.d013798 m n hm hn (q j) u)⟩

def d013842 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) where
  toFun u := _root_.GD.N0232.N0720.N1307.d013838 m n hm hn q w u / _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w u
  continuous_toFun := (_root_.GD.N0232.N0720.N1307.d013838 m n hm hn q w).continuous.div (_root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w).continuous
    (fun u ↦ (_root_.GD.N0232.N0720.N1307.d013841 m n hm hn q w hw hpositive u).ne')

def d013843 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) : _root_.GD.N0232.N0720.N1441.d013681 m n :=
  _root_.GD.N0232.N0720.N1337.d013813 m n hm hn 2 (_root_.GD.N0232.N0720.N1307.d013842 m n hm hn q w hw hpositive)

theorem d013844 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) :
    _root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦
      _root_.GD.N0232.N0720.N1307.d013838 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) / _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) :=
  _root_.GD.N0232.N0720.N1337.d013814 m n hm hn 2 (_root_.GD.N0232.N0720.N1307.d013842 m n hm hn q w hw hpositive)

def d013845 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) : ℝ :=
  ∑ i, w i * _root_.GD.N0232.N0720.N1337.d013826 m n hm hn (q i) h

def d013846 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1441.d013681 m n) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  ∑ i, w i * (_root_.GD.N0232.N0720.N1312.d013797 m n (q i) (_root_.GD.N0232.N0720.N1266.d013726 x) * (h x - _root_.GD.N0232.N0720.N1441.d013680 (q i)) ^ 2)

include hm hn in
theorem d013847 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1441.d013681 m n) : Integrable (_root_.GD.N0232.N0720.N1307.d013846 m n q w h) (_root_.GD.N0232.N0720.N1441.d013679 m n) := by
  exact integrable_finsetSum _ (fun i _ ↦ (_root_.GD.N0232.N0720.N1337.d013830 m n hm hn (q i) h).const_mul (w i))

theorem d013848 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1307.d013845 m n hm hn q w h = ∫ x, _root_.GD.N0232.N0720.N1307.d013846 m n q w h x ∂_root_.GD.N0232.N0720.N1441.d013679 m n := by
  unfold _root_.GD.N0232.N0720.N1307.d013845 _root_.GD.N0232.N0720.N1307.d013846
  rw [integral_finsetSum]
  · simp only [integral_const_mul, ← _root_.GD.N0232.N0720.N1337.d013829 m n hm hn]
  · intro i _
    exact (_root_.GD.N0232.N0720.N1337.d013830 m n hm hn (q i) h).const_mul (w i)

private theorem d013849 (a b : I → ℝ) (z : ℝ)
    (ha : (∑ i, a i) ≠ 0) :
    (∑ i, a i * (z - b i) ^ 2) -
        (∑ i, a i * ((∑ j, a j * b j) / (∑ j, a j) - b i) ^ 2) =
      (∑ i, a i) * (z - (∑ j, a j * b j) / (∑ j, a j)) ^ 2 := by
  have hexpand (v : ℝ) : (∑ i, a i * (v - b i) ^ 2) =
      (∑ i, a i) * v ^ 2 - (∑ i, a i * b i) * (2 * v) + ∑ i, a i * b i ^ 2 := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexpand, hexpand]
  field_simp [ha]
  ring

theorem d013850 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1307.d013845 m n hm hn q w h - _root_.GD.N0232.N0720.N1307.d013845 m n hm hn q w (_root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive) =
      ∫ x, _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) *
        (h x - _root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive x) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013679 m n := by
  rw [_root_.GD.N0232.N0720.N1307.d013848 m n hm hn, _root_.GD.N0232.N0720.N1307.d013848 m n hm hn,
    ← integral_sub (_root_.GD.N0232.N0720.N1307.d013847 m n hm hn q w h)
      (_root_.GD.N0232.N0720.N1307.d013847 m n hm hn q w (_root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive))]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1307.d013844 m n hm hn q w hw hpositive] with x hx
  simp only [_root_.GD.N0232.N0720.N1307.d013846, hx, _root_.GD.N0232.N0720.N1307.d013839 m n hm hn, _root_.GD.N0232.N0720.N1307.d013840 m n hm hn, ← mul_assoc]
  exact _root_.GD.N0232.N0720.N1307.d013849
    (fun i ↦ w i * _root_.GD.N0232.N0720.N1312.d013797 m n (q i) (_root_.GD.N0232.N0720.N1266.d013726 x))
    (fun i ↦ _root_.GD.N0232.N0720.N1441.d013680 (q i)) (h x)
    (by simpa only [_root_.GD.N0232.N0720.N1307.d013839 m n hm hn] using (_root_.GD.N0232.N0720.N1307.d013841 m n hm hn q w hw hpositive (_root_.GD.N0232.N0720.N1266.d013726 x)).ne')

theorem d013851 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    Integrable (fun x ↦ _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) *
      (h x - _root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive x) ^ 2) (_root_.GD.N0232.N0720.N1441.d013679 m n) := by
  apply ((_root_.GD.N0232.N0720.N1307.d013847 m n hm hn q w h).sub'
    (_root_.GD.N0232.N0720.N1307.d013847 m n hm hn q w (_root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive))).congr
  filter_upwards [_root_.GD.N0232.N0720.N1307.d013844 m n hm hn q w hw hpositive] with x hx
  simp only [_root_.GD.N0232.N0720.N1307.d013846, hx, _root_.GD.N0232.N0720.N1307.d013839 m n hm hn, _root_.GD.N0232.N0720.N1307.d013840 m n hm hn, ← mul_assoc]
  exact _root_.GD.N0232.N0720.N1307.d013849
    (fun i ↦ w i * _root_.GD.N0232.N0720.N1312.d013797 m n (q i) (_root_.GD.N0232.N0720.N1266.d013726 x))
    (fun i ↦ _root_.GD.N0232.N0720.N1441.d013680 (q i)) (h x)
    (by simpa only [_root_.GD.N0232.N0720.N1307.d013839 m n hm hn] using (_root_.GD.N0232.N0720.N1307.d013841 m n hm hn q w hw hpositive (_root_.GD.N0232.N0720.N1266.d013726 x)).ne')



theorem d013852 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (h : _root_.GD.N0232.N0720.N1441.d013681 m n)
    (hmin : ∀ k, _root_.GD.N0232.N0720.N1307.d013845 m n hm hn q w h ≤ _root_.GD.N0232.N0720.N1307.d013845 m n hm hn q w k) :
    h = _root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive := by
  have hc := _root_.GD.N0232.N0720.N1307.d013850 m n hm hn q w hw hpositive h
  have hminimal := hmin (_root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive)
  have hnonneg : ∀ x, 0 ≤ _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) *
      (h x - _root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive x) ^ 2 :=
    fun x ↦ mul_nonneg (_root_.GD.N0232.N0720.N1307.d013841 m n hm hn q w hw hpositive (_root_.GD.N0232.N0720.N1266.d013726 x)).le (sq_nonneg _)
  have hz : (∫ x, _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) *
      (h x - _root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive x) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013679 m n) = 0 := by
    have hi := MeasureTheory.integral_nonneg
      (μ := _root_.GD.N0232.N0720.N1441.d013679 m n)
      (f := fun x ↦ _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) *
        (h x - _root_.GD.N0232.N0720.N1307.d013843 m n hm hn q w hw hpositive x) ^ 2) hnonneg
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg
    (_root_.GD.N0232.N0720.N1307.d013851 m n hm hn q w hw hpositive h)).mp hz
  apply Lp.ext
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hx).resolve_left
    (_root_.GD.N0232.N0720.N1307.d013841 m n hm hn q w hw hpositive (_root_.GD.N0232.N0720.N1266.d013726 x)).ne'))

end
end GD.N0232.N0720.N1307

#print axioms _root_.GD.N0232.N0720.N1307.d013850
#print axioms _root_.GD.N0232.N0720.N1307.d013852
