import GD.Module0886
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure










open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0720.N1268

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1266 _root_.GD.N0232.N0720.N1272

variable {I : Type*} [Fintype I]

def d013764 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) :=
  ∑ i, w i • _root_.GD.N0232.N0720.N1266.d013721 (q i)

def d013765 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) :=
  ∑ i, (w i * _root_.GD.N0232.N0720.N1441.d013680 (q i)) • _root_.GD.N0232.N0720.N1266.d013721 (q i)

theorem d013766 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1266.d013712) :
    _root_.GD.N0232.N0720.N1268.d013764 q w u = ∑ i, w i * _root_.GD.N0232.N0720.N1266.d013718 (q i) u := by
  simp [_root_.GD.N0232.N0720.N1268.d013764, _root_.GD.N0232.N0720.N1266.d013721, smul_eq_mul]

theorem d013767 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1266.d013712) :
    _root_.GD.N0232.N0720.N1268.d013765 q w u = ∑ i, w i * _root_.GD.N0232.N0720.N1266.d013718 (q i) u * _root_.GD.N0232.N0720.N1441.d013680 (q i) := by
  simp [_root_.GD.N0232.N0720.N1268.d013765, _root_.GD.N0232.N0720.N1266.d013721, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

theorem d013768 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (u : _root_.GD.N0232.N0720.N1266.d013712) :
    0 < _root_.GD.N0232.N0720.N1268.d013764 q w u := by
  rw [_root_.GD.N0232.N0720.N1268.d013766]
  obtain ⟨j, hj⟩ := hpositive
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hw i) (_root_.GD.N0232.N0720.N1266.d013719 (q i) u).le
  · exact ⟨j, Finset.mem_univ j, mul_pos hj (_root_.GD.N0232.N0720.N1266.d013719 (q j) u)⟩

def d013769 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) where
  toFun u := _root_.GD.N0232.N0720.N1268.d013765 q w u / _root_.GD.N0232.N0720.N1268.d013764 q w u
  continuous_toFun := (_root_.GD.N0232.N0720.N1268.d013765 q w).continuous.div (_root_.GD.N0232.N0720.N1268.d013764 q w).continuous
    (fun u ↦ (_root_.GD.N0232.N0720.N1268.d013768 q w hw hpositive u).ne')

def d013770 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) : _root_.GD.N0232.N0720.N1441.d013681 2 2 :=
  _root_.GD.N0232.N0720.N1272.d013739 2 (_root_.GD.N0232.N0720.N1268.d013769 q w hw hpositive)

theorem d013771 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) :
    _root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] fun x ↦
      _root_.GD.N0232.N0720.N1268.d013765 q w (_root_.GD.N0232.N0720.N1266.d013726 x) / _root_.GD.N0232.N0720.N1268.d013764 q w (_root_.GD.N0232.N0720.N1266.d013726 x) :=
  _root_.GD.N0232.N0720.N1272.d013740 2 (_root_.GD.N0232.N0720.N1268.d013769 q w hw hpositive)

def d013772 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) : ℝ :=
  ∑ i, w i * _root_.GD.N0232.N0720.N1272.d013752 (q i) h

def d013773 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  ∑ i, w i * (_root_.GD.N0232.N0720.N1266.d013718 (q i) (_root_.GD.N0232.N0720.N1266.d013726 x) * (h x - _root_.GD.N0232.N0720.N1441.d013680 (q i)) ^ 2)

theorem d013774 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) : Integrable (_root_.GD.N0232.N0720.N1268.d013773 q w h) (_root_.GD.N0232.N0720.N1441.d013679 2 2) := by
  exact integrable_finsetSum _ (fun i _ ↦ (_root_.GD.N0232.N0720.N1272.d013756 (q i) h).const_mul (w i))

theorem d013775 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    _root_.GD.N0232.N0720.N1268.d013772 q w h = ∫ x, _root_.GD.N0232.N0720.N1268.d013773 q w h x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2 := by
  unfold _root_.GD.N0232.N0720.N1268.d013772 _root_.GD.N0232.N0720.N1268.d013773
  rw [integral_finsetSum]
  · simp only [integral_const_mul, ← _root_.GD.N0232.N0720.N1272.d013755]
  · intro i _
    exact (_root_.GD.N0232.N0720.N1272.d013756 (q i) h).const_mul (w i)

private theorem d013776 (a b : I → ℝ) (z : ℝ)
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

theorem d013777 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    _root_.GD.N0232.N0720.N1268.d013772 q w h - _root_.GD.N0232.N0720.N1268.d013772 q w (_root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive) =
      ∫ x, _root_.GD.N0232.N0720.N1268.d013764 q w (_root_.GD.N0232.N0720.N1266.d013726 x) *
        (h x - _root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive x) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013679 2 2 := by
  rw [_root_.GD.N0232.N0720.N1268.d013775, _root_.GD.N0232.N0720.N1268.d013775,
    ← integral_sub (_root_.GD.N0232.N0720.N1268.d013774 q w h)
      (_root_.GD.N0232.N0720.N1268.d013774 q w (_root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive))]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1268.d013771 q w hw hpositive] with x hx
  simp only [_root_.GD.N0232.N0720.N1268.d013773, hx, _root_.GD.N0232.N0720.N1268.d013766, _root_.GD.N0232.N0720.N1268.d013767, ← mul_assoc]
  exact _root_.GD.N0232.N0720.N1268.d013776
    (fun i ↦ w i * _root_.GD.N0232.N0720.N1266.d013718 (q i) (_root_.GD.N0232.N0720.N1266.d013726 x))
    (fun i ↦ _root_.GD.N0232.N0720.N1441.d013680 (q i)) (h x)
    (by simpa only [_root_.GD.N0232.N0720.N1268.d013766] using (_root_.GD.N0232.N0720.N1268.d013768 q w hw hpositive (_root_.GD.N0232.N0720.N1266.d013726 x)).ne')

theorem d013778 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    Integrable (fun x ↦ _root_.GD.N0232.N0720.N1268.d013764 q w (_root_.GD.N0232.N0720.N1266.d013726 x) *
      (h x - _root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive x) ^ 2) (_root_.GD.N0232.N0720.N1441.d013679 2 2) := by
  apply ((_root_.GD.N0232.N0720.N1268.d013774 q w h).sub'
    (_root_.GD.N0232.N0720.N1268.d013774 q w (_root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive))).congr
  filter_upwards [_root_.GD.N0232.N0720.N1268.d013771 q w hw hpositive] with x hx
  simp only [_root_.GD.N0232.N0720.N1268.d013773, hx, _root_.GD.N0232.N0720.N1268.d013766, _root_.GD.N0232.N0720.N1268.d013767, ← mul_assoc]
  exact _root_.GD.N0232.N0720.N1268.d013776
    (fun i ↦ w i * _root_.GD.N0232.N0720.N1266.d013718 (q i) (_root_.GD.N0232.N0720.N1266.d013726 x))
    (fun i ↦ _root_.GD.N0232.N0720.N1441.d013680 (q i)) (h x)
    (by simpa only [_root_.GD.N0232.N0720.N1268.d013766] using (_root_.GD.N0232.N0720.N1268.d013768 q w hw hpositive (_root_.GD.N0232.N0720.N1266.d013726 x)).ne')



theorem d013779 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2)
    (hmin : ∀ k, _root_.GD.N0232.N0720.N1268.d013772 q w h ≤ _root_.GD.N0232.N0720.N1268.d013772 q w k) :
    h = _root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive := by
  have hc := _root_.GD.N0232.N0720.N1268.d013777 q w hw hpositive h
  have hm := hmin (_root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive)
  have hn : ∀ x, 0 ≤ _root_.GD.N0232.N0720.N1268.d013764 q w (_root_.GD.N0232.N0720.N1266.d013726 x) *
      (h x - _root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive x) ^ 2 :=
    fun x ↦ mul_nonneg (_root_.GD.N0232.N0720.N1268.d013768 q w hw hpositive (_root_.GD.N0232.N0720.N1266.d013726 x)).le (sq_nonneg _)
  have hz : (∫ x, _root_.GD.N0232.N0720.N1268.d013764 q w (_root_.GD.N0232.N0720.N1266.d013726 x) *
      (h x - _root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive x) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013679 2 2) = 0 := by
    have hi := MeasureTheory.integral_nonneg
      (μ := _root_.GD.N0232.N0720.N1441.d013679 2 2)
      (f := fun x ↦ _root_.GD.N0232.N0720.N1268.d013764 q w (_root_.GD.N0232.N0720.N1266.d013726 x) *
        (h x - _root_.GD.N0232.N0720.N1268.d013770 q w hw hpositive x) ^ 2) hn
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hn
    (_root_.GD.N0232.N0720.N1268.d013778 q w hw hpositive h)).mp hz
  apply Lp.ext
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hx).resolve_left
    (_root_.GD.N0232.N0720.N1268.d013768 q w hw hpositive (_root_.GD.N0232.N0720.N1266.d013726 x)).ne'))

end
end GD.N0232.N0720.N1268

#print axioms _root_.GD.N0232.N0720.N1268.d013777
#print axioms _root_.GD.N0232.N0720.N1268.d013779
