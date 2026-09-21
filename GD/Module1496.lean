import GD.Module1280
import GD.Module0287
import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0084

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0981
open _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0156.N0444

noncomputable section

variable {k : ℕ} [NeZero k] (sizes : Fin k → ℕ)

abbrev d023414 := _root_.GD.N0232.N0719.N0859.d010811 k sizes

def d023415 (c : Fin k → ℝ) (z : _root_.GD.N0084.d023414 sizes) : _root_.GD.N0084.d023414 sizes :=
  fun i j => c i + z i j

def d023416 (z : _root_.GD.N0084.d023414 sizes) (i : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N0981.d020646 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) i

def d023417 (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (z : _root_.GD.N0084.d023414 sizes) : ℝ :=
  ∑ i, W z i * _root_.GD.N0084.d023416 sizes z i

def d023418 (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) : Prop :=
  ∀ c z, W (_root_.GD.N0084.d023415 sizes c z) = W z

omit [NeZero k] in
theorem d023419 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ ≪ (volume : Measure (_root_.GD.N0084.d023414 sizes)) := by
  rw [_root_.GD.N0156.N0444.d020668 sizes θ]
  apply _root_.GD.N0235.d004256
  intro i
  apply _root_.GD.N0235.d004256
  intro j
  exact gaussianReal_absolutelyContinuous θ.location
    (_root_.GD.N0232.N0719.N0932.d009196 (θ.scale_pos i).ne')

omit [NeZero k] in
theorem d023420 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (volume : Measure (_root_.GD.N0084.d023414 sizes)) ≪ _root_.GD.N0232.N0719.N0859.d010812 k sizes θ := by
  rw [_root_.GD.N0156.N0444.d020668 sizes θ]
  apply _root_.GD.N0235.d004256
  intro i
  apply _root_.GD.N0235.d004256
  intro j
  exact gaussianReal_absolutelyContinuous' θ.location
    (_root_.GD.N0232.N0719.N0932.d009196 (θ.scale_pos i).ne')

omit [NeZero k] in
theorem d023421 (c : Fin k → ℝ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Measure.QuasiMeasurePreserving (_root_.GD.N0084.d023415 sizes c) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  exact (measurePreserving_add_left (volume : Measure (_root_.GD.N0084.d023414 sizes))
    (fun i _ => c i)).quasiMeasurePreserving.mono
      (_root_.GD.N0084.d023419 sizes θ)
      (_root_.GD.N0084.d023420 sizes θ)

omit [NeZero k] in
theorem d023422 (hn : ∀ i, 0 < sizes i)
    (c : Fin k → ℝ) (z : _root_.GD.N0084.d023414 sizes) (i : Fin k) :
    _root_.GD.N0084.d023416 sizes (_root_.GD.N0084.d023415 sizes c z) i = c i + _root_.GD.N0084.d023416 sizes z i := by
  have hi : (sizes i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hn i).ne'
  change (∑ j, (c i + z i j)) / (sizes i : ℝ) =
    c i + (∑ j, z i j) / (sizes i : ℝ)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, add_div]
  field_simp

omit [NeZero k] in
theorem d023423 (hn : ∀ i, 0 < sizes i)
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hW : _root_.GD.N0084.d023418 sizes W)
    (c : Fin k → ℝ) (z : _root_.GD.N0084.d023414 sizes) :
    _root_.GD.N0084.d023417 sizes W (_root_.GD.N0084.d023415 sizes c z) =
      _root_.GD.N0084.d023417 sizes W z + ∑ i, W z i * c i := by
  simp only [_root_.GD.N0084.d023417, hW c z, _root_.GD.N0084.d023422 sizes hn, mul_add,
    Finset.sum_add_distrib]
  ring

omit [NeZero k] in
theorem d023424 (hn : ∀ i, 0 < sizes i)
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hW : _root_.GD.N0084.d023418 sizes W)
    (hunit : ∀ z, ∑ i, W z i = 1) (c : ℝ) (z : _root_.GD.N0084.d023414 sizes) :
    _root_.GD.N0084.d023417 sizes W (fun i j => c + z i j) = c + _root_.GD.N0084.d023417 sizes W z := by
  rw [show (fun i j => c + z i j) = _root_.GD.N0084.d023415 sizes (fun _ => c) z from rfl,
    _root_.GD.N0084.d023423 sizes hn W hW, ← Finset.sum_mul, hunit, one_mul]
  ring

theorem d023425 (hn : ∀ i, 0 < sizes i)
    (c : Fin k → ℝ) (hc : ∀ i, 0 ≤ c i) (z : _root_.GD.N0084.d023414 sizes) :
    _root_.GD.N0232.N0719.N0981.d020647 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) ≤
      _root_.GD.N0232.N0719.N0981.d020647 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm (_root_.GD.N0084.d023415 sizes c z)) := by
  apply Finset.le_inf'
  intro i _
  change _root_.GD.N0232.N0719.N0981.d020647 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) ≤ _root_.GD.N0084.d023416 sizes (_root_.GD.N0084.d023415 sizes c z) i
  rw [_root_.GD.N0084.d023422 sizes hn]
  exact (_root_.GD.N0232.N0719.N0981.d020652 sizes _ i).trans (le_add_of_nonneg_left (hc i))




theorem d023426 (hn : ∀ i, 0 < sizes i)
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hW : _root_.GD.N0084.d023418 sizes W)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hinterval : ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, _root_.GD.N0156.N0444.d020667 sizes (_root_.GD.N0084.d023417 sizes W) z) :
    ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, ∀ i, 0 ≤ W z i := by
  have hshift (i : Fin k) (n : ℕ) : ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ,
      _root_.GD.N0156.N0444.d020667 sizes (_root_.GD.N0084.d023417 sizes W)
        (_root_.GD.N0084.d023415 sizes (fun j => if j = i then (n : ℝ) else 0) z) :=
    (_root_.GD.N0084.d023421 sizes _ θ).ae hinterval
  have hall := (ae_all_iff.mpr fun i => ae_all_iff.mpr (hshift i))
  filter_upwards [hall] with z hz
  intro i
  by_contra hneg
  have hneg' : W z i < 0 := lt_of_not_ge hneg
  obtain ⟨n, hnlarge⟩ := exists_nat_gt
    ((_root_.GD.N0084.d023417 sizes W z - _root_.GD.N0232.N0719.N0981.d020647 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z)) / (-W z i))
  have hmul := (div_lt_iff₀ (neg_pos.mpr hneg')).mp hnlarge
  have hbound := (_root_.GD.N0084.d023425 sizes hn
    (fun j => if j = i then (n : ℝ) else 0)
    (fun j => by split <;> positivity) z).trans (hz i n).1
  rw [_root_.GD.N0084.d023423 sizes hn W hW] at hbound
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hbound
  nlinarith



theorem d023427 (hn : ∀ i, 0 < sizes i)
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hW : _root_.GD.N0084.d023418 sizes W)
    (hunit : ∀ z, ∑ i, W z i = 1)
    (hf : _root_.GD.N0084.d023417 sizes W ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes (_root_.GD.N0084.d023417 sizes W)) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, ∀ i, 0 ≤ W z i := by
  apply _root_.GD.N0084.d023426 sizes hn W hW θ
  exact _root_.GD.N0156.N0444.d020673 sizes hn (_root_.GD.N0084.d023417 sizes W) hf
    (_root_.GD.N0084.d023424 sizes hn W hW hunit) ht θ

end
end GD.N0084

#print axioms _root_.GD.N0084.d023421
#print axioms _root_.GD.N0084.d023424
#print axioms _root_.GD.N0084.d023426
#print axioms _root_.GD.N0084.d023427
