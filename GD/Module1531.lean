import GD.Module1530

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0051
noncomputable section

def d023838 : _root_.GD.N0051.d023832 ≃ᵐ _root_.GD.N0051.d023832 :=
  MeasurableEquiv.prodCongr MeasurableEquiv.prodComm MeasurableEquiv.prodComm

theorem d023839 (a b : ℝ) :
    MeasurePreserving _root_.GD.N0051.d023838 (_root_.GD.N0051.d023833 a b) (_root_.GD.N0051.d023833 b a) := by
  exact MeasurePreserving.prod Measure.measurePreserving_swap Measure.measurePreserving_swap

theorem d023840 {a b m v w r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (hw : 0 < w) (hwv : w ≤ v)
    (hr : 0 ≤ r) (hra : r < a)
    (f : _root_.GD.N0051.d023832 → ℝ) (hf : Measurable f)
    (hsecond : ∀ y z s t, 0 < s → 0 < t →
      (f ((y, z), (s, t)) - z) ^ 2 ≤ t * (1 + (z - y) ^ 2 / s) ^ r) :
    Integrable (fun u => (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2) (_root_.GD.N0051.d023833 a b) ∧
    (∫ u, (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2 ∂_root_.GD.N0051.d023833 a b) ≤
      w * _root_.GD.N0051.d023835 a r := by
  have hh := _root_.GD.N0051.d023837 (m := m) hb ha hw hv hwv hr hra
    (f ∘ _root_.GD.N0051.d023838) (hf.comp _root_.GD.N0051.d023838.measurable) (fun y z s t hs ht => by
      change (f ((z, y), (t, s)) - y) ^ 2 ≤ s * (1 + (z - y) ^ 2 / t) ^ r
      simpa only [sub_sq_comm] using hsecond z y t s ht hs)
  have hmp := _root_.GD.N0051.d023839 a b
  have hi := hmp.integrable_comp_of_integrable hh.1
  have heq := hmp.integral_comp' (fun u =>
    ((f ∘ _root_.GD.N0051.d023838) (_root_.GD.N0051.d023834 m w v u) - m) ^ 2)
  exact ⟨hi, heq.trans_le hh.2⟩

def d023841 (p q : ℝ) (u : _root_.GD.N0051.d023832) : ℝ :=
  _root_.GD.N0051.d022763 p q u.1.1 u.1.2 u.2.1 u.2.2

def d023842 (a b p q : ℝ) : ℝ := max (_root_.GD.N0051.d023835 b (q / p)) (_root_.GD.N0051.d023835 a (p / q))

theorem d023843 {a b p q : ℝ} (_ha : 0 < a) (hb : 0 < b)
    (_hqa : p / q < a) (hpb : q / p < b) : 0 < _root_.GD.N0051.d023842 a b p q := by
  unfold _root_.GD.N0051.d023842
  exact (_root_.GD.N0051.d023836 hb hpb).trans_le (le_max_left _ _)



theorem d023844 {a b p q m v w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q)
    (hqa : p / q < a) (hpb : q / p < b) (hv : 0 < v) (hw : 0 < w) :
    Integrable (fun u => (_root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 m v w u) - m) ^ 2)
      (_root_.GD.N0051.d023833 a b) ∧
    (∫ u, (_root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 m v w u) - m) ^ 2 ∂_root_.GD.N0051.d023833 a b) ≤
      _root_.GD.N0051.d023842 a b p q * min v w := by
  have hf : Measurable (_root_.GD.N0051.d023841 p q) := _root_.GD.N0051.d022771 p q
  rcases le_total v w with h | h
  · have hh := _root_.GD.N0051.d023837 (m := m) ha hb hv hw h (div_pos hq hp).le hpb
      (_root_.GD.N0051.d023841 p q) hf (fun _ _ _ _ hs ht => _root_.GD.N0051.d022769 hp hs ht)
    refine ⟨hh.1, hh.2.trans ?_⟩
    rw [min_eq_left h, mul_comm (_root_.GD.N0051.d023842 _ _ _ _) v]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hv.le
  · have hh := _root_.GD.N0051.d023840 (m := m) ha hb hv hw h (div_pos hp hq).le hqa
      (_root_.GD.N0051.d023841 p q) hf (fun _ _ _ _ hs ht => _root_.GD.N0051.d022770 hq hs ht)
    refine ⟨hh.1, hh.2.trans ?_⟩
    rw [min_eq_right h, mul_comm (_root_.GD.N0051.d023842 _ _ _ _) w]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hw.le

theorem d023845 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : 1 < a * b) :
    ∃ p q C : ℝ, 0 < p ∧ 0 < q ∧ 0 < C ∧
      ∀ m v w, 0 < v → 0 < w →
        (∫ u, (_root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 m v w u) - m) ^ 2 ∂_root_.GD.N0051.d023833 a b) ≤
          C * min v w := by
  obtain ⟨r, hr, hrb, hra⟩ := (_root_.GD.N0051.d022772 ha).mpr hab
  have hpr : (1 : ℝ) / r < a := hra
  have hqr : r / 1 < b := by simpa using hrb
  refine ⟨1, r, _root_.GD.N0051.d023842 a b 1 r, by norm_num, hr, _root_.GD.N0051.d023843 ha hb hpr hqr, ?_⟩
  intro m v w hv hw
  exact (_root_.GD.N0051.d023844 ha hb (by norm_num) hr hpr hqr hv hw).2

#print axioms _root_.GD.N0051.d023840
#print axioms _root_.GD.N0051.d023844
#print axioms _root_.GD.N0051.d023845
end
end GD.N0051
