import GD.Module1532
import GD.Module1536

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0031
noncomputable section

open _root_.GD.N0051 _root_.GD.N0087

def d023868 (b r : ℝ) : ℝ :=
  4 + 2 * _root_.GD.N0031.d023846 b r * _root_.GD.N0051.d022794 b

theorem d023869 {b r : ℝ} (hb : 0 < b) (hr : 0 < r) :
    0 < _root_.GD.N0031.d023868 b r := by
  have hK := _root_.GD.N0031.d023847 hb hr
  have hG := _root_.GD.N0051.d022798 b
  unfold _root_.GD.N0031.d023868
  positivity

theorem d023870 {a b p q m v w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q)
    (hcrit : (p / q) * b = 1) (hv : 0 < v) (hw : 0 < w) (hvw : v ≤ w)
    (f : _root_.GD.N0051.d023832 → ℝ) (hf : Measurable f)
    (hfirst : ∀ y z s t : ℝ, 0 < s → 0 < t →
      (f ((y, z), (s, t)) - y) ^ 2 ≤ s + (z - y) ^ 2 *
        (Iic (_root_.GD.N0031.d022775 (p / q) s (z - y))).indicator (fun _ => (1 : ℝ)) t) :
    Integrable (fun u => (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2) (_root_.GD.N0051.d023833 a b) ∧
      (∫ u, (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2 ∂_root_.GD.N0051.d023833 a b) ≤
        v * _root_.GD.N0031.d023868 b (p / q) := by
  exact _root_.GD.N0087.d023866 ha hb hv hw hvw
    (_root_.GD.N0031.d023847 hb (div_pos hp hq)).le hb.le f hf
    (fun _ _ => _root_.GD.N0031.d023849 hp hq ha hb hv hw hcrit f hf hfirst)

theorem d023871 {a b p q m v w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q)
    (hcrit : (q / p) * a = 1) (hv : 0 < v) (hw : 0 < w) (hwv : w ≤ v)
    (f : _root_.GD.N0051.d023832 → ℝ) (hf : Measurable f)
    (hsecond : ∀ y z s t : ℝ, 0 < s → 0 < t →
      (f ((y, z), (s, t)) - z) ^ 2 ≤ t + (y - z) ^ 2 *
        (Iic (_root_.GD.N0031.d022775 (q / p) t (y - z))).indicator (fun _ => (1 : ℝ)) s) :
    Integrable (fun u => (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2) (_root_.GD.N0051.d023833 a b) ∧
      (∫ u, (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2 ∂_root_.GD.N0051.d023833 a b) ≤
        w * _root_.GD.N0031.d023868 a (q / p) := by
  have hh := _root_.GD.N0031.d023870 (m := m) hb ha hq hp hcrit hw hv hwv
    (f ∘ _root_.GD.N0051.d023838) (hf.comp _root_.GD.N0051.d023838.measurable)
    (fun y z s t hs ht => hsecond z y t s ht hs)
  have hmp := _root_.GD.N0051.d023839 a b
  have hi := hmp.integrable_comp_of_integrable hh.1
  have heq := hmp.integral_comp' (fun u =>
    ((f ∘ _root_.GD.N0051.d023838) (_root_.GD.N0051.d023834 m w v u) - m) ^ 2)
  exact ⟨hi, heq.trans_le hh.2⟩

def d023872 (a b p q : ℝ) : ℝ :=
  max (_root_.GD.N0031.d023868 b (p / q)) (_root_.GD.N0031.d023868 a (q / p))

theorem d023873 {a b p q : ℝ} (hb : 0 < b) (hp : 0 < p) (hq : 0 < q) :
    0 < _root_.GD.N0031.d023872 a b p q :=
  (_root_.GD.N0031.d023869 hb (div_pos hp hq)).trans_le (le_max_left _ _)



theorem d023874 {a b p q m v w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q)
    (hcrit₁ : (p / q) * b = 1) (hcrit₂ : (q / p) * a = 1)
    (hv : 0 < v) (hw : 0 < w) :
    Integrable (fun u => (_root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 m v w u) - m) ^ 2)
      (_root_.GD.N0051.d023833 a b) ∧
    (∫ u, (_root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 m v w u) - m) ^ 2 ∂_root_.GD.N0051.d023833 a b) ≤
      _root_.GD.N0031.d023872 a b p q * min v w := by
  have hf : Measurable (_root_.GD.N0051.d023841 p q) := _root_.GD.N0051.d022771 p q
  rcases le_total v w with h | h
  · have hh := _root_.GD.N0031.d023870 (m := m) ha hb hp hq hcrit₁ hv hw h
      (_root_.GD.N0051.d023841 p q) hf (fun _ _ _ _ hs ht => _root_.GD.N0031.d022779 hp hq hs ht)
    refine ⟨hh.1, hh.2.trans ?_⟩
    rw [min_eq_left h, mul_comm (_root_.GD.N0031.d023872 _ _ _ _) v]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hv.le
  · have hh := _root_.GD.N0031.d023871 (m := m) ha hb hp hq hcrit₂ hv hw h
      (_root_.GD.N0051.d023841 p q) hf (fun _ _ _ _ hs ht => _root_.GD.N0031.d022790 hp hq hs ht)
    refine ⟨hh.1, hh.2.trans ?_⟩
    rw [min_eq_right h, mul_comm (_root_.GD.N0031.d023872 _ _ _ _) w]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hw.le

theorem d023875 {a b m v w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) (hv : 0 < v) (hw : 0 < w) :
    Integrable (fun u => (_root_.GD.N0051.d023841 a 1 (_root_.GD.N0051.d023834 m v w u) - m) ^ 2)
      (_root_.GD.N0051.d023833 a b) ∧
    (∫ u, (_root_.GD.N0051.d023841 a 1 (_root_.GD.N0051.d023834 m v w u) - m) ^ 2 ∂_root_.GD.N0051.d023833 a b) ≤
      _root_.GD.N0031.d023872 a b a 1 * min v w := by
  apply _root_.GD.N0031.d023874 ha hb ha (by norm_num)
    (by simpa only [div_one] using hab) ?_ hv hw
  exact one_div_mul_cancel ha.ne'



theorem d023876 {m v w : ℝ}
    (hv : 0 < v) (hw : 0 < w) :
    Integrable (fun u => (_root_.GD.N0051.d023841 1 2 (_root_.GD.N0051.d023834 m v w u) - m) ^ 2)
      (_root_.GD.N0051.d023833 (1 / 2) 2) ∧
    (∫ u, (_root_.GD.N0051.d023841 1 2 (_root_.GD.N0051.d023834 m v w u) - m) ^ 2
      ∂_root_.GD.N0051.d023833 (1 / 2) 2) ≤ _root_.GD.N0031.d023872 (1 / 2) 2 1 2 * min v w := by
  exact _root_.GD.N0031.d023874 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv hw

end
end GD.N0031

#print axioms _root_.GD.N0031.d023870
#print axioms _root_.GD.N0031.d023871
#print axioms _root_.GD.N0031.d023873
#print axioms _root_.GD.N0031.d023874
#print axioms _root_.GD.N0031.d023875
#print axioms _root_.GD.N0031.d023876
