import GD.Module0912

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal BigOperators

namespace GD.N0096.N0341

noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0137 _root_.GD.N0107

def d021954 (k : ℕ) (x : Fin k → ℝ) : ℝ := (∑ i, x i) / k

def d021955 (k : ℕ) (x : Fin k → ℝ) : ℝ :=
  (∑ i, (x i - _root_.GD.N0096.N0341.d021954 k x) ^ 2) / ((k : ℝ) * (k - 1 : ℕ))

def d021956 (m n : ℕ) (z : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  if 0 < _root_.GD.N0096.N0341.d021955 m z.1 + _root_.GD.N0096.N0341.d021955 n z.2 then
    (_root_.GD.N0096.N0341.d021955 n z.2 * _root_.GD.N0096.N0341.d021954 m z.1 + _root_.GD.N0096.N0341.d021955 m z.1 * _root_.GD.N0096.N0341.d021954 n z.2) /
      (_root_.GD.N0096.N0341.d021955 m z.1 + _root_.GD.N0096.N0341.d021955 n z.2)
  else 0

theorem d021957 (k : ℕ) (x : Fin k → ℝ) :
    _root_.GD.N0096.N0341.d021954 k x = _root_.GD.N0107.d009084 x := by
  simp [_root_.GD.N0096.N0341.d021954, _root_.GD.N0107.d009084, _root_.GD.N0126.d006420,
    _root_.GD.N0126.d006419]

theorem d021958 (k : ℕ) (x : Fin k → ℝ) :
    _root_.GD.N0096.N0341.d021955 k x = _root_.GD.N0107.d009085 x / k := by
  simp only [_root_.GD.N0096.N0341.d021955, _root_.GD.N0096.N0341.d021957, _root_.GD.N0107.d009085,
    _root_.GD.N0126.d006422, _root_.GD.N0126.d006421,
    _root_.GD.N0107.d009084, div_div]
  rw [mul_comm (k : ℝ)]

theorem d021959 (k : ℕ) (x : Fin k → ℝ) :
    0 ≤ _root_.GD.N0096.N0341.d021955 k x := by
  unfold _root_.GD.N0096.N0341.d021955
  positivity

theorem d021960 (m n : ℕ) : Measurable (_root_.GD.N0096.N0341.d021956 m n) := by
  unfold _root_.GD.N0096.N0341.d021956 _root_.GD.N0096.N0341.d021955 _root_.GD.N0096.N0341.d021954
  apply Measurable.ite
  · exact measurableSet_lt measurable_const (by fun_prop)
  · fun_prop
  · exact measurable_const

theorem d021961 (m n : ℕ) (z : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hpos : 0 < _root_.GD.N0096.N0341.d021955 m z.1 + _root_.GD.N0096.N0341.d021955 n z.2) :
    _root_.GD.N0096.N0341.d021956 m n z = _root_.GD.N0232.N0720.N1080.d014175 m n z := by
  rw [_root_.GD.N0096.N0341.d021956, if_pos hpos]
  simp only [_root_.GD.N0096.N0341.d021958, _root_.GD.N0096.N0341.d021957] at hpos ⊢
  unfold _root_.GD.N0232.N0720.N1080.d014175 _root_.GD.N0107.d012733 _root_.GD.N0107.d009091 _root_.GD.N0107.d009090
  field_simp [hpos.ne']
  ring

theorem d021962 (m n : ℕ) :
    _root_.GD.N0232.N0720.N1080.d014172 m n = _root_.GD.N0137.d008914 m n := by
  change (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0107.d009024 m n 0 1 1) = _
  have hid : _root_.GD.N0107.d009024 m n 0 1 1 = id := by
    funext z
    ext <;> simp [_root_.GD.N0107.d009024, _root_.GD.N0107.d009018]
  rw [hid, Measure.map_id]

theorem d021963 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∀ᵐ z ∂_root_.GD.N0232.N0720.N1080.d014172 m n, 0 < _root_.GD.N0096.N0341.d021955 m z.1 + _root_.GD.N0096.N0341.d021955 n z.2 := by
  rw [_root_.GD.N0096.N0341.d021962]
  filter_upwards [_root_.GD.N0119.d009075
    m n hm hn (e := 1 / 2) (by norm_num) (by norm_num)] with z hz
  rw [_root_.GD.N0096.N0341.d021958, _root_.GD.N0096.N0341.d021958]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact add_pos (div_pos hz.1 hm0) (div_pos hz.2 hn0)

theorem d021964 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0096.N0341.d021956 m n =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1080.d014175 m n := by
  filter_upwards [_root_.GD.N0096.N0341.d021963 m n hm hn] with z hz
  exact _root_.GD.N0096.N0341.d021961 m n z hz

theorem d021965 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0096.N0341.d021956 m n =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] _root_.GD.N0232.N0720.N1080.d014175 m n :=
  (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_eq
    (_root_.GD.N0096.N0341.d021964 m n hm hn)

theorem d021966
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0096.N0341.d021956 m n) =
      _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014197
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0096.N0341.d021965 m n hm hn θ] with z hz
  rw [hz]

end
end GD.N0096.N0341

#print axioms _root_.GD.N0096.N0341.d021960
#print axioms _root_.GD.N0096.N0341.d021965
#print axioms _root_.GD.N0096.N0341.d021966
