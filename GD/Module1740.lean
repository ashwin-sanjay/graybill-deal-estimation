import GD.Module1739



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory
namespace GD.N0106.N0428.N0765.N1671
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1670

def d028872 (c : ℝ) : ℝ := Real.exp c/(1+Real.exp c)
def d028873 (c : ℝ) : ℝ := 1/(1+Real.exp c)
def d028874 (e u v w c : ℝ) : ℝ :=
  (v*_root_.GD.N0106.N0428.N0765.N1671.d028873 c+w*_root_.GD.N0106.N0428.N0765.N1671.d028872 c)*(_root_.GD.N0106.N0428.N0765.N1671.d028873 c+e*_root_.GD.N0106.N0428.N0765.N1671.d028872 c)+(1+e)*u*_root_.GD.N0106.N0428.N0765.N1671.d028872 c*_root_.GD.N0106.N0428.N0765.N1671.d028873 c

def d028875 (e u v w c : ℝ) : ℝ :=
  let lm := _root_.GD.N0106.N0428.N0765.N1671.d028872 c*_root_.GD.N0106.N0428.N0765.N1671.d028873 c
  lm^5*Real.sqrt lm*(_root_.GD.N0106.N0428.N0765.N1671.d028873 c+e*_root_.GD.N0106.N0428.N0765.N1671.d028872 c)^10 /
    (_root_.GD.N0106.N0428.N0765.N1671.d028874 e u v w c^10*Real.sqrt (_root_.GD.N0106.N0428.N0765.N1671.d028874 e u v w c))
def d028876 (e u v w c : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1671.d028875 e u v w c * _root_.GD.N0106.N0428.N0765.N1671.d028872 c / (_root_.GD.N0106.N0428.N0765.N1671.d028873 c+e*_root_.GD.N0106.N0428.N0765.N1671.d028872 c)

theorem d028877 (e u v w c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1671.d028874 e u v w c = _root_.GD.N0106.N0428.N0765.N1670.d028854 e u v w c/(1+Real.exp c)^2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1671.d028874 _root_.GD.N0106.N0428.N0765.N1671.d028872 _root_.GD.N0106.N0428.N0765.N1671.d028873 _root_.GD.N0106.N0428.N0765.N1670.d028854
  field_simp
  <;> ring

theorem d028878 {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x^n*Real.sqrt x = x^((n : ℝ)+1/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hx]

theorem d028879 {r d q : ℝ} (hr : 0 < r) (hd : 0 < d) (hq : 0 < q) (t : ℝ) :
    (r/d^2)^5 * Real.sqrt (r/d^2) * (t/d)^10 /
      ((q/d^2)^10 * Real.sqrt (q/d^2)) =
      r^(11/2 : ℝ)*t^10*q^(-(21/2) : ℝ) := by
  have hr2 : 0 < r/d^2 := by positivity
  have hq2 : 0 < q/d^2 := by positivity
  have hn : (r/d^2)^5 * Real.sqrt (r/d^2) = (r/d^2)*(r/d^2)^(9/2 : ℝ) := by
    rw [_root_.GD.N0106.N0428.N0765.N1671.d028878 hr2]
    norm_num only [Nat.cast_ofNat]
    rw [show (11/2 : ℝ) = 9/2+1 by ring, Real.rpow_add_one hr2.ne']
    ring
  rw [hn, _root_.GD.N0106.N0428.N0765.N1671.d028878 hq2]
  norm_num only [Nat.cast_ofNat]
  rw [div_eq_mul_inv _ ((q/d^2)^(21/2 : ℝ)), ← Real.rpow_neg hq2.le]
  have hh := _root_.GD.N0106.N0428.N0765.N1616.d020961 hr hd hq
  calc
    r/d^2*(r/d^2)^(9/2 : ℝ)*(t/d)^10*(q/d^2)^(-(21/2) : ℝ) =
        ((r/d^2)*((r/d^2)^(9/2 : ℝ)*(q/d^2)^(-(21/2) : ℝ)))*(t/d)^10 := by ring
    _ = r^(11/2 : ℝ)*d^10*q^(-(21/2) : ℝ)*(t/d)^10 := by rw [hh]
    _ = r^(11/2 : ℝ)*t^10*q^(-(21/2) : ℝ) := by
      rw [div_pow]
      field_simp [hd.ne']
      <;> ring

theorem d028880 {e u v w : ℝ} (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 ≤ w) (c : ℝ) : _root_.GD.N0106.N0428.N0765.N1671.d028875 e u v w c = _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w c := by
  have hprod : _root_.GD.N0106.N0428.N0765.N1671.d028872 c*_root_.GD.N0106.N0428.N0765.N1671.d028873 c = Real.exp c/(1+Real.exp c)^2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1671.d028872 _root_.GD.N0106.N0428.N0765.N1671.d028873; field_simp <;> ring
  have ht : _root_.GD.N0106.N0428.N0765.N1671.d028873 c+e*_root_.GD.N0106.N0428.N0765.N1671.d028872 c = (1+e*Real.exp c)/(1+Real.exp c) := by
    unfold _root_.GD.N0106.N0428.N0765.N1671.d028872 _root_.GD.N0106.N0428.N0765.N1671.d028873; field_simp
  unfold _root_.GD.N0106.N0428.N0765.N1671.d028875
  rw [hprod, ht, _root_.GD.N0106.N0428.N0765.N1671.d028877, _root_.GD.N0106.N0428.N0765.N1671.d028879 (Real.exp_pos c) (by positivity)
    (_root_.GD.N0106.N0428.N0765.N1670.d028860 he hu hv hw c)]
  unfold _root_.GD.N0106.N0428.N0765.N1670.d028856 _root_.GD.N0106.N0428.N0765.N1670.d028855
  rw [← Real.exp_mul]
  congr 2 <;> ring

theorem d028881 {e u v w : ℝ} (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 ≤ w) (c : ℝ) : _root_.GD.N0106.N0428.N0765.N1671.d028876 e u v w c = _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w c := by
  have ht : 0 < 1+e*Real.exp c := by positivity
  unfold _root_.GD.N0106.N0428.N0765.N1671.d028876
  rw [_root_.GD.N0106.N0428.N0765.N1671.d028880 he hu hv hw]
  unfold _root_.GD.N0106.N0428.N0765.N1670.d028856 _root_.GD.N0106.N0428.N0765.N1670.d028857 _root_.GD.N0106.N0428.N0765.N1670.d028855 _root_.GD.N0106.N0428.N0765.N1671.d028872 _root_.GD.N0106.N0428.N0765.N1671.d028873
  rw [show (13/2 : ℝ)*c = (11/2)*c+c by ring, Real.exp_add]
  field_simp [ht.ne']
  <;> ring

end
end GD.N0106.N0428.N0765.N1671
#print axioms _root_.GD.N0106.N0428.N0765.N1671.d028880
#print axioms _root_.GD.N0106.N0428.N0765.N1671.d028881
