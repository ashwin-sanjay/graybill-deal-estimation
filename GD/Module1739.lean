import GD.Module1288
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1670
noncomputable section

def d028854 (e u v w c : ℝ) : ℝ :=
  (v + w * Real.exp c) * (1 + e * Real.exp c) +
    (1 + e) * u * Real.exp c

def d028855 (a p : ℝ) (n : ℕ) (e u v w c : ℝ) : ℝ :=
  Real.exp (a*c) * (1 + e*Real.exp c)^n * _root_.GD.N0106.N0428.N0765.N1670.d028854 e u v w c ^ (-p)

def d028856 (e u v w : ℝ) : ℝ → ℝ := _root_.GD.N0106.N0428.N0765.N1670.d028855 (11/2) (21/2) 10 e u v w
def d028857 (e u v w : ℝ) : ℝ → ℝ := _root_.GD.N0106.N0428.N0765.N1670.d028855 (13/2) (21/2) 9 e u v w

theorem d028858 {e u v w : ℝ} (he : 0 ≤ e) (hu : 0 ≤ u)
    (hw : 0 ≤ w) (c : ℝ) : v*(1+e*Real.exp c) ≤ _root_.GD.N0106.N0428.N0765.N1670.d028854 e u v w c := by
  have h1 : 0 ≤ w*Real.exp c*(1+e*Real.exp c) := by positivity
  have h2 : 0 ≤ (1+e)*u*Real.exp c := by positivity
  unfold _root_.GD.N0106.N0428.N0765.N1670.d028854
  nlinarith only [h1,h2]

theorem d028859 {e u v w : ℝ} (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (c : ℝ) :
    (w*Real.exp c)*(1+e*Real.exp c) ≤ _root_.GD.N0106.N0428.N0765.N1670.d028854 e u v w c := by
  have h1 : 0 ≤ v*(1+e*Real.exp c) := by positivity
  have h2 : 0 ≤ (1+e)*u*Real.exp c := by positivity
  unfold _root_.GD.N0106.N0428.N0765.N1670.d028854
  nlinarith only [h1,h2]

theorem d028860 {e u v w : ℝ} (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 ≤ w) (c : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1670.d028854 e u v w c :=
  (mul_pos hv (by positivity)).trans_le (_root_.GD.N0106.N0428.N0765.N1670.d028858 he hu hw c)


theorem d028861 {r t p : ℝ} {n : ℕ} (hr : 0 < r) (ht : 1 ≤ t)
    (hn : (n : ℝ) ≤ p) : t^n * (r*t)^(-p) ≤ r^(-p) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hpower : t^n * t^(-p) ≤ 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
    exact Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
  rw [Real.mul_rpow hr.le ht0.le]
  calc t^n*(r^(-p)*t^(-p)) = r^(-p)*(t^n*t^(-p)) := by ring
    _ ≤ r^(-p)*1 := mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg hr.le _)
    _ = r^(-p) := mul_one _

theorem d028862 (a p : ℝ) (n : ℕ) {e u v w : ℝ}
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 ≤ w) (c : ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w c := by
  have hq := (_root_.GD.N0106.N0428.N0765.N1670.d028860 he hu hv hw c).le
  unfold _root_.GD.N0106.N0428.N0765.N1670.d028855
  positivity


theorem d028863 (a : ℝ) {p e u v w : ℝ} {n : ℕ}
    (hn : (n : ℝ) ≤ p) (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 ≤ w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w c ≤ v^(-p)*Real.exp (a*c) := by
  have ht : 1 ≤ 1+e*Real.exp c := le_add_of_nonneg_right (mul_nonneg he (Real.exp_pos c).le)
  have ht0 : 0 < 1+e*Real.exp c := by positivity
  have hp : 0 ≤ p := (Nat.cast_nonneg n).trans hn
  have hden := Real.rpow_le_rpow_of_nonpos (mul_pos hv ht0)
    (_root_.GD.N0106.N0428.N0765.N1670.d028858 he hu hw c) (neg_nonpos.mpr hp)
  have h := (mul_le_mul_of_nonneg_left hden
    (pow_nonneg ht0.le n)).trans (_root_.GD.N0106.N0428.N0765.N1670.d028861 hv ht hn)
  calc _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w c =
      Real.exp (a*c)*((1+e*Real.exp c)^n * _root_.GD.N0106.N0428.N0765.N1670.d028854 e u v w c^(-p)) := by
        unfold _root_.GD.N0106.N0428.N0765.N1670.d028855; ring
    _ ≤ Real.exp (a*c)*v^(-p) := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := mul_comm _ _


theorem d028864 (a : ℝ) {p e u v w : ℝ} {n : ℕ}
    (hn : (n : ℝ) ≤ p) (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hw : 0 < w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w c ≤ w^(-p)*Real.exp ((a-p)*c) := by
  have ht : 1 ≤ 1+e*Real.exp c := le_add_of_nonneg_right (mul_nonneg he (Real.exp_pos c).le)
  have ht0 : 0 < 1+e*Real.exp c := by positivity
  have hr : 0 < w*Real.exp c := mul_pos hw (Real.exp_pos c)
  have hp : 0 ≤ p := (Nat.cast_nonneg n).trans hn
  have hden := Real.rpow_le_rpow_of_nonpos (mul_pos hr ht0)
    (_root_.GD.N0106.N0428.N0765.N1670.d028859 he hu hv c) (neg_nonpos.mpr hp)
  have h := (mul_le_mul_of_nonneg_left hden
    (pow_nonneg ht0.le n)).trans (_root_.GD.N0106.N0428.N0765.N1670.d028861 hr ht hn)
  calc _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w c =
      Real.exp (a*c)*((1+e*Real.exp c)^n * _root_.GD.N0106.N0428.N0765.N1670.d028854 e u v w c^(-p)) := by
        unfold _root_.GD.N0106.N0428.N0765.N1670.d028855; ring
    _ ≤ Real.exp (a*c)*(w*Real.exp c)^(-p) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = w^(-p)*Real.exp ((a-p)*c) := by
      rw [Real.mul_rpow hw.le (Real.exp_pos c).le, ← Real.exp_mul]
      rw [show Real.exp (a*c)*(w^(-p)*Real.exp (c*(-p))) =
        w^(-p)*(Real.exp (a*c)*Real.exp (c*(-p))) by ring, ← Real.exp_add]
      congr 2
      ring

theorem d028865 {e u v w : ℝ} (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 ≤ w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w c ≤ v^(-21/2 : ℝ)*Real.exp (11*c/2) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1670.d028856, show -(21/2 : ℝ) = -21/2 by ring, show (11/2 : ℝ)*c = 11*c/2 by ring] using
    _root_.GD.N0106.N0428.N0765.N1670.d028863 (11/2) (n := 10) (p := 21/2) (by norm_num) he hu hv hw c

theorem d028866 {e u v w : ℝ} (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 ≤ w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w c ≤ v^(-21/2 : ℝ)*Real.exp (13*c/2) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1670.d028857, show -(21/2 : ℝ) = -21/2 by ring, show (13/2 : ℝ)*c = 13*c/2 by ring] using
    _root_.GD.N0106.N0428.N0765.N1670.d028863 (13/2) (n := 9) (p := 21/2) (by norm_num) he hu hv hw c

theorem d028867 {e u v w : ℝ} (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hw : 0 < w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w c ≤ w^(-21/2 : ℝ)*Real.exp (-5*c) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1670.d028856, show -(21/2 : ℝ) = -21/2 by ring, show ((11/2 : ℝ)-21/2)*c = -5*c by ring] using
    _root_.GD.N0106.N0428.N0765.N1670.d028864 (11/2) (n := 10) (p := 21/2) (by norm_num) he hu hv hw c

theorem d028868 {e u v w : ℝ} (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hw : 0 < w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w c ≤ w^(-21/2 : ℝ)*Real.exp (-4*c) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1670.d028857, show -(21/2 : ℝ) = -21/2 by ring, show ((13/2 : ℝ)-21/2)*c = -4*c by ring] using
    _root_.GD.N0106.N0428.N0765.N1670.d028864 (13/2) (n := 9) (p := 21/2) (by norm_num) he hu hv hw c

theorem d028869 {e : ℝ} (he : 0 < e) (u v w c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1616.d020956 e⁻¹ u v w (Real.log e+c) = _root_.GD.N0106.N0428.N0765.N1670.d028854 e u v w c := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020956 _root_.GD.N0106.N0428.N0765.N1670.d028854
  rw [Real.exp_add, Real.exp_log he]
  field_simp
  <;> ring

theorem d028870 {e : ℝ} (he : 0 < e) (u v w c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1616.d020957 e⁻¹ u v w (Real.log e+c) =
      Real.exp (11*Real.log e/2)*_root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w c := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020957
  rw [_root_.GD.N0106.N0428.N0765.N1670.d028869 he, Real.exp_add, Real.exp_log he]
  rw [show 11*(Real.log e+c)/2 = 11*Real.log e/2 + (11/2)*c by ring,
    Real.exp_add]
  unfold _root_.GD.N0106.N0428.N0765.N1670.d028856 _root_.GD.N0106.N0428.N0765.N1670.d028855
  ring

theorem d028871 {e : ℝ} (he : 0 < e) (u v w c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1616.d020958 e⁻¹ u v w (Real.log e+c) =
      Real.exp (13*Real.log e/2)*_root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w c := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020958
  rw [_root_.GD.N0106.N0428.N0765.N1670.d028869 he, Real.exp_add, Real.exp_log he]
  rw [show 13*(Real.log e+c)/2 = 13*Real.log e/2 + (13/2)*c by ring,
    Real.exp_add]
  unfold _root_.GD.N0106.N0428.N0765.N1670.d028857 _root_.GD.N0106.N0428.N0765.N1670.d028855
  ring

end
end GD.N0106.N0428.N0765.N1670
#print axioms _root_.GD.N0106.N0428.N0765.N1670.d028863
#print axioms _root_.GD.N0106.N0428.N0765.N1670.d028864
#print axioms _root_.GD.N0106.N0428.N0765.N1670.d028870
#print axioms _root_.GD.N0106.N0428.N0765.N1670.d028871
