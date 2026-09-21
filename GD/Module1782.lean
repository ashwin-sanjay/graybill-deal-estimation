import GD.Module1739
import GD.Module1781
import GD.Module0367



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Finset
namespace GD.N0106.N0428.N0765.N1666
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1670 _root_.GD.N0106.N0428.N0765.N1668 _root_.GD.N0106.N0428.N0765.N1568

def d029635 (a p v w c h : ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1568.d005509 h (v^(-p)) a (c-h) +
    _root_.GD.N0106.N0428.N0765.N1568.d005510 h (w^(-p)) (p-a) (c+N*h)

theorem d029636 {a p e u v w h c : ℝ} {n : ℕ}
    (ha : 0 < a) (hn : (n : ℝ) ≤ p) (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) (hh : 0 < h) :
    Summable (fun m : ℕ => h*_root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w (_root_.GD.N0106.N0428.N0765.N1568.d005507 c h m)) ∧
    ∑' m : ℕ, h*_root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w (_root_.GD.N0106.N0428.N0765.N1568.d005507 c h m) ≤
      _root_.GD.N0106.N0428.N0765.N1568.d005509 h (v^(-p)) a c :=
  _root_.GD.N0106.N0428.N0765.N1568.d005519 ha hh (fun _ => _root_.GD.N0106.N0428.N0765.N1670.d028862 a p n he hu hv hw.le _)
    (fun _ => _root_.GD.N0106.N0428.N0765.N1670.d028863 a hn he hu hv hw.le _)

theorem d029637 {a p e u v w h c : ℝ} {n : ℕ}
    (hap : a < p) (hn : (n : ℝ) ≤ p) (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) (hh : 0 < h) :
    Summable (fun m : ℕ => h*_root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w (_root_.GD.N0106.N0428.N0765.N1568.d005508 c h m)) ∧
    ∑' m : ℕ, h*_root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w (_root_.GD.N0106.N0428.N0765.N1568.d005508 c h m) ≤
      _root_.GD.N0106.N0428.N0765.N1568.d005510 h (w^(-p)) (p-a) c := by
  apply _root_.GD.N0106.N0428.N0765.N1568.d005520 (sub_pos.mpr hap) hh
    (fun _ => _root_.GD.N0106.N0428.N0765.N1670.d028862 a p n he hu hv hw.le _)
  intro m
  simpa only [show a-p = -(p-a) by ring, neg_mul] using
    _root_.GD.N0106.N0428.N0765.N1670.d028864 a hn he hu hv.le hw (_root_.GD.N0106.N0428.N0765.N1568.d005508 c h m)

theorem d029638 {a p e u v w h c eps Sm Sp : ℝ} {n N : ℕ}
    (ha : 0 < a) (hap : a < p) (hn : (n : ℝ) ≤ p)
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (hh : 0 < h)
    (heps : 0 ≤ eps) (heps1 : eps < 1)
    (hrel : |h*(∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w (c+h*k)) -
      ∫ x, _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w x| ≤ eps*∫ x, _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w x)
    (hl : Sm ≤ ∑ i ∈ range N, h*_root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w (c+i*h))
    (hr : (∑ i ∈ range N, h*_root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w (c+i*h)) ≤ Sp) :
    Sm/(1+eps) ≤ ∫ x, _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w x ∧
      (∫ x, _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w x) ≤ (Sp+_root_.GD.N0106.N0428.N0765.N1666.d029635 a p v w c h N)/(1-eps) := by
  have hL := _root_.GD.N0106.N0428.N0765.N1666.d029636 (c := c-h) ha hn he hu hv hw hh
  have hR := _root_.GD.N0106.N0428.N0765.N1666.d029637 (c := c+N*h) hap hn he hu hv hw hh
  apply _root_.GD.N0106.N0428.N0765.N1568.d005525 (_root_.GD.N0106.N0428.N0765.N1670.d028862 a p n he hu hv hw.le) hh.le
    hL.1 hL.2 hR.1 hR.2 heps heps1 _ hl hr
  simpa only [tsum_mul_left, mul_comm, abs_sub_comm] using hrel

theorem d029639 {e u v w d h c Sm Sp : ℝ} {N : ℕ}
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi/2) (hh : 0 < h)
    (heps : 0 ≤ _root_.GD.N0106.N0428.N0765.N1668.d029629 d h) (heps1 : _root_.GD.N0106.N0428.N0765.N1668.d029629 d h < 1)
    (hl : Sm ≤ ∑ i ∈ range N, h*_root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w (c+i*h))
    (hr : (∑ i ∈ range N, h*_root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w (c+i*h)) ≤ Sp) :
    Sm/(1+_root_.GD.N0106.N0428.N0765.N1668.d029629 d h) ≤ ∫ x, _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w x ∧
      (∫ x, _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w x) ≤ (Sp+_root_.GD.N0106.N0428.N0765.N1666.d029635 (11/2) (21/2) v w c h N)/(1-_root_.GD.N0106.N0428.N0765.N1668.d029629 d h) :=
  _root_.GD.N0106.N0428.N0765.N1666.d029638 (by norm_num) (by norm_num) (by norm_num) he hu hv hw hh
    heps heps1 (_root_.GD.N0106.N0428.N0765.N1668.d029633 he hu hv hw hd hdpi hh c) hl hr

theorem d029640 {e u v w d h c Sm Sp : ℝ} {N : ℕ}
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi/2) (hh : 0 < h)
    (heps : 0 ≤ _root_.GD.N0106.N0428.N0765.N1668.d029629 d h) (heps1 : _root_.GD.N0106.N0428.N0765.N1668.d029629 d h < 1)
    (hl : Sm ≤ ∑ i ∈ range N, h*_root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w (c+i*h))
    (hr : (∑ i ∈ range N, h*_root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w (c+i*h)) ≤ Sp) :
    Sm/(1+_root_.GD.N0106.N0428.N0765.N1668.d029629 d h) ≤ ∫ x, _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w x ∧
      (∫ x, _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w x) ≤ (Sp+_root_.GD.N0106.N0428.N0765.N1666.d029635 (13/2) (21/2) v w c h N)/(1-_root_.GD.N0106.N0428.N0765.N1668.d029629 d h) :=
  _root_.GD.N0106.N0428.N0765.N1666.d029638 (by norm_num) (by norm_num) (by norm_num) he hu hv hw hh
    heps heps1 (_root_.GD.N0106.N0428.N0765.N1668.d029634 he hu hv hw hd hdpi hh c) hl hr

end
end GD.N0106.N0428.N0765.N1666
#print axioms _root_.GD.N0106.N0428.N0765.N1666.d029639
#print axioms _root_.GD.N0106.N0428.N0765.N1666.d029640
