import GD.Module1780
import GD.Module1782
import GD.Module1740



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Finset
namespace GD.N0106.N0428.N0765.N1669
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1670 _root_.GD.N0106.N0428.N0765.N1668 _root_.GD.N0106.N0428.N0765.N1666 _root_.GD.N0106.N0428.N0765.N1671 _root_.GD.N0106.N0428.N0765.N1667

def d029641 (v w d h c Sm1 Sp0 : ℝ) (N : ℕ) : ℝ :=
  (Sm1/(1+_root_.GD.N0106.N0428.N0765.N1668.d029629 d h)) / ((Sp0+_root_.GD.N0106.N0428.N0765.N1666.d029635 (11/2) (21/2) v w c h N)/(1-_root_.GD.N0106.N0428.N0765.N1668.d029629 d h))
def d029642 (v w d h c Sm0 Sp1 : ℝ) (N : ℕ) : ℝ :=
  ((Sp1+_root_.GD.N0106.N0428.N0765.N1666.d029635 (13/2) (21/2) v w c h N)/(1-_root_.GD.N0106.N0428.N0765.N1668.d029629 d h))/(Sm0/(1+_root_.GD.N0106.N0428.N0765.N1668.d029629 d h))



theorem d029643 {e u v w d h c Sm0 Sp0 Sm1 Sp1 : ℝ} {N : ℕ}
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi/2) (hh : 0 < h)
    (heps1 : _root_.GD.N0106.N0428.N0765.N1668.d029629 d h < 1)
    (hl0 : Sm0 ≤ ∑ i ∈ range N, h*_root_.GD.N0106.N0428.N0765.N1671.d028875 e u v w (c+i*h))
    (hr0 : (∑ i ∈ range N, h*_root_.GD.N0106.N0428.N0765.N1671.d028875 e u v w (c+i*h)) ≤ Sp0)
    (hl1 : Sm1 ≤ ∑ i ∈ range N, h*_root_.GD.N0106.N0428.N0765.N1671.d028876 e u v w (c+i*h))
    (hr1 : (∑ i ∈ range N, h*_root_.GD.N0106.N0428.N0765.N1671.d028876 e u v w (c+i*h)) ≤ Sp1)
    (hpos : 0 < Sm0) (hnn : 0 ≤ Sm1) :
    _root_.GD.N0106.N0428.N0765.N1669.d029641 v w d h c Sm1 Sp0 N ≤ _root_.GD.N0106.N0428.N0765.N1667.d029622 e u v w ∧
      _root_.GD.N0106.N0428.N0765.N1667.d029622 e u v w ≤ _root_.GD.N0106.N0428.N0765.N1669.d029642 v w d h c Sm0 Sp1 N := by
  have hc : 0 < Real.cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hdpi⟩
  have hx : 0 < 2*Real.pi*d/h := by positivity
  have hex : 0 < Real.exp (2*Real.pi*d/h)-1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
  have heps : 0 ≤ _root_.GD.N0106.N0428.N0765.N1668.d029629 d h := by
    unfold _root_.GD.N0106.N0428.N0765.N1668.d029629
    exact (div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hc _)) hex).le
  simp_rw [_root_.GD.N0106.N0428.N0765.N1671.d028880 he hu hv hw.le] at hl0 hr0
  simp_rw [_root_.GD.N0106.N0428.N0765.N1671.d028881 he hu hv hw.le] at hl1 hr1
  exact _root_.GD.N0106.N0428.N0765.N1568.d005524 (div_pos hpos (by linarith))
    (div_nonneg hnn (by linarith))
    (_root_.GD.N0106.N0428.N0765.N1666.d029639 he hu hv hw hd hdpi hh heps heps1 hl0 hr0)
    (_root_.GD.N0106.N0428.N0765.N1666.d029640 he hu hv hw hd hdpi hh heps heps1 hl1 hr1)



theorem d029644 {e L U : ℝ} (he : 0 ≤ e) (a b : ℝ)
    (hb : L ≤ _root_.GD.N0106.N0428.N0765.N1667.d029622 e (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a,b) 0)
      (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a,b) 1) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a,b) 2) ∧
      _root_.GD.N0106.N0428.N0765.N1667.d029622 e (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a,b) 0)
      (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a,b) 1) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a,b) 2) ≤ U) :
    L ≤ (_root_.GD.N0106.N0428.N0765.N1672.d021424 e a b 0 0 /
      _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b 0 0).re ∧
      (_root_.GD.N0106.N0428.N0765.N1672.d021424 e a b 0 0 /
      _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b 0 0).re ≤ U := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1667.d029628 he a b, Complex.ofReal_re] using hb

end
end GD.N0106.N0428.N0765.N1669
#print axioms _root_.GD.N0106.N0428.N0765.N1669.d029643
#print axioms _root_.GD.N0106.N0428.N0765.N1669.d029644
