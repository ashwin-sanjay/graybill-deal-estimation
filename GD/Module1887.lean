import GD.Module1885
import GD.Module1867

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0082.N0333

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1066 _root_.GD.N0232.N0720.N1069
open _root_.GD.N0232.N0720.N1035 _root_.GD.N0232.N0720.N1219
open _root_.GD.N0230.N0602
open _root_.GD.N0076.N0313 _root_.GD.N0082.N0335

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d030736 (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (t : ℝ) :
    0 ≤ _root_.GD.N0082.N0335.d030707 m n hm hn p t := by
  unfold _root_.GD.N0082.N0335.d030707
  split_ifs with ht
  · exact div_nonneg ENNReal.toReal_nonneg (_root_.GD.N0076.N0313.d030566 m n hm hn _).le
  · exact le_rfl

theorem d030737
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) (hpa : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p) =
      ENNReal.ofReal (_root_.GD.N0082.N0335.d030707 m n hm hn p (_root_.GD.N0232.N0720.N1069.d014352 m n θ)) := by
  let t := _root_.GD.N0232.N0720.N1069.d014352 m n θ
  have ht : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨_root_.GD.N0232.N0720.N1069.d014353 m n hm hn θ, _root_.GD.N0232.N0720.N1069.d014354 m n hm hn θ⟩
  let η := _root_.GD.N0232.N0720.N1219.d017942 m n hm hn t ht
  let g := _root_.GD.N0232.N0720.N1035.d014376 η θ
  have hfrac : _root_.GD.N0232.N0720.N1069.d014352 m n η = _root_.GD.N0232.N0720.N1069.d014352 m n θ :=
    _root_.GD.N0232.N0720.N1219.d017949 m n hm hn t ht
  have hmap : _root_.GD.N0232.N0720.N1215.d014272 g η = θ :=
    _root_.GD.N0232.N0720.N1035.d014379 m n hm hn hfrac
  have hg0 : ENNReal.ofReal (g.d009239 ^ 2) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply sq_pos_of_pos
    rw [_root_.GD.N0232.N0720.N1035.d014377]
    exact div_pos θ.scale₁_pos η.scale₁_pos
  have hrat : _root_.GD.N0232.N0720.N1080.d014182 m n θ p / _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ =
      _root_.GD.N0232.N0720.N1080.d014182 m n η p / _root_.GD.N0232.N0720.N1066.d014320 m n hm hn η := by
    rw [← hmap, hpa g η]
    change ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n η p /
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g η) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) = _
    rw [_root_.GD.N0232.N0720.N1215.d014293]
    exact ENNReal.mul_div_mul_left _ _ hg0 ENNReal.ofReal_ne_top
  unfold _root_.GD.N0076.N0313.d030568
  rw [_root_.GD.N0232.N0720.N1215.d014286, hrat]
  rw [_root_.GD.N0082.N0335.d030708 m n hm hn p t ht,
    ENNReal.ofReal_div_of_pos (_root_.GD.N0076.N0313.d030566 m n hm hn η),
    ENNReal.ofReal_toReal (hp η), _root_.GD.N0076.N0313.d030567]

theorem d030738 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) =
      ENNReal.ofReal (_root_.GD.N0082.N0335.d030720 m n hm hn (_root_.GD.N0232.N0720.N1069.d014352 m n θ)) := by
  have h := _root_.GD.N0082.N0333.d030737 m n hm hn (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
    (_root_.GD.N0082.N0335.d030719 m n hm hn)
    (_root_.GD.N0232.N0720.N1215.d014296 m n hm hn) θ
  simpa only [_root_.GD.N0076.N0313.d030568, _root_.GD.N0232.N0720.N1215.d014286,
    _root_.GD.N0232.N0720.N1215.d014295, _root_.GD.N0082.N0335.d030720] using h

theorem d030739 (t : ℝ) :
    0 ≤ _root_.GD.N0082.N0335.d030720 m n hm hn t :=
  _root_.GD.N0082.N0333.d030736 m n hm hn _ t

theorem d030740
    (e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (he : e ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (q : ℝ → ℝ)
    (hq0 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ q t)
    (hqcont : ContinuousOn q (Icc 0 1))
    (hqleft : q 0 < 1) (hqright : q 1 < 1)
    (hqe : ∀ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ e ≤
      ENNReal.ofReal (q (_root_.GD.N0232.N0720.N1069.d014352 m n θ))) :
    _root_.GD.N0082.d030603 m n hm hn := by
  apply _root_.GD.N0082.N0331.d030613 m n hm hn
    (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)) e
    (_root_.GD.N0076.N0313.d030572 m n
      (_root_.GD.N0082.N0335.d030719 m n hm hn)) he
    (_root_.GD.N0232.N0720.N1069.d014352 m n)
    (fun θ => ⟨_root_.GD.N0232.N0720.N1069.d014353 m n hm hn θ,
      _root_.GD.N0232.N0720.N1069.d014354 m n hm hn θ⟩)
    (_root_.GD.N0082.N0335.d030720 m n hm hn) q
    (fun t _ => _root_.GD.N0082.N0333.d030739 m n hm hn t) hq0
    (_root_.GD.N0082.N0335.d030721 m n hm hn)
    (_root_.GD.N0082.N0335.d030722 m n hm hn) hqcont hqleft hqright
    (fun θ => (_root_.GD.N0082.N0333.d030737 m n hm hn (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
      (_root_.GD.N0082.N0335.d030719 m n hm hn)
      (_root_.GD.N0232.N0720.N1215.d014296 m n hm hn) θ).le) hqe

end

end GD.N0082.N0333

#print axioms _root_.GD.N0082.N0333.d030736
#print axioms _root_.GD.N0082.N0333.d030737
#print axioms _root_.GD.N0082.N0333.d030738
#print axioms _root_.GD.N0082.N0333.d030740
