import GD.Module0890
import GD.Module1215
import GD.Module0004













open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0232.N0720.N1335

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1342
open _root_.GD.N0232.N0720.N1337
open _root_.GD.N0232.N0720.N1287 _root_.GD.N0232.N0720.N1398
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0141
open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0556

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d020087 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (g x - t) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 m n t

theorem d020088 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (t : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1335.d020087 m n g t := integral_nonneg (fun _ ↦ sq_nonneg _)

include hm hn in
theorem d020089
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (_root_.GD.N0107.d012732 m n theta.location
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) +
          _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
            _root_.GD.N0232.N0720.N1335.d020087 m n g (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) := by
  rw [_root_.GD.N0232.N0720.N1396.d014785 m n theta
    (_root_.GD.N0232.N0720.N1287.d019517 m n hm hn theta g hg hb)]
  congr 1
  exact _root_.GD.N0232.N0720.N1425.d014726
    m n hm hn theta.location theta.scale₁ theta.scale₂
    theta.scale₁_pos theta.scale₂_pos g hg (B := 1) (by norm_num)
    (fun x ↦ by rw [abs_of_nonneg (hb x).1]; exact (hb x).2)

include hm hn in


theorem d020090
    {g seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) (hseed : Measurable seed)
    (hgb : ∀ x, g x ∈ Icc (0 : ℝ) 1) (hseedb : ∀ x, seed x ∈ Icc (0 : ℝ) 1)
    (hdom : ∀ t : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0232.N0720.N1441.d013705 m n t g ≤ _root_.GD.N0232.N0720.N1441.d013705 m n t seed)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n seed) := by
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  let t : _root_.GD.N0232.N0720.N1441.d013676 :=
    ⟨_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂,
      _root_.GD.N0107.d009050 hm0 hn0 theta.scale₁_pos theta.scale₂_pos,
      _root_.GD.N0107.d009051 hm0 hn0 theta.scale₁_pos theta.scale₂_pos⟩
  have h := hdom t
  rw [_root_.GD.N0232.N0720.N1287.d019525 m n t g
      (_root_.GD.N0232.N0720.N1287.d019523 m n hm hn t g hg hgb),
    _root_.GD.N0232.N0720.N1287.d019525 m n t seed
      (_root_.GD.N0232.N0720.N1287.d019523 m n hm hn t seed hseed hseedb)] at h
  have hreal : _root_.GD.N0232.N0720.N1335.d020087 m n g t.1 ≤ _root_.GD.N0232.N0720.N1335.d020087 m n seed t.1 :=
    (ENNReal.ofReal_le_ofReal_iff (_root_.GD.N0232.N0720.N1335.d020088 m n seed t.1)).1 h
  rw [_root_.GD.N0232.N0720.N1335.d020089 m n hm hn theta hg hgb,
    _root_.GD.N0232.N0720.N1335.d020089 m n hm hn theta hseed hseedb]
  exact ENNReal.ofReal_le_ofReal (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hreal
      (_root_.GD.N0107.d009049 hm0 hn0 theta.scale₁_pos theta.scale₂_pos).le))

theorem d020091
    (seed : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hseed : Measurable seed)
    (hseedb : ∀ x, seed x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn)
      (_root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedb) := by
  rintro ⟨h, hdom, t, hstrict⟩
  have heq := (_root_.GD.N0232.N0720.N1441.d013691 hm hn seed hseed hseedb).2.1 h (fun q ↦ by
    rw [_root_.GD.N0232.N0720.N1337.d013833 m n hm hn, _root_.GD.N0232.N0720.N1337.d013833 m n hm hn]
    exact ENNReal.ofReal_le_ofReal (hdom q))
  exact lt_irrefl _ (heq ▸ hstrict)





theorem d020092
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) :
    ∃ (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (H : _root_.GD.N0232.N0720.N1441.d013681 m n),
      Measurable g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      ((H : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] _root_.GD.N0232.N0720.N1441.d013686 g) ∧
      _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn) H ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d := by
  obtain ⟨seed, hseed, hseedb, hrep⟩ :=
    _root_.GD.N0232.N0720.N1342.d019642 m n hm hn hd
  let g := _root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedb
  let H := _root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedb
  have hg : Measurable g :=
    _root_.GD.N0232.N0720.N1441.d013702 hm hn seed hseed hseedb
  have hgb : ∀ x, g x ∈ Icc (0 : ℝ) 1 :=
    _root_.GD.N0232.N0720.N1441.d013703 hm hn seed hseed hseedb
  have hweak (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
    have hbelow := _root_.GD.N0232.N0720.N1335.d020090 m n hm hn hg hseed hgb hseedb
      (_root_.GD.N0232.N0720.N1441.d013708 hm hn seed hseed hseedb) theta
    exact hbelow.trans_eq (_root_.GD.N0232.N0720.N1159.d014662 m n theta (hrep theta)).symm
  refine ⟨g, H, hg, hgb, ?_, ?_, ?_⟩
  · exact (_root_.GD.N0232.N0720.N1441.d013704 hm hn seed hseed hseedb).symm
  · exact _root_.GD.N0232.N0720.N1335.d020091 m n hm hn seed hseed hseedb
  · exact hd.2.2.2 _ (_root_.GD.N0232.N0720.N1398.d019599 m n hg) hweak

end
end GD.N0232.N0720.N1335

#print axioms _root_.GD.N0232.N0720.N1335.d020090
#print axioms _root_.GD.N0232.N0720.N1335.d020092
