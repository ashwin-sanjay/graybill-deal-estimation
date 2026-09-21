import GD.Module1194
import GD.Module1211
import GD.Module0944















open MeasureTheory Filter Set
open scoped ENNReal

namespace GD.N0232.N0720.N1398

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1295 _root_.GD.N0232.N0720.N1411
open _root_.GD.N0232.N0720.N1286 _root_.GD.N0232.N0720.N1287
open _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1437 _root_.GD.N0232.N0720.N1424
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1456
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141

theorem d019599 (m n : ℕ)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) :
    Measurable (_root_.GD.N0232.N0720.N1425.d014719 m n g) := by
  unfold _root_.GD.N0232.N0720.N1425.d014719 _root_.GD.N0232.N0720.N1437.d002998
    _root_.GD.N0232.N0720.N1437.d002996 _root_.GD.N0232.N0720.N1437.d002997
    _root_.GD.N0232.N0720.N1084.d014252
    _root_.GD.N0232.N0720.N1084.d014253
  fun_prop


theorem d019600
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≠ ⊤) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1286.d019582 g)) ≤
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) := by
  have hmem := _root_.GD.N0232.N0720.N1396.d014784 m n theta
    (_root_.GD.N0232.N0720.N1398.d019599 m n hg) hfinite
  have hclip := _root_.GD.N0232.N0720.N1287.d019517 m n hm hn theta
    (_root_.GD.N0232.N0720.N1286.d019582 g) (_root_.GD.N0232.N0720.N1286.d019583 hg)
    (_root_.GD.N0232.N0720.N1286.d019584 g)
  rw [_root_.GD.N0232.N0720.N1396.d014785 m n theta hclip,
    _root_.GD.N0232.N0720.N1396.d014785 m n theta hmem]
  exact ENNReal.ofReal_le_ofReal
    (_root_.GD.N0232.N0720.N1286.d019585 m n hm hn theta g hg hmem)


def d019601 (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) : _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  _root_.GD.N0232.N0720.N1286.d019582 (_root_.GD.N0232.N0720.N1411.d019271 d)

theorem d019602 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : Measurable d) : Measurable (_root_.GD.N0232.N0720.N1398.d019601 d) :=
  _root_.GD.N0232.N0720.N1286.d019583 (_root_.GD.N0232.N0720.N1411.d019272 hd)

theorem d019603 (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ)
    (x : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0232.N0720.N1398.d019601 d x ∈ Icc (0 : ℝ) 1 :=
  _root_.GD.N0232.N0720.N1286.d019584 (_root_.GD.N0232.N0720.N1411.d019271 d) x

theorem d019604 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 theta] _root_.GD.N0232.N0720.N1425.d014719 2 2 (_root_.GD.N0232.N0720.N1411.d019271 d) := by
  filter_upwards [_root_.GD.N0232.N0720.N1411.d019274 hd theta] with omega homega
  change d omega = _root_.GD.N0232.N0720.N1437.d002998
    (fun r s ↦ _root_.GD.N0232.N0720.N1411.d019271 d (r, s))
    (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
    (_root_.GD.N0107.d009085 omega.1 / (2 : ℝ))
    (_root_.GD.N0107.d009085 omega.2 / (2 : ℝ))
  exact homega


theorem d019605 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 2 2 theta (_root_.GD.N0232.N0720.N1425.d014719 2 2 (_root_.GD.N0232.N0720.N1398.d019601 d)) ≤
      _root_.GD.N0232.N0720.N1080.d014197 2 2 theta d := by
  have hrisk := _root_.GD.N0232.N0720.N1159.d014662 2 2 theta
    (_root_.GD.N0232.N0720.N1398.d019604 hd theta)
  have hfinite : _root_.GD.N0232.N0720.N1080.d014197 2 2 theta
      (_root_.GD.N0232.N0720.N1425.d014719 2 2 (_root_.GD.N0232.N0720.N1411.d019271 d)) ≠ ⊤ := by
    rw [← hrisk]
    exact ne_top_of_lt (hd.2.2.1 theta)
  rw [hrisk]
  exact _root_.GD.N0232.N0720.N1398.d019600 2 2 (by omega) (by omega) theta
    (_root_.GD.N0232.N0720.N1411.d019272 hd.1) hfinite


theorem d019606 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 theta] _root_.GD.N0232.N0720.N1425.d014719 2 2 (_root_.GD.N0232.N0720.N1398.d019601 d) := by
  exact (hd.2.2.2 _
    (_root_.GD.N0232.N0720.N1398.d019599 2 2 (_root_.GD.N0232.N0720.N1398.d019602 hd.1))
    (_root_.GD.N0232.N0720.N1398.d019605 hd) theta).symm



theorem d019607 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : Measurable d) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 2 2 (_root_.GD.N0232.N0720.N1398.d019601 d) omega -
      theta.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) :=
  _root_.GD.N0232.N0720.N1287.d019517 2 2 (by omega) (by omega) theta
    (_root_.GD.N0232.N0720.N1398.d019601 d) (_root_.GD.N0232.N0720.N1398.d019602 hd)
    (_root_.GD.N0232.N0720.N1398.d019603 d)

theorem d019608 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : Measurable d) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    MemLp (_root_.GD.N0232.N0720.N1398.d019601 d) 2 (_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) := by
  letI := _root_.GD.N0232.N0720.N1434.d013564 (m := 2) (n := 2)
    (by omega) (by omega) t.2.1 t.2.2
  exact memLp_of_bounded (Filter.Eventually.of_forall (_root_.GD.N0232.N0720.N1398.d019603 d))
    (_root_.GD.N0232.N0720.N1398.d019602 hd).aestronglyMeasurable 2

theorem d019609 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : Measurable d) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Integrable (fun x ↦ (_root_.GD.N0232.N0720.N1398.d019601 d x - t.1) ^ 2)
      (_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) :=
  _root_.GD.N0232.N0720.N1287.d019523 2 2 (by omega) (by omega) t
    (_root_.GD.N0232.N0720.N1398.d019601 d) (_root_.GD.N0232.N0720.N1398.d019602 hd)
    (_root_.GD.N0232.N0720.N1398.d019603 d)



def d019610 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (g x - t) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t

theorem d019611 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (t : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1398.d019610 g t := integral_nonneg (fun _ ↦ sq_nonneg _)

theorem d019612
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1080.d014197 2 2 theta (_root_.GD.N0232.N0720.N1425.d014719 2 2 g) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta)
          (_root_.GD.N0107.d012732 2 2 theta.location
            (_root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂)) +
          _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ *
            _root_.GD.N0232.N0720.N1398.d019610 g (_root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂)) := by
  rw [_root_.GD.N0232.N0720.N1396.d014785 2 2 theta
    (_root_.GD.N0232.N0720.N1287.d019517 2 2 (by omega) (by omega) theta g hg hb)]
  congr 1
  exact _root_.GD.N0232.N0720.N1425.d014726
    2 2 (by omega) (by omega) theta.location theta.scale₁ theta.scale₂
    theta.scale₁_pos theta.scale₂_pos g hg (B := 1) (by norm_num)
    (fun x ↦ by rw [abs_of_nonneg (hb x).1]; exact (hb x).2)


theorem d019613 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 2 2 theta d =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta)
          (_root_.GD.N0107.d012732 2 2 theta.location
            (_root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂)) +
          _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ *
            _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d)
              (_root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂)) := by
  rw [_root_.GD.N0232.N0720.N1159.d014662 2 2 theta (_root_.GD.N0232.N0720.N1398.d019606 hd theta)]
  exact _root_.GD.N0232.N0720.N1398.d019612 theta
    (_root_.GD.N0232.N0720.N1398.d019602 hd.1) (_root_.GD.N0232.N0720.N1398.d019603 d)


def d019614 (t : _root_.GD.N0232.N0720.N1441.d013676) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 0
  scale₁ := _root_.GD.N0232.N0720.N1424.d014846 2 t.1
  scale₂ := _root_.GD.N0232.N0720.N1424.d014847 2 t.1
  scale₁_pos := _root_.GD.N0232.N0720.N1424.d014848 (by omega) t.2.2
  scale₂_pos := _root_.GD.N0232.N0720.N1424.d014849 (by omega) t.2.1

theorem d019615 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0107.d009045 2 2 (_root_.GD.N0232.N0720.N1398.d019614 t).scale₁ (_root_.GD.N0232.N0720.N1398.d019614 t).scale₂ = 1 :=
  _root_.GD.N0232.N0720.N1424.d014852 (by omega) (by omega) t.2.1 t.2.2

theorem d019616 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0107.d009046 2 2
      (_root_.GD.N0232.N0720.N1398.d019614 t).scale₁ (_root_.GD.N0232.N0720.N1398.d019614 t).scale₂ = t.1 :=
  _root_.GD.N0232.N0720.N1424.d014853 (by omega) (by omega) t.2.1 t.2.2



theorem d019617 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) t.1 <
      _root_.GD.N0232.N0720.N1398.d019610 _root_.GD.N0232.N0720.N1424.d014839 t.1 := by
  have h := hd.2.2.1 (_root_.GD.N0232.N0720.N1398.d019614 t)
  rw [_root_.GD.N0232.N0720.N1398.d019613 hd,
    _root_.GD.N0232.N0720.N1080.d014199 2 2 (by omega) (by omega),
    _root_.GD.N0232.N0720.N1287.d019529 2 2 (by omega) (by omega)] at h
  change ENNReal.ofReal (_ + _ * _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) _) <
    ENNReal.ofReal (_ + _ * _root_.GD.N0232.N0720.N1398.d019610 _root_.GD.N0232.N0720.N1424.d014839 _) at h
  rw [_root_.GD.N0232.N0720.N1398.d019615, _root_.GD.N0232.N0720.N1398.d019616, one_mul] at h
  have hreal := (ENNReal.ofReal_lt_ofReal_iff').1 h
  linarith [hreal.1]


theorem d019618 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1441.d013705 2 2 t (_root_.GD.N0232.N0720.N1398.d019601 d) <
      _root_.GD.N0232.N0720.N1441.d013705 2 2 t _root_.GD.N0232.N0720.N1424.d014839 := by
  rw [_root_.GD.N0232.N0720.N1287.d019525 2 2 t _ (_root_.GD.N0232.N0720.N1398.d019609 hd.1 t),
    _root_.GD.N0232.N0720.N1287.d019525 2 2 t _
      (_root_.GD.N0232.N0720.N1287.d019524 2 2 (by omega) (by omega) t)]
  apply (ENNReal.ofReal_lt_ofReal_iff').2
  exact ⟨_root_.GD.N0232.N0720.N1398.d019617 hd t,
    (_root_.GD.N0232.N0720.N1398.d019611 _ _).trans_lt (_root_.GD.N0232.N0720.N1398.d019617 hd t)⟩


theorem d019619 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hdom : ∀ t : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0232.N0720.N1398.d019610 g t.1 ≤
      _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) t.1) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 2 2 theta (_root_.GD.N0232.N0720.N1425.d014719 2 2 g) ≤
      _root_.GD.N0232.N0720.N1080.d014197 2 2 theta d := by
  let t : _root_.GD.N0232.N0720.N1441.d013676 :=
    ⟨_root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂,
      _root_.GD.N0107.d009050 (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos,
      _root_.GD.N0107.d009051 (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos⟩
  rw [_root_.GD.N0232.N0720.N1398.d019612 theta hg hb,
    _root_.GD.N0232.N0720.N1398.d019613 hd theta]
  exact ENNReal.ofReal_le_ofReal (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (hdom t)
      (_root_.GD.N0107.d009049 (m := 2) (n := 2)
        (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos).le))



theorem d019620 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hdom : ∀ t : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0232.N0720.N1398.d019610 g t.1 ≤
      _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) t.1) :
    ∀ t : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0232.N0720.N1398.d019610 g t.1 =
      _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) t.1 := by
  have hae := hd.2.2.2 _ (_root_.GD.N0232.N0720.N1398.d019599 2 2 hg)
    (_root_.GD.N0232.N0720.N1398.d019619 hd hg hb hdom)
  intro t
  have h := _root_.GD.N0232.N0720.N1159.d014662 2 2 (_root_.GD.N0232.N0720.N1398.d019614 t) (hae (_root_.GD.N0232.N0720.N1398.d019614 t))
  rw [_root_.GD.N0232.N0720.N1398.d019612 _ hg hb,
    _root_.GD.N0232.N0720.N1398.d019613 hd,
    _root_.GD.N0232.N0720.N1398.d019615, _root_.GD.N0232.N0720.N1398.d019616, one_mul] at h
  simp only [one_mul] at h
  have hnonneg (q : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
      0 ≤ _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 (_root_.GD.N0232.N0720.N1398.d019614 t))
          (_root_.GD.N0107.d012732 2 2 (_root_.GD.N0232.N0720.N1398.d019614 t).location t.1) + _root_.GD.N0232.N0720.N1398.d019610 q t.1 :=
    add_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _)) (_root_.GD.N0232.N0720.N1398.d019611 q t.1)
  have hreal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (hnonneg g),
    ENNReal.toReal_ofReal (hnonneg (_root_.GD.N0232.N0720.N1398.d019601 d))] at hreal
  linarith

end
end GD.N0232.N0720.N1398

#print axioms _root_.GD.N0232.N0720.N1398.d019600
#print axioms _root_.GD.N0232.N0720.N1398.d019606
#print axioms _root_.GD.N0232.N0720.N1398.d019608
#print axioms _root_.GD.N0232.N0720.N1398.d019613
#print axioms _root_.GD.N0232.N0720.N1398.d019618
#print axioms _root_.GD.N0232.N0720.N1398.d019620
