import GD.Module1212










open MeasureTheory Filter Set

namespace GD.N0232.N0720.N1274

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1287
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441

def d019626 (g h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  (g x + h x) / 2

theorem d019627 {g h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hh : Measurable h) : Measurable (_root_.GD.N0232.N0720.N1274.d019626 g h) :=
  (hg.add hh).div_const 2

theorem d019628 {g h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : ∀ x, g x ∈ Icc (0 : ℝ) 1) (hh : ∀ x, h x ∈ Icc (0 : ℝ) 1)
    (x : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0232.N0720.N1274.d019626 g h x ∈ Icc (0 : ℝ) 1 := by
  constructor <;> unfold _root_.GD.N0232.N0720.N1274.d019626 <;>
    linarith [(hg x).1, (hg x).2, (hh x).1, (hh x).2]

theorem d019629 (t : _root_.GD.N0232.N0720.N1441.d013676)
    {g h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) (hh : Measurable h)
    (hgb : ∀ x, g x ∈ Icc (0 : ℝ) 1) (hhb : ∀ x, h x ∈ Icc (0 : ℝ) 1) :
    Integrable (fun x ↦ (g x - h x) ^ 2) (_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) := by
  letI := _root_.GD.N0232.N0720.N1434.d013564 (m := 2) (n := 2)
    (by omega) (by omega) t.2.1 t.2.2
  have hg2 : MemLp g 2 (_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) :=
    memLp_of_bounded (Filter.Eventually.of_forall hgb) hg.aestronglyMeasurable 2
  have hh2 : MemLp h 2 (_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) :=
    memLp_of_bounded (Filter.Eventually.of_forall hhb) hh.aestronglyMeasurable 2
  exact (hg2.sub hh2).integrable_sq


theorem d019630 (t : _root_.GD.N0232.N0720.N1441.d013676)
    {g h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) (hh : Measurable h)
    (hgb : ∀ x, g x ∈ Icc (0 : ℝ) 1) (hhb : ∀ x, h x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1274.d019626 g h) t.1 +
        (1 / 4 : ℝ) * ∫ x, (g x - h x) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1 =
      (_root_.GD.N0232.N0720.N1398.d019610 g t.1 + _root_.GD.N0232.N0720.N1398.d019610 h t.1) / 2 := by
  have hgI := _root_.GD.N0232.N0720.N1287.d019523 2 2 (by omega) (by omega) t g hg hgb
  have hhI := _root_.GD.N0232.N0720.N1287.d019523 2 2 (by omega) (by omega) t h hh hhb
  have hmI := _root_.GD.N0232.N0720.N1287.d019523 2 2 (by omega) (by omega) t
    (_root_.GD.N0232.N0720.N1274.d019626 g h) (_root_.GD.N0232.N0720.N1274.d019627 hg hh)
    (_root_.GD.N0232.N0720.N1274.d019628 hgb hhb)
  have hgap := _root_.GD.N0232.N0720.N1274.d019629 t hg hh hgb hhb
  have hpoint :
      (fun x ↦ (_root_.GD.N0232.N0720.N1274.d019626 g h x - t.1) ^ 2 +
        (1 / 4 : ℝ) * (g x - h x) ^ 2) =
      (fun x ↦ ((g x - t.1) ^ 2 + (h x - t.1) ^ 2) / 2) := by
    funext x
    unfold _root_.GD.N0232.N0720.N1274.d019626
    ring
  have hi := congrArg (fun f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ ↦
    ∫ x, f x ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) hpoint
  rw [integral_add hmI (hgap.const_mul (1 / 4)), integral_const_mul,
    integral_div, integral_add hgI hhI] at hi
  exact hi



theorem d019631 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hgb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hdom : ∀ t : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0232.N0720.N1398.d019610 g t.1 ≤
      _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) t.1) :
    g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] _root_.GD.N0232.N0720.N1398.d019601 d := by
  let h := _root_.GD.N0232.N0720.N1398.d019601 d
  have hh : Measurable h := _root_.GD.N0232.N0720.N1398.d019602 hd.1
  have hhb : ∀ x, h x ∈ Icc (0 : ℝ) 1 := _root_.GD.N0232.N0720.N1398.d019603 d
  have heq := _root_.GD.N0232.N0720.N1398.d019620 hd hg hgb hdom
  have hmidDom : ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1274.d019626 g h) t.1 ≤ _root_.GD.N0232.N0720.N1398.d019610 h t.1 := by
    intro t
    have htax := _root_.GD.N0232.N0720.N1274.d019630 t hg hh hgb hhb
    have hgap : 0 ≤ ∫ x, (g x - h x) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1 :=
      integral_nonneg (fun _ ↦ sq_nonneg _)
    have hle := hdom t
    change _root_.GD.N0232.N0720.N1398.d019610 g t.1 ≤ _root_.GD.N0232.N0720.N1398.d019610 h t.1 at hle
    linarith
  have hmideq := _root_.GD.N0232.N0720.N1398.d019620 hd
    (_root_.GD.N0232.N0720.N1274.d019627 hg hh) (_root_.GD.N0232.N0720.N1274.d019628 hgb hhb) hmidDom
  have htax := _root_.GD.N0232.N0720.N1274.d019630 _root_.GD.N0232.N0720.N1441.d013677 hg hh hgb hhb
  have hgeq := heq _root_.GD.N0232.N0720.N1441.d013677
  have hmeq := hmideq _root_.GD.N0232.N0720.N1441.d013677
  change _root_.GD.N0232.N0720.N1398.d019610 g _root_.GD.N0232.N0720.N1441.d013677.1 = _root_.GD.N0232.N0720.N1398.d019610 h _root_.GD.N0232.N0720.N1441.d013677.1 at hgeq
  change _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1274.d019626 g h) _root_.GD.N0232.N0720.N1441.d013677.1 =
    _root_.GD.N0232.N0720.N1398.d019610 h _root_.GD.N0232.N0720.N1441.d013677.1 at hmeq
  have hzero : (∫ x, (g x - h x) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 _root_.GD.N0232.N0720.N1441.d013677.1) = 0 := by
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x ↦ sq_nonneg (g x - h x))
    (_root_.GD.N0232.N0720.N1274.d019629 _root_.GD.N0232.N0720.N1441.d013677 hg hh hgb hhb)).1 hzero
  change g =ᵐ[_root_.GD.N0232.N0720.N1436.d013289 2 2 _root_.GD.N0232.N0720.N1441.d013677.1] h
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)


theorem d019632 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hgb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hdom : ∀ t : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0232.N0720.N1441.d013705 2 2 t g ≤
      _root_.GD.N0232.N0720.N1441.d013705 2 2 t (_root_.GD.N0232.N0720.N1398.d019601 d)) :
    g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] _root_.GD.N0232.N0720.N1398.d019601 d := by
  apply _root_.GD.N0232.N0720.N1274.d019631 hd hg hgb
  intro t
  have h := hdom t
  rw [_root_.GD.N0232.N0720.N1287.d019525 2 2 t g
      (_root_.GD.N0232.N0720.N1287.d019523 2 2 (by omega) (by omega) t g hg hgb),
    _root_.GD.N0232.N0720.N1287.d019525 2 2 t _ (_root_.GD.N0232.N0720.N1398.d019609 hd.1 t)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (_root_.GD.N0232.N0720.N1398.d019611 _ _)).1 h

end
end GD.N0232.N0720.N1274

#print axioms _root_.GD.N0232.N0720.N1274.d019630
#print axioms _root_.GD.N0232.N0720.N1274.d019631
#print axioms _root_.GD.N0232.N0720.N1274.d019632
