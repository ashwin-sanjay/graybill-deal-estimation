import GD.Module1193
import GD.Module1198
import GD.Module1176
import GD.Module0940
import GD.Module1212

















open MeasureTheory Set

namespace GD.N0232.N0720.N1342

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0860
open _root_.GD.N0232.N0719.N1010
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1295
open _root_.GD.N0232.N0720.N1467 _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1475
open _root_.GD.N0232.N0720.N1476
open _root_.GD.N0232.N0720.N1209
open _root_.GD.N0232.N0720.N1041
open _root_.GD.N0232.N0720.N1459
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1286
open _root_.GD.N0137 _root_.GD.N0107

variable (m n : ℕ)



theorem d019633
    {d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    (he : Measurable e)
    (hecov : _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦
        g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) e)
    (hae : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d) :
    _root_.GD.N0232.N0720.N1159.d014660 m n e := by
  have hrisk (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta e = _root_.GD.N0232.N0720.N1080.d014197 m n theta d :=
    _root_.GD.N0232.N0720.N1159.d014662 m n theta (hae theta)
  refine ⟨he, hecov, ?_, ?_⟩
  · intro theta
    rw [hrisk]
    exact hd.2.2.1 theta
  · intro f hf hdom theta
    exact (hd.2.2.2 f hf (fun eta ↦ by
      simpa only [hrisk] using hdom eta) theta).trans (hae theta).symm



theorem d019634
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) :
    ∃ q : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable q ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d) ∧
      _root_.GD.N0232.N0719.N0860.d011447 q ∧
      _root_.GD.N0232.N0720.N1209.d012478 q ∧
      _root_.GD.N0232.N0720.N1159.d014660 m n (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) := by
  obtain ⟨hmem, hterminal, hcharacter⟩ := _root_.GD.N0232.N0720.N1295.d019251 m n hd
  have hfinite : _root_.GD.N0232.N0720.N1159.d014637 m n (hmem.toLp d) := by
    intro theta
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n theta d hmem]
    exact ne_top_of_lt (hd.2.2.1 theta)
  let seed : _root_.GD.N0232.N0720.N1159.d014639 m n := ⟨hmem.toLp d, hfinite, hcharacter⟩
  obtain ⟨q, hq, hrep, haffine, hreflect⟩ :=
    _root_.GD.N0232.N0720.N1476.d019379
      m n hm hn seed hterminal
  have hae (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d :=
    (hrep theta).trans
      ((_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq hmem.coeFn_toLp)
  refine ⟨q, hq, hae, haffine, hreflect, ?_⟩
  apply _root_.GD.N0232.N0720.N1342.d019633 m n hd
    (hq.comp (_root_.GD.N0232.N0720.N1501.d016289 m n))
  · intro g omega
    simp only [Function.comp_apply,
      _root_.GD.N0232.N0720.N1475.d018975 m n (by omega) (by omega), _root_.GD.N0232.N0719.N1010.d011416,
      _root_.GD.N0232.N0719.N0946.d009229.d009244]
    exact haffine g.shift g.d009239 g.d009240 (_root_.GD.N0232.N0720.N1467.d012542 m n omega)
  · exact hae



theorem d019635
    (q : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    {omega eta : _root_.GD.N0232.N0720.N1080.d014170 m n}
    (hsummary : _root_.GD.N0232.N0720.N1467.d012542 m n omega = _root_.GD.N0232.N0720.N1467.d012542 m n eta) :
    (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) omega = (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) eta :=
  congrArg q hsummary




theorem d019636
    (q : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (T : _root_.GD.N0232.N0720.N1080.d014170 m n →
      _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hT : ∀ omega, _root_.GD.N0232.N0720.N1467.d012542 m n (T omega) = _root_.GD.N0232.N0720.N1467.d012542 m n omega) :
    (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) ∘ T = q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
  funext omega
  exact _root_.GD.N0232.N0720.N1342.d019635 m n q (hT omega)


theorem d019637 (s : _root_.GD.N0232.N0719.N0900.d009096 2) :
    _root_.GD.N0232.N0720.N1209.d012458 (s.mean 0) (s.mean 1)
      (s.meanVariance 0) (s.meanVariance 1) = s := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;> rfl



theorem d019638
    (q : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (haffine : _root_.GD.N0232.N0719.N0860.d011447 q)
    (hreflect : _root_.GD.N0232.N0720.N1209.d012478 q)
    {xbar ybar vx vy : ℝ} (hsum : vx + vy ≠ 0) :
    q (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy) =
      _root_.GD.N0232.N0720.N1437.d002998
        (_root_.GD.N0232.N0720.N1209.d012471 q) xbar ybar vx vy := by
  by_cases hcontrast : xbar - ybar = 0
  · rw [_root_.GD.N0232.N0720.N1041.d012486
      q haffine hreflect xbar ybar vx vy hcontrast]
    simp only [_root_.GD.N0232.N0720.N1437.d002998,
      hcontrast, zero_mul, add_zero]
  · exact _root_.GD.N0232.N0720.N1209.d012485
      q haffine hreflect hsum hcontrast




theorem d019639
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (q : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (haffine : _root_.GD.N0232.N0719.N0860.d011447 q)
    (hreflect : _root_.GD.N0232.N0720.N1209.d012478 q)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
      _root_.GD.N0232.N0720.N1425.d014719 m n
        (fun p ↦ _root_.GD.N0232.N0720.N1209.d012471 q p.1 p.2) := by
  have hpos := (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
    (_root_.GD.N0232.N0720.N1459.d018933 m n hm hn)
  filter_upwards [hpos] with omega homega
  have hnormal := _root_.GD.N0232.N0720.N1342.d019638 q haffine hreflect
    (xbar := (_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0)
    (ybar := (_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1)
    (vx := (_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
    (vy := (_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1) homega.ne'
  rw [_root_.GD.N0232.N0720.N1342.d019637] at hnormal
  simpa only [Function.comp_apply, _root_.GD.N0232.N0720.N1425.d014719,
    _root_.GD.N0232.N0720.N1467.d012545, _root_.GD.N0232.N0720.N1467.d012546,
    _root_.GD.N0232.N0720.N1467.d012547, _root_.GD.N0232.N0720.N1467.d012548,
    _root_.GD.N0232.N0720.N1084.d014252,
    _root_.GD.N0232.N0720.N1084.d014253] using hnormal





theorem d019640
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) :
    ∃ g : ℝ × ℝ → ℝ, Measurable g ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g := by
  obtain ⟨q, hq, hae, haffine, hreflect, _hterminal⟩ :=
    _root_.GD.N0232.N0720.N1342.d019634 m n hm hn hd
  refine ⟨fun p ↦ _root_.GD.N0232.N0720.N1209.d012471 q p.1 p.2,
    _root_.GD.N0232.N0720.N1209.d012473 q hq, ?_⟩
  intro theta
  exact (hae theta).symm.trans
    (_root_.GD.N0232.N0720.N1342.d019639 m n hm hn q haffine hreflect theta)


theorem d019641
    {d : _root_.GD.N0232.N0720.N1080.d014170 3 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 3 2 d) :
    ∃ g : ℝ × ℝ → ℝ, Measurable g ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 3 2 theta] _root_.GD.N0232.N0720.N1425.d014719 3 2 g :=
  _root_.GD.N0232.N0720.N1342.d019640 3 2 (by omega) (by omega) hd




theorem d019642
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) :
    ∃ g : ℝ × ℝ → ℝ, Measurable g ∧
      (∀ p, g p ∈ Icc (0 : ℝ) 1) ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g := by
  obtain ⟨g, hg, hae⟩ := _root_.GD.N0232.N0720.N1342.d019640 m n hm hn hd
  have hclipMeas : Measurable (_root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1286.d019582 g)) :=
    _root_.GD.N0232.N0720.N1398.d019599 m n
      (_root_.GD.N0232.N0720.N1286.d019583 hg)
  have hdom (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1286.d019582 g)) ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
    have hrisk := _root_.GD.N0232.N0720.N1159.d014662 m n theta (hae theta)
    have hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≠ ⊤ := by
      rw [← hrisk]
      exact ne_top_of_lt (hd.2.2.1 theta)
    rw [hrisk]
    exact _root_.GD.N0232.N0720.N1398.d019600
      m n hm hn theta hg hfinite
  refine ⟨_root_.GD.N0232.N0720.N1286.d019582 g,
    _root_.GD.N0232.N0720.N1286.d019583 hg,
    _root_.GD.N0232.N0720.N1286.d019584 g, ?_⟩
  intro theta
  exact (hd.2.2.2 _ hclipMeas hdom theta).symm



theorem d019643
    {g : ℝ × ℝ → ℝ} (hg : ∀ p, g p ∈ Icc (0 : ℝ) 1)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1425.d014719 m n g omega ∈
      Icc (min (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2))
        (max (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)) := by
  unfold _root_.GD.N0232.N0720.N1425.d014719 _root_.GD.N0232.N0720.N1437.d002998
  have hb := hg
    (_root_.GD.N0232.N0720.N1437.d002996
      (_root_.GD.N0232.N0720.N1084.d014252 m n omega)
      (_root_.GD.N0232.N0720.N1084.d014253 m n omega),
     _root_.GD.N0232.N0720.N1437.d002997
      (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
      (_root_.GD.N0232.N0720.N1084.d014252 m n omega)
      (_root_.GD.N0232.N0720.N1084.d014253 m n omega))
  rcases le_total (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2) with hxy | hyx
  · rw [min_eq_left hxy, max_eq_right hxy]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hb.1,
      mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hb.2)]
  · rw [min_eq_right hyx, max_eq_left hyx]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hyx) hb.1,
      mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr hb.2)]


theorem d019644
    {d : _root_.GD.N0232.N0720.N1080.d014170 3 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 3 2 d) :
    ∃ g : ℝ × ℝ → ℝ, Measurable g ∧
      (∀ p, g p ∈ Icc (0 : ℝ) 1) ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 3 2 theta] _root_.GD.N0232.N0720.N1425.d014719 3 2 g :=
  _root_.GD.N0232.N0720.N1342.d019642 3 2 (by omega) (by omega) hd

end
end GD.N0232.N0720.N1342

#print axioms _root_.GD.N0232.N0720.N1342.d019634
#print axioms _root_.GD.N0232.N0720.N1342.d019636
#print axioms _root_.GD.N0232.N0720.N1342.d019640
#print axioms _root_.GD.N0232.N0720.N1342.d019641
#print axioms _root_.GD.N0232.N0720.N1342.d019642
#print axioms _root_.GD.N0232.N0720.N1342.d019643
#print axioms _root_.GD.N0232.N0720.N1342.d019644
