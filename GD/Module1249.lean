import GD.Module1236
import GD.Module0943
import GD.Module1248










open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1333

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1332 _root_.GD.N0232.N0720.N1328
open _root_.GD.N0232.N0720.N1287 _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1424
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141

theorem d020201
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) (hh : Measurable h)
    (hgb : ∀ x, g x ∈ Icc (0 : ℝ) 1) (hhb : ∀ x, h x ∈ Icc (0 : ℝ) 1)
    (heq : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] h) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) =
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n h) := by
  let t : _root_.GD.N0232.N0720.N1441.d013676 :=
    ⟨_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂,
      _root_.GD.N0107.d009050 (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos,
      _root_.GD.N0107.d009051 (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos⟩
  rw [_root_.GD.N0232.N0720.N1332.d020109 m n hm hn theta hg hgb,
    _root_.GD.N0232.N0720.N1332.d020109 m n hm hn theta hh hhb,
    _root_.GD.N0232.N0720.N1332.d020108 hm hn heq t]

theorem d020202
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hdesign : m ≠ 2 ∨ n ≠ 2)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g) :
    ¬ (g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n]
      fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) := by
  intro heq
  obtain ⟨sigma, tau, hs, ht, hgap⟩ := _root_.GD.N0232.N0720.N1328.d014770 hm hn hdesign 0
  let theta : _root_.GD.N0232.N0720.N1080.d014168 := ⟨0, sigma, tau, hs, ht⟩
  have hroot_meas : Measurable (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦
      _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) :=
    (_root_.GD.N0232.N0720.N1328.d014757 _ _).comp measurable_fst
  have hroot_bound (x : _root_.GD.N0232.N0720.N1436.d013217) :
      _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 ∈ Icc (0 : ℝ) 1 :=
    _root_.GD.N0232.N0720.N1328.d014758 (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn) x.1
  have hrisk := _root_.GD.N0232.N0720.N1333.d020201 hm hn hg hroot_meas hb hroot_bound heq theta
  have hmem := _root_.GD.N0232.N0720.N1287.d019517 m n hm hn theta
    (fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1)
    hroot_meas hroot_bound
  have hstrict := hd.2.2.1 theta
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n theta (hrep theta), hrisk,
    _root_.GD.N0232.N0720.N1396.d014785 m n theta hmem,
    _root_.GD.N0232.N0720.N1396.d014785 m n theta (_root_.GD.N0232.N0720.N1080.d014177 m n hm hn theta)]
      at hstrict
  have hreal := (ENNReal.ofReal_lt_ofReal_iff').1 hstrict
  exact lt_asymm hreal.1 hgap

theorem d020203 (r : ℝ) :
    _root_.GD.N0232.N0720.N1328.d014755 (1 / 2) (1 / 2) r = _root_.GD.N0232.N0720.N1404.d020183 r := by
  unfold _root_.GD.N0232.N0720.N1328.d014755 _root_.GD.N0232.N0720.N1404.d020183
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ← mul_add]
  exact mul_div_mul_left _ _ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).ne'



theorem d020204
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g) :
    ¬ (g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n]
      fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) := by
  by_cases hdesign : m = 2 ∧ n = 2
  · rcases hdesign with ⟨rfl, rfl⟩
    intro heq
    have hroot : (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦
        _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 2) (_root_.GD.N0232.N0720.N1436.d013208 2) x.1) =
        fun x ↦ _root_.GD.N0232.N0720.N1404.d020183 x.1 := by
      funext x
      simpa only [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, Nat.reduceSub, Nat.cast_one] using
        _root_.GD.N0232.N0720.N1333.d020203 x.1
    rw [hroot] at heq
    have hloss := _root_.GD.N0232.N0720.N1332.d020108 hm hn heq
      _root_.GD.N0232.N0720.N1404.d020198
    have hcap := _root_.GD.N0232.N0720.N1332.d020113 hm hn hd hg hb hrep
      _root_.GD.N0232.N0720.N1404.d020198
    rw [hloss] at hcap
    exact lt_asymm hcap _root_.GD.N0232.N0720.N1404.d020199
  · exact _root_.GD.N0232.N0720.N1333.d020202 hm hn (by tauto) hd hg hb hrep

end
end GD.N0232.N0720.N1333

#print axioms _root_.GD.N0232.N0720.N1333.d020201
#print axioms _root_.GD.N0232.N0720.N1333.d020204
