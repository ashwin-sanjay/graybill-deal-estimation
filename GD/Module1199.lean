



























import GD.Module1191
import GD.Module1163

namespace GD
namespace N0232
namespace N0720
namespace N1480

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1097
open _root_.GD.N0232.N0720.N1096
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1135
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1047
open _root_.GD.N0232.N0719.N0946
open scoped ENNReal


def d019382 (r : ℝ) (hr : 0 < r) : _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨0, r, 1, hr, one_pos⟩


theorem d019383 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    ∃ (g : _root_.GD.N0232.N0719.N0946.d009229) (r : ℝ) (hr : 0 < r),
      _root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1480.d019382 r hr) = θ := by
  obtain ⟨loc, s1, s2, h1, h2⟩ := θ
  refine ⟨⟨loc, Real.log s2⟩, s1 / s2, div_pos h1 h2, ?_⟩
  have hd : (⟨loc, Real.log s2⟩ : _root_.GD.N0232.N0719.N0946.d009229).d009239 = s2 := Real.exp_log h2
  have hs2 := h2.ne'
  unfold _root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1480.d019382
  simp only [_root_.GD.N0232.N0720.N1080.d014168.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hd, mul_zero, add_zero]
  · simp only [hd]
    field_simp
  · simp only [hd, mul_one]



structure d019384 (m n : ℕ) where
  seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n
  descending : ∀ (k : ℕ) (r : ℝ) (hr : 0 < r),
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) (seed (k + 1)).value ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) (seed k).value

variable {m n : ℕ}



theorem d019385 (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q)
    (h : ∀ (r : ℝ) (hr : 0 < r),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) p ≤ _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) q)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ q := by
  obtain ⟨g, r, hr, rfl⟩ := _root_.GD.N0232.N0720.N1480.d019383 θ
  rw [hp g, hq g]
  exact mul_le_mul_left' (h r hr) _


theorem d019386 (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q)
    (h : ∀ (r : ℝ) (hr : 0 < r),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) p < _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) q)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014182 m n θ p < _root_.GD.N0232.N0720.N1080.d014182 m n θ q := by
  obtain ⟨g, r, hr, rfl⟩ := _root_.GD.N0232.N0720.N1480.d019383 θ
  rw [hp g, hq g]
  have hpos : (0 : ℝ) < g.d009239 ^ 2 := by
    have := g.d009240
    positivity
  rw [mul_comm (ENNReal.ofReal (g.d009239 ^ 2)) (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) p),
    mul_comm (ENNReal.ofReal (g.d009239 ^ 2)) (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) q)]
  exact ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr hpos).ne'
    ENNReal.ofReal_ne_top (h r hr)


def d019384.d019387
    (c : _root_.GD.N0232.N0720.N1480.d019384 m n) : _root_.GD.N0232.N0720.N1097.d019167 m n :=
  ⟨c.seed, fun k θ =>
    _root_.GD.N0232.N0720.N1480.d019385 _ _ (c.seed (k + 1)).riskCharacter
      (c.seed k).riskCharacter (c.descending k) θ⟩


def d019388 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) :
    _root_.GD.N0232.N0720.N1480.d019384 m n :=
  ⟨c.seed, fun k r hr => c.descending k (_root_.GD.N0232.N0720.N1480.d019382 r hr)⟩


def d019389 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∀ (r : ℝ) (hr : 0 < r),
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) s <
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)

theorem d019390
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hs : _root_.GD.N0232.N0720.N1159.d014638 m n s) (h : _root_.GD.N0232.N0720.N1480.d019389 hm hn s) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
  fun θ => _root_.GD.N0232.N0720.N1480.d019386 s _ hs
    (_root_.GD.N0232.N0720.N1047.d018647 m n hm hn) h θ


def d019391 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, _root_.GD.N0232.N0720.N1201.d015333 m n (c.seed k) < ε



theorem d019392
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n) :
    _root_.GD.N0232.N0720.N1096.d019226 c ↔ _root_.GD.N0232.N0720.N1480.d019391 c := by
  constructor
  · intro h ε hε
    obtain ⟨k, candidate, hlt⟩ := h ε hε
    exact ⟨k, lt_of_le_of_lt
      (_root_.GD.N0232.N0720.N1135.d018316 (c.seed k) candidate) hlt⟩
  · intro h ε hε
    obtain ⟨k, hk⟩ := h ε hε
    have hδ : 0 < ε - _root_.GD.N0232.N0720.N1201.d015333 m n (c.seed k) := sub_pos.mpr hk
    obtain ⟨candidate, hc⟩ := _root_.GD.N0232.N0720.N1135.d018325 (c.seed k) _ hδ
    exact ⟨k, candidate, by linarith⟩


theorem d019393
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1097.d019167 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        _root_.GD.N0232.N0720.N1480.d019391 c := by
  rw [_root_.GD.N0232.N0720.N1096.d019228 hm hn]
  constructor
  · rintro ⟨c, hs, h⟩
    exact ⟨c, hs, (_root_.GD.N0232.N0720.N1480.d019392 c).1 h⟩
  · rintro ⟨c, hs, h⟩
    exact ⟨c, hs, (_root_.GD.N0232.N0720.N1480.d019392 c).2 h⟩




theorem d019394
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1480.d019384 m n,
        _root_.GD.N0232.N0720.N1480.d019389 hm hn (c.seed 0).value ∧
        _root_.GD.N0232.N0720.N1480.d019391 c.d019387 := by
  constructor
  · intro h
    obtain ⟨c, hs, hgap⟩ :=
      (_root_.GD.N0232.N0720.N1480.d019393 hm hn).1 h
    refine ⟨_root_.GD.N0232.N0720.N1480.d019388 c, fun r hr => hs (_root_.GD.N0232.N0720.N1480.d019382 r hr), ?_⟩
    intro ε hε
    obtain ⟨k, hk⟩ := hgap ε hε
    exact ⟨k, hk⟩
  · rintro ⟨c, hs, hgap⟩
    exact (_root_.GD.N0232.N0720.N1480.d019393 hm hn).2
      ⟨c.d019387,
        _root_.GD.N0232.N0720.N1480.d019390 hm hn _
          (c.seed 0).riskCharacter hs, hgap⟩


def d019395 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) (j : ℕ) : _root_.GD.N0232.N0720.N1097.d019167 m n :=
  ⟨fun k => c.seed (j + k), fun k θ => by
    show _root_.GD.N0232.N0720.N1080.d014182 m n θ (c.seed (j + k + 1)).value ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ (c.seed (j + k)).value
    exact c.descending (j + k) θ⟩


theorem d019396
    (hm : 2 ≤ m) (hn : 2 ≤ n) (c : _root_.GD.N0232.N0720.N1097.d019167 m n) (j : ℕ)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed j).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hgap : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, j ≤ k ∧ _root_.GD.N0232.N0720.N1201.d015333 m n (c.seed k) < ε) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  refine (_root_.GD.N0232.N0720.N1480.d019393 hm hn).2
    ⟨_root_.GD.N0232.N0720.N1480.d019395 c j, fun θ => hs θ, ?_⟩
  intro ε hε
  obtain ⟨k, hjk, hk⟩ := hgap ε hε
  refine ⟨k - j, ?_⟩
  show _root_.GD.N0232.N0720.N1201.d015333 m n (c.seed (j + (k - j))) < ε
  rw [Nat.add_sub_of_le hjk]
  exact hk

#print axioms _root_.GD.N0232.N0720.N1480.d019383
#print axioms _root_.GD.N0232.N0720.N1480.d019386
#print axioms _root_.GD.N0232.N0720.N1480.d019392
#print axioms _root_.GD.N0232.N0720.N1480.d019393
#print axioms _root_.GD.N0232.N0720.N1480.d019394
#print axioms _root_.GD.N0232.N0720.N1480.d019396

end

end N1480
end N0720
end N0232
end GD
