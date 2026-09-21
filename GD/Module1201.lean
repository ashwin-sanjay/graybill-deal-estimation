



















import GD.Module1200

namespace GD
namespace N0232
namespace N0720
namespace N1086

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1097
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1480
open _root_.GD.N0232.N0720.N1098
open scoped ENNReal


structure d019414 (m n : ℕ) where
  value : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)
  riskCharacter : _root_.GD.N0232.N0720.N1159.d014638 m n value


structure d019415 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) where
  seed : ℕ → _root_.GD.N0232.N0720.N1086.d019414 m n
  descending : ∀ (k : ℕ) (r : ℝ) (hr : 0 < r),
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) (seed (k + 1)).value ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1480.d019382 r hr) (seed k).value
  strict : _root_.GD.N0232.N0720.N1480.d019389 hm hn (seed 0).value

variable {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}

namespace d019415

variable (c : _root_.GD.N0232.N0720.N1086.d019415 m n hm hn)

theorem d019416 (k : ℕ) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ (c.seed (k + 1)).value ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ (c.seed k).value :=
  _root_.GD.N0232.N0720.N1480.d019385 _ _ (c.seed (k + 1)).riskCharacter (c.seed k).riskCharacter
    (c.descending k) θ

theorem d019417 (k : ℕ) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ (c.seed k).value ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ (c.seed 0).value := by
  have hanti : Antitone (fun j => _root_.GD.N0232.N0720.N1080.d014182 m n θ (c.seed j).value) :=
    antitone_nat_of_succ_le (fun j => c.d019416 j θ)
  exact hanti (Nat.zero_le k)

theorem d019418 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
  _root_.GD.N0232.N0720.N1480.d019390 hm hn _ (c.seed 0).riskCharacter c.strict


theorem d019419 (k : ℕ) : _root_.GD.N0232.N0720.N1159.d014637 m n (c.seed k).value :=
  fun θ => ne_top_of_lt (lt_of_le_of_lt (c.d019417 k θ) (c.d019418 θ))


def d019420 (k : ℕ) : _root_.GD.N0232.N0720.N1159.d014639 m n :=
  ⟨(c.seed k).value, c.d019419 k, (c.seed k).riskCharacter⟩

def d019421 : _root_.GD.N0232.N0720.N1480.d019384 m n :=
  ⟨fun k => c.d019420 k, fun k r hr => c.descending k r hr⟩

def d019422 : _root_.GD.N0232.N0720.N1097.d019167 m n :=
  c.d019421.d019387

end d019415


def d019423 (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1086.d019415 m n hm hn :=
  ⟨fun k => ⟨(c.seed k).value, (c.seed k).riskCharacter⟩,
    fun k r hr => c.descending k (_root_.GD.N0232.N0720.N1480.d019382 r hr),
    fun r hr => hs (_root_.GD.N0232.N0720.N1480.d019382 r hr)⟩


theorem d019424
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1086.d019415 m n hm hn, _root_.GD.N0232.N0720.N1098.d019404 c.d019422 = 0 := by
  rw [_root_.GD.N0232.N0720.N1098.d019413 hm hn]
  constructor
  · rintro ⟨c, hs, h⟩
    exact ⟨_root_.GD.N0232.N0720.N1086.d019423 c hs, h⟩
  · rintro ⟨c, h⟩
    exact ⟨c.d019422, c.d019418, h⟩

#print axioms _root_.GD.N0232.N0720.N1086.d019415.d019419
#print axioms _root_.GD.N0232.N0720.N1086.d019424

end

end N1086
end N0720
end N0232
end GD
