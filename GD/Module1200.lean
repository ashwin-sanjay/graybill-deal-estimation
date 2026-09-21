

























import GD.Module1199

open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1098

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1097
open _root_.GD.N0232.N0720.N1096
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1480
open scoped ENNReal

variable {m n : ℕ}


def d019397 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) (k : ℕ) : ℝ := ‖(c.seed k).value‖ ^ 2


def d019398 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) (k : ℕ) : ℝ := _root_.GD.N0232.N0720.N1201.d015333 m n (c.seed k)

theorem d019399 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) (k : ℕ) :
    _root_.GD.N0232.N0720.N1098.d019398 c k = _root_.GD.N0232.N0720.N1098.d019397 c k - ‖c.d019172 k‖ ^ 2 := rfl

theorem d019400 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) (k : ℕ) : 0 ≤ _root_.GD.N0232.N0720.N1098.d019398 c k :=
  _root_.GD.N0232.N0720.N1201.d015334 m n (c.seed k)


theorem d019401 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) : Antitone (_root_.GD.N0232.N0720.N1098.d019397 c) := by
  apply antitone_nat_of_succ_le
  intro k
  have h : ‖(c.seed (k + 1)).value‖ ≤ ‖(c.seed k).value‖ :=
    _root_.GD.N0232.N0720.N1097.d019165 m n (c.descending k _root_.GD.N0232.N0720.N1080.d014169)
      ((c.seed k).finiteRisk _root_.GD.N0232.N0720.N1080.d014169)
  unfold _root_.GD.N0232.N0720.N1098.d019397
  nlinarith [mul_self_le_mul_self (norm_nonneg _) h]


theorem d019402 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) : Antitone (_root_.GD.N0232.N0720.N1098.d019398 c) := by
  apply antitone_nat_of_succ_le
  intro k
  have h1 : _root_.GD.N0232.N0720.N1098.d019397 c (k + 1) ≤ _root_.GD.N0232.N0720.N1098.d019397 c k := _root_.GD.N0232.N0720.N1098.d019401 c (Nat.le_succ k)
  have h2 : ‖c.d019172 k‖ ^ 2 ≤ ‖c.d019172 (k + 1)‖ ^ 2 := c.d019183 (Nat.le_succ k)
  rw [_root_.GD.N0232.N0720.N1098.d019399, _root_.GD.N0232.N0720.N1098.d019399]
  linarith

theorem d019403 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) :
    Tendsto (_root_.GD.N0232.N0720.N1098.d019397 c) atTop (𝓝 (⨅ k, _root_.GD.N0232.N0720.N1098.d019397 c k)) := by
  have hbdd : BddBelow (Set.range (_root_.GD.N0232.N0720.N1098.d019397 c)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    unfold _root_.GD.N0232.N0720.N1098.d019397
    positivity
  exact tendsto_atTop_ciInf (_root_.GD.N0232.N0720.N1098.d019401 c) hbdd


def d019404 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) : ℝ :=
  (⨅ k, _root_.GD.N0232.N0720.N1098.d019397 c k) - ‖c.d019178‖ ^ 2


theorem d019405 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) :
    Tendsto (_root_.GD.N0232.N0720.N1098.d019398 c) atTop (𝓝 (_root_.GD.N0232.N0720.N1098.d019404 c)) := by
  have hfun : _root_.GD.N0232.N0720.N1098.d019398 c = fun k => _root_.GD.N0232.N0720.N1098.d019397 c k - ‖c.d019172 k‖ ^ 2 := funext fun k => _root_.GD.N0232.N0720.N1098.d019399 c k
  rw [hfun]
  exact (_root_.GD.N0232.N0720.N1098.d019403 c).sub c.d019185

theorem d019406 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) : 0 ≤ _root_.GD.N0232.N0720.N1098.d019404 c :=
  ge_of_tendsto' (_root_.GD.N0232.N0720.N1098.d019405 c) (_root_.GD.N0232.N0720.N1098.d019400 c)


theorem d019407 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) :
    ‖c.d019178‖ ^ 2 ≤ ⨅ k, _root_.GD.N0232.N0720.N1098.d019397 c k := by
  have := _root_.GD.N0232.N0720.N1098.d019406 c
  unfold _root_.GD.N0232.N0720.N1098.d019404 at this
  linarith


theorem d019408 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) (k : ℕ) :
    _root_.GD.N0232.N0720.N1098.d019404 c ≤ _root_.GD.N0232.N0720.N1098.d019398 c k :=
  (_root_.GD.N0232.N0720.N1098.d019402 c).le_of_tendsto (_root_.GD.N0232.N0720.N1098.d019405 c) k

theorem d019409 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) :
    Tendsto (_root_.GD.N0232.N0720.N1098.d019398 c) atTop (𝓝 0) ↔ _root_.GD.N0232.N0720.N1098.d019404 c = 0 := by
  constructor
  · intro h
    exact (tendsto_nhds_unique (_root_.GD.N0232.N0720.N1098.d019405 c) h)
  · intro h
    rw [← h]
    exact _root_.GD.N0232.N0720.N1098.d019405 c


theorem d019410 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) :
    _root_.GD.N0232.N0720.N1480.d019391 c ↔ Tendsto (_root_.GD.N0232.N0720.N1098.d019398 c) atTop (𝓝 0) := by
  constructor
  · intro h
    rw [_root_.GD.N0232.N0720.N1098.d019409]
    refine le_antisymm ?_ (_root_.GD.N0232.N0720.N1098.d019406 c)
    by_contra hpos
    push Not at hpos
    obtain ⟨k, hk⟩ := h _ hpos
    exact absurd hk (not_lt.mpr (_root_.GD.N0232.N0720.N1098.d019408 c k))
  · intro h ε hε
    obtain ⟨k, hk⟩ := ((tendsto_order.1 h).2 ε hε).exists
    exact ⟨k, hk⟩

theorem d019411 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) :
    _root_.GD.N0232.N0720.N1480.d019391 c ↔ _root_.GD.N0232.N0720.N1098.d019404 c = 0 :=
  (_root_.GD.N0232.N0720.N1098.d019410 c).trans (_root_.GD.N0232.N0720.N1098.d019409 c)


theorem d019412 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) :
    _root_.GD.N0232.N0720.N1480.d019391 c ↔
      Tendsto (_root_.GD.N0232.N0720.N1098.d019397 c) atTop (𝓝 (‖c.d019178‖ ^ 2)) := by
  rw [_root_.GD.N0232.N0720.N1098.d019411]
  constructor
  · intro h
    have hinf : (⨅ k, _root_.GD.N0232.N0720.N1098.d019397 c k) = ‖c.d019178‖ ^ 2 := by
      unfold _root_.GD.N0232.N0720.N1098.d019404 at h
      linarith
    rw [← hinf]
    exact _root_.GD.N0232.N0720.N1098.d019403 c
  · intro h
    have hinf : (⨅ k, _root_.GD.N0232.N0720.N1098.d019397 c k) = ‖c.d019178‖ ^ 2 :=
      tendsto_nhds_unique (_root_.GD.N0232.N0720.N1098.d019403 c) h
    unfold _root_.GD.N0232.N0720.N1098.d019404
    linarith


theorem d019413
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1097.d019167 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        _root_.GD.N0232.N0720.N1098.d019404 c = 0 := by
  rw [_root_.GD.N0232.N0720.N1480.d019393 hm hn]
  constructor
  · rintro ⟨c, hs, h⟩
    exact ⟨c, hs, (_root_.GD.N0232.N0720.N1098.d019411 c).1 h⟩
  · rintro ⟨c, hs, h⟩
    exact ⟨c, hs, (_root_.GD.N0232.N0720.N1098.d019411 c).2 h⟩

#print axioms _root_.GD.N0232.N0720.N1098.d019402
#print axioms _root_.GD.N0232.N0720.N1098.d019405
#print axioms _root_.GD.N0232.N0720.N1098.d019408
#print axioms _root_.GD.N0232.N0720.N1098.d019410
#print axioms _root_.GD.N0232.N0720.N1098.d019411
#print axioms _root_.GD.N0232.N0720.N1098.d019412
#print axioms _root_.GD.N0232.N0720.N1098.d019413

end

end N1098
end N0720
end N0232
end GD
