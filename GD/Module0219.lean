import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

























namespace GD
namespace N0232
namespace N0720
namespace N1463

noncomputable section



def d003047 (left right action : ℝ) : ℝ :=
  left * action ^ 2 + right * (action - 1) ^ 2


def d003048 (left right : ℝ) : ℝ :=
  right / (left + right)


theorem d003049
    {left right : ℝ} (hden : left + right ≠ 0) (action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003047 left right action =
      left * right / (left + right) +
        (left + right) *
          (action - _root_.GD.N0232.N0720.N1463.d003048 left right) ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1463.d003047 _root_.GD.N0232.N0720.N1463.d003048
  field_simp [hden]
  ring



theorem d003050
    {left right : ℝ} (hleft : 0 < left) (hright : 0 < right)
    (action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003047 left right
        (_root_.GD.N0232.N0720.N1463.d003048 left right) ≤
      _root_.GD.N0232.N0720.N1463.d003047 left right action := by
  have hsum : 0 < left + right := add_pos hleft hright
  rw [_root_.GD.N0232.N0720.N1463.d003049 hsum.ne' action,
    _root_.GD.N0232.N0720.N1463.d003049 hsum.ne'
      (_root_.GD.N0232.N0720.N1463.d003048 left right)]
  simp [mul_nonneg hsum.le (sq_nonneg
    (action - _root_.GD.N0232.N0720.N1463.d003048 left right))]


theorem d003051
    {left right : ℝ} (hleft : 0 < left) (hright : 0 < right)
    (action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003047 left right action =
        _root_.GD.N0232.N0720.N1463.d003047 left right
          (_root_.GD.N0232.N0720.N1463.d003048 left right) ↔
      action = _root_.GD.N0232.N0720.N1463.d003048 left right := by
  have hsum : 0 < left + right := add_pos hleft hright
  rw [_root_.GD.N0232.N0720.N1463.d003049 hsum.ne' action,
    _root_.GD.N0232.N0720.N1463.d003049 hsum.ne'
      (_root_.GD.N0232.N0720.N1463.d003048 left right)]
  constructor
  · intro h
    have hzero :
        (left + right) *
          (action - _root_.GD.N0232.N0720.N1463.d003048 left right) ^ 2 = 0 := by
      simpa using h
    have hsquare :
        (action - _root_.GD.N0232.N0720.N1463.d003048 left right) ^ 2 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hsum.ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · rintro rfl
    rfl




noncomputable def d003052
    (leftScale rightScale r l action : ℝ) : ℝ :=
  leftScale * (1 - l) ^ r * action ^ 2 +
    rightScale * l ^ r * (action - 1) ^ 2


noncomputable def d003053
    (leftScale rightScale r l : ℝ) : ℝ :=
  rightScale * l ^ r /
    (leftScale * (1 - l) ^ r + rightScale * l ^ r)


theorem d003054
    {l leftScale rightScale : ℝ}
    (hl : l ∈ Set.Ioo (0 : ℝ) 1)
    (hleftScale : 0 < leftScale) (hrightScale : 0 < rightScale)
    (r action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003052 leftScale rightScale r l action =
      (leftScale * (1 - l) ^ r * (rightScale * l ^ r)) /
          (leftScale * (1 - l) ^ r + rightScale * l ^ r) +
        (leftScale * (1 - l) ^ r + rightScale * l ^ r) *
          (action - _root_.GD.N0232.N0720.N1463.d003053
            leftScale rightScale r l) ^ 2 := by
  have hleft : 0 < leftScale * (1 - l) ^ r :=
    mul_pos hleftScale (Real.rpow_pos_of_pos (sub_pos.mpr hl.2) r)
  have hright : 0 < rightScale * l ^ r :=
    mul_pos hrightScale (Real.rpow_pos_of_pos hl.1 r)
  simpa [_root_.GD.N0232.N0720.N1463.d003052, _root_.GD.N0232.N0720.N1463.d003053,
    _root_.GD.N0232.N0720.N1463.d003047, _root_.GD.N0232.N0720.N1463.d003048] using
    (_root_.GD.N0232.N0720.N1463.d003049
      (left := leftScale * (1 - l) ^ r)
      (right := rightScale * l ^ r)
      (add_pos hleft hright).ne' action)



theorem d003055
    {l leftScale rightScale : ℝ}
    (hl : l ∈ Set.Ioo (0 : ℝ) 1)
    (hleftScale : 0 < leftScale) (hrightScale : 0 < rightScale)
    (r action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003052 leftScale rightScale r l action =
        _root_.GD.N0232.N0720.N1463.d003052 leftScale rightScale r l
          (_root_.GD.N0232.N0720.N1463.d003053 leftScale rightScale r l) ↔
      action = _root_.GD.N0232.N0720.N1463.d003053 leftScale rightScale r l := by
  have hleft : 0 < leftScale * (1 - l) ^ r :=
    mul_pos hleftScale (Real.rpow_pos_of_pos (sub_pos.mpr hl.2) r)
  have hright : 0 < rightScale * l ^ r :=
    mul_pos hrightScale (Real.rpow_pos_of_pos hl.1 r)
  simpa [_root_.GD.N0232.N0720.N1463.d003052, _root_.GD.N0232.N0720.N1463.d003053,
    _root_.GD.N0232.N0720.N1463.d003047, _root_.GD.N0232.N0720.N1463.d003048] using
    (_root_.GD.N0232.N0720.N1463.d003051
      (left := leftScale * (1 - l) ^ r)
      (right := rightScale * l ^ r) hleft hright action)



theorem d003056
    {l leftScale rightScale : ℝ}
    (hl : l ∈ Set.Ioo (0 : ℝ) 1)
    (hleftScale : 0 < leftScale) (hrightScale : 0 < rightScale)
    (r action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003052 leftScale rightScale r l action -
        _root_.GD.N0232.N0720.N1463.d003052 leftScale rightScale r l
          (_root_.GD.N0232.N0720.N1463.d003053 leftScale rightScale r l) =
      (leftScale * (1 - l) ^ r + rightScale * l ^ r) *
        (action - _root_.GD.N0232.N0720.N1463.d003053 leftScale rightScale r l) ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1463.d003054 hl hleftScale hrightScale r action,
    _root_.GD.N0232.N0720.N1463.d003054 hl hleftScale hrightScale r
      (_root_.GD.N0232.N0720.N1463.d003053 leftScale rightScale r l)]
  ring




theorem d003057
    {l leftScale rightScale : ℝ}
    (hl : l ∈ Set.Ioo (0 : ℝ) 1)
    (hleftScale : 0 < leftScale) (hrightScale : 0 < rightScale)
    (r : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003053 rightScale leftScale r (1 - l) =
      1 - _root_.GD.N0232.N0720.N1463.d003053 leftScale rightScale r l := by
  unfold _root_.GD.N0232.N0720.N1463.d003053
  have hleft : 0 < leftScale * (1 - l) ^ r :=
    mul_pos hleftScale (Real.rpow_pos_of_pos (sub_pos.mpr hl.2) r)
  have hright : 0 < rightScale * l ^ r :=
    mul_pos hrightScale (Real.rpow_pos_of_pos hl.1 r)
  have hden :
      leftScale * (1 - l) ^ r + rightScale * l ^ r ≠ 0 :=
    (add_pos hleft hright).ne'
  rw [show 1 - (1 - l) = l by ring]
  field_simp [hden]
  ring



theorem d003058
    (leftScale rightScale r l action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003052 rightScale leftScale r (1 - l) (1 - action) =
      _root_.GD.N0232.N0720.N1463.d003052 leftScale rightScale r l action := by
  unfold _root_.GD.N0232.N0720.N1463.d003052
  rw [show 1 - (1 - l) = l by ring]
  ring




noncomputable def d003059 (alpha beta : ℝ) : ℝ :=
  (alpha / beta) ^ alpha * Real.Gamma (alpha + beta) /
    (Real.Gamma alpha * Real.Gamma beta)



noncomputable def d003060 (alpha beta : ℝ) : ℝ :=
  (beta / alpha) ^ beta * Real.Gamma (alpha + beta) /
    (Real.Gamma alpha * Real.Gamma beta)

theorem d003061
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1463.d003059 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1463.d003059
  positivity

theorem d003062
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1463.d003060 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1463.d003060
  positivity


theorem d003063 (alpha beta : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003059 beta alpha = _root_.GD.N0232.N0720.N1463.d003060 alpha beta := by
  simp [_root_.GD.N0232.N0720.N1463.d003059, _root_.GD.N0232.N0720.N1463.d003060, add_comm, mul_comm]

theorem d003064 (alpha beta : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003060 beta alpha = _root_.GD.N0232.N0720.N1463.d003059 alpha beta := by
  simp [_root_.GD.N0232.N0720.N1463.d003059, _root_.GD.N0232.N0720.N1463.d003060, add_comm, mul_comm]




noncomputable def d003065
    (alpha beta l action : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1463.d003052
    (_root_.GD.N0232.N0720.N1463.d003059 alpha beta) (_root_.GD.N0232.N0720.N1463.d003060 alpha beta)
    (alpha + beta) l action


noncomputable def d003066
    (alpha beta l : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1463.d003053
    (_root_.GD.N0232.N0720.N1463.d003059 alpha beta) (_root_.GD.N0232.N0720.N1463.d003060 alpha beta)
    (alpha + beta) l


theorem d003067
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1463.d003066 beta alpha (1 - l) =
      1 - _root_.GD.N0232.N0720.N1463.d003066 alpha beta l := by
  unfold _root_.GD.N0232.N0720.N1463.d003066
  simpa [_root_.GD.N0232.N0720.N1463.d003059, _root_.GD.N0232.N0720.N1463.d003060, add_comm, mul_comm] using
    (_root_.GD.N0232.N0720.N1463.d003057 hl
      (_root_.GD.N0232.N0720.N1463.d003061 halpha hbeta)
      (_root_.GD.N0232.N0720.N1463.d003062 halpha hbeta) (alpha + beta))



theorem d003068
    (alpha beta l action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003065 beta alpha (1 - l) (1 - action) =
      _root_.GD.N0232.N0720.N1463.d003065 alpha beta l action := by
  unfold _root_.GD.N0232.N0720.N1463.d003065
  simpa [_root_.GD.N0232.N0720.N1463.d003059, _root_.GD.N0232.N0720.N1463.d003060, add_comm, mul_comm] using
    (_root_.GD.N0232.N0720.N1463.d003058
      (_root_.GD.N0232.N0720.N1463.d003059 alpha beta) (_root_.GD.N0232.N0720.N1463.d003060 alpha beta)
      (alpha + beta) l action)



noncomputable def d003069
    (r l action : ℝ) : ℝ :=
  (1 - l) ^ r * action ^ 2 + l ^ r * (action - 1) ^ 2


noncomputable def d003070 (r l : ℝ) : ℝ :=
  l ^ r / ((1 - l) ^ r + l ^ r)


theorem d003071 (r l : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003070 r l =
      _root_.GD.N0232.N0720.N1463.d003048 ((1 - l) ^ r) (l ^ r) := by
  rfl



theorem d003072
    {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) (r action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003069 r l action =
      ((1 - l) ^ r * l ^ r) / ((1 - l) ^ r + l ^ r) +
        ((1 - l) ^ r + l ^ r) *
          (action - _root_.GD.N0232.N0720.N1463.d003070 r l) ^ 2 := by
  have hleft : 0 < (1 - l) ^ r :=
    Real.rpow_pos_of_pos (sub_pos.mpr hl.2) r
  have hright : 0 < l ^ r := Real.rpow_pos_of_pos hl.1 r
  simpa [_root_.GD.N0232.N0720.N1463.d003069, _root_.GD.N0232.N0720.N1463.d003070,
    _root_.GD.N0232.N0720.N1463.d003047, _root_.GD.N0232.N0720.N1463.d003048] using
    (_root_.GD.N0232.N0720.N1463.d003049
      (left := (1 - l) ^ r) (right := l ^ r)
      (add_pos hleft hright).ne' action)



theorem d003073
    {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) (r action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003069 r l action =
        _root_.GD.N0232.N0720.N1463.d003069 r l (_root_.GD.N0232.N0720.N1463.d003070 r l) ↔
      action = _root_.GD.N0232.N0720.N1463.d003070 r l := by
  have hleft : 0 < (1 - l) ^ r :=
    Real.rpow_pos_of_pos (sub_pos.mpr hl.2) r
  have hright : 0 < l ^ r := Real.rpow_pos_of_pos hl.1 r
  simpa [_root_.GD.N0232.N0720.N1463.d003069, _root_.GD.N0232.N0720.N1463.d003070,
    _root_.GD.N0232.N0720.N1463.d003047, _root_.GD.N0232.N0720.N1463.d003048] using
    (_root_.GD.N0232.N0720.N1463.d003051
      (left := (1 - l) ^ r) (right := l ^ r)
      hleft hright action)


theorem d003074
    {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) (r : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003070 r (1 - l) = 1 - _root_.GD.N0232.N0720.N1463.d003070 r l := by
  unfold _root_.GD.N0232.N0720.N1463.d003070
  have hleft : 0 < (1 - l) ^ r :=
    Real.rpow_pos_of_pos (sub_pos.mpr hl.2) r
  have hright : 0 < l ^ r := Real.rpow_pos_of_pos hl.1 r
  have hden : (1 - l) ^ r + l ^ r ≠ 0 :=
    (add_pos hleft hright).ne'
  rw [show 1 - (1 - l) = l by ring]
  field_simp [hden]
  ring



@[simp] theorem d003075 (l : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003070 1 l = l := by
  simp [_root_.GD.N0232.N0720.N1463.d003070]




theorem d003076
    (l action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003069 1 l action =
      l * (1 - l) + (action - l) ^ 2 := by
  simp only [_root_.GD.N0232.N0720.N1463.d003069, Real.rpow_one]
  ring



theorem d003077
    (l action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003069 1 l l ≤
      _root_.GD.N0232.N0720.N1463.d003069 1 l action := by
  rw [_root_.GD.N0232.N0720.N1463.d003076, _root_.GD.N0232.N0720.N1463.d003076]
  simpa using
    (le_add_of_nonneg_right (a := l * (1 - l))
      (sq_nonneg (action - l)))



theorem d003078
    (l action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003069 1 l action =
        _root_.GD.N0232.N0720.N1463.d003069 1 l l ↔
      action = l := by
  rw [_root_.GD.N0232.N0720.N1463.d003076, _root_.GD.N0232.N0720.N1463.d003076]
  constructor
  · intro h
    have hz : (action - l) ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · rintro rfl
    rfl



theorem d003079 (l : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003070 2 l =
      l ^ 2 / ((1 - l) ^ 2 + l ^ 2) := by
  norm_num [_root_.GD.N0232.N0720.N1463.d003070]



theorem d003080
    {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1463.d003070 2 l = l ↔ l = 1 / 2 := by
  rw [_root_.GD.N0232.N0720.N1463.d003079]
  have hden : (1 - l) ^ 2 + l ^ 2 ≠ 0 := by
    have hp : 0 < (1 - l) ^ 2 + l ^ 2 := by
      have hsq : 0 < l ^ 2 := sq_pos_of_pos hl.1
      nlinarith [sq_nonneg (1 - l)]
    exact hp.ne'
  constructor
  · intro h
    field_simp [hden] at h
    have hfac : l * (1 - l) * (2 * l - 1) = 0 := by
      nlinarith [h]
    rcases mul_eq_zero.mp hfac with hzero | hlast
    · rcases mul_eq_zero.mp hzero with hl0 | hl1
      · exact False.elim (hl.1.ne' hl0)
      · have hone : l = 1 := by linarith
        exact False.elim (hl.2.ne hone)
    · linarith
  · rintro rfl
    norm_num



theorem d003081
    {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1463.d003069 2 l (_root_.GD.N0232.N0720.N1463.d003070 2 l) <
        _root_.GD.N0232.N0720.N1463.d003069 2 l l ↔
      l ≠ 1 / 2 := by
  constructor
  · intro hlt heq
    have hp : _root_.GD.N0232.N0720.N1463.d003070 2 l = l :=
      (_root_.GD.N0232.N0720.N1463.d003080 hl).2 heq
    rw [hp] at hlt
    exact lt_irrefl _ hlt
  · intro hne
    have hle := _root_.GD.N0232.N0720.N1463.d003050
      (Real.rpow_pos_of_pos (sub_pos.mpr hl.2) 2)
      (Real.rpow_pos_of_pos hl.1 2) l
    have hle' :
        _root_.GD.N0232.N0720.N1463.d003069 2 l (_root_.GD.N0232.N0720.N1463.d003070 2 l) ≤
          _root_.GD.N0232.N0720.N1463.d003069 2 l l := by
      simpa [_root_.GD.N0232.N0720.N1463.d003069, _root_.GD.N0232.N0720.N1463.d003070,
        _root_.GD.N0232.N0720.N1463.d003047, _root_.GD.N0232.N0720.N1463.d003048] using hle
    apply lt_of_le_of_ne hle'
    intro heq
    have haction : l = _root_.GD.N0232.N0720.N1463.d003070 2 l :=
      (_root_.GD.N0232.N0720.N1463.d003073 hl 2 l).mp heq.symm
    exact hne ((_root_.GD.N0232.N0720.N1463.d003080 hl).mp haction.symm)


def d003082 (m : ℕ) : ℝ :=
  ((m - 1 : ℕ) : ℝ) / 2

@[simp] theorem d003083 :
    _root_.GD.N0232.N0720.N1463.d003082 2 = 1 / 2 := by
  norm_num [_root_.GD.N0232.N0720.N1463.d003082]

@[simp] theorem d003084 :
    _root_.GD.N0232.N0720.N1463.d003082 3 = 1 := by
  norm_num [_root_.GD.N0232.N0720.N1463.d003082]



theorem d003085
    {m : ℕ} (hm : 4 ≤ m) :
    1 < _root_.GD.N0232.N0720.N1463.d003082 m := by
  unfold _root_.GD.N0232.N0720.N1463.d003082
  have hsub : 3 ≤ m - 1 := by omega
  have hcast : (3 : ℝ) ≤ (m - 1 : ℕ) := by exact_mod_cast hsub
  linarith




theorem d003086 :
    2 * _root_.GD.N0232.N0720.N1463.d003082 2 = 1 := by
  norm_num [_root_.GD.N0232.N0720.N1463.d003082]



theorem d003087 :
    _root_.GD.N0232.N0720.N1463.d003082 3 - 1 = 0 := by
  norm_num [_root_.GD.N0232.N0720.N1463.d003082]



theorem d003088
    {m : ℕ} (hm : 4 ≤ m) :
    0 < _root_.GD.N0232.N0720.N1463.d003082 m - 1 := by
  linarith [_root_.GD.N0232.N0720.N1463.d003085 hm]



theorem d003089
    {m : ℕ} (hm : 2 ≤ m) :
    _root_.GD.N0232.N0720.N1463.d003082 m < 1 ↔ m = 2 := by
  unfold _root_.GD.N0232.N0720.N1463.d003082
  constructor
  · intro h
    have hc : ((m - 1 : ℕ) : ℝ) < 2 := by linarith
    have hn : m - 1 < 2 := by exact_mod_cast hc
    omega
  · rintro rfl
    norm_num



theorem d003090
    {m : ℕ} (hm : 2 ≤ m) :
    _root_.GD.N0232.N0720.N1463.d003082 m = 1 ↔ m = 3 := by
  unfold _root_.GD.N0232.N0720.N1463.d003082
  constructor
  · intro h
    have hc : ((m - 1 : ℕ) : ℝ) = 2 := by linarith
    have hn : m - 1 = 2 := by exact_mod_cast hc
    omega
  · rintro rfl
    norm_num



theorem d003091
    {m : ℕ} (hm : 2 ≤ m) :
    1 < _root_.GD.N0232.N0720.N1463.d003082 m ↔ 4 ≤ m := by
  constructor
  · intro h
    by_contra hn
    have hcases : m = 2 ∨ m = 3 := by omega
    rcases hcases with rfl | rfl <;>
      norm_num [_root_.GD.N0232.N0720.N1463.d003082] at h
  · intro h4
    exact _root_.GD.N0232.N0720.N1463.d003085 h4

end

end N1463
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1463.d003049
#print axioms _root_.GD.N0232.N0720.N1463.d003051
#print axioms _root_.GD.N0232.N0720.N1463.d003055
#print axioms _root_.GD.N0232.N0720.N1463.d003056
#print axioms _root_.GD.N0232.N0720.N1463.d003057
#print axioms _root_.GD.N0232.N0720.N1463.d003061
#print axioms _root_.GD.N0232.N0720.N1463.d003063
#print axioms _root_.GD.N0232.N0720.N1463.d003067
#print axioms _root_.GD.N0232.N0720.N1463.d003068
#print axioms _root_.GD.N0232.N0720.N1463.d003073
#print axioms _root_.GD.N0232.N0720.N1463.d003074
#print axioms _root_.GD.N0232.N0720.N1463.d003076
#print axioms _root_.GD.N0232.N0720.N1463.d003078
#print axioms _root_.GD.N0232.N0720.N1463.d003080
#print axioms _root_.GD.N0232.N0720.N1463.d003081
#print axioms _root_.GD.N0232.N0720.N1463.d003085
#print axioms _root_.GD.N0232.N0720.N1463.d003089
#print axioms _root_.GD.N0232.N0720.N1463.d003090
#print axioms _root_.GD.N0232.N0720.N1463.d003091
