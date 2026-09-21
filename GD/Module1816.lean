import GD.Module1814

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0248

open Set Polynomial

noncomputable section

theorem d030093 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ S : Finset ℝ,
      S.Nonempty ∧ S.card ≤ 3 ∧
      (∀ u, u ∈ S ↔ (_root_.GD.N0005.N0248.d030073 m n a b x y).eval u = 0) ∧
      (∀ u ∈ S, u ∈ Icc (min x y) (max x y)) ∧
      ∀ u : ℝ,
        (∀ v : ℝ, _root_.GD.N0005.N0248.d030071 m n a b x y v ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u) ↔
          u ∈ S ∧ ∀ v ∈ S,
            _root_.GD.N0005.N0248.d030087 m n a b x y u ≤ _root_.GD.N0005.N0248.d030087 m n a b x y v := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨S, hcard, hS⟩ := _root_.GD.N0005.N0248.d030082 hmR hnR ha hb (x := x) (y := y)
  obtain ⟨u₀, _, hu₀⟩ := _root_.GD.N0005.N0248.d030085 hmR.le hnR.le ha hb (x := x) (y := y)
  have hu₀S : u₀ ∈ S := (hS u₀).2 (_root_.GD.N0005.N0248.d030086 hu₀)
  refine ⟨S, ⟨u₀, hu₀S⟩, hcard, ?_, ?_, ?_⟩
  · intro u
    exact (hS u).trans (_root_.GD.N0005.N0248.d030080 ha hb)
  · intro u hu
    exact _root_.GD.N0005.N0248.d030081 hmR hnR ha hb ((hS u).1 hu)
  · intro u
    constructor
    · intro hu
      refine ⟨(hS u).2 (_root_.GD.N0005.N0248.d030086 hu), ?_⟩
      intro v _
      exact (_root_.GD.N0005.N0248.d030090 m n ha hb x y v u).1 (hu v)
    · rintro ⟨_, hu⟩ v
      apply (hu₀ v).trans
      exact (_root_.GD.N0005.N0248.d030090 m n ha hb x y u₀ u).2 (hu u₀ hu₀S)

theorem d030094 {m n a b x u : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) :
    deriv (_root_.GD.N0005.N0248.d030071 m n a b x x) u = 0 ↔ u = x := by
  constructor
  · intro hu
    have := _root_.GD.N0005.N0248.d030081 hm hn ha hb hu
    simp only [min_self, max_self, mem_Icc] at this
    exact le_antisymm this.2 this.1
  · rintro rfl
    rw [_root_.GD.N0005.N0248.d030080 ha hb, _root_.GD.N0005.N0248.d030075]
    simp [_root_.GD.N0005.N0248.d030072]

theorem d030095 {m n a b x u : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) :
    (∀ v : ℝ, _root_.GD.N0005.N0248.d030071 m n a b x x v ≤ _root_.GD.N0005.N0248.d030071 m n a b x x u) ↔ u = x := by
  constructor
  · intro hu
    exact (_root_.GD.N0005.N0248.d030094 hm hn ha hb).1 (_root_.GD.N0005.N0248.d030086 hu)
  · intro hux
    subst u
    obtain ⟨u, hu, hmax⟩ := _root_.GD.N0005.N0248.d030085 hm.le hn.le ha hb (x := x) (y := x)
    have hux : u = x := by
      simp only [min_self, max_self, mem_Icc] at hu
      exact le_antisymm hu.2 hu.1
    simpa only [hux] using hmax

theorem d030096 (k a d u : ℝ) :
    _root_.GD.N0005.N0248.d030072 k k a a (-d) d u = 2*k*u*(u^2+a-d^2) := by
  dsimp [_root_.GD.N0005.N0248.d030072, _root_.GD.N0005.N0248.d030070]
  ring

theorem d030097 (a d u : ℝ) :
    _root_.GD.N0005.N0248.d030087 1 1 a a (-d) d u = (u^2+a-d^2)^2 + 4*a*d^2 := by
  dsimp [_root_.GD.N0005.N0248.d030087, _root_.GD.N0005.N0248.d030070]
  ring

theorem d030098 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y u v : ℝ) :
    _root_.GD.N0005.N0248.d030071 1 1 a b x y u ≤ _root_.GD.N0005.N0248.d030071 1 1 a b x y v ↔
      _root_.GD.N0005.N0248.d030087 1 1 a b x y v ≤ _root_.GD.N0005.N0248.d030087 1 1 a b x y u := by
  simpa only [Nat.cast_one] using _root_.GD.N0005.N0248.d030090 1 1 ha hb x y u v

theorem d030099 {k a d u : ℝ} (hk : 0 < k) (ha : 0 < a) :
    deriv (_root_.GD.N0005.N0248.d030071 k k a a (-d) d) u = 0 ↔ u = 0 ∨ u^2 = d^2-a := by
  rw [_root_.GD.N0005.N0248.d030080 ha ha, _root_.GD.N0005.N0248.d030075, _root_.GD.N0005.N0248.d030096]
  have hk0 := hk.ne'
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, hk0, false_or]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)

theorem d030100 {a d u : ℝ} (ha : 0 < a) (hd : a < d^2) :
    (∀ v : ℝ, _root_.GD.N0005.N0248.d030071 1 1 a a (-d) d v ≤ _root_.GD.N0005.N0248.d030071 1 1 a a (-d) d u) ↔
      u^2 = d^2-a := by
  have hs : (Real.sqrt (d^2-a))^2 = d^2-a := Real.sq_sqrt (sub_pos.2 hd).le
  constructor
  · intro hu
    have h := (_root_.GD.N0005.N0248.d030098 ha ha (-d) d
      (Real.sqrt (d^2-a)) u).1 (hu (Real.sqrt (d^2-a)))
    rw [_root_.GD.N0005.N0248.d030097, _root_.GD.N0005.N0248.d030097] at h
    nlinarith [sq_nonneg (u^2+a-d^2)]
  · intro hu v
    apply (_root_.GD.N0005.N0248.d030098 ha ha (-d) d v u).2
    rw [_root_.GD.N0005.N0248.d030097, _root_.GD.N0005.N0248.d030097]
    nlinarith [sq_nonneg (v^2+a-d^2)]

theorem d030101 {a d u : ℝ} (ha : 0 < a) (hd : d^2 ≤ a) :
    (∀ v : ℝ, _root_.GD.N0005.N0248.d030071 1 1 a a (-d) d v ≤ _root_.GD.N0005.N0248.d030071 1 1 a a (-d) d u) ↔
      u = 0 := by
  constructor
  · intro hu
    have h := (_root_.GD.N0005.N0248.d030098 ha ha (-d) d 0 u).1 (hu 0)
    rw [_root_.GD.N0005.N0248.d030097, _root_.GD.N0005.N0248.d030097] at h
    have hpos : 0 ≤ u^2*(a-d^2) := mul_nonneg (sq_nonneg u) (sub_nonneg.2 hd)
    have hu2 : u^2 = 0 := by nlinarith [sq_nonneg (u^2)]
    nlinarith [sq_nonneg u]
  · rintro rfl v
    apply (_root_.GD.N0005.N0248.d030098 ha ha (-d) d v 0).2
    rw [_root_.GD.N0005.N0248.d030097, _root_.GD.N0005.N0248.d030097]
    have hpos : 0 ≤ v^2*(a-d^2) := mul_nonneg (sq_nonneg v) (sub_nonneg.2 hd)
    nlinarith [sq_nonneg (v^2)]

theorem d030102 (k a b x y u : ℝ) :
    _root_.GD.N0005.N0248.d030071 k k a b x y u = k * _root_.GD.N0005.N0248.d030071 1 1 a b x y u := by
  unfold _root_.GD.N0005.N0248.d030071
  ring

theorem d030103 {k a b x y u : ℝ} (hk : 0 < k) :
    (∀ v : ℝ, _root_.GD.N0005.N0248.d030071 k k a b x y v ≤ _root_.GD.N0005.N0248.d030071 k k a b x y u) ↔
      (∀ v : ℝ, _root_.GD.N0005.N0248.d030071 1 1 a b x y v ≤ _root_.GD.N0005.N0248.d030071 1 1 a b x y u) := by
  simp only [_root_.GD.N0005.N0248.d030102 k, mul_le_mul_iff_right₀ hk]

theorem d030104 {k a d u : ℝ}
    (hk : 0 < k) (ha : 0 < a) (hd : a < d^2) :
    (∀ v : ℝ, _root_.GD.N0005.N0248.d030071 k k a a (-d) d v ≤ _root_.GD.N0005.N0248.d030071 k k a a (-d) d u) ↔
      u^2 = d^2-a :=
  (_root_.GD.N0005.N0248.d030103 hk).trans (_root_.GD.N0005.N0248.d030100 ha hd)

theorem d030105 {k a d u : ℝ}
    (hk : 0 < k) (ha : 0 < a) (hd : d^2 ≤ a) :
    (∀ v : ℝ, _root_.GD.N0005.N0248.d030071 k k a a (-d) d v ≤ _root_.GD.N0005.N0248.d030071 k k a a (-d) d u) ↔
      u = 0 :=
  (_root_.GD.N0005.N0248.d030103 hk).trans (_root_.GD.N0005.N0248.d030101 ha hd)

theorem d030106 :
    ∃ a b x y u v : ℝ, 0 < a ∧ 0 < b ∧ u ≠ v ∧
      (∀ z, _root_.GD.N0005.N0248.d030071 2 2 a b x y z ≤ _root_.GD.N0005.N0248.d030071 2 2 a b x y u) ∧
      (∀ z, _root_.GD.N0005.N0248.d030071 2 2 a b x y z ≤ _root_.GD.N0005.N0248.d030071 2 2 a b x y v) := by
  refine ⟨1, 1, -2, 2, Real.sqrt 3, -Real.sqrt 3, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · have hpos := Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)
    linarith
  · apply (_root_.GD.N0005.N0248.d030104 (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2^2)).2
    norm_num [Real.sq_sqrt]

  · apply (_root_.GD.N0005.N0248.d030104 (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2^2)).2
    norm_num [Real.sq_sqrt]

def d030107 (m n : ℕ) (a b x y u : ℝ) : ℝ :=
  (a^m*b^n) / _root_.GD.N0005.N0248.d030087 m n a b x y u

theorem d030108 (m n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y u : ℝ) : 0 < _root_.GD.N0005.N0248.d030107 m n a b x y u := by
  unfold _root_.GD.N0005.N0248.d030107
  exact div_pos (mul_pos (pow_pos ha m) (pow_pos hb n))
    (_root_.GD.N0005.N0248.d030088 m n ha hb x y u)

theorem d030109 (m n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y u : ℝ) : _root_.GD.N0005.N0248.d030107 m n a b x y u ≤ 1 := by
  apply (div_le_one (_root_.GD.N0005.N0248.d030088 m n ha hb x y u)).2
  unfold _root_.GD.N0005.N0248.d030087
  apply mul_le_mul
  · exact pow_le_pow_left₀ ha.le (by dsimp [_root_.GD.N0005.N0248.d030070]; nlinarith [sq_nonneg (u-x)]) m
  · exact pow_le_pow_left₀ hb.le (by dsimp [_root_.GD.N0005.N0248.d030070]; nlinarith [sq_nonneg (u-y)]) n
  · positivity
  · exact (pow_pos (_root_.GD.N0005.N0248.d030074 ha x u) m).le

theorem d030110 (m n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y u : ℝ) :
    Real.log (_root_.GD.N0005.N0248.d030107 m n a b x y u) =
      2 * (_root_.GD.N0005.N0248.d030071 m n a b x y u +
        ((m : ℝ)*Real.log a + (n : ℝ)*Real.log b)/2) := by
  rw [_root_.GD.N0005.N0248.d030107, Real.log_div
    (mul_ne_zero (pow_ne_zero m ha.ne') (pow_ne_zero n hb.ne'))
    (_root_.GD.N0005.N0248.d030088 m n ha hb x y u).ne',
    Real.log_mul (pow_ne_zero m ha.ne') (pow_ne_zero n hb.ne'),
    Real.log_pow, Real.log_pow, _root_.GD.N0005.N0248.d030089 m n ha hb]
  ring

end
end GD.N0005.N0248

#print axioms _root_.GD.N0005.N0248.d030093
#print axioms _root_.GD.N0005.N0248.d030095
#print axioms _root_.GD.N0005.N0248.d030099
#print axioms _root_.GD.N0005.N0248.d030100
#print axioms _root_.GD.N0005.N0248.d030101
#print axioms _root_.GD.N0005.N0248.d030106
#print axioms _root_.GD.N0005.N0248.d030110
