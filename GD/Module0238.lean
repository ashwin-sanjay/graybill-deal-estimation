import GD.Module0232


















namespace GD
namespace N0229
namespace N0551

open LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]


def d003470 (B : LinearMap.BilinForm ℝ V) (c b : V) : ℝ :=
  2 * B c b - B b b


theorem d003471 (B : LinearMap.BilinForm ℝ V) (c : V) :
    _root_.GD.N0229.N0551.d003470 B c c = B c c := by
  simp only [_root_.GD.N0229.N0551.d003470]
  ring


theorem d003472 (B : LinearMap.BilinForm ℝ V) (c : V) :
    _root_.GD.N0229.N0551.d003470 B c 0 = 0 := by
  simp [_root_.GD.N0229.N0551.d003470]


theorem d003473 (B : LinearMap.BilinForm ℝ V) (c : V) :
    _root_.GD.N0229.N0551.d003470 B c (2 • c) = 0 := by
  simp only [_root_.GD.N0229.N0551.d003470, two_nsmul, map_add, LinearMap.add_apply]
  ring


theorem d003474 (B : LinearMap.BilinForm ℝ V) (c a : V) (t : ℝ) :
    _root_.GD.N0229.N0551.d003470 B c (t • a) =
      2 * t * B c a - t ^ 2 * B a a := by
  simp only [_root_.GD.N0229.N0551.d003470, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring



theorem d003475
    {B : LinearMap.BilinForm ℝ V} (hBnonneg : ∀ x : V, 0 ≤ B x x)
    {c b : V} (hgain : 0 < _root_.GD.N0229.N0551.d003470 B c b) :
    0 < B c b := by
  have henergy := hBnonneg b
  simp only [_root_.GD.N0229.N0551.d003470] at hgain
  linarith





theorem d003476
    {Θ : Type*} {B : Θ → LinearMap.BilinForm ℝ V} {c : Θ → V}
    {a : V} {δ M t : ℝ}
    (ht : 0 < t) (hδ : 0 < δ) (hM : 0 ≤ M)
    (htrace : ∀ θ, δ ≤ B θ (c θ) a)
    (henergy : ∀ θ, B θ a a ≤ M)
    (hstep : t * M < 2 * δ) :
    ∀ θ, 0 < _root_.GD.N0229.N0551.d003470 (B θ) (c θ) (t • a) := by
  intro θ
  rw [_root_.GD.N0229.N0551.d003474]
  have htraceθ := htrace θ
  have henergyθ := henergy θ
  nlinarith [mul_lt_mul_of_pos_left hstep ht]




def d003477
    {Θ : Type*} (S : Finset Θ) (w : Θ → ℝ)
    (B : Θ → LinearMap.BilinForm ℝ V) : LinearMap.BilinForm ℝ V :=
  ∑ θ ∈ S, w θ • B θ



def d003478
    {Θ : Type*} (S : Finset Θ) (w : Θ → ℝ)
    (B : Θ → LinearMap.BilinForm ℝ V) (c : Θ → V) (b : V) : ℝ :=
  ∑ θ ∈ S, w θ * B θ (c θ) b

theorem d003479
    {Θ : Type*} (S : Finset Θ) (w : Θ → ℝ)
    (B : Θ → LinearMap.BilinForm ℝ V) (x y : V) :
    _root_.GD.N0229.N0551.d003477 S w B x y =
      ∑ θ ∈ S, w θ * B θ x y := by
  simp [_root_.GD.N0229.N0551.d003477]



theorem d003480
    {Θ : Type*} (S : Finset Θ) (w : Θ → ℝ)
    (B : Θ → LinearMap.BilinForm ℝ V) (c : Θ → V) (b : V) :
    ∑ θ ∈ S, w θ * _root_.GD.N0229.N0551.d003470 (B θ) (c θ) b =
      2 * _root_.GD.N0229.N0551.d003478 S w B c b -
        _root_.GD.N0229.N0551.d003477 S w B b b := by
  simp only [_root_.GD.N0229.N0551.d003470, _root_.GD.N0229.N0551.d003478, _root_.GD.N0229.N0551.d003479]
  rw [Finset.mul_sum]
  simp_rw [mul_sub, ← mul_assoc]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro θ hθ
    ring






theorem d003481
    {Θ : Type*} (S : Finset Θ) (w : Θ → ℝ)
    (B : Θ → LinearMap.BilinForm ℝ V) (c : Θ → V) (cbar b : V)
    (hcbar :
      _root_.GD.N0229.N0551.d003477 S w B cbar b =
        _root_.GD.N0229.N0551.d003478 S w B c b) :
    ∑ θ ∈ S, w θ * _root_.GD.N0229.N0551.d003470 (B θ) (c θ) b =
      _root_.GD.N0229.N0551.d003470 (_root_.GD.N0229.N0551.d003477 S w B) cbar b := by
  rw [_root_.GD.N0229.N0551.d003480, _root_.GD.N0229.N0551.d003470, hcbar]


theorem d003482
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) (c b : V) :
    _root_.GD.N0229.N0551.d003470 B c b = B c c - B (b - c) (b - c) := by
  have hsym : B b c = B c b := by
    simpa using hB.eq b c
  simp only [_root_.GD.N0229.N0551.d003470, map_sub, LinearMap.sub_apply]
  rw [hsym]
  ring



theorem d003483
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) (c b : V) :
    0 < _root_.GD.N0229.N0551.d003470 B c b ↔ B (b - c) (b - c) < B c c := by
  rw [_root_.GD.N0229.N0551.d003482 hB]
  constructor <;> intro h <;> linarith


theorem d003484
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) (c b : V) :
    0 ≤ _root_.GD.N0229.N0551.d003470 B c b ↔ B (b - c) (b - c) ≤ B c c := by
  rw [_root_.GD.N0229.N0551.d003482 hB]
  constructor <;> intro h <;> linarith


theorem d003485
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm)
    (hBnonneg : ∀ x : V, 0 ≤ B x x) (c b : V) :
    _root_.GD.N0229.N0551.d003470 B c b ≤ _root_.GD.N0229.N0551.d003470 B c c := by
  rw [_root_.GD.N0229.N0551.d003482 hB, _root_.GD.N0229.N0551.d003471]
  exact sub_le_self _ (hBnonneg (b - c))


theorem d003486
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm)
    (hBpos : ∀ x : V, x ≠ 0 → 0 < B x x)
    {c b : V} (hbc : b ≠ c) :
    _root_.GD.N0229.N0551.d003470 B c b < _root_.GD.N0229.N0551.d003470 B c c := by
  rw [_root_.GD.N0229.N0551.d003482 hB, _root_.GD.N0229.N0551.d003471]
  have hsub : b - c ≠ 0 := sub_ne_zero.mpr hbc
  exact sub_lt_self _ (hBpos (b - c) hsub)



theorem d003487
    {B : LinearMap.BilinForm ℝ V} {c : V} (hc : B c c ≠ 0) (t : ℝ) :
    _root_.GD.N0229.N0551.d003470 B c (t • c) = 0 ↔ t = 0 ∨ t = 2 := by
  rw [_root_.GD.N0229.N0551.d003474]
  constructor
  · intro h
    have hfactor : B c c * (t * (2 - t)) = 0 := by
      calc
        B c c * (t * (2 - t)) =
            2 * t * B c c - t ^ 2 * B c c := by ring
        _ = 0 := h
    rcases mul_eq_zero.mp hfactor with henergy | ht
    · exact (hc henergy).elim
    · rcases mul_eq_zero.mp ht with ht | ht
      · exact Or.inl ht
      · exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · ring
    · ring





theorem d003488
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) (c x y : V) :
    _root_.GD.N0229.N0551.d003470 B c ((1 / 2 : ℝ) • (x + y)) =
      (1 / 2 : ℝ) * _root_.GD.N0229.N0551.d003470 B c x +
      (1 / 2 : ℝ) * _root_.GD.N0229.N0551.d003470 B c y +
      (1 / 4 : ℝ) * B (x - y) (x - y) := by
  have hxy : B y x = B x y := by
    simpa using hB.eq y x
  simp only [_root_.GD.N0229.N0551.d003470, map_smul, LinearMap.smul_apply, smul_eq_mul, map_add,
    LinearMap.add_apply, map_sub, LinearMap.sub_apply]
  ring



theorem d003489
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm)
    (hBpos : ∀ z : V, z ≠ 0 → 0 < B z z)
    (c : V) {x y : V} (hxy : x ≠ y) :
    (1 / 2 : ℝ) * _root_.GD.N0229.N0551.d003470 B c x + (1 / 2 : ℝ) * _root_.GD.N0229.N0551.d003470 B c y <
      _root_.GD.N0229.N0551.d003470 B c ((1 / 2 : ℝ) • (x + y)) := by
  rw [_root_.GD.N0229.N0551.d003488 hB]
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hpos := hBpos (x - y) hsub
  linarith

end N0551
end N0229
end GD
