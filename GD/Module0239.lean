import GD.Module0238




















namespace GD
namespace N0229
namespace N0549

open scoped BigOperators

open _root_.GD.N0229.N0551

variable {ι V : Type*}
  [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module ℝ V]


def d003490 (w : ι → ℝ) (B : ι → LinearMap.BilinForm ℝ V) :
    LinearMap.BilinForm ℝ V :=
  _root_.GD.N0229.N0551.d003477 Finset.univ w B


def d003491
    (w : ι → ℝ) (B : ι → LinearMap.BilinForm ℝ V) (c : ι → V) (b : V) : ℝ :=
  _root_.GD.N0229.N0551.d003478 Finset.univ w B c b



def d003492
    (w : ι → ℝ) (B : ι → LinearMap.BilinForm ℝ V) (c : ι → V) (b : V) : ℝ :=
  2 * _root_.GD.N0229.N0549.d003491 w B c b - _root_.GD.N0229.N0549.d003490 w B b b

theorem d003493
    (w : ι → ℝ) (B : ι → LinearMap.BilinForm ℝ V) (x y : V) :
    _root_.GD.N0229.N0549.d003490 w B x y = ∑ i, w i * B i x y := by
  exact _root_.GD.N0229.N0551.d003479 Finset.univ w B x y


theorem d003494
    (w : ι → ℝ) (B : ι → LinearMap.BilinForm ℝ V)
    (hB : ∀ i, (B i).IsSymm) :
    (_root_.GD.N0229.N0549.d003490 w B).IsSymm := by
  constructor
  intro x y
  simp only [_root_.GD.N0229.N0549.d003493]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun r : ℝ ↦ w i * r) (by
    simpa using (hB i).eq x y)


theorem d003495
    (w : ι → ℝ) (B : ι → LinearMap.BilinForm ℝ V)
    (hw : ∀ i, 0 ≤ w i)
    (hB : ∀ i x, 0 ≤ B i x x) :
    ∀ x, 0 ≤ _root_.GD.N0229.N0549.d003490 w B x x := by
  intro x
  rw [_root_.GD.N0229.N0549.d003493]
  exact Finset.sum_nonneg fun i hi ↦
    mul_nonneg (hw i) (hB i x)



theorem d003496
    (w : ι → ℝ) (B : ι → LinearMap.BilinForm ℝ V) (c : ι → V) (b : V) :
    ∑ i, w i * _root_.GD.N0229.N0551.d003470 (B i) (c i) b =
      _root_.GD.N0229.N0549.d003492 w B c b := by
  exact _root_.GD.N0229.N0551.d003480
    Finset.univ w B c b





theorem d003497
    (w : ι → ℝ) (B : ι → LinearMap.BilinForm ℝ V) (c : ι → V)
    (cbar : V)
    (hcbar :
      ∀ b, _root_.GD.N0229.N0549.d003490 w B cbar b = _root_.GD.N0229.N0549.d003491 w B c b) :
    ∀ b,
      ∑ i, w i * _root_.GD.N0229.N0551.d003470 (B i) (c i) b =
        _root_.GD.N0229.N0551.d003470 (_root_.GD.N0229.N0549.d003490 w B) cbar b := by
  intro b
  exact _root_.GD.N0229.N0551.d003481
    Finset.univ w B c cbar b (hcbar b)



theorem d003498
    {w : ι → ℝ} {B : ι → LinearMap.BilinForm ℝ V} {c : ι → V}
    {b : V} {ε : ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1)
    (hgate : ∀ i, ε ≤ _root_.GD.N0229.N0551.d003470 (B i) (c i) b) :
    ε ≤ ∑ i, w i * _root_.GD.N0229.N0551.d003470 (B i) (c i) b := by
  have hterm :
      ∀ i, w i * ε ≤ w i * _root_.GD.N0229.N0551.d003470 (B i) (c i) b := by
    intro i
    exact mul_le_mul_of_nonneg_left (hgate i) (hw i)
  calc
    ε = ∑ i, w i * ε := by
      rw [← Finset.sum_mul, hwsum, one_mul]
    _ ≤ ∑ i, w i * _root_.GD.N0229.N0551.d003470 (B i) (c i) b :=
      Finset.sum_le_sum fun i hi ↦ hterm i



theorem d003499
    {w : ι → ℝ} {B : ι → LinearMap.BilinForm ℝ V} {c : ι → V}
    {b : V}
    (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1)
    (hgate : ∀ i, 0 < _root_.GD.N0229.N0551.d003470 (B i) (c i) b) :
    0 < ∑ i, w i * _root_.GD.N0229.N0551.d003470 (B i) (c i) b := by
  have hex : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have hnonpos : (∑ i, w i) ≤ 0 :=
      Finset.sum_nonpos fun i hi ↦ h i
    rw [hwsum] at hnonpos
    norm_num at hnonpos
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (hw i) (le_of_lt (hgate i))
  · obtain ⟨i, hwi⟩ := hex
    exact ⟨i, Finset.mem_univ i, mul_pos hwi (hgate i)⟩





theorem d003500
    {B : ι → LinearMap.BilinForm ℝ V} {c : ι → V}
    {a : V} {δ M t : ℝ}
    (ht : 0 < t) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hlinear : ∀ i, δ ≤ B i (c i) a)
    (hquadratic : ∀ i, B i a a ≤ M)
    (hstep : t * M < 2 * δ) :
    ∀ i, 0 < _root_.GD.N0229.N0551.d003470 (B i) (c i) (t • a) := by
  exact _root_.GD.N0229.N0551.d003476
    ht hδ hM hlinear hquadratic hstep





theorem d003501
    {B : ι → LinearMap.BilinForm ℝ V} {c : ι → V}
    {a : V} {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hlinear : ∀ i, δ ≤ B i (c i) a)
    (hquadratic : ∀ i, B i a a ≤ M) :
    ∀ i, 0 < _root_.GD.N0229.N0551.d003470 (B i) (c i) ((δ / (M + 1)) • a) := by
  have hden : 0 < M + 1 := by linarith
  have ht : 0 < δ / (M + 1) := div_pos hδ hden
  have hfrac : M / (M + 1) < 1 :=
    (div_lt_one hden).2 (by linarith)
  have hδfrac : δ * (M / (M + 1)) < δ :=
    by simpa using mul_lt_mul_of_pos_left hfrac hδ
  have hstep : (δ / (M + 1)) * M < 2 * δ := by
    calc
      (δ / (M + 1)) * M = δ * (M / (M + 1)) := by ring
      _ < δ := hδfrac
      _ < 2 * δ := by linarith
  exact _root_.GD.N0229.N0549.d003500
    ht hδ hM hlinear hquadratic hstep

end N0549
end N0229
end GD
