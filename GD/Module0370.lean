import GD.Module0366
import GD.Module0369
import GD.Module0240
import GD.Module0185
import Mathlib.Tactic




















































set_option autoImplicit false
set_option warningAsError true

open Matrix
open _root_.GD.N0106.N0428.N0765.N1567
open _root_.GD.N0106.N0428.N0765.N1604
open _root_.GD.N0232.N0720.N1247
open _root_.GD.N0232.N0720.N1249 (d002229 d002230)
open _root_.GD.N0229.N0550

namespace GD.N0106.N0428.N0765.N1603




noncomputable def d005578 : Matrix (Fin 5) (Fin 5) ℝ := _root_.GD.N0106.N0428.N0765.N1604.d005549.map (Rat.castHom ℝ)


noncomputable def d005579 : Matrix (Fin 5) (Fin 5) ℝ := _root_.GD.N0106.N0428.N0765.N1604.d005550.map (Rat.castHom ℝ)


noncomputable def d005580 : Matrix (Fin 5) (Fin 5) ℝ := _root_.GD.N0106.N0428.N0765.N1604.d005551.map (Rat.castHom ℝ)


noncomputable def d005581 : Matrix (Fin 5) (Fin 5) ℝ := _root_.GD.N0106.N0428.N0765.N1604.d005552.map (Rat.castHom ℝ)


noncomputable def d005582 : Fin 5 → ℝ := fun i => (_root_.GD.N0106.N0428.N0765.N1604.d005553 i : ℝ)

theorem d005583 (r c : Fin 5) : _root_.GD.N0106.N0428.N0765.N1603.d005578 r c = (_root_.GD.N0106.N0428.N0765.N1604.d005549 r c : ℝ) := by
  simp [_root_.GD.N0106.N0428.N0765.N1603.d005578]

theorem d005584 (r c : Fin 5) : _root_.GD.N0106.N0428.N0765.N1603.d005579 r c = (_root_.GD.N0106.N0428.N0765.N1604.d005550 r c : ℝ) := by
  simp [_root_.GD.N0106.N0428.N0765.N1603.d005579]

theorem d005585 (i k : Fin 5) : _root_.GD.N0106.N0428.N0765.N1603.d005580 i k = (_root_.GD.N0106.N0428.N0765.N1604.d005551 i k : ℝ) := by
  simp [_root_.GD.N0106.N0428.N0765.N1603.d005580]

theorem d005586 (i k : Fin 5) : _root_.GD.N0106.N0428.N0765.N1603.d005581 i k = (_root_.GD.N0106.N0428.N0765.N1604.d005552 i k : ℝ) := by
  simp [_root_.GD.N0106.N0428.N0765.N1603.d005581]

theorem d005587 (r : Fin 4) : _root_.GD.N0106.N0428.N0765.N1603.d005582 r.castSucc = 0 := by
  simp [_root_.GD.N0106.N0428.N0765.N1603.d005582, _root_.GD.N0106.N0428.N0765.N1604.d005563]

theorem d005588 : _root_.GD.N0106.N0428.N0765.N1603.d005582 (Fin.last 4) = 1 := by
  change (_root_.GD.N0106.N0428.N0765.N1604.d005553 (Fin.last 4) : ℝ) = 1
  rw [_root_.GD.N0106.N0428.N0765.N1604.d005562, Rat.cast_one]


theorem d005589 : _root_.GD.N0106.N0428.N0765.N1603.d005580 * _root_.GD.N0106.N0428.N0765.N1603.d005578 = 1 := by
  have h : (_root_.GD.N0106.N0428.N0765.N1604.d005551 * _root_.GD.N0106.N0428.N0765.N1604.d005549).map (Rat.castHom ℝ) =
      (1 : Matrix (Fin 5) (Fin 5) ℚ).map (Rat.castHom ℝ) := by
    rw [_root_.GD.N0106.N0428.N0765.N1604.d005564]
  rw [Matrix.map_mul (f := Rat.castHom ℝ),
    Matrix.map_one (Rat.castHom ℝ) (map_zero (Rat.castHom ℝ)) (map_one (Rat.castHom ℝ))] at h
  exact h

theorem d005590 (i k : Fin 5) : |_root_.GD.N0106.N0428.N0765.N1603.d005580 i k| ≤ _root_.GD.N0106.N0428.N0765.N1603.d005581 i k := by
  rw [_root_.GD.N0106.N0428.N0765.N1603.d005585, _root_.GD.N0106.N0428.N0765.N1603.d005586]
  exact_mod_cast _root_.GD.N0106.N0428.N0765.N1604.d005565 i k

theorem d005591 (i : Fin 5) :
    ∑ j, ∑ k, _root_.GD.N0106.N0428.N0765.N1603.d005581 i k * _root_.GD.N0106.N0428.N0765.N1603.d005579 k j ≤ (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1603.d005586, _root_.GD.N0106.N0428.N0765.N1603.d005584]
  exact_mod_cast _root_.GD.N0106.N0428.N0765.N1604.d005566 i

theorem d005592 : (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) < 1 := by
  exact_mod_cast _root_.GD.N0232.N0720.N1247.d002174

theorem d005593 (i : Fin 5) : (_root_.GD.N0106.N0428.N0765.N1603.d005580 *ᵥ _root_.GD.N0106.N0428.N0765.N1603.d005582) i = (_root_.GD.N0232.N0720.N1247.d002170 i : ℝ) := by
  have h := _root_.GD.N0106.N0428.N0765.N1604.d005568 i
  simp only [Matrix.mulVec, dotProduct] at h ⊢
  simp only [_root_.GD.N0106.N0428.N0765.N1603.d005585, _root_.GD.N0106.N0428.N0765.N1603.d005582]
  exact_mod_cast h

theorem d005594 (i : Fin 5) :
    |(_root_.GD.N0106.N0428.N0765.N1603.d005580 *ᵥ _root_.GD.N0106.N0428.N0765.N1603.d005582) i| ≤ (_root_.GD.N0232.N0720.N1247.d002170 1 : ℝ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1603.d005593]
  exact_mod_cast _root_.GD.N0106.N0428.N0765.N1604.d005569 i

theorem d005595 :
    (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) * (_root_.GD.N0232.N0720.N1247.d002170 1 : ℝ) / (1 - (_root_.GD.N0232.N0720.N1247.d002169 : ℝ)) = (_root_.GD.N0232.N0720.N1247.d002171 : ℝ) := by
  exact_mod_cast _root_.GD.N0106.N0428.N0765.N1604.d005571





def d005596 (A : Matrix (Fin 5) (Fin 5) ℝ) : Prop :=
  ∀ r c, (_root_.GD.N0106.N0428.N0765.N1604.d005547 r c : ℝ) ≤ A r c ∧ A r c ≤ (_root_.GD.N0106.N0428.N0765.N1604.d005548 r c : ℝ)

theorem d005597 {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A) (r c : Fin 5) :
    |A r c - _root_.GD.N0106.N0428.N0765.N1603.d005578 r c| ≤ _root_.GD.N0106.N0428.N0765.N1603.d005579 r c := by
  obtain ⟨h1, h2⟩ := hA r c
  have hlo : (_root_.GD.N0106.N0428.N0765.N1604.d005547 r c : ℝ) = _root_.GD.N0106.N0428.N0765.N1603.d005578 r c - _root_.GD.N0106.N0428.N0765.N1603.d005579 r c := by
    rw [_root_.GD.N0106.N0428.N0765.N1603.d005583, _root_.GD.N0106.N0428.N0765.N1603.d005584, ← Rat.cast_sub, _root_.GD.N0106.N0428.N0765.N1604.d005556]
  have hhi : (_root_.GD.N0106.N0428.N0765.N1604.d005548 r c : ℝ) = _root_.GD.N0106.N0428.N0765.N1603.d005578 r c + _root_.GD.N0106.N0428.N0765.N1603.d005579 r c := by
    rw [_root_.GD.N0106.N0428.N0765.N1603.d005583, _root_.GD.N0106.N0428.N0765.N1603.d005584, ← Rat.cast_add, _root_.GD.N0106.N0428.N0765.N1604.d005557]
  rw [abs_le]
  constructor <;> linarith




theorem d005598 {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A) : IsUnit A :=
  _root_.GD.N0106.N0428.N0765.N1567.d005503 A _root_.GD.N0106.N0428.N0765.N1603.d005578 _root_.GD.N0106.N0428.N0765.N1603.d005580 _root_.GD.N0106.N0428.N0765.N1603.d005581 _root_.GD.N0106.N0428.N0765.N1603.d005579 (_root_.GD.N0232.N0720.N1247.d002169 : ℝ)
    _root_.GD.N0106.N0428.N0765.N1603.d005589 _root_.GD.N0106.N0428.N0765.N1603.d005590 (_root_.GD.N0106.N0428.N0765.N1603.d005597 hA) _root_.GD.N0106.N0428.N0765.N1603.d005591
    _root_.GD.N0106.N0428.N0765.N1603.d005592


theorem d005599 {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A) :
    ∃! w, A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582 :=
  _root_.GD.N0106.N0428.N0765.N1567.d005504 A _root_.GD.N0106.N0428.N0765.N1603.d005578 _root_.GD.N0106.N0428.N0765.N1603.d005580 _root_.GD.N0106.N0428.N0765.N1603.d005581 _root_.GD.N0106.N0428.N0765.N1603.d005579 (_root_.GD.N0232.N0720.N1247.d002169 : ℝ)
    _root_.GD.N0106.N0428.N0765.N1603.d005589 _root_.GD.N0106.N0428.N0765.N1603.d005590 (_root_.GD.N0106.N0428.N0765.N1603.d005597 hA) _root_.GD.N0106.N0428.N0765.N1603.d005591
    _root_.GD.N0106.N0428.N0765.N1603.d005592 _root_.GD.N0106.N0428.N0765.N1603.d005582


theorem d005600 {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A) :
    A *ᵥ (A⁻¹ *ᵥ _root_.GD.N0106.N0428.N0765.N1603.d005582) = _root_.GD.N0106.N0428.N0765.N1603.d005582 := by
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp (_root_.GD.N0106.N0428.N0765.N1603.d005598 hA)),
    Matrix.one_mulVec]



theorem d005601 {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A)
    {w : Fin 5 → ℝ} (hw : A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582) (i : Fin 5) :
    |w i - (_root_.GD.N0232.N0720.N1247.d002170 i : ℝ)| ≤ (_root_.GD.N0232.N0720.N1247.d002171 : ℝ) := by
  have h := _root_.GD.N0106.N0428.N0765.N1567.d005505 A _root_.GD.N0106.N0428.N0765.N1603.d005578 _root_.GD.N0106.N0428.N0765.N1603.d005580 _root_.GD.N0106.N0428.N0765.N1603.d005581 _root_.GD.N0106.N0428.N0765.N1603.d005579 (_root_.GD.N0232.N0720.N1247.d002169 : ℝ)
    _root_.GD.N0106.N0428.N0765.N1603.d005589 _root_.GD.N0106.N0428.N0765.N1603.d005590 (_root_.GD.N0106.N0428.N0765.N1603.d005597 hA) _root_.GD.N0106.N0428.N0765.N1603.d005591
    _root_.GD.N0106.N0428.N0765.N1603.d005592 w _root_.GD.N0106.N0428.N0765.N1603.d005582 hw (_root_.GD.N0232.N0720.N1247.d002170 1 : ℝ) _root_.GD.N0106.N0428.N0765.N1603.d005594 i
  rw [_root_.GD.N0106.N0428.N0765.N1603.d005593, _root_.GD.N0106.N0428.N0765.N1603.d005595] at h
  exact h



theorem d005602 {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A)
    {w : Fin 5 → ℝ} (hw : A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582) (i : Fin 5) :
    (_root_.GD.N0232.N0720.N1247.d002172 : ℝ) ≤ w i := by
  have hlow : (_root_.GD.N0232.N0720.N1247.d002170 i : ℝ) - (_root_.GD.N0232.N0720.N1247.d002171 : ℝ) ≤ w i :=
    _root_.GD.N0106.N0428.N0765.N1567.d005506 w (fun j => (_root_.GD.N0232.N0720.N1247.d002170 j : ℝ)) (_root_.GD.N0232.N0720.N1247.d002171 : ℝ)
      (_root_.GD.N0106.N0428.N0765.N1603.d005601 hA hw) i
  have h3 : (_root_.GD.N0232.N0720.N1247.d002170 3 : ℝ) ≤ (_root_.GD.N0232.N0720.N1247.d002170 i : ℝ) := by
    exact_mod_cast _root_.GD.N0106.N0428.N0765.N1604.d005570 i
  have hmin : (_root_.GD.N0232.N0720.N1247.d002172 : ℝ) = (_root_.GD.N0232.N0720.N1247.d002170 3 : ℝ) - (_root_.GD.N0232.N0720.N1247.d002171 : ℝ) := by
    exact_mod_cast _root_.GD.N0232.N0720.N1247.d002177.symm
  linarith


theorem d005603 {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A)
    {w : Fin 5 → ℝ} (hw : A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582) : ∀ i, 0 < w i :=
  _root_.GD.N0229.N0550.d003504 (fun j => (_root_.GD.N0232.N0720.N1247.d002170 j : ℝ)) w (_root_.GD.N0232.N0720.N1247.d002171 : ℝ)
    (fun j => by exact_mod_cast _root_.GD.N0106.N0428.N0765.N1604.d005572 j) (_root_.GD.N0106.N0428.N0765.N1603.d005601 hA hw)


theorem d005604 {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A) :
    ∃ w, A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582 ∧ ∀ i, 0 < w i :=
  ⟨A⁻¹ *ᵥ _root_.GD.N0106.N0428.N0765.N1603.d005582, _root_.GD.N0106.N0428.N0765.N1603.d005600 hA, _root_.GD.N0106.N0428.N0765.N1603.d005603 hA (_root_.GD.N0106.N0428.N0765.N1603.d005600 hA)⟩


theorem d005605 {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A) (c : Fin 5) : A (Fin.last 4) c = 1 := by
  obtain ⟨hlo, hhi⟩ := hA (Fin.last 4) c
  rw [_root_.GD.N0106.N0428.N0765.N1604.d005560] at hlo
  rw [_root_.GD.N0106.N0428.N0765.N1604.d005561] at hhi
  exact le_antisymm (by simpa using hhi) (by simpa using hlo)


theorem d005606 {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A) {w : Fin 5 → ℝ} (hw : A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582) :
    ∑ i, w i = 1 := by
  have h := congrFun hw (Fin.last 4)
  simpa only [Matrix.mulVec, dotProduct, _root_.GD.N0106.N0428.N0765.N1603.d005605 hA, one_mul, _root_.GD.N0106.N0428.N0765.N1603.d005588] using h


theorem d005607 {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A) {w : Fin 5 → ℝ} (hw : A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582) (i : Fin 5) :
    (170842 / 1000000 : ℝ) < w i := by
  have hmin : (170842 / 1000000 : ℝ) < (_root_.GD.N0232.N0720.N1247.d002172 : ℝ) := by
    have hcast : ((170842 / 1000000 : ℚ) : ℝ) < (_root_.GD.N0232.N0720.N1247.d002172 : ℝ) :=
      Rat.cast_lt.mpr _root_.GD.N0106.N0428.N0765.N1604.d005575
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcast
  exact hmin.trans_le (_root_.GD.N0106.N0428.N0765.N1603.d005602 hA hw i)



theorem d005608 {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : _root_.GD.N0106.N0428.N0765.N1603.d005596 A) :
    ∃! w : Fin 5 → ℝ, A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582 ∧ (∑ i, w i = 1) ∧
      ∀ i, (170842 / 1000000 : ℝ) < w i := by
  obtain ⟨w, hw, hunique⟩ := _root_.GD.N0106.N0428.N0765.N1603.d005599 hA
  refine ⟨w, ⟨hw, _root_.GD.N0106.N0428.N0765.N1603.d005606 hA hw, _root_.GD.N0106.N0428.N0765.N1603.d005607 hA hw⟩, ?_⟩
  intro y hy
  exact hunique y hy.1





noncomputable def d005609 (h : Fin 5 → Fin 4 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun r c => Fin.lastCases (motive := fun _ => ℝ) 1 (fun r' => h c r') r

theorem d005610 (h : Fin 5 → Fin 4 → ℝ) (r : Fin 4) (c : Fin 5) :
    _root_.GD.N0106.N0428.N0765.N1603.d005609 h r.castSucc c = h c r := by
  simp [_root_.GD.N0106.N0428.N0765.N1603.d005609]

theorem d005611 (h : Fin 5 → Fin 4 → ℝ) (c : Fin 5) :
    _root_.GD.N0106.N0428.N0765.N1603.d005609 h (Fin.last 4) c = 1 := by
  change Fin.lastCases (motive := fun _ => ℝ) 1 (fun r' => h c r') (Fin.last 4) = 1
  exact Fin.lastCases_last


theorem d005612 (h : Fin 5 → Fin 4 → ℝ)
    (hbox : ∀ c (r : Fin 4),
      (_root_.GD.N0106.N0428.N0765.N1604.d005547 r.castSucc c : ℝ) ≤ h c r ∧ h c r ≤ (_root_.GD.N0106.N0428.N0765.N1604.d005548 r.castSucc c : ℝ)) :
    _root_.GD.N0106.N0428.N0765.N1603.d005596 (_root_.GD.N0106.N0428.N0765.N1603.d005609 h) := by
  intro r c
  induction r using Fin.lastCases with
  | last =>
    rw [_root_.GD.N0106.N0428.N0765.N1603.d005611, _root_.GD.N0106.N0428.N0765.N1604.d005560, _root_.GD.N0106.N0428.N0765.N1604.d005561]
    simp
  | cast r =>
    rw [_root_.GD.N0106.N0428.N0765.N1603.d005610]
    exact hbox c r


theorem d005613 (h : Fin 5 → Fin 4 → ℝ) {w : Fin 5 → ℝ}
    (hw : _root_.GD.N0106.N0428.N0765.N1603.d005609 h *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582) (r : Fin 4) :
    ∑ c, w c * h c r = 0 := by
  have hr := congrFun hw r.castSucc
  simp only [Matrix.mulVec, dotProduct, _root_.GD.N0106.N0428.N0765.N1603.d005610, _root_.GD.N0106.N0428.N0765.N1603.d005587] at hr
  rw [← hr]
  apply Finset.sum_congr rfl
  intro c _
  ring


noncomputable def d005614 (g : Fin 5 → Fin 4 → ℝ) (colScale : Fin 5 → ℝ)
    (c : Fin 5) (r : Fin 4) : ℝ :=
  _root_.GD.N0232.N0720.N1249.d002229 r * g c r / colScale c





theorem d005615 (g : Fin 5 → Fin 4 → ℝ) (colScale : Fin 5 → ℝ)
    (hcol : ∀ c, 0 < colScale c)
    (hbox : ∀ c (r : Fin 4),
      (_root_.GD.N0106.N0428.N0765.N1604.d005547 r.castSucc c : ℝ) ≤ _root_.GD.N0106.N0428.N0765.N1603.d005614 g colScale c r ∧
        _root_.GD.N0106.N0428.N0765.N1603.d005614 g colScale c r ≤ (_root_.GD.N0106.N0428.N0765.N1604.d005548 r.castSucc c : ℝ)) :
    ∃ α : Fin 5 → ℝ, (∀ c, 0 < α c) ∧ ∀ r : Fin 4, ∑ c, α c * g c r = 0 := by
  have hA := _root_.GD.N0106.N0428.N0765.N1603.d005612 (_root_.GD.N0106.N0428.N0765.N1603.d005614 g colScale) hbox
  obtain ⟨w, hw, hwpos⟩ := _root_.GD.N0106.N0428.N0765.N1603.d005604 hA
  refine ⟨fun c => w c / colScale c,
    _root_.GD.N0229.N0550.d003503 colScale w hcol hwpos, ?_⟩
  have hrows : ∀ r : Fin 4, ∑ c, w c * (_root_.GD.N0232.N0720.N1249.d002229 r * g c r / colScale c) = 0 := by
    intro r
    exact _root_.GD.N0106.N0428.N0765.N1603.d005613 (_root_.GD.N0106.N0428.N0765.N1603.d005614 g colScale) hw r
  exact (_root_.GD.N0229.N0550.d003502 _root_.GD.N0232.N0720.N1249.d002229 colScale w g _root_.GD.N0232.N0720.N1249.d002230).mpr hrows


noncomputable def d005616 (g : Fin 5 → Fin 4 → ℝ) (c : Fin 5) : ℝ :=
  Real.sqrt (∑ r, (_root_.GD.N0232.N0720.N1249.d002229 r * g c r) ^ 2)

theorem d005617 (g : Fin 5 → Fin 4 → ℝ) (c : Fin 5) (hg : ∃ r, g c r ≠ 0) :
    0 < _root_.GD.N0106.N0428.N0765.N1603.d005616 g c := by
  obtain ⟨r, hr⟩ := hg
  apply Real.sqrt_pos.mpr
  apply Finset.sum_pos'
  · intro r' _
    exact sq_nonneg _
  · refine ⟨r, Finset.mem_univ r, ?_⟩
    exact sq_pos_iff.mpr (mul_ne_zero (_root_.GD.N0232.N0720.N1249.d002230 r).ne' hr)



theorem d005618 (g : Fin 5 → Fin 4 → ℝ)
    (hg : ∀ c, ∃ r, g c r ≠ 0)
    (hbox : ∀ c (r : Fin 4),
      (_root_.GD.N0106.N0428.N0765.N1604.d005547 r.castSucc c : ℝ) ≤ _root_.GD.N0106.N0428.N0765.N1603.d005614 g (_root_.GD.N0106.N0428.N0765.N1603.d005616 g) c r ∧
        _root_.GD.N0106.N0428.N0765.N1603.d005614 g (_root_.GD.N0106.N0428.N0765.N1603.d005616 g) c r ≤ (_root_.GD.N0106.N0428.N0765.N1604.d005548 r.castSucc c : ℝ)) :
    ∃ α : Fin 5 → ℝ, (∀ c, 0 < α c) ∧ ∀ r : Fin 4, ∑ c, α c * g c r = 0 :=
  _root_.GD.N0106.N0428.N0765.N1603.d005615 g (_root_.GD.N0106.N0428.N0765.N1603.d005616 g) (fun c => _root_.GD.N0106.N0428.N0765.N1603.d005617 g c (hg c)) hbox






noncomputable def d005619 (forward : Fin 5 → Fin 5 → Fin 2 → ℝ) (c : Fin 5) :
    Fin 4 → ℝ :=
  ![forward c 1 1, forward c 1 0, forward c 3 1, forward c 3 0]



theorem d005620 (forward : Fin 5 → Fin 5 → Fin 2 → ℝ)
    (colScale : Fin 5 → ℝ) (hcol : ∀ c, 0 < colScale c)
    (hbox : ∀ c (r : Fin 4),
      (_root_.GD.N0106.N0428.N0765.N1604.d005547 r.castSucc c : ℝ) ≤ _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r ∧
        _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r ≤ (_root_.GD.N0106.N0428.N0765.N1604.d005548 r.castSucc c : ℝ)) :
    ∃ α : Fin 5 → ℝ, (∀ c, 0 < α c) ∧
      (∀ j, ∑ i, α i * forward i (1 : Fin 5) j = 0) ∧
      (∀ j, ∑ i, α i * forward i (3 : Fin 5) j = 0) := by
  obtain ⟨α, hpos, hbal⟩ :=
    _root_.GD.N0106.N0428.N0765.N1603.d005615 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale hcol hbox
  refine ⟨α, hpos, ?_, ?_⟩
  · intro j
    fin_cases j
    · simpa [_root_.GD.N0106.N0428.N0765.N1603.d005619] using hbal 1
    · simpa [_root_.GD.N0106.N0428.N0765.N1603.d005619] using hbal 0
  · intro j
    fin_cases j
    · simpa [_root_.GD.N0106.N0428.N0765.N1603.d005619] using hbal 3
    · simpa [_root_.GD.N0106.N0428.N0765.N1603.d005619] using hbal 2



open _root_.GD.N0232.N0720.N1249





theorem d005621
    (eta : Fin 5 → ℝ)
    (forward reciprocal : Fin 5 → Fin 5 → Fin 2 → ℝ)
    (colScale : Fin 5 → ℝ)
    (heta : ∀ i, 0 < eta i) (hcol : ∀ i, 0 < colScale i)
    (hbox : ∀ c (r : Fin 4),
      (_root_.GD.N0106.N0428.N0765.N1604.d005547 r.castSucc c : ℝ) ≤ _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r ∧
        _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r ≤ (_root_.GD.N0106.N0428.N0765.N1604.d005548 r.castSucc c : ℝ))
    (hswap : ∀ i k j,
      eta i * reciprocal i k j = -((-1 : ℝ) ^ (k : ℕ)) * forward i k j) :
    ∃ alpha : Fin 5 → ℝ,
      (∀ atom, 0 < _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom) ∧
      ∀ k j, ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
        _root_.GD.N0232.N0720.N1249.d002218 forward reciprocal atom k j = 0 := by
  obtain ⟨alpha, hpos, hoddOne, hoddThree⟩ :=
    _root_.GD.N0106.N0428.N0765.N1603.d005620 forward colScale hcol hbox
  exact ⟨alpha, _root_.GD.N0232.N0720.N1249.d002219 eta alpha heta hpos,
    _root_.GD.N0232.N0720.N1249.d002220 eta alpha forward reciprocal hswap hoddOne hoddThree⟩




theorem d005622
    (eta : Fin 5 → ℝ)
    (forward reciprocal : Fin 5 → Fin 5 → Fin 2 → ℝ)
    (colScale : Fin 5 → ℝ)
    (zero : Fin 5 → Fin 2 → ℝ)
    (energy : Sum (Fin 5) (Fin 5) → (Fin 5 → Fin 2 → ℝ) → ℝ)
    (heta : ∀ i, 0 < eta i) (hcol : ∀ i, 0 < colScale i)
    (hbox : ∀ c (r : Fin 4),
      (_root_.GD.N0106.N0428.N0765.N1604.d005547 r.castSucc c : ℝ) ≤ _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r ∧
        _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r ≤ (_root_.GD.N0106.N0428.N0765.N1604.d005548 r.castSucc c : ℝ))
    (hswap : ∀ i k j,
      eta i * reciprocal i k j = -((-1 : ℝ) ^ (k : ℕ)) * forward i k j)
    (henergy : ∀ atom c, 0 ≤ energy atom c)
    (henergyStrict : ∀ atom c, c ≠ zero → 0 < energy atom c)
    (c : Fin 5 → Fin 2 → ℝ) (hc : c ≠ zero) :
    ∃ atom, 0 < 2 * _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal c atom + energy atom c := by
  obtain ⟨alpha, hpos, hoddOne, hoddThree⟩ :=
    _root_.GD.N0106.N0428.N0765.N1603.d005620 forward colScale hcol hbox
  exact _root_.GD.N0229.N0550.d003512 zero
    (_root_.GD.N0232.N0720.N1249.d002217 eta alpha)
    (fun atom coeff => _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal coeff atom) energy
    (_root_.GD.N0232.N0720.N1249.d002219 eta alpha heta hpos)
    (fun coeff => _root_.GD.N0232.N0720.N1249.d002222 eta alpha forward reciprocal coeff
      hswap hoddOne hoddThree)
    henergy henergyStrict c hc




theorem d005623
    (eta : Fin 5 → ℝ)
    (forward reciprocal : Fin 5 → Fin 5 → Fin 2 → ℝ)
    (colScale : Fin 5 → ℝ)
    (zero : Fin 5 → Fin 2 → ℝ)
    (energy : Sum (Fin 5) (Fin 5) → (Fin 5 → Fin 2 → ℝ) → ℝ)
    (heta : ∀ i, 0 < eta i) (hcol : ∀ i, 0 < colScale i)
    (hbox : ∀ c (r : Fin 4),
      (_root_.GD.N0106.N0428.N0765.N1604.d005547 r.castSucc c : ℝ) ≤ _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r ∧
        _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r ≤ (_root_.GD.N0106.N0428.N0765.N1604.d005548 r.castSucc c : ℝ))
    (hswap : ∀ i k j,
      eta i * reciprocal i k j = -((-1 : ℝ) ^ (k : ℕ)) * forward i k j)
    (henergy : ∀ atom c, 0 ≤ energy atom c)
    (henergyStrict : ∀ atom c, c ≠ zero → 0 < energy atom c) :
    ¬ ∃ c, c ≠ zero ∧ ∀ atom,
      2 * _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal c atom + energy atom c ≤ 0 := by
  rintro ⟨c, hc, hall⟩
  obtain ⟨atom, hatom⟩ := _root_.GD.N0106.N0428.N0765.N1603.d005622
    eta forward reciprocal colScale zero energy heta hcol hbox hswap henergy henergyStrict c hc
  exact (not_lt_of_ge (hall atom)) hatom

end GD.N0106.N0428.N0765.N1603
