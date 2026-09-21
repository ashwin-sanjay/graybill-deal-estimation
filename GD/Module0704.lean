import GD.Module0703
import GD.Module0652


















open MeasureTheory Set
open scoped BigOperators NNReal

namespace GD.N0232.N0719.N0904

noncomputable section

local instance d010384 {k : ℕ} (p : Fin k → ℝ) :
    Decidable (_root_.GD.N0232.N0719.N0951.d003580 p) :=
  Classical.propDecidable _

theorem d010385
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0902.d010372 sizes scales i := by
  apply NNReal.coe_pos.1
  simp only [_root_.GD.N0232.N0719.N0902.d010372, NNReal.coe_mk]
  have hsize : 0 < (sizes i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hsizes i))
  exact div_pos (sq_pos_of_pos (hscales i)) hsize

theorem d010386
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (i : Fin k) :
    _root_.GD.N0232.N0719.N0902.d010372 sizes scales i ≠ 0 :=
  (_root_.GD.N0232.N0719.N0904.d010385 sizes hsizes scales hscales i).ne'






theorem d010387
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0954.d009349 hk t) ≤ 1 := by
  classical
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  have hp0 : ∀ i, 0 ≤ p i :=
    fun i =>
      (_root_.GD.N0232.N0719.N0956.d010069
        hk (fun _ => 0) t ht i).le
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (_root_.GD.N0232.N0719.N1004.d009794 triangle) p
  have hselected :
      (∑ i : Subtype (_root_.GD.N0232.N0719.N1004.d009794 triangle), p i) =
        ∑ j : Fin 3, p (triangle j) := by
    exact
      ((_root_.GD.N0232.N0719.N1004.d009796 triangle).sum_comp
        (fun i : Subtype (_root_.GD.N0232.N0719.N1004.d009794 triangle) => p i)).symm
  have hcomplement :
      0 ≤
        ∑ i : Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i),
          p i :=
    Finset.sum_nonneg fun i _ => hp0 i
  have hfull :
      (∑ i, p i) = 1 := by
    rw [show p =
        _root_.GD.N0232.N0719.N0900.d009109
          (⟨(fun _ => 0), t⟩ : _root_.GD.N0232.N0719.N0900.d009096 k) by
      exact
        _root_.GD.N0232.N0719.N0956.d010067
          hk (fun _ => 0) t ht]
    exact
      _root_.GD.N0232.N0719.N0900.d009131 hk
        (⟨(fun _ => 0), t⟩ : _root_.GD.N0232.N0719.N0900.d009096 k)
  unfold _root_.GD.N0232.N0719.N0951.d003585
  calc
    (∑ j : Fin 3, p (triangle j)) =
        ∑ i : Subtype (_root_.GD.N0232.N0719.N1004.d009794 triangle), p i :=
      hselected.symm
    _ ≤
        (∑ i : Subtype (_root_.GD.N0232.N0719.N1004.d009794 triangle), p i) +
          ∑ i : Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i),
            p i :=
      le_add_of_nonneg_right hcomplement
    _ = ∑ i, p i := hsplit
    _ = 1 := hfull





theorem d010388
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    {V : ℝ} (hV : 0 < V)
    (hv0V :
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0) : ℝ) ≤ V)
    (hv1V :
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1) : ℝ) ≤ V)
    (hv2V :
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2) : ℝ) ≤ V) :
    let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
    let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
    let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
    let τ := _root_.GD.N0232.N0719.N0954.d009348 hk t / r
    (if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) *
          (3 / 128 : ℝ) * r ^ 2 *
          _root_.GD.N0232.N0719.N0892.d003667 (q 0) (q 1) (q 2)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 0) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0)))
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 1) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1)))
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 2) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2))) /
          (τ + V) ≤
      -(∫ y,
          _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
            _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
        ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
  dsimp only
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  let τ := _root_.GD.N0232.N0719.N0954.d009348 hk t / r
  let χ : ℝ := if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0
  let v₀ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0)
  let v₁ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1)
  let v₂ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2)
  let I : ℝ :=
    ∫ z,
      _root_.GD.N0232.N0719.N0890.d003772 (q 0) (q 1) (q 2) τ z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₀ v₁ v₂
  have hq : ∀ j, 0 < q j :=
    _root_.GD.N0232.N0719.N0956.d010071
      hk triangle (fun _ => 0) t ht
  have hqsum :
      q 0 + q 1 + q 2 = 1 := by
    have :=
      _root_.GD.N0232.N0719.N0956.d010072
        hk triangle (fun _ => 0) t ht
    simpa only [q, Fin.sum_univ_three] using this
  have hτ : 0 < τ := div_pos
    (_root_.GD.N0232.N0719.N0956.d010063 hk t ht)
    (_root_.GD.N0232.N0719.N0956.d010070
      hk triangle (fun _ => 0) t ht)
  have hv₀ : v₀ ≠ 0 :=
    _root_.GD.N0232.N0719.N0904.d010386
      sizes hsizes scales hscales (triangle 0)
  have hv₁ : v₁ ≠ 0 :=
    _root_.GD.N0232.N0719.N0904.d010386
      sizes hsizes scales hscales (triangle 1)
  have hv₂ : v₂ ≠ 0 :=
    _root_.GD.N0232.N0719.N0904.d010386
      sizes hsizes scales hscales (triangle 2)
  have hI :
      I ≤
        -(3 / 128 : ℝ) *
          _root_.GD.N0232.N0719.N0892.d003667 (q 0) (q 1) (q 2)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 0) v₀)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 1) v₁)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 2) v₂) /
          (τ + V) := by
    exact
      _root_.GD.N0232.N0719.N0890.d003784
        (hq 0) (hq 1) (hq 2) hqsum
        hv₀ hv₁ hv₂ hτ hV hv0V hv1V hv2V
  have hχ : 0 ≤ χ := by
    dsimp [χ]
    split_ifs <;> norm_num
  have hcoef : 0 ≤ χ * r ^ 2 :=
    mul_nonneg hχ (sq_nonneg r)
  have hmul :=
    mul_le_mul_of_nonneg_left hI hcoef
  have hcross :
      (∫ y,
          _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
            _root_.GD.N0232.N0719.N1018.d010021 triangle
              (_root_.GD.N0232.N0719.N0902.d010367 t y)
        ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) =
        χ * r ^ 2 * I := by
    simpa only [p, r, q, τ, χ, v₀, v₁, v₂, I] using
      (_root_.GD.N0232.N0719.N0902.d010377
        hk sizes hsizes scales triangle t ht)
  change
    χ * (3 / 128 : ℝ) * r ^ 2 *
          _root_.GD.N0232.N0719.N0892.d003667 (q 0) (q 1) (q 2)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 0) v₀)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 1) v₁)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 2) v₂) /
          (τ + V) ≤
      -(∫ y,
          _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
            _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
        ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales)
  rw [hcross]
  change
    χ * (3 / 128 : ℝ) * r ^ 2 *
          _root_.GD.N0232.N0719.N0892.d003667 (q 0) (q 1) (q 2)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 0) v₀)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 1) v₁)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 2) v₂) /
          (τ + V) ≤ -(χ * r ^ 2 * I)
  calc
    χ * (3 / 128 : ℝ) * r ^ 2 *
          _root_.GD.N0232.N0719.N0892.d003667 (q 0) (q 1) (q 2)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 0) v₀)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 1) v₁)
            (_root_.GD.N0232.N0719.N0895.d003746
              (q 2) v₂) /
          (τ + V) =
        -(χ * r ^ 2 *
          (-(3 / 128 : ℝ) *
            _root_.GD.N0232.N0719.N0892.d003667 (q 0) (q 1) (q 2)
              (_root_.GD.N0232.N0719.N0895.d003746
                (q 0) v₀)
              (_root_.GD.N0232.N0719.N0895.d003746
                (q 1) v₁)
              (_root_.GD.N0232.N0719.N0895.d003746
                (q 2) v₂) /
            (τ + V))) := by ring
    _ ≤ -(χ * r ^ 2 * I) := neg_le_neg hmul














theorem d010389
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    {V rFloor : ℝ} (hV : 0 < V) (hfloor : 0 ≤ rFloor)
    (hbalanced :
      _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0954.d009349 hk t))
    (hfloorMass :
      rFloor ≤
        _root_.GD.N0232.N0719.N0951.d003585 triangle
          (_root_.GD.N0232.N0719.N0954.d009349 hk t))
    (w : Fin 3 → ℝ)
    (hv₀ :
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0) : ℝ) =
        V * w 0)
    (hv₁ :
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1) : ℝ) =
        V * w 1)
    (hv₂ :
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2) : ℝ) =
        V * w 2)
    (hw₀ : w 0 ≤ 1) (hw₁ : w 1 ≤ 1) (hw₂ : w 2 ≤ 1) :
    let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
    let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
    let ω := _root_.GD.N0232.N0719.N0954.d009348 hk t
    (3 / 128 : ℝ) * rFloor * r ^ 2 * V ^ 2 *
          _root_.GD.N0232.N0719.N0856.d009528 triangle p w / (ω + V) ≤
      -(∫ y,
          _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
            _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
        ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
  dsimp only
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  let ω := _root_.GD.N0232.N0719.N0954.d009348 hk t
  let τ := ω / r
  let v₀ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0)
  let v₁ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1)
  let v₂ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2)
  have hr : 0 < r :=
    _root_.GD.N0232.N0719.N0956.d010070
      hk triangle (fun _ => 0) t ht
  have hr1 : r ≤ 1 :=
    _root_.GD.N0232.N0719.N0904.d010387 hk triangle t ht
  have hω : 0 ≤ ω :=
    (_root_.GD.N0232.N0719.N0956.d010063 hk t ht).le
  have hv₀V : (v₀ : ℝ) ≤ V := by
    dsimp [v₀]
    rw [hv₀]
    nlinarith [hV]
  have hv₁V : (v₁ : ℝ) ≤ V := by
    dsimp [v₁]
    rw [hv₁]
    nlinarith [hV]
  have hv₂V : (v₂ : ℝ) ≤ V := by
    dsimp [v₂]
    rw [hv₂]
    nlinarith [hV]
  have hbase :=
    _root_.GD.N0232.N0719.N0904.d010388
      hk sizes hsizes scales hscales triangle t ht
      hV hv₀V hv₁V hv₂V
  dsimp only at hbase
  have hA0 :
      _root_.GD.N0232.N0719.N0892.d003667 (q 0) (q 1) (q 2)
          (_root_.GD.N0232.N0719.N0895.d003746 (q 0) v₀)
          (_root_.GD.N0232.N0719.N0895.d003746 (q 1) v₁)
          (_root_.GD.N0232.N0719.N0895.d003746 (q 2) v₂) =
        V ^ 2 * _root_.GD.N0232.N0719.N0856.d009528 triangle p w := by
    exact
      _root_.GD.N0232.N0719.N0884.d009603
        triangle p V w v₀ v₁ v₂
        (by simpa [v₀] using hv₀)
        (by simpa [v₁] using hv₁)
        (by simpa [v₂] using hv₂)
  have hmismatch :
      0 ≤ _root_.GD.N0232.N0719.N0856.d009528 triangle p w :=
    _root_.GD.N0232.N0719.N0856.d009544 hk triangle hbalanced w
  have hmass :
      rFloor * r ^ 2 / (ω + V) ≤
        r ^ 2 / (ω / r + V) :=
    _root_.GD.N0232.N0719.N0884.d009606
      hfloor hfloorMass hr hr1 hω hV
  have hcoef :
      0 ≤ (3 / 128 : ℝ) * V ^ 2 *
          _root_.GD.N0232.N0719.N0856.d009528 triangle p w := by
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hmass hcoef
  have hbase' :
      (3 / 128 : ℝ) * r ^ 2 * V ^ 2 *
            _root_.GD.N0232.N0719.N0856.d009528 triangle p w /
          (ω / r + V) ≤
        -(∫ y,
            _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
              _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
          ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
    simpa [p, r, q, ω, τ, v₀, v₁, v₂, hbalanced, hA0,
      mul_assoc] using hbase
  calc
    (3 / 128 : ℝ) * rFloor * r ^ 2 * V ^ 2 *
          _root_.GD.N0232.N0719.N0856.d009528 triangle p w / (ω + V) =
        ((3 / 128 : ℝ) * V ^ 2 *
            _root_.GD.N0232.N0719.N0856.d009528 triangle p w) *
          (rFloor * r ^ 2 / (ω + V)) := by ring
    _ ≤
        ((3 / 128 : ℝ) * V ^ 2 *
            _root_.GD.N0232.N0719.N0856.d009528 triangle p w) *
          (r ^ 2 / (ω / r + V)) :=
      hscaled
    _ =
        (3 / 128 : ℝ) * r ^ 2 * V ^ 2 *
          _root_.GD.N0232.N0719.N0856.d009528 triangle p w /
            (ω / r + V) := by ring
    _ ≤ _ := hbase'

end

end GD.N0232.N0719.N0904
