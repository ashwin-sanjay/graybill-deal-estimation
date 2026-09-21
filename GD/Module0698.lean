import GD.Module0688
import GD.Module0670
import GD.Module0263
import GD.Module0697

























open MeasureTheory Set
open scoped BigOperators NNReal

namespace GD.N0232.N0719.N0905

noncomputable section

local instance d010269 {k : ℕ} (p : Fin k → ℝ) :
    Decidable (_root_.GD.N0232.N0719.N0951.d003580 p) :=
  Classical.propDecidable _



def d010270
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ)
    (z : ℝ × (ℝ × ℝ)) : ℝ :=
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  let τ := _root_.GD.N0232.N0719.N0954.d009348 hk t / r
  (if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) * r *
      _root_.GD.N0232.N0719.N0886.d003654 (q 0) (q 1) (q 2) z /
    (τ + _root_.GD.N0232.N0719.N0881.d003572
      (q 0) (q 1) (q 2) z.1 z.2.1 z.2.2)

@[fun_prop]
theorem d010271
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0905.d010270 hk triangle t) := by
  unfold _root_.GD.N0232.N0719.N0905.d010270 _root_.GD.N0232.N0719.N0886.d003654 _root_.GD.N0232.N0719.N1016.d003609
    _root_.GD.N0232.N0719.N0886.d003650 _root_.GD.N0232.N0719.N0886.d003651 _root_.GD.N0232.N0719.N0886.d003652 _root_.GD.N0232.N0719.N0881.d003572 _root_.GD.N0232.N0719.N0881.d003570
  fun_prop



theorem d010272
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N1018.d010018 triangle ⟨y, t⟩ =
      _root_.GD.N0232.N0719.N0886.d003654
        (_root_.GD.N0232.N0719.N0951.d003586 triangle
          (_root_.GD.N0232.N0719.N0954.d009349 hk t) 0)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle
          (_root_.GD.N0232.N0719.N0954.d009349 hk t) 1)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle
          (_root_.GD.N0232.N0719.N0954.d009349 hk t) 2)
        (_root_.GD.N0232.N0719.N1004.d009807 triangle y) := by
  simp only [_root_.GD.N0232.N0719.N1018.d010018, _root_.GD.N0232.N0719.N1018.d010014,
    _root_.GD.N0232.N0719.N0886.d003654, _root_.GD.N0232.N0719.N0886.d003650, _root_.GD.N0232.N0719.N0886.d003651, _root_.GD.N0232.N0719.N0886.d003652,
    _root_.GD.N0232.N0719.N1004.d009808]
  rw [_root_.GD.N0232.N0719.N0956.d010074
      hk triangle y t ht 0,
    _root_.GD.N0232.N0719.N0956.d010074
      hk triangle y t ht 1,
    _root_.GD.N0232.N0719.N0956.d010074
      hk triangle y t ht 2]



theorem d010273
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N1018.d010017 triangle ⟨y, t⟩ =
      _root_.GD.N0232.N0719.N0881.d003572
        (_root_.GD.N0232.N0719.N0951.d003586 triangle
          (_root_.GD.N0232.N0719.N0954.d009349 hk t) 0)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle
          (_root_.GD.N0232.N0719.N0954.d009349 hk t) 1)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle
          (_root_.GD.N0232.N0719.N0954.d009349 hk t) 2)
        (_root_.GD.N0232.N0719.N1004.d009807 triangle y).1
        (_root_.GD.N0232.N0719.N1004.d009807 triangle y).2.1
        (_root_.GD.N0232.N0719.N1004.d009807 triangle y).2.2 := by
  rw [_root_.GD.N0232.N0719.N1020.d010265]
  simp only [_root_.GD.N0232.N0719.N1019.d003790,
    _root_.GD.N0232.N0719.N1019.d003789,
    _root_.GD.N0232.N0719.N0881.d003572, _root_.GD.N0232.N0719.N0881.d003570,
    _root_.GD.N0232.N0719.N1018.d010014, _root_.GD.N0232.N0719.N1004.d009808]
  rw [_root_.GD.N0232.N0719.N0956.d010074
      hk triangle y t ht 0,
    _root_.GD.N0232.N0719.N0956.d010074
      hk triangle y t ht 1,
    _root_.GD.N0232.N0719.N0956.d010074
      hk triangle y t ht 2]





theorem d010274
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N1018.d010021 triangle ⟨y, t⟩ =
      _root_.GD.N0232.N0719.N0905.d010270 hk triangle t
        (_root_.GD.N0232.N0719.N1004.d009807 triangle y) := by
  unfold _root_.GD.N0232.N0719.N1018.d010021 _root_.GD.N0232.N0719.N0905.d010270
  rw [_root_.GD.N0232.N0719.N0956.d010076 hk y t ht,
    _root_.GD.N0232.N0719.N0956.d010073
      hk triangle y t ht,
    _root_.GD.N0232.N0719.N0956.d010077
      hk triangle y t ht,
    _root_.GD.N0232.N0719.N0905.d010272 hk triangle y t ht,
    _root_.GD.N0232.N0719.N0905.d010273
      hk triangle y t ht]


theorem d010275
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    (∑ j : Fin 3,
        _root_.GD.N0232.N0719.N0954.d009349 hk t (triangle j) * y (triangle j)) =
      _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0954.d009349 hk t) *
        _root_.GD.N0232.N0719.N0886.d003653
          (_root_.GD.N0232.N0719.N0951.d003586 triangle
            (_root_.GD.N0232.N0719.N0954.d009349 hk t) 0)
          (_root_.GD.N0232.N0719.N0951.d003586 triangle
            (_root_.GD.N0232.N0719.N0954.d009349 hk t) 1)
          (_root_.GD.N0232.N0719.N0951.d003586 triangle
            (_root_.GD.N0232.N0719.N0954.d009349 hk t) 2)
          (_root_.GD.N0232.N0719.N1004.d009807 triangle y) := by
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  have hr : 0 < r :=
    _root_.GD.N0232.N0719.N0956.d010070 hk triangle y t ht
  simp only [Fin.sum_univ_succ, Fin.sum_univ_two,
    _root_.GD.N0232.N0719.N0886.d003653, _root_.GD.N0232.N0719.N0886.d003650, _root_.GD.N0232.N0719.N0886.d003651, _root_.GD.N0232.N0719.N0886.d003652,
    _root_.GD.N0232.N0719.N1004.d009808, _root_.GD.N0232.N0719.N0951.d003586]
  dsimp [p, r] at hr ⊢
  field_simp [hr.ne']
  ring





theorem d010276
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N0900.d009110 ⟨y, t⟩ =
      _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0954.d009349 hk t) *
          _root_.GD.N0232.N0719.N0886.d003653
            (_root_.GD.N0232.N0719.N0951.d003586 triangle
              (_root_.GD.N0232.N0719.N0954.d009349 hk t) 0)
            (_root_.GD.N0232.N0719.N0951.d003586 triangle
              (_root_.GD.N0232.N0719.N0954.d009349 hk t) 1)
            (_root_.GD.N0232.N0719.N0951.d003586 triangle
              (_root_.GD.N0232.N0719.N0954.d009349 hk t) 2)
            (_root_.GD.N0232.N0719.N1004.d009807 triangle y) +
        _root_.GD.N0232.N0719.N1004.d009812 triangle
          (_root_.GD.N0232.N0719.N0954.d009349 hk t)
          (_root_.GD.N0232.N0719.N1004.d009800 triangle y) := by
  classical
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (_root_.GD.N0232.N0719.N1004.d009794 triangle)
      (fun i : Fin k => p i * y i)
  have hselected :
      (∑ i : Subtype (_root_.GD.N0232.N0719.N1004.d009794 triangle),
          p i * y i) =
        ∑ j : Fin 3, p (triangle j) * y (triangle j) := by
    exact ((_root_.GD.N0232.N0719.N1004.d009796 triangle).sum_comp
      (fun i : Subtype (_root_.GD.N0232.N0719.N1004.d009794 triangle) =>
        p i * y i)).symm
  have hcomplement :
      (∑ i : Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i),
          p i * y i) =
        _root_.GD.N0232.N0719.N1004.d009812 triangle p
          (_root_.GD.N0232.N0719.N1004.d009800 triangle y) := by
    simp [_root_.GD.N0232.N0719.N1004.d009812]
  have hwhole :
      _root_.GD.N0232.N0719.N0900.d009110 ⟨y, t⟩ = ∑ i, p i * y i := by
    unfold _root_.GD.N0232.N0719.N0900.d009110
    apply Finset.sum_congr rfl
    intro i _
    simpa [p] using congrArg (fun w : ℝ => w * y i)
      (_root_.GD.N0232.N0719.N0956.d010066
        hk y t ht i).symm
  rw [hwhole, ← hsplit, hselected, hcomplement,
    _root_.GD.N0232.N0719.N0905.d010275
      hk triangle y t ht]






theorem d010277
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
    let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
    let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
    let τ := _root_.GD.N0232.N0719.N0954.d009348 hk t / r
    r * _root_.GD.N0232.N0719.N0886.d003653 (q 0) (q 1) (q 2)
          (_root_.GD.N0232.N0719.N1004.d009807 triangle y) *
        _root_.GD.N0232.N0719.N0905.d010270 hk triangle t
          (_root_.GD.N0232.N0719.N1004.d009807 triangle y) =
      (if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) * r ^ 2 *
        _root_.GD.N0232.N0719.N0890.d003772
          (q 0) (q 1) (q 2) τ
          (_root_.GD.N0232.N0719.N1004.d009807 triangle y) := by
  dsimp only
  unfold _root_.GD.N0232.N0719.N0905.d010270
    _root_.GD.N0232.N0719.N0890.d003772
    _root_.GD.N0232.N0719.N0889.d003757
  ring

end

end GD.N0232.N0719.N0905
