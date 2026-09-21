import GD.Module0649
import GD.Module0624
import GD.Module0687















open scoped BigOperators

namespace GD.N0232.N0719.N0956

noncomputable section

@[simp]
theorem d010060
    {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℝ) (i : _root_.GD.N0232.N0719.N0953.d003305 (k - 1)) :
    _root_.GD.N0232.N0719.N0954.d009346 hk t i =
      t (_root_.GD.N0232.N0719.N0954.d009344 k hk i) := by
  change
    (Equiv.piCongrLeft
        (fun _ : Fin k => ℝ)
        (_root_.GD.N0232.N0719.N0954.d009344 k hk)).symm t i = _
  rw [Equiv.piCongrLeft_symm_apply]


theorem d010061
    {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0953.d003312 (_root_.GD.N0232.N0719.N0954.d009346 hk t) =
      ∑ i, (t i)⁻¹ := by
  unfold _root_.GD.N0232.N0719.N0953.d003312
  calc
    (∑ i, (_root_.GD.N0232.N0719.N0954.d009346 hk t (Sum.inl i))⁻¹) +
          (_root_.GD.N0232.N0719.N0954.d009346 hk t (Sum.inr 0))⁻¹ =
        ∑ i : _root_.GD.N0232.N0719.N0953.d003305 (k - 1),
          (_root_.GD.N0232.N0719.N0954.d009346 hk t i)⁻¹ := by
            rw [Fintype.sum_sum_type]
            simp
    _ = ∑ i, (t i)⁻¹ := by
      exact Fintype.sum_equiv
        (_root_.GD.N0232.N0719.N0954.d009344 k hk) _ _
        (fun i => by rw [_root_.GD.N0232.N0719.N0956.d010060])




theorem d010062
    {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0954.d009348 hk t =
      (∑ i, (t i)⁻¹)⁻¹ := by
  unfold _root_.GD.N0232.N0719.N0954.d009348 _root_.GD.N0232.N0719.N0954.d009347
  rw [_root_.GD.N0232.N0719.N0953.d003318]
  unfold _root_.GD.N0232.N0719.N0953.d003313
  rw [_root_.GD.N0232.N0719.N0956.d010061 hk t]

theorem d010063
    {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    0 < _root_.GD.N0232.N0719.N0954.d009348 hk t := by
  rw [_root_.GD.N0232.N0719.N0956.d010062 hk t]
  apply inv_pos.mpr
  exact Finset.sum_pos
    (fun i _ => inv_pos.mpr (ht i))
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩


theorem d010064
    {k : ℕ} (hk : 0 < k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N0900.d009107 ⟨y, t⟩ ≠ 0 := by
  have hsum :
      0 < ∑ i, (t i)⁻¹ := by
    exact Finset.sum_pos
      (fun i _ => inv_pos.mpr (ht i))
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  unfold _root_.GD.N0232.N0719.N0900.d009107 _root_.GD.N0232.N0719.N0900.d009106
  simp_rw [_root_.GD.N0232.N0719.N0900.d009127 (ht _)]
  exact hsum.ne'



theorem d010065
    {k : ℕ} (y t : Fin k → ℝ)
    (ht : ∀ i, 0 < t i) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009106 ⟨y, t⟩ i = (t i)⁻¹ := by
  exact _root_.GD.N0232.N0719.N0900.d009127 (ht i)





theorem d010066
    {k : ℕ} (hk : 0 < k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (i : Fin k) :
    _root_.GD.N0232.N0719.N0954.d009349 hk t i =
      _root_.GD.N0232.N0719.N0900.d009108 ⟨y, t⟩ i := by
  have hsource :
      _root_.GD.N0232.N0719.N0954.d009346 hk t ∈ _root_.GD.N0232.N0719.N0953.d003310 (k - 1) := by
    intro j
    rw [_root_.GD.N0232.N0719.N0956.d010060]
    exact ht _
  have htotal :
      _root_.GD.N0232.N0719.N0900.d009107 ⟨y, t⟩ =
        ∑ j, (t j)⁻¹ := by
    unfold _root_.GD.N0232.N0719.N0900.d009107 _root_.GD.N0232.N0719.N0900.d009106
    simp_rw [_root_.GD.N0232.N0719.N0900.d009127 (ht _)]
  have hscale :=
    _root_.GD.N0232.N0719.N0956.d010062 hk t
  unfold _root_.GD.N0232.N0719.N0954.d009349 _root_.GD.N0232.N0719.N0954.d009347
  have hweight :
      _root_.GD.N0232.N0719.N0953.d003334
          (_root_.GD.N0232.N0719.N0953.d003314 (_root_.GD.N0232.N0719.N0954.d009346 hk t))
          ((_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i) =
        _root_.GD.N0232.N0719.N0953.d003313 (_root_.GD.N0232.N0719.N0954.d009346 hk t) /
          _root_.GD.N0232.N0719.N0954.d009346 hk t
            ((_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i) := by
    cases hindex :
        (_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i with
    | inl j =>
        simp [_root_.GD.N0232.N0719.N0953.d003334, _root_.GD.N0232.N0719.N0953.d003307, _root_.GD.N0232.N0719.N0953.d003314, hindex]
    | inr j =>
        fin_cases j
        rw [_root_.GD.N0232.N0719.N0953.d003334, _root_.GD.N0232.N0719.N0953.d003320 hsource]
        simp [hindex]
  rw [hweight, _root_.GD.N0232.N0719.N0956.d010060,
    Equiv.apply_symm_apply]
  change
    _root_.GD.N0232.N0719.N0954.d009348 hk t / t i =
      _root_.GD.N0232.N0719.N0900.d009108 ⟨y, t⟩ i
  rw [hscale]
  unfold _root_.GD.N0232.N0719.N0900.d009108
  rw [if_neg (_root_.GD.N0232.N0719.N0956.d010064 hk y t ht),
    _root_.GD.N0232.N0719.N0956.d010065 y t ht i, htotal]
  ring


theorem d010067
    {k : ℕ} (hk : 0 < k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N0954.d009349 hk t =
      _root_.GD.N0232.N0719.N0900.d009109 ⟨y, t⟩ := by
  funext i
  exact _root_.GD.N0232.N0719.N0956.d010066 hk y t ht i



theorem d010068
    {k : ℕ} (hk : 0 < k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0900.d009108 ⟨y, t⟩ i := by
  have htotal :
      0 < _root_.GD.N0232.N0719.N0900.d009107 ⟨y, t⟩ := by
    unfold _root_.GD.N0232.N0719.N0900.d009107 _root_.GD.N0232.N0719.N0900.d009106
    simp_rw [_root_.GD.N0232.N0719.N0900.d009127 (ht _)]
    exact Finset.sum_pos
      (fun j _ => inv_pos.mpr (ht j))
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  unfold _root_.GD.N0232.N0719.N0900.d009108
  rw [if_neg htotal.ne']
  exact div_pos
    (by
      rw [_root_.GD.N0232.N0719.N0956.d010065 y t ht i]
      exact inv_pos.mpr (ht i))
    htotal



theorem d010069
    {k : ℕ} (hk : 0 < k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0954.d009349 hk t i := by
  rw [_root_.GD.N0232.N0719.N0956.d010066 hk y t ht i]
  exact _root_.GD.N0232.N0719.N0956.d010068 hk y t ht i



theorem d010070
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    0 <
      _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0954.d009349 hk t) := by
  unfold _root_.GD.N0232.N0719.N0951.d003585
  exact Finset.sum_pos
    (fun j _ => _root_.GD.N0232.N0719.N0956.d010069 hk y t ht (triangle j))
    ⟨0, Finset.mem_univ _⟩

theorem d010071
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (j : Fin 3) :
    0 <
      _root_.GD.N0232.N0719.N0951.d003586 triangle
        (_root_.GD.N0232.N0719.N0954.d009349 hk t) j := by
  exact div_pos
    (_root_.GD.N0232.N0719.N0956.d010069 hk y t ht (triangle j))
    (_root_.GD.N0232.N0719.N0956.d010070 hk triangle y t ht)

theorem d010072
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    ∑ j,
      _root_.GD.N0232.N0719.N0951.d003586 triangle
        (_root_.GD.N0232.N0719.N0954.d009349 hk t) j = 1 := by
  unfold _root_.GD.N0232.N0719.N0951.d003586 _root_.GD.N0232.N0719.N0951.d003585
  rw [← Finset.sum_div]
  exact div_self
    (_root_.GD.N0232.N0719.N0956.d010070 hk triangle y t ht).ne'







theorem d010073
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N1018.d010012 triangle ⟨y, t⟩ =
      _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0954.d009349 hk t) := by
  unfold _root_.GD.N0232.N0719.N1018.d010012 _root_.GD.N0232.N0719.N0951.d003585
  apply Finset.sum_congr rfl
  intro j _
  exact
    (_root_.GD.N0232.N0719.N0956.d010066
      hk y t ht (triangle j)).symm





theorem d010074
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (j : Fin 3) :
    _root_.GD.N0232.N0719.N1018.d010013 triangle ⟨y, t⟩ j =
      _root_.GD.N0232.N0719.N0951.d003586 triangle
        (_root_.GD.N0232.N0719.N0954.d009349 hk t) j := by
  unfold _root_.GD.N0232.N0719.N1018.d010013 _root_.GD.N0232.N0719.N0951.d003586
  rw [_root_.GD.N0232.N0719.N0956.d010073
    hk triangle y t ht]
  exact congrArg
    (fun x : ℝ => x /
      _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0954.d009349 hk t))
    (_root_.GD.N0232.N0719.N0956.d010066
      hk y t ht (triangle j)).symm






theorem d010075
    {k : ℕ} (hk : 0 < k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N1018.d010019 ⟨y, t⟩ ↔
      _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0954.d009349 hk t) := by
  unfold _root_.GD.N0232.N0719.N1018.d010019 _root_.GD.N0232.N0719.N0951.d003580
    _root_.GD.N0232.N0719.N0951.d003578 _root_.GD.N0232.N0719.N0951.d003579
  constructor
  · intro h i
    simpa [_root_.GD.N0232.N0719.N0956.d010066 hk y t ht i] using h i
  · intro h i
    simpa [_root_.GD.N0232.N0719.N0956.d010066 hk y t ht i] using h i



theorem d010076
    {k : ℕ} (hk : 0 < k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N1018.d010020 ⟨y, t⟩ =
      @ite ℝ
        (_root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0954.d009349 hk t))
        (Classical.propDecidable _) 1 0 := by
  classical
  unfold _root_.GD.N0232.N0719.N1018.d010020
  rw [_root_.GD.N0232.N0719.N0956.d010075 hk y t ht]










theorem d010077
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N1018.d010015 triangle ⟨y, t⟩ =
      _root_.GD.N0232.N0719.N0954.d009348 hk t /
        _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0954.d009349 hk t) := by
  have htotal :
      0 < ∑ i, (t i)⁻¹ := by
    exact Finset.sum_pos
      (fun i _ => inv_pos.mpr (ht i))
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hselected :
      0 < ∑ j, (t (triangle j))⁻¹ := by
    exact Finset.sum_pos
      (fun j _ => inv_pos.mpr (ht (triangle j)))
      ⟨0, Finset.mem_univ _⟩
  rw [_root_.GD.N0232.N0719.N0956.d010062 hk t]
  unfold _root_.GD.N0232.N0719.N1018.d010015 _root_.GD.N0232.N0719.N0951.d003585
  simp_rw [_root_.GD.N0232.N0719.N0956.d010066 hk y t ht]
  unfold _root_.GD.N0232.N0719.N0900.d009108
  simp_rw [if_neg (_root_.GD.N0232.N0719.N0956.d010064 hk y t ht)]
  simp_rw [_root_.GD.N0232.N0719.N0956.d010065 y t ht]
  unfold _root_.GD.N0232.N0719.N0900.d009107 _root_.GD.N0232.N0719.N0900.d009106
  simp_rw [_root_.GD.N0232.N0719.N0900.d009127 (ht _)]
  rw [← Finset.sum_div]
  field_simp [htotal.ne', hselected.ne']

end

end GD.N0232.N0719.N0956
