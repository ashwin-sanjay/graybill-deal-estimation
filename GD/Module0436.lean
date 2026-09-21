import GD.Module0434

set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Topology

namespace GD.N0101.N0383
noncomputable section

open _root_.GD.N0101.N0369

def d006746 (δ M r : ℝ) : ℝ :=
  M * (1 - δ * r) ^ 2 * (1 + r) ^ (-(5 / 2 : ℝ)) *
    (1 - r) * (1 - 2 * δ * r) ^ 2

theorem d006747 (δ M : ℝ) :
    ContinuousAt (_root_.GD.N0101.N0383.d006746 δ M) 0 := by
  have hp : ContinuousAt (fun r : ℝ => (1 + r) ^ (-(5 / 2 : ℝ))) 0 :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))
  unfold _root_.GD.N0101.N0383.d006746
  fun_prop


theorem d006748 {δ M q : ℝ} (hq : q < M) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ q < _root_.GD.N0101.N0383.d006746 δ M r := by
  have hq0 : q < _root_.GD.N0101.N0383.d006746 δ M 0 := by
    simpa [_root_.GD.N0101.N0383.d006746] using hq
  have hevent : ∀ᶠ r in 𝓝 (0 : ℝ), q < _root_.GD.N0101.N0383.d006746 δ M r :=
    continuousAt_const.eventually_lt (_root_.GD.N0101.N0383.d006747 δ M) hq0
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hevent
  let r := min (u / 2) (1 / 2)
  have hr : 0 < r := lt_min (by linarith [hlu.2]) (by norm_num)
  have hru : r < u := (min_le_left _ _).trans_lt (by linarith [hlu.2])
  exact ⟨r, hr, min_le_right _ _, hsub ⟨hlu.1.trans hr, hru⟩⟩

def d006749 (δ η : ℝ) : ℝ := (η * δ ^ (5 / 2 : ℝ) / 2) ^ (2 / 3 : ℝ)

def d006750 (δ η : ℝ) : ℝ := max (_root_.GD.N0101.N0383.d006749 δ η) (3 / η)

theorem d006751 {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    0 < _root_.GD.N0101.N0383.d006749 δ η := by
  unfold _root_.GD.N0101.N0383.d006749
  exact Real.rpow_pos_of_pos (div_pos (mul_pos hη (Real.rpow_pos_of_pos hδ _))
    (by norm_num)) _


theorem d006752 {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    (2 / 3 : ℝ) * (_root_.GD.N0101.N0383.d006749 δ η) ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) = η / 3 := by
  have hb : 0 ≤ η * δ ^ (5 / 2 : ℝ) / 2 :=
    (div_pos (mul_pos hη (Real.rpow_pos_of_pos hδ _)) (by norm_num)).le
  have hpow : (_root_.GD.N0101.N0383.d006749 δ η) ^ (3 / 2 : ℝ) = η * δ ^ (5 / 2 : ℝ) / 2 := by
    unfold _root_.GD.N0101.N0383.d006749
    rw [← Real.rpow_mul hb]
    norm_num
  have hcancel : δ ^ (5 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hδ]
    norm_num
  rw [hpow]
  calc
    _ = (η / 3) * (δ ^ (5 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ))) := by ring
    _ = _ := by rw [hcancel, mul_one]

theorem d006753 {δ η : ℝ} (hη : 0 < η) :
    1 / _root_.GD.N0101.N0383.d006750 δ η ≤ η / 3 := by
  calc
    _ ≤ 1 / (3 / η) := one_div_le_one_div_of_le
      (div_pos (by norm_num) hη) (le_max_right _ _)
    _ = _ := by field_simp [hη.ne']

theorem d006754 {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    (2 / 3 : ℝ) * (_root_.GD.N0101.N0383.d006749 δ η) ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) +
      1 / _root_.GD.N0101.N0383.d006750 δ η ≤ (2 / 3 : ℝ) * η := by
  rw [_root_.GD.N0101.N0383.d006752 hδ hη]
  linarith [_root_.GD.N0101.N0383.d006753 (δ := δ) hη]



theorem d006755 {q : ℝ} (hq : q < 1) :
    ∃ δ ε c η H R : ℝ,
      0 < δ ∧ δ < 1 / 2 ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧ 1 ≤ c ∧
      ε ≤ δ * (c - 1) ∧ 0 < η ∧ η < 1 ∧ 0 < H ∧ H ≤ R ∧
      (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) + 1 / R ≤
        (2 / 3 : ℝ) * η ∧
      q < _root_.GD.N0101.N0369.d006733 δ * (1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ)) *
        (1 - η) * (1 - 2 * ε) ^ 2 := by
  obtain ⟨δ, hδ, hδhalf, hmass⟩ := _root_.GD.N0101.N0369.d006738 hq
  obtain ⟨r, hr, hrhalf, hretain⟩ := _root_.GD.N0101.N0383.d006748 (δ := δ) hmass
  refine ⟨δ, δ * r, 1 + r, r, _root_.GD.N0101.N0383.d006749 δ r, _root_.GD.N0101.N0383.d006750 δ r,
    hδ, hδhalf, mul_pos hδ hr, ?_, ?_, ?_, hr, ?_,
    _root_.GD.N0101.N0383.d006751 hδ hr, le_max_left _ _, _root_.GD.N0101.N0383.d006754 hδ hr, ?_⟩
  · have hrone : r ≤ 1 := by linarith
    exact (mul_le_of_le_one_right hδ.le hrone).trans hδhalf.le
  · linarith
  · ring_nf
    exact le_rfl
  · linarith
  · simpa only [_root_.GD.N0101.N0383.d006746, mul_assoc] using hretain

end
end GD.N0101.N0383

#print axioms _root_.GD.N0101.N0383.d006748
#print axioms _root_.GD.N0101.N0383.d006752
#print axioms _root_.GD.N0101.N0383.d006753
#print axioms _root_.GD.N0101.N0383.d006754
#print axioms _root_.GD.N0101.N0383.d006755
