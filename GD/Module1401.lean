import GD.Module1399
import GD.Module1393











set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace GD.N0173
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0180 _root_.GD.N0181
open _root_.GD.N0193 _root_.GD.N0177
open _root_.GD.N0163 _root_.GD.N0164
open _root_.GD.N0172 _root_.GD.N0160


def d022532 (t : ℝ) : ℝ := min t (1 - t) / max t (1 - t)

theorem d022533 (t : ℝ) : _root_.GD.N0173.d022532 (1 - t) = _root_.GD.N0173.d022532 t := by
  simp only [_root_.GD.N0173.d022532, sub_sub_cancel]
  rw [min_comm (1 - t) t, max_comm (1 - t) t]

theorem d022534 {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / (130321 : ℝ)) : _root_.GD.N0173.d022532 t ≤ 1 / (130320 : ℝ) := by
  have hhalf : t ≤ 1 - t := by linarith
  have hden : 0 < 1 - t := by linarith
  rw [_root_.GD.N0173.d022532, min_eq_left hhalf, max_eq_right hhalf]
  apply (div_le_iff₀ hden).2
  nlinarith only [ht]

theorem d022535 : _root_.GD.N0181.d007269 19 ≤ 1 / (19 : ℝ) ^ 4 :=
  _root_.GD.N0181.d007290 (by norm_num : 16 ≤ (19 : ℕ))

theorem d022536 (i : _root_.GD.N0193.d007344 19) :
    _root_.GD.N0193.d007347 19 i ∈ Ioc (0 : ℝ) (_root_.GD.N0181.d007269 19) ∪ Ico (1 - _root_.GD.N0181.d007269 19) 1 := by
  have h0 := _root_.GD.N0193.d007358 (by norm_num : 2 ≤ (19 : ℕ)) i.1
  have hd := _root_.GD.N0193.d007360 (by norm_num : 2 ≤ (19 : ℕ)) i.1
  unfold _root_.GD.N0193.d007347
  split_ifs
  · exact Or.inl ⟨h0, hd⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

theorem d022537 (i : _root_.GD.N0193.d007344 19) :
    ∃ r : ℚ, (r : ℝ) = _root_.GD.N0193.d007347 19 i :=
  ⟨_root_.GD.N0193.d007349 19 i, _root_.GD.N0193.d007364 19 i⟩

theorem d022538 : Fintype.card (_root_.GD.N0193.d007344 19) = 12996 := by
  norm_num [_root_.GD.N0193.d007370, _root_.GD.N0193.d007343]

theorem d022539 : (Finset.univ.image (_root_.GD.N0193.d007347 19)).card = 12996 := by
  classical
  simpa [_root_.GD.N0193.d007343] using _root_.GD.N0193.d007373 (N := 19) (by norm_num)

theorem d022540 : _root_.GD.N0193.d007348 19 = 1 / (12996 : ℝ) := by
  norm_num [_root_.GD.N0193.d007348, _root_.GD.N0193.d007343]

theorem d022541 (i : _root_.GD.N0193.d007344 19) :
    _root_.GD.N0193.d007351 19 {_root_.GD.N0193.d007347 19 i} = ENNReal.ofReal (1 / (12996 : ℝ)) := by
  rw [_root_.GD.N0193.d007378 (by norm_num : 2 ≤ (19 : ℕ)), _root_.GD.N0173.d022540]


theorem d022542 :
    _root_.GD.N0193.d007351 19 (Ioc (0 : ℝ) (_root_.GD.N0181.d007269 19) ∪ Ico (1 - _root_.GD.N0181.d007269 19) 1)ᶜ = 0 := by
  rw [_root_.GD.N0193.d007351, Measure.sum_apply _
    ((measurableSet_Ioc.union measurableSet_Ico).compl)]
  apply ENNReal.tsum_eq_zero.mpr
  intro i
  have hi := _root_.GD.N0173.d022536 i
  have hnot : _root_.GD.N0193.d007347 19 i ∉ (Ioc (0 : ℝ) (_root_.GD.N0181.d007269 19) ∪ Ico (1 - _root_.GD.N0181.d007269 19) 1)ᶜ := by
    simpa only [Set.mem_compl_iff, not_not] using hi
  rw [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem hnot, smul_zero]

theorem d022543 (i : _root_.GD.N0193.d007344 19) :
    _root_.GD.N0173.d022532 (_root_.GD.N0193.d007347 19 i) ≤ 1 / (130320 : ℝ) := by
  have h0 := _root_.GD.N0193.d007358 (by norm_num : 2 ≤ (19 : ℕ)) i.1
  have hd := (_root_.GD.N0193.d007360 (by norm_num : 2 ≤ (19 : ℕ)) i.1).trans
    _root_.GD.N0173.d022535
  have hsmall : _root_.GD.N0193.d007346 19 i.1 ≤ 1 / (130321 : ℝ) := by
    norm_num at hd ⊢
    exact hd
  have hb := _root_.GD.N0173.d022534 h0.le hsmall
  unfold _root_.GD.N0193.d007347
  split_ifs
  · exact hb
  · simpa only [_root_.GD.N0173.d022533] using hb


theorem d022544 :
    (∫ t, _root_.GD.N0173.d022532 t ∂_root_.GD.N0193.d007351 19) ≤ 1 / (130320 : ℝ) := by
  rw [_root_.GD.N0164.d022437 (by norm_num : 2 ≤ (19 : ℕ))]
  calc
    _ ≤ ∑ _i : _root_.GD.N0193.d007344 19, _root_.GD.N0193.d007348 19 * (1 / (130320 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (_root_.GD.N0173.d022543 i)
        (_root_.GD.N0193.d007367 (by norm_num : 2 ≤ (19 : ℕ))).le
    _ = (∑ _i : _root_.GD.N0193.d007344 19, _root_.GD.N0193.d007348 19) * (1 / (130320 : ℝ)) := by
      rw [Finset.sum_mul]
    _ = 1 / (130320 : ℝ) := by
      rw [_root_.GD.N0193.d007374 (by norm_num : 2 ≤ (19 : ℕ)), one_mul]


theorem d022545 :
    (∫ t, _root_.GD.N0173.d022532 t ∂_root_.GD.N0193.d007351 19) ≤ 1 / (130320 : ℝ) ∧
    (1 : ℝ) / 130320 < 1 / 76 ∧
    (1 : ℝ) / 76 < _root_.GD.N0160.d022516 19 :=
  ⟨_root_.GD.N0173.d022544, by norm_num, _root_.GD.N0160.d022523⟩


theorem d022546 (g : _root_.GD.N0172.d022466) :
    _root_.GD.N0160.d022516 19 ≤
      ∫ t, _root_.GD.N0164.d022430 (_root_.GD.N0163.d022211 g.1) t ∂_root_.GD.N0193.d007351 19 := by
  letI : Nonempty (_root_.GD.N0193.d007344 19) :=
    ⟨(⟨0, _root_.GD.N0193.d007353 (by norm_num : 2 ≤ (19 : ℕ))⟩, 0)⟩
  rw [_root_.GD.N0164.d022439
    (by norm_num : 2 ≤ (19 : ℕ)), _root_.GD.N0160.d022517
    (by norm_num : 2 ≤ (19 : ℕ))]
  rw [← _root_.GD.N0163.d022209
    (fun _ : _root_.GD.N0193.d007344 19 => _root_.GD.N0193.d007348 19)
    (_root_.GD.N0177.d022414 (by norm_num : 2 ≤ (19 : ℕ)))
    (fun _ => _root_.GD.N0193.d007367 (by norm_num : 2 ≤ (19 : ℕ)))]
  exact _root_.GD.N0163.d022215
    (fun _ : _root_.GD.N0193.d007344 19 => _root_.GD.N0193.d007348 19)
    (_root_.GD.N0177.d022414 (by norm_num : 2 ≤ (19 : ℕ)))
    (fun _ => _root_.GD.N0193.d007367 (by norm_num : 2 ≤ (19 : ℕ)))
    g.1 g.property.1 g.property.2


theorem d022547 (g : _root_.GD.N0172.d022466) :
    ¬ (∀ i : _root_.GD.N0193.d007344 19,
      _root_.GD.N0180.d022173 (_root_.GD.N0177.d022414 (by norm_num : 2 ≤ (19 : ℕ)) i)
        (_root_.GD.N0163.d022211 g.1) ≤ _root_.GD.N0173.d022532 (_root_.GD.N0193.d007347 19 i)) := by
  intro hcap
  have hsum : (∫ t, _root_.GD.N0164.d022430 (_root_.GD.N0163.d022211 g.1) t ∂_root_.GD.N0193.d007351 19) ≤
      ∫ t, _root_.GD.N0173.d022532 t ∂_root_.GD.N0193.d007351 19 := by
    rw [_root_.GD.N0164.d022439
      (by norm_num : 2 ≤ (19 : ℕ)), _root_.GD.N0164.d022437
      (by norm_num : 2 ≤ (19 : ℕ))]
    unfold _root_.GD.N0163.d022185
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hcap i)
      (_root_.GD.N0193.d007367 (by norm_num : 2 ≤ (19 : ℕ))).le
  have hlower := _root_.GD.N0173.d022546 g
  have hupper := _root_.GD.N0173.d022544
  have hstrict := _root_.GD.N0160.d022523
  have hb : _root_.GD.N0160.d022516 19 ≤ 1 / (130320 : ℝ) := hlower.trans (hsum.trans hupper)
  exact (not_lt_of_ge hb) ((by norm_num : (1 : ℝ) / 130320 < 1 / 76).trans hstrict)


theorem d022548 :
    ¬ ∃ g : _root_.GD.N0172.d022466, ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      _root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 g.1) ≤ _root_.GD.N0173.d022532 t := by
  rintro ⟨g, hg⟩
  apply _root_.GD.N0173.d022547 g
  intro i
  simpa only [_root_.GD.N0177.d022414] using
    hg (_root_.GD.N0177.d022414 (by norm_num : 2 ≤ (19 : ℕ)) i)

end
end GD.N0173

#print axioms _root_.GD.N0173.d022533
#print axioms _root_.GD.N0173.d022534
#print axioms _root_.GD.N0173.d022535
#print axioms _root_.GD.N0173.d022536
#print axioms _root_.GD.N0173.d022537
#print axioms _root_.GD.N0173.d022538
#print axioms _root_.GD.N0173.d022539
#print axioms _root_.GD.N0173.d022540
#print axioms _root_.GD.N0173.d022541
#print axioms _root_.GD.N0173.d022542
#print axioms _root_.GD.N0173.d022543
#print axioms _root_.GD.N0173.d022544
#print axioms _root_.GD.N0173.d022545
#print axioms _root_.GD.N0173.d022546
#print axioms _root_.GD.N0173.d022547
#print axioms _root_.GD.N0173.d022548
