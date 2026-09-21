import GD.Module1874
import GD.Module1895

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0372
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1066 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1228 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0686



theorem d030802
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) (hd : Measurable d) :
    1 ≤ _root_.GD.N0232.N0720.N1228.d016745 2 2 (by decide) (by decide) d := by
  by_contra h
  have hlt : _root_.GD.N0232.N0720.N1228.d016745 2 2 (by decide) (by decide) d < 1 :=
    lt_of_not_ge h
  have htop : _root_.GD.N0232.N0720.N1228.d016745 2 2 (by decide) (by decide) d ≠ ⊤ :=
    ne_top_of_lt hlt
  let q := (_root_.GD.N0232.N0720.N1228.d016745 2 2 (by decide) (by decide) d).toReal
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q < 1 := by
    simpa only [q, ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal htop ENNReal.one_ne_top).mpr hlt
  apply _root_.GD.N0101.N0378.d030662 d hd hq hq1
  intro θ
  apply (_root_.GD.N0232.N0720.N1228.d016746 2 2 (by decide) (by decide) θ d q hq).mp
  rw [ENNReal.ofReal_toReal htop]
  exact le_iSup (fun θ => _root_.GD.N0232.N0720.N1228.d016744 2 2 (by decide) (by decide) θ d) θ



theorem d030803
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 2 2) :
    _root_.GD.N0232.N0720.N1228.d016752 2 2 (by decide) (by decide) d ≤ 0 := by
  have hpoint : ∀ θ, _root_.GD.N0232.N0720.N1228.d016744 2 2 (by decide) (by decide) θ d ≠ ⊤ :=
    fun θ => ENNReal.div_ne_top (hd.2 θ)
      (_root_.GD.N0232.N0720.N1066.d014322 2 2 (by decide) (by decide) θ)
  have h := _root_.GD.N0230.N0686.d003547
    (_root_.GD.N0232.N0720.N1228.d016744 2 2 (by decide) (by decide)) d 1 ENNReal.one_ne_top
    hpoint (_root_.GD.N0101.N0372.d030802 d hd.1)
  simpa only [_root_.GD.N0232.N0720.N1228.d016752, _root_.GD.N0230.N0686.d003544, ENNReal.toReal_one, sub_self,
    EReal.coe_zero] using h



theorem d030804 :
    _root_.GD.N0232.N0720.N1228.d016752 2 2 (by decide) (by decide)
      (_root_.GD.N0232.N0720.N1080.d014176 2 2 (by decide) (by decide)) = 0 := by
  have hs := _root_.GD.N0232.N0720.N1221.d015562
    2 2 (by decide) (by decide)
  apply le_antisymm (_root_.GD.N0101.N0372.d030803 _ ⟨hs.1.1, hs.2⟩)
  apply le_iInf
  intro θ
  have hle : _root_.GD.N0232.N0720.N1228.d016744 2 2 (by decide) (by decide) θ
      (_root_.GD.N0232.N0720.N1080.d014176 2 2 (by decide) (by decide)) ≤ 1 := by
    unfold _root_.GD.N0232.N0720.N1228.d016744
    rw [ENNReal.div_le_iff (_root_.GD.N0232.N0720.N1066.d014322 2 2 (by decide) (by decide) θ)
      (_root_.GD.N0232.N0720.N1066.d014323 2 2 (by decide) (by decide) θ), one_mul,
      _root_.GD.N0232.N0720.N1215.d014295]
    exact (_root_.GD.N0232.N0720.N1080.d014186 2 2 (by decide) (by decide) θ).le
  apply (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top 1))
    (Or.inl (EReal.coe_ne_bot 1))).mpr
  simpa only [EReal.coe_ennreal_one, EReal.coe_one] using
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr hle



theorem d030805 :
    _root_.GD.N0232.N0720.N1228.d016753 2 2 (by decide) (by decide) (_root_.GD.N0232.N0720.N1256.d015551 2 2) = 0 ∧
    _root_.GD.N0232.N0720.N1228.d016753 2 2 (by decide) (by decide)
      (_root_.GD.N0232.N0720.N1256.d015552 2 2) = 0 := by
  have hs := _root_.GD.N0232.N0720.N1221.d015562
    2 2 (by decide) (by decide)
  have hclass : ∀ C : Set (_root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ),
      (∀ d ∈ C, d ∈ _root_.GD.N0232.N0720.N1256.d015551 2 2) →
      _root_.GD.N0232.N0720.N1080.d014176 2 2 (by decide) (by decide) ∈ C →
      _root_.GD.N0232.N0720.N1228.d016753 2 2 (by decide) (by decide) C = 0 := by
    intro C hC hseed
    apply le_antisymm
    · exact iSup_le fun d => iSup_le fun hd =>
        _root_.GD.N0101.N0372.d030803 d (hC d hd)
    · rw [← _root_.GD.N0101.N0372.d030804]
      exact le_iSup_of_le (_root_.GD.N0232.N0720.N1080.d014176 2 2 (by decide) (by decide))
        (le_iSup_of_le hseed le_rfl)
  exact ⟨hclass _ (fun _ h => h) ⟨hs.1.1, hs.2⟩,
    hclass _ (fun _ h => ⟨h.1.1, h.2⟩) hs⟩



theorem d030806
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (0 < _root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015551 m n) ∧
      0 < _root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015552 m n)) ↔
      m ≤ 3 ∧ n ≤ 3 ∧ (m ≠ 2 ∨ n ≠ 2) := by
  by_cases h22 : m = 2 ∧ n = 2
  · rcases h22 with ⟨rfl, rfl⟩
    have hz := _root_.GD.N0101.N0372.d030805
    simp [hz.1, hz.2]
  · have hnot22 : m ≠ 2 ∨ n ≠ 2 := by omega
    have h := _root_.GD.N0041.d030799
      m n hm hn hnot22
    constructor
    · intro hp
      exact ⟨(h.mp hp).1, (h.mp hp).2, hnot22⟩
    · rintro ⟨hm3, hn3, _⟩
      exact h.mpr ⟨hm3, hn3⟩



theorem d030807
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015551 m n) = 0 ∧
      _root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015552 m n) = 0) ↔
      (m = 2 ∧ n = 2) ∨ 4 ≤ m ∨ 4 ≤ n := by
  by_cases h22 : m = 2 ∧ n = 2
  · rcases h22 with ⟨rfl, rfl⟩
    have hz := _root_.GD.N0101.N0372.d030805
    simp [hz.1, hz.2]
  · have hnot22 : m ≠ 2 ∨ n ≠ 2 := by omega
    simpa only [h22, false_or] using
      _root_.GD.N0041.d030800 m n hm hn hnot22

end
end GD.N0101.N0372

#print axioms _root_.GD.N0101.N0372.d030802
#print axioms _root_.GD.N0101.N0372.d030803
#print axioms _root_.GD.N0101.N0372.d030804
#print axioms _root_.GD.N0101.N0372.d030805
#print axioms _root_.GD.N0101.N0372.d030806
#print axioms _root_.GD.N0101.N0372.d030807
