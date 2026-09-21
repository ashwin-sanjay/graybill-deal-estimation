import GD.Module1893
import GD.Module1188

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0053
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1066 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1228 _root_.GD.N0232.N0720.N1101
open _root_.GD.N0082
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0686

theorem d030789 :
    ∃ (J : ℕ) (f : _root_.GD.N0232.N0720.N1080.d014170 3 2 → ℝ), 1≤J ∧ f ∈ _root_.GD.N0232.N0720.N1256.d015552 3 2 ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 2 θ f ≤
        ENNReal.ofReal (_root_.GD.N0082.d030598 J)*_root_.GD.N0232.N0720.N1066.d014320 3 2 (by omega) (by omega) θ := by
  obtain ⟨J,f,hJ,hf,hcap⟩ := _root_.GD.N0053.d030787
  refine ⟨J,f ∘ _root_.GD.N0232.N0720.N1101.d019094 3 2,hJ,?_,?_⟩
  · refine ⟨⟨hf.1.1.comp (_root_.GD.N0232.N0720.N1101.d019096 3 2),?_⟩,?_⟩
    · intro b a ha ω
      exact hf.1.2 b a ha (_root_.GD.N0232.N0720.N1101.d019094 3 2 ω)
    · intro θ
      rw [_root_.GD.N0232.N0720.N1101.d019101 3 2 θ f hf.1.1]
      exact hf.2 _
  · intro θ
    rw [_root_.GD.N0232.N0720.N1101.d019101 3 2 θ f hf.1.1]
    have hb := _root_.GD.N0232.N0720.N1101.d019106 3 2 (by omega) (by omega) θ
    rw [_root_.GD.N0232.N0720.N1080.d014199 3 2 (by omega) (by omega),
      _root_.GD.N0232.N0720.N1080.d014199 2 3 (by omega) (by omega)] at hb
    change _root_.GD.N0232.N0720.N1080.d014182 3 2 θ (_root_.GD.N0232.N0720.N1080.d014180 3 2 (by omega) (by omega)) =
      _root_.GD.N0232.N0720.N1080.d014182 2 3 (_root_.GD.N0232.N0720.N1043.d019058 θ)
        (_root_.GD.N0232.N0720.N1080.d014180 2 3 (by omega) (by omega)) at hb
    change _ ≤ ENNReal.ofReal (_root_.GD.N0082.d030598 J)*
      _root_.GD.N0232.N0720.N1080.d014182 3 2 θ (_root_.GD.N0232.N0720.N1080.d014180 3 2 (by omega) (by omega))
    rw [hb]
    exact hcap _

theorem d030790 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ f ≤
      ENNReal.ofReal c*_root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ) :
    0 < _root_.GD.N0232.N0720.N1228.d016752 m n hm hn f := by
  have hw : _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn) f ≤ ENNReal.ofReal c := by
    apply iSup_le
    intro θ
    exact (ENNReal.div_le_iff (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)).mpr (hcap θ)
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw
  have hreal : (_root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn) f).toReal < 1 :=
    (ENNReal.toReal_le_of_le_ofReal hc hw).trans_lt hc1
  change 0 < _root_.GD.N0230.N0686.d003544 (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn) f
  rw [_root_.GD.N0230.N0686.d003548 _ _ hfinite]
  exact_mod_cast (sub_pos.mpr hreal)

theorem d030791 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hf : f ∈ _root_.GD.N0232.N0720.N1256.d015552 m n)
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ f ≤
      ENNReal.ofReal c*_root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ) :
    0 < _root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015551 m n) ∧
    0 < _root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015552 m n) := by
  have hg := _root_.GD.N0053.d030790 m n hm hn f hc hc1 hcap
  exact ⟨hg.trans_le (le_iSup_of_le f (le_iSup_of_le ⟨hf.1.1,hf.2⟩ le_rfl)),
    hg.trans_le (le_iSup_of_le f (le_iSup_of_le hf le_rfl))⟩

theorem d030792 :
    0 < _root_.GD.N0232.N0720.N1228.d016753 2 3 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015551 2 3) ∧
    0 < _root_.GD.N0232.N0720.N1228.d016753 2 3 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015552 2 3) := by
  obtain ⟨J,f,_hJ,hf,hcap⟩ := _root_.GD.N0053.d030787
  exact _root_.GD.N0053.d030791 2 3 (by omega) (by omega) f hf
    (_root_.GD.N0082.d030599 J) (_root_.GD.N0082.d030600 J) hcap

theorem d030793 :
    0 < _root_.GD.N0232.N0720.N1228.d016753 3 2 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015551 3 2) ∧
    0 < _root_.GD.N0232.N0720.N1228.d016753 3 2 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015552 3 2) := by
  obtain ⟨J,f,_hJ,hf,hcap⟩ := _root_.GD.N0053.d030789
  exact _root_.GD.N0053.d030791 3 2 (by omega) (by omega) f hf
    (_root_.GD.N0082.d030599 J) (_root_.GD.N0082.d030600 J) hcap

end
end GD.N0053

#print axioms _root_.GD.N0053.d030789
#print axioms _root_.GD.N0053.d030792
#print axioms _root_.GD.N0053.d030793
