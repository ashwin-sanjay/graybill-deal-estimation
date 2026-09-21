import GD.Module0552
import GD.Module1372
import GD.Module1865
import GD.Module1432

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0076.N0309

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0230.N0611
open _root_.GD.N0096.N0343
open _root_.GD.N0076.N0313

theorem d030675 : _root_.GD.N0077.N0315.d008223 :=
  _root_.GD.N0077.N0315.d008224

theorem d030676 (c a b : ℝ≥0∞) (hc : c ≠ 0) (hfinite : c ≠ ⊤) :
    (c * a ≤ c * b ↔ a ≤ b) ∧ (c * a < c * b ↔ a < b) :=
  ⟨ENNReal.mul_le_mul_iff_right hc hfinite, ENNReal.mul_lt_mul_iff_right hc hfinite⟩

theorem d030677 : _root_.GD.N0077.N0315.d008223 ∧
    ∀ (k : ℕ) (sizes : Fin k → ℕ), 2 ≤ k → (∀ i, 2 ≤ sizes i) →
      ∀ (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ),
        (∀ z, _root_.GD.N0076.N0311.N0760.d022078 sizes z →
          f z = _root_.GD.N0076.N0311.N0760.d022079 sizes z) →
        ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f =
            _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
              (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
  refine ⟨_root_.GD.N0076.N0309.d030675, ?_⟩
  intro k sizes hk hsizes f hf θ
  exact _root_.GD.N0076.N0311.N0760.d022089 sizes (by omega) hsizes f hf θ

theorem d030678
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (hno : ¬ _root_.GD.N0076.N0313.d030592 m n d) :
    0 < _root_.GD.N0096.N0343.d022808 m n d := by
  have hmem := _root_.GD.N0232.N0720.N1215.d014285 m n d hd.1
    (hd.2 _root_.GD.N0232.N0720.N1080.d014169)
  let p := hmem.toLp d
  have hp : _root_.GD.N0232.N0720.N1159.d014637 m n p := by
    intro θ
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n θ d hmem]
    exact hd.2 θ
  by_contra hpos
  have hz : _root_.GD.N0096.N0343.d022808 m n d = 0 :=
    le_antisymm (le_of_not_gt hpos) (_root_.GD.N0096.N0343.d022815 m n d)
  have hzero : _root_.GD.N0096.N0343.d022808 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) = 0 := by
    rw [_root_.GD.N0096.N0343.d022818 m n d hmem]
    exact hz
  have hfixed := (_root_.GD.N0096.N0343.d022819 m n p hp).mp hzero
  have hall := _root_.GD.N0232.N0720.N1482.d015167 (m := m) (n := n) p hp hfixed.1 hfixed.2
  obtain ⟨e, he, hae, hcov⟩ := (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn p hp).mp hall
  apply hno
  refine ⟨e, he, hcov, ?_⟩
  have href : e =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1214.d014265 m n p := hae _root_.GD.N0232.N0720.N1080.d014169
  exact href.trans ((_root_.GD.N0232.N0720.N1214.d014267 m n p).trans hmem.coeFn_toLp)

theorem d030679 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d) :
    _root_.GD.N0076.N0313.d030569 m n hm hn ≤
      _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d := by
  classical
  by_cases hfinite : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≠ ⊤
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0076.N0313.d030568 m n hm hn)
      (show d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n from ⟨hd, hfinite⟩)
  · push Not at hfinite
    obtain ⟨θ, hθ⟩ := hfinite
    have htop : _root_.GD.N0076.N0313.d030568 m n hm hn θ d = ⊤ := by
      rw [_root_.GD.N0076.N0313.d030568, hθ,
        ENNReal.top_div_of_ne_top (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)]
    exact le_trans le_top (htop ▸ le_iSup
      (fun η ↦ _root_.GD.N0076.N0313.d030568 m n hm hn η d) θ)

theorem d030680 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n,
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d < _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      _root_.GD.N0076.N0313.d030591 m n d ∧
      ¬ _root_.GD.N0076.N0313.d030592 m n d ∧
      _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d =
        _root_.GD.N0076.N0313.d030569 m n hm hn ∧
      (∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
        _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d ≤
          _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) e) ∧
      0 < _root_.GD.N0096.N0343.d022808 m n d := by
  obtain ⟨d, hd, hstrict, hterminal, hno, hvalue⟩ :=
    _root_.GD.N0076.N0313.d030596 m n hm hn
  refine ⟨d, hd, hstrict, hterminal, hno, hvalue, ?_,
    _root_.GD.N0076.N0309.d030678 m n hm hn d hd hno⟩
  intro e he
  rw [hvalue]
  exact _root_.GD.N0076.N0309.d030679 m n hm hn e he

theorem d030681 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0076.N0313.d030568 m n hm hn θ d =
      _root_.GD.N0232.N0720.N1080.d014197 m n θ d / _root_.GD.N0232.N0720.N1080.d014197 m n θ
        (_root_.GD.N0096.N0341.d021956 m n) := by
  change _root_.GD.N0232.N0720.N1080.d014197 m n θ d / _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ = _
  rw [_root_.GD.N0096.N0341.d021966
    m n hm hn θ, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn θ]
  rfl

theorem d030682
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable d ∧
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d < _root_.GD.N0232.N0720.N1080.d014197 m n θ
        (_root_.GD.N0096.N0341.d021956 m n)) ∧
      _root_.GD.N0076.N0313.d030591 m n d ∧ 0 < _root_.GD.N0096.N0343.d022808 m n d ∧
      ∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
        (⨆ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d / _root_.GD.N0232.N0720.N1080.d014197 m n θ
          (_root_.GD.N0096.N0341.d021956 m n)) ≤
        (⨆ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ e / _root_.GD.N0232.N0720.N1080.d014197 m n θ
          (_root_.GD.N0096.N0341.d021956 m n)) := by
  obtain ⟨d, hd, hstrict, hterminal, _, _, hoptimal, henergy⟩ :=
    _root_.GD.N0076.N0309.d030680 m n hm hn
  refine ⟨d, hd.1, ?_, hterminal, henergy, ?_⟩
  · intro θ
    rw [_root_.GD.N0096.N0341.d021966
      m n hm hn θ]
    exact hstrict θ
  · intro e he
    simpa only [_root_.GD.N0230.N0611.d003516, _root_.GD.N0076.N0309.d030681 m n hm hn] using hoptimal e he

end
end GD.N0076.N0309

#print axioms _root_.GD.N0076.N0309.d030675
#print axioms _root_.GD.N0076.N0309.d030676
#print axioms _root_.GD.N0076.N0309.d030677
#print axioms _root_.GD.N0076.N0309.d030678
#print axioms _root_.GD.N0076.N0309.d030679
#print axioms _root_.GD.N0076.N0309.d030680
#print axioms _root_.GD.N0076.N0309.d030681
#print axioms _root_.GD.N0076.N0309.d030682
