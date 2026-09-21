import GD.Module0393
import GD.Module0983
import GD.Module1079

set_option autoImplicit false
set_option warningAsError true

open Filter Topology MeasureTheory
open scoped ENNReal

namespace GD.N0035.N0301

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1139 _root_.GD.N0232.N0720.N1141
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1226
open _root_.GD.N0230.N0608





theorem d022823 {m n : ℕ} (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (approx : ℕ → ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (upper lower : ℕ → ℚ)
    (hu : ∀ N, ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ (upper N : ℝ))
    (hl : ∀ N, (lower N : ℝ) ≤ ‖_root_.GD.N0232.N0720.N1139.d017232 s N‖ ^ 2)
    (hlim : Tendsto (fun N => ((upper N - lower N : ℚ) : ℝ)) atTop (𝓝 0))
    (happrox : ∀ N j, ‖approx N j - _root_.GD.N0232.N0720.N1139.d017232 s N‖ ≤
      (_root_.GD.N0035.d006053 j : ℝ)) :
    (∀ j : ℕ, ‖approx (_root_.GD.N0035.d006056 (fun N => upper N - lower N)
      (_root_.GD.N0035.d006058 _ hlim) j) (j + 1) -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ≤ (_root_.GD.N0035.d006053 j : ℝ)) ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
  refine ⟨?_, (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.1⟩
  exact _root_.GD.N0035.d006061 _ _ approx upper lower
    (_root_.GD.N0232.N0720.N1141.d017277 s) hu hl hlim happrox


theorem d022824 {m n : ℕ} (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (base : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value base)
    (approx : ℕ → ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (upper lower : ℕ → ℚ)
    (hu : ∀ N, ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ (upper N : ℝ))
    (hl : ∀ N, (lower N : ℝ) ≤ ‖_root_.GD.N0232.N0720.N1139.d017232 s N‖ ^ 2)
    (hlim : Tendsto (fun N => ((upper N - lower N : ℚ) : ℝ)) atTop (𝓝 0))
    (happrox : ∀ N j, ‖approx N j - _root_.GD.N0232.N0720.N1139.d017232 s N‖ ≤
      (_root_.GD.N0035.d006053 j : ℝ)) :
    (∀ j : ℕ, ‖approx (_root_.GD.N0035.d006056 (fun N => upper N - lower N)
      (_root_.GD.N0035.d006058 _ hlim) j) (j + 1) -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ≤ (_root_.GD.N0035.d006053 j : ℝ)) ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ∧
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) base := by
  obtain ⟨hname, hterminal⟩ := _root_.GD.N0035.N0301.d022823 s approx upper lower hu hl hlim happrox
  exact ⟨hname, hterminal,
    _root_.GD.N0232.N0720.N1159.d014636 m n s.value base hstrict⟩



theorem d022825 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (approx : ℕ → ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (upper lower : ℕ → ℚ)
    (hu : ∀ N, ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ (upper N : ℝ))
    (hl : ∀ N, (lower N : ℝ) ≤ ‖_root_.GD.N0232.N0720.N1139.d017232 s N‖ ^ 2)
    (hlim : Tendsto (fun N => ((upper N - lower N : ℚ) : ℝ)) atTop (𝓝 0))
    (happrox : ∀ N j, ‖approx N j - _root_.GD.N0232.N0720.N1139.d017232 s N‖ ≤
      (_root_.GD.N0035.d006053 j : ℝ)) :
    (∀ j : ℕ, ‖approx (_root_.GD.N0035.d006056 (fun N => upper N - lower N)
      (_root_.GD.N0035.d006058 _ hlim) j) (j + 1) -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ≤ (_root_.GD.N0035.d006053 j : ℝ)) ∧
    Measurable (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) ∧
    (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) <
      _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
    (∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value))) →
      ∀ θ, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) := by
  obtain ⟨hname, hterminal, hstrictp⟩ := _root_.GD.N0035.N0301.d022824 s
    (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict approx upper lower hu hl hlim happrox
  refine ⟨hname, _root_.GD.N0232.N0720.N1214.d014266 m n _, ?_,
    _root_.GD.N0232.N0720.N1226.d015581 m n _ hterminal⟩
  intro θ
  rw [_root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
  exact hstrictp θ

end
end GD.N0035.N0301

#print axioms _root_.GD.N0035.N0301.d022823
#print axioms _root_.GD.N0035.N0301.d022824

#print axioms _root_.GD.N0035.N0301.d022825
