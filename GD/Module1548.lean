import GD.Module1547

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0092
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0968
open _root_.GD.N0213.N0502
open _root_.GD.N0230.N0611

variable (k : ℕ) (sizes : Fin k → ℕ)

theorem d023972 :
    _root_.GD.N0213.N0502.d022051 k sizes ≤
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) := by
  apply le_iInf
  intro e
  apply le_iInf
  intro he
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
    (_root_.GD.N0092.d023969 k sizes he)

theorem d023973
    (hV : _root_.GD.N0213.N0502.d022051 k sizes = ⊤) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) =
      _root_.GD.N0213.N0502.d022051 k sizes := by
  exact le_antisymm (by rw [hV]; exact le_top)
    (_root_.GD.N0092.d023972 k sizes)




theorem d023974
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (hV : _root_.GD.N0213.N0502.d022051 k sizes = ⊤) :
    ∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0213.N0502.d022051 k sizes := by
  have hs := _root_.GD.N0232.N0719.N0968.d012201 k sizes hk hn
  let s := _root_.GD.N0232.N0719.N0859.d010816 k sizes hk hn
  have hsFin : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := ⟨hs.1.1, hs.2⟩
  let e := _root_.GD.N0232.N0719.N0970.d012314 k sizes s hsFin
  have he : e ∈ _root_.GD.N0092.d023968 k sizes :=
    ⟨_root_.GD.N0232.N0719.N0970.d012316 k sizes s hsFin,
      _root_.GD.N0232.N0719.N0970.d012321 k sizes s hsFin (_root_.GD.N0232.N0719.N0970.d012329 k sizes hk hn),
      _root_.GD.N0232.N0719.N0970.d012317 k sizes s hsFin⟩
  refine ⟨e, he, le_antisymm (by rw [hV]; exact le_top) ?_⟩
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
    (_root_.GD.N0092.d023969 k sizes he)





theorem d023975
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) =
      _root_.GD.N0213.N0502.d022051 k sizes ↔
    _root_.GD.N0213.N0502.d022051 k sizes = ⊤ ∨
      ∃ s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ, Measurable s ∧
        _root_.GD.N0232.N0719.N0970.d012310 k sizes s ∧ _root_.GD.N0232.N0719.N0962.d012187 k sizes s ≠ ⊤ := by
  constructor
  · intro h
    by_cases hV : _root_.GD.N0213.N0502.d022051 k sizes = ⊤
    · exact Or.inl hV
    · right
      have hW : _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) < ⊤ := by
        rw [h]
        exact lt_top_iff_ne_top.mpr hV
      change (⨅ f ∈ _root_.GD.N0092.d023968 k sizes,
        _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) f) < ⊤ at hW
      obtain ⟨s, hs⟩ := iInf_lt_iff.mp hW
      obtain ⟨hs, hsfinite⟩ := iInf_lt_iff.mp hs
      exact ⟨s, hs.1.1, hs.2.1, ne_top_of_lt hsfinite⟩
  · rintro (hV | ⟨s, hs, hstrict, hfinite⟩)
    · exact _root_.GD.N0092.d023973 k sizes hV
    · exact _root_.GD.N0092.d023970 k sizes hk hn s
        (_root_.GD.N0213.N0502.d022053 k sizes hk hn ⟨hs, fun θ => (hstrict θ).le⟩) hstrict hfinite




theorem d023976
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) = ⊤ ∨
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) =
      _root_.GD.N0213.N0502.d022051 k sizes := by
  by_cases hW : _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) = ⊤
  · exact Or.inl hW
  · right
    apply (_root_.GD.N0092.d023975 k sizes hk hn).mpr
    right
    have hlt : _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) < ⊤ :=
      lt_top_iff_ne_top.mpr hW
    change (⨅ f ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) f) < ⊤ at hlt
    obtain ⟨s, hs⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hs, hsfinite⟩ := iInf_lt_iff.mp hs
    exact ⟨s, hs.1.1, hs.2.1, ne_top_of_lt hsfinite⟩

end
end GD.N0092

#print axioms _root_.GD.N0092.d023974
#print axioms _root_.GD.N0092.d023975
#print axioms _root_.GD.N0092.d023976
