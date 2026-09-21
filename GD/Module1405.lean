import GD.Module1393
import GD.Module1404















set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace GD.N0170
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0180 _root_.GD.N0163 _root_.GD.N0172
open _root_.GD.N0164 _root_.GD.N0194 _root_.GD.N0201



def d022576 (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ g : _root_.GD.N0172.d022466,
    ENNReal.ofReal (∫ r, _root_.GD.N0164.d022430 (_root_.GD.N0163.d022211 g.1) r ∂μ)




theorem d022577 {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 < p i) :
    _root_.GD.N0170.d022576 (_root_.GD.N0164.d022432 p t) = ENNReal.ofReal (_root_.GD.N0163.d022186 p t) := by
  unfold _root_.GD.N0170.d022576
  simp_rw [_root_.GD.N0164.d022435 p t (fun i => (hp i).le)]
  exact (_root_.GD.N0172.d022482 p t hp).symm


theorem d022578 {I : Type*} [Fintype I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0172.d022466) :
    Integrable (_root_.GD.N0164.d022430 (_root_.GD.N0163.d022211 g.1)) (_root_.GD.N0164.d022432 p t) :=
  _root_.GD.N0164.d022434 p t (_root_.GD.N0163.d022211 g.1)



theorem d022579 {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 < p i)
    (hsum : (∑ i, p i) = 1) :
    _root_.GD.N0170.d022576 (_root_.GD.N0164.d022432 p t) < ENNReal.ofReal (Real.pi / 4) := by
  rw [_root_.GD.N0170.d022577 p t hp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < Real.pi / 4)).mpr
    (_root_.GD.N0201.d022515 p t hp hsum)



def d022580 : Set (Measure ℝ) :=
  {μ | ∃ (I : Type) (hI : Fintype I) (_ : Nonempty I)
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676),
    @_root_.GD.N0194.d022570 I hI p t ∧ μ = @_root_.GD.N0164.d022432 I hI p t}

theorem d022581 {μ : Measure ℝ}
    (hμ : μ ∈ _root_.GD.N0170.d022580) : IsProbabilityMeasure μ := by
  rcases hμ with ⟨I, hI, hne, p, t, hp, rfl⟩
  letI : Fintype I := hI
  exact _root_.GD.N0164.d022433 p t (fun i => (hp.1 i).le) hp.2.1

theorem d022582 {μ : Measure ℝ}
    (hμ : μ ∈ _root_.GD.N0170.d022580) (g : _root_.GD.N0172.d022466) :
    Integrable (_root_.GD.N0164.d022430 (_root_.GD.N0163.d022211 g.1)) μ := by
  rcases hμ with ⟨I, hI, hne, p, t, hp, rfl⟩
  letI : Fintype I := hI
  exact _root_.GD.N0170.d022578 p t g


def d022583 : Set ℝ≥0∞ :=
  _root_.GD.N0170.d022576 '' _root_.GD.N0170.d022580



theorem d022584 :
    _root_.GD.N0170.d022583 = _root_.GD.N0194.d022571 := by
  ext x
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    rcases hμ with ⟨I, hI, hne, p, t, hp, rfl⟩
    letI : Fintype I := hI
    letI : Nonempty I := hne
    exact ⟨I, hI, hne, p, t, hp, _root_.GD.N0170.d022577 p t hp.1⟩
  · rintro ⟨I, hI, hne, p, t, hp, rfl⟩
    letI : Fintype I := hI
    letI : Nonempty I := hne
    exact ⟨_root_.GD.N0164.d022432 p t, ⟨I, hI, hne, p, t, hp, rfl⟩,
      _root_.GD.N0170.d022577 p t hp.1⟩

theorem d022585 :
    sSup _root_.GD.N0170.d022583 = ENNReal.ofReal (Real.pi / 4) := by
  rw [_root_.GD.N0170.d022584]
  exact _root_.GD.N0194.d022574

theorem d022586 {μ : Measure ℝ}
    (hμ : μ ∈ _root_.GD.N0170.d022580) :
    _root_.GD.N0170.d022576 μ < _root_.GD.N0194.d022559 := by
  rw [_root_.GD.N0194.d022568]
  rcases hμ with ⟨I, hI, hne, p, t, hp, rfl⟩
  letI : Fintype I := hI
  letI : Nonempty I := hne
  exact _root_.GD.N0170.d022579 p t hp.1 hp.2.1



theorem d022587 :
    sSup _root_.GD.N0170.d022583 = _root_.GD.N0194.d022559 ∧
      _root_.GD.N0194.d022559 = ENNReal.ofReal (Real.pi / 4) ∧
      _root_.GD.N0194.d022558 _root_.GD.N0201.d022510 = _root_.GD.N0194.d022559 ∧
      ∀ μ ∈ _root_.GD.N0170.d022580, _root_.GD.N0170.d022576 μ < _root_.GD.N0194.d022559 := by
  exact ⟨_root_.GD.N0170.d022585.trans _root_.GD.N0194.d022568.symm,
    _root_.GD.N0194.d022568, _root_.GD.N0194.d022569,
    fun _ hμ => _root_.GD.N0170.d022586 hμ⟩

end
end GD.N0170

#print axioms _root_.GD.N0170.d022577
#print axioms _root_.GD.N0170.d022578
#print axioms _root_.GD.N0170.d022579
#print axioms _root_.GD.N0170.d022581
#print axioms _root_.GD.N0170.d022582
#print axioms _root_.GD.N0170.d022584
#print axioms _root_.GD.N0170.d022585
#print axioms _root_.GD.N0170.d022586
#print axioms _root_.GD.N0170.d022587
