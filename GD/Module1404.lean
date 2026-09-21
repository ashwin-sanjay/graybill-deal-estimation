import GD.Module1399








set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0194
noncomputable section
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0180 _root_.GD.N0163 _root_.GD.N0172
open _root_.GD.N0201 _root_.GD.N0160
open _root_.GD.N0193 _root_.GD.N0177


def d022558 (g : _root_.GD.N0172.d022466) : ℝ≥0∞ :=
  ⨆ t : _root_.GD.N0232.N0720.N1441.d013676, ENNReal.ofReal (_root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 g.1))

def d022559 : ℝ≥0∞ := ⨅ g : _root_.GD.N0172.d022466, _root_.GD.N0194.d022558 g

theorem d022560 (g : _root_.GD.N0172.d022466)
    (hg : _root_.GD.N0194.d022558 g ≠ ⊤) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 g.1) ≤ (_root_.GD.N0194.d022558 g).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hg).mp
  exact le_iSup (fun s : _root_.GD.N0232.N0720.N1441.d013676 =>
    ENNReal.ofReal (_root_.GD.N0180.d022173 s (_root_.GD.N0163.d022211 g.1))) t

theorem d022561 {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 < p i)
    (hsum : (∑ i, p i) = 1) (g : _root_.GD.N0172.d022466) :
    ENNReal.ofReal (_root_.GD.N0163.d022186 p t) ≤ _root_.GD.N0194.d022558 g := by
  classical
  by_cases hg : _root_.GD.N0194.d022558 g = ⊤
  · rw [hg]
    exact le_top
  apply (ENNReal.ofReal_le_iff_le_toReal hg).mpr
  have hmin := _root_.GD.N0163.d022215 p t hp g.1 g.property.1 g.property.2
  rw [_root_.GD.N0163.d022209 p t hp] at hmin
  have hsumBound : _root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022211 g.1) ≤
      ∑ i, p i * (_root_.GD.N0194.d022558 g).toReal := by
    unfold _root_.GD.N0163.d022185
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (_root_.GD.N0194.d022560 g hg (t i)) (hp i).le)
  rw [← Finset.sum_mul, hsum, one_mul] at hsumBound
  exact hmin.trans hsumBound

theorem d022562 {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 < p i)
    (hsum : (∑ i, p i) = 1) :
    ENNReal.ofReal (_root_.GD.N0163.d022186 p t) ≤ _root_.GD.N0194.d022559 := by
  exact le_iInf (fun g => _root_.GD.N0194.d022561 p t hp hsum g)

theorem d022563 :
    _root_.GD.N0194.d022558 _root_.GD.N0201.d022510 ≤ ENNReal.ofReal (Real.pi / 4) := by
  apply iSup_le
  intro t
  exact ENNReal.ofReal_le_ofReal (_root_.GD.N0201.d022512 t).le

theorem d022564 :
    _root_.GD.N0194.d022559 ≤ ENNReal.ofReal (Real.pi / 4) :=
  (iInf_le _root_.GD.N0194.d022558 _root_.GD.N0201.d022510).trans _root_.GD.N0194.d022563

theorem d022565 : _root_.GD.N0194.d022559 ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top _root_.GD.N0194.d022564


theorem d022566 {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 < p i)
    (hsum : (∑ i, p i) = 1) :
    0 ≤ _root_.GD.N0163.d022186 p t ∧
      _root_.GD.N0163.d022186 p t ≤ _root_.GD.N0194.d022559.toReal ∧
      _root_.GD.N0194.d022559.toReal ≤ Real.pi / 4 ∧
      _root_.GD.N0163.d022186 p t < Real.pi / 4 := by
  refine ⟨_root_.GD.N0163.d022208 p t hp,
    (ENNReal.ofReal_le_iff_le_toReal _root_.GD.N0194.d022565).mp
      (_root_.GD.N0194.d022562 p t hp hsum), ?_,
    _root_.GD.N0201.d022515 p t hp hsum⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top _root_.GD.N0194.d022564
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi / 4)] using h

theorem d022567 {N : ℕ} (hN : 2 ≤ N) :
    ENNReal.ofReal (_root_.GD.N0160.d022516 N) ≤ _root_.GD.N0194.d022559 := by
  letI : Nonempty (_root_.GD.N0193.d007344 N) := ⟨(⟨0, _root_.GD.N0193.d007353 hN⟩, 0)⟩
  rw [_root_.GD.N0160.d022517 hN]
  exact _root_.GD.N0194.d022562
    (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN)
    (fun _ => _root_.GD.N0193.d007367 hN) (_root_.GD.N0193.d007374 hN)

theorem d022568 : _root_.GD.N0194.d022559 = ENNReal.ofReal (Real.pi / 4) := by
  apply le_antisymm _root_.GD.N0194.d022564
  apply le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp _root_.GD.N0160.d022525)
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact _root_.GD.N0194.d022567 hN

theorem d022569 : _root_.GD.N0194.d022558 _root_.GD.N0201.d022510 = _root_.GD.N0194.d022559 := by
  apply le_antisymm
  · rw [_root_.GD.N0194.d022568]
    exact _root_.GD.N0194.d022563
  · exact iInf_le _root_.GD.N0194.d022558 _root_.GD.N0201.d022510


def d022570 {I : Type*} [Fintype I] (p : I → ℝ)
    (t : I → _root_.GD.N0232.N0720.N1441.d013676) : Prop :=
  (∀ i, 0 < p i) ∧ (∑ i, p i) = 1 ∧
    (∀ i, ∃ q : ℚ, (q : ℝ) = p i) ∧
    (∀ i, ∃ q : ℚ, (q : ℝ) = (t i : ℝ))


def d022571 : Set ℝ≥0∞ :=
  {x | ∃ (I : Type) (hI : Fintype I) (_ : Nonempty I)
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676),
    @_root_.GD.N0194.d022570 I hI p t ∧ x = ENNReal.ofReal (@_root_.GD.N0163.d022186 I hI p t)}

theorem d022572 {x : ℝ≥0∞} (hx : x ∈ _root_.GD.N0194.d022571) :
    x < ENNReal.ofReal (Real.pi / 4) := by
  rcases hx with ⟨I, hI, hne, p, t, hp, rfl⟩
  letI : Fintype I := hI
  letI : Nonempty I := hne
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < Real.pi / 4)).mpr
    (_root_.GD.N0201.d022515 p t hp.1 hp.2.1)

theorem d022573 {N : ℕ} (hN : 2 ≤ N) :
    ENNReal.ofReal (_root_.GD.N0160.d022516 N) ∈ _root_.GD.N0194.d022571 := by
  let hne : Nonempty (_root_.GD.N0193.d007344 N) := ⟨(⟨0, _root_.GD.N0193.d007353 hN⟩, 0)⟩
  refine ⟨_root_.GD.N0193.d007344 N, inferInstance, hne, (fun _ => _root_.GD.N0193.d007348 N), _root_.GD.N0177.d022414 hN,
    ?_, congrArg ENNReal.ofReal (_root_.GD.N0160.d022517 hN)⟩
  refine ⟨(fun _ => _root_.GD.N0193.d007367 hN), _root_.GD.N0193.d007374 hN, ?_, ?_⟩
  · intro i
    exact ⟨_root_.GD.N0193.d007350 N, _root_.GD.N0193.d007366 N⟩
  · intro i
    exact ⟨_root_.GD.N0193.d007349 N i, _root_.GD.N0193.d007364 N i⟩

theorem d022574 : sSup _root_.GD.N0194.d022571 = ENNReal.ofReal (Real.pi / 4) := by
  apply le_antisymm
  · exact sSup_le (fun _ hx => (_root_.GD.N0194.d022572 hx).le)
  · apply le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp _root_.GD.N0160.d022525)
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact le_sSup (_root_.GD.N0194.d022573 hN)

theorem d022575 :
    sSup _root_.GD.N0194.d022571 = _root_.GD.N0194.d022559 ∧
      _root_.GD.N0194.d022559 = ENNReal.ofReal (Real.pi / 4) ∧
      _root_.GD.N0194.d022558 _root_.GD.N0201.d022510 = _root_.GD.N0194.d022559 ∧
      ∀ x ∈ _root_.GD.N0194.d022571, x < _root_.GD.N0194.d022559 := by
  refine ⟨_root_.GD.N0194.d022574.trans _root_.GD.N0194.d022568.symm,
    _root_.GD.N0194.d022568, _root_.GD.N0194.d022569, ?_⟩
  intro x hx
  rw [_root_.GD.N0194.d022568]
  exact _root_.GD.N0194.d022572 hx

end
end GD.N0194

#print axioms _root_.GD.N0194.d022560
#print axioms _root_.GD.N0194.d022561
#print axioms _root_.GD.N0194.d022562
#print axioms _root_.GD.N0194.d022563
#print axioms _root_.GD.N0194.d022564
#print axioms _root_.GD.N0194.d022565
#print axioms _root_.GD.N0194.d022566
#print axioms _root_.GD.N0194.d022567
#print axioms _root_.GD.N0194.d022568
#print axioms _root_.GD.N0194.d022569
#print axioms _root_.GD.N0194.d022572
#print axioms _root_.GD.N0194.d022573
#print axioms _root_.GD.N0194.d022574
#print axioms _root_.GD.N0194.d022575
