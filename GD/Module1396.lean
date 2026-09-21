import GD.Module1395
import GD.Module1392
import GD.Module0477

















set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators Interval ENNReal

namespace GD.N0172
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0163 _root_.GD.N0174
open _root_.GD.N0158 _root_.GD.N0177
open _root_.GD.N0181 _root_.GD.N0167 _root_.GD.N0171
open _root_.GD.N0193


abbrev d022466 :=
  {g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ // Measurable g ∧ ∀ p, g p ∈ Icc (0 : ℝ) 1}

def d022467 : _root_.GD.N0172.d022466 :=
  ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩

instance : Nonempty _root_.GD.N0172.d022466 := ⟨_root_.GD.N0172.d022467⟩


def d022468 (A T : ℝ) : ℝ :=
  ⨅ g : _root_.GD.N0172.d022466, _root_.GD.N0174.d022397 A T g.1


def d022469 (A T : ℝ) : ℝ≥0∞ :=
  ⨅ g : _root_.GD.N0172.d022466, ENNReal.ofReal (_root_.GD.N0174.d022397 A T g.1)

theorem d022470 {A T : ℝ} (hA : 0 < A) (hT : 0 < T)
    (g : _root_.GD.N0172.d022466) : 0 ≤ _root_.GD.N0174.d022397 A T g.1 := by
  unfold _root_.GD.N0174.d022397
  apply mul_nonneg
  · exact one_div_nonneg.mpr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hT.le)
  · apply intervalIntegral.integral_nonneg (by linarith : A ≤ A + T)
    intro r hr
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
    exact _root_.GD.N0174.d022399 (hA.trans_le hr.1) g.1 hp


theorem d022471 {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    BddBelow (Set.range (fun g : _root_.GD.N0172.d022466 => _root_.GD.N0174.d022397 A T g.1)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨g, rfl⟩
  exact _root_.GD.N0172.d022470 hA hT g

theorem d022472 {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    0 ≤ _root_.GD.N0172.d022468 A T :=
  le_ciInf (fun g => _root_.GD.N0172.d022470 hA hT g)

theorem d022473 {A T : ℝ} (hA : 0 < A) (hT : 0 < T)
    (g : _root_.GD.N0172.d022466) : _root_.GD.N0172.d022468 A T ≤ _root_.GD.N0174.d022397 A T g.1 :=
  ciInf_le (_root_.GD.N0172.d022471 hA hT) g

theorem d022474 (A T : ℝ) :
    ENNReal.ofReal (_root_.GD.N0172.d022468 A T) = _root_.GD.N0172.d022469 A T :=
  ENNReal.ofReal_iInf (fun g : _root_.GD.N0172.d022466 => _root_.GD.N0174.d022397 A T g.1)

theorem d022475 (A T : ℝ) :
    _root_.GD.N0172.d022469 A T ≠ ⊤ := by
  rw [← _root_.GD.N0172.d022474]
  exact ENNReal.ofReal_ne_top

theorem d022476 {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    (_root_.GD.N0172.d022469 A T).toReal = _root_.GD.N0172.d022468 A T := by
  rw [← _root_.GD.N0172.d022474,
    ENNReal.toReal_ofReal (_root_.GD.N0172.d022472 hA hT)]


theorem d022477 {eta a b A T : ℝ}
    (heta : 0 < eta) (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b)
    (hA : Real.log 2 < A) (hwindow : Real.log (b / a) < T) :
    _root_.GD.N0165.d007234 (Real.exp (-A)) eta a *
      (1 - Real.log (b / a) / T) *
      (_root_.GD.N0203.d007249 eta a b -
        Real.exp (-A) * _root_.GD.N0203.d007250 eta a b) ≤ _root_.GD.N0172.d022468 A T := by
  apply le_ciInf
  intro g
  exact _root_.GD.N0158.d022465 heta hhalf ha hab hA hwindow
    g.1 g.property.1 g.property.2

section FinitePacket
variable {I : Type*} [Fintype I] [Nonempty I]
variable (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 < p i)


def d022478 : _root_.GD.N0172.d022466 :=
  ⟨fun x => _root_.GD.N0163.d022181 p t x,
    (_root_.GD.N0163.d022192 p t).comp measurable_subtype_coe,
    fun x => _root_.GD.N0163.d022196 p t hp x⟩


theorem d022479 :
    _root_.GD.N0163.d022211 (_root_.GD.N0172.d022478 p t hp).1 = _root_.GD.N0163.d022181 p t := by
  funext x
  by_cases hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218
  · rw [show _root_.GD.N0163.d022211 (_root_.GD.N0172.d022478 p t hp).1 x =
        (_root_.GD.N0172.d022478 p t hp).1 ⟨x, hx⟩ from
      _root_.GD.N0163.d022212 (_root_.GD.N0172.d022478 p t hp).1 ⟨x, hx⟩]
    rfl
  · have hn : ¬ ∃ y : _root_.GD.N0232.N0720.N1436.d013218, (y : _root_.GD.N0232.N0720.N1436.d013217) = x := by
      rintro ⟨y, hy⟩
      apply hx
      rw [← hy]
      exact y.property
    rw [_root_.GD.N0163.d022211,
      Function.extend_apply' (_root_.GD.N0172.d022478 p t hp).1 (fun _ => 0) x hn]
    simp only [_root_.GD.N0163.d022181, Set.indicator_of_notMem hx]


theorem d022480 :
    _root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022211 (_root_.GD.N0172.d022478 p t hp).1) = _root_.GD.N0163.d022186 p t := by
  rw [_root_.GD.N0172.d022479]
  exact _root_.GD.N0163.d022209 p t hp

include hp in

theorem d022481 :
    _root_.GD.N0163.d022186 p t =
      ⨅ g : _root_.GD.N0172.d022466, _root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022211 g.1) := by
  have hlower : ∀ g : _root_.GD.N0172.d022466,
      _root_.GD.N0163.d022186 p t ≤ _root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022211 g.1) := by
    intro g
    rw [← _root_.GD.N0163.d022209 p t hp]
    exact _root_.GD.N0163.d022215 p t hp g.1 g.property.1 g.property.2
  have hbounded : BddBelow
      (Set.range (fun g : _root_.GD.N0172.d022466 => _root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022211 g.1))) := by
    refine ⟨_root_.GD.N0163.d022186 p t, ?_⟩
    rintro y ⟨g, rfl⟩
    exact hlower g
  apply le_antisymm
  · exact le_ciInf hlower
  · exact ciInf_le_of_le hbounded (_root_.GD.N0172.d022478 p t hp) (_root_.GD.N0172.d022480 p t hp).le

include hp in
theorem d022482 :
    ENNReal.ofReal (_root_.GD.N0163.d022186 p t) =
      ⨅ g : _root_.GD.N0172.d022466, ENNReal.ofReal (_root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022211 g.1)) := by
  rw [_root_.GD.N0172.d022481 p t hp, ENNReal.ofReal_iInf]

end FinitePacket


theorem d022483 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0171.d007331 N * _root_.GD.N0172.d022468 (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007306 N) - _root_.GD.N0171.d007332 N ≤
      _root_.GD.N0163.d022186 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) := by
  letI : Nonempty (_root_.GD.N0193.d007344 N) := ⟨(⟨0, _root_.GD.N0193.d007353 hN⟩, 0)⟩
  let g : _root_.GD.N0172.d022466 := _root_.GD.N0172.d022478
    (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) (fun _ => _root_.GD.N0193.d007367 hN)
  have hA : 0 < _root_.GD.N0167.d007305 N :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans (_root_.GD.N0167.d007316 hN)
  have hc := mul_le_mul_of_nonneg_left
    (_root_.GD.N0172.d022473 hA (_root_.GD.N0167.d007318 hN) g) (_root_.GD.N0171.d007335 hN).le
  have hbin := _root_.GD.N0177.d022425 hN g.1 g.property.1 g.property.2
  have hatt : _root_.GD.N0163.d022185 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN)
      (_root_.GD.N0163.d022211 g.1) =
        _root_.GD.N0163.d022186 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) :=
    _root_.GD.N0172.d022480 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN)
      (fun _ => _root_.GD.N0193.d007367 hN)
  rw [hatt] at hbin
  exact (sub_le_sub_right hc (_root_.GD.N0171.d007332 N)).trans hbin


theorem d022484 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0204.d007394 N * (_root_.GD.N0181.d007274 N - _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N) ≤
      _root_.GD.N0172.d022468 (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007306 N) := by
  have hn2 : 2 ≤ N := by omega
  have ha := _root_.GD.N0181.d007293 hn2
  have hb : 0 < _root_.GD.N0181.d007272 N := ha.trans_le (_root_.GD.N0181.d007294 hn2)
  have hab : _root_.GD.N0181.d007271 N < _root_.GD.N0181.d007272 N := (one_lt_div ha).mp
    ((Real.log_pos_iff (div_pos hb ha).le).mp (_root_.GD.N0167.d007321 hn2))
  have hbound := _root_.GD.N0172.d022477 (_root_.GD.N0181.d007291 hn2)
    (_root_.GD.N0181.d007292 hN).le ha hab (_root_.GD.N0167.d007316 hn2) (_root_.GD.N0167.d007329 hN)
  rw [← _root_.GD.N0167.d007311 hn2] at hbound
  change _root_.GD.N0204.d007394 N * (_root_.GD.N0181.d007274 N - _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N) ≤
    _root_.GD.N0172.d022468 (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007306 N) at hbound
  exact hbound


theorem d022485 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0171.d007331 N * (_root_.GD.N0204.d007394 N * (_root_.GD.N0181.d007274 N - _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N)) - _root_.GD.N0171.d007332 N ≤
      _root_.GD.N0163.d022186 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 (by omega : 2 ≤ N)) := by
  have hn2 : 2 ≤ N := by omega
  exact (sub_le_sub_right
    (mul_le_mul_of_nonneg_left (_root_.GD.N0172.d022484 hN) (_root_.GD.N0171.d007335 hn2).le)
    (_root_.GD.N0171.d007332 N)).trans (_root_.GD.N0172.d022483 hn2)

end
end GD.N0172

#print axioms _root_.GD.N0172.d022470
#print axioms _root_.GD.N0172.d022471
#print axioms _root_.GD.N0172.d022472
#print axioms _root_.GD.N0172.d022473
#print axioms _root_.GD.N0172.d022474
#print axioms _root_.GD.N0172.d022475
#print axioms _root_.GD.N0172.d022476
#print axioms _root_.GD.N0172.d022477
#print axioms _root_.GD.N0172.d022479
#print axioms _root_.GD.N0172.d022480
#print axioms _root_.GD.N0172.d022481
#print axioms _root_.GD.N0172.d022482
#print axioms _root_.GD.N0172.d022483
#print axioms _root_.GD.N0172.d022484
#print axioms _root_.GD.N0172.d022485
