import GD.Module1842
import GD.Module1840
import GD.Module1843
import GD.Module1361

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0034.N0288

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1220
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0718
open _root_.GD.N0046.N0305
open _root_.GD.N0034.N0289 _root_.GD.N0034.N0286

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030330 : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :=
  {d | Measurable d ∧ ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
    min (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ))
      (_root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0034.N0290.d021948 m n))}

include hm hn in
theorem d030331 :
    _root_.GD.N0034.N0288.d030330 m n = _root_.GD.N0034.N0294.d030312 m n := by
  ext d
  simp only [_root_.GD.N0034.N0288.d030330, _root_.GD.N0034.N0294.d030312, Set.mem_setOf_eq,
    _root_.GD.N0034.N0290.d021953 m n hm hn, le_min_iff]

def d030332 : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
      _root_.GD.N0232.N0720.N1220.d017301 m n F w + ε ≤ _root_.GD.N0034.N0289.d030220 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 +
        ∑ θ ∈ F, w θ * _root_.GD.N0034.N0289.d030220 m n hm hn θ

theorem d030333 :
    _root_.GD.N0034.N0289.d030224 m n hm hn ↔ _root_.GD.N0034.N0288.d030332 m n hm hn := by
  constructor
  · intro h
    have hp := (_root_.GD.N0034.N0295.d030306 m n hm hn).mpr h
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      (_root_.GD.N0034.N0286.d030288 m n hm hn).mp hp
    exact _root_.GD.N0034.N0297.d030296 m n hm hn hp hq hpq
  · rintro ⟨ε, hε, h⟩ F w hw
    exact (le_add_of_nonneg_right hε.le).trans (h F w hw)

theorem d030334 :
    ¬ _root_.GD.N0034.N0286.d030282 m n hm hn ↔ _root_.GD.N0034.N0288.d030332 m n hm hn :=
  (_root_.GD.N0034.N0295.d030307 m n hm hn).trans
    (_root_.GD.N0034.N0288.d030333 m n hm hn)

theorem d030335 :
    _root_.GD.N0034.N0286.d030282 m n hm hn ↔
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) ∧
        _root_.GD.N0034.N0289.d030220 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 +
          ∑ θ ∈ F, w θ * _root_.GD.N0034.N0289.d030220 m n hm hn θ < _root_.GD.N0232.N0720.N1220.d017301 m n F w :=
  (_root_.GD.N0034.N0295.d030304 m n hm hn).trans
    (_root_.GD.N0034.N0289.d030226 m n hm hn)

theorem d030336
    (hK : (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty) :
    ∃ t ∈ _root_.GD.N0046.N0305.d030202 m n hm hn,
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ t < ENNReal.ofReal (_root_.GD.N0034.N0289.d030220 m n hm hn θ)) ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) t ∧ 0 < _root_.GD.N0034.N0287.d021571 m n t := by
  have he := (_root_.GD.N0034.N0295.d030305 m n hm hn).mpr hK
  obtain ⟨p, hp, q, hq, hpq⟩ := (_root_.GD.N0034.N0286.d030288 m n hm hn).mp he
  have hz := _root_.GD.N0046.N0305.d030209 m n hp hq
  obtain ⟨t, ht, hbelow, hterm, henergy⟩ :=
    _root_.GD.N0034.N0295.d030310 m n hm hn (_root_.GD.N0230.N0718.d001528 p q) hz
  refine ⟨t, ht, ?_, hterm, henergy⟩
  intro θ
  exact (hbelow θ).trans_lt
    (_root_.GD.N0034.N0297.d030293 m n hm hn hp hq hpq θ)

theorem d030337 :
    (¬ _root_.GD.N0034.N0286.d030282 m n hm hn ↔ _root_.GD.N0034.N0286.d030283 m n hm hn) ∧
    (_root_.GD.N0034.N0286.d030283 m n hm hn ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty) ∧
    (_root_.GD.N0034.N0286.d030283 m n hm hn ↔ _root_.GD.N0034.N0289.d030224 m n hm hn) ∧
    (_root_.GD.N0034.N0289.d030224 m n hm hn ↔ _root_.GD.N0034.N0288.d030332 m n hm hn) ∧
    (_root_.GD.N0034.N0286.d030282 m n hm hn ↔ _root_.GD.N0046.N0305.d030202 m n hm hn = ∅) :=
  ⟨_root_.GD.N0034.N0286.d030284 m n hm hn,
    _root_.GD.N0034.N0295.d030305 m n hm hn,
    _root_.GD.N0034.N0295.d030306 m n hm hn,
    _root_.GD.N0034.N0288.d030333 m n hm hn,
    _root_.GD.N0034.N0295.d030304 m n hm hn⟩

theorem d030338 :
    _root_.GD.N0034.N0294.d030314 m n ↔ _root_.GD.N0034.N0288.d030332 m n hm hn :=
  (_root_.GD.N0034.N0294.d030325 m n hm hn).trans
    ((_root_.GD.N0034.N0295.d030306 m n hm hn).trans
      (_root_.GD.N0034.N0288.d030333 m n hm hn))

theorem d030339 :
    (¬ _root_.GD.N0034.N0294.d030315 m n ↔ _root_.GD.N0034.N0294.d030314 m n) ∧
    (_root_.GD.N0034.N0294.d030314 m n ↔ _root_.GD.N0034.N0288.d030332 m n hm hn) ∧
    (_root_.GD.N0034.N0294.d030315 m n ↔ _root_.GD.N0034.N0294.d030312 m n = ∅) :=
  ⟨_root_.GD.N0034.N0294.d030327 m n,
    _root_.GD.N0034.N0288.d030338 m n hm hn,
    _root_.GD.N0034.N0294.d030328 m n hm hn⟩

theorem d030340 :
    ((¬ ∀ d ∈ _root_.GD.N0034.N0288.d030330 m n, _root_.GD.N0034.N0294.d030313 m n d = 0) ↔
      ∃ d ∈ _root_.GD.N0034.N0288.d030330 m n, 0 < _root_.GD.N0034.N0294.d030313 m n d) ∧
    ((∃ d ∈ _root_.GD.N0034.N0288.d030330 m n, 0 < _root_.GD.N0034.N0294.d030313 m n d) ↔
      _root_.GD.N0034.N0288.d030332 m n hm hn) ∧
    ((∀ d ∈ _root_.GD.N0034.N0288.d030330 m n, _root_.GD.N0034.N0294.d030313 m n d = 0) ↔
      _root_.GD.N0034.N0288.d030330 m n = ∅) := by
  rw [_root_.GD.N0034.N0288.d030331 m n hm hn]
  exact _root_.GD.N0034.N0288.d030339 m n hm hn

end
end GD.N0034.N0288

#print axioms _root_.GD.N0034.N0288.d030333
#print axioms _root_.GD.N0034.N0288.d030334
#print axioms _root_.GD.N0034.N0288.d030335
#print axioms _root_.GD.N0034.N0288.d030336
#print axioms _root_.GD.N0034.N0288.d030337
#print axioms _root_.GD.N0034.N0288.d030338
#print axioms _root_.GD.N0034.N0288.d030339
#print axioms _root_.GD.N0034.N0288.d030331
#print axioms _root_.GD.N0034.N0288.d030340
