import GD.Module1176
import GD.Module1202
import GD.Module1198

























open MeasureTheory

namespace GD
namespace N0232
namespace N0720
namespace N1456

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1086
open _root_.GD.N0232.N0720.N1106
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1209
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1459
open _root_.GD.N0232.N0720.N1460
open _root_.GD.N0232.N0720.N1468
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1471
open _root_.GD.N0232.N0720.N1475
open _root_.GD.N0232.N0720.N1476
open _root_.GD.N0232.N0720.N1501





def d019471
    (m n : ℕ) (f : ℝ → ℝ → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1460.d003027 f
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1)



structure d019472 (m n : ℕ) where
  coefficient : ℝ → ℝ → ℝ
  measurable_coefficient :
    Measurable (fun p : ℝ × ℝ ↦ coefficient p.1 p.2)
  memLp : MemLp (_root_.GD.N0232.N0720.N1456.d019471 m n coefficient) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)


def d019472.d019473
    {m n : ℕ} (c : _root_.GD.N0232.N0720.N1456.d019472 m n) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient) c.memLp



theorem d019474
    (m n : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : Measurable (fun p : ℝ × ℝ ↦ f p.1 p.2)) :
    Measurable (_root_.GD.N0232.N0720.N1456.d019471 m n f) := by
  unfold _root_.GD.N0232.N0720.N1456.d019471 _root_.GD.N0232.N0720.N1460.d003027 _root_.GD.N0232.N0720.N1460.d003025 _root_.GD.N0232.N0720.N1460.d003024
    _root_.GD.N0232.N0720.N1460.d003026
  fun_prop


theorem d019475
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f : ℝ → ℝ → ℝ) :
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229)
        (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y)
      (_root_.GD.N0232.N0720.N1456.d019471 m n f) := by
  intro g omega
  have hsummary := _root_.GD.N0232.N0720.N1475.d018975 m n hm hn g omega
  have hlift := _root_.GD.N0232.N0720.N1460.d003033 f g.shift g.d009239
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1) g.d009240
  unfold _root_.GD.N0232.N0720.N1456.d019471
  rw [hsummary]
  simpa [_root_.GD.N0232.N0719.N0946.d009229.d009244, _root_.GD.N0232.N0719.N0900.d009101] using hlift



theorem d019472.d019476
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n) :
    _root_.GD.N0232.N0720.N1159.d014652 m n c.d019473 := by
  refine ⟨_root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient,
    _root_.GD.N0232.N0720.N1456.d019474 m n c.coefficient c.measurable_coefficient,
    ?_, _root_.GD.N0232.N0720.N1456.d019475 m n hm hn c.coefficient⟩
  have href : _root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega ↦ c.d019473 omega := by
    exact c.memLp.coeFn_toLp.symm
  intro theta
  have hphysical := (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le href
  have hborelPhysical := (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
    (_root_.GD.N0232.N0720.N1214.d014267 m n c.d019473).symm
  exact Filter.EventuallyEq.trans hphysical
    hborelPhysical



def d019472.d019477
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n) : _root_.GD.N0232.N0720.N1086.d019414 m n where
  value := c.d019473
  riskCharacter :=
    _root_.GD.N0232.N0720.N1159.d014653
      m n c.d019473
        (c.d019476 m n hm hn)


def d019478
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n) : Prop :=
  _root_.GD.N0232.N0720.N1460.d003040 c.coefficient ∧
  (∀ (ρ : ℝ) (hρ : 0 < ρ),
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) ∧
  ¬ ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), _root_.GD.N0232.N0720.N1468.d018953 m n e c.d019473


def d019479
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∀ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
    _root_.GD.N0232.N0720.N1460.d003040 c.coefficient →
    (∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) →
      ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        _root_.GD.N0232.N0720.N1468.d018953 m n e c.d019473





theorem d019480
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    ∃ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
      _root_.GD.N0232.N0720.N1460.d003040 c.coefficient ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1456.d019471 m n c.coefficient =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
          fun omega ↦ s.value omega := by
  obtain ⟨repaired, hrepairedMeasurable, hrepairedClass,
      hrepairedAffine, hrepairedReflection⟩ :=
    _root_.GD.N0232.N0720.N1476.d019379
      m n hm hn s hsTerminal
  let d : ℝ → ℝ → ℝ → ℝ → ℝ :=
    fun u v vx vy ↦ repaired (_root_.GD.N0232.N0720.N1209.d012458 u v vx vy)
  let f : ℝ → ℝ → ℝ := _root_.GD.N0232.N0720.N1460.d003029 d
  have hdMeasurable : Measurable (fun p : ℝ × ℝ ↦ f p.1 p.2) := by
    dsimp only [f, _root_.GD.N0232.N0720.N1460.d003029, d]
    apply hrepairedMeasurable.comp
    rw [measurable_comap_iff]
    change Measurable (fun p : ℝ × ℝ ↦
      ((fun i : Fin 2 ↦ ![p.1, 0] i),
        fun i : Fin 2 ↦ ![p.2, 1 - p.2] i))
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro i
      fin_cases i <;> fun_prop
    · apply measurable_pi_lambda
      intro i
      fin_cases i <;> fun_prop
  have hdAffine : _root_.GD.N0232.N0720.N1437.d003000 d := by
    intro shift dilationFactor u v vx vy hdilation
    have h := hrepairedAffine shift dilationFactor hdilation
      (_root_.GD.N0232.N0720.N1209.d012458 u v vx vy)
    have hsummary :
        _root_.GD.N0232.N0719.N0900.d009101 shift dilationFactor (_root_.GD.N0232.N0720.N1209.d012458 u v vx vy) =
          _root_.GD.N0232.N0720.N1209.d012458 (shift + dilationFactor * u)
            (shift + dilationFactor * v) (dilationFactor ^ 2 * vx)
            (dilationFactor ^ 2 * vy) := by
      apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;>
        simp [_root_.GD.N0232.N0719.N0900.d009101, _root_.GD.N0232.N0720.N1209.d012458]
    rw [hsummary] at h
    exact h
  have hfOdd : _root_.GD.N0232.N0720.N1460.d003040 f := by
    intro z q
    apply _root_.GD.N0232.N0720.N1460.d003041 d
    intro u v vx vy
    exact hrepairedReflection u v vx vy
  have hprojective : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1456.d019471 m n f =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
        fun omega ↦ s.value omega := by
    intro theta
    have hweld := _root_.GD.N0232.N0720.N1459.d018935
      m n hm hn d hdAffine theta
    have hrep := hrepairedClass theta
    filter_upwards [hweld, hrep] with omega hweldOmega hrepOmega
    have hcoordinates :
        _root_.GD.N0232.N0720.N1209.d012458
            ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0)
            ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1)
            ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
            ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1) =
          _root_.GD.N0232.N0720.N1467.d012542 m n omega := by
      apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;> rfl
    calc
      _root_.GD.N0232.N0720.N1456.d019471 m n f omega =
          _root_.GD.N0232.N0720.N1459.d018931 m n d omega := rfl
      _ = _root_.GD.N0232.N0720.N1459.d018930 m n d omega := hweldOmega.symm
      _ = repaired (_root_.GD.N0232.N0720.N1467.d012542 m n omega) := by
        simp only [_root_.GD.N0232.N0720.N1459.d018930, d, hcoordinates]
      _ = s.value omega := hrepOmega
  have href := hprojective _root_.GD.N0232.N0720.N1080.d014169
  have hmem : MemLp (_root_.GD.N0232.N0720.N1456.d019471 m n f) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    apply MemLp.ae_eq href.symm
    exact Lp.memLp s.value
  exact ⟨⟨f, hdMeasurable, hmem⟩, hfOdd, hprojective⟩






theorem d019481
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
        _root_.GD.N0232.N0720.N1456.d019478 m n hm hn c := by
  rw [_root_.GD.N0232.N0720.N1471.d019440
    m n hm hn]
  constructor
  · rintro ⟨s, hstrict, hno⟩
    let t := _root_.GD.N0232.N0720.N1471.N1760.d019433 m n hm hn s hstrict
    have htTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) t.value := by
      have hstruct := _root_.GD.N0232.N0720.N1471.d019441
        m n hm hn s hstrict hno
      exact hstruct.2.2.1
    obtain ⟨c, hcOdd, hcClass⟩ :=
      _root_.GD.N0232.N0720.N1456.d019480
        m n hm hn t htTerminal
    have hcValue : c.d019473 = t.value := by
      apply Lp.ext
      have href := hcClass _root_.GD.N0232.N0720.N1080.d014169
      filter_upwards [c.memLp.coeFn_toLp, href] with omega hcoe hclass
      exact hcoe.trans hclass
    refine ⟨c, hcOdd, ?_, ?_⟩
    · intro ρ hρ
      rw [hcValue]
      exact hstrict ρ hρ
    · intro hdom
      apply hno
      simpa only [_root_.GD.N0232.N0720.N1471.d019431, t,
        _root_.GD.N0232.N0720.N1471.N1760.d019433, hcValue] using hdom
  · rintro ⟨c, _hcOdd, hstrict, hno⟩
    let s := c.d019477 m n
      (lt_of_lt_of_le (by omega) hm) (lt_of_lt_of_le (by omega) hn)
    refine ⟨s, ?_, ?_⟩
    · exact hstrict
    · exact hno






theorem d019482
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ¬ _root_.GD.N0232.N0720.N1456.d019479 m n hm hn := by
  rw [_root_.GD.N0232.N0720.N1456.d019481
    m n hm hn]
  unfold _root_.GD.N0232.N0720.N1456.d019479
    _root_.GD.N0232.N0720.N1456.d019478
  constructor
  · rintro ⟨c, hodd, hstrict, hno⟩ hall
    exact hno (hall c hodd hstrict)
  · intro hnot
    by_contra hnone
    apply hnot
    intro c hodd hstrict
    by_contra hnoDominator
    exact hnone ⟨c, hodd, hstrict, hnoDominator⟩

end
end N1456
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1456.d019480
#print axioms _root_.GD.N0232.N0720.N1456.d019481
#print axioms _root_.GD.N0232.N0720.N1456.d019482
