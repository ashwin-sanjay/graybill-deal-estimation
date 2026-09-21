import GD.Module0724
import GD.Module0727
import GD.Module0634
























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0896

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0107
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0609

variable
  (k : ℕ) (sizes : Fin k → ℕ)
  (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)





def d011088
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  AEStronglyMeasurable.mk
    (fun omega ↦ p omega) (Lp.aestronglyMeasurable p)

theorem d011089
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    Measurable (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) :=
  AEStronglyMeasurable.measurable_mk (Lp.aestronglyMeasurable p)

theorem d011090
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0896.d011088 k sizes p =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] fun omega ↦ p omega :=
  (Lp.aestronglyMeasurable p).ae_eq_mk.symm

theorem d011091
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    MemLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  exact MemLp.ae_eq
    (_root_.GD.N0232.N0719.N0896.d011090 k sizes p).symm (Lp.memLp p)

theorem d011092
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    MemLp.toLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)
      (_root_.GD.N0232.N0719.N0896.d011091 k sizes p) = p := by
  calc
    MemLp.toLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)
          (_root_.GD.N0232.N0719.N0896.d011091 k sizes p) =
        MemLp.toLp (fun omega ↦ p omega) (Lp.memLp p) :=
      MemLp.toLp_congr
        (_root_.GD.N0232.N0719.N0896.d011091 k sizes p) (Lp.memLp p)
        (_root_.GD.N0232.N0719.N0896.d011090 k sizes p)
    _ = p := Lp.toLp_coeFn p (Lp.memLp p)



theorem d011093
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p := by
  rw [_root_.GD.N0232.N0719.N0859.d010841 k sizes theta
    (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) (_root_.GD.N0232.N0719.N0896.d011091 k sizes p)]
  rw [_root_.GD.N0232.N0719.N0896.d011092]



theorem d011094
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {d e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hde : d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] e) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e := by
  unfold _root_.GD.N0232.N0719.N0859.d010840
  apply lintegral_congr_ae
  filter_upwards [hde] with omega homega
  rw [homega]


theorem d011095
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hd : Measurable d)
    (hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d ≠ ⊤) :
    MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  apply (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).2
  have hlin :
      (∫⁻ omega, ENNReal.ofReal (d omega ^ 2) ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) ≠ ⊤ := by
    simpa [_root_.GD.N0232.N0719.N0859.d010840,
      _root_.GD.N0232.N0719.N0859.d010813,
      _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0859.d010810,
      _root_.GD.N0232.N0719.d009182] using hfinite
  have hint :=
    integrable_toReal_of_lintegral_ne_top
      ((hd.pow_const 2).ennreal_ofReal.aemeasurable) hlin
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint




def d011096
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :=
  {d | _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s d}

theorem d011097
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    IsClosed (_root_.GD.N0232.N0719.N0896.d011096 k sizes s) := by
  simpa [_root_.GD.N0232.N0719.N0896.d011096, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta => _root_.GD.N0232.N0719.N0859.d010821 k sizes theta s)
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))

theorem d011098
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    Convex ℝ (_root_.GD.N0232.N0719.N0896.d011096 k sizes s) := by
  simpa [_root_.GD.N0232.N0719.N0896.d011096, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta => _root_.GD.N0232.N0719.N0859.d010821 k sizes theta s)
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))



noncomputable def d011099
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  _root_.GD.N0230.N0608.d000681
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) s
    (by simpa [_root_.GD.N0232.N0719.N0896.d011096] using _root_.GD.N0232.N0719.N0896.d011097 k sizes s)
    (by simpa [_root_.GD.N0232.N0719.N0896.d011096] using _root_.GD.N0232.N0719.N0896.d011098 k sizes s)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)

theorem d011100
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s (_root_.GD.N0232.N0719.N0896.d011099 k sizes s) ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0896.d011099 k sizes s) ∧
      (∀ d, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s d →
        _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) (_root_.GD.N0232.N0719.N0896.d011099 k sizes s) ≤
          _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d) := by
  exact _root_.GD.N0230.N0608.d000682
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) s
    (by simpa [_root_.GD.N0232.N0719.N0896.d011096] using _root_.GD.N0232.N0719.N0896.d011097 k sizes s)
    (by simpa [_root_.GD.N0232.N0719.N0896.d011096] using _root_.GD.N0232.N0719.N0896.d011098 k sizes s)
    (_root_.GD.N0232.N0719.N0859.d010829 k sizes)



theorem d011101
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0896.d011099 k sizes s = s ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s := by
  constructor
  · intro heq
    simpa only [heq] using (_root_.GD.N0232.N0719.N0896.d011100 k sizes s).2.1
  · intro hterminal
    exact hterminal _ (_root_.GD.N0232.N0719.N0896.d011100 k sizes s).1


theorem d011102
    (s base : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s base) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0896.d011099 k sizes s) base := by
  intro theta
  exact lt_of_le_of_lt
    ((_root_.GD.N0232.N0719.N0896.d011100 k sizes s).1 theta) (hstrict theta)



def d011103
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) : Prop :=
  ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p ≠ ⊤

def d011104 (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010809 k :=
  _root_.GD.N0232.N0719.N0845.d010881 g.shift g.d009239 g.d009240 theta

def d011105
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) : Prop :=
  ∀ (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0719.N0859.d010809 k),
    _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0896.d011104 k g theta) p =
      ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p

structure d011106 where
  value : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
  finiteRisk : _root_.GD.N0232.N0719.N0896.d011103 k sizes value
  riskCharacter : _root_.GD.N0232.N0719.N0896.d011105 k sizes value

theorem d011107
    (p base : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p base) :
    _root_.GD.N0232.N0719.N0896.d011103 k sizes p := by
  intro theta
  exact ne_top_of_lt (hstrict theta)



theorem d011108
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    MemLp
      (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p))
      2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  apply _root_.GD.N0232.N0719.N0896.d011095 k sizes
    (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p))
    (_root_.GD.N0232.N0719.N0842.d010912 k sizes g.shift g.d009239
      (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) (_root_.GD.N0232.N0719.N0896.d011089 k sizes p))
  let theta : _root_.GD.N0232.N0719.N0859.d010809 k :=
    _root_.GD.N0232.N0719.N0845.d010881 (_root_.GD.N0232.N0719.N0842.d010906 g.shift g.d009239) g.d009239⁻¹
      (inv_pos.mpr g.d009240) (_root_.GD.N0232.N0719.N0859.d010810 k)
  have heta : _root_.GD.N0232.N0719.N0896.d011104 k g theta = _root_.GD.N0232.N0719.N0859.d010810 k := by
    exact _root_.GD.N0232.N0719.N0842.d010919
      g.shift g.d009239 g.d009240 (_root_.GD.N0232.N0719.N0859.d010810 k)
  have hrisk := _root_.GD.N0232.N0719.N0842.d010920
    k sizes g.shift g.d009239 g.d009240 theta
    (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) (_root_.GD.N0232.N0719.N0896.d011089 k sizes p)
  change
    _root_.GD.N0232.N0719.N0859.d010840 k sizes
        (_root_.GD.N0232.N0719.N0896.d011104 k g theta)
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)) =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) at hrisk
  rw [heta] at hrisk
  rw [hrisk, _root_.GD.N0232.N0719.N0896.d011093]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hp theta)

noncomputable def d011109
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  MemLp.toLp
    (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p))
    (_root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp)

theorem d011110
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0896.d011104 k g theta)
        (_root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp) =
      ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p := by
  unfold _root_.GD.N0232.N0719.N0896.d011109 _root_.GD.N0232.N0719.N0896.d011104
  rw [← _root_.GD.N0232.N0719.N0859.d010841 k sizes
    (_root_.GD.N0232.N0719.N0845.d010881 g.shift g.d009239 g.d009240 theta)
    (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p))
    (_root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp)]
  rw [_root_.GD.N0232.N0719.N0842.d010920
    k sizes g.shift g.d009239 g.d009240 theta
    (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) (_root_.GD.N0232.N0719.N0896.d011089 k sizes p)]
  rw [_root_.GD.N0232.N0719.N0896.d011093]

theorem d011111
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : p ∈ _root_.GD.N0232.N0719.N0896.d011096 k sizes s.value) :
    _root_.GD.N0232.N0719.N0896.d011103 k sizes p := by
  intro theta
  exact ne_top_of_le_ne_top (s.finiteRisk theta) (hp theta)

noncomputable def d011112
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0719.N0896.d011096 k sizes s.value → _root_.GD.N0232.N0719.N0896.d011096 k sizes s.value :=
  fun p =>
    ⟨_root_.GD.N0232.N0719.N0896.d011109 k sizes g p.1
        (_root_.GD.N0232.N0719.N0896.d011111 k sizes s p.1 p.2),
      by
        intro eta
        let theta : _root_.GD.N0232.N0719.N0859.d010809 k :=
          _root_.GD.N0232.N0719.N0845.d010881 (_root_.GD.N0232.N0719.N0842.d010906 g.shift g.d009239) g.d009239⁻¹
            (inv_pos.mpr g.d009240) eta
        have heta : _root_.GD.N0232.N0719.N0896.d011104 k g theta = eta := by
          exact _root_.GD.N0232.N0719.N0842.d010919
            g.shift g.d009239 g.d009240 eta
        rw [← heta, _root_.GD.N0232.N0719.N0896.d011110,
          s.riskCharacter]
        exact mul_le_mul_left' (p.2 theta) _⟩

noncomputable def d011113
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) : _root_.GD.N0232.N0719.N0896.d011096 k sizes s.value :=
  ⟨_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value,
    (_root_.GD.N0232.N0719.N0896.d011100 k sizes s.value).1⟩



noncomputable def d011114
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) (g : _root_.GD.N0232.N0719.N0946.d009229) : ℝ :=
  ‖(_root_.GD.N0232.N0719.N0896.d011112 k sizes s g
      (_root_.GD.N0232.N0719.N0896.d011113 k sizes s)).1‖ ^ 2 -
    ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ ^ 2

theorem d011115
    (s d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : d ∈ _root_.GD.N0232.N0719.N0896.d011096 k sizes s) :
    ‖d - _root_.GD.N0232.N0719.N0896.d011099 k sizes s‖ ^ 2 ≤
      ‖d‖ ^ 2 - ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes s‖ ^ 2 := by
  simpa only [_root_.GD.N0232.N0719.N0896.d011099, zero_sub, norm_neg] using
    (_root_.GD.N0230.N0609.d000701
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0859.d010810 k)
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) s d
      (by simpa [_root_.GD.N0232.N0719.N0896.d011096] using _root_.GD.N0232.N0719.N0896.d011097 k sizes s)
      (by simpa [_root_.GD.N0232.N0719.N0896.d011096] using _root_.GD.N0232.N0719.N0896.d011098 k sizes s)
      (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)

theorem d011116
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    ‖(_root_.GD.N0232.N0719.N0896.d011112 k sizes s g
          (_root_.GD.N0232.N0719.N0896.d011113 k sizes s)).1 -
        _root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ ^ 2 ≤
      _root_.GD.N0232.N0719.N0896.d011114 k sizes s g := by
  simpa only [_root_.GD.N0232.N0719.N0896.d011114] using
    (_root_.GD.N0232.N0719.N0896.d011115 k sizes s.value
      (_root_.GD.N0232.N0719.N0896.d011112 k sizes s g
        (_root_.GD.N0232.N0719.N0896.d011113 k sizes s)).1
      (_root_.GD.N0232.N0719.N0896.d011112 k sizes s g
        (_root_.GD.N0232.N0719.N0896.d011113 k sizes s)).2)

theorem d011117
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    0 ≤ _root_.GD.N0232.N0719.N0896.d011114 k sizes s g := by
  exact le_trans (sq_nonneg _)
    (_root_.GD.N0232.N0719.N0896.d011116 k sizes s g)

theorem d011118
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0719.N0896.d011114 k sizes s g = 0 ↔
      _root_.GD.N0232.N0719.N0896.d011112 k sizes s g (_root_.GD.N0232.N0719.N0896.d011113 k sizes s) =
        _root_.GD.N0232.N0719.N0896.d011113 k sizes s := by
  constructor
  · intro hzero
    have hsq :
        ‖(_root_.GD.N0232.N0719.N0896.d011112 k sizes s g
              (_root_.GD.N0232.N0719.N0896.d011113 k sizes s)).1 -
            _root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ ^ 2 ≤ 0 := by
      simpa only [hzero] using
        _root_.GD.N0232.N0719.N0896.d011116 k sizes s g
    have hnorm :
        ‖(_root_.GD.N0232.N0719.N0896.d011112 k sizes s g
              (_root_.GD.N0232.N0719.N0896.d011113 k sizes s)).1 -
            _root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ = 0 := by
      nlinarith [norm_nonneg
        ((_root_.GD.N0232.N0719.N0896.d011112 k sizes s g
            (_root_.GD.N0232.N0719.N0896.d011113 k sizes s)).1 -
          _root_.GD.N0232.N0719.N0896.d011099 k sizes s.value)]
    apply Subtype.ext
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro hfixed
    have hvalue := congrArg Subtype.val hfixed
    unfold _root_.GD.N0232.N0719.N0896.d011114
    rw [hvalue]
    change
      ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ ^ 2 -
        ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ ^ 2 = 0
    exact sub_self _





theorem d011119
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    Measure.QuasiMeasurePreserving
      (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  refine ⟨_root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation, ?_⟩
  unfold _root_.GD.N0232.N0719.N0859.d010813
    _root_.GD.N0232.N0719.d009182
  rw [_root_.GD.N0232.N0719.d009188]
  simpa using
    (_root_.GD.N0232.N0719.d009181
      k sizes shift 0 (fun _ ↦ dilation) (fun _ ↦ 1)
      (fun _ ↦ hdilation.ne') (fun _ ↦ one_ne_zero))



theorem d011120
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    {d e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hde : d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] e) :
    _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 d =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 e := by
  have hpull :=
    (_root_.GD.N0232.N0719.N0896.d011119
      k sizes (_root_.GD.N0232.N0719.N0842.d010906 g.shift g.d009239) g.d009239⁻¹
      (inv_pos.mpr g.d009240)).ae_eq hde
  filter_upwards [hpull] with omega homega
  have hvalue :
      d (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.shift g.d009239 omega) =
        e (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.shift g.d009239 omega) := by
    simpa only [Function.comp_apply, _root_.GD.N0232.N0719.N0842.d010907] using homega
  unfold _root_.GD.N0232.N0719.N0842.d010911
  rw [hvalue]



def d011121
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) : Prop :=
  ∃ repaired : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
    Measurable repaired ∧
    (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      repaired =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
        _root_.GD.N0232.N0719.N0896.d011088 k sizes p) ∧
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229)
        (omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes) => g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) repaired


theorem d011122
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229)
        (omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes) => g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) d)
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 d = d := by
  funext omega
  have h := hd g
    (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.shift g.d009239 omega)
  change
    d (g • _root_.GD.N0232.N0719.N0842.d010907 k sizes g.shift g.d009239 omega) =
      g • d (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.shift g.d009239 omega) at h
  rw [_root_.GD.N0232.N0719.N0946.d009258] at h
  rw [_root_.GD.N0232.N0719.N0842.d010910
    k sizes g.shift g.d009239 g.d009241 omega] at h
  simpa only [_root_.GD.N0232.N0719.N0842.d010911, _root_.GD.N0232.N0719.N0946.d009229.d009244] using h.symm



theorem d011123
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hrep : _root_.GD.N0232.N0719.N0896.d011121 k sizes p) :
    _root_.GD.N0232.N0719.N0896.d011105 k sizes p := by
  obtain ⟨repaired, hrepairedMeasurable, hrepairedClass,
    hrepairedEquivariant⟩ := hrep
  have hrisk (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta repaired =
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p := by
    calc
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta repaired =
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
            (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) := by
        unfold _root_.GD.N0232.N0719.N0859.d010840
        apply lintegral_congr_ae
        filter_upwards [hrepairedClass theta] with omega homega
        rw [homega]
      _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p :=
        _root_.GD.N0232.N0719.N0896.d011093 k sizes theta p
  have htransport (g : _root_.GD.N0232.N0719.N0946.d009229) :
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 repaired = repaired :=
    _root_.GD.N0232.N0719.N0896.d011122 k sizes repaired hrepairedEquivariant g
  intro g theta
  calc
    _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0896.d011104 k g theta) p =
        _root_.GD.N0232.N0719.N0859.d010840 k sizes
          (_root_.GD.N0232.N0719.N0896.d011104 k g theta) repaired :=
      (hrisk (_root_.GD.N0232.N0719.N0896.d011104 k g theta)).symm
    _ = _root_.GD.N0232.N0719.N0859.d010840 k sizes
          (_root_.GD.N0232.N0719.N0896.d011104 k g theta)
          (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 repaired) := by
      rw [htransport g]
    _ = ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta repaired := by
      exact _root_.GD.N0232.N0719.N0842.d010920
        k sizes g.shift g.d009239 g.d009240 theta
          repaired hrepairedMeasurable
    _ = ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p := by
      rw [hrisk theta]



theorem d011124
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p)
    (hfixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp = p) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega ↦ _root_.GD.N0232.N0719.N0896.d011088 k sizes p (g • omega)) =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010813 k sizes]
      fun omega ↦ g • _root_.GD.N0232.N0719.N0896.d011088 k sizes p omega := by
  have hrawFixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N0896.d011088 k sizes p := by
    intro g
    apply (MemLp.toLp_eq_toLp_iff
      (_root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp)
      (_root_.GD.N0232.N0719.N0896.d011091 k sizes p)).mp
    change _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp =
      MemLp.toLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)
        (_root_.GD.N0232.N0719.N0896.d011091 k sizes p)
    rw [hfixed g, _root_.GD.N0232.N0719.N0896.d011092]
  intro g
  have hpull :=
    (_root_.GD.N0232.N0719.N0896.d011119
      k sizes g.shift g.d009239 g.d009240).ae_eq (hrawFixed g)
  filter_upwards [hpull] with omega homega
  change
    _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes g.shift g.d009239 omega) =
      _root_.GD.N0232.N0719.N0896.d011088 k sizes p
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes g.shift g.d009239 omega) at homega
  rw [_root_.GD.N0232.N0719.N0842.d010913
    k sizes g.shift g.d009239 g.d009241
      (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) omega] at homega
  simpa only [_root_.GD.N0232.N0719.N0946.d009258,
    _root_.GD.N0232.N0719.N0946.d009229.d009244] using homega.symm

include hk hsizes in


theorem d011125
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p)
    (hfixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp = p) :
    _root_.GD.N0232.N0719.N0896.d011121 k sizes p := by
  have hcov := _root_.GD.N0232.N0719.N0896.d011124
    k sizes p hp hfixed
  obtain ⟨repaired, hrepairedMeasurable, hrepairedClass,
      hrepairedEquivariant⟩ :=
    _root_.GD.N0232.N0719.N0946.d009262
      (k := k) (sizes := sizes)
      (lt_of_lt_of_le (by norm_num) hk)
      (fun i => lt_of_lt_of_le (by norm_num) (hsizes i))
      (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) (_root_.GD.N0232.N0719.N0896.d011089 k sizes p) hcov
  refine ⟨repaired, hrepairedMeasurable, ?_, hrepairedEquivariant⟩
  intro theta
  exact hrepairedClass theta.location theta.scale theta.scale_pos



theorem d011126
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p)
    (hrep : _root_.GD.N0232.N0719.N0896.d011121 k sizes p) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp = p := by
  obtain ⟨repaired, _hrepairedMeasurable, hrepairedClass,
    hrepairedEquivariant⟩ := hrep
  intro g
  have hrepairedReference :
      repaired =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N0896.d011088 k sizes p := by
    simpa [_root_.GD.N0232.N0719.N0859.d010813,
      _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0859.d010810,
      _root_.GD.N0232.N0719.d009182] using
      hrepairedClass (_root_.GD.N0232.N0719.N0859.d010810 k)
  have htransportCongr :
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 repaired :=
    _root_.GD.N0232.N0719.N0896.d011120 k sizes g hrepairedReference.symm
  have htransportRepaired :
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 repaired = repaired :=
    _root_.GD.N0232.N0719.N0896.d011122
      k sizes repaired hrepairedEquivariant g
  have htransportFixed :
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N0896.d011088 k sizes p := by
    filter_upwards [htransportCongr, hrepairedReference] with omega hcongr hclass
    calc
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) omega =
          _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 repaired omega := hcongr
      _ = repaired omega := congrFun htransportRepaired omega
      _ = _root_.GD.N0232.N0719.N0896.d011088 k sizes p omega := hclass
  unfold _root_.GD.N0232.N0719.N0896.d011109
  calc
    MemLp.toLp
          (_root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p))
          (_root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp) =
        MemLp.toLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)
          (_root_.GD.N0232.N0719.N0896.d011091 k sizes p) :=
      MemLp.toLp_congr
        (_root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp)
        (_root_.GD.N0232.N0719.N0896.d011091 k sizes p) htransportFixed
    _ = p := _root_.GD.N0232.N0719.N0896.d011092 k sizes p

include hk hsizes in

theorem d011127
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    (∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp = p) ↔
      _root_.GD.N0232.N0719.N0896.d011121 k sizes p := by
  constructor
  · exact _root_.GD.N0232.N0719.N0896.d011125
      k sizes hk hsizes p hp
  · exact
      _root_.GD.N0232.N0719.N0896.d011126
        k sizes p hp

include hk hsizes in


theorem d011128
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) :
    (∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0719.N0896.d011114 k sizes s g = 0) ↔
      _root_.GD.N0232.N0719.N0896.d011121 k sizes
        (_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value) := by
  let hpFinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes
      (_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value) :=
    _root_.GD.N0232.N0719.N0896.d011111 k sizes s
      (_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value)
      (_root_.GD.N0232.N0719.N0896.d011100 k sizes s.value).1
  rw [← _root_.GD.N0232.N0719.N0896.d011127
    k sizes hk hsizes (_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value) hpFinite]
  constructor
  · intro hzero g
    have hfixed :=
      (_root_.GD.N0232.N0719.N0896.d011118 k sizes s g).1 (hzero g)
    have hvalue := congrArg Subtype.val hfixed
    simpa only [_root_.GD.N0232.N0719.N0896.d011112, _root_.GD.N0232.N0719.N0896.d011113] using hvalue
  · intro hfixed g
    apply (_root_.GD.N0232.N0719.N0896.d011118 k sizes s g).2
    apply Subtype.ext
    simpa only [_root_.GD.N0232.N0719.N0896.d011112, _root_.GD.N0232.N0719.N0896.d011113] using hfixed g



def d011129
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hrep : _root_.GD.N0232.N0719.N0896.d011121 k sizes p)
    (hstrict : _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    _root_.GD.N0232.N0719.N0896.d011106 k sizes :=
  ⟨p,
    _root_.GD.N0232.N0719.N0896.d011107
      k sizes p (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) hstrict,
    _root_.GD.N0232.N0719.N0896.d011123
      k sizes p hrep⟩



def d011130 : Prop :=
  ∃ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes),
    _root_.GD.N0232.N0719.N0896.d011121 k sizes p ∧
    _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) ∧
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p


def d011131
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : Prop :=
  Measurable d ∧
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229)
        (omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes) => g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) d ∧
    (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) ∧
    (∀ e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable e →
      (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d) →
      ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        e =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] d)

def d011132 : Prop :=
  ∃ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
    _root_.GD.N0232.N0719.N0896.d011131 k sizes d

include hk hsizes in


theorem d011133 :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes ↔
      _root_.GD.N0232.N0719.N0896.d011130 k sizes hk hsizes := by
  constructor
  · rintro ⟨d, hdMeasurable, hdEquivariant, hdStrict, hdTerminal⟩
    have hdMemLp :
        MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
      apply _root_.GD.N0232.N0719.N0896.d011095 k sizes d hdMeasurable
      exact ne_top_of_lt (hdStrict (_root_.GD.N0232.N0719.N0859.d010810 k))
    let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
      MemLp.toLp d hdMemLp
    have hpRisk (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p =
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
      exact (_root_.GD.N0232.N0719.N0859.d010841
        k sizes theta d hdMemLp).symm
    have hdClassReference :
        d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          _root_.GD.N0232.N0719.N0896.d011088 k sizes p := by
      have hcoe :
          (fun omega => p omega) =ᵐ[
            _root_.GD.N0232.N0719.N0859.d010813 k sizes] d := by
        simpa only [p] using hdMemLp.coeFn_toLp
      exact hcoe.symm.trans
        (_root_.GD.N0232.N0719.N0896.d011090 k sizes p).symm
    have hdClass : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
          _root_.GD.N0232.N0719.N0896.d011088 k sizes p := by
      intro theta
      exact (_root_.GD.N0232.N0719.N0859.d010814
        k sizes theta).ae_le hdClassReference
    have hpRepresentative :
        _root_.GD.N0232.N0719.N0896.d011121 k sizes p :=
      ⟨d, hdMeasurable, hdClass, hdEquivariant⟩
    have hpStrict : _root_.GD.N0230.N0608.d000675
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p
        (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) := by
      intro theta
      calc
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p =
            _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d :=
          hpRisk theta
        _ < _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
              (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := hdStrict theta
        _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
              (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) :=
          _root_.GD.N0232.N0719.N0859.d010842
            k sizes hk hsizes theta
    have hpTerminal : _root_.GD.N0230.N0608.d000674
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p := by
      intro e heDominates
      have heRawDominates : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
              (_root_.GD.N0232.N0719.N0896.d011088 k sizes e) ≤
            _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
        intro theta
        rw [_root_.GD.N0232.N0719.N0896.d011093, ← hpRisk theta]
        exact heDominates theta
      have heClassReference :
          _root_.GD.N0232.N0719.N0896.d011088 k sizes e =ᵐ[
              _root_.GD.N0232.N0719.N0859.d010813 k sizes]
            _root_.GD.N0232.N0719.N0896.d011088 k sizes p :=
        (hdTerminal (_root_.GD.N0232.N0719.N0896.d011088 k sizes e)
          (_root_.GD.N0232.N0719.N0896.d011089 k sizes e) heRawDominates
          (_root_.GD.N0232.N0719.N0859.d010810 k)).trans
            hdClassReference
      calc
        e = MemLp.toLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes e)
            (_root_.GD.N0232.N0719.N0896.d011091 k sizes e) :=
          (_root_.GD.N0232.N0719.N0896.d011092 k sizes e).symm
        _ = MemLp.toLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)
            (_root_.GD.N0232.N0719.N0896.d011091 k sizes p) :=
          MemLp.toLp_congr
            (_root_.GD.N0232.N0719.N0896.d011091 k sizes e)
            (_root_.GD.N0232.N0719.N0896.d011091 k sizes p) heClassReference
        _ = p := _root_.GD.N0232.N0719.N0896.d011092 k sizes p
    exact ⟨p, hpRepresentative, hpStrict, hpTerminal⟩
  · rintro ⟨p, hpRepresentative, hpStrict, hpTerminal⟩
    obtain ⟨repaired, hrepairedMeasurable, hrepairedClass,
      hrepairedEquivariant⟩ := hpRepresentative
    have hrepairedRisk : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta repaired =
          _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p := by
      intro theta
      calc
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta repaired =
            _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
              (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) :=
          _root_.GD.N0232.N0719.N0896.d011094 k sizes theta (hrepairedClass theta)
        _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p :=
          _root_.GD.N0232.N0719.N0896.d011093 k sizes theta p
    refine ⟨repaired, hrepairedMeasurable, hrepairedEquivariant, ?_, ?_⟩
    · intro theta
      rw [hrepairedRisk theta,
        _root_.GD.N0232.N0719.N0859.d010842
          k sizes hk hsizes theta]
      exact hpStrict theta
    · intro e heMeasurable heDominates
      have heMemLp :
          MemLp e 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
        apply _root_.GD.N0232.N0719.N0896.d011095
          k sizes e heMeasurable
        apply ne_top_of_le_ne_top
          (show _root_.GD.N0232.N0719.N0859.d010840 k sizes
              (_root_.GD.N0232.N0719.N0859.d010810 k) repaired ≠ ⊤ by
            rw [hrepairedRisk]
            exact ne_top_of_lt
              (hpStrict (_root_.GD.N0232.N0719.N0859.d010810 k)))
        exact heDominates (_root_.GD.N0232.N0719.N0859.d010810 k)
      let eL2 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
        MemLp.toLp e heMemLp
      have heDominatesL2 : _root_.GD.N0230.N0608.d000672
          (_root_.GD.N0232.N0719.N0859.d010821 k sizes) eL2 p := by
        intro theta
        calc
          _root_.GD.N0232.N0719.N0859.d010821 k sizes theta eL2 =
              _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e :=
            (_root_.GD.N0232.N0719.N0859.d010841
              k sizes theta e heMemLp).symm
          _ ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes theta repaired :=
            heDominates theta
          _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p :=
            hrepairedRisk theta
      have heq : eL2 = p := hpTerminal eL2 heDominatesL2
      have heClassReference :
          e =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] repaired := by
        have heCoe :
            (fun omega => eL2 omega) =ᵐ[
              _root_.GD.N0232.N0719.N0859.d010813 k sizes] e := by
          simpa only [eL2] using heMemLp.coeFn_toLp
        have heqCoe :
            (fun omega => eL2 omega) =ᵐ[
                _root_.GD.N0232.N0719.N0859.d010813 k sizes]
              fun omega => p omega := by rw [heq]
        have hpBorel :
            (fun omega => p omega) =ᵐ[
                _root_.GD.N0232.N0719.N0859.d010813 k sizes]
              _root_.GD.N0232.N0719.N0896.d011088 k sizes p :=
          (_root_.GD.N0232.N0719.N0896.d011090 k sizes p).symm
        have hBorelRepaired :
            _root_.GD.N0232.N0719.N0896.d011088 k sizes p =ᵐ[
                _root_.GD.N0232.N0719.N0859.d010813 k sizes] repaired := by
          simpa [_root_.GD.N0232.N0719.N0859.d010813,
            _root_.GD.N0232.N0719.N0859.d010812,
            _root_.GD.N0232.N0719.N0859.d010810,
            _root_.GD.N0232.N0719.d009182] using
              (hrepairedClass
                (_root_.GD.N0232.N0719.N0859.d010810 k)).symm
        exact heCoe.symm.trans
          (heqCoe.trans (hpBorel.trans hBorelRepaired))
      intro theta
      exact (_root_.GD.N0232.N0719.N0859.d010814
        k sizes theta).ae_le heClassReference

include hk hsizes in


theorem d011134
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hrep : _root_.GD.N0232.N0719.N0896.d011121 k sizes p)
    (hstrict : _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes))
    (hterminal : _root_.GD.N0230.N0608.d000674
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p) :
    let s := _root_.GD.N0232.N0719.N0896.d011129
      k sizes hk hsizes p hrep hstrict
    _root_.GD.N0232.N0719.N0896.d011099 k sizes s.value = p ∧
      ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0719.N0896.d011114 k sizes s g = 0 := by
  dsimp only
  let s := _root_.GD.N0232.N0719.N0896.d011129
    k sizes hk hsizes p hrep hstrict
  have hsvalue : s.value = p := rfl
  have heq : _root_.GD.N0232.N0719.N0896.d011099 k sizes s.value = s.value :=
    (_root_.GD.N0232.N0719.N0896.d011101 k sizes s.value).2
      (by simpa only [hsvalue] using hterminal)
  refine ⟨heq.trans hsvalue, ?_⟩
  apply (_root_.GD.N0232.N0719.N0896.d011128
    k sizes hk hsizes s).2
  rw [heq]
  simpa only [hsvalue] using hrep





theorem d011135 :
    _root_.GD.N0232.N0719.N0896.d011130 k sizes hk hsizes ↔
      ∃ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
        _root_.GD.N0230.N0608.d000675
          (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
          (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) ∧
        ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0719.N0896.d011114 k sizes s g = 0 := by
  constructor
  · rintro ⟨p, hrep, hstrict, hterminal⟩
    let s := _root_.GD.N0232.N0719.N0896.d011129
      k sizes hk hsizes p hrep hstrict
    refine ⟨s, ?_, ?_⟩
    · simpa only [s, _root_.GD.N0232.N0719.N0896.d011129] using hstrict
    · exact
        (_root_.GD.N0232.N0719.N0896.d011134
          k sizes hk hsizes p hrep hstrict hterminal).2
  · rintro ⟨s, hstrict, hzero⟩
    refine ⟨_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value, ?_, ?_, ?_⟩
    · exact (_root_.GD.N0232.N0719.N0896.d011128
        k sizes hk hsizes s).1 hzero
    · exact _root_.GD.N0232.N0719.N0896.d011102
        k sizes s.value
          (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) hstrict
    · exact (_root_.GD.N0232.N0719.N0896.d011100 k sizes s.value).2.1






theorem d011136 :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes ↔
      ∃ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
        _root_.GD.N0230.N0608.d000675
          (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
          (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) ∧
        ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0719.N0896.d011114 k sizes s g = 0 := by
  exact
    (_root_.GD.N0232.N0719.N0896.d011133
      k sizes hk hsizes).trans
      (_root_.GD.N0232.N0719.N0896.d011135
        k sizes hk hsizes)



theorem d011137
    (hnot : ¬ _root_.GD.N0232.N0719.N0896.d011130 k sizes hk hsizes)
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hstrict : _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    ∃ g : _root_.GD.N0232.N0719.N0946.d009229, 0 < _root_.GD.N0232.N0719.N0896.d011114 k sizes s g := by
  by_contra hnone
  have hzero : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0719.N0896.d011114 k sizes s g = 0 := by
    intro g
    have hnotpos : ¬ 0 < _root_.GD.N0232.N0719.N0896.d011114 k sizes s g := by
      exact fun hpos => hnone ⟨g, hpos⟩
    exact le_antisymm (le_of_not_gt hnotpos)
      (_root_.GD.N0232.N0719.N0896.d011117 k sizes s g)
  apply hnot
  exact (_root_.GD.N0232.N0719.N0896.d011135
    k sizes hk hsizes).2 ⟨s, hstrict, hzero⟩



theorem d011138
    (hnot : ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes)
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hstrict : _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    ∃ g : _root_.GD.N0232.N0719.N0946.d009229, 0 < _root_.GD.N0232.N0719.N0896.d011114 k sizes s g := by
  apply _root_.GD.N0232.N0719.N0896.d011137
    k sizes hk hsizes
  · intro hclass
    exact hnot
      ((_root_.GD.N0232.N0719.N0896.d011133
        k sizes hk hsizes).2 hclass)
  · exact hstrict

end

end N0896
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0896.d011101
#print axioms _root_.GD.N0232.N0719.N0896.d011118
#print axioms _root_.GD.N0232.N0719.N0896.d011128
#print axioms _root_.GD.N0232.N0719.N0896.d011134
#print axioms _root_.GD.N0232.N0719.N0896.d011133
#print axioms _root_.GD.N0232.N0719.N0896.d011135
#print axioms _root_.GD.N0232.N0719.N0896.d011136
#print axioms _root_.GD.N0232.N0719.N0896.d011137
#print axioms _root_.GD.N0232.N0719.N0896.d011138
