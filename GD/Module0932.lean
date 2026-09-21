import GD.Module0931
































open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1159

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1081
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0609
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)




def d014630
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {d | _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s d}


theorem d014631
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    IsClosed (_root_.GD.N0232.N0720.N1159.d014630 m n s) := by
  simpa [_root_.GD.N0232.N0720.N1159.d014630, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun theta => _root_.GD.N0232.N0720.N1080.d014182 m n theta s)
      (_root_.GD.N0232.N0720.N1080.d014173 m n))


theorem d014632
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    Convex ℝ (_root_.GD.N0232.N0720.N1159.d014630 m n s) := by
  simpa [_root_.GD.N0232.N0720.N1159.d014630, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun theta => _root_.GD.N0232.N0720.N1080.d014182 m n theta s)
      (_root_.GD.N0232.N0720.N1080.d014173 m n))



noncomputable def d014633
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0230.N0608.d000681
    (_root_.GD.N0232.N0720.N1080.d014182 m n) _root_.GD.N0232.N0720.N1080.d014169
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) s
    (by simpa [_root_.GD.N0232.N0720.N1159.d014630] using _root_.GD.N0232.N0720.N1159.d014631 m n s)
    (by simpa [_root_.GD.N0232.N0720.N1159.d014630] using _root_.GD.N0232.N0720.N1159.d014632 m n s)
    (_root_.GD.N0232.N0720.N1080.d014190 m n)


theorem d014634
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s (_root_.GD.N0232.N0720.N1159.d014633 m n s) ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1159.d014633 m n s) ∧
      (∀ d, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s d →
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014633 m n s) ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 d) := by
  exact _root_.GD.N0230.N0608.d000682
    (_root_.GD.N0232.N0720.N1080.d014182 m n) _root_.GD.N0232.N0720.N1080.d014169
    (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) s
    (by simpa [_root_.GD.N0232.N0720.N1159.d014630] using _root_.GD.N0232.N0720.N1159.d014631 m n s)
    (by simpa [_root_.GD.N0232.N0720.N1159.d014630] using _root_.GD.N0232.N0720.N1159.d014632 m n s)
    (_root_.GD.N0232.N0720.N1080.d014190 m n)



theorem d014635
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1159.d014633 m n s = s ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s := by
  constructor
  · intro heq
    have hterminal := (_root_.GD.N0232.N0720.N1159.d014634 m n s).2.1
    simpa only [heq] using hterminal
  · intro hterminal
    exact hterminal _ (_root_.GD.N0232.N0720.N1159.d014634 m n s).1


theorem d014636
    (s base : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s base) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1159.d014633 m n s) base := by
  intro theta
  exact lt_of_le_of_lt
    ((_root_.GD.N0232.N0720.N1159.d014634 m n s).1 theta) (hstrict theta)




def d014637
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≠ ⊤


def d014638
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∀ (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168),
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) p =
      ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p



structure d014639 where
  value : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)
  finiteRisk : _root_.GD.N0232.N0720.N1159.d014637 m n value
  riskCharacter : _root_.GD.N0232.N0720.N1159.d014638 m n value


theorem d014640
    (p base : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p base) :
    _root_.GD.N0232.N0720.N1159.d014637 m n p := by
  intro theta
  exact ne_top_of_lt (hstrict theta)





theorem d014641
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    MemLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  apply _root_.GD.N0232.N0720.N1215.d014285 m n
    (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
    (_root_.GD.N0232.N0720.N1214.d014262 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)
      (_root_.GD.N0232.N0720.N1214.d014266 m n p))
  let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = _root_.GD.N0232.N0720.N1080.d014169 := by
    simp [theta]
  have hrisk := _root_.GD.N0232.N0720.N1215.d014284
    m n g theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014266 m n p)
  rw [heta] at hrisk
  rw [hrisk, _root_.GD.N0232.N0720.N1215.d014286]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hp theta)



noncomputable def d014642
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
    (_root_.GD.N0232.N0720.N1159.d014641 m n g p hp)


theorem d014643
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
        (_root_.GD.N0232.N0720.N1159.d014642 m n g p hp) =
      ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p := by
  unfold _root_.GD.N0232.N0720.N1159.d014642
  rw [← _root_.GD.N0232.N0720.N1080.d014198 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
    (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
    (_root_.GD.N0232.N0720.N1159.d014641 m n g p hp)]
  rw [_root_.GD.N0232.N0720.N1215.d014284
    m n g theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014266 m n p)]
  rw [_root_.GD.N0232.N0720.N1215.d014286]



theorem d014644
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1159.d014637 m n p := by
  intro theta
  exact ne_top_of_le_ne_top (s.finiteRisk theta) (hp theta)



noncomputable def d014645
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1159.d014630 m n s.value → _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
  fun p =>
    ⟨_root_.GD.N0232.N0720.N1159.d014642 m n g p.1
        (_root_.GD.N0232.N0720.N1159.d014644 m n s p.1 p.2),
      by
        intro eta
        let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
        have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by simp [theta]
        rw [← heta, _root_.GD.N0232.N0720.N1159.d014643,
          s.riskCharacter]
        exact mul_le_mul_left' (p.2 theta) _⟩


noncomputable def d014646
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
  ⟨_root_.GD.N0232.N0720.N1159.d014633 m n s.value,
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1⟩




noncomputable def d014647
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229) : ℝ :=
  ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s g
      (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1‖ ^ 2 -
    ‖(_root_.GD.N0232.N0720.N1159.d014633 m n s.value)‖ ^ 2


theorem d014648
    (s d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s) :
    ‖d - _root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2 ≤
      ‖d‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2 := by
  simpa only [_root_.GD.N0232.N0720.N1159.d014633, zero_sub, norm_neg] using
    (_root_.GD.N0230.N0609.d000701
      (_root_.GD.N0232.N0720.N1080.d014182 m n) _root_.GD.N0232.N0720.N1080.d014169
      (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) s d
      (by simpa [_root_.GD.N0232.N0720.N1159.d014630] using _root_.GD.N0232.N0720.N1159.d014631 m n s)
      (by simpa [_root_.GD.N0232.N0720.N1159.d014630] using _root_.GD.N0232.N0720.N1159.d014632 m n s)
      (_root_.GD.N0232.N0720.N1080.d014190 m n) hd)


theorem d014649
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s g
          (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1159.d014647 m n s g := by
  simpa only [_root_.GD.N0232.N0720.N1159.d014647] using
    (_root_.GD.N0232.N0720.N1159.d014648 m n s.value
      (_root_.GD.N0232.N0720.N1159.d014645 m n s g
        (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1
      (_root_.GD.N0232.N0720.N1159.d014645 m n s g
        (_root_.GD.N0232.N0720.N1159.d014646 m n s)).2)


theorem d014650
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    0 ≤ _root_.GD.N0232.N0720.N1159.d014647 m n s g := by
  exact le_trans (sq_nonneg _)
    (_root_.GD.N0232.N0720.N1159.d014649 m n s g)



theorem d014651
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s) =
        _root_.GD.N0232.N0720.N1159.d014646 m n s := by
  constructor
  · intro hzero
    have hsq :
        ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s g
              (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 -
            _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ 0 := by
      simpa only [hzero] using
        _root_.GD.N0232.N0720.N1159.d014649 m n s g
    have hnorm :
        ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s g
              (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 -
            _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ = 0 := by
      nlinarith [norm_nonneg
        ((_root_.GD.N0232.N0720.N1159.d014645 m n s g
            (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 -
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value)]
    apply Subtype.ext
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro hfixed
    have hvalue := congrArg Subtype.val hfixed
    unfold _root_.GD.N0232.N0720.N1159.d014647
    rw [hvalue]
    change
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 = 0
    exact sub_self _





def d014652
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
    Measurable repaired ∧
    (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      repaired =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1214.d014265 m n p) ∧
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) => g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) repaired



theorem d014653
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p) :
    _root_.GD.N0232.N0720.N1159.d014638 m n p := by
  obtain ⟨repaired, hrepairedMeasurable, hrepairedClass,
    hrepairedEquivariant⟩ := hrep
  have hrisk (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired = _root_.GD.N0232.N0720.N1080.d014182 m n theta p := by
    calc
      _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired =
          _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
        unfold _root_.GD.N0232.N0720.N1080.d014197
        apply lintegral_congr_ae
        filter_upwards [hrepairedClass theta] with omega homega
        rw [homega]
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n theta p :=
        _root_.GD.N0232.N0720.N1215.d014286 m n theta p
  have htransport (g : _root_.GD.N0232.N0719.N0946.d009229) :
      _root_.GD.N0232.N0720.N1214.d014261 m n g repaired = repaired := by
    funext omega
    calc
      _root_.GD.N0232.N0720.N1214.d014261 m n g repaired omega =
          g • repaired (g⁻¹ • omega) := rfl
      _ = repaired (g • (g⁻¹ • omega)) := by
        symm
        exact hrepairedEquivariant g (g⁻¹ • omega)
      _ = repaired omega := by rw [smul_inv_smul]
  intro g theta
  calc
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) p =
        _root_.GD.N0232.N0720.N1080.d014197 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) repaired :=
      (hrisk (_root_.GD.N0232.N0720.N1215.d014272 g theta)).symm
    _ = _root_.GD.N0232.N0720.N1080.d014197 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
          (_root_.GD.N0232.N0720.N1214.d014261 m n g repaired) := by rw [htransport g]
    _ = ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired :=
      _root_.GD.N0232.N0720.N1215.d014284
        m n g theta repaired hrepairedMeasurable
    _ = ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p := by
      rw [hrisk theta]


theorem d014654
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p := by
  obtain ⟨repaired, _hrepairedMeasurable, hrepairedClass,
    hrepairedEquivariant⟩ := hrep
  intro g
  have hrepairedReference :
      repaired =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1214.d014265 m n p := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172] using hrepairedClass _root_.GD.N0232.N0720.N1080.d014169
  have htransportCongr :
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014261 m n g repaired :=
    _root_.GD.N0232.N0720.N1081.d014625 m n g hrepairedReference.symm
  have htransportRepaired : _root_.GD.N0232.N0720.N1214.d014261 m n g repaired = repaired := by
    funext omega
    calc
      _root_.GD.N0232.N0720.N1214.d014261 m n g repaired omega =
          g • repaired (g⁻¹ • omega) := rfl
      _ = repaired (g • (g⁻¹ • omega)) := by
        symm
        exact hrepairedEquivariant g (g⁻¹ • omega)
      _ = repaired omega := by rw [smul_inv_smul]
  have htransportFixed :
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p := by
    filter_upwards [htransportCongr, hrepairedReference] with omega hcongr hclass
    calc
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) omega =
          _root_.GD.N0232.N0720.N1214.d014261 m n g repaired omega := hcongr
      _ = repaired omega := congrFun htransportRepaired omega
      _ = _root_.GD.N0232.N0720.N1214.d014265 m n p omega := hclass
  unfold _root_.GD.N0232.N0720.N1159.d014642
  calc
    MemLp.toLp
          (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
          (_root_.GD.N0232.N0720.N1159.d014641 m n g p hp) =
        MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n p)
          (_root_.GD.N0232.N0720.N1214.d014268 m n p) :=
      MemLp.toLp_congr
        (_root_.GD.N0232.N0720.N1159.d014641 m n g p hp)
        (_root_.GD.N0232.N0720.N1214.d014268 m n p) htransportFixed
    _ = p := _root_.GD.N0232.N0720.N1214.d014269 m n p

include hm hn in

theorem d014655
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    (∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p) ↔
      _root_.GD.N0232.N0720.N1159.d014652 m n p := by
  constructor
  · intro hfixed
    exact _root_.GD.N0232.N0720.N1214.d014271
      m n hm hn p
      (fun g => _root_.GD.N0232.N0720.N1159.d014641 m n g p hp) hfixed
  · exact
      _root_.GD.N0232.N0720.N1159.d014654
        m n p hp

include hm hn in


theorem d014656
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0) ↔
      _root_.GD.N0232.N0720.N1159.d014652 m n
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
  let hpFinite : _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  rw [← _root_.GD.N0232.N0720.N1159.d014655 m n hm hn
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hpFinite]
  constructor
  · intro hzero g
    have hfixed :=
      (_root_.GD.N0232.N0720.N1159.d014651 m n s g).1 (hzero g)
    have hvalue := congrArg Subtype.val hfixed
    simpa only [_root_.GD.N0232.N0720.N1159.d014645, _root_.GD.N0232.N0720.N1159.d014646] using hvalue
  · intro hfixed g
    apply (_root_.GD.N0232.N0720.N1159.d014651 m n s g).2
    apply Subtype.ext
    simpa only [_root_.GD.N0232.N0720.N1159.d014645, _root_.GD.N0232.N0720.N1159.d014646] using hfixed g



def d014657
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014639 m n :=
  ⟨p,
    _root_.GD.N0232.N0720.N1159.d014640 m n p
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict,
    _root_.GD.N0232.N0720.N1159.d014653
      m n p hrep⟩

include hm hn in




theorem d014658
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p) :
    let s := _root_.GD.N0232.N0720.N1159.d014657 m n hm hn p hrep hstrict
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value = p ∧
      ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  dsimp only
  let s := _root_.GD.N0232.N0720.N1159.d014657 m n hm hn p hrep hstrict
  have hsvalue : s.value = p := rfl
  have hterminalS : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
    simpa only [hsvalue] using hterminal
  have heq : _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value :=
    (_root_.GD.N0232.N0720.N1159.d014635 m n s.value).2 hterminalS
  refine ⟨heq.trans hsvalue, ?_⟩
  apply (_root_.GD.N0232.N0720.N1159.d014656 m n hm hn s).2
  rw [heq]
  simpa only [hsvalue] using hrep






def d014659 : Prop :=
  ∃ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    _root_.GD.N0232.N0720.N1159.d014652 m n p ∧
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p









def d014660
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  Measurable d ∧
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) => g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) d ∧
    (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d <
        _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
    (∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable e →
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta d) →
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)


def d014661 : Prop :=
  ∃ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, _root_.GD.N0232.N0720.N1159.d014660 m n d



theorem d014662
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hde : d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] e) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta d = _root_.GD.N0232.N0720.N1080.d014197 m n theta e := by
  unfold _root_.GD.N0232.N0720.N1080.d014197
  apply lintegral_congr_ae
  filter_upwards [hde] with omega homega
  rw [homega]



theorem d014663
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p) :
    ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable repaired ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) => g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) repaired ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired = _root_.GD.N0232.N0720.N1080.d014182 m n theta p := by
  obtain ⟨repaired, hrepairedMeasurable, hrepairedClass,
    hrepairedEquivariant⟩ := hrep
  refine ⟨repaired, hrepairedMeasurable, hrepairedEquivariant, ?_⟩
  intro theta
  calc
    _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired =
        _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) :=
      _root_.GD.N0232.N0720.N1159.d014662 m n theta (hrepairedClass theta)
    _ = _root_.GD.N0232.N0720.N1080.d014182 m n theta p := _root_.GD.N0232.N0720.N1215.d014286 m n theta p

include hm hn in



theorem d014664 :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      _root_.GD.N0232.N0720.N1159.d014659 m n hm hn := by
  constructor
  · rintro ⟨d, hdMeasurable, hdEquivariant, hdStrict, hdTerminal⟩
    have hdMemLp : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
      apply _root_.GD.N0232.N0720.N1215.d014285 m n d hdMeasurable
      exact ne_top_of_lt (hdStrict _root_.GD.N0232.N0720.N1080.d014169)
    let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := MemLp.toLp d hdMemLp
    have hpRisk (theta : _root_.GD.N0232.N0720.N1080.d014168) :
        _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
      exact (_root_.GD.N0232.N0720.N1080.d014198 m n theta d hdMemLp).symm
    have hdClassReference :
        d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1214.d014265 m n p := by
      have hcoe : (fun omega => p omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] d := by
        simpa only [p] using hdMemLp.coeFn_toLp
      exact hcoe.symm.trans (_root_.GD.N0232.N0720.N1214.d014267 m n p).symm
    have hdClass : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1214.d014265 m n p := by
      intro theta
      exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
        hdClassReference
    have hpRepresentative :
        _root_.GD.N0232.N0720.N1159.d014652 m n p :=
      ⟨d, hdMeasurable, hdClass, hdEquivariant⟩
    have hpStrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p
        (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
      intro theta
      calc
        _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014197 m n theta d := hpRisk theta
        _ < _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n) := hdStrict theta
        _ = _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
          _root_.GD.N0232.N0720.N1080.d014199 m n hm hn theta
    have hpTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p := by
      intro e heDominates
      have heRawDominates : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n e) ≤
            _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
        intro theta
        rw [_root_.GD.N0232.N0720.N1215.d014286, ← hpRisk theta]
        exact heDominates theta
      have heClassReference :
          _root_.GD.N0232.N0720.N1214.d014265 m n e =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
            _root_.GD.N0232.N0720.N1214.d014265 m n p :=
        (hdTerminal (_root_.GD.N0232.N0720.N1214.d014265 m n e)
          (_root_.GD.N0232.N0720.N1214.d014266 m n e) heRawDominates
          _root_.GD.N0232.N0720.N1080.d014169).trans hdClassReference
      calc
        e = MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n e)
            (_root_.GD.N0232.N0720.N1214.d014268 m n e) :=
          (_root_.GD.N0232.N0720.N1214.d014269 m n e).symm
        _ = MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n p)
            (_root_.GD.N0232.N0720.N1214.d014268 m n p) :=
          MemLp.toLp_congr
            (_root_.GD.N0232.N0720.N1214.d014268 m n e)
            (_root_.GD.N0232.N0720.N1214.d014268 m n p) heClassReference
        _ = p := _root_.GD.N0232.N0720.N1214.d014269 m n p
    exact ⟨p, hpRepresentative, hpStrict, hpTerminal⟩
  · rintro ⟨p, hpRepresentative, hpStrict, hpTerminal⟩
    obtain ⟨repaired, hrepairedMeasurable, hrepairedClass,
      hrepairedEquivariant⟩ := hpRepresentative
    have hrepairedRisk : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired = _root_.GD.N0232.N0720.N1080.d014182 m n theta p := by
      intro theta
      calc
        _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired =
            _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) :=
          _root_.GD.N0232.N0720.N1159.d014662 m n theta (hrepairedClass theta)
        _ = _root_.GD.N0232.N0720.N1080.d014182 m n theta p :=
          _root_.GD.N0232.N0720.N1215.d014286 m n theta p
    refine ⟨repaired, hrepairedMeasurable, hrepairedEquivariant, ?_, ?_⟩
    · intro theta
      rw [hrepairedRisk theta,
        _root_.GD.N0232.N0720.N1080.d014199 m n hm hn theta]
      exact hpStrict theta
    · intro e heMeasurable heDominates
      have heMemLp : MemLp e 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
        apply _root_.GD.N0232.N0720.N1215.d014285 m n e heMeasurable
        apply ne_top_of_le_ne_top
          (show _root_.GD.N0232.N0720.N1080.d014197 m n _root_.GD.N0232.N0720.N1080.d014169 repaired ≠ ⊤ by
            rw [hrepairedRisk _root_.GD.N0232.N0720.N1080.d014169]
            exact ne_top_of_lt (hpStrict _root_.GD.N0232.N0720.N1080.d014169))
        exact heDominates _root_.GD.N0232.N0720.N1080.d014169
      let eL2 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := MemLp.toLp e heMemLp
      have heDominatesL2 : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) eL2 p := by
        intro theta
        calc
          _root_.GD.N0232.N0720.N1080.d014182 m n theta eL2 = _root_.GD.N0232.N0720.N1080.d014197 m n theta e :=
            (_root_.GD.N0232.N0720.N1080.d014198 m n theta e heMemLp).symm
          _ ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired := heDominates theta
          _ = _root_.GD.N0232.N0720.N1080.d014182 m n theta p := hrepairedRisk theta
      have heq : eL2 = p := hpTerminal eL2 heDominatesL2
      have heClassReference : e =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] repaired := by
        have heCoe : (fun omega => eL2 omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] e := by
          simpa only [eL2] using heMemLp.coeFn_toLp
        have heqCoe : (fun omega => eL2 omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
            fun omega => p omega := by
          rw [heq]
        have hpBorel :
            (fun omega => p omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
              _root_.GD.N0232.N0720.N1214.d014265 m n p :=
          (_root_.GD.N0232.N0720.N1214.d014267 m n p).symm
        have hBorelRepaired :
            _root_.GD.N0232.N0720.N1214.d014265 m n p =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] repaired := by
          have href := hrepairedClass _root_.GD.N0232.N0720.N1080.d014169
          simpa [_root_.GD.N0232.N0720.N1080.d014172] using href.symm
        exact heCoe.symm.trans
          (heqCoe.trans (hpBorel.trans hBorelRepaired))
      intro theta
      exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
        heClassReference









theorem d014665 :
    _root_.GD.N0232.N0720.N1159.d014659 m n hm hn ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  constructor
  · rintro ⟨p, hrep, hstrict, hterminal⟩
    let s : _root_.GD.N0232.N0720.N1159.d014639 m n :=
      ⟨p,
        _root_.GD.N0232.N0720.N1159.d014640 m n p
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict,
        _root_.GD.N0232.N0720.N1159.d014653
          m n p hrep⟩
    refine ⟨s, hstrict, ?_⟩
    apply (_root_.GD.N0232.N0720.N1159.d014656 m n hm hn s).2
    have heq : _root_.GD.N0232.N0720.N1159.d014633 m n s.value = p :=
      (_root_.GD.N0232.N0720.N1159.d014635 m n p).2 hterminal
    simpa only [s, heq] using hrep
  · rintro ⟨s, hstrict, hzero⟩
    refine ⟨_root_.GD.N0232.N0720.N1159.d014633 m n s.value, ?_, ?_, ?_⟩
    · exact (_root_.GD.N0232.N0720.N1159.d014656 m n hm hn s).1 hzero
    · exact _root_.GD.N0232.N0720.N1159.d014636
        m n s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict
    · exact (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.1






theorem d014666 :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  exact
    (_root_.GD.N0232.N0720.N1159.d014664
      m n hm hn).trans
      (_root_.GD.N0232.N0720.N1159.d014665
        m n hm hn)




theorem d014667
    (hnot : ¬ _root_.GD.N0232.N0720.N1159.d014659 m n hm hn)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ g : _root_.GD.N0232.N0719.N0946.d009229, 0 < _root_.GD.N0232.N0720.N1159.d014647 m n s g := by
  by_contra hnone
  have hzero : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
    intro g
    have hnotpos : ¬ 0 < _root_.GD.N0232.N0720.N1159.d014647 m n s g := by
      exact fun hpos => hnone ⟨g, hpos⟩
    exact le_antisymm (le_of_not_gt hnotpos)
      (_root_.GD.N0232.N0720.N1159.d014650 m n s g)
  apply hnot
  exact (_root_.GD.N0232.N0720.N1159.d014665
    m n hm hn).2 ⟨s, hstrict, hzero⟩



theorem d014668
    (hnot : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ g : _root_.GD.N0232.N0719.N0946.d009229, 0 < _root_.GD.N0232.N0720.N1159.d014647 m n s g := by
  apply _root_.GD.N0232.N0720.N1159.d014667
    m n hm hn
  · intro hclass
    exact hnot
      ((_root_.GD.N0232.N0720.N1159.d014664
        m n hm hn).2 hclass)
  · exact hstrict

end

end N1159
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1159.d014635
#print axioms _root_.GD.N0232.N0720.N1159.d014651
#print axioms _root_.GD.N0232.N0720.N1159.d014656
#print axioms _root_.GD.N0232.N0720.N1159.d014658
#print axioms _root_.GD.N0232.N0720.N1159.d014664
#print axioms _root_.GD.N0232.N0720.N1159.d014665
#print axioms _root_.GD.N0232.N0720.N1159.d014666
#print axioms _root_.GD.N0232.N0720.N1159.d014667
#print axioms _root_.GD.N0232.N0720.N1159.d014668
