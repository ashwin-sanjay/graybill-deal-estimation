import GD.Module0091
import GD.Module1067
import GD.Module0948



























open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1147

noncomputable section

open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0232.N0720.N1065
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1105
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1483

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)




def d017285
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n) : Set (_root_.GD.N0232.N0720.N1025.d014303 m n) :=
  toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) '' _root_.GD.N0232.N0720.N1159.d014630 m n p

theorem d017286
    (p d : _root_.GD.N0232.N0720.N1025.d014302 m n) :
    toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d ∈
        _root_.GD.N0232.N0720.N1147.d017285 m n p ↔
      d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n p := by
  constructor
  · rintro ⟨e, he, hde⟩
    have : e = d := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).injective hde
    simpa [this] using he
  · intro hd
    exact ⟨d, hd, rfl⟩

theorem d017287
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n) :
    (_root_.GD.N0232.N0720.N1147.d017285 m n p).Nonempty := by
  refine ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) p, ?_⟩
  exact ⟨p, _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) p, rfl⟩

theorem d017288
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n) :
    Convex ℝ (_root_.GD.N0232.N0720.N1147.d017285 m n p) := by
  exact (_root_.GD.N0232.N0720.N1159.d014632 m n p).linear_image
    (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).toLinearMap

theorem d017289
    (p d : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n p) :
    ‖d‖ ≤ ‖p‖ := by
  have href := hd _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hsquare : ‖d‖ ^ 2 ≤ ‖p‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp href
  nlinarith [norm_nonneg d, norm_nonneg p]

theorem d017290
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n) :
    IsCompact (_root_.GD.N0232.N0720.N1147.d017285 m n p) := by
  exact _root_.GD.N0230.N0633.d001201
    ‖p‖ (_root_.GD.N0232.N0720.N1159.d014632 m n p) (_root_.GD.N0232.N0720.N1159.d014631 m n p)
    (fun d hd ↦ _root_.GD.N0232.N0720.N1147.d017289 m n p d hd)

theorem d017291
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n) :
    _root_.GD.N0230.N0709.d001221 (_root_.GD.N0232.N0720.N1147.d017285 m n p) := by
  unfold _root_.GD.N0230.N0709.d001221 _root_.GD.N0232.N0720.N1147.d017285
  have himage :
      (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm ''
          (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) '' _root_.GD.N0232.N0720.N1159.d014630 m n p) =
        _root_.GD.N0232.N0720.N1159.d014630 m n p := by
    ext d
    constructor
    · rintro ⟨w, ⟨e, he, rfl⟩, rfl⟩
      simpa using he
    · intro hd
      exact ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d,
        ⟨d, hd, rfl⟩, by simp⟩
  rw [himage]
  rw [isBounded_iff_forall_norm_le]
  exact ⟨‖p‖, fun d hd ↦ _root_.GD.N0232.N0720.N1147.d017289 m n p d hd⟩

theorem d017292
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1147.d017285 m n p ⊆ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := by
  rintro _ ⟨d, hd, rfl⟩
  exact ⟨d, _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n) hp hd, rfl⟩



theorem d017293
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    MapsTo (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g)
      (_root_.GD.N0232.N0720.N1147.d017285 m n p)
      (_root_.GD.N0232.N0720.N1147.d017285 m n p) := by
  intro w hw
  obtain ⟨d, hd, rfl⟩ := hw
  have hdOuter : d ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n) hp hd
  have hweakOuter : toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d ∈
      _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := ⟨d, hdOuter, rfl⟩
  rw [_root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hweakOuter]
  refine ⟨_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d hdOuter, ?_, ?_⟩
  · intro eta
    let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
    have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by simp [theta]
    rw [← heta,
      _root_.GD.N0232.N0720.N1215.d014290 m n hm hn g theta d hdOuter,
      hcharacter g theta]
    exact mul_le_mul_of_nonneg_left (hd theta) bot_le
  · rfl





theorem d017294
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n p) :
    ∃ r : _root_.GD.N0232.N0720.N1025.d014302 m n,
      r ∈ _root_.GD.N0232.N0720.N1159.d014630 m n p ∧
      r ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn ∧
      ∀ hr : r ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn, ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
        _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g r
          hr = r := by
  let C := _root_.GD.N0232.N0720.N1147.d017285 m n p
  let inner : ℝ → _root_.GD.N0232.N0720.N1025.d014303 m n → _root_.GD.N0232.N0720.N1025.d014303 m n :=
    fun t ↦ _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)
  let outer : ℝ → _root_.GD.N0232.N0720.N1025.d014303 m n → _root_.GD.N0232.N0720.N1025.d014303 m n :=
    fun s ↦ _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)
  have hCsubset : C ⊆ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1147.d017292 m n hm hn p hp
  obtain ⟨x, hxC, hxinner, hxouter⟩ :=
    _root_.GD.N0230.N0710.d001248
      inner outer C
      (_root_.GD.N0232.N0720.N1147.d017290 m n p)
      (_root_.GD.N0232.N0720.N1147.d017288 m n p)
      (_root_.GD.N0232.N0720.N1147.d017287 m n p)
      (_root_.GD.N0232.N0720.N1147.d017291 m n p)
      (fun t ↦ _root_.GD.N0232.N0720.N1147.d017293 m n hm hn p hp hcharacter
        (_root_.GD.N0232.N0720.N1065.d014602 t))
      (fun t ↦ (_root_.GD.N0232.N0720.N1483.d014905
        m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)).mono hCsubset)
      (fun t u hu v hv a b ha hb hab ↦
        _root_.GD.N0232.N0720.N1065.d014586 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)
          (hCsubset hu) (hCsubset hv) ha hb hab)
      (_root_.GD.N0232.N0720.N1065.d014609 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014611 m n hm hn)
      (fun s ↦ _root_.GD.N0232.N0720.N1147.d017293 m n hm hn p hp hcharacter
        (_root_.GD.N0232.N0720.N1065.d014603 s))
      (fun s ↦ (_root_.GD.N0232.N0720.N1483.d014905
        m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)).mono hCsubset)
      (fun s u hu v hv a b ha hb hab ↦
        _root_.GD.N0232.N0720.N1065.d014586 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)
          (hCsubset hu) (hCsubset hv) ha hb hab)
      (_root_.GD.N0232.N0720.N1065.d014610 m n hm hn)
  have hxOuter : x ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := hCsubset hxC
  change x ∈ _root_.GD.N0232.N0720.N1147.d017285 m n p at hxC
  obtain ⟨r, hrp, hrx⟩ := hxC
  subst x
  have hrOuter : r ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n) hp hrp
  refine ⟨r, hrp, hrOuter, ?_⟩
  intro hr g
  have hfactor := _root_.GD.N0232.N0720.N1065.d014606 g
  have hmul := _root_.GD.N0232.N0720.N1065.d014596 m n hm hn
    (_root_.GD.N0232.N0720.N1065.d014602 g.shift) (_root_.GD.N0232.N0720.N1065.d014603 g.logScale) hxOuter
  have hfixedAmbient :
      _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g
          (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r) =
        toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r := by
    rw [← hfactor, ← hmul]
    change inner g.shift
      (outer g.logScale (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r)) =
        toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r
    rw [hxouter g.logScale, hxinner g.shift]
  let w : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r, hxOuter⟩
  have hweakFixed : _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g w = w := by
    apply Subtype.ext
    change (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g w).1 =
      toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) r
    rw [← _root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hxOuter]
    exact hfixedAmbient
  have hstrongFixed :
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm w) =
        (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm w := by
    apply (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).injective
    simpa only [_root_.GD.N0232.N0720.N1025.d014316, Function.comp_apply,
      Equiv.apply_symm_apply] using hweakFixed
  have hwStrong :
      (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm w = ⟨r, hrOuter⟩ := by
    apply Subtype.ext
    change r = r
    rfl
  rw [hwStrong] at hstrongFixed
  have hvalue := congrArg Subtype.val hstrongFixed
  have hcanonical :
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g r hrOuter = r := by
    simpa only [_root_.GD.N0232.N0720.N1215.d014298] using hvalue
  rw [show hr = hrOuter from Subsingleton.elim _ _]
  exact hcanonical





theorem d017295
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n
      (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn))
    (hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n p) :
    ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014182 m n theta p =
        _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) := by
  have hpOuter : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn) hp
  obtain ⟨r, hrp, hrOuter, hrfixed⟩ :=
    _root_.GD.N0232.N0720.N1147.d017294
      m n hm hn p hpOuter hcharacter
  have hrq : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) r
      (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) :=
    _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n) hp hrp
  have hrequal : r = _root_.GD.N0232.N0720.N1029.d015364 m n hm hn :=
    _root_.GD.N0232.N0720.N1029.d015369
      m n hm hn r hrq hrfixed
  intro theta
  apply le_antisymm (hp theta)
  rw [← hrequal]
  exact hrp theta

theorem d017296
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n)
    (hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n
      (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn))
    (hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n p) :
    ‖p‖ ^ 2 = ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 := by
  have href := _root_.GD.N0232.N0720.N1147.d017295
    m n hm hn p hp hcharacter _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  apply le_antisymm
  · exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp href.le
  · exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp href.ge



theorem d017297
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hgap : 0 < _root_.GD.N0232.N0720.N1201.d015333 m n
      (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)) :
    ¬ _root_.GD.N0232.N0720.N1105.d017120 m n kappa (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) := by
  rintro ⟨p, hp, hcharacter, _htax, hnorm⟩
  have hnormEq :=
    _root_.GD.N0232.N0720.N1147.d017296
      m n hm hn p hp hcharacter
  have hpositive : 0 < kappa * _root_.GD.N0232.N0720.N1201.d015333 m n
      (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) := mul_pos hkappa hgap
  change ‖p‖ ^ 2 ≤ ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 -
    kappa * _root_.GD.N0232.N0720.N1201.d015333 m n
      (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) at hnorm
  rw [hnormEq] at hnorm
  have hnonpos :
      kappa * _root_.GD.N0232.N0720.N1201.d015333 m n
        (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) ≤ 0 := by
    nlinarith only [hnorm]
  exact (not_lt_of_ge hnonpos) hpositive



theorem d017298
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hcap : ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) s.value →
      0 < _root_.GD.N0232.N0720.N1201.d015333 m n s →
      _root_.GD.N0232.N0720.N1105.d017120 m n kappa s) :
    _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) = 0 := by
  rcases (_root_.GD.N0232.N0720.N1201.d015334 m n
    (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)).lt_or_eq with hpos | hzero
  · exact False.elim
      ((_root_.GD.N0232.N0720.N1147.d017297
        m n hm hn kappa hkappa hpos)
        (hcap (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
          (_root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n)
            (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)) hpos))
  · exact hzero.symm



theorem d017299
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hcap : ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) s.value →
      0 < _root_.GD.N0232.N0720.N1201.d015333 m n s →
      _root_.GD.N0232.N0720.N1105.d017120 m n kappa s) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1029.d015374
    m n hm hn
  exact _root_.GD.N0232.N0720.N1147.d017298
    m n hm hn kappa hkappa hcap

end

end N1147
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1147.d017295
#print axioms _root_.GD.N0232.N0720.N1147.d017297
#print axioms _root_.GD.N0232.N0720.N1147.d017298
