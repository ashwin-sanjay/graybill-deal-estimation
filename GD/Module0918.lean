import GD.Module0144
import GD.Module0914
import GD.Module0917


























open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1025

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0230.N0553
open _root_.GD.N0230.N0585
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0718
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

abbrev d014301 :=
  _root_.GD.N0232.N0719.N0946.d009229


abbrev d014302 := _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)


abbrev d014303 := WeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)



def d014304 : Set (_root_.GD.N0232.N0720.N1025.d014303 m n) :=
  toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) '' _root_.GD.N0232.N0720.N1080.d014187 m n hm hn


def d014305
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ENNReal :=
  _root_.GD.N0232.N0720.N1080.d014182 m n theta ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm d)



theorem d014306 (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ↔
      (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm d ∈
        _root_.GD.N0232.N0720.N1080.d014187 m n hm hn := by
  constructor
  · rintro ⟨e, he, rfl⟩
    simpa using he
  · intro hd
    exact ⟨(toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm d, hd, by simp⟩



def d014307 :
    _root_.GD.N0232.N0720.N1080.d014187 m n hm hn ≃ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn where
  toFun p := ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) p.1,
    ⟨p.1, p.2, rfl⟩⟩
  invFun p :=
    ⟨(toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p.1,
      (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn p.1).1 p.2⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv p := by
    apply Subtype.ext
    simp

@[simp] theorem d014308
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn p).1 =
      toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) p.1 := rfl

@[simp] theorem d014309
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).1 =
      (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p.1 := rfl



theorem d014310 :
    (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn).Nonempty := by
  refine ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn), ?_⟩
  exact ⟨_root_.GD.N0232.N0720.N1080.d014181 m n hm hn,
    _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn), rfl⟩


theorem d014311 :
    IsCompact (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  exact _root_.GD.N0232.N0720.N1080.d014251 m n hm hn


theorem d014312 :
    Convex ℝ (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  exact (_root_.GD.N0232.N0720.N1080.d014189 m n hm hn).linear_image
    (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).toLinearMap



theorem d014313 (e d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) e d ↔
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm e)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm d) := by
  rfl



theorem d014314 :
    _root_.GD.N0230.N0616.d000721 (_root_.GD.N0232.N0720.N1025.d014305 m n) (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  intro d e hd he
  apply (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn e).2
  exact _root_.GD.N0230.N0608.d000678
    (_root_.GD.N0232.N0720.N1080.d014182 m n)
    ((_root_.GD.N0232.N0720.N1025.d014306 m n hm hn d).1 hd)
    ((_root_.GD.N0232.N0720.N1025.d014313 m n e d).1 he)



theorem d014315 (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n) d ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm d) := by
  constructor
  · intro hd e he
    have hweak : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n)
        (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) e) d := by
      exact (_root_.GD.N0232.N0720.N1025.d014313 m n _ _).2 (by simpa using he)
    have heq := hd (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) e) hweak
    exact (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).injective (by simpa using heq)
  · intro hd e he
    have hstrong : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm e)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm d) :=
      (_root_.GD.N0232.N0720.N1025.d014313 m n e d).1 he
    have heq := hd _ hstrong
    apply (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm.injective
    simpa using heq



def d014316 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0232.N0720.N1025.d014304 m n hm hn → _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
  _root_.GD.N0232.N0720.N1025.d014307 m n hm hn ∘
    _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g ∘
      (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm

@[simp] theorem d014317 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p =
      _root_.GD.N0232.N0720.N1025.d014307 m n hm hn
        (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p)) := rfl



theorem d014318
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p) :
    ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p) =
      (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p := by
  intro g
  apply (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).injective
  simpa [_root_.GD.N0232.N0720.N1025.d014316] using hfixed g















theorem
    d014319
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (profile : K → _root_.GD.N0232.N0720.N1025.d014303 m n → ℝ)
    (profileTax : K → _root_.GD.N0232.N0720.N1025.d014303 m n →
      _root_.GD.N0232.N0720.N1025.d014303 m n → ℝ)
    (objective : _root_.GD.N0232.N0720.N1025.d014303 m n → ℝ)
    (hobjectiveLsc : LowerSemicontinuousOn objective
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn))
    (hLUB : ∀ d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
      IsLUB (Set.range (fun k ↦ profile k d)) (objective d))
    (hcontinuous : ∀ d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
      Continuous (fun k ↦ profile k d))
    (hexact : ∀ p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
      ∀ q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn, ∀ k,
        profile k (_root_.GD.N0230.N0718.d001528 p q) + profileTax k p q =
          (profile k p + profile k q) / 2)
    (htax : ∀ p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
      ∀ q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn, ∀ k,
        0 ≤ profileTax k p q)
    (hfaithful : _root_.GD.N0230.N0553.d001612
      profile profileTax objective (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn))
    (hmono : _root_.GD.N0230.N0585.d001305 (_root_.GD.N0232.N0720.N1025.d014305 m n) objective)
    (hpreserve : ∀ (g : _root_.GD.N0232.N0720.N1025.d014301)
      (d : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn),
      objective (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g d :
        _root_.GD.N0232.N0720.N1025.d014303 m n) = objective d.1) :
    ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable repaired ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0720.N1025.d014301) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0720.N1025.d014301) (y : ℝ) ↦ g • y) repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired <
          _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      (∀ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
        Measurable d →
        (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
            _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired) →
        ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] repaired) := by
  have hlscResidual : ∀ p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
      ∀ q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
      LowerSemicontinuous (fun k ↦
        profileTax k p q +
          _root_.GD.N0230.N0554.d001565
            profile objective k p q) := by
    intro p hp q hq
    exact
      _root_.GD.N0230.N0587.d001594
        profile profileTax objective p q
        (hexact p hp q hq)
        (hcontinuous (_root_.GD.N0230.N0718.d001528 p q)
          (_root_.GD.N0232.N0720.N1025.d014312 m n hm hn hp hq
            (by norm_num) (by norm_num) (by norm_num)))
  obtain ⟨pC, _hpMin, hpFixed, hpTerminal⟩ :=
    _root_.GD.N0230.N0553.d001614
      profile profileTax (_root_.GD.N0232.N0720.N1025.d014305 m n) objective
      (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014310 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014311 m n hm hn)
      hobjectiveLsc
      (_root_.GD.N0232.N0720.N1025.d014312 m n hm hn)
      hLUB hexact htax hlscResidual hfaithful
      (_root_.GD.N0232.N0720.N1025.d014314 m n hm hn)
      hmono hpreserve
  let p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm pC
  have hpStrongTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p.1 := by
    exact (_root_.GD.N0232.N0720.N1025.d014315 m n pC.1).1 hpTerminal
  have hpStrongFixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g p = p := by
    exact _root_.GD.N0232.N0720.N1025.d014318
      m n hm hn pC hpFixed
  exact
    _root_.GD.N0232.N0720.N1215.d014300
      m n hm hn p hpStrongTerminal hpStrongFixed

end

end N1025
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1025.d014314
#print axioms _root_.GD.N0232.N0720.N1025.d014315
#print axioms _root_.GD.N0232.N0720.N1025.d014318
#print axioms _root_.GD.N0232.N0720.N1025.d014319
