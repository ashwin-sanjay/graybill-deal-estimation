import GD.Module1835
import GD.Module1855

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0048
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0611
open _root_.GD.N0022.N0255
open _root_.GD.N0023



theorem d030448
    (C : ℝ) (hC : 0 ≤ C) (d : _root_.GD.N0232.N0720.N1080.d014170 2 5 → ℝ) (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 5 θ d ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 2 5 θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 5 θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 2 5 θ (_root_.GD.N0232.N0720.N1080.d014175 2 5)) : False := by
  obtain ⟨g, hg, hb, hbound⟩ :=
    _root_.GD.N0020.d030259
      2 5 (by decide) (by decide) C hC d hd hcap hbase
  exact _root_.GD.N0029.d030441 g hg hb (C - 1)
    (_root_.GD.N0023.N0262.d021914 2 5 (by decide) (by decide)
      g hg hb C hC (fun θ => (hbound θ).1))
    (_root_.GD.N0023.N0262.d021920 2 5 (by decide) (by decide)
      g hg hb (fun θ => (hbound θ).2))


theorem d030449
    (C : ℝ) (hC : 0 ≤ C) (d : _root_.GD.N0232.N0720.N1080.d014170 5 2 → ℝ) (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 5 2 θ d ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 5 2 θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 5 2 θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 5 2 θ (_root_.GD.N0232.N0720.N1080.d014175 5 2)) : False := by
  apply _root_.GD.N0048.d030448 C hC
    (d ∘ _root_.GD.N0232.N0720.N1101.d019094 2 5) (hd.comp measurable_swap)
  · intro θ
    rw [_root_.GD.N0232.N0720.N1101.d019101 2 5 θ d hd]
    simpa only [_root_.GD.N0232.N0720.N1257.d015508, _root_.GD.N0232.N0720.N1043.d019058, add_comm]
      using hcap (_root_.GD.N0232.N0720.N1043.d019058 θ)
  · intro θ
    rw [_root_.GD.N0232.N0720.N1101.d019101 2 5 θ d hd]
    exact (hbase (_root_.GD.N0232.N0720.N1043.d019058 θ)).trans_eq
      (_root_.GD.N0232.N0720.N1101.d019106 2 5
        (by decide) (by decide) θ).symm

theorem d030450
    (m n : ℕ) (hm : 1 ≤ m)
    (hno : ∀ (C : ℝ), 0 ≤ C → ∀ (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ), Measurable d →
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n θ)) →
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) → False)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : d ∈ _root_.GD.N0022.N0255.d030393 m n) :
    _root_.GD.N0232.N0720.N1256.d015548 m n d = ⊤ := by
  by_contra hfinite
  let C := (_root_.GD.N0232.N0720.N1256.d015548 m n d).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  apply hno C hC d hd.1 _ hd.2
  intro θ
  apply (_root_.GD.N0232.N0720.N1256.d015553 m n hm C hC θ d).mp
  exact (le_iSup (fun η => _root_.GD.N0232.N0720.N1256.d015547 m n η d) θ).trans_eq
    (ENNReal.ofReal_toReal hfinite).symm



theorem d030451
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 5 → ℝ) (hd : d ∈ _root_.GD.N0022.N0255.d030393 2 5) :
    _root_.GD.N0232.N0720.N1256.d015548 2 5 d = ⊤ :=
  _root_.GD.N0048.d030450 2 5 (by decide)
    _root_.GD.N0048.d030448 d hd

theorem d030452
    (d : _root_.GD.N0232.N0720.N1080.d014170 5 2 → ℝ) (hd : d ∈ _root_.GD.N0022.N0255.d030393 5 2) :
    _root_.GD.N0232.N0720.N1256.d015548 5 2 d = ⊤ :=
  _root_.GD.N0048.d030450 5 2 (by decide)
    _root_.GD.N0048.d030449 d hd

theorem d030453 : _root_.GD.N0022.N0255.d030394 2 5 = ⊤ := by
  apply top_unique
  apply le_iInf
  intro d
  apply le_iInf
  intro hd
  exact le_of_eq (_root_.GD.N0048.d030451 d hd).symm

theorem d030454 : _root_.GD.N0022.N0255.d030394 5 2 = ⊤ := by
  apply top_unique
  apply le_iInf
  intro d
  apply le_iInf
  intro hd
  exact le_of_eq (_root_.GD.N0048.d030452 d hd).symm



theorem d030455 :
    _root_.GD.N0232.N0720.N1256.d015549 2 5 ≠ ⊤ ∧ _root_.GD.N0022.N0255.d030394 2 5 = ⊤ :=
  ⟨_root_.GD.N0030.d023898, _root_.GD.N0048.d030453⟩



theorem d030456
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 5 → ℝ) (hd : d ∈ _root_.GD.N0022.N0255.d030393 2 5) :
    d ∈ _root_.GD.N0232.N0720.N1256.d015551 2 5 ∧
      ∀ C : ℝ, ∃ θ, ENNReal.ofReal C < _root_.GD.N0232.N0720.N1256.d015547 2 5 θ d := by
  refine ⟨⟨hd.1, fun θ => ?_⟩, fun C => ?_⟩
  · have hbase : _root_.GD.N0232.N0720.N1080.d014197 2 5 θ (_root_.GD.N0232.N0720.N1080.d014175 2 5) ≠ ⊤ := by
      rw [_root_.GD.N0232.N0720.N1080.d014199 2 5 (by decide) (by decide),
        _root_.GD.N0232.N0720.N1080.d014184 2 5 (by decide) (by decide)]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hbase (hd.2 θ)
  · have h : ENNReal.ofReal C < _root_.GD.N0232.N0720.N1256.d015548 2 5 d := by
      rw [_root_.GD.N0048.d030451 d hd]
      exact ENNReal.ofReal_lt_top
    exact (lt_iSup_iff).mp h


theorem d030457
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 5 → ℝ) (hd : Measurable d)
    (hfinite : _root_.GD.N0232.N0720.N1256.d015548 2 5 d ≠ ⊤) :
    ∃ θ, _root_.GD.N0232.N0720.N1080.d014197 2 5 θ (_root_.GD.N0232.N0720.N1080.d014175 2 5) < _root_.GD.N0232.N0720.N1080.d014197 2 5 θ d := by
  by_contra hnot
  apply hfinite (_root_.GD.N0048.d030451 d ⟨hd, ?_⟩)
  intro θ
  exact not_lt.mp (fun hθ => hnot ⟨θ, hθ⟩)




theorem d030458 :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 2 5,
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 5 θ d < _root_.GD.N0232.N0720.N1080.d014197 2 5 θ (_root_.GD.N0232.N0720.N1080.d014175 2 5)) ∧
      (∀ e : _root_.GD.N0232.N0720.N1080.d014170 2 5 → ℝ, Measurable e →
        (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 5 θ e ≤ _root_.GD.N0232.N0720.N1080.d014197 2 5 θ d) →
        ∀ θ, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 5 θ] d) ∧
      _root_.GD.N0232.N0720.N1256.d015548 2 5 d = _root_.GD.N0022.N0255.d030394 2 5 := by
  let d := _root_.GD.N0232.N0720.N1080.d014194 2 5 (by decide) (by decide)
  have hd : Measurable d := _root_.GD.N0232.N0720.N1080.d014195 2 5 (by decide) (by decide)
  have hs := _root_.GD.N0232.N0720.N1080.d014201 2 5 (by decide) (by decide)
  have hb : d ∈ _root_.GD.N0022.N0255.d030393 2 5 := ⟨hd, fun θ => (hs θ).le⟩
  refine ⟨d, ⟨hd, fun θ => ne_top_of_lt (hs θ)⟩, hs, ?_, ?_⟩
  · exact _root_.GD.N0232.N0720.N1080.d014202 2 5 (by decide) (by decide)
  · rw [_root_.GD.N0048.d030451 d hb,
      _root_.GD.N0048.d030453]

end
end GD.N0048

#print axioms _root_.GD.N0048.d030448
#print axioms _root_.GD.N0048.d030449
#print axioms _root_.GD.N0048.d030450
#print axioms _root_.GD.N0048.d030451
#print axioms _root_.GD.N0048.d030452
#print axioms _root_.GD.N0048.d030453
#print axioms _root_.GD.N0048.d030454
#print axioms _root_.GD.N0048.d030455
#print axioms _root_.GD.N0048.d030456
#print axioms _root_.GD.N0048.d030457
#print axioms _root_.GD.N0048.d030458
