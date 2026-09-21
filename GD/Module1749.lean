import GD.Module1748
import GD.Module1716

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0019
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0092
open _root_.GD.N0213.N0502
open _root_.GD.N0230.N0611

variable {k : ℕ} (sizes : Fin k → ℕ)


def d028998 : Set (_root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :=
  _root_.GD.N0092.d023968 k sizes ∩ _root_.GD.N0232.N0719.N0962.d012185 k sizes


def d028999 (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : Prop :=
  ∃ a ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes, d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] a

theorem d029000 (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (ha : d ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes d) :
    ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes d := by
  intro ht
  apply _root_.GD.N0212.N0466.d028993 hk sizes hn
  refine ⟨d, ha.1, ?_, hs, ht⟩
  intro g ω
  simpa only [_root_.GD.N0232.N0719.N0946.d009258,
    _root_.GD.N0232.N0719.N0946.d009229.d009244] using
    ha.2 g.shift g.d009239 g.d009240 ω

theorem d029001 (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0019.d028998 sizes = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro d hd
  exact _root_.GD.N0019.d029000 sizes hk hn hd.2 hd.1.2.1 hd.1.2.2

theorem d029002 (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0019.d028998 sizes) = ⊤ := by
  rw [_root_.GD.N0019.d029001 sizes hk hn]
  simp [_root_.GD.N0230.N0611.d003517]


theorem d029003
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hd : d ∈ _root_.GD.N0092.d023968 k sizes) :
    ¬ _root_.GD.N0019.d028999 sizes d := by
  rintro ⟨a, ha, hda⟩
  have hae (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] a :=
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hda
  have hr (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ a :=
    _root_.GD.N0232.N0719.N0896.d011094 k sizes θ (hae θ)
  have hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes a := by
    intro θ
    rw [← hr θ]
    exact hd.2.1 θ
  apply _root_.GD.N0019.d029000 sizes hk hn ha hs
  intro e he hedom θ
  have hed : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d := by
    intro θ
    rw [hr θ]
    exact hedom θ
  exact (hd.2.2 e he hed θ).trans (hae θ)


theorem d029004
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {d a : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hd : d ∈ _root_.GD.N0092.d023968 k sizes) (ha : a ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : ¬ d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] a := by
  intro hda
  apply _root_.GD.N0019.d029003 sizes hk hn hd
  refine ⟨a, ha, ?_⟩
  exact (_root_.GD.N0232.N0719.d009183
    k sizes θ.location θ.scale θ.scale_pos).2.ae_le hda


theorem d029005
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) ≠ ⊤ := by
  rw [_root_.GD.N0092.d028702 sizes hk hn]
  exact _root_.GD.N0092.d028701 sizes hk hn


theorem d029006
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) <
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0019.d028998 sizes) := by
  rw [_root_.GD.N0019.d029002 sizes hk (fun i => by have := hn i; omega)]
  exact lt_top_iff_ne_top.mpr (_root_.GD.N0019.d029005 sizes hk hn)



theorem d029007
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) (ε : ℝ) (hε : 0 < ε) :
    ∃ d ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d <
        ENNReal.ofReal ((_root_.GD.N0213.N0502.d022051 k sizes).toReal + ε) ∧
      ¬ _root_.GD.N0019.d028999 sizes d := by
  obtain ⟨d, hd, hcap⟩ := _root_.GD.N0092.d028703 sizes hk hn ε hε
  exact ⟨d, hd, hcap, _root_.GD.N0019.d029003 sizes hk
    (fun i => by have := hn i; omega) hd⟩

end
end GD.N0019

#print axioms _root_.GD.N0019.d029000
#print axioms _root_.GD.N0019.d029001
#print axioms _root_.GD.N0019.d029002
#print axioms _root_.GD.N0019.d029003
#print axioms _root_.GD.N0019.d029004
#print axioms _root_.GD.N0019.d029005
#print axioms _root_.GD.N0019.d029006
#print axioms _root_.GD.N0019.d029007
