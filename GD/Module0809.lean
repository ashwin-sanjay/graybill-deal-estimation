import GD.Module0804
















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0719.N0970

noncomputable section

open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0969
open _root_.GD.N0232.N0719.N0968
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0611

variable (k : ℕ) (sizes : Fin k → ℕ)



def d012309 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : Prop :=
  ∀ e : _root_.GD.N0232.N0719.d009173 k sizes → ℝ, Measurable e →
    (∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d) →
    ∀ theta, e =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] d


def d012310 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : Prop :=
  ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d <
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes)



theorem d012311
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p) :
    _root_.GD.N0232.N0719.N0970.d012309 k sizes (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) := by
  intro e he hdom
  have heFinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) e ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (hdom (_root_.GD.N0232.N0719.N0859.d010810 k))
    rw [_root_.GD.N0232.N0719.N0896.d011093, _root_.GD.N0232.N0719.N0859.d010829]
    exact ENNReal.ofReal_ne_top
  have heMem := _root_.GD.N0232.N0719.N0896.d011095 k sizes e he heFinite
  let eL2 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    MemLp.toLp e heMem
  have hdomL2 : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) eL2 p := by
    intro theta
    rw [show _root_.GD.N0232.N0719.N0859.d010821 k sizes theta eL2 = _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e from
      (_root_.GD.N0232.N0719.N0859.d010841 k sizes theta e heMem).symm,
      ← _root_.GD.N0232.N0719.N0896.d011093]
    exact hdom theta
  have heq : eL2 = p := hp eL2 hdomL2
  have heCoe : (fun omega ↦ eL2 omega) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] e := heMem.coeFn_toLp
  have heClass : (fun omega ↦ eL2 omega) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] fun omega ↦ p omega := by
    rw [heq]
  have href : e =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N0896.d011088 k sizes p :=
    heCoe.symm.trans (heClass.trans (_root_.GD.N0232.N0719.N0896.d011090 k sizes p).symm)
  intro theta
  exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta).ae_le href


def d012312 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  MemLp.toLp d (_root_.GD.N0232.N0719.N0896.d011095 k sizes d hd.1
    (hd.2 (_root_.GD.N0232.N0719.N0859.d010810 k)))

theorem d012313 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0970.d012312 k sizes d hd) = _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d :=
  (_root_.GD.N0232.N0719.N0859.d010841 k sizes theta d _).symm


def d012314 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0896.d011088 k sizes (_root_.GD.N0232.N0719.N0896.d011099 k sizes (_root_.GD.N0232.N0719.N0970.d012312 k sizes d hd))

theorem d012315 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0970.d012314 k sizes d hd) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
  rw [_root_.GD.N0232.N0719.N0970.d012314, _root_.GD.N0232.N0719.N0896.d011093, ← _root_.GD.N0232.N0719.N0970.d012313 k sizes d hd]
  exact (_root_.GD.N0232.N0719.N0896.d011100 k sizes (_root_.GD.N0232.N0719.N0970.d012312 k sizes d hd)).1 theta

theorem d012316 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    _root_.GD.N0232.N0719.N0970.d012314 k sizes d hd ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := by
  refine ⟨_root_.GD.N0232.N0719.N0896.d011089 k sizes _, ?_⟩
  intro theta
  exact ne_top_of_le_ne_top (hd.2 theta) (_root_.GD.N0232.N0719.N0970.d012315 k sizes d hd theta)

theorem d012317 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    _root_.GD.N0232.N0719.N0970.d012309 k sizes (_root_.GD.N0232.N0719.N0970.d012314 k sizes d hd) :=
  _root_.GD.N0232.N0719.N0970.d012311 k sizes _
    (_root_.GD.N0232.N0719.N0896.d011100 k sizes (_root_.GD.N0232.N0719.N0970.d012312 k sizes d hd)).2.1

theorem d012318 {e d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ}
    (h : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes e ≤ _root_.GD.N0232.N0719.N0962.d012187 k sizes d := by
  apply iSup_mono
  intro theta
  exact ENNReal.div_le_div_right (h theta) _

theorem d012319 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0970.d012314 k sizes d hd) ≤
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d :=
  _root_.GD.N0232.N0719.N0970.d012318 k sizes (_root_.GD.N0232.N0719.N0970.d012315 k sizes d hd)



theorem d012320 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hvalue : _root_.GD.N0232.N0719.N0962.d012187 k sizes d = _root_.GD.N0232.N0719.N0962.d012188 k sizes) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0970.d012314 k sizes d hd) =
      _root_.GD.N0232.N0719.N0962.d012188 k sizes := by
  apply le_antisymm
  · exact (_root_.GD.N0232.N0719.N0970.d012319 k sizes d hd).trans_eq hvalue
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
      (_root_.GD.N0232.N0719.N0970.d012316 k sizes d hd).1


theorem d012321 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (hstrict : _root_.GD.N0232.N0719.N0970.d012310 k sizes d) :
    _root_.GD.N0232.N0719.N0970.d012310 k sizes (_root_.GD.N0232.N0719.N0970.d012314 k sizes d hd) := by
  intro theta
  exact lt_of_le_of_lt (_root_.GD.N0232.N0719.N0970.d012315 k sizes d hd theta) (hstrict theta)

def d012322 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0970.d012314 k sizes (_root_.GD.N0232.N0719.N0969.d012211 k sizes hk hsizes)
    ⟨(_root_.GD.N0232.N0719.N0969.d012212 k sizes hk hsizes).1.1,
      (_root_.GD.N0232.N0719.N0969.d012212 k sizes hk hsizes).2⟩

theorem d012323 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0970.d012322 k sizes hk hsizes ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes :=
  _root_.GD.N0232.N0719.N0970.d012316 k sizes _ _

theorem d012324 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0970.d012322 k sizes hk hsizes) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0969.d012211 k sizes hk hsizes) :=
  _root_.GD.N0232.N0719.N0970.d012315 k sizes _ _ theta

theorem d012325 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0970.d012322 k sizes hk hsizes) =
      _root_.GD.N0232.N0719.N0962.d012188 k sizes :=
  _root_.GD.N0232.N0719.N0970.d012320 k sizes _ _ (_root_.GD.N0232.N0719.N0969.d012213 k sizes hk hsizes)

theorem d012326 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0970.d012309 k sizes (_root_.GD.N0232.N0719.N0970.d012322 k sizes hk hsizes) :=
  _root_.GD.N0232.N0719.N0970.d012317 k sizes _ _



theorem d012327 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ∃ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d =
        _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012190 k sizes) ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes d := by
  refine ⟨_root_.GD.N0232.N0719.N0970.d012322 k sizes hk hsizes,
    _root_.GD.N0232.N0719.N0970.d012323 k sizes hk hsizes, ?_,
    _root_.GD.N0232.N0719.N0970.d012326 k sizes hk hsizes⟩
  exact (_root_.GD.N0232.N0719.N0970.d012325 k sizes hk hsizes).trans
    (_root_.GD.N0232.N0719.N0962.d012198 k sizes hk hsizes)




theorem d012328 :
    (∃ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes d) ↔
    (∃ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes d ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes d) := by
  constructor
  · rintro ⟨d, hd, hvalue, hstrict⟩
    exact ⟨_root_.GD.N0232.N0719.N0970.d012314 k sizes d hd,
      _root_.GD.N0232.N0719.N0970.d012316 k sizes d hd,
      _root_.GD.N0232.N0719.N0970.d012320 k sizes d hd hvalue,
      _root_.GD.N0232.N0719.N0970.d012317 k sizes d hd,
      _root_.GD.N0232.N0719.N0970.d012321 k sizes d hd hstrict⟩
  · rintro ⟨d, hd, hvalue, _, hstrict⟩
    exact ⟨d, hd, hvalue, hstrict⟩



theorem d012329 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0970.d012310 k sizes (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes) := by
  intro theta
  have hmem : MemLp (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    simpa [_root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0859.d010810,
      _root_.GD.N0232.N0719.d009182] using
      _root_.GD.N0232.N0719.N0859.d010818 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010841 k sizes theta (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes) hmem,
    _root_.GD.N0232.N0719.N0859.d010842 k sizes hk hsizes theta]
  exact _root_.GD.N0232.N0719.N0859.d010825 k sizes hk hsizes theta



theorem d012330
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (htop : _root_.GD.N0232.N0719.N0962.d012188 k sizes = ⊤) :
    ∃ d ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes d := by
  let d := _root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes
  have hd := _root_.GD.N0232.N0719.N0968.d012201 k sizes hk hsizes
  refine ⟨d, hd, ?_, _root_.GD.N0232.N0719.N0970.d012329 k sizes hk hsizes⟩
  apply le_antisymm
  · rw [htop]
    exact le_top
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hd.1.1




theorem d012331
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (htop : _root_.GD.N0232.N0719.N0962.d012188 k sizes = ⊤) :
    ∃ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes d ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes d := by
  obtain ⟨d, hd, hvalue, hstrict⟩ :=
    _root_.GD.N0232.N0719.N0970.d012330 k sizes hk hsizes htop
  exact (_root_.GD.N0232.N0719.N0970.d012328 k sizes).mp
    ⟨d, ⟨hd.1.1, hd.2⟩, hvalue, hstrict⟩




theorem d012332
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hbaseline : _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0859.d010815 k sizes) =
      _root_.GD.N0232.N0719.N0962.d012188 k sizes) :
    ∃ d ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes d := by
  let d := _root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes
  have hd := _root_.GD.N0232.N0719.N0968.d012201 k sizes hk hsizes
  have hstrict := _root_.GD.N0232.N0719.N0970.d012329 k sizes hk hsizes
  refine ⟨d, hd, ?_, hstrict⟩
  apply le_antisymm
  · exact (_root_.GD.N0232.N0719.N0970.d012318 k sizes (fun theta => (hstrict theta).le)).trans_eq
      hbaseline
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hd.1.1



theorem d012333
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hbaseline : _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0859.d010815 k sizes) =
      _root_.GD.N0232.N0719.N0962.d012188 k sizes) :
    ∃ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes d ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes d := by
  obtain ⟨d, hd, hvalue, hstrict⟩ :=
    _root_.GD.N0232.N0719.N0970.d012332 k sizes hk hsizes hbaseline
  exact (_root_.GD.N0232.N0719.N0970.d012328 k sizes).mp
    ⟨d, ⟨hd.1.1, hd.2⟩, hvalue, hstrict⟩

end
end GD.N0232.N0719.N0970

#print axioms _root_.GD.N0232.N0719.N0970.d012317
#print axioms _root_.GD.N0232.N0719.N0970.d012320
#print axioms _root_.GD.N0232.N0719.N0970.d012327
#print axioms _root_.GD.N0232.N0719.N0970.d012328
#print axioms _root_.GD.N0232.N0719.N0970.d012330
#print axioms _root_.GD.N0232.N0719.N0970.d012331
#print axioms _root_.GD.N0232.N0719.N0970.d012332
#print axioms _root_.GD.N0232.N0719.N0970.d012333
