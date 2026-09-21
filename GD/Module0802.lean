import GD.Module0242
import GD.Module0801












set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0719.N0962

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0964
open _root_.GD.N0230.N0611
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (k : ℕ) (sizes : Fin k → ℕ)

def d012184 : Set (_root_.GD.N0232.N0719.d009173 k sizes → ℝ) := {d | Measurable d}


def d012185 : Set (_root_.GD.N0232.N0719.d009173 k sizes → ℝ) :=
  {d | Measurable d ∧ ∀ (b a : ℝ), 0 < a → ∀ omega,
    d (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a omega) = b + a * d omega}

def d012186 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d / ENNReal.ofReal (_root_.GD.N0232.N0719.N0963.d012141 k sizes theta)

def d012187 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) d

def d012188 : ℝ≥0∞ := _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012184 k sizes)

def d012189 : ℝ≥0∞ := _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012185 k sizes)



def d012190 : Set (_root_.GD.N0232.N0719.d009173 k sizes → ℝ) :=
  {d | Measurable d ∧ ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≠ ⊤}

def d012191 : Set (_root_.GD.N0232.N0719.d009173 k sizes → ℝ) :=
  {d | d ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes ∧ ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≠ ⊤}

theorem d012192 (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i) (C : ℝ) (hC : 0 ≤ C)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0962.d012186 k sizes theta d ≤ ENNReal.ofReal C ↔
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta) := by
  unfold _root_.GD.N0232.N0719.N0962.d012186
  rw [ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr
    (_root_.GD.N0232.N0719.N0963.d012143 k sizes hk hsizes theta))) ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul hC]



theorem d012193
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C)
    (hne : (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012184 k sizes)
      (ENNReal.ofReal C)).Nonempty) :
    (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012185 k sizes)
      (ENNReal.ofReal C)).Nonempty := by
  obtain ⟨d, hd, hb⟩ := hne
  have hraw : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta) :=
    fun theta => (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega) (fun i => by have := hsizes i; omega) C hC theta d).mp (hb theta)
  obtain ⟨e, he, heq, heRisk⟩ :=
    _root_.GD.N0232.N0719.N0964.d012183 k sizes hk hsizes C hC d hd hraw
  refine ⟨e, ⟨he, ?_⟩, ?_⟩
  · intro b a ha omega
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨b, Real.log a⟩
    have hg : g.d009239 = a := Real.exp_log ha
    have h := heq g omega
    simpa only [_root_.GD.N0232.N0719.N0946.d009258,
      _root_.GD.N0232.N0719.N0946.d009229.d009244, hg, show g.shift = b from rfl] using h
  · intro theta
    exact (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega) (fun i => by have := hsizes i; omega) C hC theta e).mpr (heRisk theta)



theorem d012194
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes = _root_.GD.N0232.N0719.N0962.d012189 k sizes := by
  exact _root_.GD.N0230.N0611.d003525 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
    (_root_.GD.N0232.N0719.N0962.d012184 k sizes) (_root_.GD.N0232.N0719.N0962.d012185 k sizes) (fun _ hd => hd.1)
    (_root_.GD.N0232.N0719.N0962.d012193 k sizes hk hsizes)


theorem d012195
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0962.d012189 k sizes ≤ _root_.GD.N0232.N0719.N0962.d012187 k sizes d := by
  rw [← _root_.GD.N0232.N0719.N0962.d012194 k sizes hk hsizes]
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hd



theorem d012196
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d)
    (hfinite : _root_.GD.N0232.N0719.N0962.d012187 k sizes d ≠ ⊤) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e ≤ _root_.GD.N0232.N0719.N0962.d012187 k sizes d := by
  let C := (_root_.GD.N0232.N0719.N0962.d012187 k sizes d).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hval : ENNReal.ofReal C = _root_.GD.N0232.N0719.N0962.d012187 k sizes d :=
    ENNReal.ofReal_toReal hfinite
  have hb : (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012184 k sizes)
      (ENNReal.ofReal C)).Nonempty := by
    refine ⟨d, hd, ?_⟩
    intro theta
    rw [hval]
    exact le_iSup (fun theta => _root_.GD.N0232.N0719.N0962.d012186 k sizes theta d) theta
  obtain ⟨e, he, heb⟩ := _root_.GD.N0232.N0719.N0962.d012193 k sizes hk hsizes C hC hb
  refine ⟨e, he, ?_⟩
  rw [← hval]
  exact iSup_le heb



theorem d012197
    (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i) (C : ℝ) (hC : 0 ≤ C) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0962.d012186 k sizes theta d ≤ ENNReal.ofReal C) :
    ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≠ ⊤ := by
  intro theta
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((_root_.GD.N0232.N0719.N0962.d012192 k sizes hk hsizes C hC theta d).mp (hb theta))



theorem d012198 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes =
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012190 k sizes) := by
  apply _root_.GD.N0230.N0611.d003525 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
    (_root_.GD.N0232.N0719.N0962.d012184 k sizes) (_root_.GD.N0232.N0719.N0962.d012190 k sizes) (fun _ hd => hd.1)
  intro C hC hne
  obtain ⟨d, hd, hb⟩ := hne
  exact ⟨d, ⟨hd, _root_.GD.N0232.N0719.N0962.d012197 k sizes (by omega) (fun i => by have := hsizes i; omega) C hC d hb⟩, hb⟩



theorem d012199
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012190 k sizes) =
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012191 k sizes) := by
  apply _root_.GD.N0230.N0611.d003525 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
    (_root_.GD.N0232.N0719.N0962.d012190 k sizes) (_root_.GD.N0232.N0719.N0962.d012191 k sizes)
    (fun _ hd => ⟨hd.1.1, hd.2⟩)
  intro C hC hne
  obtain ⟨d, hd, hb⟩ := hne
  obtain ⟨e, he, heb⟩ := _root_.GD.N0232.N0719.N0962.d012193 k sizes hk hsizes C hC ⟨d, hd.1, hb⟩
  exact ⟨e, ⟨he, _root_.GD.N0232.N0719.N0962.d012197 k sizes (by omega) (fun i => by have := hsizes i; omega) C hC e heb⟩, heb⟩

end
end GD.N0232.N0719.N0962

#print axioms _root_.GD.N0232.N0719.N0962.d012194
#print axioms _root_.GD.N0232.N0719.N0962.d012195
#print axioms _root_.GD.N0232.N0719.N0962.d012196
#print axioms _root_.GD.N0232.N0719.N0962.d012198
#print axioms _root_.GD.N0232.N0719.N0962.d012199
