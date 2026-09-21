import GD.Module0242
import GD.Module0979












set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1256

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1258
open _root_.GD.N0230.N0611
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)

def d015545 : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) := {d | Measurable d}


def d015546 : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :=
  {d | Measurable d ∧ ∀ (b a : ℝ), 0 < a → ∀ omega,
    d (_root_.GD.N0107.d009024 m n b a a omega) = b + a * d omega}

def d015547 (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0232.N0720.N1080.d014197 m n theta d / ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n theta)

def d015548 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0720.N1256.d015547 m n) d

def d015549 : ℝ≥0∞ := _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015545 m n)

def d015550 : ℝ≥0∞ := _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015546 m n)



def d015551 : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :=
  {d | Measurable d ∧ ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≠ ⊤}

def d015552 : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :=
  {d | d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n ∧ ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≠ ⊤}

theorem d015553 (hm : 1 ≤ m) (C : ℝ) (hC : 0 ≤ C)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0232.N0720.N1256.d015547 m n theta d ≤ ENNReal.ofReal C ↔
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1256.d015547
  rw [ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr
    (_root_.GD.N0232.N0720.N1257.d015510 m n hm theta))) ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul hC]



theorem d015554
    (hm : 2 ≤ m) (hn : 2 ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (hne : (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015545 m n)
      (ENNReal.ofReal C)).Nonempty) :
    (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015546 m n)
      (ENNReal.ofReal C)).Nonempty := by
  obtain ⟨d, hd, hb⟩ := hne
  have hraw : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) :=
    fun theta => (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) C hC theta d).mp (hb theta)
  obtain ⟨e, he, heq, heRisk⟩ :=
    _root_.GD.N0232.N0720.N1258.d015544 m n hm hn C hC d hd hraw
  refine ⟨e, ⟨he, ?_⟩, ?_⟩
  · intro b a ha omega
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨b, Real.log a⟩
    have hg : g.d009239 = a := Real.exp_log ha
    have h := heq g omega
    simpa only [_root_.GD.N0232.N0720.N1214.d014259,
      _root_.GD.N0232.N0719.N0946.d009229.d009244, hg, show g.shift = b from rfl] using h
  · intro theta
    exact (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) C hC theta e).mpr (heRisk theta)



theorem d015555
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n = _root_.GD.N0232.N0720.N1256.d015550 m n := by
  exact _root_.GD.N0230.N0611.d003525 (_root_.GD.N0232.N0720.N1256.d015547 m n)
    (_root_.GD.N0232.N0720.N1256.d015545 m n) (_root_.GD.N0232.N0720.N1256.d015546 m n) (fun _ hd => hd.1)
    (_root_.GD.N0232.N0720.N1256.d015554 m n hm hn)


theorem d015556
    (hm : 2 ≤ m) (hn : 2 ≤ n) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0720.N1256.d015550 m n ≤ _root_.GD.N0232.N0720.N1256.d015548 m n d := by
  rw [← _root_.GD.N0232.N0720.N1256.d015555 m n hm hn]
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n) hd



theorem d015557
    (hm : 2 ≤ m) (hn : 2 ≤ n) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hfinite : _root_.GD.N0232.N0720.N1256.d015548 m n d ≠ ⊤) :
    ∃ e ∈ _root_.GD.N0232.N0720.N1256.d015546 m n,
      _root_.GD.N0232.N0720.N1256.d015548 m n e ≤ _root_.GD.N0232.N0720.N1256.d015548 m n d := by
  let C := (_root_.GD.N0232.N0720.N1256.d015548 m n d).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hval : ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015548 m n d :=
    ENNReal.ofReal_toReal hfinite
  have hb : (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015545 m n)
      (ENNReal.ofReal C)).Nonempty := by
    refine ⟨d, hd, ?_⟩
    intro theta
    rw [hval]
    exact le_iSup (fun theta => _root_.GD.N0232.N0720.N1256.d015547 m n theta d) theta
  obtain ⟨e, he, heb⟩ := _root_.GD.N0232.N0720.N1256.d015554 m n hm hn C hC hb
  refine ⟨e, he, ?_⟩
  rw [← hval]
  exact iSup_le heb



theorem d015558
    (hm : 1 ≤ m) (C : ℝ) (hC : 0 ≤ C) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hb : ∀ theta, _root_.GD.N0232.N0720.N1256.d015547 m n theta d ≤ ENNReal.ofReal C) :
    ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≠ ⊤ := by
  intro theta
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((_root_.GD.N0232.N0720.N1256.d015553 m n hm C hC theta d).mp (hb theta))



theorem d015559 (hm : 2 ≤ m) :
    _root_.GD.N0232.N0720.N1256.d015549 m n =
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015551 m n) := by
  apply _root_.GD.N0230.N0611.d003525 (_root_.GD.N0232.N0720.N1256.d015547 m n)
    (_root_.GD.N0232.N0720.N1256.d015545 m n) (_root_.GD.N0232.N0720.N1256.d015551 m n) (fun _ hd => hd.1)
  intro C hC hne
  obtain ⟨d, hd, hb⟩ := hne
  exact ⟨d, ⟨hd, _root_.GD.N0232.N0720.N1256.d015558 m n (by omega) C hC d hb⟩, hb⟩



theorem d015560
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015551 m n) =
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015552 m n) := by
  apply _root_.GD.N0230.N0611.d003525 (_root_.GD.N0232.N0720.N1256.d015547 m n)
    (_root_.GD.N0232.N0720.N1256.d015551 m n) (_root_.GD.N0232.N0720.N1256.d015552 m n)
    (fun _ hd => ⟨hd.1.1, hd.2⟩)
  intro C hC hne
  obtain ⟨d, hd, hb⟩ := hne
  obtain ⟨e, he, heb⟩ := _root_.GD.N0232.N0720.N1256.d015554 m n hm hn C hC ⟨d, hd.1, hb⟩
  exact ⟨e, ⟨he, _root_.GD.N0232.N0720.N1256.d015558 m n (by omega) C hC e heb⟩, heb⟩

end
end GD.N0232.N0720.N1256

#print axioms _root_.GD.N0232.N0720.N1256.d015555
#print axioms _root_.GD.N0232.N0720.N1256.d015556
#print axioms _root_.GD.N0232.N0720.N1256.d015557
#print axioms _root_.GD.N0232.N0720.N1256.d015559
#print axioms _root_.GD.N0232.N0720.N1256.d015560
