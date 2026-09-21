import GD.Module0932
import GD.Module0982
















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0232.N0720.N1226

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1221
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0611

variable (m n : ℕ)


def d015576 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  Measurable d ∧
    (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d <
        _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
    _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n



def d015577 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  _root_.GD.N0232.N0720.N1226.d015576 m n d ∧
    (∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta d) →
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)

def d015578 : Prop :=
  ∃ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, _root_.GD.N0232.N0720.N1226.d015577 m n d



theorem d015576.d015579
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1226.d015576 m n d) :
    d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n :=
  ⟨hd.1, fun theta => ne_top_of_lt (hd.2.1 theta)⟩



theorem d015580
    {d s : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hbelow : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta s) :
    _root_.GD.N0232.N0720.N1256.d015548 m n d ≤ _root_.GD.N0232.N0720.N1256.d015548 m n s := by
  apply iSup_mono
  intro theta
  exact ENNReal.div_le_div_right (hbelow theta) _




theorem d015581
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p)
    (e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (he : Measurable e)
    (hbelow : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p)) :
    ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1214.d014265 m n p := by
  have heMemLp : MemLp e 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    apply _root_.GD.N0232.N0720.N1215.d014285 m n e he
    apply ne_top_of_le_ne_top _ (hbelow _root_.GD.N0232.N0720.N1080.d014169)
    rw [_root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1080.d014190]
    exact ENNReal.ofReal_ne_top
  have heq : MemLp.toLp e heMemLp = p := by
    apply hp
    intro theta
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n theta e heMemLp,
      ← _root_.GD.N0232.N0720.N1215.d014286 m n theta p]
    exact hbelow theta
  have href : e =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1214.d014265 m n p := by
    apply (MemLp.toLp_eq_toLp_iff heMemLp (_root_.GD.N0232.N0720.N1214.d014268 m n p)).mp
    exact heq.trans (_root_.GD.N0232.N0720.N1214.d014269 m n p).symm
  intro theta
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le href




theorem d015582
    (s : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hs : _root_.GD.N0232.N0720.N1226.d015576 m n s) :
    ∃ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      _root_.GD.N0232.N0720.N1226.d015577 m n d ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta s := by
  have hsMemLp : MemLp s 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n s hs.1
      (ne_top_of_lt (hs.2.1 _root_.GD.N0232.N0720.N1080.d014169))
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n (MemLp.toLp s hsMemLp)
  let d := _root_.GD.N0232.N0720.N1214.d014265 m n p
  have hd : Measurable d := _root_.GD.N0232.N0720.N1214.d014266 m n p
  have hbelow : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta s := by
    intro theta
    rw [_root_.GD.N0232.N0720.N1080.d014198 m n theta s hsMemLp]
    change _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) ≤ _
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    exact (_root_.GD.N0232.N0720.N1159.d014634 m n (MemLp.toLp s hsMemLp)).1 theta
  have hminimax : _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n := by
    apply le_antisymm
    · exact (_root_.GD.N0232.N0720.N1226.d015580 m n hbelow).trans_eq hs.2.2
    · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n) hd
  refine ⟨d, ⟨⟨hd, ?_, hminimax⟩, ?_⟩, hbelow⟩
  · intro theta
    exact (hbelow theta).trans_lt (hs.2.1 theta)
  · exact _root_.GD.N0232.N0720.N1226.d015581 m n p
      (_root_.GD.N0232.N0720.N1159.d014634 m n (MemLp.toLp s hsMemLp)).2.1


theorem d015583
    (s : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hs : _root_.GD.N0232.N0720.N1226.d015576 m n s) :
    _root_.GD.N0232.N0720.N1226.d015578 m n := by
  obtain ⟨d, hd, _⟩ := _root_.GD.N0232.N0720.N1226.d015582 m n s hs
  exact ⟨d, hd⟩



theorem d015584 :
    _root_.GD.N0232.N0720.N1226.d015578 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, _root_.GD.N0232.N0720.N1226.d015576 m n s := by
  constructor
  · rintro ⟨d, hd, _⟩
    exact ⟨d, hd⟩
  · rintro ⟨s, hs⟩
    exact _root_.GD.N0232.N0720.N1226.d015583 m n s hs



theorem d015585
    (hm : 2 ≤ m) (hn : 2 ≤ n) (htop : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤) :
    _root_.GD.N0232.N0720.N1226.d015576 m n (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) := by
  have hd := _root_.GD.N0232.N0720.N1221.d015562 m n hm hn
  refine ⟨hd.1.1, ?_, ?_⟩
  · intro theta
    have hmem : MemLp (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
      simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
        _root_.GD.N0232.N0720.N1080.d014179 m n hm hn _root_.GD.N0232.N0720.N1080.d014169
    rw [_root_.GD.N0232.N0720.N1080.d014198 m n theta (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) hmem,
      _root_.GD.N0232.N0720.N1080.d014199 m n hm hn theta]
    exact _root_.GD.N0232.N0720.N1080.d014186 m n hm hn theta
  · apply le_antisymm
    · rw [htop]
      exact le_top
    · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n) hd.1.1




theorem d015586
    (hm : 2 ≤ m) (hn : 2 ≤ n) (htop : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤) :
    _root_.GD.N0232.N0720.N1226.d015578 m n :=
  _root_.GD.N0232.N0720.N1226.d015583 m n (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn)
    (_root_.GD.N0232.N0720.N1226.d015585 m n hm hn htop)

end
end GD.N0232.N0720.N1226

#print axioms _root_.GD.N0232.N0720.N1226.d015576.d015579
#print axioms _root_.GD.N0232.N0720.N1226.d015580
#print axioms _root_.GD.N0232.N0720.N1226.d015581
#print axioms _root_.GD.N0232.N0720.N1226.d015582
#print axioms _root_.GD.N0232.N0720.N1226.d015583
#print axioms _root_.GD.N0232.N0720.N1226.d015584
#print axioms _root_.GD.N0232.N0720.N1226.d015585
#print axioms _root_.GD.N0232.N0720.N1226.d015586
