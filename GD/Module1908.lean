import GD.Module1907
import GD.Module0458
import GD.Module1906
import GD.Module1859

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0058
noncomputable section
open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1226
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0059 _root_.GD.N0056
open _root_.GD.N0014 _root_.GD.N0012
open _root_.GD.N0022.N0255
open _root_.GD.N0046.N0305


theorem d030916 : _root_.GD.N0012.d030893 := by
  intro g hg hb
  have h := _root_.GD.N0056.d030915 _root_.GD.N0059.d007100
    (fun _ hc => _root_.GD.N0059.d007122 hc) (fun _ hc => _root_.GD.N0059.d007123 hc)
    _root_.GD.N0059.d007125 g hg hb
  rw [_root_.GD.N0059.d007126] at h
  exact h

theorem d030917 : _root_.GD.N0012.d030892 :=
  _root_.GD.N0012.d030896 _root_.GD.N0058.d030916


theorem d030918
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤
      ENNReal.ofReal (_root_.GD.N0012.d030890 * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) : False :=
  _root_.GD.N0012.d030900 _root_.GD.N0058.d030917 d hd hcap hbase

theorem d030919
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d)
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 + ENNReal.ofReal (1/1000:ℝ) < _root_.GD.N0232.N0720.N1256.d015548 3 3 d :=
  _root_.GD.N0012.d030903 _root_.GD.N0058.d030917 d hd hbase

theorem d030920 :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 + ENNReal.ofReal (1/1000:ℝ) < _root_.GD.N0022.N0255.d030394 3 3 := by
  have h : _root_.GD.N0232.N0720.N1256.d015549 3 3 + ENNReal.ofReal (1/1000:ℝ) < ENNReal.ofReal _root_.GD.N0012.d030890 := by
    rw [_root_.GD.N0012.d030890, ENNReal.ofReal_add (by norm_num) (by norm_num)]
    exact ENNReal.add_lt_add_right (by simp)
      _root_.GD.N0010.d030858
  exact h.trans_le (_root_.GD.N0012.d030904 _root_.GD.N0058.d030917)

theorem d030921 :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 < _root_.GD.N0022.N0255.d030394 3 3 := by
  have hcap : _root_.GD.N0232.N0720.N1256.d015549 3 3 < ENNReal.ofReal _root_.GD.N0012.d030890 :=
    _root_.GD.N0010.d030858.trans_le
      (ENNReal.ofReal_le_ofReal (by norm_num [_root_.GD.N0012.d030890]))
  exact hcap.trans_le (_root_.GD.N0012.d030904 _root_.GD.N0058.d030917)

theorem d030922 :
    _root_.GD.N0046.N0305.d030202 3 3 (by omega) (by omega) = ∅ :=
  (_root_.GD.N0022.N0255.d030398 3 3 (by omega) (by omega)).mpr
    _root_.GD.N0058.d030921

theorem d030923 :
    ¬ _root_.GD.N0232.N0720.N1226.d015578 3 3 := by
  intro h
  obtain ⟨p,hp,_⟩ := (_root_.GD.N0046.N0305.d030214
    3 3 (by omega) (by omega)).mp h
  rw [_root_.GD.N0058.d030922] at hp
  exact hp


theorem d030924
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1226.d015578 m n ↔ _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤ := by
  rw [_root_.GD.N0063.d030488 m n hm hn]
  exact or_iff_left (by rintro ⟨_,_,h⟩; exact _root_.GD.N0058.d030923 h)

theorem d030925
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1226.d015578 m n ↔ (m=2 ∧ n ≤ 4) ∨ (n=2 ∧ m ≤ 4) := by
  rw [_root_.GD.N0058.d030924 m n hm hn,
    _root_.GD.N0067.d023924 m n hm hn]

theorem d030926
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hfinite : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    ¬ _root_.GD.N0232.N0720.N1226.d015578 m n :=
  fun h => hfinite ((_root_.GD.N0058.d030924 m n hm hn).mp h)

private theorem d030927 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hp : (m-1)*(n-1)=4) : (m=2 ∧ n=5) ∨ (m=3 ∧ n=3) ∨ (m=5 ∧ n=2) := by
  have hml : m-1 ≤ (m-1)*(n-1) := by
    calc
      m-1=(m-1)*1 := by omega
      _ ≤ (m-1)*(n-1) := Nat.mul_le_mul_left _ (by omega)
  have hnl : n-1 ≤ (m-1)*(n-1) := by
    calc
      n-1=1*(n-1) := by omega
      _ ≤ (m-1)*(n-1) := Nat.mul_le_mul_right _ (by omega)
  have hm5 : m ≤ 5 := by omega
  have hn5 : n ≤ 5 := by omega
  interval_cases m <;> omega



theorem d030928
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ ↔ _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ := by
  constructor
  · intro hempty htop
    have hex := (_root_.GD.N0058.d030924 m n hm hn).mpr htop
    obtain ⟨p,hp,_⟩ := (_root_.GD.N0046.N0305.d030214 m n hm hn).mp hex
    rw [hempty] at hp
    exact hp
  · intro hfinite
    have hlow := (_root_.GD.N0067.d023923 m n hm hn).mp hfinite
    by_cases hstrict : 4 < (m-1)*(n-1)
    · exact _root_.GD.N0037.d030436
        m n hm hn hstrict
    · have heq : (m-1)*(n-1)=4 := by omega
      rcases _root_.GD.N0058.d030927 m n hm hn heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact _root_.GD.N0029.d030442
      · exact _root_.GD.N0058.d030922
      · exact _root_.GD.N0029.d030445

theorem d030929
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n < _root_.GD.N0022.N0255.d030394 m n ↔ _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ :=
  (_root_.GD.N0022.N0255.d030398 m n hm hn).symm.trans
    (_root_.GD.N0058.d030928 m n hm hn)

end
end GD.N0058

#print axioms _root_.GD.N0058.d030916
#print axioms _root_.GD.N0058.d030917
#print axioms _root_.GD.N0058.d030918
#print axioms _root_.GD.N0058.d030919
#print axioms _root_.GD.N0058.d030920
#print axioms _root_.GD.N0058.d030921
#print axioms _root_.GD.N0058.d030922
#print axioms _root_.GD.N0058.d030923
#print axioms _root_.GD.N0058.d030924
#print axioms _root_.GD.N0058.d030925
#print axioms _root_.GD.N0058.d030926

#print axioms _root_.GD.N0058.d030928
#print axioms _root_.GD.N0058.d030929
