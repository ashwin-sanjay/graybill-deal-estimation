import GD.Module1242
import GD.Module1275
import GD.Module1259
import GD.Module0963












namespace GD.N0232.N0720.N1319

open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1303 _root_.GD.N0232.N0720.N1325
open _root_.GD.N0232.N0720.N1317 _root_.GD.N0232.N0720.N1482
open _root_.GD.N0230.N0608

set_option maxHeartbeats 2400000

theorem d020618 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n := by
  rintro ⟨d, hd⟩
  obtain ⟨g, μ, hg, hb, hrep, hpost⟩ := _root_.GD.N0232.N0720.N1303.d020149 m n hm hn hd
  let k := m + n - 1
  have hdim : m + n = k + 1 := by dsimp [k]; omega
  obtain ⟨m1⟩ := _root_.GD.N0232.N0720.N1325.d020617 m n k hdim hm hn hd hg hb hrep μ hpost
  let prior : MeasureTheory.Measure _root_.GD.N0232.N0720.N1290.d004131 := μ
  have hpostPointwise : ∀ᵐ x ∂ _root_.GD.N0232.N0720.N1441.d013679 m n,
      g x = _root_.GD.N0232.N0720.N1290.d004140
        (_root_.GD.N0232.N0720.N1436.d013210 m n)
        (_root_.GD.N0232.N0720.N1336.d013420 m n x)
        prior := by
    filter_upwards [hpost] with x hx
    exact hx
  apply _root_.GD.N0232.N0720.N1317.d020334 hm hn hd hg hb
    (fun θ ↦ (hrep θ).symm) prior
  · exact hpostPointwise
  · exact m1

theorem d020619
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) seed.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    0 < _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) seed :=
  (_root_.GD.N0232.N0720.N1482.d015175 hm hn).1
    (_root_.GD.N0232.N0720.N1319.d020618 m n hm hn) seed hstrict

theorem d020620
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ ∃ seed : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) seed.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) seed = 0 := by
  rintro ⟨seed, hstrict, hzero⟩
  exact (_root_.GD.N0232.N0720.N1319.d020619 m n hm hn seed hstrict).ne' hzero

end GD.N0232.N0720.N1319

#print axioms _root_.GD.N0232.N0720.N1319.d020618
#print axioms _root_.GD.N0232.N0720.N1319.d020619
#print axioms _root_.GD.N0232.N0720.N1319.d020620
