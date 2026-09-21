import GD.Module0980














set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0232.N0720.N1221

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0611

variable (m n : ℕ)



theorem d015561
    (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) ≠ ⊤ := by
  have hmem : MemLp (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
      _root_.GD.N0232.N0720.N1080.d014179 m n hm hn _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014198 m n theta (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) hmem]
  change _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) ≠ ⊤
  rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
  exact ENNReal.ofReal_ne_top



theorem d015562
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1080.d014176 m n hm hn ∈ _root_.GD.N0232.N0720.N1256.d015552 m n := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [_root_.GD.N0232.N0720.N1080.d014176] using
      _root_.GD.N0232.N0720.d014162 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn)
  · intro b a ha omega
    simpa [_root_.GD.N0232.N0720.N1080.d014176] using
      _root_.GD.N0232.N0720.d014164 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn)
        b (ne_of_gt ha) omega
  · exact _root_.GD.N0232.N0720.N1221.d015561 m n hm hn

theorem d015563
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0232.N0720.N1256.d015552 m n).Nonempty :=
  ⟨_root_.GD.N0232.N0720.N1080.d014176 m n hm hn, _root_.GD.N0232.N0720.N1221.d015562 m n hm hn⟩



theorem d015564
    (hm : 2 ≤ m) (hn : 2 ≤ n) (htop : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤) :
    ∃ e ∈ _root_.GD.N0232.N0720.N1256.d015552 m n,
      _root_.GD.N0232.N0720.N1256.d015548 m n e = _root_.GD.N0232.N0720.N1256.d015549 m n := by
  obtain ⟨e, he⟩ := _root_.GD.N0232.N0720.N1221.d015563 m n hm hn
  refine ⟨e, he, ?_⟩
  have hlower : _root_.GD.N0232.N0720.N1256.d015549 m n ≤ _root_.GD.N0232.N0720.N1256.d015548 m n e :=
    _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n) he.1.1
  apply le_antisymm _ hlower
  rw [htop]
  exact le_top

end
end GD.N0232.N0720.N1221

#print axioms _root_.GD.N0232.N0720.N1221.d015561
#print axioms _root_.GD.N0232.N0720.N1221.d015562
#print axioms _root_.GD.N0232.N0720.N1221.d015563
#print axioms _root_.GD.N0232.N0720.N1221.d015564
