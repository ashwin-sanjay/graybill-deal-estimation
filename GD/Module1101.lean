import GD.Module0031
import GD.Module1097
import GD.Module1098
import GD.Module1100


























open Filter MeasureTheory Set
open scoped RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1184

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1112
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1166
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1186
open _root_.GD.N0232.N0720.N1188
open _root_.GD.N0232.N0720.N1189
open _root_.GD.N0232.N0720.N1190
open _root_.GD.N0232.N0720.N1193
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0230.N0563
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0606
open _root_.GD.N0230.N0608

abbrev d017648 :=
  _root_.GD.N0232.N0720.N1173.d015933

abbrev d017649 := _root_.GD.N0232.N0720.N1184.d017648 → ℝ


abbrev d017650 (k : ℕ) :=
  _root_.GD.N0232.N0720.N1189.d017617 _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
    (_root_.GD.N0232.N0720.N1166.d017432 k)


abbrev d017651 (k : ℕ) (reservoir : _root_.GD.N0232.N0720.N1184.d017649) : ℝ :=
  _root_.GD.N0232.N0720.N1185.d017521 _root_.GD.N0232.N0720.N1493.d016104
    _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k) reservoir


theorem d017652 (k : ℕ) (reservoir : _root_.GD.N0232.N0720.N1184.d017649) :
    0 ≤ _root_.GD.N0232.N0720.N1184.d017651 k reservoir := by
  dsimp only [_root_.GD.N0232.N0720.N1184.d017651]
  unfold _root_.GD.N0232.N0720.N1185.d017521
  apply integral_nonneg_of_ae
  filter_upwards [_root_.GD.N0232.N0720.N1186.d017600 k] with x hx
  exact div_nonneg (sq_nonneg _) hx.le



structure d017653
    (D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k) where
  reservoir : ℕ → _root_.GD.N0232.N0720.N1184.d017649
  legal : ∀ k, (D k).Legal (reservoir k)
  residualZero : Tendsto
    (fun k ↦ _root_.GD.N0232.N0720.N1184.d017651 k (reservoir k)) atTop (nhds 0)



def d017654
    (D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k) : Prop :=
  _root_.GD.N0230.N0563.d000360
    (fun k w ↦ (D k).Legal w) _root_.GD.N0232.N0720.N1184.d017651


def d017655
    (D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k) : Prop :=
  _root_.GD.N0230.N0563.d000363
    (fun k w ↦ (D k).Legal w) _root_.GD.N0232.N0720.N1184.d017651




theorem d017656
    (D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k) :
    Nonempty (_root_.GD.N0232.N0720.N1184.d017653 D) ↔
      _root_.GD.N0232.N0720.N1184.d017654 D := by
  have hgeneric :=
    _root_.GD.N0230.N0563.d000362
      (fun k w ↦ (D k).Legal w) _root_.GD.N0232.N0720.N1184.d017651
      (fun k ↦ ⟨0, (D k).legal_zero⟩)
      _root_.GD.N0232.N0720.N1184.d017652
  constructor
  · rintro ⟨R⟩
    apply hgeneric.mp
    exact ⟨R.reservoir, R.legal, R.residualZero⟩
  · intro happrox
    obtain ⟨reservoir, hlegal, hzero⟩ := hgeneric.mpr happrox
    exact ⟨⟨reservoir, hlegal, hzero⟩⟩



theorem d017657
    (D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k) :
    (¬ Nonempty (_root_.GD.N0232.N0720.N1184.d017653 D)) ↔
      _root_.GD.N0232.N0720.N1184.d017655 D := by
  have hgeneric :=
    _root_.GD.N0230.N0563.d000364
      (fun k w ↦ (D k).Legal w) _root_.GD.N0232.N0720.N1184.d017651
      (fun k ↦ ⟨0, (D k).legal_zero⟩)
      _root_.GD.N0232.N0720.N1184.d017652
  constructor
  · intro hnone
    apply hgeneric.mp
    rintro ⟨reservoir, hlegal, hzero⟩
    exact hnone ⟨⟨reservoir, hlegal, hzero⟩⟩
  · intro hfloor
    have hnone := hgeneric.mpr hfloor
    rintro ⟨R⟩
    exact hnone ⟨R.reservoir, R.legal, R.residualZero⟩




theorem d017658
    (D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k) :
    Nonempty (_root_.GD.N0232.N0720.N1184.d017653 D) ∨
      _root_.GD.N0232.N0720.N1184.d017655 D := by
  by_cases hdiagonal : Nonempty (_root_.GD.N0232.N0720.N1184.d017653 D)
  · exact Or.inl hdiagonal
  · exact Or.inr
      ((_root_.GD.N0232.N0720.N1184.d017657 D).mp
        hdiagonal)



theorem d017659
    (D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k)
    (htarget : ∀ k,
      _root_.GD.N0232.N0720.N1186.d017593 _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
          (_root_.GD.N0232.N0720.N1166.d017432 k) (_root_.GD.N0232.N0720.N1188.d017610 k) ∈
        _root_.GD.N0232.N0720.N1189.d017629 (D k)) :
    _root_.GD.N0232.N0720.N1184.d017654 D := by
  intro ε hε
  apply Filter.Eventually.of_forall
  intro k
  obtain ⟨reservoir, hlegal, hresidual⟩ :=
    (_root_.GD.N0232.N0720.N1189.d017636
      (D k)
      (_root_.GD.N0232.N0720.N1186.d017599 k)
      (_root_.GD.N0232.N0720.N1186.d017600 k)
      (_root_.GD.N0232.N0720.N1188.d017610 k)).mp (htarget k) ε hε
  exact ⟨reservoir, hlegal, hresidual⟩




structure d017660
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D) where
  prior : ℕ → Measure _root_.GD.N0232.N0720.N1184.d017648
  priorFinite : ∀ k, IsFiniteMeasure (prior k)
  retain : _root_.GD.N0232.N0720.N1111.d016605 prior
  bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2)
  bayesSequence : _root_.GD.N0232.N0720.N1111.d016612
    2 2 _root_.GD.N0232.N0720.N1173.d015935 prior bayes
  candidateIntegrable : ∀ k, Integrable
    (fun theta ↦
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1185.d017526).toReal)
    (prior k)
  combinedEvidence : ∀ k, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
    0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
      (fun theta ↦ _root_.GD.N0232.N0720.N1166.d017432 k theta +
        R.reservoir k theta) x
  upperRaw : ∀ k,
    _root_.GD.N0232.N0720.N1185.d017514 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536
        (fun theta ↦ _root_.GD.N0232.N0720.N1166.d017432 k theta +
          R.reservoir k theta) ≤
      _root_.GD.N0232.N0720.N1184.d017651 k (R.reservoir k)
  deficitEqRaw : ∀ k,
    _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k _root_.GD.N0232.N0720.N1185.d017526 -
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k (bayes k) =
      _root_.GD.N0232.N0720.N1185.d017514
        _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
          (fun theta ↦ _root_.GD.N0232.N0720.N1166.d017432 k theta +
            R.reservoir k theta)



theorem d017661
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (E : _root_.GD.N0232.N0720.N1184.d017660 R) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := 2) (n := 2)
      _root_.GD.N0232.N0720.N1185.d017530 = 0 := by
  exact _root_.GD.N0232.N0720.N1193.d017646
    E.prior E.priorFinite E.retain E.bayes E.bayesSequence
      E.candidateIntegrable _root_.GD.N0232.N0720.N1166.d017432 R.reservoir
      E.combinedEvidence E.upperRaw R.residualZero E.deficitEqRaw



theorem d017662
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (E : _root_.GD.N0232.N0720.N1184.d017660 R) :
    ∃ s : _root_.GD.N0232.N0720.N1159.d014639 2 2,
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) s.value
        (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) ∧
      _root_.GD.N0232.N0720.N1482.d015169 (m := 2) (n := 2) s = 0 := by
  refine ⟨_root_.GD.N0232.N0720.N1185.d017530, ?_, ?_⟩
  · simpa only [_root_.GD.N0232.N0720.N1185.d017531] using
      _root_.GD.N0232.N0720.N1185.d017532
  · exact _root_.GD.N0232.N0720.N1184.d017661 R E




theorem d017663
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (E : _root_.GD.N0232.N0720.N1184.d017660 R) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact
    (_root_.GD.N0232.N0720.N1482.d015173
      (m := 2) (n := 2) (by norm_num) (by norm_num)).2
      (_root_.GD.N0232.N0720.N1184.d017662 R E)




theorem d017664
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (hnot : ¬ _root_.GD.N0232.N0720.N1159.d014661 2 2) :
    ¬ Nonempty (_root_.GD.N0232.N0720.N1184.d017660 R) := by
  rintro ⟨E⟩
  exact hnot (_root_.GD.N0232.N0720.N1184.d017663 R E)

#print axioms _root_.GD.N0232.N0720.N1184.d017656
#print axioms _root_.GD.N0232.N0720.N1184.d017657
#print axioms _root_.GD.N0232.N0720.N1184.d017658
#print axioms _root_.GD.N0232.N0720.N1184.d017661
#print axioms _root_.GD.N0232.N0720.N1184.d017662
#print axioms _root_.GD.N0232.N0720.N1184.d017663
#print axioms _root_.GD.N0232.N0720.N1184.d017664

end

end N1184
end N0720
end N0232
end GD
