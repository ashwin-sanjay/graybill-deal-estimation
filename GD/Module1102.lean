import GD.Module1101
import GD.Module1099


















open Filter MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1191

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1166
open _root_.GD.N0232.N0720.N1167
open _root_.GD.N0232.N0720.N1169
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1183
open _root_.GD.N0232.N0720.N1184
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1186
open _root_.GD.N0232.N0720.N1188
open _root_.GD.N0232.N0720.N1189
open _root_.GD.N0232.N0720.N1190
open _root_.GD.N0232.N0720.N1192
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

abbrev d017665 :=
  _root_.GD.N0232.N0720.N1173.d015933

abbrev d017666 :=
  _root_.GD.N0232.N0720.N1173.d015936

private abbrev d017667 : Measure _root_.GD.N0232.N0720.N1191.d017665 :=
  _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104


def d017668
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (k : ℕ) : _root_.GD.N0232.N0720.N1191.d017665 → ℝ :=
  fun theta ↦ _root_.GD.N0232.N0720.N1166.d017432 k theta + R.reservoir k theta

theorem d017669
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (k : ℕ) (theta : _root_.GD.N0232.N0720.N1191.d017665) :
    0 ≤ R.reservoir k theta := by
  exact (D k).weight_nonnegative (R.legal k) theta

theorem d017670
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (k : ℕ) (theta : _root_.GD.N0232.N0720.N1191.d017665) :
    0 ≤ _root_.GD.N0232.N0720.N1191.d017668 R k theta := by
  exact add_nonneg (_root_.GD.N0232.N0720.N1166.d017437 k theta)
    (_root_.GD.N0232.N0720.N1191.d017669 R k theta)


theorem d017671
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D) (k : ℕ) :
    _root_.GD.N0232.N0720.N1166.d017433 k ≤
      _root_.GD.N0232.N0720.N1183.d017550 (_root_.GD.N0232.N0720.N1191.d017668 R k) := by
  rw [_root_.GD.N0232.N0720.N1166.d017440]
  unfold _root_.GD.N0232.N0720.N1183.d017550
  apply withDensity_mono
  filter_upwards with theta
  apply ENNReal.ofReal_le_ofReal
  rw [_root_.GD.N0232.N0720.N1166.d017435]
  exact le_add_of_nonneg_right
    (_root_.GD.N0232.N0720.N1191.d017669 R k theta)



theorem d017672
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668 R)) :
    _root_.GD.N0232.N0720.N1111.d016605
      (fun k ↦ _root_.GD.N0232.N0720.N1183.d017550 (_root_.GD.N0232.N0720.N1191.d017668 R k)) := by
  exact _root_.GD.N0232.N0720.N1169.d017506
    _root_.GD.N0232.N0720.N1166.d017433
    (fun k ↦ _root_.GD.N0232.N0720.N1183.d017550 (_root_.GD.N0232.N0720.N1191.d017668 R k))
    (fun _ ↦ by infer_instance)
    (fun k ↦ (F.legal k).finitePrior)
    _root_.GD.N0232.N0720.N1166.d017442
    (_root_.GD.N0232.N0720.N1191.d017671 R)



theorem d017673
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668 R)) (k : ℕ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1191.d017668 R k) x := by
  filter_upwards [(F.legal k).moments] with x hx
  have hevidenceNonneg :
      0 ≤ _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1191.d017668 R k) x := by
    unfold _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088 _root_.GD.N0232.N0720.N1173.d015939
    apply integral_nonneg
    intro theta
    exact mul_nonneg
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x)
      (_root_.GD.N0232.N0720.N1191.d017670 R k theta)
  exact lt_of_le_of_ne hevidenceNonneg hx.2.2.2.symm



theorem d017674
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668 R)) (k : ℕ) :
    Integrable
      (_root_.GD.N0232.N0720.N1185.d017513 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1191.d017668 R k))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  exact _root_.GD.N0232.N0720.N1192.d017640
    (_root_.GD.N0232.N0720.N1191.d017668 R k) (F.legal k)
      (F.t118RiskIntegrable k)



theorem d017675
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D) (k : ℕ) :
    Integrable
      (fun x ↦
        (_root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
              _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k) x +
            _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
              _root_.GD.N0232.N0720.N1190.d017536 (R.reservoir k) x) ^ 2 /
          _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
            (_root_.GD.N0232.N0720.N1166.d017432 k) x)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  have hreservoir := (D k).current_memLp (R.legal k)
  have hsum : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k) +
        _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1190.d017536 (R.reservoir k))
      2 (_root_.GD.N0232.N0720.N1186.d017597 k) := by
    exact (_root_.GD.N0232.N0720.N1188.d017610 k).add hreservoir
  simpa only [Pi.add_apply] using
    _root_.GD.N0232.N0720.N1192.d017641 k _ hsum


theorem d017676
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1191.d017666) :
    0 ≤ _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
      (R.reservoir k) x := by
  exact _root_.GD.N0232.N0720.N1169.d017500
    _root_.GD.N0232.N0720.N1493.d016104 (R.reservoir k) x
      (_root_.GD.N0232.N0720.N1191.d017669 R k)



theorem d017677
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668 R)) (k : ℕ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
        (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 (R.reservoir k) theta x)
        _root_.GD.N0232.N0720.N1191.d017667 := by
  filter_upwards [(F.legal k).moments, _root_.GD.N0232.N0720.N1167.d017493 k]
    with x hcombined hbase
  have hdiff := hcombined.1.sub hbase.1
  refine hdiff.congr ?_
  filter_upwards [] with theta
  simp only [Pi.sub_apply, _root_.GD.N0232.N0720.N1191.d017668, _root_.GD.N0232.N0720.N1173.d015939]
  ring


theorem d017678
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668 R)) (k : ℕ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1191.d017668 R k) x =
        _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
            (_root_.GD.N0232.N0720.N1166.d017432 k) x +
          _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
            (R.reservoir k) x := by
  filter_upwards [_root_.GD.N0232.N0720.N1167.d017493 k,
    _root_.GD.N0232.N0720.N1191.d017677 R F k]
      with x hbase hreservoir
  change _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
      (fun theta ↦ _root_.GD.N0232.N0720.N1166.d017432 k theta + R.reservoir k theta) x =
    _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1166.d017432 k) x +
      _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104 (R.reservoir k) x
  exact _root_.GD.N0232.N0720.N1169.d017498 _root_.GD.N0232.N0720.N1493.d016104
    (_root_.GD.N0232.N0720.N1166.d017432 k) (R.reservoir k) x hbase.1 hreservoir



theorem d017679
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D) (k : ℕ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1191.d017668 R k) x =
        _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
            _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k) x +
          _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
            _root_.GD.N0232.N0720.N1190.d017536 (R.reservoir k) x := by
  filter_upwards [_root_.GD.N0232.N0720.N1167.d017493 k] with x hbase
  have hbaseCurrent : Integrable
      (fun theta ↦ (_root_.GD.N0232.N0720.N1173.d015938 theta - _root_.GD.N0232.N0720.N1190.d017536 x) *
        _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) theta x) _root_.GD.N0232.N0720.N1191.d017667 := by
    have hdiff := hbase.2.1.sub (hbase.1.const_mul (_root_.GD.N0232.N0720.N1190.d017536 x))
    refine hdiff.congr ?_
    filter_upwards [] with theta
    simp only [Pi.sub_apply]
    ring
  change _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
      _root_.GD.N0232.N0720.N1190.d017536
        (fun theta ↦ _root_.GD.N0232.N0720.N1166.d017432 k theta + R.reservoir k theta) x =
    _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k) x +
      _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 (R.reservoir k) x
  exact _root_.GD.N0232.N0720.N1185.d017520 _root_.GD.N0232.N0720.N1493.d016104
    _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k) (R.reservoir k) x
    hbaseCurrent ((D k).current_integrable (R.legal k) x)



theorem d017680
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668 R)) (k : ℕ) :
    _root_.GD.N0232.N0720.N1185.d017514 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1191.d017668 R k) ≤
      _root_.GD.N0232.N0720.N1184.d017651 k (R.reservoir k) := by
  unfold _root_.GD.N0232.N0720.N1191.d017668 _root_.GD.N0232.N0720.N1184.d017651
  apply _root_.GD.N0232.N0720.N1185.d017523
    _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
      (_root_.GD.N0232.N0720.N1166.d017432 k) (R.reservoir k)
  · have h :=
      _root_.GD.N0232.N0720.N1191.d017674 R F k
    unfold _root_.GD.N0232.N0720.N1191.d017668 at h
    exact h
  · exact _root_.GD.N0232.N0720.N1191.d017675 R k
  · exact _root_.GD.N0232.N0720.N1186.d017600 k
  · exact Filter.Eventually.of_forall
      (_root_.GD.N0232.N0720.N1191.d017676 R k)
  · have h := _root_.GD.N0232.N0720.N1191.d017678 R F k
    unfold _root_.GD.N0232.N0720.N1191.d017668 at h
    exact h
  · have h := _root_.GD.N0232.N0720.N1191.d017679 R k
    unfold _root_.GD.N0232.N0720.N1191.d017668 at h
    exact h



def d017681
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668 R)) :
    _root_.GD.N0232.N0720.N1184.d017660 R where
  prior := fun k ↦ _root_.GD.N0232.N0720.N1183.d017550 (_root_.GD.N0232.N0720.N1191.d017668 R k)
  priorFinite := fun k ↦ (F.legal k).finitePrior
  retain := _root_.GD.N0232.N0720.N1191.d017672 R F
  bayes := _root_.GD.N0232.N0720.N1183.d017566 (_root_.GD.N0232.N0720.N1191.d017668 R) F.legal
  bayesSequence := F.d017570
  candidateIntegrable := F.t118RiskIntegrable
  combinedEvidence := by
    intro k
    have h := _root_.GD.N0232.N0720.N1191.d017673 R F k
    unfold _root_.GD.N0232.N0720.N1191.d017668 at h
    exact h
  upperRaw := by
    intro k
    have h := _root_.GD.N0232.N0720.N1191.d017680 R F k
    unfold _root_.GD.N0232.N0720.N1191.d017668 at h
    exact h
  deficitEqRaw := by
    intro k
    have h := _root_.GD.N0232.N0720.N1183.d017569.d017571
      (_root_.GD.N0232.N0720.N1191.d017668 R) F k
    unfold _root_.GD.N0232.N0720.N1191.d017668 at h
    exact h



theorem d017682
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668 R)) :
    ∃ s : _root_.GD.N0232.N0720.N1159.d014639 2 2,
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) s.value
        (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) ∧
      _root_.GD.N0232.N0720.N1482.d015169 (m := 2) (n := 2) s = 0 := by
  exact _root_.GD.N0232.N0720.N1184.d017662 R
    (_root_.GD.N0232.N0720.N1191.d017681 R F)


theorem d017683
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668 R)) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact _root_.GD.N0232.N0720.N1184.d017663 R
    (_root_.GD.N0232.N0720.N1191.d017681 R F)





def d017684
    (D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k)
    (happrox : _root_.GD.N0232.N0720.N1184.d017654 D) :
    _root_.GD.N0232.N0720.N1184.d017653 D :=
  Classical.choice
    ((_root_.GD.N0232.N0720.N1184.d017656 D).2
      happrox)



theorem d017685
    (D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k)
    (happrox : _root_.GD.N0232.N0720.N1184.d017654 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668
        (_root_.GD.N0232.N0720.N1191.d017684 D happrox))) :
    ∃ s : _root_.GD.N0232.N0720.N1159.d014639 2 2,
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) s.value
        (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) ∧
      _root_.GD.N0232.N0720.N1482.d015169 (m := 2) (n := 2) s = 0 := by
  exact _root_.GD.N0232.N0720.N1191.d017682
    (_root_.GD.N0232.N0720.N1191.d017684 D happrox) F



theorem d017686
    (D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k)
    (happrox : _root_.GD.N0232.N0720.N1184.d017654 D)
    (F : _root_.GD.N0232.N0720.N1183.d017569
      (_root_.GD.N0232.N0720.N1191.d017668
        (_root_.GD.N0232.N0720.N1191.d017684 D happrox))) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact _root_.GD.N0232.N0720.N1191.d017683
    (_root_.GD.N0232.N0720.N1191.d017684 D happrox) F

end

end N1191
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1191.d017680
#print axioms _root_.GD.N0232.N0720.N1191.d017681
#print axioms _root_.GD.N0232.N0720.N1191.d017682
#print axioms _root_.GD.N0232.N0720.N1191.d017683
#print axioms _root_.GD.N0232.N0720.N1191.d017685
#print axioms _root_.GD.N0232.N0720.N1191.d017686
