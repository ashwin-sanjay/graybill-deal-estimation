import GD.Module0972
import GD.Module1096
import GD.Module1102


















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1416

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1085
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1183
open _root_.GD.N0232.N0720.N1166
open _root_.GD.N0232.N0720.N1168
open _root_.GD.N0232.N0720.N1184
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1187
open _root_.GD.N0232.N0720.N1189
open _root_.GD.N0232.N0720.N1190
open _root_.GD.N0232.N0720.N1191
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

abbrev d017755 :=
  _root_.GD.N0232.N0720.N1173.d015933





noncomputable abbrev d017756 :
    _root_.GD.N0232.N0720.d014158 2 2 (by norm_num) (by norm_num) :=
  _root_.GD.N0232.N0720.N1080.d014174 2 2 (by norm_num) (by norm_num)



theorem d017757 :
    _root_.GD.N0232.N0720.N1185.d017526 =
      _root_.GD.N0232.N0720.N1082.d015387 2 2 (by norm_num) (by norm_num)
        _root_.GD.N0232.N0720.N1416.d017756 1 := by
  apply Lp.ext
  filter_upwards
    [(show MemLp (_root_.GD.N0232.N0720.N1080.d014176 2 2 (by norm_num) (by norm_num)) 2
          (_root_.GD.N0232.N0720.N1080.d014172 2 2) from by
        simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
          _root_.GD.N0232.N0720.N1080.d014179 2 2 (by norm_num) (by norm_num)
            _root_.GD.N0232.N0720.N1080.d014169).coeFn_toLp,
     (show MemLp
          (_root_.GD.N0232.N0720.N1082.d015380 2 2 (by norm_num) (by norm_num)
            _root_.GD.N0232.N0720.N1416.d017756 1) 2 (_root_.GD.N0232.N0720.N1080.d014172 2 2) from by
        simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
          _root_.GD.N0232.N0720.N1082.d015386 2 2 (by norm_num) (by norm_num)
            _root_.GD.N0232.N0720.N1080.d014169 _root_.GD.N0232.N0720.N1416.d017756 1).coeFn_toLp]
      with x ht118 hamp
  rw [show _root_.GD.N0232.N0720.N1185.d017526 x = _root_.GD.N0232.N0720.N1080.d014176 2 2 (by norm_num) (by norm_num) x
      by simpa [_root_.GD.N0232.N0720.N1185.d017526, _root_.GD.N0232.N0720.N1080.d014181] using ht118,
    show _root_.GD.N0232.N0720.N1082.d015387 2 2 (by norm_num) (by norm_num)
        _root_.GD.N0232.N0720.N1416.d017756 1 x =
          _root_.GD.N0232.N0720.N1082.d015380 2 2 (by norm_num) (by norm_num)
            _root_.GD.N0232.N0720.N1416.d017756 1 x by
      simpa [_root_.GD.N0232.N0720.N1082.d015387] using hamp]
  simp [_root_.GD.N0232.N0720.N1416.d017756, _root_.GD.N0232.N0720.N1080.d014176, _root_.GD.N0232.N0720.N1082.d015380]


noncomputable abbrev d017758 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  _root_.GD.N0232.N0720.N1082.d015387 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1416.d017756 (5 / 4)


theorem d017759
    (U : _root_.GD.N0232.N0720.d014158 2 2 (by norm_num) (by norm_num))
    (a : ℝ) :
    _root_.GD.N0232.N0720.N1159.d014637 2 2
      (_root_.GD.N0232.N0720.N1082.d015387 2 2 (by norm_num) (by norm_num) U a) := by
  intro theta
  rw [_root_.GD.N0232.N0720.N1082.d015389]
  exact ENNReal.ofReal_ne_top


theorem d017760 :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 2 2) _root_.GD.N0232.N0720.N1416.d017758 _root_.GD.N0232.N0720.N1185.d017526 := by
  intro theta
  rw [_root_.GD.N0232.N0720.N1416.d017757]
  exact (_root_.GD.N0232.N0720.N1085.d015417
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756 theta).le



theorem d017761 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1416.d017758 _root_.GD.N0232.N0720.N1185.d017526 := by
  intro theta
  rw [_root_.GD.N0232.N0720.N1416.d017757]
  exact _root_.GD.N0232.N0720.N1085.d015417
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756 theta





theorem d017762
    {Theta : Type*} [MeasurableSpace Theta]
    {nu pi : Measure Theta} (hmeasure : nu ≤ pi)
    (rq rd : Theta → ℝ)
    (hq : Integrable rq pi) (hd : Integrable rd pi)
    (hgap : ∀ᵐ theta ∂pi, 0 ≤ rq theta - rd theta) :
    ∫ theta, rq theta - rd theta ∂nu ≤
      ∫ theta, rq theta - rd theta ∂pi := by
  exact integral_mono_measure hmeasure hgap (hq.sub hd)






theorem d017763
    {Theta : Type*} [MeasurableSpace Theta]
    {nu pi : Measure Theta} (hmeasure : nu ≤ pi)
    (rq rd ra : Theta → ℝ)
    (hq : Integrable rq pi) (hd : Integrable rd pi)
    (_ha : Integrable ra pi)
    (hgap : ∀ᵐ theta ∂pi, 0 ≤ rq theta - rd theta)
    (hbayes : (∫ theta, ra theta ∂pi) ≤ ∫ theta, rd theta ∂pi) :
    (∫ theta, rq theta - rd theta ∂nu) ≤
      (∫ theta, rq theta ∂pi) - ∫ theta, ra theta ∂pi := by
  have hmono := _root_.GD.N0232.N0720.N1416.d017762 hmeasure rq rd hq hd hgap
  rw [integral_sub hq hd] at hmono
  linarith




theorem d017764
    {Theta : Type*} [MeasurableSpace Theta]
    (c : NNReal) {nu pi : Measure Theta}
    (hmeasure : c • nu ≤ pi)
    (rq rd ra : Theta → ℝ)
    (hq : Integrable rq pi) (hd : Integrable rd pi)
    (_ha : Integrable ra pi)
    (hgap : ∀ᵐ theta ∂pi, 0 ≤ rq theta - rd theta)
    (hbayes : (∫ theta, ra theta ∂pi) ≤ ∫ theta, rd theta ∂pi) :
    (c : ℝ) * (∫ theta, rq theta - rd theta ∂nu) ≤
      (∫ theta, rq theta ∂pi) - ∫ theta, ra theta ∂pi := by
  have hmono := integral_mono_measure hmeasure hgap (hq.sub hd)
  rw [integral_smul_nnreal_measure, integral_sub hq hd] at hmono
  have htail :
      (∫ theta, rq theta ∂pi) - ∫ theta, rd theta ∂pi ≤
        (∫ theta, rq theta ∂pi) - ∫ theta, ra theta ∂pi :=
    sub_le_sub_left hbayes _
  norm_num [NNReal.smul_def] at hmono
  exact hmono.trans htail


theorem d017765
    {Theta : Type*} [MeasurableSpace Theta]
    {nu pi : Measure Theta} (hmeasure : nu ≤ pi)
    (rq rd ra : Theta → ℝ) (eta : ℝ)
    (hq : Integrable rq pi) (hd : Integrable rd pi)
    (_ha : Integrable ra pi)
    (hgap : ∀ᵐ theta ∂pi, 0 ≤ rq theta - rd theta)
    (hbayes : (∫ theta, ra theta ∂pi) ≤
      (∫ theta, rd theta ∂pi) + eta) :
    (∫ theta, rq theta - rd theta ∂nu) - eta ≤
      (∫ theta, rq theta ∂pi) - ∫ theta, ra theta ∂pi := by
  have hmono := _root_.GD.N0232.N0720.N1416.d017762 hmeasure rq rd hq hd hgap
  rw [integral_sub hq hd] at hmono
  linarith





def d017766 : _root_.GD.N0232.N0720.N1416.d017755 :=
  (0, (⟨1, by norm_num⟩, ⟨1 / 2, by norm_num⟩))




theorem d017767 :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ N : ℕ, ∀ k, N ≤ k →
        epsilon ≤
          _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935
              _root_.GD.N0232.N0720.N1166.d017433 k _root_.GD.N0232.N0720.N1185.d017526 -
            _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935
              _root_.GD.N0232.N0720.N1166.d017433 k (_root_.GD.N0232.N0720.N1166.d017479 k) := by
  have hchart : Continuous _root_.GD.N0232.N0720.N1173.d015935 :=
    _root_.GD.N0232.N0720.N1486.d015877 2 2 (by norm_num) (by norm_num)
  have ht118Integrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1185.d017526).toReal)
      (_root_.GD.N0232.N0720.N1166.d017433 k) := by
    intro k
    rw [← _root_.GD.N0232.N0720.N1168.d017574 k]
    exact _root_.GD.N0232.N0720.N1168.d017581.t118RiskIntegrable k
  obtain ⟨epsilon, hepsilon, N, hgap⟩ :=
    _root_.GD.N0232.N0720.N1111.d016609
      2 2 _root_.GD.N0232.N0720.N1173.d015935 hchart _root_.GD.N0232.N0720.N1166.d017433
      (fun _k ↦ by infer_instance)
      _root_.GD.N0232.N0720.N1166.d017442
      _root_.GD.N0232.N0720.N1185.d017528
      _root_.GD.N0232.N0720.N1416.d017760
      ht118Integrable
      (_root_.GD.N0232.N0720.N1416.d017761
        (_root_.GD.N0232.N0720.N1173.d015935 _root_.GD.N0232.N0720.N1416.d017766))
  refine ⟨epsilon, hepsilon, N, ?_⟩
  intro k hk
  have hfixed := hgap k hk
  have hbayes := _root_.GD.N0232.N0720.N1168.d017583
    k _root_.GD.N0232.N0720.N1416.d017758
      (_root_.GD.N0232.N0720.N1416.d017759
        _root_.GD.N0232.N0720.N1416.d017756 (5 / 4))
  linarith



theorem d017768 (k : ℕ) :
    _root_.GD.N0232.N0720.N1185.d017514 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k) =
      _root_.GD.N0232.N0720.N1184.d017651 k 0 := by
  unfold _root_.GD.N0232.N0720.N1185.d017514
    _root_.GD.N0232.N0720.N1185.d017513 _root_.GD.N0232.N0720.N1184.d017651
    _root_.GD.N0232.N0720.N1185.d017521
  apply integral_congr_ae
  filter_upwards with x
  rw [_root_.GD.N0232.N0720.N1189.d017615]
  ring



theorem d017769 :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ N : ℕ, ∀ k, N ≤ k → epsilon ≤ _root_.GD.N0232.N0720.N1184.d017651 k 0 := by
  obtain ⟨epsilon, hepsilon, N, hfloor⟩ :=
    _root_.GD.N0232.N0720.N1416.d017767
  refine ⟨epsilon, hepsilon, N, ?_⟩
  intro k hk
  have h := hfloor k hk
  rw [_root_.GD.N0232.N0720.N1187.d017603,
    _root_.GD.N0232.N0720.N1416.d017768] at h
  exact h










theorem d017770
    {D : ∀ k : ℕ, _root_.GD.N0232.N0720.N1184.d017650 k}
    (R : _root_.GD.N0232.N0720.N1184.d017653 D) :
    ¬ _root_.GD.N0232.N0720.N1183.d017569 (_root_.GD.N0232.N0720.N1191.d017668 R) := by
  intro F
  let prior : ℕ → Measure _root_.GD.N0232.N0720.N1416.d017755 :=
    fun k ↦ _root_.GD.N0232.N0720.N1183.d017550 (_root_.GD.N0232.N0720.N1191.d017668 R k)
  have hchart : Continuous _root_.GD.N0232.N0720.N1173.d015935 := by
    exact _root_.GD.N0232.N0720.N1486.d015877 2 2 (by norm_num) (by norm_num)
  have hdescFinite : _root_.GD.N0232.N0720.N1159.d014637 2 2 _root_.GD.N0232.N0720.N1416.d017758 :=
    _root_.GD.N0232.N0720.N1416.d017759 _root_.GD.N0232.N0720.N1416.d017756 (5 / 4)
  have hdescIntegrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta)
          _root_.GD.N0232.N0720.N1416.d017758).toReal) (prior k) := by
    intro k
    exact _root_.GD.N0232.N0720.N1111.d016608
      2 2 _root_.GD.N0232.N0720.N1173.d015935 hchart (prior k)
      _root_.GD.N0232.N0720.N1185.d017528
      _root_.GD.N0232.N0720.N1416.d017760
      (F.t118RiskIntegrable k)
  obtain ⟨epsilon, hepsilon, N, hfixedGap⟩ :=
    _root_.GD.N0232.N0720.N1111.d016609
      2 2 _root_.GD.N0232.N0720.N1173.d015935 hchart prior
      (fun k ↦ (F.legal k).finitePrior)
      (_root_.GD.N0232.N0720.N1191.d017672 R F)
      _root_.GD.N0232.N0720.N1185.d017528
      _root_.GD.N0232.N0720.N1416.d017760
      F.t118RiskIntegrable
      (_root_.GD.N0232.N0720.N1416.d017761
        (_root_.GD.N0232.N0720.N1173.d015935 _root_.GD.N0232.N0720.N1416.d017766))
  have hresidualLower : ∀ k, N ≤ k →
      epsilon ≤ _root_.GD.N0232.N0720.N1184.d017651 k (R.reservoir k) := by
    intro k hk
    have hgap := hfixedGap k hk
    have hbayes := F.d017570.minimizes
      k _root_.GD.N0232.N0720.N1416.d017758 hdescFinite (hdescIntegrable k)
    have hdeficit : epsilon ≤
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k _root_.GD.N0232.N0720.N1185.d017526 -
          _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k
            (_root_.GD.N0232.N0720.N1183.d017566
              (_root_.GD.N0232.N0720.N1191.d017668 R) F.legal k) := by
      dsimp only [prior] at hgap hbayes ⊢
      linarith
    have hexact := _root_.GD.N0232.N0720.N1183.d017569.d017571
      (_root_.GD.N0232.N0720.N1191.d017668 R) F k
    have hupper := _root_.GD.N0232.N0720.N1191.d017680 R F k
    dsimp only [prior] at hdeficit
    rw [hexact] at hdeficit
    exact hdeficit.trans hupper
  have heventualLower : ∀ᶠ k in atTop,
      epsilon ≤ _root_.GD.N0232.N0720.N1184.d017651 k (R.reservoir k) :=
    (eventually_atTop.2 ⟨N, hresidualLower⟩)
  have heventualSmall : ∀ᶠ k in atTop,
      _root_.GD.N0232.N0720.N1184.d017651 k (R.reservoir k) < epsilon :=
    (tendsto_order.1 R.residualZero).2 epsilon hepsilon
  have hfalse : ∀ᶠ _k : ℕ in atTop, False := by
    filter_upwards [heventualLower, heventualSmall] with k hlower hsmall
    exact (not_lt_of_ge hlower) hsmall
  have hbot : (atTop : Filter ℕ) = ⊥ :=
    Filter.eventually_false_iff_eq_bot.mp hfalse
  exact (show (atTop : Filter ℕ) ≠ ⊥ from Filter.NeBot.ne inferInstance) hbot

#print axioms _root_.GD.N0232.N0720.N1416.d017757
#print axioms _root_.GD.N0232.N0720.N1416.d017761
#print axioms _root_.GD.N0232.N0720.N1416.d017762
#print axioms _root_.GD.N0232.N0720.N1416.d017763
#print axioms _root_.GD.N0232.N0720.N1416.d017764
#print axioms _root_.GD.N0232.N0720.N1416.d017765
#print axioms _root_.GD.N0232.N0720.N1416.d017767
#print axioms _root_.GD.N0232.N0720.N1416.d017768
#print axioms _root_.GD.N0232.N0720.N1416.d017769
#print axioms _root_.GD.N0232.N0720.N1416.d017770

end

end N1416
end N0720
end N0232
end GD
