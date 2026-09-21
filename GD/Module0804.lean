import GD.Module0241
import GD.Module0803
















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0719.N0969

noncomputable section

open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0232.N0719.N0964 _root_.GD.N0232.N0719.N0968
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0586
open _root_.GD.N0230.N0602

variable (k : ℕ) (sizes : Fin k → ℕ)


theorem d012204 : Monotone (_root_.GD.N0232.N0719.N0963.d012146 k sizes) := by
  intro a b hab p hp theta
  exact (hp theta).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hab (_root_.GD.N0232.N0719.N0963.d012142 k sizes theta)))

theorem d012205 : Monotone (_root_.GD.N0232.N0719.N0963.d012152 k sizes) := by
  intro a b hab
  exact Set.image_mono (_root_.GD.N0232.N0719.N0969.d012204 k sizes hab)



theorem d012206 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C)
    (hV : _root_.GD.N0232.N0719.N0962.d012188 k sizes < ENNReal.ofReal C) :
    (_root_.GD.N0232.N0719.N0963.d012146 k sizes C).Nonempty := by
  change (⨅ d ∈ _root_.GD.N0232.N0719.N0962.d012184 k sizes, _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) d) <
    ENNReal.ofReal C at hV
  obtain ⟨d, hd⟩ := iInf_lt_iff.mp hV
  obtain ⟨hdBorel, hdRisk⟩ := iInf_lt_iff.mp hd
  have hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta) := by
    intro theta
    apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega) (fun i => by have := hsizes i; omega) C hC theta d).mp
    exact (le_iSup (fun theta => _root_.GD.N0232.N0719.N0962.d012186 k sizes theta d) theta).trans hdRisk.le
  obtain ⟨p, hp, _⟩ := _root_.GD.N0232.N0719.N0963.d012170 k sizes C d hdBorel hb
  exact ⟨p, hp⟩



theorem d012207 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hfinite : _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤) :
    (_root_.GD.N0232.N0719.N0963.d012146 k sizes (_root_.GD.N0232.N0719.N0962.d012188 k sizes).toReal).Nonempty := by
  let v := (_root_.GD.N0232.N0719.N0962.d012188 k sizes).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hV : ENNReal.ofReal v = _root_.GD.N0232.N0719.N0962.d012188 k sizes :=
    ENNReal.ofReal_toReal hfinite
  have hne : ∀ c : ℝ, v < c → (_root_.GD.N0232.N0719.N0963.d012152 k sizes c).Nonempty := by
    intro c hc
    have hcpos : 0 < c := lt_of_le_of_lt hv hc
    have hlt : _root_.GD.N0232.N0719.N0962.d012188 k sizes < ENNReal.ofReal c := by
      rw [← hV]
      exact (ENNReal.ofReal_lt_ofReal_iff hcpos).mpr hc
    exact (_root_.GD.N0232.N0719.N0969.d012206 k sizes hk hsizes c hcpos.le hlt).image _
  obtain ⟨x, hx⟩ := _root_.GD.N0230.N0586.d003514
    (_root_.GD.N0232.N0719.N0963.d012152 k sizes) (_root_.GD.N0232.N0719.N0969.d012205 k sizes) v
    (fun c hc => _root_.GD.N0232.N0719.N0963.d012153 k sizes (le_trans hv hc.le)) hne
  let p := (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))).symm x
  refine ⟨p, ?_⟩
  intro theta
  have hnorm : _root_.GD.N0232.N0719.N0962.d012186 k sizes theta (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) ≤
      ENNReal.ofReal v := by
    apply _root_.GD.N0230.N0586.d003515 hv
    intro c hc
    apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega) (fun i => by have := hsizes i; omega) c (le_trans hv hc.le)
      theta (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)).mpr
    rw [_root_.GD.N0232.N0719.N0896.d011093]
    exact ((_root_.GD.N0232.N0719.N0963.d012155 k sizes c x).mp (hx c hc)) theta
  have hraw := (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega) (fun i => by have := hsizes i; omega) v hv theta
    (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)).mp hnorm
  simpa only [_root_.GD.N0232.N0719.N0896.d011093] using hraw


theorem d012208 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hfinite : _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0232.N0719.N0962.d012188 k sizes := by
  let v := (_root_.GD.N0232.N0719.N0962.d012188 k sizes).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hV : ENNReal.ofReal v = _root_.GD.N0232.N0719.N0962.d012188 k sizes :=
    ENNReal.ofReal_toReal hfinite
  obtain ⟨p, hp⟩ := _root_.GD.N0232.N0719.N0969.d012207 k sizes hk hsizes hfinite
  have hraw : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) ≤
      ENNReal.ofReal (v * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta) := by
    intro theta
    rw [_root_.GD.N0232.N0719.N0896.d011093]
    exact hp theta
  have hcap : (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012184 k sizes)
      (ENNReal.ofReal v)).Nonempty := by
    refine ⟨_root_.GD.N0232.N0719.N0896.d011088 k sizes p, _root_.GD.N0232.N0719.N0896.d011089 k sizes p, ?_⟩
    intro theta
    exact (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega) (fun i => by have := hsizes i; omega) v hv theta _).mpr (hraw theta)
  obtain ⟨e, he, heb⟩ := _root_.GD.N0232.N0719.N0962.d012193 k sizes hk hsizes v hv hcap
  refine ⟨e, ⟨he, _root_.GD.N0232.N0719.N0962.d012197 k sizes (by omega) (fun i => by have := hsizes i; omega) v hv e heb⟩, ?_⟩
  apply le_antisymm
  · rw [← hV]
    exact iSup_le heb
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) he.1


theorem d012209 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0232.N0719.N0962.d012188 k sizes := by
  by_cases htop : _root_.GD.N0232.N0719.N0962.d012188 k sizes = ⊤
  · exact _root_.GD.N0232.N0719.N0968.d012203 k sizes hk hsizes htop
  · exact _root_.GD.N0232.N0719.N0969.d012208 k sizes hk hsizes htop



theorem d012210 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e =
        _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012190 k sizes) ∧
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e =
        _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0962.d012191 k sizes) := by
  obtain ⟨e, he, hval⟩ := _root_.GD.N0232.N0719.N0969.d012209 k sizes hk hsizes
  have hD := _root_.GD.N0232.N0719.N0962.d012198 k sizes hk hsizes
  have hE := _root_.GD.N0232.N0719.N0962.d012199 k sizes hk hsizes
  exact ⟨e, he, ⟨he.1.1, he.2⟩, hval.trans hD, (hval.trans hD).trans hE⟩


def d012211 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  Classical.choose (_root_.GD.N0232.N0719.N0969.d012209 k sizes hk hsizes)

theorem d012212 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0969.d012211 k sizes hk hsizes ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes :=
  (Classical.choose_spec (_root_.GD.N0232.N0719.N0969.d012209 k sizes hk hsizes)).1

theorem d012213 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0969.d012211 k sizes hk hsizes) = _root_.GD.N0232.N0719.N0962.d012188 k sizes :=
  (Classical.choose_spec (_root_.GD.N0232.N0719.N0969.d012209 k sizes hk hsizes)).2



theorem d012214 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0969.d012211 k sizes hk hsizes) ≤ _root_.GD.N0232.N0719.N0962.d012187 k sizes d := by
  rw [_root_.GD.N0232.N0719.N0969.d012213 k sizes hk hsizes]
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hd

end
end GD.N0232.N0719.N0969

#print axioms _root_.GD.N0232.N0719.N0969.d012207
#print axioms _root_.GD.N0232.N0719.N0969.d012208
#print axioms _root_.GD.N0232.N0719.N0969.d012209
#print axioms _root_.GD.N0232.N0719.N0969.d012210
#print axioms _root_.GD.N0232.N0719.N0969.d012212
#print axioms _root_.GD.N0232.N0719.N0969.d012213
#print axioms _root_.GD.N0232.N0719.N0969.d012214

