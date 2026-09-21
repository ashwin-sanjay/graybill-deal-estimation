import GD.Module0241
import GD.Module0981
















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1222

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1258 _root_.GD.N0232.N0720.N1221
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0586
open _root_.GD.N0230.N0602

variable (m n : ℕ)


theorem d015565 : Monotone (_root_.GD.N0232.N0720.N1257.d015513 m n) := by
  intro a b hab p hp theta
  exact (hp theta).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hab (_root_.GD.N0232.N0720.N1257.d015509 m n theta)))

theorem d015566 : Monotone (_root_.GD.N0232.N0720.N1257.d015519 m n) := by
  intro a b hab
  exact Set.image_mono (_root_.GD.N0232.N0720.N1222.d015565 m n hab)



theorem d015567 (hm : 2 ≤ m) (C : ℝ) (hC : 0 ≤ C)
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n < ENNReal.ofReal C) :
    (_root_.GD.N0232.N0720.N1257.d015513 m n C).Nonempty := by
  change (⨅ d ∈ _root_.GD.N0232.N0720.N1256.d015545 m n, _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0720.N1256.d015547 m n) d) <
    ENNReal.ofReal C at hV
  obtain ⟨d, hd⟩ := iInf_lt_iff.mp hV
  obtain ⟨hdBorel, hdRisk⟩ := iInf_lt_iff.mp hd
  have hb : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
    intro theta
    apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) C hC theta d).mp
    exact (le_iSup (fun theta => _root_.GD.N0232.N0720.N1256.d015547 m n theta d) theta).trans hdRisk.le
  obtain ⟨p, hp, _⟩ := _root_.GD.N0232.N0720.N1257.d015531 m n C d hdBorel hb
  exact ⟨p, hp⟩



theorem d015568 (hm : 2 ≤ m)
    (hfinite : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    (_root_.GD.N0232.N0720.N1257.d015513 m n (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal).Nonempty := by
  let v := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hV : ENNReal.ofReal v = _root_.GD.N0232.N0720.N1256.d015549 m n :=
    ENNReal.ofReal_toReal hfinite
  have hne : ∀ c : ℝ, v < c → (_root_.GD.N0232.N0720.N1257.d015519 m n c).Nonempty := by
    intro c hc
    have hcpos : 0 < c := lt_of_le_of_lt hv hc
    have hlt : _root_.GD.N0232.N0720.N1256.d015549 m n < ENNReal.ofReal c := by
      rw [← hV]
      exact (ENNReal.ofReal_lt_ofReal_iff hcpos).mpr hc
    exact (_root_.GD.N0232.N0720.N1222.d015567 m n hm c hcpos.le hlt).image _
  obtain ⟨x, hx⟩ := _root_.GD.N0230.N0586.d003514
    (_root_.GD.N0232.N0720.N1257.d015519 m n) (_root_.GD.N0232.N0720.N1222.d015566 m n) v
    (fun c hc => _root_.GD.N0232.N0720.N1257.d015520 m n (le_trans hv hc.le)) hne
  let p := (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))).symm x
  refine ⟨p, ?_⟩
  intro theta
  have hnorm : _root_.GD.N0232.N0720.N1256.d015547 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) ≤
      ENNReal.ofReal v := by
    apply _root_.GD.N0230.N0586.d003515 hv
    intro c hc
    apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) c (le_trans hv hc.le)
      theta (_root_.GD.N0232.N0720.N1214.d014265 m n p)).mpr
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    exact ((_root_.GD.N0232.N0720.N1257.d015522 m n c x).mp (hx c hc)) theta
  have hraw := (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) v hv theta
    (_root_.GD.N0232.N0720.N1214.d014265 m n p)).mp hnorm
  simpa only [_root_.GD.N0232.N0720.N1215.d014286] using hraw


theorem d015569 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hfinite : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    ∃ e ∈ _root_.GD.N0232.N0720.N1256.d015552 m n,
      _root_.GD.N0232.N0720.N1256.d015548 m n e = _root_.GD.N0232.N0720.N1256.d015549 m n := by
  let v := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hV : ENNReal.ofReal v = _root_.GD.N0232.N0720.N1256.d015549 m n :=
    ENNReal.ofReal_toReal hfinite
  obtain ⟨p, hp⟩ := _root_.GD.N0232.N0720.N1222.d015568 m n hm hfinite
  have hraw : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) ≤
      ENNReal.ofReal (v * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
    intro theta
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    exact hp theta
  have hcap : (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015545 m n)
      (ENNReal.ofReal v)).Nonempty := by
    refine ⟨_root_.GD.N0232.N0720.N1214.d014265 m n p, _root_.GD.N0232.N0720.N1214.d014266 m n p, ?_⟩
    intro theta
    exact (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) v hv theta _).mpr (hraw theta)
  obtain ⟨e, he, heb⟩ := _root_.GD.N0232.N0720.N1256.d015554 m n hm hn v hv hcap
  refine ⟨e, ⟨he, _root_.GD.N0232.N0720.N1256.d015558 m n (by omega) v hv e heb⟩, ?_⟩
  apply le_antisymm
  · rw [← hV]
    exact iSup_le heb
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n) he.1


theorem d015570 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ e ∈ _root_.GD.N0232.N0720.N1256.d015552 m n,
      _root_.GD.N0232.N0720.N1256.d015548 m n e = _root_.GD.N0232.N0720.N1256.d015549 m n := by
  by_cases htop : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤
  · exact _root_.GD.N0232.N0720.N1221.d015564 m n hm hn htop
  · exact _root_.GD.N0232.N0720.N1222.d015569 m n hm hn htop



theorem d015571 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ e ∈ _root_.GD.N0232.N0720.N1256.d015552 m n,
      e ∈ _root_.GD.N0232.N0720.N1256.d015551 m n ∧
      _root_.GD.N0232.N0720.N1256.d015548 m n e =
        _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015551 m n) ∧
      _root_.GD.N0232.N0720.N1256.d015548 m n e =
        _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015552 m n) := by
  obtain ⟨e, he, hval⟩ := _root_.GD.N0232.N0720.N1222.d015570 m n hm hn
  have hD := _root_.GD.N0232.N0720.N1256.d015559 m n hm
  have hE := _root_.GD.N0232.N0720.N1256.d015560 m n hm hn
  exact ⟨e, he, ⟨he.1.1, he.2⟩, hval.trans hD, (hval.trans hD).trans hE⟩


def d015572 (hm : 2 ≤ m) (hn : 2 ≤ n) : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  Classical.choose (_root_.GD.N0232.N0720.N1222.d015570 m n hm hn)

theorem d015573 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1222.d015572 m n hm hn ∈ _root_.GD.N0232.N0720.N1256.d015552 m n :=
  (Classical.choose_spec (_root_.GD.N0232.N0720.N1222.d015570 m n hm hn)).1

theorem d015574 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0232.N0720.N1222.d015572 m n hm hn) = _root_.GD.N0232.N0720.N1256.d015549 m n :=
  (Classical.choose_spec (_root_.GD.N0232.N0720.N1222.d015570 m n hm hn)).2



theorem d015575 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0232.N0720.N1222.d015572 m n hm hn) ≤ _root_.GD.N0232.N0720.N1256.d015548 m n d := by
  rw [_root_.GD.N0232.N0720.N1222.d015574 m n hm hn]
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n) hd

end
end GD.N0232.N0720.N1222

#print axioms _root_.GD.N0232.N0720.N1222.d015568
#print axioms _root_.GD.N0232.N0720.N1222.d015569
#print axioms _root_.GD.N0232.N0720.N1222.d015570
#print axioms _root_.GD.N0232.N0720.N1222.d015571
#print axioms _root_.GD.N0232.N0720.N1222.d015573
#print axioms _root_.GD.N0232.N0720.N1222.d015574
#print axioms _root_.GD.N0232.N0720.N1222.d015575
