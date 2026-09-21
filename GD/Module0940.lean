import GD.Module0915
import GD.Module0877
import GD.Module0901





















open MeasureTheory ProbabilityTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1425

noncomputable section

open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1437
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1435
open _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1084
open _root_.GD.N0232.N0720.N1207



def d014719
    (m n : ℕ) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0232.N0720.N1437.d002998 (fun r s ↦ g (r, s))
    (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
    (_root_.GD.N0232.N0720.N1084.d014252 m n omega)
    (_root_.GD.N0232.N0720.N1084.d014253 m n omega)


theorem d014720
    (m n : ℕ) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.N1425.d014719 m n g omega =
      _root_.GD.N0107.d009084 omega.2 + _root_.GD.N0107.d009090 m n omega *
        g
          (_root_.GD.N0107.d009091 m n
              (_root_.GD.N0107.d009085 omega.1)
              (_root_.GD.N0107.d009085 omega.2),
            _root_.GD.N0107.d009093 m n omega) := by
  unfold _root_.GD.N0232.N0720.N1425.d014719 _root_.GD.N0232.N0720.N1437.d002998
  rw [← _root_.GD.N0232.N0720.N1084.d014255
      m n omega,
    ← _root_.GD.N0232.N0720.N1084.d014256
      m n omega]
  rfl



theorem d014721
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.N1425.d014719 m n g omega - mu =
      _root_.GD.N0141.d006685
        (_root_.GD.N0107.d012732 m n mu
          (_root_.GD.N0107.d009046 m n sigma tau))
        (_root_.GD.N0107.d009038 m n mu sigma tau
          (_root_.GD.N0107.d009046 m n sigma tau)
          (_root_.GD.N0107.d009045 m n sigma tau))
        (fun z ↦
          g
            (_root_.GD.N0107.d009039 m n mu sigma tau
                (_root_.GD.N0107.d009046 m n sigma tau) z,
              _root_.GD.N0107.d009040 m n mu sigma tau
                (_root_.GD.N0107.d009046 m n sigma tau) z))
        (_root_.GD.N0107.d009046 m n sigma tau) omega := by
  rw [_root_.GD.N0232.N0720.N1425.d014720]
  unfold _root_.GD.N0141.d006685
  dsimp only
  rw [_root_.GD.N0107.d012724
      m n hm hn mu sigma tau hsigma htau omega,
    _root_.GD.N0107.d012729
      m n hm hn mu sigma tau hsigma htau omega,
    _root_.GD.N0107.d012731
      m n hm hn mu sigma tau hsigma htau omega]
  unfold _root_.GD.N0107.d012732
  ring





theorem d014722
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hlift : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - mu)
      2 (_root_.GD.N0107.d009030 m n mu sigma tau)) :
    MemLp
      (fun omega ↦
        _root_.GD.N0107.d009038 m n mu sigma tau
            (_root_.GD.N0107.d009046 m n sigma tau)
            (_root_.GD.N0107.d009045 m n sigma tau) omega *
          (g
              (_root_.GD.N0107.d009039 m n mu sigma tau
                  (_root_.GD.N0107.d009046 m n sigma tau) omega,
                _root_.GD.N0107.d009040 m n mu sigma tau
                  (_root_.GD.N0107.d009046 m n sigma tau) omega) -
            _root_.GD.N0107.d009046 m n sigma tau))
      2 (_root_.GD.N0107.d009030 m n mu sigma tau) := by
  have horacle : MemLp
      (_root_.GD.N0107.d012732 m n mu
        (_root_.GD.N0107.d009046 m n sigma tau))
      2 (_root_.GD.N0107.d009030 m n mu sigma tau) :=
    _root_.GD.N0107.d012747
      m n hm hn mu sigma tau hsigma htau
  have hdiff := hlift.sub horacle
  apply (memLp_congr_ae ?_).2 hdiff
  filter_upwards [] with omega
  change
    _root_.GD.N0107.d009038 m n mu sigma tau
          (_root_.GD.N0107.d009046 m n sigma tau)
          (_root_.GD.N0107.d009045 m n sigma tau) omega *
        (g
            (_root_.GD.N0107.d009039 m n mu sigma tau
                (_root_.GD.N0107.d009046 m n sigma tau) omega,
              _root_.GD.N0107.d009040 m n mu sigma tau
                (_root_.GD.N0107.d009046 m n sigma tau) omega) -
          _root_.GD.N0107.d009046 m n sigma tau) =
      (_root_.GD.N0232.N0720.N1425.d014719 m n g omega - mu) -
        _root_.GD.N0107.d012732 m n mu
          (_root_.GD.N0107.d009046 m n sigma tau) omega
  rw [_root_.GD.N0232.N0720.N1425.d014721
    m n hm hn mu sigma tau hsigma htau g omega]
  unfold _root_.GD.N0141.d006685
  ring




theorem d014723
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (phi : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hphi : Measurable phi) :
    _root_.GD.N0120.d008809
        (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t phi =
      ∫ x, phi x ∂_root_.GD.N0232.N0720.N1436.d013289 m n t := by
  rw [_root_.GD.N0125.d008860
      (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn)]
  rw [← _root_.GD.N0125.d008873
      (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn)]
  simp_rw [← _root_.GD.N0232.N0720.N1434.d013553]
  rw [← integral_map (_root_.GD.N0232.N0720.N1435.d013471 t).aemeasurable
      hphi.aestronglyMeasurable,
    _root_.GD.N0232.N0720.N1434.d013563
      hm hn ht0 ht1]



theorem d014724
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hcarrier : MemLp
      (fun omega ↦
        _root_.GD.N0107.d009038 m n mu sigma tau
            (_root_.GD.N0107.d009046 m n sigma tau)
            (_root_.GD.N0107.d009045 m n sigma tau) omega *
          (g
              (_root_.GD.N0107.d009039 m n mu sigma tau
                  (_root_.GD.N0107.d009046 m n sigma tau) omega,
                _root_.GD.N0107.d009040 m n mu sigma tau
                  (_root_.GD.N0107.d009046 m n sigma tau) omega) -
            _root_.GD.N0107.d009046 m n sigma tau))
      2 (_root_.GD.N0107.d009030 m n mu sigma tau)) :
    (∫ omega,
        _root_.GD.N0107.d012732 m n mu
            (_root_.GD.N0107.d009046 m n sigma tau) omega *
          (_root_.GD.N0107.d009038 m n mu sigma tau
              (_root_.GD.N0107.d009046 m n sigma tau)
              (_root_.GD.N0107.d009045 m n sigma tau) omega *
            (g
                (_root_.GD.N0107.d009039 m n mu sigma tau
                    (_root_.GD.N0107.d009046 m n sigma tau) omega,
                  _root_.GD.N0107.d009040 m n mu sigma tau
                    (_root_.GD.N0107.d009046 m n sigma tau) omega) -
              _root_.GD.N0107.d009046 m n sigma tau))
      ∂_root_.GD.N0107.d009030 m n mu sigma tau) = 0 := by
  let t := _root_.GD.N0107.d009046 m n sigma tau
  let Sigma := _root_.GD.N0107.d009045 m n sigma tau
  have hU := _root_.GD.N0107.d012747
    m n hm hn mu sigma tau hsigma htau
  have hindepDLF := _root_.GD.N0107.d012745
    m n hm hn mu sigma tau hsigma htau
  have hindepCarrier : IndepFun
      (_root_.GD.N0107.d012732 m n mu t)
      (fun omega ↦
        _root_.GD.N0107.d009038 m n mu sigma tau t Sigma omega *
          (g
              (_root_.GD.N0107.d009039 m n mu sigma tau t omega,
                _root_.GD.N0107.d009040 m n mu sigma tau t omega) - t))
      (_root_.GD.N0107.d009030 m n mu sigma tau) := by
    have h := hindepDLF.comp measurable_id
      (show Measurable
        (fun p : ℝ × (ℝ × ℝ) ↦ p.1 * (g p.2 - t)) by
          fun_prop)
    simpa [t, Sigma, Function.comp_def] using h
  have hcentered := _root_.GD.N0107.d012746
    m n hm hn mu sigma tau hsigma htau
  exact _root_.GD.N0141.d006692
    hindepCarrier hU.aestronglyMeasurable hcarrier.aestronglyMeasurable
      hcentered



theorem d014725
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hcarrier : MemLp
      (fun omega ↦
        _root_.GD.N0107.d009038 m n mu sigma tau
            (_root_.GD.N0107.d009046 m n sigma tau)
            (_root_.GD.N0107.d009045 m n sigma tau) omega *
          (g
              (_root_.GD.N0107.d009039 m n mu sigma tau
                  (_root_.GD.N0107.d009046 m n sigma tau) omega,
                _root_.GD.N0107.d009040 m n mu sigma tau
                  (_root_.GD.N0107.d009046 m n sigma tau) omega) -
            _root_.GD.N0107.d009046 m n sigma tau))
      2 (_root_.GD.N0107.d009030 m n mu sigma tau)) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - mu) =
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (_root_.GD.N0107.d012732 m n mu
            (_root_.GD.N0107.d009046 m n sigma tau)) +
        _root_.GD.N0107.d009045 m n sigma tau *
          ∫ x,
            (g x - _root_.GD.N0107.d009046 m n sigma tau) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n
              (_root_.GD.N0107.d009046 m n sigma tau) := by
  let t := _root_.GD.N0107.d009046 m n sigma tau
  let Sigma := _root_.GD.N0107.d009045 m n sigma tau
  let D := _root_.GD.N0107.d009038 m n mu sigma tau t Sigma
  let L : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n → ℝ := fun omega ↦
    g
      (_root_.GD.N0107.d009039 m n mu sigma tau t omega,
        _root_.GD.N0107.d009040 m n mu sigma tau t omega)
  let U := _root_.GD.N0107.d012732 m n mu t
  have ht0 : 0 < t := _root_.GD.N0107.d009050
    (by omega) (by omega) hsigma htau
  have ht1 : t < 1 := _root_.GD.N0107.d009051
    (by omega) (by omega) hsigma htau
  have hU : MemLp U 2 (_root_.GD.N0107.d009030 m n mu sigma tau) := by
    exact _root_.GD.N0107.d012747
      m n hm hn mu sigma tau hsigma htau
  have horth :
      (∫ omega, U omega * (D omega * (L omega - t))
        ∂_root_.GD.N0107.d009030 m n mu sigma tau) = 0 := by
    exact _root_.GD.N0232.N0720.N1425.d014724
      m n hm hn mu sigma tau hsigma htau g hg hcarrier
  have hrisk := _root_.GD.N0232.N0720.N1207.d012751
    hU hcarrier horth
  have herror :
      (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - mu) =
        _root_.GD.N0141.d006685 U D L t := by
    funext omega
    exact _root_.GD.N0232.N0720.N1425.d014721
      m n hm hn mu sigma tau hsigma htau g omega
  have hsource := _root_.GD.N0107.d009052
    m n hm hn mu sigma tau hsigma htau
      (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦ (g x - t) ^ 2)
      ((hg.sub measurable_const).pow_const 2)
  have hsource' :
      (∫ omega, D omega ^ 2 * (L omega - t) ^ 2
        ∂_root_.GD.N0107.d009030 m n mu sigma tau) =
        Sigma * _root_.GD.N0120.d008809
          (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t
            (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦ (g x - t) ^ 2) := by
    simpa [D, L, t, Sigma, _root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208] using hsource
  have hprojective :=
    _root_.GD.N0232.N0720.N1425.d014723
      hm hn ht0 ht1 (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦ (g x - t) ^ 2)
        ((hg.sub measurable_const).pow_const 2)
  rw [herror]
  calc
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau) (_root_.GD.N0141.d006685 U D L t) =
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau) U +
          ∫ omega, D omega ^ 2 * (L omega - t) ^ 2
            ∂_root_.GD.N0107.d009030 m n mu sigma tau := by
      linarith [hrisk]
    _ = _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau) U +
          Sigma * _root_.GD.N0120.d008809
            (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t
              (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦ (g x - t) ^ 2) := by
      exact congrArg
        (fun z ↦ _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau) U + z)
        hsource'
    _ = _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau) U +
          Sigma * ∫ x, (g x - t) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n t := by
      rw [hprojective]



theorem d014726
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : 0 ≤ B) (hgBound : ∀ x, |g x| ≤ B) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 m n g omega - mu) =
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (_root_.GD.N0107.d012732 m n mu
            (_root_.GD.N0107.d009046 m n sigma tau)) +
        _root_.GD.N0107.d009045 m n sigma tau *
          ∫ x,
            (g x - _root_.GD.N0107.d009046 m n sigma tau) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n
              (_root_.GD.N0107.d009046 m n sigma tau) := by
  let t := _root_.GD.N0107.d009046 m n sigma tau
  have ht0 : 0 < t := _root_.GD.N0107.d009050
    (by omega) (by omega) hsigma htau
  have ht1 : t < 1 := _root_.GD.N0107.d009051
    (by omega) (by omega) hsigma htau
  let q : _root_.GD.N0232.N0720.N1436.d013217 → ℝ := fun x ↦ g x - t
  have hq : Measurable q := hg.sub measurable_const
  have hqBound : ∀ x, |q x| ≤ B + 1 := by
    intro x
    calc
      |q x| = |g x - t| := rfl
      _ ≤ |g x| + |t| := abs_sub _ _
      _ ≤ B + 1 := by
        apply add_le_add
        · exact hgBound x
        · rw [abs_of_pos ht0]
          exact ht1.le
  have hcarrier :=
    (_root_.GD.N0107.d012748
      m n hm hn mu sigma tau hsigma htau q hq
      (show 0 ≤ B + 1 by positivity) hqBound).2
  exact
    _root_.GD.N0232.N0720.N1425.d014725
      m n hm hn mu sigma tau hsigma htau g hg
        (by simpa [q, t] using hcarrier)

end

end N1425
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1425.d014723
#print axioms _root_.GD.N0232.N0720.N1425.d014722
#print axioms _root_.GD.N0232.N0720.N1425.d014725
#print axioms _root_.GD.N0232.N0720.N1425.d014726
