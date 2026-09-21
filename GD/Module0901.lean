import GD.Module0900
import GD.Module0855
import GD.Module0859
import GD.Module0880
import GD.Module0836



















open MeasureTheory ProbabilityTheory Filter Set

namespace GD
namespace N0232
namespace N0720
namespace N1433

noncomputable section

open _root_.GD.N0232.N0720.N1423
open _root_.GD.N0232.N0720.N1421
open _root_.GD.N0232.N0720.N1426
open _root_.GD.N0232.N0720.N1428
open _root_.GD.N0232.N0720.N1438
open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0107
open _root_.GD.N0137
open _root_.GD.N0141


def d014024 (m : ℕ) : ℝ :=
  ((m - 1 : ℕ) : ℝ) / 2


def d014025 (n : ℕ) : ℝ :=
  ((n - 1 : ℕ) : ℝ) / 2

theorem d014026
    {m : ℕ} (hm : 2 ≤ m) :
    0 < _root_.GD.N0232.N0720.N1433.d014024 m := by
  unfold _root_.GD.N0232.N0720.N1433.d014024
  have hm1 : 0 < m - 1 := by omega
  exact div_pos (by exact_mod_cast hm1) (by norm_num)

theorem d014027
    {n : ℕ} (hn : 2 ≤ n) :
    0 < _root_.GD.N0232.N0720.N1433.d014025 n := by
  unfold _root_.GD.N0232.N0720.N1433.d014025
  have hn1 : 0 < n - 1 := by omega
  exact div_pos (by exact_mod_cast hn1) (by norm_num)


def d014028
    (m n : ℕ) (mu sigma tau : ℝ) : ℝ :=
  _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun omega => _root_.GD.N0107.d012733 m n omega - mu) -
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
      (_root_.GD.N0107.d012732 m n mu (_root_.GD.N0107.d009046 m n sigma tau))



theorem d014029
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    (∫ omega,
        _root_.GD.N0107.d012732 m n mu (_root_.GD.N0107.d009046 m n sigma tau) omega *
          (_root_.GD.N0107.d009038 m n mu sigma tau
              (_root_.GD.N0107.d009046 m n sigma tau)
              (_root_.GD.N0107.d009045 m n sigma tau) omega *
            (_root_.GD.N0107.d009039 m n mu sigma tau
                (_root_.GD.N0107.d009046 m n sigma tau) omega -
              _root_.GD.N0107.d009046 m n sigma tau))
      ∂_root_.GD.N0107.d009030 m n mu sigma tau) = 0 := by
  let e := _root_.GD.N0107.d009046 m n sigma tau
  let Sigma := _root_.GD.N0107.d009045 m n sigma tau
  have hU := _root_.GD.N0107.d012747
    m n hm hn mu sigma tau hsigma htau
  have hWeight : MemLp
      (fun omega =>
        _root_.GD.N0107.d009038 m n mu sigma tau e Sigma omega *
          (_root_.GD.N0107.d009039 m n mu sigma tau e omega - e))
      2 (_root_.GD.N0107.d009030 m n mu sigma tau) := by
    exact (_root_.GD.N0107.d012748
      m n hm hn mu sigma tau hsigma htau
      (fun _ : ℝ × ℝ => 0) measurable_const
      (B := 0) (by norm_num) (by intro p; simp)).1
  have hIndepDLF := _root_.GD.N0107.d012745
    m n hm hn mu sigma tau hsigma htau
  have hIndepWeight : IndepFun
      (_root_.GD.N0107.d012732 m n mu e)
      (fun omega =>
        _root_.GD.N0107.d009038 m n mu sigma tau e Sigma omega *
          (_root_.GD.N0107.d009039 m n mu sigma tau e omega - e))
      (_root_.GD.N0107.d009030 m n mu sigma tau) := by
    have h := hIndepDLF.comp measurable_id
      (show Measurable
        (fun p : ℝ × (ℝ × ℝ) => p.1 * (p.2.1 - e)) by fun_prop)
    simpa [e, Sigma, Function.comp_def] using h
  have hCentered := _root_.GD.N0107.d012746
    m n hm hn mu sigma tau hsigma htau
  exact _root_.GD.N0141.d006692
    hIndepWeight hU.aestronglyMeasurable
      hWeight.aestronglyMeasurable hCentered






theorem d014030
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega => _root_.GD.N0107.d012733 m n omega - mu) -
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (_root_.GD.N0107.d012732 m n mu (_root_.GD.N0107.d009046 m n sigma tau)) =
      _root_.GD.N0107.d009045 m n sigma tau *
        _root_.GD.N0232.N0720.N1091.d012791
          (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
          (_root_.GD.N0107.d009046 m n sigma tau) := by
  let e := _root_.GD.N0107.d009046 m n sigma tau
  let Sigma := _root_.GD.N0107.d009045 m n sigma tau
  have he0 : 0 < e :=
    _root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau
  have he1 : e < 1 :=
    _root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau
  have hU := _root_.GD.N0107.d012747
    m n hm hn mu sigma tau hsigma htau
  have hWeight : MemLp
      (fun omega =>
        _root_.GD.N0107.d009038 m n mu sigma tau e Sigma omega *
          (_root_.GD.N0107.d009039 m n mu sigma tau e omega - e))
      2 (_root_.GD.N0107.d009030 m n mu sigma tau) := by
    exact (_root_.GD.N0107.d012748
      m n hm hn mu sigma tau hsigma htau
      (fun _ : ℝ × ℝ => 0) measurable_const
      (B := 0) (by norm_num) (by intro p; simp)).1
  have hOrth := _root_.GD.N0232.N0720.N1433.d014029
    m n hm hn mu sigma tau hsigma htau
  have hLaw := _root_.GD.N0107.d009052
    m n hm hn mu sigma tau hsigma htau
  have hRisk := _root_.GD.N0232.N0720.N1423.d014022
    (alpha := _root_.GD.N0232.N0720.N1433.d014024 m)
    (beta := _root_.GD.N0232.N0720.N1433.d014025 n)
    (p := e) (Sigma := Sigma)
    (U := _root_.GD.N0107.d012732 m n mu e)
    (D := _root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
    (L := _root_.GD.N0107.d009039 m n mu sigma tau e)
    (F := _root_.GD.N0107.d009040 m n mu sigma tau e)
    (_root_.GD.N0232.N0720.N1433.d014026 hm) (_root_.GD.N0232.N0720.N1433.d014027 hn)
    he0 he1 hU hWeight hOrth hLaw
  have hBase :
      _root_.GD.N0141.d006685
          (_root_.GD.N0107.d012732 m n mu e)
          (_root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
          (_root_.GD.N0107.d009039 m n mu sigma tau e) e =
        (fun omega => _root_.GD.N0107.d012733 m n omega - mu) := by
    funext omega
    dsimp [e, Sigma]
    unfold _root_.GD.N0141.d006685
    rw [_root_.GD.N0107.d012724
      m n hm hn mu sigma tau hsigma htau omega,
      _root_.GD.N0107.d012729
        m n hm hn mu sigma tau hsigma htau omega]
    unfold _root_.GD.N0107.d012733 _root_.GD.N0107.d012732
    ring
  rw [hBase] at hRisk
  simpa [_root_.GD.N0232.N0720.N1433.d014024, _root_.GD.N0232.N0720.N1433.d014025, e, Sigma] using hRisk


theorem d014031
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1433.d014028 m n mu sigma tau =
      _root_.GD.N0107.d009045 m n sigma tau *
        _root_.GD.N0232.N0720.N1091.d012791
          (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
          (_root_.GD.N0107.d009046 m n sigma tau) := by
  unfold _root_.GD.N0232.N0720.N1433.d014028
  exact _root_.GD.N0232.N0720.N1433.d014030
    m n hm hn mu sigma tau hsigma htau


theorem d014032
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1433.d014028 m n mu sigma tau =
      _root_.GD.N0107.d009045 m n sigma tau *
        _root_.GD.N0232.N0720.N1091.d012790
          (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
          (_root_.GD.N0107.d009046 m n sigma tau) := by
  rw [_root_.GD.N0232.N0720.N1433.d014031
    m n hm hn mu sigma tau hsigma htau]
  congr 1
  symm
  exact _root_.GD.N0232.N0720.N1091.d012800
    (_root_.GD.N0232.N0720.N1433.d014026 hm) (_root_.GD.N0232.N0720.N1433.d014027 hn)
    (_root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau)
    (_root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau)

theorem d014033
    {m : ℕ} (hm : 6 ≤ m) :
    2 < _root_.GD.N0232.N0720.N1433.d014024 m := by
  unfold _root_.GD.N0232.N0720.N1433.d014024
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  norm_num
  exact_mod_cast (show 4 < m - 1 by omega)

theorem d014034
    {n : ℕ} (hn : 6 ≤ n) :
    2 < _root_.GD.N0232.N0720.N1433.d014025 n := by
  unfold _root_.GD.N0232.N0720.N1433.d014025
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  norm_num
  exact_mod_cast (show 4 < n - 1 by omega)

@[simp] theorem d014035 :
    _root_.GD.N0232.N0720.N1433.d014024 5 = 2 := by
  norm_num [_root_.GD.N0232.N0720.N1433.d014024]

@[simp] theorem d014036 :
    _root_.GD.N0232.N0720.N1433.d014025 5 = 2 := by
  norm_num [_root_.GD.N0232.N0720.N1433.d014025]





theorem d014037
    {m n : ℕ} (hm : 6 ≤ m) (hn : 2 ≤ n)
    {mu sigma tau : ℕ → ℝ}
    (hsigma : ∀ k, 0 < sigma k) (htau : ∀ k, 0 < tau k)
    (hp : Tendsto
      (fun k => _root_.GD.N0107.d009046 m n (sigma k) (tau k))
      atTop (nhds 0)) :
    Tendsto
      (fun k =>
        _root_.GD.N0232.N0720.N1433.d014028 m n (mu k) (sigma k) (tau k) /
          (_root_.GD.N0107.d009045 m n (sigma k) (tau k) *
            _root_.GD.N0107.d009046 m n (sigma k) (tau k) ^ 2))
      atTop
      (nhds
        ((_root_.GD.N0232.N0720.N1433.d014024 m ^ 2 +
              _root_.GD.N0232.N0720.N1433.d014024 m * _root_.GD.N0232.N0720.N1433.d014025 n +
              2 * _root_.GD.N0232.N0720.N1433.d014025 n) /
          (_root_.GD.N0232.N0720.N1433.d014025 n * (_root_.GD.N0232.N0720.N1433.d014024 m - 1) *
            (_root_.GD.N0232.N0720.N1433.d014024 m - 2)))) := by
  let p : ℕ → ℝ := fun k => _root_.GD.N0107.d009046 m n (sigma k) (tau k)
  have hm2 : 2 ≤ m := by omega
  have hp0 : ∀ k, 0 < p k := fun k =>
    _root_.GD.N0107.d009050 (by omega) (by omega) (hsigma k) (htau k)
  have hp1 : ∀ k, p k < 1 := fun k =>
    _root_.GD.N0107.d009051 (by omega) (by omega) (hsigma k) (htau k)
  have hBeta := _root_.GD.N0232.N0720.N1421.d013121
    (_root_.GD.N0232.N0720.N1433.d014033 hm) (_root_.GD.N0232.N0720.N1433.d014027 hn)
    (p := p) hp hp0 hp1
  convert hBeta using 1
  funext k
  dsimp [p]
  rw [_root_.GD.N0232.N0720.N1433.d014032
    m n hm2 hn (mu k) (sigma k) (tau k) (hsigma k) (htau k)]
  have hSigma : 0 < _root_.GD.N0107.d009045 m n (sigma k) (tau k) :=
    _root_.GD.N0107.d009049 (by omega) (by omega) (hsigma k) (htau k)
  field_simp [hSigma.ne', (hp0 k).ne']





theorem d014038
    {n : ℕ} (hn : 2 ≤ n)
    {mu sigma tau : ℕ → ℝ}
    (hsigma : ∀ k, 0 < sigma k) (htau : ∀ k, 0 < tau k)
    (hp : Tendsto
      (fun k => _root_.GD.N0107.d009046 5 n (sigma k) (tau k))
      atTop (nhds 0)) :
    Tendsto
      (fun k =>
        _root_.GD.N0232.N0720.N1433.d014028 5 n (mu k) (sigma k) (tau k) /
          (_root_.GD.N0107.d009045 5 n (sigma k) (tau k) *
            (_root_.GD.N0107.d009046 5 n (sigma k) (tau k) ^ 2 *
              Real.log (1 /
                _root_.GD.N0107.d009046 5 n (sigma k) (tau k)))))
      atTop
      (nhds (_root_.GD.N0232.N0720.N1428.d013133 (_root_.GD.N0232.N0720.N1433.d014025 n))) := by
  let p : ℕ → ℝ := fun k => _root_.GD.N0107.d009046 5 n (sigma k) (tau k)
  have hp0 : ∀ k, 0 < p k := fun k =>
    _root_.GD.N0107.d009050 (by omega) (by omega) (hsigma k) (htau k)
  have hp1 : ∀ k, p k < 1 := fun k =>
    _root_.GD.N0107.d009051 (by omega) (by omega) (hsigma k) (htau k)
  have hBeta := _root_.GD.N0232.N0720.N1426.d013206
    (_root_.GD.N0232.N0720.N1433.d014027 hn) (p := p) hp hp0 hp1
  convert hBeta using 1
  funext k
  dsimp [p]
  rw [_root_.GD.N0232.N0720.N1433.d014032
    5 n (by norm_num) hn (mu k) (sigma k) (tau k)
      (hsigma k) (htau k), _root_.GD.N0232.N0720.N1433.d014035]
  have hSigma : 0 < _root_.GD.N0107.d009045 5 n (sigma k) (tau k) :=
    _root_.GD.N0107.d009049 (by omega) (by omega) (hsigma k) (htau k)
  have hratio : 1 < 1 / _root_.GD.N0107.d009046 5 n (sigma k) (tau k) := by
    exact (lt_div_iff₀ (hp0 k)).2 (by simpa using hp1 k)
  have hlog : 0 < Real.log
      (1 / _root_.GD.N0107.d009046 5 n (sigma k) (tau k)) :=
    Real.log_pos hratio
  field_simp [hSigma.ne', (hp0 k).ne', hlog.ne']


theorem d014039
    {m n : ℕ} (hm : 2 ≤ m) (hn : 6 ≤ n)
    {mu sigma tau : ℕ → ℝ}
    (hsigma : ∀ k, 0 < sigma k) (htau : ∀ k, 0 < tau k)
    (hp : Tendsto
      (fun k => _root_.GD.N0107.d009046 m n (sigma k) (tau k))
      atTop (nhds 1)) :
    Tendsto
      (fun k =>
        _root_.GD.N0232.N0720.N1433.d014028 m n (mu k) (sigma k) (tau k) /
          (_root_.GD.N0107.d009045 m n (sigma k) (tau k) *
            (1 - _root_.GD.N0107.d009046 m n (sigma k) (tau k)) ^ 2))
      atTop
      (nhds
        ((_root_.GD.N0232.N0720.N1433.d014025 n ^ 2 +
              _root_.GD.N0232.N0720.N1433.d014025 n * _root_.GD.N0232.N0720.N1433.d014024 m +
              2 * _root_.GD.N0232.N0720.N1433.d014024 m) /
          (_root_.GD.N0232.N0720.N1433.d014024 m * (_root_.GD.N0232.N0720.N1433.d014025 n - 1) *
            (_root_.GD.N0232.N0720.N1433.d014025 n - 2)))) := by
  let p : ℕ → ℝ := fun k => _root_.GD.N0107.d009046 m n (sigma k) (tau k)
  have hn2 : 2 ≤ n := by omega
  have hp0 : ∀ k, 0 < p k := fun k =>
    _root_.GD.N0107.d009050 (by omega) (by omega) (hsigma k) (htau k)
  have hp1 : ∀ k, p k < 1 := fun k =>
    _root_.GD.N0107.d009051 (by omega) (by omega) (hsigma k) (htau k)
  have hBeta := _root_.GD.N0232.N0720.N1438.d013604
    (_root_.GD.N0232.N0720.N1433.d014026 hm) (_root_.GD.N0232.N0720.N1433.d014034 hn)
    (p := p) hp hp0 hp1
  convert hBeta using 1
  funext k
  dsimp [p]
  rw [_root_.GD.N0232.N0720.N1433.d014032
    m n hm hn2 (mu k) (sigma k) (tau k) (hsigma k) (htau k)]
  have hSigma : 0 < _root_.GD.N0107.d009045 m n (sigma k) (tau k) :=
    _root_.GD.N0107.d009049 (by omega) (by omega) (hsigma k) (htau k)
  have hright : 0 < 1 - _root_.GD.N0107.d009046 m n (sigma k) (tau k) :=
    sub_pos.mpr (hp1 k)
  field_simp [hSigma.ne', hright.ne']


theorem d014040
    {m : ℕ} (hm : 2 ≤ m)
    {mu sigma tau : ℕ → ℝ}
    (hsigma : ∀ k, 0 < sigma k) (htau : ∀ k, 0 < tau k)
    (hp : Tendsto
      (fun k => _root_.GD.N0107.d009046 m 5 (sigma k) (tau k))
      atTop (nhds 1)) :
    Tendsto
      (fun k =>
        _root_.GD.N0232.N0720.N1433.d014028 m 5 (mu k) (sigma k) (tau k) /
          (_root_.GD.N0107.d009045 m 5 (sigma k) (tau k) *
            ((1 - _root_.GD.N0107.d009046 m 5 (sigma k) (tau k)) ^ 2 *
              Real.log (1 /
                (1 - _root_.GD.N0107.d009046 m 5 (sigma k) (tau k))))))
      atTop
      (nhds (_root_.GD.N0232.N0720.N1428.d013133 (_root_.GD.N0232.N0720.N1433.d014024 m))) := by
  let p : ℕ → ℝ := fun k => _root_.GD.N0107.d009046 m 5 (sigma k) (tau k)
  have hp0 : ∀ k, 0 < p k := fun k =>
    _root_.GD.N0107.d009050 (by omega) (by omega) (hsigma k) (htau k)
  have hp1 : ∀ k, p k < 1 := fun k =>
    _root_.GD.N0107.d009051 (by omega) (by omega) (hsigma k) (htau k)
  have hBeta := _root_.GD.N0232.N0720.N1438.d013605
    (_root_.GD.N0232.N0720.N1433.d014026 hm) (p := p) hp hp0 hp1
  convert hBeta using 1
  funext k
  dsimp [p]
  rw [_root_.GD.N0232.N0720.N1433.d014032
    m 5 hm (by norm_num) (mu k) (sigma k) (tau k)
      (hsigma k) (htau k), _root_.GD.N0232.N0720.N1433.d014036]
  have hSigma : 0 < _root_.GD.N0107.d009045 m 5 (sigma k) (tau k) :=
    _root_.GD.N0107.d009049 (by omega) (by omega) (hsigma k) (htau k)
  have hright : 0 < 1 - _root_.GD.N0107.d009046 m 5 (sigma k) (tau k) :=
    sub_pos.mpr (hp1 k)
  have hratio : 1 <
      1 / (1 - _root_.GD.N0107.d009046 m 5 (sigma k) (tau k)) := by
    exact (lt_div_iff₀ hright).2 (by linarith [hp0 k])
  have hlog : 0 < Real.log
      (1 / (1 - _root_.GD.N0107.d009046 m 5 (sigma k) (tau k))) :=
    Real.log_pos hratio
  field_simp [hSigma.ne', hright.ne', hlog.ne']

end

end N1433
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1433.d014029
#print axioms _root_.GD.N0232.N0720.N1433.d014030
#print axioms _root_.GD.N0232.N0720.N1433.d014032
#print axioms _root_.GD.N0232.N0720.N1433.d014037
#print axioms _root_.GD.N0232.N0720.N1433.d014038
#print axioms _root_.GD.N0232.N0720.N1433.d014039
#print axioms _root_.GD.N0232.N0720.N1433.d014040
