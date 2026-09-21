import GD.Module0653
import GD.Module0662
import GD.Module0714




















open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0914

noncomputable section



theorem d010619
    {k : ℕ}
    {shape variance : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hvariance : ∀ i, 0 < variance i) :
    ∀ i, 0 < _root_.GD.N0232.N0719.N0960.d009692 shape variance i := by
  intro i
  exact div_pos (hshape i) (hvariance i)



theorem d010620
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk) :
    0 <
      _root_.GD.N0232.N0719.N0954.d009508
        shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) := by
  have hp :
      ∀ i, 0 < _root_.GD.N0232.N0719.N0853.d009567 hk q i :=
    fun i => _root_.GD.N0232.N0719.N0951.d003590 hk hq i
  rw [_root_.GD.N0232.N0719.N0954.d009515
    hk hshape hrate hp]
  exact mul_pos
    (_root_.GD.N0232.N0719.N0954.d009516 hk hshape hrate)
    (lt_of_lt_of_le
      (_root_.GD.N0232.N0719.N0954.d009519 hk hshape)
      (_root_.GD.N0232.N0719.N0954.d009521
        hk hshape
        (_root_.GD.N0232.N0719.N0954.d009513 hk hrate) hq))








theorem d010621
    {k : ℕ} (hk : 0 < k)
    {shape variance : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hvariance : ∀ i, 0 < variance i)
    (triangle : Fin 3 ↪ Fin k)
    {V : ℝ} (hV : 0 < V)
    (hselected : variance (triangle 0) ≤ V)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk)
    {H : ℝ} (hH : 0 ≤ H) :
    _root_.GD.N0232.N0719.N0954.d009508
          shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
        (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) * H ≤
      ∫ ω in Set.Ioi 0,
        _root_.GD.N0232.N0719.N0954.d009483
            (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
            (_root_.GD.N0232.N0719.N0954.d009350 hk
              (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
            (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
          (H / (ω + V)) := by
  have hrate :
      ∀ i, 0 < _root_.GD.N0232.N0719.N0960.d009692 shape variance i :=
    _root_.GD.N0232.N0719.N0914.d010619 hshape hvariance
  have hqInterior :
      q ∈ _root_.GD.N0232.N0719.N0955.d009607 k :=
    _root_.GD.N0232.N0719.N0955.d009622 hk hq
  have hradial :=
    _root_.GD.N0232.N0719.N0960.d009695
      hk hshape hvariance hq (triangle 0) hselected
  have hmarg :
      0 ≤
        _root_.GD.N0232.N0719.N0954.d009508
          shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) :=
    (_root_.GD.N0232.N0719.N0914.d010620
      hk hshape hrate hq).le
  have hscaled :
      _root_.GD.N0232.N0719.N0954.d009508
            shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
          (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) * H ≤
        _root_.GD.N0232.N0719.N0954.d009508
            shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
          (∫ ω,
            1 / (ω + V)
              ∂gammaMeasure
                (_root_.GD.N0232.N0719.N0954.d009503 shape)
                (_root_.GD.N0232.N0719.N0951.d003587
                  (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
                  (_root_.GD.N0232.N0719.N0853.d009567 hk q))) * H := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hradial hmarg) hH
  rw [_root_.GD.N0232.N0719.N0955.d009625
    hk hshape hrate hqInterior
    (fun ω => H / (ω + V))]
  rw [show
      (∫ ω,
          H / (ω + V)
            ∂gammaMeasure
              (_root_.GD.N0232.N0719.N0954.d009503 shape)
              (_root_.GD.N0232.N0719.N0951.d003587
                (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
                (_root_.GD.N0232.N0719.N0853.d009567 hk q))) =
        H *
          ∫ ω,
            1 / (ω + V)
              ∂gammaMeasure
                (_root_.GD.N0232.N0719.N0954.d009503 shape)
                (_root_.GD.N0232.N0719.N0951.d003587
                  (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
                  (_root_.GD.N0232.N0719.N0853.d009567 hk q)) by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    ring]
  nlinarith






theorem d010622
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk)
    (H : ℝ) :
    (∫ ω in Set.Ioi 0,
        _root_.GD.N0232.N0719.N0954.d009483
            (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
            (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
            (_root_.GD.N0232.N0719.N0955.d009612 q ω) * H) =
      _root_.GD.N0232.N0719.N0954.d009508
        shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) * H := by
  rw [_root_.GD.N0232.N0719.N0955.d009625
    hk hshape hrate
    (_root_.GD.N0232.N0719.N0955.d009622 hk hq)
    (fun _ => H)]
  letI :
      IsProbabilityMeasure
        (gammaMeasure
          (_root_.GD.N0232.N0719.N0954.d009503 shape)
          (_root_.GD.N0232.N0719.N0951.d003587 rate
            (_root_.GD.N0232.N0719.N0853.d009567 hk q))) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0232.N0719.N0954.d009504 hk hshape)
      (by
        unfold _root_.GD.N0232.N0719.N0951.d003587
        exact Finset.sum_pos
          (fun i _ =>
            div_pos (hrate i)
              (_root_.GD.N0232.N0719.N0951.d003590 hk hq i))
          ⟨⟨0, hk⟩, Finset.mem_univ _⟩)
  simp



def d010623
    {k : ℕ} (hk : 0 < k)
    (shape variance : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ)
    (V : ℝ) : ℝ :=
  ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
    ∫ ω in Set.Ioi 0,
      _root_.GD.N0232.N0719.N0954.d009483
          (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
          (_root_.GD.N0232.N0719.N0954.d009350 hk
            (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
          (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
        (_root_.GD.N0232.N0719.N0855.d010602 hk triangle q w /
          (ω + V))



def d010624
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (V : ℝ)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) : ℝ :=
  250000 * _root_.GD.N0232.N0719.N0855.d010601 hk triangle q ^ 2 * V






theorem d010625
    {k : ℕ} (hk : 0 < k)
    (hk3 : 3 ≤ k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    {V : ℝ} (hV : 0 ≤ V)
    (hfull :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
            _root_.GD.N0232.N0719.N0914.d010624 hk (Fin.castLEEmb hk3) V q)
        (_root_.GD.N0232.N0719.N0853.d009581 hk)) :
    _root_.GD.N0232.N0719.N0954.d009509 shape rate *
        (∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
            _root_.GD.N0232.N0719.N0914.d010624 hk (Fin.castLEEmb hk3) V q) ≤
      _root_.GD.N0232.N0719.N0954.d009509 shape rate *
        V * _root_.GD.N0232.N0719.N0950.d010595 shape := by
  have hbound :=
    _root_.GD.N0232.N0719.N0855.d010618
      hk hk3 hshape hrate hV
      (_root_.GD.N0232.N0719.N0914.d010624 hk (Fin.castLEEmb hk3) V)
      (fun q hq => by
        unfold _root_.GD.N0232.N0719.N0914.d010624
        exact mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg _)) hV)
      (fun q hq => by rfl)
      hfull
  calc
    _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          (∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
            _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
              _root_.GD.N0232.N0719.N0914.d010624 hk (Fin.castLEEmb hk3) V q) ≤
        _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          (_root_.GD.N0232.N0719.N0954.d009518 shape *
            (250000 * _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V)) :=
      hbound
    _ =
        _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          V * _root_.GD.N0232.N0719.N0950.d010595 shape := by
      unfold _root_.GD.N0232.N0719.N0950.d010595
      ring






theorem d010626
    {k : ℕ} (hk : 0 < k)
    {shape variance : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hvariance : ∀ i, 0 < variance i)
    (triangle : Fin 3 ↪ Fin k)
    {V : ℝ} (hV : 0 < V)
    (hselected : variance (triangle 0) ≤ V)
    (w : Fin 3 → ℝ)
    (hleft :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0954.d009508
              shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
              (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
            (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
            _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w)
        (_root_.GD.N0232.N0719.N0853.d009581 hk))
    (hright :
      IntegrableOn
        (fun q =>
          ∫ ω in Set.Ioi 0,
            _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
                (_root_.GD.N0232.N0719.N0954.d009350 hk
                  (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              (_root_.GD.N0232.N0719.N0855.d010602 hk triangle q w /
                (ω + V)))
        (_root_.GD.N0232.N0719.N0853.d009581 hk)) :
    (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
        _root_.GD.N0232.N0719.N0855.d010604
          hk shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) triangle w ≤
      _root_.GD.N0232.N0719.N0914.d010623
        hk shape variance triangle w V := by
  have hrate :
      ∀ i, 0 < _root_.GD.N0232.N0719.N0960.d009692 shape variance i :=
    _root_.GD.N0232.N0719.N0914.d010619 hshape hvariance
  have hpoint :
      ∀ q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk,
        _root_.GD.N0232.N0719.N0954.d009508
              shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
              (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
            (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
            _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w ≤
          ∫ ω in Set.Ioi 0,
            _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
                (_root_.GD.N0232.N0719.N0954.d009350 hk
                  (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              (_root_.GD.N0232.N0719.N0855.d010602 hk triangle q w /
                (ω + V)) := by
    intro q hq
    exact _root_.GD.N0232.N0719.N0914.d010621
      hk hshape hvariance triangle hV hselected hq
      (_root_.GD.N0232.N0719.N0855.d010608 hk triangle hq w)
  have hmono :=
    setIntegral_mono_on hleft hright
      (_root_.GD.N0232.N0719.N0853.d009583 hk).measurableSet hpoint
  have hprojective :
      (∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
          _root_.GD.N0232.N0719.N0954.d009508
                shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
                (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
              (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
              _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w) =
        (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
          _root_.GD.N0232.N0719.N0855.d010604
            hk shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) triangle w := by
    unfold _root_.GD.N0232.N0719.N0855.d010604
    calc
      (∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
            _root_.GD.N0232.N0719.N0954.d009508
                  shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
                  (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
                (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
                _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w) =
          ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
            ((_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
              _root_.GD.N0232.N0719.N0954.d009509
                shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)) *
              (_root_.GD.N0232.N0719.N0855.d010603
                  hk shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) q *
                _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w) := by
            apply setIntegral_congr_fun
              (_root_.GD.N0232.N0719.N0853.d009583 hk).measurableSet
            intro q hq
            have hp :
                ∀ i, 0 < _root_.GD.N0232.N0719.N0853.d009567 hk q i :=
              fun i => _root_.GD.N0232.N0719.N0951.d003590 hk hq i
            simp only
            rw [_root_.GD.N0232.N0719.N0954.d009515
              hk hshape hrate hp]
            simp [_root_.GD.N0232.N0719.N0855.d010603]
            ring
      _ =
          ((_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
              _root_.GD.N0232.N0719.N0954.d009509
                shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)) *
            ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
              _root_.GD.N0232.N0719.N0855.d010603
                  hk shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) q *
                _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w := by
            rw [integral_const_mul]
      _ =
          (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
            (_root_.GD.N0232.N0719.N0954.d009509
                shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) *
              ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
                _root_.GD.N0232.N0719.N0855.d010603
                    hk shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) q *
                  _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w) := by
            ring
  rw [← hprojective]
  exact hmono












theorem d010627
    {k : ℕ} (hk : 0 < k)
    {shape variance : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hvariance : ∀ i, 0 < variance i)
    (triangle : Fin 3 ↪ Fin k)
    {V : ℝ} (hV : 0 < V)
    (hselected : variance (triangle 0) ≤ V)
    {w : Fin 3 → ℝ}
    (hw :
      w ∈
        _root_.GD.N0232.N0719.N0856.d009532)
    (hprojective :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 hk shape
              (_root_.GD.N0232.N0719.N0960.d009692 shape variance) q *
            _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w)
        (_root_.GD.N0232.N0719.N0853.d009581 hk))
    (hleft :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0954.d009508
              shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
              (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
            (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
            _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w)
        (_root_.GD.N0232.N0719.N0853.d009581 hk))
    (hright :
      IntegrableOn
        (fun q =>
          ∫ ω in Set.Ioi 0,
            _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
                (_root_.GD.N0232.N0719.N0954.d009350 hk
                  (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              (_root_.GD.N0232.N0719.N0855.d010602 hk triangle q w /
                (ω + V)))
        (_root_.GD.N0232.N0719.N0853.d009581 hk)) :
    _root_.GD.N0232.N0719.N0954.d009509
          shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) *
        V * _root_.GD.N0232.N0719.N0950.d010593 hk shape triangle ≤
      (3 / 128) * _root_.GD.N0232.N0719.N0950.d010587 k * V ^ 2 *
        _root_.GD.N0232.N0719.N0914.d010623
          hk shape variance triangle w V := by
  have hrate :
      ∀ i, 0 < _root_.GD.N0232.N0719.N0960.d009692 shape variance i :=
    _root_.GD.N0232.N0719.N0914.d010619 hshape hvariance
  have hprojectiveLower :=
    _root_.GD.N0232.N0719.N0855.d010616
      hk hshape hrate triangle hw hprojective
  have hradial :=
    _root_.GD.N0232.N0719.N0914.d010626
      hk hshape hvariance triangle hV hselected w
      hleft hright
  have hc :
      0 < _root_.GD.N0232.N0719.N0950.d010591 shape triangle :=
    _root_.GD.N0232.N0719.N0950.d010592 hk hshape triangle
  have hscale :
      0 <
        (3 / 128 : ℝ) *
          _root_.GD.N0232.N0719.N0950.d010587 k * V ^ 2 :=
    mul_pos
      (mul_pos (by norm_num)
        (_root_.GD.N0232.N0719.N0950.d010589 hk))
      (sq_pos_of_pos hV)
  have hcombined :
      (3 / 128) * _root_.GD.N0232.N0719.N0950.d010587 k * V ^ 2 *
          ((_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
            (_root_.GD.N0232.N0719.N0954.d009509
                shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) *
              (_root_.GD.N0232.N0719.N0954.d009517 shape *
                _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 *
                _root_.GD.N0232.N0719.N0857.d009401 k *
                (_root_.GD.N0232.N0719.N0853.d009592 hk triangle *
                  (volume
                    (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal)))) ≤
        (3 / 128) * _root_.GD.N0232.N0719.N0950.d010587 k * V ^ 2 *
          _root_.GD.N0232.N0719.N0914.d010623
            hk shape variance triangle w V :=
    mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left
        hprojectiveLower
        (div_nonneg hc.le hV.le)).trans hradial)
      hscale.le
  have hfloor :
      _root_.GD.N0232.N0719.N0950.d010582 hk triangle =
        _root_.GD.N0232.N0719.N0853.d009592 hk triangle := rfl
  have hfactor :
      _root_.GD.N0232.N0719.N0954.d009509
            shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) *
          V * _root_.GD.N0232.N0719.N0950.d010593 hk shape triangle =
        (3 / 128) * _root_.GD.N0232.N0719.N0950.d010587 k * V ^ 2 *
          ((_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
            (_root_.GD.N0232.N0719.N0954.d009509
                shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) *
              (_root_.GD.N0232.N0719.N0954.d009517 shape *
                _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 *
                _root_.GD.N0232.N0719.N0857.d009401 k *
                (_root_.GD.N0232.N0719.N0853.d009592 hk triangle *
                  (volume
                    (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal)))) := by
    rw [_root_.GD.N0232.N0719.N0950.d010593,
      _root_.GD.N0232.N0719.N0950.d010585, hfloor]
    field_simp [hV.ne']
  rw [hfactor]
  exact hcombined














theorem d010628
    {k : ℕ} (hk3 : 3 ≤ k)
    {shape variance : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hvariance : ∀ i, 0 < variance i)
    {V B C : ℝ} (hV : 0 < V)
    (hselected :
      variance ((Fin.castLEEmb hk3) 0) ≤ V)
    {w : Fin 3 → ℝ}
    (hw :
      w ∈
        _root_.GD.N0232.N0719.N0856.d009532)
    (hprojectiveGain :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 (by omega) shape
              (_root_.GD.N0232.N0719.N0960.d009692 shape variance) q *
            _root_.GD.N0232.N0719.N0855.d010602 (by omega)
              (Fin.castLEEmb hk3) q w)
        (_root_.GD.N0232.N0719.N0853.d009581 (by omega)))
    (hleft :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0954.d009508
              shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
              (_root_.GD.N0232.N0719.N0853.d009567 (by omega) q) *
            (_root_.GD.N0232.N0719.N0950.d010591 shape
              (Fin.castLEEmb hk3) / V) *
            _root_.GD.N0232.N0719.N0855.d010602 (by omega)
              (Fin.castLEEmb hk3) q w)
        (_root_.GD.N0232.N0719.N0853.d009581 (by omega)))
    (hright :
      IntegrableOn
        (fun q =>
          ∫ ω in Set.Ioi 0,
            _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 (by omega) shape)
                (_root_.GD.N0232.N0719.N0954.d009350 (by omega)
                  (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              (_root_.GD.N0232.N0719.N0855.d010602 (by omega)
                  (Fin.castLEEmb hk3) q w /
                (ω + V)))
        (_root_.GD.N0232.N0719.N0853.d009581 (by omega)))
    (hprojectiveEnergy :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 (by omega) shape
              (_root_.GD.N0232.N0719.N0960.d009692 shape variance) q *
            _root_.GD.N0232.N0719.N0914.d010624 (by omega)
              (Fin.castLEEmb hk3) V q)
        (_root_.GD.N0232.N0719.N0853.d009581 (by omega)))
    (henergyBridge :
      B ≤
        _root_.GD.N0232.N0719.N0954.d009509
            shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance) *
          ∫ q in _root_.GD.N0232.N0719.N0853.d009581 (by omega),
            _root_.GD.N0232.N0719.N0855.d010603 (by omega) shape
                (_root_.GD.N0232.N0719.N0960.d009692 shape variance) q *
              _root_.GD.N0232.N0719.N0914.d010624 (by omega)
                (Fin.castLEEmb hk3) V q)
    (hcrossBridge :
      (3 / 128) *
          _root_.GD.N0232.N0719.N0950.d010587 k * V ^ 2 *
          _root_.GD.N0232.N0719.N0914.d010623
            (by omega) shape variance
            (Fin.castLEEmb hk3) w V ≤
        -C) :
    C < 0 ∧
      B ≤
        _root_.GD.N0232.N0719.N0950.d010597
            (by omega) shape (Fin.castLEEmb hk3) *
          (-C) := by
  let hk : 0 < k := by omega
  let triangle : Fin 3 ↪ Fin k := Fin.castLEEmb hk3
  let rate : Fin k → ℝ := _root_.GD.N0232.N0719.N0960.d009692 shape variance
  have hrate : ∀ i, 0 < rate i :=
    _root_.GD.N0232.N0719.N0914.d010619 hshape hvariance
  have hgain :=
    _root_.GD.N0232.N0719.N0914.d010627
      hk hshape hvariance triangle hV hselected hw
      hprojectiveGain hleft hright
  have hgainCross :
      _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          V * _root_.GD.N0232.N0719.N0950.d010593 hk shape triangle ≤
        -C :=
    hgain.trans hcrossBridge
  have hstrict :
      0 <
        _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          V * _root_.GD.N0232.N0719.N0950.d010593 hk shape triangle :=
    mul_pos
      (mul_pos
        (_root_.GD.N0232.N0719.N0954.d009516 hk hshape hrate)
        hV)
      (_root_.GD.N0232.N0719.N0950.d010594
        hk hshape triangle)
  have hC : C < 0 := by
    linarith
  have henergyEnvelope :=
    _root_.GD.N0232.N0719.N0914.d010625
      hk hk3 hshape hrate hV.le hprojectiveEnergy
  have henergy :
      B ≤
        _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          V * _root_.GD.N0232.N0719.N0950.d010595 shape :=
    henergyBridge.trans henergyEnvelope
  refine ⟨hC, ?_⟩
  exact
    _root_.GD.N0232.N0719.N0950.d010600
      hk hshape triangle
      (_root_.GD.N0232.N0719.N0954.d009516 hk hshape hrate)
      hV henergy hgainCross

end

end GD.N0232.N0719.N0914
