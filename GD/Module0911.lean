import GD.Module0910

















namespace GD.N0232.N0720

noncomputable section



abbrev d014158 :=
  _root_.GD.N0145.d014114



abbrev d014159
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :=
  _root_.GD.N0117.d014139 U



abbrev d014160
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :=
  _root_.GD.N0117.d014154 U


theorem d014161
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    Measurable (_root_.GD.N0232.N0720.d014159 U) :=
  by
    simpa only [_root_.GD.N0232.N0720.d014159] using
      (_root_.GD.N0117.d014145 U)


theorem d014162
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    Measurable
      (_root_.GD.N0107.d012734
        m n (U.step : ℝ) (_root_.GD.N0232.N0720.d014159 U)) :=
  by
    simpa only [_root_.GD.N0232.N0720.d014159] using
      (_root_.GD.N0117.d014147 U)



theorem d014163
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (d : ℝ) {c : ℝ} (hc : c ≠ 0)
    (ω : _root_.GD.N0137.d008894 m ×
      _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.d014159 U
        (_root_.GD.N0107.d009024 m n d c c ω) =
      _root_.GD.N0232.N0720.d014159 U ω :=
  by
    simpa only [_root_.GD.N0232.N0720.d014159] using
      (_root_.GD.N0117.d014152
        U d hc ω)


theorem d014164
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (d : ℝ) {c : ℝ} (hc : c ≠ 0)
    (ω : _root_.GD.N0137.d008894 m ×
      _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d012734
        m n (U.step : ℝ) (_root_.GD.N0232.N0720.d014159 U)
        (_root_.GD.N0107.d009024 m n d c c ω) =
      d + c *
        _root_.GD.N0107.d012734
          m n (U.step : ℝ) (_root_.GD.N0232.N0720.d014159 U) ω :=
  by
    simpa only [_root_.GD.N0232.N0720.d014159] using
      (_root_.GD.N0117.d014153
        U d hc ω)


theorem d014165
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    0 < _root_.GD.N0232.N0720.d014160 U :=
  by
    simpa only [_root_.GD.N0232.N0720.d014160] using
      (_root_.GD.N0117.d014155 U)


theorem d014166
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (Ucert : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
    _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n μ σ τ)
          (fun ω =>
            _root_.GD.N0107.d012734
                m n (Ucert.step : ℝ) (_root_.GD.N0232.N0720.d014159 Ucert) ω - μ)
        -
        _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n μ σ τ)
          (fun ω =>
            _root_.GD.N0107.d012733 m n ω - μ)
      ≤
        -(_root_.GD.N0107.d009045 m n σ τ *
          _root_.GD.N0120.d008813
            (((m - 1 : ℕ) : ℝ) / 2)
            (((n - 1 : ℕ) : ℝ) / 2)
            (_root_.GD.N0107.d009046 m n σ τ) *
          _root_.GD.N0232.N0720.d014160 Ucert)
    ∧
    _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n μ σ τ)
          (fun ω =>
            _root_.GD.N0107.d012734
                m n (Ucert.step : ℝ) (_root_.GD.N0232.N0720.d014159 Ucert) ω - μ)
      <
        _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n μ σ τ)
          (fun ω =>
            _root_.GD.N0107.d012733 m n ω - μ) :=
  by
    simpa only [_root_.GD.N0232.N0720.d014159, _root_.GD.N0232.N0720.d014160] using
      (_root_.GD.N0117.d014156
        Ucert μ σ τ hσ hτ)




theorem d014167
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ Ucert : _root_.GD.N0232.N0720.d014158 m n hm hn,
      0 < Ucert.step
      ∧ 0 < _root_.GD.N0232.N0720.d014160 Ucert
      ∧ ∀ (μ σ τ : ℝ), 0 < σ → 0 < τ →
        _root_.GD.N0141.d006684
              (_root_.GD.N0107.d009030 m n μ σ τ)
              (fun ω =>
                _root_.GD.N0107.d012734
                    m n (Ucert.step : ℝ)
                    (_root_.GD.N0232.N0720.d014159 Ucert) ω - μ)
            -
            _root_.GD.N0141.d006684
              (_root_.GD.N0107.d009030 m n μ σ τ)
              (fun ω =>
                _root_.GD.N0107.d012733 m n ω - μ)
          ≤
            -(_root_.GD.N0107.d009045 m n σ τ *
              _root_.GD.N0120.d008813
                (((m - 1 : ℕ) : ℝ) / 2)
                (((n - 1 : ℕ) : ℝ) / 2)
                (_root_.GD.N0107.d009046 m n σ τ) *
              _root_.GD.N0232.N0720.d014160 Ucert)
        ∧
        _root_.GD.N0141.d006684
              (_root_.GD.N0107.d009030 m n μ σ τ)
              (fun ω =>
                _root_.GD.N0107.d012734
                    m n (Ucert.step : ℝ)
                    (_root_.GD.N0232.N0720.d014159 Ucert) ω - μ)
          <
            _root_.GD.N0141.d006684
              (_root_.GD.N0107.d009030 m n μ σ τ)
              (fun ω =>
                _root_.GD.N0107.d012733 m n ω - μ) :=
  by
    simpa only [_root_.GD.N0232.N0720.d014159, _root_.GD.N0232.N0720.d014160] using
      (_root_.GD.N0117.d014157
        m n hm hn)

end

end GD.N0232.N0720
