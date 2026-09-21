import GD.Module0721


















open Set

namespace GD.N0232.N0719.N1024

noncomputable section



theorem d010804
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scales < 0 :=
  (_root_.GD.N0232.N0719.N0912.d010782
    hk sizes hsizes scales hscales).1





theorem d010805
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.N1024.d010718 k sizes hk scales ≤
      _root_.GD.N0232.N0719.N0950.d010597 (by omega)
        (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0232.N0719.N1024.d010710 hk) := by
  have hresult :=
    _root_.GD.N0232.N0719.N0912.d010782
      hk sizes hsizes scales hscales
  have hden : 0 < -_root_.GD.N0232.N0719.N1024.d010712 k sizes hk scales :=
    neg_pos.mpr hresult.1
  unfold _root_.GD.N0232.N0719.N1024.d010718
  exact (div_le_iff₀ hden).2 hresult.2








theorem d010806
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i) :
    BddAbove (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk) := by
  refine
    ⟨_root_.GD.N0232.N0719.N0950.d010597 (by omega)
        (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0232.N0719.N1024.d010710 hk), ?_⟩
  intro x hx
  rcases hx with ⟨scales, hscales, rfl⟩
  exact _root_.GD.N0232.N0719.N1024.d010805
    hk sizes hsizes scales hscales






theorem d010807
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scales) -
        ∫ ω,
          (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
            ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scales <
      _root_.GD.N0232.N0719.N1024.d010727 k sizes hk * _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scales := by
  exact
    _root_.GD.N0232.N0719.N1024.d010739
      k sizes hk hsizes location scales hscales
      (_root_.GD.N0232.N0719.N1024.d010806 hk sizes hsizes)
      (_root_.GD.N0232.N0719.N1024.d010804 hk sizes hsizes scales hscales)
      (_root_.GD.N0232.N0719.N1024.d010735
        k sizes hk hsizes location scales hscales)
      (_root_.GD.N0232.N0719.N1024.d010736
        k sizes hk hsizes location scales hscales)
      (_root_.GD.N0232.N0719.N1024.d010737
        k sizes hk hsizes location scales hscales)









theorem d010808
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scales) <
      ∫ ω,
        (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scales := by
  exact
    _root_.GD.N0232.N0719.N1024.d010741
      k sizes hk hsizes location scales hscales
      (_root_.GD.N0232.N0719.N1024.d010806 hk sizes hsizes)
      (_root_.GD.N0232.N0719.N1024.d010804 hk sizes hsizes scales hscales)

end

end GD.N0232.N0719.N1024
