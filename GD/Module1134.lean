import GD.Module0993
import GD.Module0990
import GD.Module1133
import GD.Module0037
import GD.Module0991









namespace GD.N0232.N0720.N1302

noncomputable section

open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1083
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1346
open _root_.GD.N0232.N0720.N1407
open _root_.GD.N0232.N0720.N1416
open _root_.GD.N0232.N0720.N1464
open _root_.GD.N0232.N0720.N1465
open _root_.GD.N0232.N0720.N1466



noncomputable def d018241 : ℝ :=
  _root_.GD.N0232.N0720.N1465.d015694
    (_root_.GD.N0232.N0720.N1466.d015735 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756)



noncomputable abbrev d018242 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  _root_.GD.N0232.N0720.N1082.d015387 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1416.d017756 _root_.GD.N0232.N0720.N1302.d018241

theorem d018243 :
    (5 / 4 : ℝ) < _root_.GD.N0232.N0720.N1302.d018241 := by
  exact _root_.GD.N0232.N0720.N1465.d015695
    (_root_.GD.N0232.N0720.N1466.d015737 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756)



theorem d018244 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018242 _root_.GD.N0232.N0720.N1416.d017758 := by
  apply _root_.GD.N0232.N0720.N1465.d015697
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756
  · exact _root_.GD.N0232.N0720.N1466.d015736 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756
  · exact _root_.GD.N0232.N0720.N1466.d015737 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756
  · intro theta
    exact _root_.GD.N0232.N0720.N1464.d015739
      2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756
      theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos




noncomputable def d018245 : ℝ :=
  _root_.GD.N0232.N0720.N1465.d015700
    (_root_.GD.N0232.N0720.N1466.d015735 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756)


noncomputable abbrev d018246 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  _root_.GD.N0232.N0720.N1082.d015387 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1416.d017756 _root_.GD.N0232.N0720.N1302.d018245

theorem d018247 :
    _root_.GD.N0232.N0720.N1302.d018241 < _root_.GD.N0232.N0720.N1302.d018245 := by
  exact _root_.GD.N0232.N0720.N1465.d015702
    (_root_.GD.N0232.N0720.N1466.d015737 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756)



theorem d018248 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018246 _root_.GD.N0232.N0720.N1302.d018242 := by
  apply _root_.GD.N0232.N0720.N1465.d015708
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756
  · exact _root_.GD.N0232.N0720.N1466.d015736 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756
  · exact _root_.GD.N0232.N0720.N1466.d015737 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756
  · intro theta
    exact _root_.GD.N0232.N0720.N1464.d015739
      2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756
      theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos


theorem d018249 :
    ¬ _root_.GD.N0232.N0720.N1036.d014669 2 2 _root_.GD.N0232.N0720.N1302.d018242 := by
  exact _root_.GD.N0232.N0720.N1407.d018235
    2 2 _root_.GD.N0232.N0720.N1302.d018242 _root_.GD.N0232.N0720.N1302.d018246
      _root_.GD.N0232.N0720.N1302.d018248




noncomputable def d018250 : ℝ :=
  _root_.GD.N0232.N0720.N1465.d015701
    (_root_.GD.N0232.N0720.N1466.d015735 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756)

noncomputable abbrev d018251 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  _root_.GD.N0232.N0720.N1082.d015387 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1416.d017756 _root_.GD.N0232.N0720.N1302.d018250

theorem d018252 :
    _root_.GD.N0232.N0720.N1302.d018245 < _root_.GD.N0232.N0720.N1302.d018250 := by
  exact _root_.GD.N0232.N0720.N1465.d015703
    (_root_.GD.N0232.N0720.N1466.d015737 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756)



theorem d018253 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018251 _root_.GD.N0232.N0720.N1302.d018242 := by
  apply _root_.GD.N0232.N0720.N1465.d015709
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756
  · exact _root_.GD.N0232.N0720.N1466.d015736 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756
  · exact _root_.GD.N0232.N0720.N1466.d015737 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1416.d017756
  · intro theta
    exact _root_.GD.N0232.N0720.N1464.d015739
      2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756
      theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos



theorem d018254 :
    ¬ _root_.GD.N0232.N0720.N1036.d014669 2 2 _root_.GD.N0232.N0720.N1416.d017758 := by
  exact _root_.GD.N0232.N0720.N1407.d018235
    2 2 _root_.GD.N0232.N0720.N1416.d017758 _root_.GD.N0232.N0720.N1302.d018242
      _root_.GD.N0232.N0720.N1302.d018244




theorem d018255 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018242
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) := by
  intro theta
  exact
    (_root_.GD.N0232.N0720.N1302.d018244 theta).trans
      (_root_.GD.N0232.N0720.N1407.d018239 theta)


noncomputable def d018256 : _root_.GD.N0232.N0720.N1159.d014639 2 2 :=
  _root_.GD.N0232.N0720.N1159.d014657 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1302.d018242
    (_root_.GD.N0232.N0720.N1082.d015396
      2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756
        _root_.GD.N0232.N0720.N1302.d018241)
    _root_.GD.N0232.N0720.N1302.d018255

@[simp] theorem d018257 :
    _root_.GD.N0232.N0720.N1302.d018256.value = _root_.GD.N0232.N0720.N1302.d018242 := by
  rfl



theorem d018258
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 2 2
      _root_.GD.N0232.N0720.N1302.d018242) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  apply _root_.GD.N0232.N0720.N1346.d018226
    _root_.GD.N0232.N0720.N1302.d018256
  · simpa only [_root_.GD.N0232.N0720.N1302.d018257] using
      _root_.GD.N0232.N0720.N1302.d018255
  · simpa only [_root_.GD.N0232.N0720.N1302.d018257] using hterminal





theorem d018259 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018251
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) := by
  intro theta
  exact
    (_root_.GD.N0232.N0720.N1302.d018253 theta).trans
      (_root_.GD.N0232.N0720.N1302.d018255 theta)

noncomputable def d018260 : _root_.GD.N0232.N0720.N1159.d014639 2 2 :=
  _root_.GD.N0232.N0720.N1159.d014657 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1302.d018251
    (_root_.GD.N0232.N0720.N1082.d015396
      2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756
        _root_.GD.N0232.N0720.N1302.d018250)
    _root_.GD.N0232.N0720.N1302.d018259

@[simp] theorem d018261 :
    _root_.GD.N0232.N0720.N1302.d018260.value = _root_.GD.N0232.N0720.N1302.d018251 := by
  rfl



theorem d018262
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 2 2
      _root_.GD.N0232.N0720.N1302.d018251) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  apply _root_.GD.N0232.N0720.N1346.d018226
    _root_.GD.N0232.N0720.N1302.d018260
  · simpa only [_root_.GD.N0232.N0720.N1302.d018261] using
      _root_.GD.N0232.N0720.N1302.d018259
  · simpa only [_root_.GD.N0232.N0720.N1302.d018261] using hterminal









noncomputable def d018263 : ℝ :=
  _root_.GD.N0232.N0720.N1083.d015723 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1416.d017756

noncomputable abbrev d018264 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  _root_.GD.N0232.N0720.N1082.d015387 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1416.d017756 _root_.GD.N0232.N0720.N1302.d018263

theorem d018265 : 0 < _root_.GD.N0232.N0720.N1302.d018263 := by
  exact _root_.GD.N0232.N0720.N1083.d015726
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756

theorem d018266 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018264
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) := by
  exact _root_.GD.N0232.N0720.N1083.d015730
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756



theorem d018267
    {b : ℝ} (hb : _root_.GD.N0232.N0720.N1302.d018263 < b) :
    ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      (_root_.GD.N0232.N0720.N1082.d015387 2 2 (by norm_num) (by norm_num)
        _root_.GD.N0232.N0720.N1416.d017756 b)
      _root_.GD.N0232.N0720.N1302.d018264 := by
  exact _root_.GD.N0232.N0720.N1083.d015731
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756 hb

noncomputable def d018268 : _root_.GD.N0232.N0720.N1159.d014639 2 2 :=
  _root_.GD.N0232.N0720.N1159.d014657 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1302.d018264
    (_root_.GD.N0232.N0720.N1082.d015396
      2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1416.d017756
        _root_.GD.N0232.N0720.N1302.d018263)
    _root_.GD.N0232.N0720.N1302.d018266

@[simp] theorem d018269 :
    _root_.GD.N0232.N0720.N1302.d018268.value = _root_.GD.N0232.N0720.N1302.d018264 := by
  rfl



theorem d018270
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 2 2
      _root_.GD.N0232.N0720.N1302.d018264) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  apply _root_.GD.N0232.N0720.N1346.d018226
    _root_.GD.N0232.N0720.N1302.d018268
  · simpa only [_root_.GD.N0232.N0720.N1302.d018269] using
      _root_.GD.N0232.N0720.N1302.d018266
  · simpa only [_root_.GD.N0232.N0720.N1302.d018269] using hterminal

end

end GD.N0232.N0720.N1302

#print axioms _root_.GD.N0232.N0720.N1302.d018243
#print axioms _root_.GD.N0232.N0720.N1302.d018244
#print axioms _root_.GD.N0232.N0720.N1302.d018254
#print axioms _root_.GD.N0232.N0720.N1302.d018258
#print axioms _root_.GD.N0232.N0720.N1302.d018248
#print axioms _root_.GD.N0232.N0720.N1302.d018249
#print axioms _root_.GD.N0232.N0720.N1302.d018253
#print axioms _root_.GD.N0232.N0720.N1302.d018262
#print axioms _root_.GD.N0232.N0720.N1302.d018267
#print axioms _root_.GD.N0232.N0720.N1302.d018270
