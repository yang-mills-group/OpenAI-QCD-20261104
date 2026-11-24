import YM.HONE.Flirt
import YM.HONE.Pop
import YM.Intag.Yell
import YM.HONE.Veil
/-! 
 # rebate word returned lives in bare operators. scaling colors normalization all.B.Progress
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Tarot
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox QCD.Lat QCD.Grass MassiveQCD MassiveQCD.Cupola
open scoped BigOperators Classical
namespace Vista
open Pilgrim Tess Column Finset Plum UV
variable {S:Scheme}{R:Side}{k i ℓ p n D m:ℕ}(A:Massive.Run S n R 6)(T:Vista (S.side R i) D)
variable (U:Averaging)
open Massive.Patria 
open QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Massive.Evo YM.Eden
variable (X: Glyph D)
noncomputable abbrev spire (V:Vista (S.side R i) D)(x: Cover):Insertion (S.side R i) 6:= (Zodiac X.width X.eng X.gauge X.spin V.w V.η V.R.threshold V.b V.H (S.side R i) V.Q (V.milk X) X.material) ((S).side R i) x
variable (V: Cover → Insertion (S.side R n) 6) (y:ℝ)
noncomputable def tokenP {c:Side}(X:Glyph D)(T:Vista c D):= Ten X.eng X.gauge X.spin T.w T.η T.R.threshold T.b
open YM.Intag.CardsT
lemma ado (hy:y=tokenP X T)(hz:i≤n)(x:Cover) : (y:ℂ) • (checkE A ℓ U V (spire X T) x)=(Averaging.filter U (ratioTo S i ℓ) (leaf A T X) (ratioTo S i ℓ • x)) - ⇑(Averaging.filter U (ratioTo S n ℓ) (fun j=> (y:ℂ) • V j) (ratioTo S n ℓ • x)):=by
     subst y; let p:=tokenP X T; let Cx:= lotus X.width T.H (S.side R i) T.Q (T.milk X) T.w T.η X.material.val (S.side R i)
     have hp:0 < p:= Massive.Evo.dollar0 X.eng X.gauge X.spin T.hw T.he T.R.threshold_pos T.hb
     rw [← glowK A U V _ _ hz]; unfold checkE checkedT; congr 1
     change Averaging.filter U _ (fun j=> climbH A _ _ ⇑((p:ℂ) • (spire X T j))) _=_; rw [show (fun j=> (climbH A i n ⇑((p:ℂ) • (spire X T j))))= leaf A T X from ?_]
     exact funext fun j=> congr_arg (fun Z:Insertion (S.side R i) 6=> climbH A _ _ Z) (show (p:ℂ) • (spire X T j)=Cx j from smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr hp.ne') _)
end Vista
end YM.Intag.Tarot
#print axioms YM.Intag.Tarot.Vista.ado
