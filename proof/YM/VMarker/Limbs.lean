import YM.MassiveQCD.Plate.Lotion
import YM.VMarker.Shields
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)(Y: Ruby.Hue c N J)(F: Patron.Rail c (ample N I) U)
local notation "M"=> Ribbon.ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "b'"=>banknote N p φ
local notation "d!"=> withdraw N p θ
local notation "F!"=> pursue N p θ F φ r
local notation "Y!"=> radial I Y
local notation "K!"=> limb N p θ φ r Y F
namespace Wage
set_option quotPrecheck false
open QCD.Villa QCD.Leaf QCD.Loom QCD.Loom.Fleet QCD.Stew QCD.High QCD.Acre QCD.Meridians QCD.Kites
local notation "bz"=> O.threshold
open QCD.Leaf QCD.Jets
lemma engine₁ {A:Type}[Fintype A](x:Grass.Alg A):engine 1 A x=x:=by
    apply Stew.poster; intro; rw [fundW]; simp
lemma wear₁ (x:EvenA c N):wearK c N 1 x=x:= Subtype.ext (engine₁ x.val)
lemma once {D:Type} (X:Patron.Rail c N D): flightK X 1=X:=by cases X; unfold flightK; congr! 2; first | exact funext (fun U=> wear₁ N _) | exact wear₁ N _
lemma turn₁ (x:Patio (Keys c N⊕Spine I)): Plate.turn I 1 x=x:=by apply pluckVisible; intro j; rw [turned,engine₁] -- scopeD
open QCD.Kites Coda QCD.Finch
variable {C' W V:Type}{x z ν β ε:ℝ}
open Sway
-- through fields at chosen horizon threshold with witnesses
structure Tip (X:Patron.Rail c (ample N I) U)(P:BudgetPoint)(t η w:ℝ):Prop where
   tilt:Pill X P.threshold t P.B η w
   fits:∀ i V,Well N p t q (X.warp i V)
lemma travel (H:Tip N p q F O φ v w)(hY: Wax Y O.threshold O.B a A θ)(hP:∀ i,shadeG (Y.mean i))(h:0<r)(hr:r*θ ≤ φ)(hs:StackK O.B w z v β a A)(hz:1 ≤θ) : Tip N p q (limb N p θ φ r Y F O.threshold) O θ β z:=by
    let Z:= pursue N p θ F φ r; let W:= radial I Y; have hv :0<θ:=zero_lt_one.trans_le hz
    exact ⟨lowerPill N p q θ φ r Y F H.tilt hY hP h hz hr H.fits (hs c M J U W Z O.threshold θ (WaxGov (I:=I) θ Y hY|>.expense) (portage N p θ q F φ r w H.tilt h hv hr H.fits|>.sold)),fun i V=> engraved N p q θ φ r Y F hz H.fits V i⟩
variable (X:Ruby.Hue c N C')(Z:Ruby.Hue c N W) (G: Patron.Rail c N V)
variable (O)
-- prepare using Switch. track precisely θ/phase
open QCD.Jets.Touch
local notation "St"=>speedP L t x
local notation "Ft"=>fan L t x
local notation "gn"=> Kites.run L x -- verify
variable (hX: Switch (N:=N) O L x t φ ε A)
noncomputable abbrev triT (f b:ℝ) (t:ℝ) := limb N p f f 1 Z (limb N p f b r X (limb N p b φ 1 Y F t) t) t
local notation "Lg"=> limb N p (speedP L t x) φ 1 Y F O.threshold
local notation "Xg"=> limb N p (fan L t x) (speedP L t x) r X (Lg) O.threshold
local notation "Zg"=> limb N p (fan L t x) (fan L t x) 1 Z (Xg) O.threshold
open ConnectedActivityE6 QCD.Kites
local notation "pr"=> pra L (run L x)
variable (hY: Purchases Y O.threshold O.B (1+1+1) (pra L (run L x)) (speedP L t x))(h₁:Purchases X O.threshold O.B (1/8+1/8+1) 1 (fan L t x))(h₂:Wax Z O.threshold O.B (7*(1/32)+1) 1 (fan L t x)) (h₃:∀ i,shadeG (Z.mean i))
variable (hβ:Tip N p q F O φ (1+1) (priceK L ε (run L x)))(hk:1 ≤ priceK L ε (run L x))(hr:0 < r)(hv:r ≤ 2)
open Sway
local notation "f!"=>faultK N p φ F
local notation "Z!"=> Trail Z (Trail X (flightK (Trail Y (faultK N p φ F) O.threshold) r) O.threshold) O.threshold
local notation "β!"=> (turn I (D:=K) r).comp (withdraw N p φ)
local notation "Ro" => rootR R K
variable (hZ:Correspond (Ruby.Trail Z (Ruby.Trail X (flightK (Ruby.Trail Y (faultK N p φ F) O.threshold) r) O.threshold) O.threshold) G)
include hX
lemma carryFault : (Acre.Rails.Links.toEnv (faultK N p Ft Zg))= Acre.Rails.Links.toEnv (Z!):=by
     have hS := hX.count; have hF :1 ≤ St:=by unfold speedP; linarith
     -- eq as sigma.Environment.
     rw [pair_c N p Ft Ft 1 Z Xg hS]; let A:= Trail Z (flightK (faultK N p Ft Xg) 1) O.threshold
     let B:= Trail X (flightK (faultK N p St Lg) r) O.threshold
     change Acre.Rails.Links.toEnv (A)=_
     unfold A; rw [pair_c N p St Ft r X Lg hS,once]
     let C:= Trail Y (flightK (f!) 1) O.threshold
     have ht: Rails.Links.toEnv (faultK N p St Lg)= Rails.Links.toEnv (Trail Y (f!) O.threshold):=by rw [pair_c N p φ St 1 Y F hF]; change Rails.Links.toEnv C=_; unfold C; rw [once]
     exact Rails.Links.env_trail _ _ _ _ (Rails.Links.env_trail _ _ _ _ (Rails.Links.env_wears r _ _ ht))
include hZ
lemma carryFunds : Correspond (faultK N p Ft Zg) G:=Conductor.Tandem.payment _ _ _ (carryFault N O p φ r Y F X Z hX).symm hZ
omit hZ
open QCD.Acre QCD.Jets.Touch
include hY h₁ h₂ hβ hk hr hv h₃
lemma growthV [Countable J] [Countable U] : Tip N p q (Zg) O Ft (3/16) (taxK L x 4)∧∀ V:Grid c, withdraw N p Ft (heartK Zg O.threshold V)= (β!) (heartK F O.threshold V) *Ro ((wearK c N r (exp (swarm Y V))*exp (swarm X V))*exp (swarm Z V)):=by
    have hz:= hX.count; have hF:0 < Ft:=zero_lt_one.trans_le hz; have hS:1 ≤ St:=by unfold speedP; linarith; -- trailing
    have hφ: 1*St≤ φ:= (one_mul _).le.trans hX.steer; have hr':r*Ft ≤ St:= mul_le_mul_of_nonneg_right hv hF.le
    have he: Wax Y O.threshold O.B (1+1+1) pr St:=⟨hY.life,cashSoft _ hY⟩; have he': Wax X O.threshold O.B (1/8+1/8+1) 1 Ft:=⟨h₁.life,cashSoft _ h₁⟩
    have hu:= travel N p q St φ 1 Y F hβ he hY.projection.gauge zero_lt_one hφ hX.path hS
    have hQ :Countable (Plot (radial I Y) (pursue N p St F φ 1)):= QCD.Acre.Rails.glazeP .. -- fix
    have hL: Tip N p q Lg O St (1/8+1/8) (taxK L x 8):=⟨⟨hu.tilt.uses,hu.tilt.pigment,Kites.tide (p:=O) Lg (liveK Lg hu.tilt.sold (by norm_num) (zero_lt_one.trans_le hS) le_rfl) (Real.exp_pos _).le hX.blaze⟩,hu.fits⟩
    have ht':= travel N p q Ft St r X Lg hL he' h₁.projection.gauge hr hr' hX.pool hz
    have hp' : 1*Ft≤ Ft:=by rw [one_mul]
    have hw(k:ℝ)(h:0 ≤ k):1 ≤ taxK L x k:=Real.one_le_exp (mul_nonneg h (fan_pos ..).le)
    refine ⟨travel N p q Ft Ft 1 Z Xg ht' h₂ h₃ zero_lt_one hp' hX.quilt hz, fun U'=>?_⟩
    have ha := warmed N p q Ft Ft 1 Z Xg U' ht'.tilt h₂ zero_lt_one hz hz hp' (hw 6 (by norm_num)) (by norm_num) (by norm_num) ht'.fits
    have hb := warmed N p q St Ft r X Lg U' hL.tilt he' hr hz hS hr' (hw 8 (by norm_num)) (by norm_num) (by norm_num) hL.fits
    have hc := warmed N p q φ St 1 Y F U' hβ.tilt he zero_lt_one hS (hS.trans hX.steer) hφ hk (by norm_num) (by norm_num) hβ.fits
    simp_rw [AlgHom.comp_apply,turn₁] at ha hc; rw [AlgHom.comp_apply] at hb
    rw [ha,hb,hc,map_mul (Plate.turn I r),map_exp (Plate.turn I r) ((Plate.turn I (D:=K) r).toLinearMap.toContinuousLinearMap.continuous),rollRoot]
    simp only [map_mul Ro,map_exp Ro (Ro).toLinearMap.toContinuousLinearMap.continuous, map_exp (wearK c N r) (Loom.Fleet.songT (c:=c) (N:=N) r).continuous,AlgHom.comp_apply]; ring
end Wage
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Wage.growthV
