import YM.Parishes.BudgetH
import YM.Oars.Mother
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j kP k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j kP}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open MassiveQCD.Lyre MassiveQCD.Plate MassiveQCD.Lyre.Drawing Massive.Poised.Plans Massive.Poised.Pipes
namespace Bank.Hike
open QCD.Kites QCD.Kit MassiveQCD.Twist
open Massive.Poised Massive.Poised.Stative Massive.Poised.TrainG Massive.Poised.Plans.Stamp
local notation "αI"=> (1/16:ℝ)
local notation "αL"=> (3/16+1:ℝ)
local notation "μ⁰"=> (1/8:ℝ)
-- role contracts pre and post.Fill together. output Price only charged vs from-board G.GR.
variable {i0 kq Gn Dx nL r:ℕ}{pre αp βp χp Gv εd ξ ε:ℝ}
local notation "d0"=> Kit.slope L
local notation "xg"=>run L x
local notation "Ωv"=>preS pre βp
local notation "outX"=> supportC pre βp αp
-- loan heights. specify ∀ We/Toted weighted.Jump.
namespace Ivy
open MassiveQCD.Sample MassiveQCD.Sample.Sail
local notation "Pu"=> spareCut
-- receipt.E payout for differences along a stencil.Any ξ.L.Arg scale.D
structure Silo (L:Side)(Q i Gn n k R' E D:ℕ)(θ pre B A ε x:ℝ): Prop where
    enjoys : let z:=run L x; let u:=Kit.slope L; let w:=Sail.roomAt L θ z; 0<w ∧ (Real.exp ((1/8:ℝ)*81)*B)*w+w ≤ spareCut (Jets.Touch.chip L z) ∧ w≤ spareCut 1 ∧
       let A':= preS pre B; let v:= ArchC L θ Q i k n E D z
       (∀ y:ℝ, y≤w→ ∀ q:ℝ,q≤w→let X':= A'*y + ((u^(Gn+1)*pre)*q+ v); FeeE i k n z * King.flowM L z+B*(A*X')≤1) ∧ ArchC L θ Q i k n E D z ≤ (u^(Gn+1))*w ∧ tax_save L x ≤(u^(Gn+1))*w∧
       (max ((Fintype.card (Rings Gn):ℝ)*(2*relief L z)) (FeeH L L Gn A pre z))*w+ A*v ≤ ε*u^(Gn+1)*w ∧ 2*relief L z* B ≤ ε*u^(Gn+1)
-- eventual version.
variable (L:Side)(i0 Q Gn n kq r Dx nL:ℕ)(θ pre B A εd:ℝ)(hθ:0<θ)(hP:1 ≤ pre)(hB:1 ≤ B)(hA:1 ≤ A)(he:0< εd)
include hθ hP hB hA he
lemma tidies :∀ᶠ x in atTop, Silo L Q i0 Gn n kq r Dx nL θ pre B A εd x:=by
   let u:= Kit.slope L; let t:= u^(Gn+1); have hf:0<t:=pow_pos (Kit.slope_pos _) _
   have hΨ:Tendsto (run L) atTop atTop:=YM.Work.E09.betaF_growth su L; have hp : 0<B:= zero_lt_one.trans_le hB; have ha : 0<A:= zero_lt_one.trans_le hA; have hg : 0<pre:= zero_lt_one.trans_le hP
   let w:= Sail.roomAt L θ; let V(x):=FeeE i0 kq n x * King.flowM L x; let C:= preS pre B; have hu: 0<C:=by unfold C preS; positivity
   let D:= (Fintype.card (Rings Gn):ℝ); have hV:Rate su L (- (3/10)) V:=by simpa only [zero_add] using (((Reel.for_voices L 2 μ⁰).mul_left (Girdle.tariff i0 2 kq n)).mul (show Rate su L (-(3/10)) (King.flowM L) from Rate.power))
   have hW : Rate su L (-1) w:= Sail.slotR L θ
   let χ:= εd*t/2; have hΧ:0<χ:=by unfold χ; positivity
   have hDd: ∀ᶠ x:ℝ in atTop, FeeH L L Gn A pre x≤χ:=by
       let K:= A*(Kit.slope L^(Gn+1)*pre); exact (((Real.tendsto_exp_atBot.comp ((pulse_growthD L).const_mul_atTop_of_neg (show αI-μ⁰<0 by norm_num))).mul_const K).eventually_le_const (show (0:ℝ)*K<χ from zero_mul K|>.symm ▸ hΧ))
   have hS: Jets.Touch.Seat L ((-1)/3) (fun x :ℝ=>D*(2*relief L x)):= Seat.timesL (Seat.timesL Seat.keeps _) _ -- syntactic
   have hC: Jets.Touch.Seat L ((-1)/3) (fun x:ℝ=>2*relief L x*B):= Seat.times (Seat.timesL Seat.keeps _) _
   let S:= B*A*(C+t*pre+t); have hN:0<S:=by unfold S; positivity
   have hE :0 < spareCut 1:=by unfold spareCut; rw [mul_one,sub_pos]; exact Real.exp_lt_one_iff.mpr (by norm_num)
   have hp1: ∀ᶠ x:ℝ in atTop,(Real.exp ((1/8:ℝ)*81)*B)*w x+w x ≤ spareCut (Jets.Touch.chip L x):=by
       let G:=Real.exp ((1/8:ℝ)*81)*B+1
       let F:=fan L (-θ/16); have hQ: Jets.Touch.Seat L (-θ/16) (fun x=>G*F x):=Jets.Touch.Seat.keeps.timesL (L:=L) _ -- syntax?
       filter_upwards [hQ.shrinks (by linarith) hE,event_chip L 1] with x hx hz; let V:= Jets.Touch.chip L x;
       have h: G * F x * V ≤ spareCut 1 * V:= mul_le_mul_of_nonneg_right ((le_abs_self _).trans hx) hz.2.1.le; unfold w roomAt spareCut G at *; unfold F V at h; linarith only [h]
   have ht : ∀ᶠ x in atTop, tax_save L x ≤ t*w (run L x):=by
       let Q:=Hike.tax_save L; have hW: Rate su L (-2) Q:= Touch.couplings L (by norm_num : 0<(1/2:ℝ)); filter_upwards [((hW.mul (Sail.inverseSlot L θ)).below (by norm_num) (t/4) (by positivity)),Sail.shuttle L θ] with x hk hG'; have hb : Q x / w x ≤ t/4:=by rw [div_eq_mul_inv]; exact (le_abs_self _).trans hk
       exact ((div_le_iff₀ hG'.1).1 hb).trans ((mul_le_mul_of_nonneg_left hG'.2.1 (by positivity:0≤ t/4)).trans_eq (by unfold w; ring))
   filter_upwards [hΨ.eventually ((Sail.reliefStage L θ Q i0 kq n Dx nL _ hf hθ)), hΨ.eventually (Sail.reliefStage L θ Q i0 kq n Dx nL (χ/A) (by positivity) hθ),hΨ.eventually (Sail.shuttle L θ), hΨ.eventually hp1,hΨ.eventually (hW.below (by norm_num) _ hE),ht,hΨ.eventually ((hW.mul_left S).below (by norm_num) (1/2) (by norm_num)), hΨ.eventually (hV.below (by norm_num) (1/2) (by norm_num)),hΨ.eventually (hS.shrinks (by norm_num) hΧ),hΨ.eventually hDd, hΨ.eventually (hC.shrinks (by norm_num) (mul_pos he hf))] with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
   let z:= run L x; let w' := w z; have hw :0 < w':=h3.1
   refine ⟨hw,h4,(le_abs_self _).trans h5,fun y hy q h=>?_,h1,h6,?_, (le_abs_self _).trans h11⟩ -- using let fields.Et. maybe struct braces.
   · intro X'; have h : X' ≤ (C+t*pre+t)*w' :=by
          unfold X'; apply (add_le_add (mul_le_mul_of_nonneg_left hy hu.le) (add_le_add (mul_le_mul_of_nonneg_left h (mul_pos hf hg).le) h1)).trans_eq; ring
     apply (add_le_add_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h ha.le) hp.le) _).trans; have hV: S*w' ≤1/2:= (le_abs_self _).trans h7; have hX: V z≤1/2:=(le_abs_self _).trans h8; unfold S at hV; unfold V z at hX
     nlinarith only [hV,hX]
   apply (add_le_add (mul_le_mul_of_nonneg_right (max_le ((le_abs_self _).trans h9) h10) hw.le) (mul_le_mul_of_nonneg_left h2 ha.le)).trans_eq; field_simp; unfold χ t; ring -- type ring mixed L1
end Ivy
end Bank.Hike
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Bank.Hike.Ivy.tidies
