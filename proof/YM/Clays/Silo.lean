import YM.Differ.Baboon
import YM.QCD.Hearth.Focus
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
local notation "α0"=> (24/256:ℝ)
noncomputable def extraE (L: Side)(A pre:ℝ)(Gn:ℕ)(x:ℝ):ℝ:= Real.exp ((αI-α0)*highR L x)*(A*(Kit.slope L^(Gn+1)*pre))
structure CareL (L:Side)(Q i0 Gn n k R' E D:ℕ)(θ pre B A ε x:ℝ): Prop where
      knows : Silo L Q i0 Gn n k R' E D θ pre B A ε x
      gives : let z:=run L x; let u:=Kit.slope L; let w:= Sail.roomAt L θ z; let v:= ArchC L θ Q i0 k n E D z; (max ((Fintype.card (Rings Gn):ℝ)*(2*relief L z)) (extraE L A pre Gn z))*w+A*v ≤ ε*u^(Gn+1)*w ∧ v ≤ ε*u^(Gn+1)*w
noncomputable def crawl (L: Side)(η:ℕ)(x:ℝ):ℝ:= 1/(1+(highR L x:ℝ))^η
variable (L:Side)(i0 Q Gn n kq r Dx nL:ℕ)(θ pre B A:ℝ)(E:ℕ) (hθ:0<θ)(hP:1 ≤ pre)(hB:1 ≤ B)(hA:1 ≤ A)
include hθ hP hB hA
-- can apply to future clocks post-L.V runtime. gamma term exact at run L x (NO bounds monotone promise for startX.B use earlier feasibility). includes Clays* bound. supply at same release.W.
set_option maxHeartbeats 630000 in
lemma scrutiny : ∀ᶠ x in atTop,CareL L Q i0 Gn n kq r Dx nL θ pre B A (crawl L E (run L x)) x:=by
      let v (x:ℝ):=1+(highR L x:ℝ); let w:=roomAt L θ; let z x:= (v x)^E; let k:=(Fintype.card (Rings Gn):ℝ)
      let u:=(Kit.slope L)^(Gn+1); have hu:0 < u:=pow_pos (Kit.slope_pos _) _; have ha:0<A:=zero_lt_one.trans_le hA
      have hz: Jets.Touch.Seat L 0 z:=by
          have hp:Seat L 0 (fun x=> (highR L x:ℝ)):=by
                intro b hb; filter_upwards [Delay.monitor_pays su L 1 (D:=1) zero_le_one hb] with x hx; refine le_trans ?_ hx; unfold highR radiusB Delay.bill; rw [abs_of_nonneg (by positivity),one_mul,pow_one]; have h:= Nat.ceil_lt_add_one (sq_nonneg (Real.log (betaF su x L))); linarith only [h, Nat.cast_nonneg (α:=ℝ) (Nat.ceil (Real.log x ^ 2))]
          exact ((Seat.comb (Seat.numbers 1) hp).powered E).above (by simp)
      have hS: Jets.Touch.Seat L ((-1)/3) (fun x :ℝ=>k*(2*relief L x)):= Seat.timesL (Seat.timesL Seat.keeps _) _ -- syntactic
      have hC: Jets.Touch.Seat L ((-1)/3) (fun x:ℝ=>2*relief L x*B):= Seat.times (Seat.timesL Seat.keeps _) _
      let X:= ArchC L θ Q i0 kq n Dx nL; have hE': Rate su L (-1) (extraE L A pre Gn):=by
           have hα:αI-α0= -(1/32:ℝ):=by norm_num
           unfold extraE; rw [hα]; exact (Hearth.paysA (-1) (by norm_num : (0:ℝ)<1/32) L).mul_right _
      let v0:=fan L (-θ/16); let f (x:ℝ):= X x*(Jets.Touch.chip L x)⁻¹; let g:=crawl L E; have hk : ∀ x, 0<g x:=fun i=>by unfold g crawl; positivity
      have hi(i):0< z i:=by unfold z v; positivity
      have hg(i):g i*z i=1:=div_mul_cancel₀ _ (hi _|>.ne')
      have hp := prepSignal L Q i0 kq n Dx nL θ
      have hT: Tendsto (run L) atTop atTop:=Work.E09.betaF_growth su L
      filter_upwards [tidies L i0 Q Gn n kq r Dx nL θ pre B A 1 hθ hP hB hA zero_lt_one, hT.eventually ((hz.ponies hS).shrinks (by norm_num) (half_pos hu)), hT.eventually ((hz.ponies hC).shrinks (by norm_num) hu), hT.eventually ((hE'.mul hz.ruled).below (by norm_num) (u/2) (half_pos hu)),hT.eventually ((hz.ponies (hp.ponies (skin_i L (-θ/16)))).shrinks (by linarith only [hθ]) (show 0 < u/(2*A) from by positivity)),hT.eventually (event_chip L 0)] with x hx h1 h2 h3 h4 h5
      let x':=run L x; let E':= extraE L A pre Gn x'; let r':=g x'*u; let δ:= k*(2*relief L x')
      have hw :0<w x':= hx.enjoys.1; have hχ:0 < r':=mul_pos (hk _) hu
      have h₁:δ ≤ r'/2:=by apply le_of_mul_le_mul_left _ (hi x'); have he:z x'*δ ≤ u/2:= (le_abs_self _).trans h1; apply he.trans_eq; unfold r'; field_simp; rw [mul_comm (z x'),hg] -- orientation div
      have h₂: 2*relief L x'*B ≤ r':= by apply le_of_mul_le_mul_left _ (hi x'); have h: z x'*(2*relief L x'*B) ≤ u:= (le_abs_self _).trans h2; exact h.trans_eq (by unfold r'; rw [←mul_assoc,mul_comm (z x'),hg,one_mul])
      have h₃: E' ≤ r'/2:=by apply le_of_mul_le_mul_right _ (hi x'); have he:E'*z x' ≤ u/2:= (le_abs_self _).trans h3; apply he.trans_eq; unfold r'; field_simp; rw [hg] -- ring
      have h₄ :X x' ≤ (r'/(2*A))*w x':=by
          have h:z x'*(f x'*(v0 x')⁻¹) ≤ u/(2*A):= (le_abs_self _).trans h4
          have ht:f x'*(v0 x')⁻¹ ≤ r'/(2*A):=le_of_mul_le_mul_left (h.trans_eq ?_) (hi _); rotate_left; · unfold r'; field_simp; rw [mul_comm (z x'),hg]
          rw [←div_eq_mul_inv] at ht; have hV:0 < Jets.Touch.chip L x':=h5.2.1
          refine ((div_le_iff₀ hV).mp ?_).trans_eq (b:= (r'/(2*A)) * v0 x'*Jets.Touch.chip L x') (mul_assoc ..); rw [div_eq_mul_inv]; change f x' ≤ _; exact (div_le_iff₀ (fan_pos ..)).1 ht
      have hh: A*X x' ≤ r'/2*w x':= (mul_le_mul_of_nonneg_left h₄ ha.le).trans_eq (by field_simp)
      have hV: max δ E'*w x'+ A*X x' ≤ r'*w x':=(add_le_add (mul_le_mul_of_nonneg_right (max_le h₁ h₃) hw.le) hh).trans_eq (by ring)
      refine ⟨?_,hV,h₄.trans (mul_le_mul_of_nonneg_right ((div_le_self hχ.le (by linarith only [hA]))) hw.le)⟩
      obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,-,-⟩:= hx.enjoys; refine ⟨a₁,a₂,a₃,a₄,a₅,a₆,?_,h₂⟩; refine (add_le_add_left (mul_le_mul_of_nonneg_right (max_le_max_left _ ?_) hw.le) _).trans hV
      unfold FeeH E' extraE; have h : 0≤A*(Kit.slope L^(Gn+1)*pre):=by positivity
      apply mul_le_mul_of_nonneg_right _ h; apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
end Ivy
end Bank.Hike
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Bank.Hike.Ivy.scrutiny
