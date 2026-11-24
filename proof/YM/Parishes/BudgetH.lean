import YM.Parishes.ArchC
import YM.Parishes.Braid
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Rate
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
def Curve (L:Side)(t z:ℝ):= t*(Jets.Touch.chip L z)
abbrev preS (M B:ℝ) := M* Real.exp (αI*81)*B
abbrev supportC (M B A:ℝ):=(1+B*A)*(preS M B+2) -- bound old β.
variable {i0 kq Gn Dx nL r:ℕ}{pre αp βp χp Gv εd ξ ε:ℝ}
abbrev FeeH (X L:Side)(Gn:ℕ)(A M t:ℝ):ℝ:= Real.exp ((αI-μ⁰)*highR L t)*(A*(Kit.slope L^(Gn+1)*M))
local notation "d0"=> Kit.slope L
local notation "xg"=>run L x
local notation "Ωv"=>preS pre βp
local notation "outX"=> supportC pre βp αp
-- loan heights. specify ∀ We/Toted weighted.Jump.
structure BudgetH (L:Side)(Q i Gn n k R' E D:ℕ)(θ pre B A G ε x:ℝ): Prop where
   costs : Marginal L θ x
   baseT : fiery su (run L x) L ≤4* temp (run L x) -- incoming→out
   readV : fan L θ (run L x)≤2*fan L θ x
   ahead : R'+1 ≤ highR L (run L x)
   era : 81 ≤ highR L (run L x)
   lens : i≤ 10*radiusB (run L x) ∧ 8≤radiusB (run L x)
   halo :∀ (c f:Side)(R:Ratio c f),R.count=L →Footprint.preCost (Q+8)+Footprint.conversion R (Q+8)*81 ≤ radiusB (run L x)
   earnings : let z:=run L x; let u:=Kit.slope L; ∃ w:ℝ,0<w ∧ (Real.exp (μ⁰*81)*B)*w+G*w ≤ spareCut (Jets.Touch.chip L z)∧ G*w≤ spareCut 1 ∧
       let A':= preS pre B; let v:= ArchC L θ Q i k n E D z
       (∀ y:ℝ,u^Gn * w≤y→ y≤w→∀ q:ℝ,q≤G*w→let X':= A'*y + ((u^(Gn+1)*pre)*q+ v); FeeE i k n z *King.flowM L z+B*(A*X')≤1 ∧ (1+B*A)*X' ≤ supportC pre B A*y∧ tax_save L x ≤ y) ∧
       (max ((Fintype.card (Rings Gn):ℝ)*(2*relief L z)) (FeeH L L Gn A pre z))*(G*w)+ A*v ≤ ε*u^Gn*w ∧
       2*relief L z*B ≤ ε*u^Gn
-- E=Dx at specs.S confusion.Y OK.
private lemma tax_slope (L:Side)(M:ℝ)(hp:0<M): ∀ᶠ x in atTop,Hike.tax_save L x ≤ M* Jets.Touch.chip L (run L x):=by
    let A:=Hike.tax_save L
    have hz : Calm.Signal L (-1) A := Calm.Signal.seed (show Rate su L (-2) A from Touch.couplings L (by norm_num : 0<(1/2:ℝ))) (by norm_num)
    filter_upwards [Finch.pegL L, Calm.Signal.moneyP hz (by norm_num) (half_pos hp)] with x h hc; have hF:= mul_le_mul_of_nonneg_left h.1 (half_pos hp).le; linarith only [hF,hc]
lemma sizingH (M:ℝ)(hM:0<M): ∃ s:ℕ,∀ L:Side,s≤ L.val → Kit.slope L*M ≤1:=by
    obtain ⟨u,hu⟩:= exists_nat_ge (M^2); refine ⟨u,fun L h=>?_⟩; have ht:M^2 ≤ (L.val:ℝ):= hu.trans (by exact_mod_cast h); unfold Kit.slope; have hF : 0< (L.val:ℝ):=by positivity
    exact (show (Real.sqrt (L.val:ℝ))⁻¹*M=M/Real.sqrt (L.val:ℝ) from by ring).trans_le ((div_le_one (Real.sqrt_pos.mpr hF)).2 ((Real.sqrt_sq hM.le).symm.trans_le (Real.sqrt_le_sqrt ht)))
lemma pulse_growthD (L:Side): Tendsto (fun x:ℝ=>(highR L x:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp (YM.Work.E09.betaF_growth su L))
variable (Q r i0 Gn n kq Dx nL:ℕ)(θ pre A B Gx Dd:ℝ) -- duplicates.Q outer Guide binder choose names.Z shadow; hxν
-- note high.After.Ap.Power sport.
lemma loanGate (hp:1≤pre)(hA:1≤A)(hB:1≤B)(hG:1≤Gx)(ht:0<θ)(hD:0 < Dd) : ∃ m:ℕ,∀ (W:Patch),m≤ W.L.val→ ∀ᶠ x in atTop, BudgetH W.L Q i0 Gn n kq r Dx nL θ pre B A Gx Dd x:=by
    have hR :0<B:= zero_lt_one.trans_le hB; have hR1: 0<pre:= zero_lt_one.trans_le hp; have hYP:0<Gx:= zero_lt_one.trans_le hG; have hAo:0<A:= zero_lt_one.trans_le hA
    obtain ⟨m,H⟩:= sizingH (pre*Gx) (by positivity); refine ⟨m, fun W h =>?_⟩
    let L:=W.L; let u:=Kit.slope L; have hU:0<u:=Kit.slope_pos _; let T:=preS pre B; have hT: 0≤T:=by unfold T preS; positivity
    have hA0:=H L h; let Yd:=u^Gn; have hF:0<Yd:=pow_pos hU _; let g:= fun x:ℝ=> run L x
    let D:=Real.exp (μ⁰*81)*B; let V:=D+Gx; have hV:0<V:=by unfold V D; positivity
    have hξ : 0<spareCut 1:=by unfold spareCut; rw [mul_one]; exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    let z:= spareCut 1 /V; have hz:0<z:=div_pos hξ hV; let w:=fun x=> z*Jets.Touch.chip L x; have hΨ:Tendsto g atTop atTop:=YM.Work.E09.betaF_growth su L
    let F':=ArchC L θ Q i0 kq n Dx nL
    let P(x:ℝ):=FeeH L L Gn A pre x; let t:= min Yd ((Dd*Yd)/(2*A)); have ht' :0<t:= lt_min hF (by positivity)
    let Aα:= Fintype.card (Rings Gn); have he : Rate su L (-(3/10)) (fun x=> FeeE i0 kq n x * King.flowM L x):=by simpa only [zero_add] using (((Reel.for_voices L 2 μ⁰).mul_left (Girdle.tariff i0 2 kq n)).mul (show Rate su L (-(3/10)) (King.flowM L) from Rate.power))
    have hh:Rate su L (-1) w:=(Jets.Touch.chip_rate L).mul_left _; -- alias
    let χ:=(Dd*Yd)/(2*Gx); have hΧ:0<χ:=by unfold χ; positivity
    have hP : ∀ᶠ x in atTop,P x≤χ:=by
       let K:= A*(u^(Gn+1)*pre); have hA0:= (((Real.tendsto_exp_atBot.comp ((pulse_growthD L).const_mul_atTop_of_neg (show αI-μ⁰<0 by norm_num))).mul_const K).eventually_le_const (show (0:ℝ)*K<χ from zero_mul K|>.symm ▸ hΧ)); exact hA0 -- API
    have hS: Jets.Touch.Seat L ( (-1)/3) (fun x :ℝ=> (Aα:ℝ)*(2*relief L x)):= Seat.timesL (Seat.timesL Seat.keeps _) _ -- syntactic
    have hC: Jets.Touch.Seat L ( (-1)/3) (fun x:ℝ=>2*relief L x*B):= Seat.times (Seat.timesL Seat.keeps _) _
    let Ω:=Footprint.preCost (Q+8); have hΩ:0 ≤ Ω:=by unfold Ω Footprint.preCost; positivity
    have hV': Tendsto (fun x:ℝ=>radiusB (g x)) atTop atTop:= YM.Work.E01.radiusB_tendsto.comp hΨ; have hP': Tendsto (fun x:ℝ=> highR L (g x)) atTop atTop:= YM.Work.E01.radiusB_tendsto.comp (hΨ.comp hΨ)
    let S:ℝ:= B*A*(T+2); have hS0:0 ≤ S:=by unfold S; positivity
    filter_upwards [maintains L θ,hΨ.eventually (AnalyticNext.ConnectedActivity.Rates.closer su W), Finch.dim L θ,hP'.eventually_ge_atTop (r+1+81), hV'.eventually_ge_atTop (i0+8), (tendsto_natCast_atTop_atTop.comp hV').eventually_ge_atTop (Ω+10*Ω*81),hΨ.eventually (event_chip L 0),hΨ.eventually ((hh.mul_left Gx).below (by norm_num) _ hξ), tax_slope L (Yd*z) (by positivity), hΨ.eventually (((hh.mul_left S).weaken (show (-1:ℝ)≤ -1/2 by norm_num)).below (by norm_num) (1/2) (by norm_num)), hΨ.eventually (he.below (by norm_num) (1/2) (by norm_num)),hΨ.eventually (hung L Q i0 kq n Dx nL θ (t*z) (by positivity) ht), hΨ.eventually (hS.shrinks (by norm_num) hΧ), hΨ.eventually hP,hΨ.eventually (hC.shrinks (by norm_num) (mul_pos hD hF))] with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    let x':=g x; let Ω':=w x'; have hw:0<Ω':=mul_pos hz h7.2.1
    change r+1+81≤highR W.L (run W.L x) at h4; change i0+8≤radiusB (run W.L x) at h5
    refine ⟨h1,le_trans h2.2 (mul_le_mul_of_nonneg_right (by norm_num) (YM.Work.E04.temp_nonneg (g x))), h3,(by omega),(by omega),⟨by omega,by omega⟩, (fun c f R hR'=>?_), Ω',hw,?_, (le_abs_self _).trans h8, fun y hy hy' q hq=> ?_,?_, (le_abs_self _).trans h15⟩
    · let K := R.count; have hT:Footprint.conversion R (Q+8) ≤ 10*Ω:= div_le_self (by positivity : 0≤10*Ω) (by change 1≤(K.val:ℝ); exact_mod_cast K.property); exact (add_le_add_right (mul_le_mul_of_nonneg_right hT (by norm_num)) Ω).trans h6
    · apply le_of_eq; change D*_+Gx*_= _; rw [← add_mul]; unfold Ω' w z spareCut; change V*((1-_)*1/V*_) = _; field_simp; rfl
    · have hp: (u^(Gn+1)*pre)*q ≤y:=by
          have ht': u*(pre*Gx)≤1:= hA0
          have he:= mul_le_mul_of_nonneg_right ht' (mul_pos hF hw).le; exact (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ u^(Gn+1)*pre)).trans ((by rw [pow_succ]; nlinarith only [he] : (u^(Gn+1)*pre)*(Gx*Ω') ≤ Yd*Ω').trans hy)
      have hV:F' x' ≤ y:=h12.trans (by exact ((mul_assoc ..|>.le).trans (mul_le_mul_of_nonneg_right (min_le_left ..) hw.le)).trans hy)
      intro X'; have hX:X' ≤ (T+2)*y:=by change T*y+_≤ _; rw [add_mul]; linarith only [hp,hV]
      refine ⟨add_le_one_of ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hAo.le) hR.le) ,?_, h9.trans ((mul_assoc ..|>.le).trans hy)⟩ -- edit sum
      rotate_left; · exact (mul_le_mul_of_nonneg_left hX (by positivity : 0≤1+B*A)).trans_eq (mul_assoc ..).symm
      have hg:S*y≤1/2:= (mul_le_mul_of_nonneg_left hy' hS0).trans ((le_abs_self _).trans h10); unfold S at hg; linarith only [hg,(le_abs_self _).trans h11]
    have h0 :max ((Aα:ℝ)*(2*relief L x')) (P x') ≤χ:= max_le ((le_abs_self _).trans h13) h14
    have hf := mul_le_mul_of_nonneg_right h0 (mul_pos hYP hw).le; have hs:t*(2*A) ≤ Dd*Yd:= (le_div_iff₀ (by positivity)).1 (min_le_right ..); have hv : χ*(2*Gx)=Dd*Yd:=by unfold χ; field_simp
    have hΩ:F' x' ≤ t*Ω':= h12.trans_eq (mul_assoc ..); nlinarith only [hf,mul_le_mul_of_nonneg_left hΩ hAo.le, mul_le_mul_of_nonneg_right hs hw.le, congr_arg (fun t:ℝ=>t*Ω') hv]
 where
    add_le_one_of {a b c:ℝ}(hx:a+c ≤ 1)(hb:b ≤ c):a+b ≤ 1:= (add_le_add_right hb _).trans hx
end Bank.Hike
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Bank.Hike.loanGate
