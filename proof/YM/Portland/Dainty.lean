import YM.Portland.Spoon
import YM.Portland.Rank
import YM.VStages.FullRun
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
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {K:KernelChoices}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open MeasureTheory Rails.Reference Next.Rank IV Rain
open Finset NormedSpace Grass
open Cairn
open YM.Massive.Pressure (noiseZ)
open YM.SectorNext.Vacuum (rich spare)
variable {κ:ℝ}
open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open Affair
namespace Melt
open Weft Fibre Sway OrbitG Conductor Conductor.Quant Struck Struck.Library Aperture -- Weft
variable {Pt:ℕ→BudgetPoint}{Δ:PlaqAxes}
variable (B:SparkMesh) (T:Affair P₀ A X B x n) (Z:Sheltered P₀ A X B T k Pt Δ)
set_option quotPrecheck false
local notation "Pq"=> J (A.level i)
local notation "S'"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
variable (V U W:ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) N)
variable (hp:Tavern P₀ A X B T κ Z V U W F)(hX:entire P₀ A x Pt)(hc:Suburb.Calm P₀ A X x)
variable (E:RiseBook P₀)
open Rails.Kin Massive.Filament
variable (M₀:Arrow N) {M₃:ℝ} (he:Views P₀ A X E x)
variable (Y:Precinct P₀ A B k n) (hh: Keeps P₀ A X B T V W F Y)
local notation "ζi"=> (clockQ P₀ A x i)
local notation "θ₀"=> θ
local notation "Fz0"=>family P₀ A B Y
local notation "Fz"=>family P₀ A B Y M₀.tip

namespace Lobby
open MassiveQCD.Plate MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Twist Bank
open Massive.Pressure Rails.Reference.Sharp
-- active point on gears
include he
variable {s w:ℝ}(C:DomeVoice P₀ A X B T V U W E M₀ Y Pt 0 s)
open scoped ComplexOrder
variable (Ht: Uptax P₀ A E x)(O:Paved P₀ A X x) (L1:HaarBudget su)
variable (hC:Glacier P₀ A X B T V U W E M₀ Y Ht C L1 w O)
local notation "DL" hi=> C.Λ i (Nat.zero_le _) hi
local notation "Fz!"=> family P₀ A B Y M₀.tip s
local notation "Tt"=> voyage P₀ A x w i
include hC
local notation "cp"=>A.ring (B.n k) i
local notation "fp"=>A.ring (B.n k) (i+1)
variable {Iq AA BB:Type} [Fintype Iq]
local notation "Θ"=> voyage P₀ A x w
local notation "qS"=> A.spacing i
local notation "vT"=>fan qS θ ζi
local notation "x⁺"=>run (A.spacing i) (clockQ P₀ A x i)
local notation "vT₁"=>fan qS θ x⁺
local notation "Ff"=>30*radiusB x⁺
local notation "Bn"=> Banner P₀ A X B T k Pt V
local notation "Sn"=> basisR P₀ A X B T k U
open Comet
local notation "Bz"=> maltar P₀ A X B T V U W E M₀ Y s w C
local notation "Dⁱ"=> stepper P₀ A X B T i
variable (hpV:MarketCredit (P₀ (A.node i)) (X i) (clockQ P₀ A x i)) (αH:ℝ)
local notation "v!"=>escrow P₀ A X x αH
local notation "Ψ"=>continuum
local notation "F0"=>Fleet.Glow.payFee (P₀ (A.node i)).guide qS θ x⁺
local notation "Qw"=> Comet.wishGain x⁺ qS
omit he hC
open YM.Massive.PCAC.Brave YM.Massive.PCAC.Brave.CoatB YM.QCD.Acre.Rails.Reference.Glint
-- λ Step base before clock grant. bTop radius arbitrary Ψ lock.H Ener ℓ.
section
noncomputable def stub (L:Side)(t ξ x:ℝ): TokenP:=⟨enhancedB ξ,fan L t x,0,0,100*fundsL L t ξ,1,1⟩
noncomputable def costa (J:Patch)(r ξ ε y:ℝ):ℝ:= Requests (N:=6) ξ ε J y/(fan J.L r y)^4
noncomputable def cupsB (K:Spike)(p κ σ r ξ ε:ℝ)(J:Patch)(n:ℕ)(x y:ℝ):ℝ:= let S:=stub J.L r x y; let F:=moldB x; cupSize K n (4*positiveAnswer J y κ r) (8*p+F*S.v) (bronze S F 2) (bronze S F 4) (costa J r ξ ε y) -- σ unused. OK
lemma mug (X:Spike)(p κ ε t σ o:ℝ)(J:Patch)(n:ℕ)(he:0< ε)(hs:0<σ)(hp:0 < t)(r:ℝ)(hr:0<r):∀ᶠ x in atTop, cupsB X p κ σ t o ε J n (run J.L x) x ≤ r*Glint.Value (Glint.money t (Quant.crest J.L x ε σ) J.L x):=by
    let L:=J.L; let d:= σ^2*ε/16; let u:=4*(κ/(8*J.L.val)); let g:=Jets.Touch.chip L; let f:=fan L t; let V:=Sharp.outE 6 ε o; let q(x:ℝ):=enhancedB (run L x); let w(x:ℝ):= 100*fundsL L t (run L x); let Y(x):=moldB (run L x); let g'(x:ℝ):=g x/(f x)^2; let c0(x):=8*p+Y x*w x; let c2(x):=2*(Y x*w x/(q x*f x)^2); let c4(x):=24*(Y x*w x/(q x*f x)^4)
    let z:ℝ:=Fintype.card Lat.Fiber; let k:=spinPrice Lat.g5; let c:=spinPrice X; let D(x):= cupSize X n (u*g' x) (c0 x) (c2 x) (c4 x) (V*g x/f x^4); have hE(x):cupsB X p κ σ t o ε J n (run J.L x) x=D x:=by
         have hK: 4*positiveAnswer J x κ t=u * g' x:=by unfold positiveAnswer roofK Emax u g' speedP f; ring -- denomin eq g J.L
         unfold cupsB; rw[hK]; dsimp only [D,cupSize]; unfold c4 c2 bronze q w Y c0; norm_num [stub,Nat.factorial]; exact Or.inl rfl
    have hc0(x): Glint.Value (Glint.money t (Quant.crest J.L x ε σ) J.L x)=d*g' x:=by unfold Glint.Value Glint.money Quant.crest d g' f g; ring
    have hx : Tendsto (run L) atTop atTop:= Work.E09.betaF_growth ..
    have hf : Tendsto f atTop atTop:=(tendsto_rpow_atTop hp).comp (Jets.Touch.Seat.your L)
    have hW : Tendsto w atTop (𝓝 0):=by
       have he:Tendsto (Jets.Touch.fundsL L t) atTop (𝓝 0):=(tendsto_inv_atTop_zero.comp hf).congr' (Eventually.of_forall fun x=>by unfold Jets.Touch.fundsL; exact (Real.rpow_neg (Delay.monitor_pos ..).le t).symm)
       simpa only [Function.comp_apply,w,mul_zero] using ((he.comp hx).const_mul (100:ℝ))
    have hq:Tendsto q atTop atTop:=(tendsto_rpow_atTop (by norm_num : (0:ℝ)<17/100)).comp hx
    have hv:Tendsto Y atTop (𝓝 0):= (tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<9/25)).comp hx)).congr' ((hx.eventually_gt_atTop 0).mono fun _ h=>(Real.rpow_neg h.le _).symm)
    have h0:Tendsto c0 atTop (𝓝 (8*p)):=by simpa only [mul_zero,add_zero] using tendsto_const_nhds.add (hv.mul hW) (a:=8*p)
    have hf': Tendsto (fun x=>(f x)⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp hf
    have hq': Tendsto (fun x=>(q x)⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp hq
    have h2:Tendsto c2 atTop (𝓝 0):=by
       have hh: Tendsto (fun x:ℝ=> 2*((Y x*w x)*( (f x)⁻¹*(q x)⁻¹)^2)) atTop (𝓝 0):=by simpa only [mul_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] using (((hv.mul hW).mul ((hf'.mul hq').pow 2)).const_mul (2:ℝ))
       apply hh.congr'; filter_upwards with x; unfold c2; rw [div_eq_mul_inv,← inv_pow, _root_.mul_inv_rev] -- inv_pow order
    have heγ:Tendsto g atTop (𝓝 0):=by
        rw [Metric.tendsto_nhds]; intro ε he; filter_upwards [(chip_rate L).below (by norm_num) (ε/2) (by positivity)] with x hx; rw [Real.dist_eq]; simp only [sub_zero]; exact hx.trans_lt (by linarith only [he] : ε/2 < ε)
    have hg': Tendsto g' atTop (𝓝 0):=by
        have hh:Tendsto (fun x=>g x*(f x)⁻¹ ^2) atTop (𝓝 0):=by simpa using heγ.mul (hf'.pow 2)
        apply hh.congr'; filter_upwards with x; unfold g'; rw[inv_pow,div_eq_mul_inv]
    let δ₁ (x:ℝ):= Y x *((q x)⁻¹)^4*(g x)⁻¹
    have heδ:Tendsto δ₁ atTop (𝓝 0):=by
        have hh : Rate su L ((-(9/25)+-17/100*4)+1) δ₁:= by
             refine (Rate.power.mul ((?_ : Rate su L (-17/100) (fun x=>(q x)⁻¹)).pow 4)).mul (top_chip L)
             refine Rate.power.congr ((hx.eventually_gt_atTop 0).mono fun x h=>?_); unfold q enhancedB; rw [show (-17/100:ℝ)=-(17/100:ℝ) from by ring]; exact (Real.rpow_neg h.le _).symm
        rw [Metric.tendsto_nhds]; intro ε he; filter_upwards [hh.below (by norm_num) (ε/2) (by positivity)] with x hx; rw [Real.dist_eq]; simp only[sub_zero]; exact hx.trans_lt (by linarith only [he])
    let Q(x:ℝ):=(f x)⁻¹ ^ 2; have hQ:Tendsto Q atTop (𝓝 0):=by simpa [Q] using hf'.pow 2
    let bq x:= 24*(w x*(δ₁ x* Q x))
    have hq:Tendsto bq atTop (𝓝 0):=by simpa only [mul_zero] using ((hW.mul (heδ.mul hQ)).const_mul (24:ℝ))
    let F(x):= z*c*(z*circleW n*( bq x+c0 x * (k*u*k*u*g' x) +u*c2 x +k*u*k*c2 x)+ c0 x *24*(V*Q x))
    have hF:Tendsto F atTop (𝓝 0):=by simpa only [mul_zero,zero_mul,add_zero] using! ( (((((hq.add (h0.mul (hg'.const_mul (k*u*k*u)))).add (h2.const_mul u)).add (h2.const_mul (k*u*k))).const_mul (z*circleW n)).add ((h0.mul_const 24).mul (hQ.const_mul V))).const_mul (z*c))
    filter_upwards [hF.eventually_le_const (mul_pos hr (show 0<d from by unfold d; positivity)), hx.eventually_gt_atTop 0] with x hv hx; have h:0< g x:= healthy_chip hx; have hg:0<f x:=fan_pos ..; have hp':0< q x:= by unfold q enhancedB; exact Real.rpow_pos_of_pos hx _
    have hs':F x * g' x=D x:=by unfold D cupSize rootM wingC F bq Q δ₁ c4 g' z k c; field_simp -- huge?
    rw [hE,← hs',hc0,← mul_assoc]; exact mul_le_mul_of_nonneg_right hv (div_pos h (pow_pos hg _)).le
end
end Lobby
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.mug
