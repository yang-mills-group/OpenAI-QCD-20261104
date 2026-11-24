import YM.Magi.Town
set_option autoImplicit false
noncomputable section
namespace YM.Hypnos
open Filter Function Lattice Wilson Tree RG Pressure Finset MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations Push.SectorMeasure Push.SectorMeasure.Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Coat Blaze.Vine
open Shell Channel

open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Next.SectorChange
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Matrix Census Green Mask Pulse Itinerary Matter Poll Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{β τ C μ W:ℝ} {o: ConnectedActivityE6.Target.Order G W}{Q:ConnectedActivityE6.Target G P} {X:S.Choices} {r u t d A M D:ℝ}{F:Tree.Forest S.ratio}{n:ℕ}

-- actual aid for enclosures etc
variable (X:Coat T F)(Y: Support c)
open Planned.AtomRegular.Foliage
def inkV (N:ℕ)(M:ℝ)(x:ℝ):= M*(4*(temp x*(1+(↑(N*radiusB x):ℝ))))
lemma windyV (G:Gauge)(L:Side)(m:ℕ) : ∃ C:ℝ,0<C ∧ ∀ᶠ x:ℝ in atTop, 0≤ inkV m C x ∧ ∀ (c:Side)(i : Site c)(U:Config G c)(Y:Support c)(n:ℕ), n ≤ m*radiusB x→ Healthy (temp x) Y U → halo (n+1) {i}⊆Y → 2*(n+1)<c.val → ∃ g: Site c→ G.El, ∃ b:Directions G c, ‖b‖≤ inkV m C x ∧ AgreeNear id i n (gauge g U) (increment 1 b):=by
    obtain ⟨C,d,hC,hd,h⟩:= log_chart_cost G
    let r x:= (m* radiusB x:ℕ); let Z (x:ℝ):= 4*(temp x*(1+(r x:ℝ))); have hZ : Rate G L (-(1/2)) Z:=by
       have hh:Rate G L 0 (fun x=>(r x:ℝ)):=by unfold r; push_cast; exact Rate.radius_price.mul_left m
       simpa only [add_zero] using ((vein_temp G L).mul ((Rate.const 1).add hh)).mul_left 4
    refine ⟨_,hC,?_⟩
    filter_upwards [hZ.below (by norm_num) d hd] with x hx
    have hp:=Work.E04.temp_nonneg x; have hs : 0 ≤ Z x:=by unfold Z; positivity
    refine ⟨mul_nonneg hC.le hs, ?_⟩; intro c i U Y n he hv hY hc; obtain ⟨g,hg⟩:=Cube.anchored i hv hp hY hc
    let b:=PhysicalNext.JointLoad.Heir.crop i n g U
    have ht (a: Bond c) (ht: separation i a.1 ≤ n): G.chord (gauge g U a)≤ Z x := (hg a ht).trans (by unfold Z; gcongr; exact ht.trans he)
    refine ⟨g,b,?_,?_⟩
    · refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le hs)).mpr fun j=> ?_; unfold b JointLoad.Heir.crop; split
      next he => exact (h _ ((ht _ he).trans ((le_abs_self _).trans hx))).2.trans (mul_le_mul_of_nonneg_left (ht _ he) hC.le)
      rw [norm_zero]; positivity
    intro a hq; change separation i a.1≤n at hq
    rw [increment]; unfold b JointLoad.Heir.crop; rw [if_pos hq,(h _ ((ht a hq).trans ((le_abs_self _).trans hx))).1,Pi.one_apply,mul_one]

end YM.Hypnos
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
variable {c f C F L:Side} {J:Patch} {j k n m i l n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
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
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
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
local notation "SCp"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
variable (V U W:ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) 6)
variable (hp:Tavern P₀ A X B T κ Z V U W F)(hX:entire P₀ A x Pt)(hc:Suburb.Calm P₀ A X x)
variable (E:RiseBook P₀)
open Rails.Kin Massive.Filament
variable (M₀:Arrow 6) {M₃:ℝ} (he:Views P₀ A X E x)
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
-- Mark price route from DomeVoice all.Account property in representation already. Heights regraded goals for firing.
local notation "qS"=> A.spacing i
local notation "sⁱ"=> clockQ P₀ A x i
local notation "x⁺"=> run (A.spacing i) (clockQ P₀ A x i)
local notation "vT"=>fan qS θ sⁱ
local notation "vT₁"=>fan qS θ x⁺
local notation "Dⁱ"=> stepper P₀ A X B T i
local notation "d'T"=>A.next (B.n k) i
local notation "S★"=> (stepper P₀ A X B T i).visit K (A.next (B.n k) i)

local notation "Bn"=> Banner P₀ A X B T k Pt V
local notation "Sn"=> basisR P₀ A X B T k U
local notation "D₁" hi=> (C.Λ i (Nat.zero_le _) hi)
open MassiveQCD.FlareV MassiveQCD.Cape MassiveQCD.Play MassiveQCD.Rebus Hypnos
open Suburb.Melt.Lobby Suburb.Affair.Nimbus
open MintV
variable {Zp:Finset (Finset Iq)}
omit hC he
namespace LeaseV
open Hypnos
variable (L:Side)
set_option quotPrecheck false
local notation "EV"=>measureV L
local notation "Ω"=> cutOffV L
local notation "Bᵥ"=>run L
local notation "Hb"=> distV L
namespace Advent
-- delivery.Template.Econ Ω.Price budgets.V future.Ow.Support. prefer evaluate pol only over smallFV at terminal rather than full ^time clock. Use EV6 chart based.He. 
lemma stature (L:Side): Jets.Touch.Seat L 0 (fun x=> (Pressure.radiusB (run L x):ℝ)) :=by
     -- shift, metres.P.Point
     have ht:∀ᶠ x:ℝ in atTop,(radiusB (run L x))^2 ≤2*(radiusB x)^2:= Stock.stepsize _ -- namespace
     apply Jets.Touch.Seat.compares (Jets.Touch.Seat.timesL Jets.Touch.Seat.radius 2); filter_upwards [ht] with x hx
     rw [abs_of_nonneg (by positivity)]; apply le_trans _ (le_abs_self _); exact_mod_cast (show radiusB (run L x) ≤ 2*radiusB x from by by_contra h; push Not at h; nlinarith)
lemma windsV (n b:ℕ)(C:ℝ)(hC:0<C)(hL:1<L.val) : ∀ᶠ z in atTop,∀ i ≤ Hb n z,let y:=riseV L z i; inkV b C (Bᵥ y) ≤ freshS L 5 z:=by
     let p x:ℝ:= C*(4:ℝ)*(1+(b*radiusB (run L x):ℕ))
     have hG:Jets.Touch.Seat L 0 p:=by unfold p; push_cast; exact ((Jets.Touch.Seat.numbers 1).comb ((stature L).timesL b)).timesL _
     filter_upwards [lapsV L n,aheadΩ L _ (rainingV L hL),aheadΩ L _ (hG 1 zero_lt_one), Delay.shift_pos su L,curtailV L n 1 hL,priceL L n 3 4 hL (by omega) 1,(buysV L).eventually_ge_atTop 4,goCost L 4 5 2 1 hL (by norm_num)] with z h ht hh hp hv hA hx hf i hi
     intro y; have hr: Bᵥ z≤ Bᵥ y:= (h _ hi).1; have hv' : p y ≤ EV 3 z:= ((le_abs_self _).trans (hh i)).trans (hv _ hi)
     have hc :0 ≤ p y:=by unfold p; positivity
     have hg:= hA i hi; rw [pow_one] at hg
     have h0:= lightsV L z hp (1/2); have hΛ:1 ≤ EV 4 z:=uniformV ..
     calc
        inkV b C (Bᵥ y) = fiery su y L * p y:=by unfold inkV p; dsimp only [fiery,run]; ring -- decal clash
        _ ≤ freshS L 3 y * p y := mul_le_mul_of_nonneg_right (ht i) hc
        _ ≤ (Ω (1/2) z * EV 4 z)* EV 4 z :=mul_le_mul (show freshS L 3 y≤ Ω (1/2) z * EV 4 z from mul_le_mul (marginsV L hp hr _ (by norm_num)) hg (MintV.χone ..|>.le) h0.le) (hv'.trans (outR L _ _ z ((show 1 ≤4 from by norm_num).trans hx) (by norm_num))) hc (by positivity)
        _ ≤ _:=by rw [mul_assoc,← pow_two]; unfold freshS; apply mul_le_mul_of_nonneg_left (le_trans _ hf) h0.le; rw [one_mul]
structure RouteV (L:Side)(n m:ℕ)(z:ℝ):Prop where
      act i: i ≤ distV L n z→ let x:=riseV L z i; let b:=radiusB (run L x); ∀ (c:Side)(p:Site c)(U:Grid c)(Y:Support c)(r:ℕ), r ≤ m*b → Healthy (fiery su x L) Y U → halo (r+1) {p}⊆ Y → 2*(r+1)< c.val → ∃ g: Site c→ su.El, ∃ B: Directions su c, ‖B‖ ≤ freshS L 5 z ∧ AgreeNear id p r (gauge g U) (increment 1 B)
lemma findsV (n m:ℕ) (hL:1<L.val):∀ᶠ x in atTop, RouteV L n m x:=by
      obtain ⟨C,hC,h⟩:=windyV su L m
      filter_upwards [windsV L n m C hC hL,aheadΩ L _ ((Work.E09.betaF_growth su L).eventually h)] with x ht he; constructor; intro i hi y b c p U Y r hv hz hp hq; obtain ⟨g,B,hB,hv'⟩:=(he i).2 _ _ _ _ _ hv hz hp hq; exact ⟨g,B,hB.trans (ht i hi),hv'⟩
end Advent
end LeaseV
end Lobby
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.LeaseV.Advent.findsV
