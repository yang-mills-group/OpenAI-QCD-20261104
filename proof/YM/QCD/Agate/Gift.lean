import YM.QCD.Agate.Pillar
import YM.QCD.Corn.Green
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
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
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N) (hG: Stargate T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0)
namespace IV
open Globe
open Land Plum Agate
variable (Y U W T:ℕ→ℕ→ℝ)(X₀:∀ i k:ℕ,Pixel (finC O B i k) N)(M Z:ℕ→ℝ)(hh:Evokes Q b' O a d D B Y U W T X₀ M Z κ x τ')
variable (hB:Even (B.n 0).val)(hE:∀ i,B.n i=B.n 0*O.L^i)
variable (Ω':Ultrafilter ℕ)(he:(Ω':Filter ℕ)≤ atTop)
structure Skates (V M W₀:ℕ→ℝ)(S:ℕ→ScaleF N):Prop where
   stature (i:ℕ): Tendsto (fun k:ℕ=>(Y (k+1-i) k,U (k+1-i) k,W (k+1-(i+1)) k)) (Ω':Filter ℕ) (𝓝 (V i,M i,W₀ i))
   mass(i:ℕ)(A:Lot)(p:Malt A N): Tendsto (fun k=>songR B X₀ A p i k) (Ω':Filter ℕ) (𝓝 ((S i).mass A p))
include hh hB hE he
lemma sweeping :∃ V M W₀:ℕ→ℝ,∃ S':ℕ→ScaleF N,Skates B Y U W X₀ Ω' V M W₀ S':=by
    choose V H using spot B b' Y U W T X₀ M Z hh hB hE Ω' he; let g (i k:ℕ):= (Y (k+1-i) k,U (k+1-i) k,W (k+1-(i+1)) k); have hp(i:ℕ):∃ p:ℝ×ℝ×ℝ,Tendsto (g i) (Ω': Filter ℕ) (𝓝 p):=by
         let K:= Knot (Rᵥ:=Z) (x:=x) (κ:=κ) (r:=τ'.t) O i; have h:∀ᶠ k in atTop,g i k∈K:=by
             filter_upwards [eventually_ge_atTop i] with k hk; obtain ⟨_,_,_,_,h,hp',hr⟩:= (hh.candor k).capital i (by omega); obtain ⟨he,hv,_⟩:= (hh.candor k).vocals i (by omega); exact ⟨⟨h,hp'⟩,abs_le.mp hr,hv,he⟩
         obtain ⟨u,hv,H⟩:=mantic Ω' he K (show IsCompact K from isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) (g i) h; exact ⟨u,H⟩
    choose p hz using hp; exact ⟨(fun i=>(p i).1),(fun i=>(p i).2.1),(fun i=>(p i).2.2),V,hz,H⟩
omit hB hE
variable (V M' W₀:ℕ→ℝ)(S₀:ℕ→ScaleF N)(hk:Skates B Y U W X₀ Ω' V M' W₀ S₀)
include hk
-- Mass bare tuning not physical mass, stiffness etc. parameters UV.Run actual positive eventually.
lemma leapJ : M' 0=0 ∧ V 0=run O.L x ∧ ∀ i, GaugeM O i x/2 ≤ V i ∧ V i ≤2*GaugeM O i x ∧|M' i| ≤ rangeG O i 0 κ τ'.t x ∧ Z i ≤ W₀ i ∧ W₀ i ≤ 4:=by
    refine ⟨tendsto_nhds_unique (show Tendsto (fun k:ℕ=> U (k+1-0) k) (Ω':Filter ℕ) (𝓝 (M' 0)) from (continuous_fst.tendsto _).comp ((continuous_snd.tendsto _).comp (hk.stature 0))) (tendsto_const_nhds.congr fun i=> ((hh.candor i).mint.1).symm),tendsto_nhds_unique (show Tendsto (fun k:ℕ=> Y (k+1-0) k) (Ω':Filter ℕ) (𝓝 (V 0)) from (continuous_fst.tendsto _).comp (hk.stature 0)) (tendsto_const_nhds.congr fun i=> ((hh.candor i).mint.2).symm),fun i=>?_⟩
    let K:= Knot (Rᵥ:=Z) (x:=x) (κ:=κ) (r:=τ'.t) O i; have h:(V i,M' i,W₀ i) ∈ K:=by apply (show IsClosed K from isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)).mem_of_tendsto (hk.stature i) (he ((eventually_ge_atTop i).mono fun k h=>?_)); obtain ⟨_,_,_,_,h',h'',hV⟩:= (hh.candor k).capital i (by omega); obtain ⟨hp,hX,-⟩:= (hh.candor k).vocals i (by omega); exact ⟨⟨h',h''⟩,abs_le.mp hV,hX,hp⟩
    exact ⟨h.1.1,h.1.2,abs_le.mpr h.2.1,h.2.2⟩
end IV
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.IV.sweeping
