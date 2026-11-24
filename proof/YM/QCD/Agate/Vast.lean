import YM.QCD.Agate.Ember
import YM.QCD.Plum.Gist
import YM.QCD.Agate.Stride
import YM.Branch.Pick
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
open Tide
-- variable look compatibility: does not presume sequential all bounded Borel
variable (hB:Even (B.n 0).val)(hE:∀ i,B.n i=B.n 0*O.L^i)
variable {D':Lot}
variable (Ω':Ultrafilter ℕ)(he:(Ω':Filter ℕ)≤ atTop)
open scoped ComplexOrder
structure Cer (P:ScaleF N)(O:Patch):Prop where
    rel(A: Lot)(x:Malt A N)(D: Lot)(W:Wall)(hW:W.Within A D)(hp:A ⊆D)(hx: stern W A (longM O)): 0 ≤ P.mass D (torch W hW x*wheel hp x)
-- hermitian on whole half-margin by polarization. Gap scales to zero.
variable (V M' W₀:ℕ→ℝ)(X:ℕ→ScaleF N)(hV:Skates B Y U W X₀ Ω' V M' W₀ X)
include hh hB hE he hV
lemma vera(i:ℕ): Cer (X i) O:=by
   constructor; intro A p D W hm hp hT; apply ge_of_tendsto (hV.mass i D _); apply he; let s:= finC O B i; have hv:= finEv B hB hE i; have ht:= finH B O i
   filter_upwards [outH W s ht hv _ hT, Agate.trusted W hm p s ht hv, ht.eventually (eventually_ge_atTop 4),eventually_ge_atTop i] with k hx hu hm hl
   let R:= FaceR W (hv k); have hh': (s k).val=2*R.half.val:=R.even; have hh'':2 ≤ R.half.val:=by change 4≤ (s k).val at hm; omega
   unfold songR; rw [map_mul,wheeling]; rw [← hu]; exact (hh.ocean k i (by omega)).rails R rfl hh'' (Agate.visit _ p) (palps _ p).hp (palps _ p).hz (staysJ _ _ _ hx)
-- full obligation in unified package
omit hh hB hE he hV
structure Converse (Q:ConnectedActivityE6.Target su T')(P:Patch)(F:Flavor N)(a d D:ℝ) : Prop where
   frameK : ∃ (τ:Policy Q T'.top N)(κ:ℝ)(l:ℕ),0 < τ.t ∧0 < κ ∧∀ᶠ x:ℝ in atTop, ∃ (B:SparkMesh)(Y U W T:ℕ→ℕ→ℝ)(X₀:∀ i k:ℕ,Pixel (finC P B i k) N)(M Z:ℕ→ℝ), Even (B.n 0).val ∧B.n 0=sFirst P.L l (run P.L x)∧ (∀ i,B.n i=B.n 0*P.L^i)∧ (∀ i,0<Z i)∧(∀ y,x ≤y→ Shade P.L τ.t y)∧ Evokes Q F P a d D B Y U W T X₀ M Z κ x τ ∧∀ Ω':Ultrafilter ℕ,(Ω':Filter ℕ)≤ atTop → ∃ (V M' W₀:ℕ→ℝ)(X:ℕ→ScaleF N), Skates B Y U W X₀ Ω' V M' W₀ X∧ M' 0=0∧ V 0=run P.L x∧(∀ i, GaugeM P i x/2≤ V i ∧ V i ≤ 2*GaugeM P i x ∧ |M' i|≤ rangeG P i 0 κ τ.t x ∧ Z i≤ W₀ i∧ W₀ i≤4)∧ (∀ i,Cer (X i) P)∧(∀ i:ℕ,∀ (A: Lot)(p:Malt A N),∃ y:Malt (rimH A P) N, TrackF P T'.bind B (V (i+1)) (W₀ i) i p y ∧ (X i).mass A p=(X (i+1)).mass (rimH A P) y)
lemma verseR (F:Flavor N)(h:Milestone Q O F a d D)(hk: O.Branches T'.bind su): Converse Q O F a d D:=by
    obtain ⟨τ,κ,l,hκ,hT,H⟩:= h.dawn; refine ⟨τ,κ,l,hT,hκ,?_⟩; filter_upwards [H] with x h; obtain ⟨B,M,Z,Y,U,W,T,X,hZ,hShade,hB,hX,hE,hh⟩:= h; refine ⟨B,Y,U,W,T,X,M,Z,hB,hX,hE,hZ,hShade,hh,fun Ω' he=> ?_⟩
    obtain ⟨V,M',W₀,X',hp⟩:= sweeping B F Y U W T X M Z hh hB hE Ω' he; obtain ⟨ht,hv,hK⟩:=leapJ B F Y U W T X M Z hh Ω' he V M' W₀ X' hp; refine ⟨V,M',W₀,X',hp,ht,hv,hK,vera B F Y U W T X M Z hh hB hE Ω' he V M' W₀ X' hp,fun i A p=>?_⟩
    obtain ⟨y,hL⟩:= linkedF B hB hE hk (V (i+1)) (W₀ i) p i -- needs V
    exact ⟨y,hL,warm B F Y U W T X M Z hh hB hE Ω' he V M' W₀ X' hp i p hk y (hZ i) hL⟩
lemma saturated (h:N ≤ 8)(hN:Even N) : (∃ Ω' : Ultrafilter ℕ, (Ω':Filter ℕ) ≤ atTop) ∧ ∃ (T': Teller su),(∀ J:Patch,J.Branches T'.bind su)∧∃(Q:ConnectedActivityE6.Target su T')(s t D:ℝ)(m:ℕ), 0≤D∧ 512 ≤ m∧ (∃J:Patch,J.J=4∧m ≤ J.L.val)∧∀ J:Patch,J.J=4→ m ≤ J.L.val→ 2*(D+3) ≤ subG N*Real.log J.L.val∧ Converse Q J b' s t D:=by
   obtain ⟨K,-,H⟩:= Axial.viable su _ (show (0:ℝ)<1 by norm_num); obtain ⟨T,hk,Q,s,t,D,m,h0,h1,h2⟩:= IV.might b' K h hN; subst K; refine ⟨?_,T,H,Q,s,t,D,m,h0,h1,?_,fun J he hv=>?_⟩
   · exact ⟨Ultrafilter.of atTop,Ultrafilter.of_le _⟩
   · let L:Side:= ⟨2*m+1,by omega⟩; have hx:L.val=2*m+1:=rfl; exact ⟨⟨L,4,le_rfl,by omega,m,rfl⟩,rfl,(show m ≤ L.val by omega)⟩
   exact ⟨(h2 J he (H J) hv).1,verseR b' (h2 J he (H J) hv).2 (H J)⟩
end IV
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.IV.saturated
