import YM.QCD.Agate.Wisp
import YM.QCD.Agate.Gift
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
open Tide
lemma hub (r:Ratio c f)(he:Even c.val) : r.embed (origin c)=origin f:=by
   ext1 i; rw [← per_root,per_val]; change (((((↑(c.val/2):Per c).val*r.count.val):ℕ): Per f)= _); have hp:c.val/2<c.val:=Nat.div_lt_self c.property (by decide); rw [ZMod.val_natCast_of_lt hp]; apply congr_arg (fun a:ℕ=> (a:Per f)); obtain ⟨k,hk⟩:=he; rw [r.exact_size,hk,add_mul, show (k+k)/2=k from (by omega)]; omega
lemma gleaming (Y:Lot)(s:ℕ→Side)(h:Tendsto (fun i=> (s i).val) atTop atTop):∀ᶠ k in atTop, stoke (origin (s k)) Y:=by
     have hp(x:Court Y)(a:Axis):∀ᶠ k:ℕ in atTop,seam 0 (Agate.leap (origin (s k)) x.val) a=1:=by
          filter_upwards [h.eventually (eventually_ge_atTop (4*((x.val a).natAbs+2)))] with k hk; unfold seam; rw [if_neg]
          let n:=s k; change ((x.val a:Per n)+((n.val/2:ℕ):Per n))+1≠0; let t:= x.val a+((n.val/2:ℕ):ℤ)+1
          change 4*((x.val a).natAbs+2)≤ n.val at hk; have hh:0 < t ∧ t<n.val:=by unfold t; omega
          rw [show (((x.val a:ℤ):Per n)+ _ )+1=(↑t.toNat:Per n) from ?_];
          · intro g; have he:=ZMod.val_natCast_of_lt (show t.toNat<n.val by omega); have ht':t.toNat≠0:=by omega
            rw [g] at he; exact ht' (by simpa using he.symm)
          rw [← Int.cast_natCast (R:=Per n) t.toNat,Int.toNat_of_nonneg hh.1.le]; unfold t; simp only [Int.cast_add,Int.cast_natCast,Int.cast_one]
     exact (eventually_all.mpr fun i=> eventually_all.mpr (hp i))
-- actual pushed local class
abbrev TrackF (J:Patch)(K:KernelChoices)(B:SparkMesh)(p q:ℝ)(i:ℕ){D:Lot}(X: Malt D N)(Y:Malt (rimH D J) N): Prop:=∀ᶠ k in atTop, Tide.look (Pike J 0) K (powerV B J i k) p q (Agate.visit (origin _) X)= Agate.visit (origin _) Y
variable (hB:Even (B.n 0).val)(hE:∀ i,B.n i=B.n 0*O.L^i)(hk:O.Branches K su)
noncomputable def Spur (J:Patch)(B:SparkMesh)(i k:ℕ):= sliceL (Pike J 0) (powerV B J i k)
structure Wings (J:Patch)(B:SparkMesh)(i k:ℕ)(X:Lot):Prop where
    small:Fits (finC J B i k) X
    large:Fits (finC J B (i+1) k) (rimH X J)
    stake:stoke ((Spur J B i k).embed (origin _)) (rimH X J)
    realw: (Spur J B i k).embed (origin _)=origin _
include hB hE
lemma feather (X:Lot)(j k:ℕ):(Spur O B j k).embed (origin _)=origin _:=hub _ (finEv B hB hE _ _)
lemma flightH (X:Lot) (i:ℕ):∀ᶠ k in atTop,Wings O B i k X:=by
     filter_upwards [gravity X (finC O B i) (finH B O i),gravity (rimH X O) (finC O B (i+1)) (finH ..),gleaming (rimH X O) (finC O B (i+1)) (finH ..)] with k hk hl hw; exact ⟨hk,hl,by rw [feather B hB hE X]; exact hw,feather B hB hE X _ _⟩
omit hB hE
variable (hp:Lot){D':Lot}
noncomputable def soared (H:Wings O B i k D')(K:KernelChoices)(h: O.Branches K su)(p q:ℝ)(X:Malt D' N): Malt (rimH D' O) N:= ⟨arborn (Pike O 0) K (powerV B O i k) (origin _) p q X.val,honorable (Pike O 0) _ (powerV B O i k) (origin _) p q H.small H.large h H.stake X⟩
lemma flying(H:Wings O B i k D')(G:Wings O B i j D')(p q:ℝ)(X:Malt D' N): Tide.look (Pike O 0) K (powerV B O i j) p q (Agate.visit (origin _) X)= Agate.visit (origin _) (soared B H K hk p q X):=by
    rw [← G.realw]; exact victory (Pike O 0) K (powerV B O i k) (origin _) p q H.small H.large hk (powerV B O i j) G.small G.large H.stake G.stake _ (staysP X)
lemma unic (H:Malt D' N)(V Q':Malt (rimH D' J) N)(p q:ℝ)(he:TrackF J K B p q i H V)(hp:TrackF J K B p q i H Q'): V=Q':=by obtain ⟨s,h,h',ht⟩:= ((gravity (rimH D' J) (finC J B (i+1)) (finH ..)).and (he.and hp)).exists; exact reading (origin _) h (h'.symm.trans ht)
include hB hE hk
lemma linkedF (p q:ℝ)(Y:Malt D' N)(i:ℕ): ∃ X:Malt (rimH D' O) N,TrackF O K B p q i Y X:=by
   have H:= flightH B hB hE D' i; obtain ⟨r,hr⟩:= H.exists; refine ⟨soared B hr _ hk p q Y,H.mono fun k h=> flying B hk hr h p q Y⟩
end IV
end Rails
end YM.QCD.Acre
