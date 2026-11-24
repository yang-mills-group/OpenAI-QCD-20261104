import YM.Massive.Struck.Yule
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Struck
open Acre
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
open Stew Ursell
open Blaze Shells Sands Dust King Lapis Sienna Fare Octave Fount Grove Planned.JetPort Tidings Entr PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit -- Badge from Acre below
open Acre Rails
open Finset Coat Grass NormedSpace
open MeasureTheory Massive.Filament Pith Fibre Fused
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
variable {I Ω ι β: Type}
namespace Library
variable {t : ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (Y: Code c N) -- independent shape
set_option quotPrecheck false
namespace Carrier
-- amp scaling. use s ∈positive ℝ at 0 even if pEARTH below.L.
def ampE (G:Gem c N I)(a:ℝ):= wind G fun _ => (a:ℂ)
def ampK (G:Rail c N I)(a:ℝ):= watt G (a:ℂ)
-- for proof consider θ≥1 etc separately.
variable (φ:ℝ) (z s:ℂ)
def solvent (G:Gem c N I)(a:I→Dye) (z s:ℂ): Gem c N (I×Tw):= loggem (wind G (fun i=> Struck.pigment (a i) z s))
def knot (n:ℕ):Dye:= (n,3)
def pegE : Dye:= (1,2)
abbrev EIndex (Y:Code c N):= Y.master.ι ⊕ ((Site c × Flavor N) × Tw) ⊕ (Y.A × Tw) ⊕ (Y.B × Tw)
abbrev KIndex (Y:Code c N):= Y.master.β ⊕ Y.E ⊕ Y.F
noncomputable def rent (z:ℂ)(s:ℂ):= solvent (ampE Y.canonical (φ⁻¹^2)) (fun _=>pegE) z s
noncomputable def louvre (z:ℂ)(s:ℂ):= solvent (ampE Y.low (φ⁻¹^2)) (fun _=>pegE) z s
noncomputable def heights (z:ℂ)(s:ℂ):= solvent (ampE Y.high (φ⁻¹^3)) (fun i=> knot (Y.ad i)) z s
-- defeq brittle so define composite.Portal & equations
noncomputable def PackageE (z:ℂ)(s:ℂ): Gem c N (EIndex Y):= weave Y.master.P (weave (rent Y φ z s) (weave (louvre Y φ z s) (heights Y φ z s)))
noncomputable def PackageK (z:ℂ)(s:ℂ): Rail c N (KIndex Y):= tie Y.master.K (tie (watt (ampK Y.prime (φ⁻¹^2)) (Struck.pigment pegE z s)) (hueW (ampK Y.top (φ⁻¹^3)) (fun i=> Struck.pigment (knot (Y.up i)) z s)))
def Cane (z:ℂ)(s:ℂ):=duo (PackageE Y φ z s) (PackageK Y φ z s)
abbrev Mast:= Cane Y φ 1 1
lemma supportsK : (PackageK Y φ z s).addr=(PackageK Y φ 1 1).addr:=rfl
private lemma weaveAddr (A C:Gem c N I)(B D:Gem c N Ω)(h:A.addr=C.addr)(he:B.addr=D.addr) : (weave A B).addr=(weave C D).addr:=by
    change Sum.elim _ _=Sum.elim _ _; exact congr_arg₂ Sum.elim h he
private lemma solvAddr (X:Gem c N I) (d:I→Dye)(z s:ℂ): (solvent X d z s).addr=(solvent X d 1 1).addr:=rfl
lemma supportsE: (PackageE Y φ z s).addr=(PackageE Y φ 1 1).addr:=weaveAddr Y.master.P Y.master.P _ _ rfl (weaveAddr _ _ _ _ (solvAddr _ _ z s) (weaveAddr _ _ _ _ (solvAddr _ _ z s) (solvAddr _ _ z s)))
private lemma wholeEq {G H:Rise c N I ι} (h:G.row=H.row)(hp:G.front=H.front): Villa.evalRise H G.main G.plug=G:=by unfold Villa.evalRise; rw [← h,← hp]
lemma buttress : Villa.evalRise (Mast Y φ) (Cane Y φ z s).main (Cane Y φ z s).plug=Cane Y φ z s:=wholeEq (supportsE ..) (supportsK ..)
-- Accounting. canonical direction pip.
def growth (X:I→Dye)(p:I×Tw):Dye:=digit p.2 • X p.1
def turf : EIndex Y→Dye:= Sum.elim (fun _=>0) (Sum.elim (growth (fun _=>pegE)) (Sum.elim (growth (fun _=>pegE)) (growth (fun i=>knot (Y.ad i)))))
def sideE : KIndex Y→ Dye:=Sum.elim (fun _=>0) (Sum.elim (fun _=>pegE) (fun i=> knot (Y.up i)))
def kind : EIndex Y → Bool := Sum.elim (fun _=>false) (Sum.elim (fun _=>false) (Sum.elim (fun _=>true) (fun _=>false))) -- tag unmarked false? store Fleck false unconditionally with .Me.Mud.Wrap. Off. issue unmarked need all.Mud.C.Wick Feather.S.A on wrapping? Booth.Seed? check.
lemma normal (z:ℕ) (h:2 ≤ z): Ash (knot z):= Or.inr (Or.inr ⟨h, le_rfl⟩)
lemma fisc : Ash pegE:= Or.inr (Or.inl rfl)
lemma grown (n:ℕ)(z:Dye) (h:Ash z): Ash (n • z) := by induction n with|zero=>exact zero_smul ℕ z ▸ Or.inl rfl|succ n ih=>rw [add_smul,one_smul]; exact brightAdd _ _ ih h
lemma quiet (Z:Dye): Struck.pigment Z 1 1=1:=by simp [Struck.pigment]
lemma cords {b:Flavor N}(he:Desk Y P b L x ρ): (∀ x, Ash (turf Y x)) ∧ ∀ x,Ash (sideE Y x):= ⟨fun i=>by rcases i with i|i|i|i; exact Or.inl rfl; exact grown _ _ fisc; exact grown _ _ fisc; exact grown _ _ (normal _ (he.bottom _)), fun i=> by rcases i with i|i|i; exact Or.inl rfl; exact fisc; exact normal _ (he.star _)⟩ -- b
lemma cog (p: Dye)(n:ℕ): Struck.pigment (n • p) z s=(Struck.pigment p z s)^n:=by
       -- lane
       exact map_pow (Struck.lane z s) (Multiplicative.ofAdd p) n
lemma observeK (i:KIndex Y)(U:Grid c): (Cane Y φ z s).plug i U=Struck.pigment (sideE Y i) z s • (Mast Y φ).plug i U:=by
   rcases i with i|i|i
   · change _= Struck.pigment (0,0) z s • _; rw [show Struck.pigment (0,0) z s=1 from (by simp [Struck.pigment]),one_smul]; rfl -- explicit
   · change Struck.pigment _ _ _ • _= _ • (Struck.pigment pegE 1 1 • _); rw [quiet,one_smul]; rfl
   change Struck.pigment _ _ _ • _ = _ • (Struck.pigment (knot (Y.up i)) 1 1 • _); rw [quiet,one_smul]; rfl
lemma solvent_core (G:Gem c N I)(a:I→Dye): solvent G a 1 1=loggem G:=by unfold solvent; simp_rw [quiet]; rw [show wind G (fun _=>1)=G from ?_]; unfold Library.wind; simp
-- defeq Kick proof.Elim.
structure Budget (Y:Code c N)(P:BudgetPoint)(L:Side)(x ρ φ ζ κ p q r:ℝ) : Prop where
   low : Bite (ampE Y.low (φ⁻¹^2)) P (fan L ρ x) p q true
   high : Bite (ampE Y.high (φ⁻¹^3)) P (fan L ρ x) p q false
   rent : Bite (ampE Y.canonical (φ⁻¹^2)) P (fan L ρ x) r q false
   loft : Quits (ampK Y.prime (φ⁻¹^2)) P.B ζ (taxK L x 1) q (fan L ρ x)
   top : Quits (ampK Y.top (φ⁻¹^3)) P.B κ (taxK L x 1) q (fan L ρ x)
lemma notice (G: Gem c N I)(h:I→Dye)(f:I→ℝ)(hp:LowFare G P q t r f)(he:0≤q)(hl:1≤t)(hh:r≤1/8)(hr:2^P.order*r≤1/4)(hz:‖z‖≤1)(hs:‖s‖≤1)(U:Grid c)(i:I×Tw):
    exp (letters (solvent G h z s) P.threshold U i)-1= Struck.pigment (growth h i) z s • (exp (letters (solvent G h 1 1) P.threshold U i)-1):=by
     rw [solvent_core,growth,cog]; exact wand G f hp he hl hh hr (fun i=>_) (fun i=>upperPaint (h i) z s hz hs) U i
private abbrev Stark (G H:Gem c N I)(U:Grid c)(t:ℝ)(Q:I→Dye): Prop:= ∀ i, exp (letters G t U i)-1 = Struck.pigment (Q i) z s • (exp (letters H t U i)-1)
private lemma agreed (U:Grid c)(Q R:Gem c N I)(A B:Gem c N Ω)(f:I→Dye)(g:Ω→ Dye)(h:Stark z s Q R U t f)(he:Stark z s A B U t g): Stark z s (weave Q A) (weave R B) U t (Sum.elim f g):=by rintro (i|i); exact h i; exact he i
private lemma Stark.self (F:Gem c N I)(U:Grid c): Stark z s F F U t (fun _=>0):=by intro i; rw [show Struck.pigment 0 z s=1 from ?_,one_smul]; simp [Struck.pigment]
lemma passport {p:ℝ}(he:0≤q)(hl:1≤ fan L ρ x)(hn:∀ u:ℝ, u≤p∨u≤r → u≤ 1/8 ∧2^P.order*u ≤1/4) (hp: Budget Y P L x ρ φ a u p q r)(hz:‖z‖≤1)(hs:‖s‖≤1)(U:Grid c)(i:EIndex Y): exp ((Cane Y φ z s).reading P.threshold U i)-1=Struck.pigment (turf Y i) z s • (exp ((Mast Y φ).reading P.threshold U i)-1):=by
    let M:=PackageE Y φ z s; let T:= PackageE Y φ 1 1
    suffices h:Stark z s M T U P.threshold (turf Y) by exact h i
    refine agreed z s U _ _ _ _ _ _ (Stark.self z s Y.master.P U) (agreed z s U _ _ _ _ _ _ ?_ (agreed z s U _ _ _ _ _ _ ?_ ?_))

    · obtain ⟨f,hf,h⟩:=hp.rent.law.zone; obtain ⟨ha,hb⟩:= hn _ (Or.inr le_rfl); exact fun i=> notice z s (ampE Y.canonical _) _ f ⟨hf,h⟩ he hl ha hb hz hs U i
    · obtain ⟨f,hf,h⟩:= hp.low.law.zone; obtain ⟨ha,hb⟩:=hn _ (Or.inl le_rfl); exact fun i=> notice z s (ampE Y.low _) _ f ⟨hf,h⟩ he hl ha hb hz hs U i
    obtain ⟨f,hf,h⟩:= hp.high.law.zone; obtain ⟨ha,hb⟩:= hn _ (Or.inl le_rfl); exact fun i=> notice z s (ampE Y.high _) _ f ⟨hf,h⟩ he hl ha hb hz hs U i
end Carrier
end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.Carrier.passport
