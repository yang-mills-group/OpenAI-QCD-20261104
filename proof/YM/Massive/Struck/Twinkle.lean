import YM.Massive.Struck.Sail
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
variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (Y: Code c N)
namespace Carrier
variable {b:Flavor N}(φ:ℝ) (z s:ℂ)
private lemma addresses (U V:RegularAddress c)(h:U.site=V.site)(he:U.support=V.support):U=V:=by cases U; cases V; congr
lemma sym (Y:Voice c N)(hp:Enn P b L x ρ r (duo Y.P Y.K)): Crossing Y.P ∧ MixedP Y.K:=by
     obtain ⟨f,g,hp,_⟩:=hp; have H:=hp.pan; have hx p (k:Spike) g (h:Warrant p g k):=H.turns p g k h
     refine ⟨⟨⟨H.refr.main,fun i U k he=> (H.flavors k he U).ease i,fun i U=> (H.real U).ease i⟩,?_⟩,⟨H.refr.plug,fun i U k he=> (H.flavors k he U).voyage i,fun i U=>(H.real U).voyage i,?_⟩⟩
     · intro s k g he; obtain ⟨e,j,h⟩:=hx s k g he; exact ⟨e,fun i=>⟨addresses _ _ ((h 1).site i) ((h 1).poseE i),fun U=> (h U).ease i⟩⟩
     intro s g k he; obtain ⟨e,j,h⟩:=hx s k g he; exact ⟨j,fun i=>⟨(h 1).current i,(h 1).inv i,fun U=>(h U).voyage i⟩⟩
lemma paysReg (Z:Voice c N) (h:Enn P b L x ρ r (duo Z.P Z.K)): Z.K.Reg P.threshold:=by
    obtain ⟨f,g,hz,_⟩:=h; exact ⟨hz.waveP.oblige,hz.waveP.budget,hz.waveP.chair,hz.waveP.permits⟩
lemma crossP (G:Gem c N I)(h:Crossing G): CrossP G:=⟨h.blank.gauge,fun i U=> fitP _ (h.blank.num i U),h.blank.real,h.rays⟩
def Lurch (G: Gem c N I)(Q:I→Dye): Prop:= CrossP G ∧ ∀ p k g, Warrant p g k → ∃ e:Equiv.Perm I, ∀ i, Q (e i)=Q i ∧ G.addr (e i)=rotateL (G.addr i) p ∧∀ U, Diode N p k g (G.view i (sky p U))= G.view (e i) U
def Lurk (G: Rail c N I)(Q:I→Dye): Prop:= Charm G ∧∀ p k g, Warrant p g k→∃ e:Equiv.Perm I,Fibre.Swing p k g e G∧ ∀ i, Q (e i)=Q i
lemma fromG (G: Gem c N I)(p:Dye)(h:CrossP G): Lurch G (fun _=>p):=by refine ⟨h,?_⟩; intro p k g he; obtain ⟨e,hx⟩:=h.rays _ _ _ he; exact ⟨e,fun i=>⟨rfl,hx i⟩⟩
lemma fromR (G: Rail c N I)(p:Dye)(h:Charm G): Lurk G (fun _=>p):=by refine ⟨h,?_⟩; intro p k g he; obtain ⟨e,hx⟩:=h.turn _ _ _ he; exact ⟨e,hx,fun _=>rfl⟩
lemma ByGrit (G: Gem c N I)(Q:I→Dye)(h:∀ i,Grit (G.view i))(hp:∀ (p:Strut c) k g, Warrant p g k→ ∃ e:Equiv.Perm I,∀ i, Q (e i)=Q i ∧G.addr (e i)=rotateL (G.addr i) p∧∀ U,Diode N p k g (G.view i (sky p U))= G.view (e i) U): Lurch G Q:=by
     refine ⟨⟨fun i=> (h i).gauge,fun i=>(h i).flex,fun i=>(h i).real,?_⟩,hp⟩; intro p k g h; obtain ⟨e,he⟩:=hp p k g h; exact ⟨e,fun i=>(he i).2⟩
lemma lurkPin (G:Gem c N I)(P:I→Dye)(t:ℝ)(h:Lurch G P): Lurch (ampE G t) P:=by
    refine ByGrit _ P (fun i=> grip _ ⟨h.1.gauge i,h.1.num i,h.1.real i⟩ t) (fun p k g hh=>?_) -- implicit
    obtain ⟨e,he⟩:= h.2 p k g hh; exact ⟨e,fun i=>⟨(he i).1,(he i).2.1,fun U=>(eSM _ (OrbitG.phare _) t _).trans (congr_arg (t • ·) ((he i).2.2 U))⟩⟩
lemma lurkRise (G: Gem c N I)(P:I→ Dye)(h:Lurch G P):Lurch (loggem G) (growth P):=by
    refine ⟨wake G h.1,fun p k g hh=>?_⟩; obtain ⟨e,he⟩:= h.2 p k g hh; let E:=Equiv.prodCongr e (Equiv.refl Tw)
    exact ⟨E,fun i=>⟨congr_arg ((digit i.2) • ·) (he i.1).1, wakeK G e p k g hh (fun i=> (he i).2) i⟩⟩
lemma lurkLog (G:Gem c N I)(P:I→ Dye)(t:ℝ)(h:Lurch G P): Lurch (solvent (ampE G t) P 1 1) (growth P):=by rw [solvent_core]; exact lurkRise _ _ (lurkPin _ _ t h)
lemma lurks (G:Rail c N I)(P:I→Dye)(t:ℝ)(h:Lurk G P): Lurk (watt G (t:ℂ)) P:=by
    refine ⟨wattCharm _ h.1 t,fun p k g hh=>?_⟩; obtain ⟨e,he,hP⟩:= h.2 p k g hh; exact ⟨e,fun i=> ⟨(he i).1,(he i).2.1,fun U=>(eSM _ (OrbitG.phare _) t _).trans (congr_arg (t • ·) ((he i).2.2 U))⟩,hP⟩
lemma lurkWeave (G:Gem c N I)(X:Gem c N Ω)(f:I→Dye)(g:Ω→Dye)(h:Lurch G f)(he:Lurch X g):Lurch (weave G X) (Sum.elim f g):=by
    apply ByGrit; · rintro (i|i); exact ⟨h.1.gauge i,h.1.num i,h.1.real i⟩; exact ⟨he.1.gauge i,he.1.num i,he.1.real i⟩
    intro p k g hp; obtain ⟨e,h⟩:=h.2 p k g hp; obtain ⟨d,hr⟩:= he.2 p k g hp; exact ⟨Equiv.sumCongr e d,fun i=>by cases i; exact h _; exact hr _⟩
lemma lurkWheel (G:Rail c N I)(X:Rail c N Ω)(f:I→Dye)(g:Ω→Dye)(h:Lurk G f)(he:Lurk X g): Lurk (tie G X) (Sum.elim f g):=by
    have hp (p:Strut c)(k:Spike)(d:Site c→ℂ)(hp:Warrant p d k): ∃ w, Fibre.Swing p k d w (tie G X) ∧ ∀ i, Sum.elim f g (w i)=Sum.elim f g i:=by
           obtain ⟨e,h1,h₂⟩:=h.2 p k d hp; obtain ⟨v,hv,hM⟩:= he.2 p k d hp; refine ⟨Equiv.sumCongr e v, ?_,?_⟩
           · rintro (i|i); exact h1 i; exact hv i
           rintro (i|i); exact h₂ i; exact hM i
    refine ⟨⟨fun i=>by cases i; exact h.1.tone _; exact he.1.tone _,?_⟩,hp⟩; intro p k g he; obtain ⟨e,hh,_⟩:= hp p k g he; exact ⟨e,hh⟩
lemma lurkParade [Countable I][Countable ι] (G:Gem c N I)(T:Rail c N ι)(Q:I→Dye)(P:ι→Dye)(h:Lurch G Q)(hp:Lurk T P): Villa.PantryX c N t Q P (duo G T):=by
    refine ⟨⟨h.1.gauge,fun i=>(hp.1.tone i).gauge⟩,?_,fun U=>Villa.permanence _ _ _ (fun i U=> h.1.real i U) (fun i U=>(hp.1.tone i).real U) U,fun W hv U=> Villa.permanence _ _ _ (fun i U=> h.1.num i U W hv) (fun i U=>(hp.1.tone i).flex U W hv) U⟩ -- permanence signature maybe requires [Countable]
    intro v g k hh; obtain ⟨e,he⟩:= h.2 v k g hh; obtain ⟨d,hK,hh⟩:= hp.2 v k g hh; exact ⟨e,d,fun i=> (he i).1,hh,fun U=> ⟨Work.H03.flags_send ..,fun i=>congr_arg RegularAddress.support (he i).2.1,fun i=>congr_arg RegularAddress.site (he i).2.1,fun i=>(hK i).1,fun i=>(hK i).2.1,fun i=>(he i).2.2 U,fun i=>(hK i).2.2 U⟩⟩
local notation "T!"=>Desk Y P b L x ρ
variable (hp: Desk Y P b L x ρ)
include hp
lemma lyr : Lurch Y.high (knot ∘ Y.ad):=by
    refine ⟨hp.eve,fun p k g he=>?_⟩; obtain ⟨e,h⟩:= hp.carries p k g he; exact ⟨e,fun i=>⟨congr_arg knot (h i).1,(h i).2⟩⟩
lemma pawn : Lurk Y.top (knot ∘ Y.up):=by refine ⟨hp.wish,fun p k g he=>?_⟩; obtain ⟨e,h,he⟩:= hp.rises p k g he; exact ⟨e,h,fun i=> congr_arg knot (he i)⟩
omit hp in
lemma quietHue (X:Rail c N I)(P:I→ Dye): hueW X (fun i=> Struck.pigment (P i) 1 1)=watt X 1:=by unfold hueW watt; simp_rw [Carrier.quiet]
lemma Company : Lurch (PackageE Y φ 1 1) (turf Y) ∧ Lurk (PackageK Y φ 1 1) (sideE Y):=by
    obtain ⟨h,hq⟩:= sym _ hp.base; refine ⟨lurkWeave _ _ _ _ (fromG Y.master.P 0 (crossP _ h)) (lurkWeave _ _ _ _ (lurkLog _ _ _ (fromG Y.canonical pegE (rentCross c Y.focus))) (lurkWeave _ _ _ _ (lurkLog _ _ _ (fromG _ pegE hp.arg)) (lurkLog _ _ _ (lyr Y hp)))),?_⟩
    have hV:= lurks Y.top (knot ∘ Y.up) (φ⁻¹^3) (pawn Y hp); unfold PackageK; simp_rw [Carrier.quiet]; apply lurkWheel; · exact fromR _ _ (Fibre.gear Y.master.K hq)
    exact lurkWheel _ _ _ _ (lurks _ _ (1:ℝ) (lurks Y.prime _ _ (fromR _ _ hp.warm))) (lurks _ _ 1 hV)
lemma ship : Villa.PantryX c N P.threshold (turf Y) (sideE Y) (Mast Y φ):= lurkParade _ _ _ _ (Company Y φ hp).1 (Company Y φ hp).2
omit hp
lemma closureK (Y:Rail c N ι)(g:ι→ℂ)(t:ℝ)(h:Y.Reg t): (hueW Y g).Reg t:= ⟨fun i=> (watt_reg Y h (g i)).uses i, fun i=> (watt_reg Y h (g i)).reads i,fun i V=>(watt_reg Y h (g i)).role i V, fun i U=>(watt_reg Y h (g i)).buys i U⟩
lemma Cart (X:Rail c N I)(Y:Rail c N ι)(h:X.Reg t)(hp:Y.Reg t): (tie X Y).Reg t:= by
    refine ⟨?_,?_,?_,?_⟩
    · rintro (i|i); exact h.uses i; exact hp.uses i
    · rintro (i|i); exact h.reads i; exact hp.reads i
    · rintro (i|i); exact h.role i; exact hp.role i
    rintro (i|i); exact h.buys i; exact hp.buys i
include hp
lemma health_z : (PackageK Y φ z s).Reg P.threshold:=by exact Cart _ _ (paysReg Y.master hp.base) (Cart _ _ (watt_reg _ (watt_reg Y.prime hp.low _) _) (closureK _ _ _ (watt_reg Y.top hp.high _)))
omit hp
lemma shadeColor  (f:Grid c→ EvenA c N)(w:ℂ)(h:shadeG f):shadeG (w • f):=by
    intro U g; exact congr_arg Subtype.val ((complexFactor w (Lat.rotates N g) (f (Lattice.gauge g U))).trans (congr_arg (w • ·) (show sways (Lat.rotates N g) _=_ from Subtype.ext (h ..))))
abbrev StrollE (G: Gem c N I): Prop:=∀ i,shadeG (G.view i)
abbrev StrollK (G: Rail c N I): Prop:=∀ i,shadeG (G.warp i)
lemma walkE (X:Gem c N I)(Y:Gem c N ι)(hp:StrollE X)(he:StrollE Y): StrollE (weave X Y):=by rintro (i|i); exact hp i; exact he i
lemma walkK (X:Rail c N I)(Y:Rail c N ι)(hp:StrollK X)(he:StrollK Y): StrollK (tie X Y):=by rintro (i|i); exact hp i; exact he i
lemma takeM (G:Gem c N I)(P:I→Dye)(a:ℝ)(h:CrossP G): StrollE (solvent (ampE G a) P z s):= fun i=> sepC _ (shadeColor _ _ (shadeColor _ _ (h.gauge i.1))) i.2
lemma hireK (G:Rail c N I)(f:I→ℂ)(h:Charm G)(a:ℝ): StrollK (hueW (ampK G a) f):=fun i=> shadeColor _ _ (shadeColor _ _ (h.tone i).gauge)
include hp
lemma status : Rise.Reframe (Cane Y φ z s):=by
    obtain ⟨hr,h⟩:= sym _ hp.base
    constructor
    · exact walkE _ _ hr.blank.gauge (walkE _ _ (takeM z s _ _ _ (rentCross c _)) (walkE _ _ (takeM z s _ _ _ hp.arg) (takeM z s _ _ _ hp.eve)))
    exact walkK _ _ h.gauge (walkK _ _ (hireK Y.prime _ hp.warm _) (hireK Y.top _ hp.wish _))
local notation "q₁"=> (1/8:ℝ)
lemma eclipse (hR:P.B=highR L x)(hS:Budget Y P L x ρ φ a u p q₁ r) (he:modulus P p r)(hz:‖z‖ ≤1)(hs:‖s‖≤1)(ht:1 ≤ fan L ρ x) : (Cane Y φ z s).Wave P.threshold:=by obtain ⟨f,g,t,k,h⟩:= table Y φ hS hR hp; exact regimen (PackageE Y φ z s) _ (Licence_g (show Licence P q₁ (massPay P L x r p) (fan L ρ x) (PackageE Y φ z s) from ⟨rings Y f g t k P,sails Y φ z s f g t k h he hz hs (by norm_num : 0≤(1/8:ℝ)) ht ⟩)) (health_z Y φ z s hp)
-- when enhancing real costs, Penta.K. Ensure Fleck under any particles θ. G loggem at sphere; use hp explicitly
omit hp
lemma kneel_low (G:Gem c N I)(t:ℝ)(f:I→Dye)(g:I→ℝ)(b:Bool)(he:LowFare G P q t u g)(h:modulus P u u)(hp:1≤t)(ht:0≤q)(hv:(∀ i,Grit (G.view i)))(hM:∀ i,Mint b (G.view i) (G.addr i).site (G.addr i).support) (i:I×Tw): let T:= solvent G f 1 1; Nonwrapping (T.addr i).support (T.addr i).site→ Fleck P (T.addr i).support (T.addr i).site b (T.view i) t (logBudget P g i):=by
   rw [solvent_core]; intro T hV; have hh:= h u (Or.inl le_rfl); refine puff (b':=b) _ (gritE _ (hv i.1) i.2) ((logFare G g he ht hp hh.1 hh.2).2 i) ?_ (zero_lt_one.trans_le hp) hV (T.addr i).anchor; exact wishBill G g he ht hp hh.1 hh.2 _ hM i
include hp
local notation "L₀"=> fan L ρ x
-- ∀ i full table master incl Wrapping boost call. unmasked Fleck accepted on old unmarked; use `fromFeast`, apply.Bool.false.
abbrev Pawnee (G:Gem c N I)(P:BudgetPoint)(t:ℝ)(f:I→ℝ)(h:I→Bool) := ∀ i,Nonwrapping (G.addr i).support (G.addr i).site → Fleck P (G.addr i).support (G.addr i).site (h i) (G.view i) t (f i)
omit hp
lemma Pawnee.join (G:Gem c N I)(Z:Gem c N ι)(a:I→ℝ)(b:ι→ℝ)(U:I→Bool)(V:ι→Bool) (h:Pawnee G P t a U)(he:Pawnee Z P t b V): Pawnee (weave G Z) P t (Sum.elim a b) (Sum.elim U V):=by rintro (i|i); exact h _; exact he _
lemma Crisp (G:Gem c N I)(H:CrossP G):∀ i,Grit (G.view i):=fun i=> ⟨H.gauge i,H.num i,H.real i⟩
lemma leFee (G:Gem c N I)(f:I→ℝ)(h:∀ i, Nonwrapping (G.addr i).support (G.addr i).site → Feast P (G.addr i).support (G.addr i).site b (G.view i) t (f i)): Pawnee G P t f (fun _=>false):=by
     intro i hi; have hh:= Brick.fromFeast (G.addr i).site b t (f i) (h i hi); exact { hh with rack:= fun h=> False.elim (Bool.noConfusion h) }
include hp
lemma flower (hS:Budget Y P L x ρ φ a u p q₁ r) (he:modulus P p r)(f:Y.master.ι→ℝ)(g: Site c×Flavor N→ℝ)(t:Y.A→ℝ)(w:Y.B→ℝ) (hf:SeatsE φ Y P L x ρ q₁ r p b f g t w)(ht:1 ≤ L₀): Pawnee (PackageE Y φ 1 1) P L₀ (rings Y f g t w P) (kind Y):=by
     have hh : modulus P p p:=fun _ hr=> he _ (Or.inl (or_self_iff.mp hr)); have hl: modulus P r r:=fun _ hr=> he _ (Or.inr (or_self_iff.mp hr))
     refine Pawnee.join _ _ _ _ _ _ (leFee Y.master.P f hf.prime) (Pawnee.join (rent Y φ 1 1) _ _ _ _ _ ?_ (Pawnee.join (louvre Y φ 1 1) (heights Y φ 1 1) _ _ _ _ ?_ ?_))
     · intro i; refine kneel_low _ (fan L ρ x) (fun _=> pegE) g _ hf.rent hl ht (by norm_num) (fun i=> grip (Y.canonical.view i) (Crisp Y.canonical (rentCross c _) i) _) (Bite.mint _ hS.rent) i
     · intro i; exact kneel_low _ (fan L ρ x) (fun _=> pegE) t _ hf.cool hh ht (by norm_num) (fun i=> grip _ (Crisp Y.low hp.arg i) _) (Bite.mint _ hS.low) i
     intro i; exact kneel_low _ (fan L ρ x) _ w _ hf.heat hh ht (by norm_num) (fun i=> grip _ (Crisp Y.high hp.eve i) _) (Bite.mint _ hS.high) i
end Carrier
end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.Carrier.ship
#print axioms YM.QCD.Struck.Library.Carrier.flower
