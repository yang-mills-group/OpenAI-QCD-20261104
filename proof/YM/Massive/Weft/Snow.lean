import YM.Massive.Weft.Sale
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Weft
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
variable {c f Cv F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
variable {I Ω ι β: Type}
open Struck Struck.Library
open Finch Carrier

variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (Y0: Code c N) -- independent shape
set_option quotPrecheck false
variable (Y:Ruby.Hue c N Ω)(X:Gem c N I)(Q:Ruby.Hue c N I)(K: ℝ)
variable {g:Site c→ℂ}(L':I→Dye)(L0:Ω→ Dye)
open Ruby
open Warmlet
variable (E G :Gem c N I)(U:Grid c)(i:I)(w u:ℝ)
variable {E₀:Ruby.Hue c N I}(X:Gem c N Ω)
noncomputable def frost (i:I):ℂ:= - ↑(Reggae.river c N (E.view i 1))
abbrev farm (f:I→ℂ): ℂ:= ∑' i,f i*frost E i
lemma visitors (i:I) : frost E i • (1:EvenA c N) = sewShelf E i:=by unfold sewShelf Reggae.ocean frost; rw [neg_smul,_root_.neg_apply,Reggae.gets,Complex.coe_smul]
lemma snowPoint (hp: Lurch E L')(he: E.Gather): Lurch (Pith.dusting E) L' ∧ PatchH (Pith.Tall.branches E t) L':=by
    let B:= Pith.Tall.branches E t; refine ⟨⟨snowy E hp.1 he,fun s k g h=>?_⟩,⟨fun i=> ⟨Tall.gaugeT E i,Tall.phaseT E i, fun U=> Tall.solace E i U hp.1⟩, fun s k g h=>?_⟩⟩
    · obtain ⟨u,ht⟩:= hp.2 s k g h; exact ⟨u,fun i=>⟨(ht i).1,(ht i).2.1,fun U=> sparkleM E i U hp.1 he u k h (fun i=>(ht i).2)⟩⟩ -- fix
    obtain ⟨u,hp'⟩:=hp.2 s k g h; exact ⟨u,fun i=>⟨(Tall.bridge E i (1:Grid c) hp.1 he u h (fun i=>(hp' i).2)).1,fun U=>(Tall.bridge E i U hp.1 he u h (fun i=>(hp' i).2)).2⟩,fun i=>(hp' i).1⟩
lemma snowB (hp:CrossP E)(hu:Licence P v w t E)(ht:0<t): Bite (Pith.dusting E) P t ((2+jointFee N)*w) v true:=by
    have hG:= Licence_g hu; obtain ⟨f,hf,h⟩:=hu.zone; refine ⟨fun i=>(2+jointFee N)*f i,valued_mult E.addr f hf ?_,fun i=> ?_⟩; · have h:= joint_valid N; linarith
    exact ⟨renown E i (h i) ht,zero_mud E i hp, fleckIssue E i hp hG ht (h i)⟩
abbrev branchCost (P:BudgetPoint)(N:ℕ)(v r:ℝ):= reFare P ((1+jointFee N)*v) r
lemma luminosity (hp: Lurch E L')(hu:Licence P v w t E)(ht:0<t)(he:r+2≤v)(hh:0≤r): CostTall (Tall.branches E P.threshold) P t r (branchCost P N w r) L':= by
     refine ⟨Tall.charges E, (snowPoint L' E hp (Entr.Licence_g hu)).2,?_⟩
     obtain ⟨f,hf,h⟩:= (wells E hu he (le_refl w)).zone; exact ⟨_, Tall.bank E f h hh hf,fun i U=> Tall.utility E i U (h i) ht⟩
lemma flora (hp:Licence P v w t E)(ht:0≤v)(he:0≤t): Summable (fun i=> ‖frost E i‖):= by
   obtain ⟨g,hg,h⟩:= hp.zone; refine (sumRide _ _ _ hg (fun i=> (h i).travel) ht).of_nonneg_of_le (fun i=>norm_nonneg _) fun i=> ?_
   rw [frost,norm_neg,Complex.norm_real]; exact (Reggae.sees (E.addr i).site _ he).trans ((h i).sizeU 1 (flat_ok ..))
lemma parcel (hp:Summable (fun i=> ‖frost E i‖))(f:I→ℂ)(h:∀ i, ‖f i‖≤1): Summable (fun i=> f i*frost E i):= Summable.of_norm_bounded hp fun i=> (norm_mul _ _).trans_le (mul_le_of_le_one_left (norm_nonneg _) (h i))
lemma ice (hp:Summable (fun i=> ‖frost E i‖))(f:I→ℂ)(h:∀ i, ‖f i‖≤1): HasSum (fun i=> f i • sewShelf E i) (farm E f • (1:EvenA c N)):=by
   apply ((parcel E hp f h).hasSum.smul_const _).congr_fun; intro i; rw [← visitors, mul_smul]
lemma snowEq (U:Grid c)(hp:Lurch E L')(hf:Licence P v w t E)(he:r+2 ≤ v)(hL:1 ≤ t)(hx:0 ≤ r): Patron.total E P.threshold U= farm E (fun _=>1) • (1:EvenA c N) + Patron.total (Pith.rentGem (c:=c) (Pith.gaugeMass E)) P.threshold U + Patron.total (dusting E) P.threshold U+Calm.netT (Pith.Tall.branches E P.threshold) U:=by
   have h:0 < t:=zero_lt_one.trans_le hL; have hv:0≤v:=by linarith
   obtain ⟨h1,h2,hY⟩:=luminosity L' E w hp hf h he hx; obtain ⟨g,hg,hQ⟩:= hf.zone; have hu := ice E (flora E w hf hv h.le) (fun _=>1) (by simp);
   have hr:= rentRecept E U hg hQ hv h hp.1; let Q:= P.threshold; let p:=Tall.branches E Q; let y(t:I):= p.mean t U; have hw:= readable p Q U h1 hY hx hL
   refine ((((hu.add hr).add (Stew.permits _ (snowB E w hp.1 hf h).law h hv U).hasSum).add hw.1.hasSum).congr_fun (g:=letters E P.threshold U) ?_).tsum_eq
   intro i; rw [Tall.golden E i U,one_smul]; abel
end YM.QCD.Weft
