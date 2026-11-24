import YM.Massive.Aperture.Mass
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Aperture
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
open Struck Struck.Library
open Finch Carrier

variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (X:ℂ→ℂ→ Patron.Rail c N I)(Y:ℂ→ℂ→Ruby.Hue c N Ω)
open Ruby Weft High
set_option quotPrecheck false
local notation "Tz"=>P.threshold
variable {b Y₁: ℝ}{s z U:ℂ}{W₁:Grid c}
local notation "νT"=> (1/8:ℝ)
open Conductor Conductor.Quant Meridians
open Pith AnalyticBridge.VerifiedReset
-- Off-mask Talculus.
abbrev fringe (c:Side)(u:Flavor N → ℝ)(p:BudgetPoint): Ruby.Hue c N (Site c×Flavor N):= Entr.offT (rentGem u) p.threshold
abbrev fTax (t s:ℝ)(u:Flavor N→ℝ):ℝ:= Real.exp t*∑ i, priceL u s i
abbrev coreTax : ℝ:=7*(1/32)+1
variable (u v:Flavor N→ℝ) (U:Grid c)
lemma packed (E:Gem c N Ω)(h:E.Gather): (offT E p).Tall p:=by
    refine ⟨fun i U V he hQ=>congr_arg₂ (·-·) (h.sees i _ _ he) (clearUse _ i (h.sees _) _ U V he hQ),fun i=>(h.reads i).sub (masked_measurable _ _ _ (h.reads _)),fun i U hN hx=> hN ?_,fun i U=> wingsZ _ _ _ (h.role i U) (licit E h i U)⟩
    change E.view i U-_= _; change Healthy p (E.addr i).support U at hx; rw [letters,masked_eq _ _ _ _ hx,sub_self]
lemma pledgeZ (E:Gem c N Ω)(hp:CrossP E): PatchH (offT E t) (fun _=>Carrier.pegE):=by
    refine ⟨fun i=>⟨fun U k=> ?_,fun U g h=>?_,fun U=>?_⟩,fun s k g h=>?_⟩
    · have he:sways (Lat.rotates N k) (E.view i (gauge k U))=E.view i U:=Subtype.ext (hp.gauge i U k); refine congr_arg Subtype.val (show sways _ (_- _)=_ from ?_); rw [map_sub]; exact congr_arg₂ _ he (sprayer _ _ _ _ _ _ _ _ (by unfold Healthy; rw [gauge_flags]) he)
    · change sways _ (_-_)=_; rw [map_sub]; have hx:= hp.num i U g h; exact congr_arg₂ _ hx (sprayer _ _ _ _ _ _ _ _ Iff.rfl hx)
    · change Regal c N (_-_)=_; rw [map_sub]; have he:=hp.real i U; exact congr_arg₂ _ he (sprayer _ _ _ _ _ _ _ _ Iff.rfl he)
    obtain ⟨e,he⟩:= hp.rays s k g h; have hf(i):=(he i).1; refine ⟨e,fun i=>⟨?_,fun U=>?_⟩,fun _=>rfl⟩
    · exact congr_arg RegularAddress.support (hf _)
    change Diode _ _ _ _ (_-_) =_; have hh: (E.addr (e i)).support=_:= (show (E.addr (e i)).support=(E.addr i).support.image (act s) from congr_arg RegularAddress.support (hf _)); have hz:= (he i).2 U; rw [map_sub]; exact congr_arg₂ _ hz (sprayer _ _ _ _ _ _ _ _ (hh.symm ▸ (healthy_image ..).symm) hz)
lemma priced (h:0<t): CostTall (fringe c u P) P t a (fTax a t u) (fun _=> pegE):=by
    let X:= rentGem (c:=c) u; let Y:= offT X P.threshold; let f (i:Site c×Flavor N):= priceL u t i.2; have hv:= rentPaid c u (t:=t) (p:=P) (q:=a); have hh(i:Site c × Flavor N):Woven i.1 {i.1} P t (X.view i) (f i):= Pith.moneyL i.2 i.1 _ P h
    refine ⟨packed _ (Licence_g (show Licence P a (fTax a t u) t X from ⟨f,hv,fun i=> hh i⟩)),pledgeZ _ (rentCross c u),f,fun i=>?_,fun i U=>?_⟩
    · have hk(s:Site c×Flavor N): s.1=i↔ i∈Y.bud s:= by change s.1=i ↔ _∈{s.1}; simp only [mem_singleton]; exact eq_comm
      change SumBudget (fun j=> if i∈Y.bud j then _ else _) _; simp_rw [← hk]; exact hv i
    apply le_trans (b:=Sen i.1 t (Y.mean i U)) (shot (lens _) _ _ h); change Sen i.1 t (X.view i U-letters X P.threshold U i) ≤ _
    by_cases hv:Healthy P.threshold (X.addr i).support U; · rw [letters,masked_eq _ _ _ _ hv,sub_self,← measures,map_zero,norm_zero]; exact (hh _).travel
    rw [letters,masked_ne _ _ _ _ hv,sub_zero]; exact Pith.approved i.2 i.1 _ P h
lemma see_all : ingredient c u= Calm.netT (fringe c u P) U+ Patron.total (rentGem (c:=c) u) P.threshold U:=by
    let X:= rentGem (c:=c) u; unfold Calm.netT Patron.total; rw [tsum_fintype, tsum_fintype, ← sum_add_distrib]; refine sum_congr rfl fun i _=> ?_ ; exact (sub_add_cancel (X.view i U) _).symm
lemma oneFlux : ingredient c u= Patron.total (rentGem (c:=c) u) P.threshold 1:=by
    unfold Patron.total; rw [tsum_fintype]; refine sum_congr rfl fun i _=>?_ ; exact (masked_eq _ _ _ _ (flat_ok ..)).symm -- he
-- seed bill startup lemmas with hPhysical scaled. choose φ and κ&gt from increased.World.Pure.La etc
variable (S: Voice c N)
abbrev Htour (z s:ℂ)(Z:Ruby.Hue c N ι):= wet Z fun _=> Struck.pigment pegE z s
abbrev morningR (S:Voice c N):=fun (_ _:ℂ)=> S.K
abbrev Pique (p:BudgetPoint):=fun z s:ℂ=>Htour z s (fringe c u p)
abbrev trailStamp (P:BudgetPoint)(X: Voice c N):=graffiti (morningR X) (Pique (c:=c) u P) P.threshold
local notation "fZ"=> fan L η x
variable {b':Flavor N}
variable (hp:Enn P b' L x η νT (duo S.P S.K))
include hp
variable {z':ℂ}
lemma seedG (h: Quits S.K P.B 1 (taxK L x 8) 1 (fan L η x))(hh:1 ≤ fZ): Seed (morningR S) P (taxK L x 6) (7*(1/32)) fZ z':=by
    have hv:= Carrier.paysReg S hp; have hx:= (Carrier.sym S hp).2; have he:=Fibre.gear _ hx
    refine ⟨constantArc _,fun _ hh=> ⟨fun _ i _=>he.tone i,fun p k g h=>?_⟩,hx,fun z s ht hz=>?_⟩ -- rotate
    · obtain ⟨e,h⟩:=he.turn p k g h; exact ⟨e,fun _ _=>h⟩
    have h₀ : 1≤taxK L x 8:=Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos L (1/3) x).le); have hr:= ensures _ h h₀ zero_le_one hh; refine ⟨hv,Kites.tide _ (liveK _ h (by norm_num) (fan_pos ..) le_rfl) (Real.exp_pos _).le ?_,fun V=> (lastK _ _ _ (hr V))⟩
    exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by norm_num : (6:ℝ)≤8) (fan_pos ..|>.le))
variable {z' : ℂ} (hT:Switch (N:=N) P L x η w D a) (hK:Quits S.K P.B 1 (taxK L x 8) 1 (fan L η x))(hU:fTax coreTax (fan L η x) u ≤1)
include hT hK
include hU in
lemma sprayerR : Seed (trailStamp u P S) P (taxK L x 4) (3/16) fZ 0:= climbed _ _ hT _ (priced u (fan_pos ..)) (fun _ => Carrier.fisc) (fun _=> Nat.zero_lt_one) hU le_rfl (seedG S hp hK hT.count)
lemma paidR (z s:ℂ) (hz:‖z‖≤1)(hs:‖s‖≤1): heartK (trailStamp u P S z s) P.threshold U=heartK S.K P.threshold U *exp ((Struck.pigment pegE z s) • (Calm.netT (fringe c u P) U)):=by
    have hpX:= (seedG S hp hK hT.count (z':=0)).scene z s hz hs; let Y:=fringe c u P; let v:=Struck.pigment pegE z s; have hu:= (springY Y _ (fun _=> Carrier.fisc) (priced (a:=coreTax) u (fan_pos L η x)) (fun _=> Nat.zero_lt_one) (b0:=0)); obtain ⟨hz',hx⟩:= hu.hearth z s hz hs; have hh:= heartEarned (morningR S) (Pique u P) (constantArc _) hu.prog hz' hx hT.count (by unfold coreTax; norm_num) (hpX.awake U)
    refine hh.trans ?_; congr 2; exact hailH Y U v Summable.of_finite
omit hp hT hK
lemma scaledRent (y:ℝ): Calm.netT (fringe c (y • u) P) U=y • Calm.netT (fringe c u P) U:=by
    rw [show Calm.netT (fringe c u P) U=ingredient c u- Patron.total (rentGem (c:=c) u) P.threshold U from eq_sub_of_add_eq (see_all u U).symm, show Calm.netT (fringe c (y • u) P) U= _ from (eq_sub_of_add_eq (see_all (P:=P) (y • u) U).symm), scaling,smul_sub]; congr 1
    rw [show rentGem (c:=c) (y • u) = _ from (clearsL (c:=c) u y).symm]; exact (Library.spar _ _ U Summable.of_finite).tsum_eq
end YM.QCD.Aperture
#print axioms YM.QCD.Aperture.sprayerR
