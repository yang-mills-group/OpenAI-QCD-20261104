import YM.Massive.Weft.Market
set_option autoImplicit false
set_option linter.unusedSimpArgs false
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
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
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
variable (G':Gem c N Ω)(X':Ruby.Hue c N Ω)(qℓ:ℝ) -- edit
abbrev Lit (I:Type):Type:= (I⊕I) ⊕ I ⊕ I
noncomputable def liveWet : Ruby.Hue c N (Lit Ω):= HJoin (HJoin Y (Pith.Tall.branches X P.threshold)) (HJoin X' (shill G' P.threshold))
noncomputable def colorLit (D:Ω→Dye): Lit Ω→Dye:=Sum.elim (Sum.elim (myLow Ω) (myLow Ω)) (Sum.elim D D)
structure Cargo (E:Gem c N I)(Q:I→Dye)(F:Gem c N Ω)(G:Gem c N Ω)(Y:Ruby.Hue c N Ω)(X:Ruby.Hue c N Ω)(Qh:Ω→Dye)(P:BudgetPoint)(t v A u u' r K:ℝ):Prop where
       mass : Warm (LowSection E Q) (myLow I) F Y (myLow Ω) (myLow Ω) P t A K u r v
       high : Warm (MoreSection E Q) (myH Q) G X Qh Qh P t A K u' r v
       polar :AgreesF (LowSection E Q) (myLow I) P.threshold
       beam : AgreesF (MoreSection E Q) (myH Q) P.threshold
       digest (i:Ω) : qualified (Qh i)
       brink (U:Grid c): Summable (letters E P.threshold U)
       value (i:I):Ash (Q i)
-- goals only.Orth.
variable (hp:Cargo E L' X G' Y X' L0 P t v A u w r K)
variable (hQ:0 ≤ K) (hs:1≤t)(hv:K+2≤A)
include hp
lemma gr_y : Patron.total X P.threshold 1=wearK c N v (Patron.total (LowSection E L') P.threshold 1):=by rw [show wearK c N v _ = _ from qLowH _ _ _ _ _ _ hp.mass hp.polar _,hush (E₀:=Y) hp.mass.bird.tree,add_zero]
include hQ hs hv
local notation "Yp"=> LowSection E L'
local notation "Hp"=> MoreSection E L'
local notation "Zp"=> Pith.Tall.branches X P.threshold
local notation "Xp"=> shill G' P.threshold
local notation "F?"=> liveWet (P:=P) Y X G' X'
structure Receipt (X G:Gem c N Ω) (Y X':Ruby.Hue c N Ω)(D:Ω→ Dye)(P:BudgetPoint)(t v A u r K:ℝ):Prop where
    tilt: Lurch (dusting X) (myLow Ω)
    rise: Lurch (shone G) D
    low : Bite (Pith.dusting X) P t ((2+jointFee N)*u) A true
    high:Bite (shone G) P t (2*r) A false
    funds: CostTall (liveWet (P:=P) Y X G X') P t K ((v+branchCost P N u K)+(v+reFare P r K)) (colorLit D) -- v here uniform Lira budget
lemma cashable : Receipt X G' Y X' L0 P t r A u w K:=by
     obtain ⟨hd,h⟩:=snowPoint _ X hp.mass.pupil (Licence_g hp.mass.cost) (t:=P.threshold); obtain ⟨he,hg⟩:=borneH _ G' hp.high.pupil (t:=P.threshold); have hF:0 < t:= zero_lt_one.trans_le hs; refine ⟨hd,he,snowB X u hp.mass.pupil.1 hp.mass.cost hF,shoneCost G' w hp.high.pupil.1 hp.high.cost hF,?_⟩; exact couple _ _ _ _ (couple _ _ _ _ hp.mass.bird (luminosity _ X u hp.mass.pupil hp.mass.cost hF hv hQ)) (couple _ _ _ _ hp.high.bird (shillCost _ G' w hp.high.pupil hp.high.cost hF hv hQ))
abbrev moneyL (x s:ℂ): ℂ:= Struck.pigment pegE x s * farm X (fun _=>1) + farm G' (serving L0 x s)
lemma completeS (x s:ℂ)(hz:‖x‖ ≤1)(h:‖s‖≤1): wearK c N v (Patron.total (Library.wind E (serving L' x s)) P.threshold U- Patron.total (Library.wind E (serving L' 0 0)) P.threshold U) = moneyL L0 X G' x s • (1:EvenA c N) + pigment pegE x s • (Patron.total (Pith.rentGem (c:=c) (Pith.gaugeMass X)) P.threshold U + Patron.total (dusting X) P.threshold U) + Patron.total (Library.wind (shone G') (serving L0 x s)) P.threshold U + Calm.netT (wet (liveWet (P:=P) Y X G' X') (serving (colorLit L0) x s)) U:=by
    rw [show Patron.total ..-Patron.total ..=_ from holdS L' E U x s hp.value (hp.brink U) hz h,map_add]
    let H:=shill G' P.threshold; let Np:=netT (c:=c) (N:=N) (wet H (serving L0 x s)) U
    have ht:0<t:= zero_lt_one.trans_le hs; have hA:0≤ A:=by linarith
    let g (i:Dye):= pigment i x s; have hg i: ‖g i‖≤1:= upperPaint i x s hz h; let p:=(g pegE); let v':=v; let rQ:= P.threshold
    have hK':= hp.high.equal g U hg (hp.beam g hg U); let t':= myH L'; change wearK c N v (Patron.total (Library.wind Hp (serving t' x s)) rQ U)=_ at hK'
    have hL':= hp.mass.equal g U hg (hp.polar g hg U); change wearK c N v (Patron.total (Library.wind Yp (fun _=> Struck.pigment pegE x s)) P.threshold U)=_ at hL'
    change _+wearK c N v (Patron.total (Library.wind Hp (serving t' x s)) rQ U)=_; rw [hK',hL']
    have hT:= luminosity (myLow _) X u hp.mass.pupil hp.mass.cost ht hv hQ; let V:=HJoin Y (Zp); let B:= HJoin X' (Xp); -- annotate
    have hB:=shillCost L0 G' w hp.high.pupil hp.high.cost ht hv hQ; have hzE:= couple _ _ _ _ hp.mass.bird hT; have hz₁:=couple _ _ _ _ hp.high.bird hB
    have hy(I:Type)(Z:Ruby.Hue c N I)(f:I→Dye)(u:ℝ)(h:CostTall Z P t K u f): Summable (fun i=> Z.mean i U):=(readable Z P.threshold U h.tree h.budget hQ hs).1
    unfold liveWet colorLit; rw [netSum (HJoin Y Zp) (HJoin X' Xp) _ _ U x s hzE hz₁ hQ hs hz h, netSum Y Zp _ _ U x s hp.mass.bird hT hQ hs hz h,netSum X' Xp _ _ U x s hp.high.bird hB hQ hs hz h]
    -- specialize horseQ earnings.E high cost. 
    have hs0:= ice G' (flora G' w hp.high.cost hA ht.le) (serving L0 x s) (fun i=> upperPaint _ x s hz h)
    have hX := shimmer L0 G' U w hp.high.pupil hp.high.cost hs hv hQ (serving L0 x s) (fun i=>upperPaint _ x s hz h)
    have hY := snowEq (myLow _) X u U hp.mass.pupil hp.mass.cost hv hs hQ
    rw [show g ∘ myLow Ω=(fun _=>p) from rfl,show g ∘ L0=serving L0 x s from rfl,show serving (myLow Ω) x s=(fun _=>p) from rfl,show Patron.total (Library.wind X _) _ U=p • _ from (Library.spar X p U (permits _ hp.mass.cost ht hA U)).tsum_eq, show Patron.total (Library.wind G' _) _ U=_ from hX,hY] -- ambiguous second rewriting also RHS.
    let Q:= (fun _:Ω=>p); rw [show netT (wet Y _) U=_ from hailH Y U p (hy _ Y _ _ hp.mass.bird), show netT (wet (Zp) _) U=_ from hailH (Zp) U p (hy _ _ _ _ hT)]; -- cancels p orientation.S
    unfold Weft.moneyL p g; -- p flag
    simp only [smul_add,add_smul,mul_smul]; abel
end YM.QCD.Weft
