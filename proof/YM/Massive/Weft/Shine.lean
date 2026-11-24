import YM.Massive.Weft.Snow
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
-- coat all high uninterpreted rank; scalar still absent at zero.Sector. Mask correction by shill.
def shone : Gem c N I:= ⟨E.addr,fun i=>E.view i-(fun _=>sewShelf E i)⟩
def shill (t:ℝ): Ruby.Hue c N I:= ⟨fun i=>(E.addr i).support,fun i U=> masked t (E.addr i).support (fun _=>sewShelf E i) U-sewShelf E i⟩
lemma shinePay (hp:Woven (E.addr i).site (E.addr i).support P t (E.view i) p)(ht:0<t): Woven (E.addr i).site (E.addr i).support P t ((shone E).view i) (2*p):=by rw [two_mul]; exact Loom.Wminus _ _ hp (sewBudget E i hp ht)
lemma mintH (hp: Regal c N (E.view i 1)=E.view i 1): Mint false ((shone E).view i) (E.addr i).site (E.addr i).support:=⟨Reggae.chooseP (E.view i 1) hp,fun _ h=>False.elim (Bool.noConfusion h)⟩
lemma gritH : Grit (fun _:Grid c=>sewShelf E i):=⟨fun _ k=> congr_arg Subtype.val (show sways (Lat.rotates N k) _=_ from Reggae.thorough (OrbitG.trade (Lat.rotates N k)) (Reggae.river c N (E.view i 1))), fun _ _ _=> Reggae.thorough ..,fun _=> Reggae.thorough ..⟩
lemma sheen (hp: CrossP E): Grit ((shone E).view i):= Grit_difference (E.view i) _ ⟨hp.gauge i,hp.num i,hp.real i⟩ (gritH E i)
lemma borneH (hp:Lurch E L'): Lurch (shone E) L' ∧ PatchH (shill E t) L':=by
    let S:=shill E t; refine ⟨ByGrit _ _ (fun i=>sheen E i hp.1) (fun s k g h=>?_ ),⟨fun j=> Grit_difference _ _ (tokens _ (E.addr j).support (gritH E j) t) (gritH E j),fun s k g h=>?_⟩⟩
    · obtain ⟨v,hv⟩:=hp.2 s k g h; exact ⟨v,fun i=>⟨(hv i).1,(hv i).2.1,fun U=> (map_sub _ _ _).trans (congr_arg₂ Sub.sub ((hv i).2.2 U) (sew_turn E i h fun i=> (hv i).2.2 1))⟩⟩
    obtain ⟨v,hv⟩:=hp.2 s k g h; have hh(i): S.bud (v i)=(S.bud i).image (act s):= congr_arg RegularAddress.support (hv i).2.1; refine ⟨v, fun i=>⟨hh i,fun U=>?_⟩,fun i=>(hv i).1⟩
    have hh' := sew_turn E i h (w:=v) fun i=>(hv i).2.2 1; exact (map_sub _ _ _).trans (congr_arg₂ Sub.sub (sprayer t (S.bud i) (S.bud (v i)) _ _ _ _ _ ((hh i).symm ▸ (healthy_image ..).symm) hh') hh')
lemma shine (U:Grid c): letters E t U i= sewShelf E i+letters (shone E) t U i+(shill E t).mean i U:=by
    change _= sewShelf E i+masked t (E.addr i).support (E.view i-(fun _=>sewShelf E i)) U+_; rw [Tall.mask_sub]; unfold shill letters; dsimp only; abel
lemma shoneCost (hp: CrossP E)(hv:Licence P v w t E)(he:0<t): Bite (shone E) P t (2*w) v false:=by
    obtain ⟨f,hf,h⟩:=hv.zone; refine ⟨fun i=>2*f i,valued_mult E.addr f hf (by norm_num),fun i=> ?_⟩; have hζ:= mintH E i (hp.real i 1); have hh:= shinePay E i (h i) he; exact ⟨hh,hζ.1,fun hi=>Library.puff _ (sheen E i hp) hh hζ he hi (E.addr i).anchor⟩
lemma ShoneTall : (shill E t).Tall t:=by
    constructor
    · exact fun i U V he ht=> congr_arg₂ Sub.sub (Tall.readsL (sewShelf E i) ((shill E t).bud i) U V he ht) rfl -- name args
    · exact fun i=> (RG.masked_measurable _ _ _ measurable_const).sub measurable_const
    · intro i U hM he; apply hM; exact sub_eq_zero.mpr (masked_eq t _ (fun _=> sewShelf E i) U he)
    intro i U; let P:=(E.addr i).support; let f:=sewShelf E i; change Cove.Gated P (masked t P (fun _=>f) U-f); unfold masked Set.indicator; split; · rw [sub_self]; exact Fleet.spruce P
    exact wingsZ _ _ _ (Fleet.spruce _) (Reggae.gator ..)
lemma shredT (hp:Woven (E.addr i).site (E.addr i).support P t (E.view i) p)(he:0<t)(U:Grid c): ‖token c N t ((shill E P.threshold).mean i U)‖≤ p:=by
    unfold shill; dsimp only; by_cases h:Healthy P.threshold (E.addr i).support U; · rw [masked_eq _ _ _ _ h,sub_self,map_zero,norm_zero]; exact hp.travel
    rw [masked_ne _ _ _ _ h,zero_sub,map_neg,norm_neg]; exact (Stem.opticX _ _ _ he).trans ((sewBudget E i hp he).sizeU 1 (flat_ok ..))
lemma shillCost (hp:Lurch E L')(hv:Licence P v w t E)(he:0<t)(hM:r+2≤v)(hQ:0≤r): CostTall (shill E P.threshold) P t r (reFare P w r) L':=by
    obtain ⟨f,hf,h⟩:= hv.zone; refine ⟨ShoneTall E,(borneH L' E hp).2,⟨f, Stem.tipped E f hf (fun i=>(h i).travel) (by linarith) hQ,fun i U=>shredT E i (h i) he U⟩⟩
lemma shimmer (hp:Lurch E L')(hv:Licence P v w t E)(he:1≤t)(hM:r+2 ≤ v)(hQ:0≤ r)(f:I→ℂ)(h:∀ i, ‖f i‖≤1): Patron.total (Library.wind E f) P.threshold U= farm E f • (1:EvenA c N) + Patron.total (Library.wind (shone E) f) P.threshold U + Calm.netT (wet (shill E P.threshold) f) U:=by
    have hs:0<t:=zero_lt_one.trans_le he; have hα:0 ≤v:=by linarith
    have hF:= ice E (flora E w hv hα hs.le) f h; let M:=shill E P.threshold; obtain ⟨hX,hZ,hV⟩:= shillCost L' E w hp hv hs hM hQ
    have ht:=readable (wet M f) P.threshold U (wetted M f hX) (wetCost M _ h hV) hQ he; have hh:=(permits _ (Library.frozen (shone E) _ h (shoneCost E w hp.1 hv hs).law) hs hα U)
    refine (((hF.add hh.hasSum).add ht.1.hasSum).congr_fun (g:=letters (Library.wind E f) P.threshold U) ?_).tsum_eq; intro i; rw [wireL,wireL,shine];  rw [smul_add,smul_add]; rfl
end YM.QCD.Weft
