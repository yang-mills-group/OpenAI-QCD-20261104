import YM.Massive.Struck.Twinkle
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
open High
local notation "q₁"=> (1/8:ℝ)
local notation "L₀"=>fan L ρ x
structure WickFee (G:Gem c N I)(b:Flavor N)(P:BudgetPoint)(t u:ℝ):Prop where
    wit : High.Wick G
    power : Quanta G b
    passport : Licence P q₁ u t G
    lines : Crossing G
lemma investor (Z:Voice c N)(hp:Enn P b L x ρ q₁ (duo Z.P Z.K))(hX:P.B= highR L x): WickFee Z.P b P L₀ (Jets.Touch.chip L x):=by
     refine ⟨?_,?_,(Library.steady Z hp hX).shelf,(sym Z hp).1⟩; all_goals obtain ⟨f,g,hc,hF⟩:=hp; intro i hi; have h: Feast P (Z.P.addr i).support (Z.P.addr i).site b (Z.P.view i) L₀ (f i):=(hF i).2 hi
     · let v:= Z.P.view i 1; have he:Reggae.river c N v=0:=h.base.value
       refine ⟨?_,h.base.mute hi ⟩; have hp:=chooseP v (h.joy 1); rw [he,map_zero,sub_zero] at hp; exact hp
     exact h.rack
lemma combine (A:Gem c N I)(P':Gem c N ι)(hp:WickFee A b P t u)(he:WickFee P' b P t v): WickFee (weave A P') b P t (u+v):=by refine ⟨?_,fibs _ _ _ hp.power he.power,guardL _ _ hp.passport he.passport,pilot _ _ hp.lines he.lines⟩; rintro (i|i); exact hp.wit _; exact he.wit _
lemma dim_zero (z:ℂ)(V:EvenA c N)(n:Dye)(h:0<n.1): Struck.pigment n 0 z • V=0:=by unfold Struck.pigment; rw [zero_pow h.ne',mul_zero,zero_smul]
lemma dimc (z:ℂ)(V:EvenA c N)(n:ℕ)(hn:0<n): Struck.pigment (n,2) 0 z • V=0:=dim_zero _ _ _ hn
lemma dead (G:Gem c N I)(f:I→Dye)(hp:∀ i,0<(f i).1): (solvent G f 0 z).view=0:=by
    funext i U; let w k:= wind G (fun i=>Struck.pigment (f i) 0 k); let t:=i.2
    have hv t: off ((w z).view i.1) t U=0:=by induction t with | nil=>exact dim_zero z _ _ (hp i.1)|cons j q h=> rw [Lime.off,Pi.smul_apply,Pi.pow_apply,h,zero_pow (by omega : j+2≠0),smul_zero]
    change Massive.Log.log (off _ _ U)=0; rw [hv]; exact log_zero
lemma womb (A:Gem c N I)(B:Gem c N I)(p:B.addr=A.addr)(h:A.view=0)(he:CrossP B): WickFee A b P t 0:=by
    have ht (i) : A.view i=0:=by rw [h]; rfl
    constructor
    · intro i _; rw [ht i]; change Reggae.mud (0:EvenA c N)=0∧ _; refine ⟨map_zero (clay c N),fun x y a b=> ?_⟩; rw [show (Reggae.river c N) ∘ (0:Grid c→EvenA c N)=0 from ?_]; · exact hessian_zero ..
      funext i; exact map_zero _
    · intro i _ y; rw [ht]; change profile (A.addr i).site y (Stew.meter b (0:EvenA c N))=_; rw [map_zero,map_zero]
    · refine ⟨fun _=>0,fun i=>?_,fun i=>?_⟩
      · refine ⟨fun j=> ?_, ?_,?_⟩ <;> try (simp)
      · rw [ht]; exact Loom.Wzero _
    refine ⟨?_,fun v k g h0=>?_⟩
    · exact ⟨fun i U k=> by rw [ht]; exact congr_arg Subtype.val (map_zero (sways (Lat.rotates N k))),fun i U z hv=>by rw [ht]; exact map_zero _,fun i U=>by rw [ht]; exact map_zero _⟩
    obtain ⟨e,h⟩:= he.rays v k g h0; exact ⟨e,fun i=>⟨(by rw [← p]; exact (h i).1),fun U=>by rw [ht,ht]; exact map_zero _⟩⟩
lemma RIP (G:Gem c N I)(a:I→Dye)(g:ℝ)(ha:∀ i,0<(a i).1)(hp:Lurch G a): WickFee (solvent (ampE G g) a 0 s) b P t 0:= by
    let H:= lurkLog G a g hp; apply womb (solvent (ampE G g) a 0 s) (solvent (ampE G g) a 1 1) rfl (dead s (ampE G g) a ha) H.1 -- dead binder s!
variable (hp:Desk Y P b L x ρ)
include hp
lemma canned (hr:P.B=highR L x): WickFee (PackageE Y φ 0 s) b P L₀ (Jets.Touch.chip L x):= by
   rw [← add_zero (Jets.Touch.chip L x)]; refine combine _ _ (investor Y.master hp.base hr) ?_; rw [← add_zero (0:ℝ)]; exact combine _ _ (RIP s Y.canonical _ (φ⁻¹^2) (fun _=>by decide) (fromG _ _ (rentCross c _))) (add_zero (0:ℝ) ▸ combine _ _ (RIP s Y.low _ (φ⁻¹^2) (fun _=>by decide) (fromG _ pegE hp.arg)) (RIP s _ (knot ∘ Y.ad) (φ⁻¹^3) (fun i=> Nat.zero_lt_of_lt (lt_of_lt_of_le (show 1<2 by omega) (hp.bottom i))) (lyr Y hp)))
omit hp
-- preserve Full.P. for all ears. `Arc p` demands classical heart, not near spent.
lemma mixed_void (G J:Rail c N I)(p:J.addr=G.addr)(he:G.warp=0)(hv:Charm J): MixedP G:=by
    have ht (i: I): G.warp i=0:=by rw [he]; rfl
    refine ⟨fun i U k=>by rw [ht]; exact congr_arg Subtype.val (map_zero (sways (Lat.rotates N k))),fun i U k he=>by rw [ht]; exact map_zero _,fun i U=>by rw [ht]; exact map_zero _,?_⟩
    intro s g k he; obtain ⟨e,H⟩:=hv.turn _ _ _ he; exact ⟨e,fun i=> ⟨(by rw [← p]; exact (H i).1), (by rw [← p]; exact (H i).2.1), fun U=>by rw [ht,ht]; exact map_zero _⟩⟩
lemma mixed_tie (G:Rail c N I)(J:Rail c N ι)(he:MixedP G)(hv:MixedP J): MixedP (tie G J):=by
    refine ⟨?_,?_,?_,?_⟩ <;> first| (rintro (i|i); exact he.real _; exact hv.real _)| (rintro (i|i); exact he.num _; exact hv.num _)| (rintro (i|i); exact he.gauge _; exact hv.gauge _)|skip
    intro p g k h; obtain ⟨e,he⟩:=he.moves p g k h; obtain ⟨d,hv⟩:=hv.moves p g k h; exact ⟨Equiv.sumCongr e d,fun i=>by cases i; exact he _; exact hv _⟩
lemma voidK (X: Rail c N I)(h:X.warp=0): Quits X P.B 0 u v t:=by
    refine ⟨fun i=>0,(fuelHit ..).mpr fun i=>?_,fun i U=>?_⟩
    · simp only [mul_zero]; exact ⟨fun i=>le_rfl,summable_zero,by simp⟩
    rw [h,Pi.zero_apply,Pi.zero_apply,map_zero,norm_zero]
include hp
abbrev frameBot (s:ℂ):= hueW (ampK Y.top (φ⁻¹^3)) (fun i=> Struck.pigment (knot (Y.up i)) 0 s)
abbrev pegBot (s:ℂ):= watt (ampK Y.prime (φ⁻¹^2)) (Struck.pigment pegE 0 s)
lemma deep_k (hr:P.B=highR L x): let K:=PackageK Y φ 0 s; MixedP K∧ K.Reg P.threshold∧ Quits K P.B 1 (taxK L x 1) q₁ L₀:=by
    let V:= frameBot Y φ s; let G:= pegBot Y φ s; have hv: V.warp=0:=funext fun i=>funext fun U=>dim_zero _ _ _ (Nat.zero_lt_of_lt (lt_of_lt_of_le (show 1<2 by omega) (hp.star i))) -- implicit knot
    have hg : G.warp=0:=funext fun i=>funext fun U=>dimc _ _ _ (by norm_num : (0:ℕ)<1)
    intro K'; refine ⟨mixed_tie _ (tie G V) (sym Y.master hp.base).2 (mixed_tie _ _ (mixed_void G Y.prime rfl hg hp.warm) (mixed_void V Y.top rfl hv hp.wish)),health_z Y φ 0 s hp,?_⟩
    exact wattsLoosen _ (quitsTie Y.master.K (tie G V) (Library.steady _ hp.base hr).bill (quitsTie _ _ (voidK _ (P:=P) hg) (voidK _ (P:=P) hv))) (by linarith)
lemma painted_orig (hr:P.B=highR L x): Enn P b L x ρ q₁ (Cane Y φ 0 s):=by
    obtain ⟨hw,hV,hf,hL⟩:= canned Y φ s hp hr; obtain ⟨ha,hE,hB⟩:= deep_k Y φ s hp hr
    exact High.levy _ _ _ hL ha hw hV hE hf hB hr (by norm_num)
end Carrier
end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.Carrier.canned
#print axioms YM.QCD.Struck.Library.Carrier.painted_orig
