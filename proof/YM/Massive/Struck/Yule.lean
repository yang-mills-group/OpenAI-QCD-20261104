import YM.Massive.Struck.Snap
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
variable {t:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (G:Gem c N I)(w:Tw) (i:I)
variable (h:CrossP G)
-- `ψ` planning always at pre-L and sized against B.order
abbrev penny (j:ℕ):ℝ:=2^j*cInv j
lemma totem (P:BudgetPoint): 1≤penny P.order:= le_trans (show 1≤cInv P.order from (by linarith [cInv_head P.order])) (le_mul_of_one_le_left (zero_le_one.trans (show 1≤cInv P.order from (by linarith [cInv_head P.order]))) (one_le_pow₀ (by norm_num : (1:ℝ) ≤2)))
def loggem (G:Gem c N I): Gem c N (I×Tw):= ⟨G.addr ∘ Prod.fst, fun i=> Massive.Log.log ∘ Lime.off (G.view i.1) i.2⟩
def logBudget (p:BudgetPoint)(z:I→ℝ): I× Tw→ℝ:= fun i=>penny p.order * Lime.cost (z i.1) i.2
def LowFare (G:Gem c N I)(P:BudgetPoint)(q t w:ℝ)(z:I→ℝ):Prop:= Valued G.addr q z P.B w ∧∀ i, Woven (G.addr i).site (G.addr i).support P t (G.view i) (z i)
variable (z:I→ℝ)
lemma logFare (hz: LowFare G P q t u z)(ht:0≤q)(hp:1≤t)(hh:u≤1/8)(hr:2^P.order*u ≤1/4) : LowFare (loggem G) P q t (penny P.order*(2*u)) (logBudget P z):=by
    obtain ⟨h,hq⟩:=hz; have hz:0≤z:=fun i=>(hq i).travel
    have he(i):z i≤u := anchored_each _ _ _ h ht hz i
    constructor
    · unfold logBudget; apply valued_mult (fun i:I×Tw=>G.addr i.1) (fun i=>Lime.cost (z i.1) i.2) _ (zero_le_one.trans (totem P))
      intro x; apply budget_rows _ _ _ (budget_scale (by norm_num : (0:ℝ)≤ 2) (h x)) -- generates currency
      intro i; dsimp only; by_cases ht : (G.addr i).site=x
      · simp_rw [if_pos ht]; let v:= Real.exp (q*coverNumber P.B (G.addr i).support); change SumBudget (fun y=> Lime.cost (z i) y * v) (2*(z i*v)); rw [show 2*(z i*v) = v*(2*z i) from (by ring)]; rw [show (fun y=> Lime.cost (z i) y * v)=(fun y=> v*Lime.cost (z i) y) from funext fun i=>mul_comm ..]; exact budget_scale (Real.exp_pos _).le (ledger (hz i))
      simp only [if_neg ht,mul_zero]; exact ⟨fun _=> le_rfl,summable_zero,by simp⟩
    · intro i; exact Lime.logSpend (hq i.1) hp ((he i.1).trans hh) ((mul_le_mul_of_nonneg_left (he i.1) (by positivity : (0:ℝ)≤2^P.order)).trans hr) i.2
-- assign Mint for any b at every Euler-child.

lemma wishBill (hz:LowFare G P q t u z)(ht:0≤q)(hp:1≤t)(hh:u≤1/8)(hr:2^P.order*u ≤1/4) (b:I→Bool)(hT:∀ i, Mint (b i) (G.view i) (G.addr i).site (G.addr i).support) (p:I×Tw): Mint (b p.1) ((loggem G).view p) (G.addr p.1).site (G.addr p.1).support:=by
    obtain ⟨h0,hq⟩:=hz; let i:=p.1; have he : z i≤u:=anchored_each (fun i=>(G.addr i).site) z _ h0 ht (fun i=>(hq i).travel) i -- G.addr wrong
    have hw:= (mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ)≤2^P.order)).trans hr; have hp':= Lime.tenure (hq i) hp hw p.2
    refine log_mint _ _ (wishM _ _ p.2 (hT i)) ?_
    exact ((sen_norm (o:=(G.addr i).site) t _ hp).trans ((hp'.sizeU (1:Grid c) (flat_ok ..)).trans (cost_le (hq i).travel p.2))).trans_lt (he.trans_lt (hh.trans_lt (by norm_num : (1/8:ℝ)<1)))
lemma soma (hz:LowFare G P q t u z)(ht:0≤q)(hp:1≤t)(hh:u≤1/8)(hr:2^P.order*u≤1/4) (V:Grid c): HasSum (letters (loggem G) P.threshold V) (Patron.total G P.threshold V):=by
    obtain ⟨h0,hq⟩:= hz; let C : Licence P q u t G := ⟨z,h0,hq⟩ -- `let` Prop.As
    have hn:= logFare G z ⟨h0,hq⟩ ht hp hh hr; let L:= (loggem G); let f:= letters L P.threshold V; have ht':0<t:=zero_lt_one.trans_le hp
    have hc:Summable f:= Stew.permits L (show Licence P q (penny P.order*(2*u)) t L from ⟨logBudget P z,hn⟩) ht' ht V
    have he(i): z i≤u:= anchored_each _ _ _ h0 ht (fun i=>(hq i).travel) i
    suffices hc' : ∀ i: I,(∑' n:Tw, f (i,n))=letters G P.threshold V i by
       rw [show Patron.total G P.threshold V=∑' i:I×Tw,f i from (hc.tsum_prod.trans (tsum_congr hc')).symm]; exact hc.hasSum
    intro i; let H:=(G.addr i).support; have hw:= (mul_le_mul_of_nonneg_left (he i) (by positivity : (0:ℝ) ≤2^P.order)).trans hr; change (∑' n:Tw,masked P.threshold H _ V)= masked P.threshold H _ V
    by_cases hV: Healthy P.threshold H V
    · rw [masked_eq _ _ _ _ hV]; simp_rw [masked_eq _ _ _ _ hV]; exact (Lime.expand (hq i) hp ((he i).trans hh) hw hV).tsum_eq
    simp only [masked_ne _ _ _ _ hV,tsum_zero]
lemma wakeK (wp:Equiv.Perm I)(p:Strut c)(K:Spike)(Z:Site c → ℂ)(hp: Warrant p Z K)(hV:∀ i, G.addr (wp i)= rotateL (G.addr i) p ∧∀ U, Diode N p K Z (G.view i (sky p U))= G.view (wp i) U) : let w:=Equiv.prodCongr wp (Equiv.refl Tw); ∀ i, (loggem G).addr (w i)=rotateL ((loggem G).addr i) p∧∀ U, Diode N p K Z ((loggem G).view i (sky p U))= (loggem G).view (w i) U:=by
    intro w i; obtain ⟨he,hq⟩:=hV i.1; refine ⟨he,fun U=>?_⟩; let P:= Diode N p K Z; let u:=G.view (wp i.1); exact walk_log _ P (sky p U) U (Lime.off u i.2) (offK _ i.2 P (sky p U) _ u (hq U) (OrbitG.phare _)) (OrbitG.phare _) (surfeit (copies_unitary _ _ (trail hp)))
lemma wake (H:CrossP G) : CrossP (loggem G):=by
    have hv(i:I×Tw):Grit ((loggem G).view i):=gritE _ (show Grit (G.view i.1) from ⟨H.gauge i.1,H.num i.1,H.real i.1⟩) i.2
    refine ⟨(fun i=>(hv i).gauge),(fun i=>(hv i).flex),(fun i=>(hv i).real),fun p k g h=>?_⟩; obtain ⟨e,hq⟩:= H.rays _ _ _ h; exact ⟨_,wakeK G e p k g h hq⟩
-- evaluate scaled weights on every helmet profile. all complex with |.|≤1. masked exponential = true group terms.
lemma wakingL (hz: LowFare G P q t u z)(a:I→ℂ)(he:∀ i, ‖a i‖≤1): LowFare (wind G a) P q t u z:= ⟨hz.1,fun i=>(Lime.scaleP (hz.2 i) _).stretches (Finset.Subset.refl _) (mul_le_of_le_one_left (hz.2 i).travel (he i))⟩
lemma wand (hz: LowFare G P q t u z)(ht:0≤q)(hp:1≤t)(hh:u≤1/8)(hr:2^P.order*u ≤1/4)(a:I→ℂ)(he:∀ i, ‖a i‖≤1)(U:Grid c)(i:I×Tw): NormedSpace.exp (letters (loggem (wind G a)) P.threshold U i)-1=a i.1^Lime.digit i.2 • (NormedSpace.exp (letters (loggem G) P.threshold U i)-1):= by
    let C:= (G.addr i.1).support; by_cases hV:Healthy P.threshold C U; swap; · unfold letters; rw [show ((loggem (wind G a)).addr i).support=C from rfl, show ((loggem G).addr i).support=C from rfl,masked_ne _ _ _ _ hV, masked_ne _ _ _ _ hV,exp_zero,sub_self,smul_zero] -- defeq supports
    let L:=(wind G a); let p:= Lime.off (L.view i.1) i.2; let Z:=Lime.off (G.view i.1) i.2; have hb:=anchored_each _ _ _ hz.1 ht (fun i=>(hz.2 i).travel) i.1; have hw:= (mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ)≤ 2^P.order)).trans hr
    have ht₁ : NormedSpace.exp ((loggem L).view i U)-1=p U:=by
        rw [show NormedSpace.exp ((loggem L).view i U)=1+p U from Lime.mayer ((wakingL G z hz a he).2 i.1) hp (hb.trans hh) hw hV i.2]; abel
    have ht₂ : NormedSpace.exp ((loggem G).view i U)-1=Z U:=by rw [show NormedSpace.exp ((loggem G).view i U)=1+Z U from Lime.mayer (hz.2 i.1) hp (hb.trans hh) hw hV i.2]; abel
    unfold letters; rw [show ((loggem (wind G a)).addr i).support=C from rfl, show ((loggem G).addr i).support=C from rfl,masked_eq _ _ _ _ hV,masked_eq _ _ _ _ hV,ht₁,ht₂]; exact congr_fun (Lime.scaled i.2 (a i.1) (G.view i.1)) U
end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.wishBill
#print axioms YM.QCD.Struck.Library.wand
#print axioms YM.QCD.Struck.Library.logFare
