import YM.QCD.Stem.Eyr
/-! # Book pays un-Strut E before averaging. survive Ω before Calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Calm
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure Pressure.Testing RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort Octave
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Token Tidings Sienna QCD.Loom Fleet Cove Reggae
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.L2Operator
open Lat YM.Next.Free
open Jets.Touch Port Kit Run Bay Leaf Tee Flume Garden Orbit LeafM AtomF Kings Fog Raft Transfer ParcelR Birth Beam
open GasP Ursell Greenbelt Patron Fount Oasis Stem Grove Slide Trio.Sharp Stew Creek
open Animals AnalyticBridge.VerifiedReset
variable {t a u D A θ h M h' ξ ζ w w' : ℝ}{I J V: Type}{m b s q N n :ℕ}{c C :Side}{Y: Stars→ Side}{B:BudgetPoint}
section books
-- bookkeeping: sales of actual physical terms before Strut averaging. revenues nonvacuum.
abbrev netT (V':Ruby.Hue c N V) (U:Grid c):= ∑' i,V'.mean i U
variable (S:Gem c N I)(G: Ruby.Hue c N J)(T:Finset I) {f: Grid c→EvenA c N}{k:ℝ}
structure PayC (S:Gem c N I) (G:Ruby.Hue c N J)(B:BudgetPoint) (a t u h h' d:ℝ)(f:Grid c→EvenA c N): Prop where
   hue  : Dyed S
   pay  : Licence B t h a S
   hat  : TokenB G B.threshold B.B u h' a
   ears (U:Grid c): potion f U=Reggae.ocean c N d+potion (Stem.income S B.threshold+ netT G) U
section jig
variable (P:Gem c N J)(Z:Ruby.Hue c N V)
lemma alien (f : Grid c→EvenA c N)(hQ : Bound S T P Z B q h M h' a t u f): f=(fun U=>∑ i∈ T,letters S B.threshold U i) +(Stem.income P B.threshold+netT Z):=funext (fun i=>by rw [hQ.earns]; exact add_assoc ..)
lemma tokenZ (g:TokenB G k n t h u)(he:0<a)(hz:a≤u):TokenB G k n t h a:=by
   obtain ⟨w,hw,hp⟩:=g.pay; refine {g with pay:=⟨w,hw,fun i V=> ?_ ⟩}
   let W:= G.mean i V; refine le_trans (b:= Creek.load (fun _=>u) W.val) ?_ (hp i V); change Creek.load (fun _=>a) W.val≤_; rw [Creek.dry _ (fun _=> he), Creek.dry _ (fun _=> he.trans_le hz)]; apply sum_le_sum; intro i _; rw [prod_const,prod_const]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact pow_le_pow_left₀ he.le hz _
lemma ledger (g: Licence B u k t S)(hv:0≤a)(hp:a ≤ t): Licence B u k a S:=by obtain ⟨w,hw,h⟩:=g.zone; refine ⟨w,hw,fun i=>{ (h i) with pole:=fun j he l hx hp'=> (Stew.future (lens _) hv hp _).trans ((h i).pole j he l hx hp') }⟩ -- open lemma name
lemma carves (hx:TokenB Z B.threshold B.B u w a)(hr:D ≥ w):TokenB Z B.threshold B.B u D a:=by obtain ⟨r,he,hv⟩:=hx.pay; exact {hx with pay:=⟨r,fun i=> Extra.Iteration.Cost.enlarge (he i) hr,hv⟩}
lemma leisure (hx:Bound S T P Z B q h M w a t u f)(hv:h ≤ D)(he : w ≤ h')(hp:M ≤ θ): Bound S T P Z B q D θ h' a t u f:=by obtain ⟨v,hr,hV⟩:= hx.rip.tokenEq; exact { hx with rip:=⟨v,hr,fun i=> (hV i).trans hp⟩, loom:=wells P hx.loom le_rfl hv,cash:= carves _ hx.cash he }
lemma penny (hx: Licence B t h a S)(ht:Dyed S)(hp:TokenB G B.threshold B.B u h' a):PayC S G B a t u h h' 0 (Stem.income S B.threshold+netT G):=⟨ht,hx,hp,fun _=> (by rw [map_zero,zero_add])⟩
variable (K:Ruby.Hue c N V)
lemma glib (S:Gem c N I)(F:Gem c N J)(h:Dyed S)(hv:Dyed F): Dyed (Reggae.weave S F):=by refine ⟨fun i=>?_,fun i=> ?_,fun i=>?_ ⟩<;>cases i; exacts [h.gauge _,hv.gauge _,h.num _,hv.num _,h.real _,hv.real _]
variable {I':Type}
-- G may share type J here with P but avoid.
lemma bonuses (W:Gem c N I') (g: Grid c→EvenA c N)(he: PayC S G B a t u h h' D f)(hv:PayC W K B a t u w w' M g)(hz:1 ≤ a)(ha:0 ≤ t)(hx:0≤u): PayC (Reggae.weave S W) (Ruby.HJoin G K) B a t u (h+w) (h'+w') (D+M) (f+g):=by
    constructor
    · exact glib _ _ he.hue hv.hue
    · exact guardL S W he.pay hv.pay
    · exact strew G K he.hat hv.hat
    intro V; rw [crestedX,he.ears,hv.ears]
    have he':(Stem.income (Reggae.weave S W) B.threshold+ netT (Ruby.HJoin G K))=(Stem.income S B.threshold+netT G) +(Stem.income W B.threshold+netT K):=by
       funext U; simp only [Pi.add_apply]; unfold Stem.income; rw [woven_sum _ _ U (permits S he.pay (zero_lt_one.trans_le hz) ha U) (permits W hv.pay (zero_lt_one.trans_le hz) ha U),show netT (Ruby.HJoin G K) U= netT G U+netT K U from (HasSum.sum (f:=fun i=>(Ruby.HJoin G K).mean i U) (scaledLift G he.hat U hx hz|>.hasSum) (scaledLift K hv.hat U hx hz|>.hasSum)).tsum_eq]
       abel
    rw [he',crestedX (Stem.income S B.threshold+netT G),map_add]; abel
end jig
-- currency with single x and low vol weights
local notation "HI" => helm S T b
lemma whaled (G: Gem c N (Site c))(hp:∀ i,G.addr i= wharf c m i)(ht:m ≤ n*B.B)(he:∀ i,Woven i (neighbors m i) B a (G.view i) M)(hv:0 ≤ t): Licence B t (M * Real.exp (t*(ballCost n:ℝ))) a G:=by
    have hz (i:Site c) :coverNumber B.B (neighbors m i) ≤ ballCost n:= vRide _ _ i ht rfl B.B_pos
    have hh (i:Site c): 0≤M:=(he i).travel
    refine ⟨fun _=>M,fun i=> ?_,fun i=> by rw [hp i]; exact he _ ⟩
    constructor
    · intro j; dsimp only; split; exact mul_nonneg (hh j) (Real.exp_pos _).le; exact le_rfl
    refine ⟨Summable.of_finite,?_⟩; rw [tsum_fintype]; simp_rw [hp]; change (∑ j:Site c, if j=i then M* Real.exp (t*coverNumber B.B (neighbors m j)) else 0)≤_; rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ i)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hz i)) hv)) (hh i)
end books
end YM.QCD.Calm
#print axioms YM.QCD.Calm.ledger
