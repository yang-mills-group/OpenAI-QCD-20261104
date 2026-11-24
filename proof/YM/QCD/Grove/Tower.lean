import YM.QCD.Grove.Clare
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Slide Trio.Sharp
-- layout
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
section lift
variable (A:Window c C D)(P:Gem c N I)(Q:Gem C N J)(T:Finset I)(T':Finset J)(g:Site C→ℂ)
-- Character ready for union. Lens~Z patience
structure LiftQ (B: BudgetPoint)(w:ℕ) : Prop where
    rays x (U:Grid c):flags B.threshold U=∅→ orchid T P (A.cut x) U= axes A g N (orchid T' Q x (A.links U)) ∧ duskQ T P (A.cut x) U= duskQ T' Q x (A.links U)
-- use `B` no w; i unused
lemma officer (W:BudgetPoint)(v:ℕ)(hp:SoilB T P W v t)(hx:SoilB T' Q W v t')(hk:∀ x:Site C,Set.InjOn A.cut (neighbors v x))(ht:∀ (x:Site C),∃ p:(↥(pondC T P (A.cut x)) ≃ ↥(pondC T' Q x)), ∀ i:↥(pondC T P (A.cut x)),(P.addr i.val).support=((Q.addr ((p i).val)).support.image A.cut)∧∀ U:Grid c,flags W.threshold U=∅→ axes A g N (Q.view (p i).val (A.links U))=P.view i.val U): LiftQ A P Q T T' g W v:=by
    constructor; intro x U hu; obtain ⟨s,he⟩:=ht x; let V:= pondC T P (A.cut x); let Z:= pondC T' Q x; let f i:= P.view i U; let z i:= Q.view i (A.links U); let Γ:=axes A g N; let X:=Q
    have hm :(∑ i∈V, buds (A.cut x) N (f i))= Γ (buds x N (∑ i∈Z,z i)):=by
       rw [← Finset.sum_coe_sort, ← Finset.sum_coe_sort Z,map_sum,map_sum,← Equiv.sum_comp s]; apply sum_congr rfl; rintro i _; rw [show f i.val= _ from ((he i).2 U hu).symm]; let Y:=(s i).val; let S:=(Q.addr Y).support; have hh:Y∈ pondC T' Q x:= (s i).2; have ho:=mem_filter.mp hh; exact pulsesG _ _ S _ ((hx.fees Y ho.1).choose_spec.gated _) x ho.2 ((hk x).mono (coe_subset.mpr (hx.tortillas _ ho.1 x ho.2))) -- sum_coe signature
    constructor
    · rw [ornate T P hp, ornate T' Q hx]; unfold primed; rw [map_sum]; exact hm
    unfold duskQ; rw [← Finset.sum_coe_sort,← Finset.sum_coe_sort (pondC T' Q x), ← Equiv.sum_comp s]; refine sum_congr rfl fun i _=>?_ ; rw [(he i).1]; let Y:=s i; have hh := mem_filter.mp Y.property; rw [card_image_of_injOn ((hk x).mono (coe_subset.mpr (hx.tortillas _ hh.1 _ hh.2)))]; congr 1 -- g
    rw [← (he i).2 U hu]; exact congr_arg (fun z:ℂ=> -z.re) (mud_ax A g _)
end lift
section crossing
variable (A:Window c C D)(M:Window f C D')(P:Gem c N I)(Q:Gem C N J)(S:Gem f N V)(T:Finset I)(T':Finset J)(T₀:Finset V)(g v:Site C→ℂ)
noncomputable def closeQ (x:Site f→Site C): EvenA f N→L[ℝ]EvenA c N:= (streamL A.cut g N).comp (streamL x (star ∘ v ∘ x) N)
variable (ha:LiftQ A P Q T T' g B w)(hv:LiftQ M S Q T₀ T' v B w) (ht:SoilB T' Q B w t)
include ha hv ht
lemma resorts (Qw:Site C)(U:Grid c)(W:Grid f)(hp:flags B.threshold U=∅)(hm:flags B.threshold W=∅)(hx: Agrees (neighbors w Qw) (A.links U) (M.links W))(he:Quaint M v)(u:Site f→ Site C)(h:∀ i∈neighbors w Qw, u (M.cut i)=i):
    orchid T P (A.cut Qw) U=closeQ A g v u (orchid T₀ S (M.cut Qw) W):=by
    obtain ⟨hy,-⟩:=ha.rays Qw U hp; obtain ⟨hV,-⟩:=hv.rays Qw W hm; rw [hy, hV, mintL T' Q ht _ _ _ hx]
    let X:=neighbors w Qw; have hh:Healthy B.threshold X (1:Grid C):=AnalyticBridge.VerifiedReset.flat_ok ..
    let V:= orchid T' Q Qw (M.links W); change axes A g N V= streamL A.cut g N (streamL u _ N (axes M v N V)); rw [quayK M v u X h he V ((wind T' Q ht _ Qw hh).2 _), marker_down]
end crossing
end YM.QCD.Grove
