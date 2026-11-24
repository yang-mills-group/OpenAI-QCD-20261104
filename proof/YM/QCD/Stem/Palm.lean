import YM.QCD.Stem.Stole
/-! # Lifting stowed Rolls. Also pointwise angular accounting. -/
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
open AnalyticBridge VerifiedReset Footprint
section spread
variable (hC : C.val = c.val*D) (v:Site C→ℂ)(P:Gem c N (Site c))(S:Gem C N (Site C)) (T:BudgetPoint)
local notation "A"=> normal (Deck.divides hC) hC
lemma neatX (L:Side)(W:Gem L N (Site L))(h:∀ i,(W.addr i).support=neighbors w i) (x:Site L): pondC univ W x= neighbors w x:=by ext i; simp only [pondC,mem_filter,mem_univ,true_and,h]; rw [neighbors_mem, neighbors_mem,separation_comm]
lemma crossguard (hp:2*(w+w)< c.val)(he:∀ i,(P.addr i).support=neighbors w i)(hz:∀ i,(S.addr i).support=neighbors w i)(ht: SoilB univ P T (w+w) t)(hx: SoilB univ S T (w+w) t')(h:∀ (x:Site C) (U:Grid c), axes (normal (Deck.divides hC) hC) v N (S.view x ((normal (Deck.divides hC) hC).links U))=P.view ((normal (Deck.divides hC) hC).cut x) U) : LiftQ A P S univ univ v T (w+w):=by
    have hh (x:Site C):(neighbors w ((A).cut x))=(neighbors w x).image (A).cut:=by
       unfold neighbors; convert! ringed hC ({x}:Support C) w <;> simp
    refine officer _ _ _ _ _ v T (w+w) ht hx (fun i=> Meadow.garden hC i hp) fun i=>?_
    obtain ⟨p',h'⟩:= Moss.permit (A).cut (pondC univ S i) (pondC univ P ((A).cut i)) (by rw [neatX c _ he,neatX C _ hz]; exact hh _) (by rw [neatX C _ hz]; exact Meadow.garden hC i (by omega))
    refine ⟨p'.symm,fun x=> ?_⟩; obtain ⟨x,rfl⟩:=p'.surjective x; rw [Equiv.symm_apply_apply,h',he,hz]; exact ⟨hh x.val,fun U _=> h _ _⟩
end spread
section loom
variable (P:Gem c N I)(S:Gem c N J)(W:Finset I)(X:Finset J)
variable (Y U:Type) (A:Gem C N Y)(Z:Gem C N U)(Q:Finset Y)(Q':Finset U)
set_option quotPrecheck false
local notation "P'"=> Reggae.weave P S
local notation "W'"=> Finset.disjSum W X
lemma hawser (i:Site c): pondC (W') (P') i=(pondC W P i).disjSum (pondC X S i):=by
    ext x; unfold pondC; rcases x with x|x
    · simp only [mem_filter, inl_mem_disjSum]; rfl
    simp only [mem_filter,inr_mem_disjSum]; rfl
lemma richer (V:Grid c): primed (W') (P') V=primed W P V+primed X S V:= by unfold primed; rw [sum_disjSum]; rfl
lemma chants (V:Grid c)(i: Site c): duskQ (W') (P') i V=duskQ W P i V+duskQ X S i V:=by rw [duskQ,hawser,sum_disjSum]; rfl
lemma windfall {d':ℝ} (h:Pockets W P B t d) (hp:Pockets X S B t d'): Pockets (W') (P') B t (d+d'):=by
   obtain ⟨f,hf,h⟩:=h.tokenEq; obtain ⟨g,hg,hx⟩:=hp.tokenEq; refine ⟨Sum.elim f g,fun i hi=> ?_,fun i=>?_⟩
   · cases i; exact hf _ (inl_mem_disjSum.mp hi); exact hg _ (inr_mem_disjSum.mp hi)
   rw [hawser, sum_disjSum]; exact add_le_add (h i) (hx i)
lemma vault (h:SoilB W P B w t)(hp:SoilB X S B w t): SoilB (W') (P') B w t:=⟨fun i hi=>by cases i; exact h.fees _ (inl_mem_disjSum.mp hi); exact hp.fees _ (inr_mem_disjSum.mp hi),fun i hi=>by cases i; exact h.tortillas _ (inl_mem_disjSum.mp hi); exact hp.tortillas _ (inr_mem_disjSum.mp hi),fun i hi=>by cases i; exact h.gauge _ (inl_mem_disjSum.mp hi); exact hp.gauge _ (inr_mem_disjSum.mp hi),fun i hi=>by cases i; exact h.fit _ (inl_mem_disjSum.mp hi); exact hp.fit _ (inr_mem_disjSum.mp hi),fun i hi=>by cases i; exact h.real _ (inl_mem_disjSum.mp hi); exact hp.real _ (inr_mem_disjSum.mp hi) ⟩ -- syntax?
lemma opensP (h:SoilB W P B w t)(hp: w ≤ j): SoilB W P B j t:= { h with tortillas:=fun i hi x hx => (h.tortillas i hi x hx).trans fun i hi=>(neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hp)}
set_option synthInstance.maxHeartbeats 200000 in
lemma thick (G:Window c C D)(v:Site C→ℂ) (hp:LiftQ G P A W Q v B w) (hk:LiftQ G S Z X Q' v B j) : LiftQ G (P') (Reggae.weave A Z) (W') (Finset.disjSum Q Q') v B n:=by
    constructor; intro x V h; have he:=hp.rays x V h; have hh:=hk.rays x V h; constructor
    · unfold orchid; simp only [comp_apply,richer]; rw [map_add (buds (G.cut x) N),map_add (buds x N),(map_add (axes G v N) (buds x N (primed Q A (G.links V))) (buds x N (primed Q' Z (G.links V))))]; exact congr_arg₂ (·+·) he.1 hh.1
    rw [chants,chants,he.2,hh.2]
end loom
end YM.QCD.Grove
