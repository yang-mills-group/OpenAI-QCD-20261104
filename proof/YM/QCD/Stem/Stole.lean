import YM.QCD.Stem.Water
/-! # short-books binding. Possibility lenses include Rent on OLD. Dust pay after enlarging neighbors.
 Uses Ink.Hit for unmasked? short already masked-leak.
 -/
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
section short
variable (S:Gem c N I) (X:Finset I)(w:ℕ) (h:Licence B r d t S)(hT:Dyed S) (hv:∀ i∈X,(S.addr i).support⊆ neighbors w (S.addr i).site)
def bust (x:Site c):= X.filter fun i=>(S.addr i).site=x
def tuckS : Gem c N (Site c):=⟨fun i=>Grove.wharf c w i,fun i=> ∑ x∈bust S X i,S.view x⟩
def coins (i:Site c)(U:Grid c):=∑ j∈ bust S X i, letters S t U j -- uses t implicit
def burl (B:BudgetPoint): Ruby.Hue c N (Site c):=⟨fun i=> neighbors w i,fun i V=> coins (t:=B.threshold) S X i V- letters (tuckS S X w) B.threshold V i⟩
local notation "ξ"=>B.threshold
local notation "T₁"=>tuckS S X w
local notation "X₁"=>burl S X w B
lemma riversQ (V:Grid c): (∑ i∈ X,letters S ξ V i)=(∑ i,letters T₁ ξ V i)+(∑ i,(X₁).mean i V):=by
    have he:(∑ i,coins (t:=ξ) S X i V)= (∑ i∈X,letters S ξ V i):=by unfold coins bust; simp_rw [sum_filter]; rw [sum_comm]; simp
    rw [← he]; unfold burl; simp only; rw [sum_sub_distrib]; abel
include hv
lemma paidT (i:Site c) (U:Grid c)(hU:Healthy B.threshold (neighbors w i) U): (X₁).mean i U=0:=by
    change _-letters _ _ U i=_; unfold letters; rw [show ((T₁).addr i).support=neighbors w i from rfl,masked_eq _ _ _ _ hU,sub_eq_zero]; unfold coins;
    change (∑ x∈ bust S X i,letters S _ U x)=(∑ x∈ bust S X i,S.view x) U; rw [Finset.sum_apply]; refine sum_congr rfl fun x hx=> ?_; have he:= mem_filter.mp hx; exact masked_eq _ _ _ _ (hU.mono_left (he.2 ▸ hv x he.1))
omit hv
include hT
lemma vibes : Dyed T₁:=by
    have hx i U: (T₁).view i U=∑ j∈ bust S X i,S.view j U:=Finset.sum_apply ..
    refine ⟨fun i U k=> ?_,fun i U W hv=>?_,fun i V=>?_⟩
    · refine congr_arg Subtype.val (show sways (Lat.rotates N k) ((T₁).view i (Lattice.gauge k U))=_ from ?_); simp_rw [hx,map_sum]; exact sum_congr rfl (fun j hj=>Subtype.ext (hT.gauge j U k))
    · rw [hx,map_sum]; exact sum_congr rfl fun j hj=> hT.num j U W hv
    rw [hx,map_sum]; exact sum_congr rfl fun j hj=> hT.real j V
omit hT
lemma balanceK (i:Site c)(u:I→ℝ) (g:I→ℕ) (hp:Anchored (fun i=>(S.addr i).site) u g r d)(hk:0≤r)(ht:∀ i,0 ≤u i): ∑ j∈ bust S X i,u j≤d:=by
    let y:=bust S X i; let U j:= if (S.addr j).site=i then u j*Real.exp (r*g j) else 0; have hv :SumBudget U d:= hp i
    refine (sum_le_sum (g:=U) ?_).trans ((hv.2.1.sum_le_tsum y (fun i _=> hv.1 i)).trans hv.2.2); intro j hj; rw [show U j= _ from if_pos ((mem_filter.mp hj).2)]; exact le_mul_of_one_le_right (ht j) (Real.one_le_exp (by positivity))
variable (hr:0≤r)
include hv h hr
lemma chief (x:Site c): Woven x (neighbors w x) B t ((T₁).view x) d:=by
    obtain ⟨f,hf,h⟩:=h.zone; refine (Woven.sumX S.view (bust S X x) f ?_).stretches (Subset.refl _) (balanceK S X x f _ hf hr (fun i=> (h i).travel)) -- remove o
    intro i hi; have he:= mem_filter.mp hi; exact he.2 ▸ ((h i).stretches (hv i he.1) le_rfl)
include hT
lemma ridden : SoilB univ T₁ B (w+w) t ∧ Pockets univ T₁ B t (d*(ballCost w:ℝ)):=by
    have hf(x:Site c):= chief S X w h hv hr x -- hT unused for chief section inc after
    have ht:= vibes S X w hT; refine ⟨⟨fun i hi=>⟨_,hf i⟩,?_,fun i hi=> ht.gauge i,fun i _=> ht.num i,fun i _=> ht.real i⟩,fun _=>d,fun i hi=>hf i,fun i=>?_⟩ -- collapse braces
    · intro i _ j hj k hk; apply (neighbors_mem ..).2; refine (separation_triangle j i k).trans (Nat.add_le_add ((separation_comm ..).trans_le ((neighbors_mem ..).1 hj)) ((neighbors_mem ..).1 hk))
    let V:= pondC univ T₁ i; have hv : V = neighbors w i:=by ext j; simp only [V,pondC,mem_filter,mem_univ,true_and]; change i∈neighbors w j ↔ _; rw [neighbors_mem,neighbors_mem,separation_comm]
    rw [sum_const,nsmul_eq_mul, show pondC univ T₁ i=neighbors w i from hv, mul_comm]; have he := neighbors_card w i -- check
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast he) (hf i).travel
lemma paleness (ht:0<t): Colors B (X₁) t d :=by
    have hP:= chief S X w h hv hr
    have hT₁:= vibes S X w hT; obtain ⟨f,hf,hq⟩:=h.zone; let U i:= coins (t:=ξ) S X i; have hw i:= wonders (S.view i) (S.addr i).support B.threshold (hT.gauge i) (hT.num i) (hT.real i) (hq i).gated
    have hh i:= wonders ((T₁).view i) (neighbors w i) B.threshold (hT₁.gauge i) (hT₁.num i) (hT₁.real i) (hP i).gated
    refine ⟨⟨?_,?_,fun i U h hU=> h (paidT S X w hv i U hU),?_⟩,?_,?_,?_,?_⟩
    · intro i x y H H'; refine congr_arg₂ (·-·) ?_ (clearUse _ i (hP i).room ξ x y H H'); refine sum_congr rfl fun j hj=>?_ ; have he:=mem_filter.mp hj; have h':(S.addr j).support⊆neighbors w i:= he.2 ▸ hv j he.1
      exact Work.H03.reads_larger h' (clearUse _ _ (hq j).room ξ) _ _ H H'
    · intro i; exact (Finset.measurable_fun_sum _ fun i _=> RG.masked_measurable _ _ _ (hq i).Borel).sub (RG.masked_measurable _ _ _ (hP _).Borel)
    · intro i V; refine wingsZ (neighbors w i) _ _ (?_) ((hh i).2 V|>.2.2); unfold Gated coins; rw [map_sum]; apply Subalgebra.sum_mem; intro j h; have he:= mem_filter.mp h; exact gateMon _ _ (he.2 ▸ (hv j he.1)) _ ((hw j).2 _|>.2.2) -- variance
    · intro i V k; refine congr_arg Subtype.val (show sways (Lat.rotates N k) ((X₁).mean i (Lattice.gauge k V))=_ from ?_); change sways _ (U i _-_) = U i V-_; rw [map_sub]; apply congr_arg₂ (·-·) _ (Subtype.ext ((hh i).1 V k)); unfold U coins; rw [map_sum]; exact sum_congr rfl fun j _=> Subtype.ext ((hw j).1 V k)
    · intro i V; change Regal c N (U i _-_)=U i _-_; rw [map_sub]; apply congr_arg₂ (·-·) _ ((hh i).2 _|>.2.1); unfold U coins; rw [map_sum]; exact sum_congr rfl fun j _=> ((hw j).2 _|>.2.1)
    · intro i V W h; change sways _ (U i _-_)=U i _-_; rw [map_sub]; apply congr_arg₂ (·-·) _ (((hh i).2 V).1 W h); unfold U coins; rw [map_sum]; exact sum_congr rfl fun j _=> (((hw j).2 V).1 W h)
    intro i V; by_cases he:Healthy B.threshold (neighbors w i) V
    · rw [paidT _ _ _ hv _ _ he,map_zero,norm_zero]; exact (hP i).travel
    change ‖token _ _ _ (coins _ _ _ _-letters T₁ ξ V i)‖≤ _; rw [letters,show ((T₁).addr i).support=neighbors w i from rfl, masked_ne _ _ _ _ he,sub_zero]; unfold coins; rw [map_sum]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=f) ?_).trans (balanceK S X i f _ hf hr (fun i=>(hq i).travel))); intro j hj; by_cases hz:Healthy B.threshold (S.addr j).support V
    · unfold letters; rw [masked_eq _ _ _ _ hz]; exact (shot (lens (S.addr j).site) _ t ht).trans ((hq _).sizeU V hz)
    unfold letters; rw [masked_ne _ _ _ _ hz,map_zero,norm_zero]; exact (hq j).travel
end short
end YM.QCD.Grove
