import YM.QCD.Grove.Shelf
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
open AnalyticBridge VerifiedReset -- conflicts.
section frac
variable (P:Gem c N I)(T:Finset I)(B:BudgetPoint)(s:ℕ) (h: SoilB T P B w t)(hp:w ≤ s) (x:Site c)
abbrev wharf (c:Side)(w:ℕ)(i:Site c): RegularAddress c:=⟨i,neighbors w i,halo_subset _ _ (mem_singleton_self _)⟩
noncomputable def helm (P:Gem c N I)(T:Finset I)(s:ℕ) : Gem c N (Site c):= ⟨wharf c s,orchid T P⟩
noncomputable def aleph : Ruby.Hue c N (Site c):=⟨fun i=>neighbors s i,fun i V=>buds i N (cashD T P V i (B:=B))-letters (helm P T s) B.threshold V i⟩
local notation "J'"=> helm P T s
local notation "V'"=> aleph P T B s
-- costume elementary S terms no psi Herm.
structure Colors (P:BudgetPoint)(U:Ruby.Hue c N I)(v d:ℝ) :Prop where
    tide : U.Tall P.threshold
    shape : ∀ i,shadeG (U.mean i)
    class' :∀ i V, Regal c N (U.mean i V)=U.mean i V
    flag : ∀ i V, Fit (U.mean i V)
    earn :∀ i V,‖token c N v (U.mean i V)‖ ≤ d
-- basic H stencil
include h
lemma coast : Dyed J' ∧∀ i,LocalOn (neighbors w i) ((J').view i):=by
    obtain ⟨he,hp,hk⟩:= notes T P h
    exact ⟨⟨fun i=>recast i _ (fun _=>1) hp,fun i V=> galaxy i _ (hk V).1,fun i V=> (joyous _ i).trans (congr_arg _ (hk V).2)⟩, mintL T P h⟩
omit h in
lemma wonders (f:Grid c→ EvenA c N)(W:Support c)(δ:ℝ)(ht:shadeG f)(hp:∀ x,Fit (f x))(hq:∀ x,Regal c N (f x)=f x)(hv:∀ U,Gated W (f U)):
   let f':=masked δ W f; shadeG f'∧∀ i, Fit (f' i)∧ Regal c N (f' i)=f' i∧ Gated W (f' i) :=by
    intro f'; refine ⟨fun i k=>?_,fun i=> ?_⟩
    · have h : Healthy δ W (gauge k i) ↔ Healthy δ W i:=by unfold Healthy; rw [gauge_flags]
      by_cases he:Healthy δ W i
      · unfold f'; rw [masked_eq _ _ _ _ (h.2 he),masked_eq _ _ _ _ he]; exact ht i k
      unfold f'; rw [masked_ne _ _ _ _ (mt h.1 he),masked_ne _ _ _ _ he]; exact congr_arg Subtype.val (map_zero (sways (Lat.rotates N k)))
    by_cases he:Healthy δ W i
    · unfold f'; rw [masked_eq _ _ _ _ he]; exact ⟨hp _,hq _,hv _⟩
    unfold f'; rw [masked_ne _ _ _ _ he]; exact ⟨fun _ _=> map_zero _,map_zero _, Loom.Fleet.spruce W⟩
include hp
lemma fiscal (hp': Pockets T P B t d)(he:0<t) : Colors B (aleph P T B s) t d :=by
   let U:=J'; have hx:=coast P T B s h -- B?
   have hf i (hi:i∈T):=wonders (P.view i) (P.addr i).support B.threshold (h.gauge i hi) (h.fit i hi) (h.real i hi) (h.fees i hi|>.choose_spec.gated)
   have hk i v:Gated (neighbors s i) (orchid T P i v):= gateMon _ _ (fun i hi=>(neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hp)) _ ((wind T P h 1 i (VerifiedReset.flat_ok ..)).2 _)
   have hz i:=wonders (c:=c) (U.view i) (neighbors s i) B.threshold (hx.1.gauge i) (hx.1.num i) (hx.1.real i) (hk i)
   let W i V:= letters U B.threshold V i; let f i V:= cashD T P (B:=B) V i; let Z i:= pondC T P i
   have hS i (V:Grid c)(hev:Healthy B.threshold (neighbors s i) V): (V').mean i V=0:=by
       change buds i N (cashD T P (B:=B) V i) - letters U B.threshold V i=_; rw [speak T P h V i (hev.mono_left (fun x hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hp))), letters, show (U.addr i).support=neighbors s i from rfl,masked_eq _ _ _ _ hev]; rw [show U.view i V=_ from ornate T P h V i,sub_self]
   have hQ i:UsesFinal B.threshold (neighbors s i) (f i) :=fun x y hv H=> sum_congr rfl (fun j hj=> by have hh:= mem_filter.mp hj; exact Work.H03.reads_larger (Finset.Subset.trans (h.tortillas _ hh.1 _ hh.2) (fun z hi=>(neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hp))) (Stew.clearUse P j (h.fees j hh.1|>.choose_spec.room) B.threshold) x y hv H ) -- order
   have hA i:Measurable (f i):=Finset.measurable_fun_sum (Z i) fun j hj=> RG.masked_measurable _ _ _ (h.fees j (mem_filter.mp hj).1|>.choose_spec.Borel) -- with path
   have hΩ i:LocalOn (neighbors s i) (U.view i):=fun x y hV=> hx.2 i _ _ (agrees_mono hV (coe_subset.mpr (fun j hj=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hj).trans hp))))
   refine ⟨⟨fun i x y H H' => congr_arg₂ (·-·) (congr_arg (buds i N) (hQ i x y H H')) (clearUse U i (hΩ i) _ x y H H'),fun i=> ((buds i N).continuous.measurable.comp (hA i)).sub (RG.masked_measurable _ _ _ ((buds i N).continuous.measurable.comp (notes T P h).1)), fun i V ht he=> ht (hS i V he),?_⟩,?_,?_,?_,?_⟩
   · intro i V; refine wingsZ (neighbors s i) _ _ (green i (neighbors s i) (cashD T P (B:=B) V i) ?_) ((hz i).2 V|>.2.2); unfold Gated cashD; rw [map_sum]; refine Subalgebra.sum_mem _ fun j hj=>?_ ; have hh:=mem_filter.mp hj; exact gateMon _ _ ((h.tortillas _ hh.1 i hh.2).trans (fun z hh=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hh).trans hp))) _ ((hf j hh.1).2 _|>.2.2)
   · intro i V k; let A:=Lattice.gauge k V; let L:= Lat.rotates N k; apply congr_arg Subtype.val (show sways _ ((V').mean i _)=(V').mean i _ from ?_); change sways L (buds i N (cashD T P (B:=B) A i)-W i A)=buds i N _-W i V; rw [map_sub,sought]; apply congr_arg₂ (·-·); apply congr_arg; unfold cashD; rw [map_sum]; exact sum_congr rfl (fun j hj=> Subtype.ext ((hf j (mem_filter.mp hj).1).1 V k)); exact Subtype.ext ((hz i).1 V k)
   · intro i V; change Regal c N (buds i N (cashD T P (B:=B) V i)-W i V)=_; rw [map_sub,joyous,show Regal c N (W i V)=_ from ((hz i).2 V).2.1]; apply congr_arg (fun x=> buds i N x -W i V); unfold cashD; rw [map_sum]; exact sum_congr rfl fun j hj=> ((hf j (mem_filter.mp hj).1).2 V).2.1
   · intro i V g hh; have he:Fit (buds i N (cashD T P (B:=B) V i)):= galaxy i _ (fun k H=> by unfold cashD; rw [map_sum]; exact sum_congr rfl (fun j hj=> ((hf j (mem_filter.mp hj).1).2 V).1 k H))
     change sways _ (buds i N _-W i V)=_; rw [map_sub,he g hh,show sways (flute (Lat.Row c) g) (W i V)=W i V from ((hz i).2 V).1 g hh]; rfl
   intro i V; have h:= afloat P T hp' he V i; by_cases H:Healthy B.threshold (neighbors s i) V; · rw [hS i V H, map_zero, norm_zero]; exact h.2.2
   change ‖token _ _ _ (buds i N (f i V)-letters U B.threshold V i)‖≤d; rw [letters,show (U.addr i).support=neighbors s i from rfl,masked_ne _ _ _ _ H, sub_zero]; exact (corporation i _ t he).trans h.1
end frac
end YM.QCD.Grove
