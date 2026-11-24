import YM.QCD.Grove.Lobby
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
-- Tile independent area => panel local 
structure SoilB (T:Finset I)(S:Gem c N I) (P:BudgetPoint)(w:ℕ)(t:ℝ):Prop where
    fees i : i∈ T → ∃ b, Woven (S.addr i).site (S.addr i).support P t (S.view i) b
    tortillas :∀ i∈T,∀ x∈(S.addr i).support,(S.addr i).support⊆ neighbors w x
    gauge i : i ∈ T → shadeG (S.view i)
    fit i : i∈ T→ ∀ U, Fit (S.view i U)
    real i : i∈ T→∀ U, Regal c N (S.view i U)=S.view i U
variable (T:Finset I)(S:Gem c N I)
def primed (U: Grid c): EvenA c N:= ∑ i∈ T,S.view i U
noncomputable def orchid (x:Site c) :Grid c→ EvenA c N:= buds x N ∘ primed T S
noncomputable def pondC (x:Site c):= T.filter fun i=> x∈ (S.addr i).support
noncomputable def cashD {B:BudgetPoint} (V:Grid c) (x:Site c): EvenA c N:= ∑ i ∈ pondC T S x, letters S B.threshold V i -- B implicit
variable (hp:SoilB T S B w t)
include hp
lemma ornate (U:Grid c)(x:Site c): orchid T S x U= buds x N (primed (pondC T S x) S U):=by
   unfold orchid primed; simp only [Function.comp_apply,map_sum]; symm; refine sum_subset (filter_subset ..) fun i hi h=>?_ ; obtain ⟨b,hb⟩:=hp.fees i hi; exact sprout x _ _ (hb.gated _) (fun hk=>h (mem_filter.mpr ⟨hi,hk⟩))
lemma speak (U:Grid c)(x:Site c)(h:Healthy B.threshold (neighbors w x) U): cashD T S (B:=B) U x=primed (pondC T S x) S U:=by
    unfold cashD primed; apply sum_congr rfl; intro i hi; have he:=mem_filter.mp hi; exact masked_eq _ _ _ _ (h.mono_left (hp.tortillas i he.1 x he.2))
lemma wind (Z:Grid c)(x:Site c)(hZ:Healthy B.threshold (neighbors w x) Z): Push.Local.Chart B.order (orchid T S x) Z ∧ (∀ V,Gated (neighbors w x) (orchid T S x V)):=by
    let P:=primed (pondC T S x) S; rw [funext (fun U=>ornate T S hp U x)]; have hf(i)(hi:i ∈ pondC T S x): Push.Local.Chart B.order (S.view i) Z ∧ (∀ V,Gated (neighbors w x) (S.view i V)):=by
        have he:=mem_filter.mp hi; obtain ⟨u,hu⟩:=hp.fees i he.1; have hz:= hu.stretches (hp.tortillas i he.1 _ he.2) le_rfl; exact ⟨hz.use Z hZ,hz.gated⟩
    have h : Push.Local.Chart B.order P Z:= ContDiffAt.sum fun i hi=> (hf i hi).1
    refine ⟨(buds x N).contDiff.contDiffAt.comp 0 h,fun i=>green x _ _ ?_⟩; unfold Gated; unfold primed; rw [map_sum]; exact Subalgebra.sum_mem _ fun i hi=> (hf i hi).2 _
lemma mint (V:Grid c)(hv:flags B.threshold V=∅): Push.Local.Chart B.order (primed T S) V:=by
    refine ContDiffAt.sum (f:=fun i U=> S.view i (increment V U)) fun i hi=> ?_; obtain ⟨p,hp⟩:=hp.fees i hi; exact hp.use _ (by unfold Healthy; rw [hv]; simp)
lemma notes : Measurable (primed T S)∧ shadeG (primed T S)∧∀ V, Fit (primed T S V) ∧ Regal c N (primed T S V)=primed T S V:=by
   refine ⟨measurable_fun_sum _ (fun i hi=>(hp.fees i hi).choose_spec.Borel),fun U k=> ?_,fun V=>⟨fun W hx=>?_,?_⟩⟩
   · suffices he: sways (Lat.rotates N k) (primed T S (Lattice.gauge k U))=primed T S U from congr_arg Subtype.val he -- better
     unfold primed; rw [map_sum]; exact sum_congr rfl fun i hi=> Subtype.ext (hp.gauge i hi U k)
   · unfold primed; rw [map_sum]; exact sum_congr rfl fun i hi=>hp.fit i hi V _ hx
   unfold primed; rw [map_sum]; exact sum_congr rfl fun i hi=>hp.real i hi V
lemma mintL (x:Site c): LocalOn (neighbors w x) (orchid T S x):=by
    intro U V h; rw [ornate _ _ hp,ornate _ _ hp]; apply congr_arg; refine sum_congr rfl fun i hi=> ?_; have he:=mem_filter.mp hi; exact (hp.fees i he.1).choose_spec.room _ _ (agrees_mono h (coe_subset.mpr (hp.tortillas i he.1 _ he.2)))
noncomputable def duskQ (x:Site c)(U:Grid c):ℝ:= ∑ i∈ pondC T S x, (river c N (S.view i U))/(((S.addr i).support).card:ℝ) -- scalar SIGN
noncomputable def cloudQ {B:BudgetPoint} (x:Site c)(U:Grid c):ℝ:= ∑ i∈ pondC T S x, (river c N (letters S B.threshold U i))/(((S.addr i).support).card:ℝ) -- B
lemma utter (U:Grid c) (p:Site c)(hp':Healthy B.threshold (neighbors w p) U): cloudQ T S (B:=B) p U=duskQ T S p U:=by unfold cloudQ duskQ; apply sum_congr rfl; intro i hi; have he:=mem_filter.mp hi; unfold letters; rw [masked_eq _ _ _ _ (hp'.mono_left (hp.tortillas i he.1 _ he.2))]
end YM.QCD.Grove
