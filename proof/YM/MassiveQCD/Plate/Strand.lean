import YM.MassiveQCD.Plate.Sight
/-! # Restoring regular exponent on the new physical phase shelves (even with odd sources) -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{m k B N:ℕ}{s t h a r η σ:ℝ}{P:BudgetPoint}{J D I E:Type}[Fintype I]
set_option quotPrecheck false
local notation "Z"=> Keys c N
local notation "R"=> Spine I
local notation "M"=> Ribbon.ample N I
local notation "mkr"=>Patio (Keys c N⊕Spine I)
namespace Reel
variable (N)(p:I→Site c)(q:I→Bool)(φ r₀:ℝ)(G: Gem c (ample N I) E)(Ω:E→Finset I)(A:Set (Finset I))
local notation "w"=> withdraw N p φ
local notation "v"=> (turn I (D:=Z) r₀).comp w
local notation "F"=> Finset I
local notation "e!"=> v
noncomputable abbrev Answer:= {i:E // Ω i∈ A∧(Ω i).Nonempty∧(Ω i).image p⊆(G.addr i).support }
local notation "J'"=> Answer N p G Ω A
noncomputable def render: Reel c N I (Answer N p G Ω A):= ⟨G.addr ∘ Subtype.val, Ω ∘ Subtype.val, fun i U=> v (G.view i.val U)⟩
local notation "B'"=>render N p φ r₀ G Ω A
variable (X:Reel c N I E)
instance [Countable E]: Countable (Answer N p G Ω A):=Subtype.countable
variable (hp :∀ i U,Mint N p φ q (Ω i) (G.view i U))(ht:0<φ)(hv: G.Gather) (hx:∀ i,shadeG (G.view i))
include ht hp hv
include hx
lemma new_book : (B').Book p q:=by
   refine ⟨fun i=> i.2.2.1, fun i=>i.2.2.2,fun i=>(e!).toLinearMap.toContinuousLinearMap.measurable.comp (hv.reads _),fun i x y hh=> congr_arg (e!) (hv.sees _ x y hh),fun i U=>⟨cloak r₀ (Ω i.val) _ q (hp i.val U).shows,?_⟩,?_⟩
   · intro j; change pluck Z j ((turn I r₀) (w (G.view i.val U)))∈_; rw [turned]; exact hopeful N r₀ _ _ (pennied N p φ j _ _ (hv.role i.val U))
   intro i U z; let X:= G.view i.val (Lattice.gauge z U); let Y:= w X; let W:=G.view i.val U; let pf:=parcelColor N z I
   have h':pf Y=w W:=by apply Eq.trans (Cupola.home N p φ ht (pf Y)).symm; apply congr_arg; let K:= trade (Lat.rotates M z); have he:= hp i.val (Lattice.gauge z U); exact (across N p φ q _ z _ he.shows).trans ((congr_arg K.passL he.spark).trans (Subtype.ext (hx i.val U z)))
   exact (freeT r₀ Y z).symm.trans (congr_arg _ h')
omit hx ht hv
include ht
omit hp ht in
lemma vacuum (x:EvenA c (ample N I))(s:Finset I)(hh:Mint N p φ q s x) : rootR R Z (vacR R Z (v x))=if s=∅ then v x else 0:=by
    have hξ:=hh.shows; let F':= turn I (D:=Z) r₀; rw [← Film.personality N q]; have h: Polite q s (v x):= cloak r₀ s _ q hξ; split
    next hp=> subst s; exact eq_pick _ _ _ _ h
    next hp=> apply Subtype.ext; change stake _ (burst q ∅) (scrape Z _ (v x).val)=0; rw [h.spectral _ (fun e=> hp (burstUnique q e).symm),map_zero]
-- restoration. Message/body term addition *before wear OK*. no support expansion here. any desired orientation estimator at same cost if reads physically unchanged.Must use with operator morphism retaining Φ. 
omit ht
variable (W: Grid c) (s':Finset I)
lemma mast (i:E): Mint N p φ q (Ω i) (letters G t W i):= by unfold letters; by_cases he:Healthy t (G.addr i).support W; rw [masked_eq _ _ _ _ he]; exact hp i W; rw [masked_ne _ _ _ _ he]; exact Mint.none _
include ht hv
-- tent without tag if no T. Loom.sum at `Φ` real.H.S. 
local notation "p'"=> (rootR R Z).comp ((vacR R Z).comp v)
set_option linter.unusedSectionVars false in
lemma escape (i:E)(_hq:(Ω i).Nonempty)(hn:¬ (Ω i).image p⊆(G.addr i).support): G.view i W=0:=by
   let x:= G.view i W; let g:= w x; let Mx:= hp i W
   have hk:pluck Z (burst q (Ω i)) g=0:=confined N p φ _ x _ (hv.role _ _) (fun he=>hn ((Cupola.held_pins p _ _ q).1 he))
   have h:g=0:=by apply Subtype.ext; exact (Mx.shows.exact).symm.trans ((congr_arg _ hk).trans (map_zero _)) -- variable M notation conflict
   exact Mx.spark.symm.trans ((congr_arg _ h).trans (map_zero _))
local notation "S1"=> p'
local notation "U1"=> (shutter Z s')
lemma offsetS (i:E)(hu:(Ω i).Nonempty)(hS:¬(Ω i∈ A ∧(Ω i).Nonempty∧(Ω i).image p⊆(G.addr i).support)) (hA:(s'.powerset:Set (Finset I))⊆ A) : (U1) (v (letters G t W i))=0:=by
     by_cases hx: (Ω i).image p ⊆(G.addr i).support; swap; · have hp:= escape N p q φ G Ω hp ht hv W i hu hx; unfold letters; by_cases hh:Healthy t (G.addr i).support W; rw [masked_eq _ _ _ _ hh,hp,map_zero,map_zero]; rw [masked_ne _ _ _ _ hh,map_zero,map_zero]
     rw [stamen_h Z q (Ω i)]; rw [if_neg (fun hh=> hS ⟨hA (mem_powerset.mpr hh),hu,hx⟩)]; exact cloak r₀ _ _ _ (mast N p q φ G Ω hp W i).shows
omit hp ht hv in
lemma currentS (i:J') : mist B' t i W=v (letters G t W i.val):=by unfold letters mist; by_cases hh:Healthy t (G.addr i.val).support W; rw [masked_eq _ _ _ _ (show Healthy _ ((B').addr i).support W from hh),masked_eq _ _ _ _ hh]; rfl; rw [masked_ne _ _ _ _ (show ¬Healthy _ ((B').addr i).support W from hh),masked_ne _ _ _ _ hh,map_zero]
variable (hT:Summable (letters G t W))
omit hp ht hv
include hT
lemma pages : Summable fun i=> mist B' t i W:= by simp_rw [currentS N p φ r₀ G Ω A]; exact (((e!).toLinearMap.toContinuousLinearMap.hasSum hT.hasSum).summable).comp_injective Subtype.val_injective
include hp ht hv
lemma presenceD (hA: (s'.powerset:Set (Finset I))⊆ A): (U1) (v (Patron.total G t W))=(U1) ( p' (Patron.total G t W)+ rope B' t W):=by
   let x:=letters G t W; let f i:=U1 (v (x i)); let g i:=U1 (p' (x i)); let e:=rope B' t W; have he:Summable f:=(( (U1).comp v).toLinearMap.toContinuousLinearMap.hasSum hT.hasSum).summable
   have hh:Summable g:=(((U1).comp (p')).toLinearMap.toContinuousLinearMap.hasSum hT.hasSum).summable; rw [map_add]; let m:= Patron.total G t W
   apply eq_add_of_sub_eq' -- names. 
   have hg:= he.sub hh; let L:J'→ E:= Subtype.val
   have hr : ∀ i:J', f (L i)-g (L i)= U1 (mist B' t i W):=by
       intro i; rw [currentS]; unfold g; rw [show p' _=rootR R Z (vacR R Z (v (x (L i)))) from rfl,vacuum N p q φ r₀ _ _ ?_,if_neg (nonempty_iff_ne_empty.mp i.2.2.1),map_zero,sub_zero];
       exact mast N p q φ G Ω hp W i.val
   have hf: Function.support (f-g) ⊆ Set.range L:=fun i h=>by
       by_contra hd; change f i-g i≠0 at h; apply h; apply sub_eq_zero.mpr; unfold f g; have he':p' (x i)=if Ω i=∅ then v (x i) else 0:= vacuum N p q φ r₀ _ _ (mast N p q φ G Ω hp W i); rw [he']; split; rfl
       next hh=> rw [map_zero]; exact offsetS N p q φ r₀ G Ω A hp ht hv W s' i (nonempty_iff_ne_empty.mpr hh) (fun hx=>hd ⟨⟨i,hx⟩,rfl⟩) hA
   have hX: (∑' i,f i)-(∑' i,g i)=∑' i:J',U1 (mist B' t i W):=by rw [← he.tsum_sub hh]; exact (Subtype.val_injective (p:=fun i=> Ω i∈ A ∧(Ω i).Nonempty∧(Ω i).image p⊆(G.addr i).support)).tsum_eq hf |>.symm.trans (tsum_congr fun i=>hr i)
   exact Eq.trans (congr_arg₂ (· - ·) (((U1).comp v).toLinearMap.toContinuousLinearMap.map_tsum hT) (((U1).comp p').toLinearMap.toContinuousLinearMap.map_tsum hT)) (hX.trans (((U1).toLinearMap.toContinuousLinearMap.map_tsum (pages N p φ r₀ G Ω A W hT))).symm)
end Reel
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Reel.presenceD
