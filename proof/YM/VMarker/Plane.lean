import YM.VMarker.Spare
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Twist
open QCD QCD.Grass QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Cupola Function Loom QCD.Cove
open MeasureTheory NormedSpace Filter
open Kites Ruby Finch Relight Plate Stew Stew.Phased Reggae
open scoped Topology BigOperators ContDiff Classical Matrix
variable {A B I E J K R U:Type}[Fintype I] {c:Side}{N:ℕ}
open Stitch
variable (P:Rise c N E K) (F:Reel c N I R)(G:Film c N I U)(O:Register P F G)
local notation "Z"=> Keys c N
local notation "Xq"=> Ribbon.Spine I
local notation "U★"=>rootR Xq (Keys c N)
local notation "P★"=>vacR Xq (Keys c N)
local notation "P₂"=> fun i=>rootR Xq Z ∘ P.plug i

local notation "Y★"=> result P F G O
variable {q:I→Bool}{p:I→Site c}{s a v u ε q0 w ξ η x:ℝ}{m:ℕ}{f:E→ℝ}{g:K→ℝ}
-- shared capacities; use given basis and startup extra ledgers. Use ALL support Boost estates.E.Shape
open Jets Jets.Touch Push.AbsoluteSums Ruby LanternK Tablet Footprint
open Dust Patron
-- package exact publishing with external F.BOOK issuance. can read before.Actual phase.
variable (U₀:Grid c)(t:ℝ) (h:(result P F G O).Staid t U₀)(he:Neat (result P F G O))
local notation "u₀"=> t
set_option quotPrecheck false
local notation "c₁"=> rootR Xq Z
local notation "c₀"=> vacR Xq Z
local notation "χ"=> (result P F G O)
variable (Y: Patron.Rail c N A)
noncomputable def bareRail (P:Rise c N E K): Patron.Rail c N K:= ⟨P.front,P.plug⟩
local notation "Pⁱ"=> bareRail P
lemma clean_tsum {T:Type}[NormedAddCommGroup T](p:A↪ B)(g:B→T)(f:A→T)(he:∀ i,f i=g (p i))(hg:Function.support g⊆Set.range p): ∑' i,f i=∑' i,g i:= (tsum_congr he).trans (p.injective.tsum_eq hg)
-- E.read mismatch.M Mark pay.Life
lemma dormant (i:R) : P.reading t U₀ (O.ear i)=0:=by
   unfold Rise.reading; rw [O.freeP]; by_cases h: Healthy t (P.row (O.ear i)).support U₀; rw [masked_eq _ _ _ _ h]; rfl; exact masked_ne _ _ _ _ h
include h he
lemma restore : ∑' i,(χ).read t U₀ i = c₁ (P.hyp t U₀) + F.rope t U₀ :=by
     let u:=(χ).read t U₀; let p:= P.reading t U₀; let f:E→ Tine c N I := fun i=> c₁ (p i) -- L wrong; remove annotation
     have hp i: c₀ (u i)=p i:=by unfold u p; unfold Rise.reading Tablet.read; by_cases h: Healthy t (P.row i).support U₀; rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; exact he.main i U₀; rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,map_zero]
     have he':Summable p:= (((c₀).toLinearMap.toContinuousLinearMap.hasSum h.exp.hasSum).summable).congr hp -- hp argu.Flip
     have hf:Summable f:= ((c₁).toLinearMap.toContinuousLinearMap.hasSum he'.hasSum).summable
     have hr: (∑' j,f j)= c₁ (P.hyp t U₀):= ((c₁).toLinearMap.toContinuousLinearMap.map_tsum he').symm; let g:=u-f
     have hx: support g ⊆ Set.range O.ear:=fun i hi=>by_contra (fun h=>hi (sub_eq_zero.mpr (rootE P F G O i h ..)))
     apply eq_add_of_sub_eq'; rw [←hr,←h.exp.tsum_sub hf]; refine (clean_tsum O.ear g _ ?_ hx).symm; intro i; change F.mist t i U₀=(χ).read t U₀ _- c₁ (P.reading t U₀ _); rw [dormant,pullE,map_zero,sub_zero]
variable (hq : Correspond (bareRail P) Y)
include h hq
omit he
omit h hq in
lemma mergeY {V:Type}[NormedCommRing V][CompleteSpace V] (F:B→ Hat c)(G:A→ Hat c)(e:A↪B)(hE:∀ i,F (e i)=G i)(H:Hat c)(f u:B→V) (g:A→ V)(hf:Summable fun i=>‖f i‖)(hu:Summable fun i=>‖u i‖) (hx:∀ i,f (e i)=g i)(hr:∀ i,u (e i)=0)(h:∀ i∉Set.range e,f i=u i): coin F f H=coin F u H+coin G g H:=by
    rw [fingerprint,fingerprint,fingerprint]; let v (f:B→ V) i:= if F i=H then f i else 0; apply eq_add_of_sub_eq'; rw [← (Film.aloneC F H f hf).tsum_sub (Film.aloneC F H u hu)]; let s i:=v f i-v u i; have hp:support s⊆Set.range e:=fun i hi=>by_contra fun he=> hi (by apply sub_eq_zero.mpr; unfold v; rw [h i he]); apply Eq.symm; apply clean_tsum e s _ _ hp; intro i; unfold s v; rw [hE,hx,hr]; split; exact (sub_zero ..).symm; exact (sub_self _).symm
omit hq in
lemma k_pose : Summable fun i=> ‖G.mark i U₀‖:=by
    let g (j:K):= ‖(χ).plug j U₀‖; have he: Summable fun i=> g (O.tag i):= h.plugs.comp_injective O.tag.injective; apply he.congr; intro i; unfold g; rw [(figuresK P F G O i).1]
omit hq h in
lemma cab_e (i:Finset K): (result P F G O).dusk t U₀ i= Plate.roof P.front (fun j=>(result P F G O).plug j U₀) (RG.flags t U₀) i :=by
    unfold Tablet.dusk Plate.roof; split
    next h₀=> exact (if_pos (show Arm .. from h₀)).symm
    next h₀=> exact (if_neg (fun (hx:Arm ..)=>h₀ hx)).symm
omit h in
lemma k_witness (U:Grid c)(H:Hat c) : coin Y.addr (c₁ ∘ (fun i=>Y.warp i U)) H= coin P.front (fun i=>c₁ (P.plug i U)) H:=by
    let Y₁ i:=Y.warp i U; let P₁ i:=P.plug i U; have hp:= hq.pays U;
    refine Eq.trans (readycoin Y.addr Y₁ _ (c₁).toLinearMap.toContinuousLinearMap (hq.coins U)) ((congr_arg (c₁) (hq.governs H U).symm).trans ?_); exact (readycoin P.front P₁ _ (c₁).toLinearMap.toContinuousLinearMap hp).symm
lemma k_sale (H:Hat c) : let g:= fun i=> (χ).plug i U₀; let m:=fun j=>Film.spruced N G Y j U₀; coin P.front g H=coin (Film.addressSets N G Y) m H:=by
    let V:=U₀; intro g m; let k:=Film.addressSets N G Y; let l i:=G.mark i V; have hl:= k_pose P F G O U₀ t h
    have hp:= hq.pays V; let Y₁ i:=Y.warp i V; let P₁ i:=P.plug i V; let e i:=c₁ (P₁ i)
    have he : coin k m H= coin Y.addr (c₁ ∘ Y₁) H+coin G.addr l H:= Eq.trans (show coin k m H= coin k (Sum.elim (c₁ ∘ Y₁) l) H from congr_arg (fun z=>coin k z H) (funext (by rintro (i|i) <;> rfl))) (Film.coin_merge Y.addr G.addr (c₁ ∘ Y₁) l (Film.payable (c₁).toLinearMap.toContinuousLinearMap (hq.coins V)) hl H) -- probably not defeq
    change coin P.front g H=coin k m H; have hr:coin Y.addr (c₁ ∘ Y₁) H=coin P.front e H:= k_witness (I:=I) P Y hq V H; rw [he,hr]; exact mergeY P.front G.addr O.tag O.mark H g e l h.plugs (Film.payable (c₁).toLinearMap.toContinuousLinearMap hp) (fun i=>congr_fun (figuresK P F G O i).1 V) (fun i=> by unfold e P₁; rw [O.freeG,Pi.zero_apply,map_zero]) (fun i hi=>congr_fun (orientK P F G O i hi).1 V)
set_option maxHeartbeats 440000 in
lemma shuttersK : ∑' i,(χ).dusk t U₀ i=Film.reports N G Y t U₀:=by
    let V:= U₀; let f:=P.plug; let g (j:K) :=(χ).plug j V; let l (i:U):=G.mark i V; have hl: Summable (fun i=> ‖l i‖):= k_pose P F G O U₀ t h
    let k:= Film.addressSets N G Y; let m:=fun j=>Film.spruced N G Y j V; let U':= RG.flags t V; have hh i: (χ).dusk t U₀ i=Plate.roof P.front g U' i:= cab_e P F G O U₀ t i
    rw [tsum_congr hh]; have hC : Film.reports N G Y t U₀= ∑' i,Plate.roof id (coin k m) U' i:= catalogue k m _ (Summable.sum _ (Film.payable (c₁).toLinearMap.toContinuousLinearMap (hq.coins V)) hl)
    have he:= (catalogue P.front g U' h.plugs); rw [he,hC]; exact congr_arg (fun x:Hat c→ Tine c N I=> ∑' i,Plate.roof id x U' i) (funext fun i=>k_sale P F G O U₀ t h Y hq i)
include he
lemma envoy : (χ).bluff t U₀= relativeE N F G Y (P.hyp t) t U₀:=by rw [Tablet.bluff, restore P F G O U₀ t h he, shuttersK P F G O U₀ t h Y hq]; rfl
end YM.MassiveQCD.Twist
#print axioms YM.MassiveQCD.Twist.envoy
