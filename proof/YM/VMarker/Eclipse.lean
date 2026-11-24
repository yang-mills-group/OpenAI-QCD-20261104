import YM.VMarker.JetRegister
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
local notation "X"=> Ribbon.Spine I
local notation "U★"=>rootR X (Keys c N)
local notation "P★"=>vacR X (Keys c N)
local notation "P₁"=> fun i=>rootR X Z ∘ P.main i
local notation "P₂"=> fun i=>rootR X Z ∘ P.plug i
noncomputable def result : Tablet P I:= ⟨clean O.ear F.mark (P₁),clean O.tag G.mark (P₂), clean O.ear F.z (fun _=>∅),clean O.tag G.z (fun _=>∅)⟩
local notation "Y★"=> result P F G O
variable (s:Finset I) (p:I→Site c)(q:I→Bool) {t a:ℝ}
lemma figures (i:R): (Y★).main (O.ear i)= F.mark i∧(Y★).spine (O.ear i)=F.z i:=by simp only [result,became, and_self]
lemma figuresK (i:U): (Y★).plug (O.tag i)= G.mark i∧(Y★).shadow (O.tag i)=G.z i:=by simp only [result,became, and_self]
lemma orient (i:E)(h:i∉Set.range O.ear): (Y★).main i=rootR X Z ∘ P.main i ∧ (Y★).spine i=∅:=by simp only [result,other _ _ _ _ h, and_self]
lemma orientK (i:K)(h:i∉Set.range O.tag): (Y★).plug i=rootR X Z ∘ P.plug i∧ (Y★).shadow i=∅:=by simp only [result,other _ _ _ _ h, and_self]
lemma crest_l (v:Support c)(x:EvenA c N)(h:Gated v x): lights ∅ v p q ((U★) x) :=by
    have hr : ((U★) x).val=stake Z (∅:Finset X) x.val:= (quiet ..).symm; refine ⟨?_,?_⟩
    · exact ⟨x.val,(by rw [Ribbon.burst_absent]; exact (quiet ..))⟩
    intro i; rw [hr,stakesX]; split; exact h; exact Subalgebra.zero_mem _
lemma root_turn (g:Lat.Frame c)(h i:EvenA c N)(hp:Lat.slots N g h.val=i.val): Stitch.color c N I g ((U★) h).val=((U★) i).val:=by -- slots namespace
   change carry X (Lat.slots N g).toLinearMap.toContinuousLinearMap (Ribbon.fiber _ h.val)=Ribbon.fiber _ i.val; rw [←quiet, ←quiet,speaks]; exact congr_arg _ hp
variable (h:P.Wave t) (hv:P.Reframe) (hF:F.Book p q)(hG:G.Beat N p q t)
include h hv hF hG
set_option maxHeartbeats 340000 in
lemma giveWave : Tablet.Wave (Y★) t q p:=by
    let R:= rootR X Z
    constructor
    · apply toggle O.ear; exact fun i=> O.homeP i |>.symm ▸ ((figures P F G O i).1.symm ▸ hF.room i); intro i hi; rw [(orient P F G O i hi).1]; intro x y he; exact congr_arg R (h.use i x y he)
    · apply toggle O.ear; · intro i V; rw [O.homeP,(figures P F G O i).1,(figures P F G O i).2]; exact hF.stage i V
      intro i he V; rw [(orient P F G O i he).1,(orient P F G O i he).2]; exact crest_l p q _ _ (h.appear i V)
    · apply toggle O.ear; exact fun i=>(figures P F G O i).1.symm ▸ hF.permit _; intro i he; rw [(orient P F G O i he).1]; exact R.toLinearMap.toContinuousLinearMap.measurable.comp (h.measure i)
    · apply toggle O.tag; · intro i; rw [O.mark,(figuresK P F G O i).1]; exact hG.reads i
      intro i hi; rw [(orientK P F G O i hi).1]; intro x y hx hy; exact congr_arg R (h.oblige i x y hx hy)
    · apply toggle O.tag; · intro i V; rw [O.mark,(figuresK P F G O i).1,(figuresK P F G O i).2]; exact hG.budget i V
      intro i hi V; rw [(orientK P F G O i hi).1,(orientK P F G O i hi).2]; exact crest_l p q _ _ (h.chair i V)
    · apply toggle O.tag; exact fun i=> (figuresK P F G O i).1.symm ▸ hG.matters _; intro i hi; rw [(orientK P F G O i hi).1]; exact R.toLinearMap.toContinuousLinearMap.measurable.comp (h.budget i)
    · apply toggle O.tag; · intro i; rw [O.mark,(figuresK P F G O i).1]; exact fun u hx=> hG.mask i u hx
      intro i hi; rw [(orientK P F G O i hi).1]; exact fun u hx=> h.permits i u (fun he=>hx ((congr_arg R he).trans (map_zero _)))
    · apply toggle O.ear; · intro i; rw [O.homeP,(figures P F G O i).2]; exact hF.stamp i
      intro i hi; rw [(orient P F G O i hi).2,image_empty]; exact empty_subset _
    · apply toggle O.tag; · intro i; rw [O.mark,(figuresK P F G O i).2]; exact hG.spark i
      intro i hi; rw [(orientK P F G O i hi).2,image_empty]; exact empty_subset _
    · apply toggle O.ear; · intro i; rw [(figures P F G O i).1]; exact fun x g=>congr_arg Subtype.val (hF.tint i x g)
      intro i hi; rw [(orient P F G O i hi).1]; exact fun V g=> root_turn g _ _ (hv.main i V g)
    apply toggle O.tag; · intro i; rw [(figuresK P F G O i).1]; exact fun x g=>congr_arg Subtype.val (hG.color i x g)
    intro i hi; rw [(orientK P F G O i hi).1]; exact fun V g=> root_turn g _ _ (hv.plug i V g)
omit h hv hF hG
lemma bleaching (x:Tine c N I)(he:Polite q s x)(h:s.Nonempty):vacR X Z x=0:=by apply Subtype.ext; change resetM _ _ x.val=0; rw [← he.exact,judgeB]; rw [if_neg (fun e=> nonempty_iff_ne_empty.mp h (burstUnique q (e.trans (burst_absent _).symm)))]
include hF hG
lemma nostalgia : Neat Y★:=by
    constructor
    · apply toggle O.ear; · intro i; rw [(figures P F G O i).1,O.freeP]; exact fun U=> bleaching _ q _ (hF.stage i U).1 (hF.stays i)
      intro i hi; rw [(orient P F G O i hi).1]; exact fun _=> off X _
    apply toggle O.tag; · intro i; rw [(figuresK P F G O i).1,O.freeG]; exact fun V=> bleaching _ q _ (hG.budget i V).1 (hG.commits i)
    intro i hi; rw [(orientK P F G O i hi).1]; exact fun _=> off X _
end YM.MassiveQCD.Twist
#print axioms YM.MassiveQCD.Twist.giveWave
