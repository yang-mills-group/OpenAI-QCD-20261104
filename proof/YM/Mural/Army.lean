import YM.Mural.Voces
import YM.VMarker.Eclipse
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
local notation "Y★"=> result P F G O
variable (s:Finset I) (p:I→Site c)(q:I→Bool) {t a:ℝ}
/-! Local receipt. Separates heat-domain use from color orientation. -/
structure Pillars (Jm:Support c) :Prop where
   stays i:(F.z i).Nonempty
   stamp i:(F.z i).image p⊆(F.addr i).support
   permit i:Measurable (F.mark i)
   room i:LocalOn (F.addr i).support (F.mark i)
   stage i U:Stitch.lights (F.z i) (F.addr i).support p q (F.mark i U)
   boast i: Jm⊆(F.addr i).support
structure Frails (t:ℝ) (Jm:Support c):Prop where
   commits i:(G.z i).Nonempty
   spark i:(G.z i).image p ⊆ (G.addr i).place
   matters i:Measurable (G.mark i)
   reads i: UsesFinal t (G.addr i).place (G.mark i)
   mask i U (h :G.mark i U≠0):RG.flags t U∩(G.addr i).place=(G.addr i).inv
   budget i V: Stitch.lights (G.z i) (G.addr i).place p q (G.mark i V)
   rails i: Jm⊆ (G.addr i).place
variable (Wm:Support c) (h:P.Wave t) (hv:P.Reframe) (hF:Pillars F p q Wm)(hG:Frails G p q t Wm)
include h hv hF hG
set_option maxHeartbeats 340000 in
lemma givingV : Tablet.Flora (Y★) t q p:=by
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
omit h hv

lemma nobility : Neat Y★:=by
    constructor
    · apply toggle O.ear; · intro i; rw [(figures P F G O i).1,O.freeP]; exact fun U=> bleaching _ q _ (hF.stage i U).1 (hF.stays i)
      intro i hi; rw [(orient P F G O i hi).1]; exact fun _=> off X _
    apply toggle O.tag; · intro i; rw [(figuresK P F G O i).1,O.freeG]; exact fun V=> bleaching _ q _ (hG.budget i V).1 (hG.commits i)
    intro i hi; rw [(orientK P F G O i hi).1]; exact fun _=> off X _
end YM.MassiveQCD.Twist
#print axioms YM.MassiveQCD.Twist.givingV
