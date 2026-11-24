import YM.QCD.Fold.River
/-! # one-color board. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry Port RG Leaf Tee LeafM Rudder Eyrie Sparks Garden YM.Next.Free Loom
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C:Side}{D b B k :ℕ}{L: Window c C D}
variable (L:Window c C D)(d:c.val ∣ C.val)(h:L.cut=(⇑(splitter d)))(p:Site C→ℂ)(hp:Quaint L p)
def deck : Collum c C (Site c) (Site C) D:=⟨id,id,L,L.cut,p,d,h.symm,fun _=>rfl⟩
local notation "r"=> singleR c
local notation "R"=>singleR C
local notation "D₀"=> deck L d h p
include hp
lemma plaque {u:Strut c}{v:Strut C}(hs:v.1=u.1)(he:L.cut v.2=u.2){T:Spike}(g:Site c→ℂ)(ht:Warrant (raise r u) g T):∃ f, Warrant (raise R v) f T∧ (D₀).salt u v g f (sun r) (sun R):=by
    have hh : L.cut (raise R v).2=(raise r u).2:=by unfold Strut.raise; dsimp only; rwa [monotype,monotype]
    have hG:= pegs L d h (show (raise R v).1=(raise r u).1 from hs) hh
    obtain ⟨f,H,hF⟩:= belt L hp hG T ht; exact ⟨f,H,hs,hG.2,fun i=>congr_fun hG.2 i,hF⟩
lemma tucks (u:Strut c)(f:Site c→ℂ)(T:Spike)(hr:Warrant (raise r u) f T):∃ v g, Warrant (raise R v) g T ∧ (D₀).salt u v f g (sun r) (sun R):=by
    obtain ⟨w,hw⟩:= Macrame.seeds d u.2; exact ⟨(u.1,w),plaque L d h p hp (show ((u.1,w):Strut C).1=u.1 from rfl) (show L.cut w=u.2 from h.symm ▸ hw) f hr⟩
open Collum
lemma litter (x y:Site C) (hr:L.cut x=L.cut y): ∃ w z,(D₀).salt (pin r) w (fun _=>1) z (sun r) (sun R)∧Warrant (raise R w) z 1∧ (sun R).shiftP w x=y:=by
    let w :Strut C:=(1,y-x); have hf:L.cut w.2=0:=by rw [h,map_sub, show splitter d x= _ from (show splitter d x=splitter d y from h ▸ hr),sub_self]
    obtain ⟨g,hp,hV⟩:= plaque L d h p hp (show w.1=(pin r).1 from rfl) (show L.cut w.2=(pin r).2 from hf) (fun _=>1) pin_cost; refine ⟨w,g,hV,hp,?_⟩; change affine 1 ((R).embed (y-x)) x=y; rw [monotype]; simp [affine]
open Villa Pine
variable {W:Land C (Site C) (Site C)}{Y:Pays C (Site C) (Site C)}{Q:Plan k}{Z:Train k}{a t w :ℝ}
lemma needed (T:Plan k)(Z:Train k): Receives (deck L d h p) (wood T (0:Site C) Z) (wood T (0:Site c) Z):=by
   refine ⟨L.fold,fun i=>?_,fun U i j=> rule L p hp _ _ (balmW T Z L p hp U) i j⟩; rcases hp.sign i with h|h <;> change ‖p i‖=_ <;> rw [h] <;>simp
lemma strives (hf:Run.Pack id id a t b (wood Q 0 Z) w W Y)(hW:Torch W)(hr:0 ≤ t)(hv:4*B+3<c.val):
   Run.Pack id id a t b (wood Q 0 Z) w ((deck L d h p).cloud W b B) ((deck L d h p).payC Y b B) ∧ Torch ((deck L d h p).cloud W b B):=by
      refine ⟨(deck L d h p).plates W Y b B hf hv (needed L d h p hp Q Z) hr, (deck L d h p).holds hW.1 (tucks L d h p hp) b B,(deck L d h p).wax b B W hW.2⟩
end YM.QCD.Folding
#print axioms YM.QCD.Folding.strives
