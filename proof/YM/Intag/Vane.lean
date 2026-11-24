import YM.Intag.Ground
import YM.QCD.Tide.Ingot
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Set Filter MeasureTheory
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Romance QCD QCD.Tide
open scoped BigOperators Classical
variable {c f l:Side}(g:Ratio c f)(r:Ratio f l)(G:Ratio c l)
variable (x y:Site f)(p:Site c)(he:Even c.val)(hp:Odd g.count.val) (hr:Odd r.count.val)
local notation "T" => mural g he x
local notation "n" => g.count.val
local notation "s"=> r.count.val
local notation "k"=> G.count.val
local notation "b"=> ((g.count.val/2):ℕ)
local notation "Tb"=>mural G he (r.embed x)
include he hp hr
lemma odd_v: Odd G.count.val:=by rw [size_comp g r]; exact hr.mul hp
omit he in
lemma vaneP : k/2=s*b + s/2 :=by
    obtain ⟨u,hu⟩:= hp; obtain ⟨w,hw⟩:= hr
    have hx:k/2=s*u+w:=by
      rw [size_comp g r]; have hv:s*n= 2*(s*u+w)+1:=by rw [hu,hw]; ring
      rw [hv]; omega
    rw [hx,show b=u by omega,show s/2=w by omega]
lemma stepSpan (k':ℕ): y∈(mural g he x).margin p k' ↔ r.embed y∈ (mural G he (r.embed x)).margin p (s*k'):=by
      rw [key_margin g x y p he hp,key_margin G (r.embed x) _ p he (odd_v g r G he hp hr)]
      rw [embed_comp g r,show r.embed x+r.embed (g.embed p)= r.embed (x+g.embed p) from (r.root.map_add _ _).symm,both,vaneP g r G hp hr,← mul_add]; constructor
      · intro h; exact (Nat.mul_le_mul_left s h).trans (Nat.le_add_right _ _)
      intro h; by_contra! hv; have ht:= Nat.mul_le_mul_left s hv; have hp0:s >0:=r.count.property; rw [Nat.mul_succ] at ht; omega
omit hr in
lemma swath (u:Site f): (mural g he x).copyMap p u= ((T).omega p).act (u-x) + (x+g.embed p):=by
   have hh:= tuned g he hp x p; rw [Tiling.copyMap,affine] at hh ⊢; rw [← hh, ((T).omega p).act_sub]; abel
lemma maps_step (u : Site f) : (mural G he (r.embed x)).copyMap p (r.embed u)=r.embed ((mural g he x).copyMap p u):=by
   rw [swath g x p he hp u, swath G _ p he (odd_v g r G he hp hr)]
   change _ = r.root _; rw [map_add, map_add, Ratio.root_embed r, r.signed]; change _ = ((Tb).omega p).act (r.root (u-x))+ (r.embed x+r.embed (g.embed p)); rw [map_sub, embed_comp g r G]; rfl

omit he hp hr in
private lemma eq_cut (C H : Cut c)(hx:C.kind=H.kind)(hp:C.pos=H.pos)(hz:C.baseLine=H.baseLine): C=H:=by
    have hh:C.half=H.half:=Subtype.ext ((Nat.mul_right_inj (by norm_num:(2:ℕ)≠0)).mp (C.even.symm.trans H.even)); cases C; cases H; congr
lemma bankcut (a:Axis): (mural G he (r.embed x)).bandCut p a = gateH ((mural g he x).bandCut p a) r:=by
    refine eq_cut _ _ rfl rfl ?_; change (Tb).starts p a=perM r a ((T).starts p a)-_ -- implicit div weird
    apply sub_eq_zero.mp
    have h₁ := behind g x p he hp a; apply_fun (perM r a) at h₁; rw [map_add,per_nat, per_root r (x+g.embed p) a] at h₁; have h₂:= behind G (r.embed x) p he (odd_v g r G he hp hr) a
    rw [show r.embed (x+g.embed p)= r.embed x+ G.embed p from (r.root.map_add ..|>.trans (by rw [embed_comp g r G]; rfl)),← h₂,vaneP g r G hp hr,mul_comm _ b,Nat.cast_add] at h₁; rw [show (↑(s/2 : ℕ):Per l)= (perM r a ((T).starts p a))- (Tb).starts p a from ?_]; abel
    linear_combination -h₁
lemma roomy (w:ℕ)(h:r.embed y ∈ (mural G he (r.embed x)).margin p w): s*separation y (x+g.embed p)+w ≤ k/2:=by
   have hv:=(key_margin _ _ _ _ _ (odd_v g r G he hp hr) w).mp h; rw [embed_comp g r, show r.embed x+r.embed (g.embed p)=r.embed (x+g.embed p) from (r.root.map_add ..).symm, both] at hv; exact hv
end YM.Intag
#print axioms YM.Intag.maps_step
#print axioms YM.Intag.bankcut
#print axioms YM.Intag.stepSpan
