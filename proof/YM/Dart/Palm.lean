import YM.Dart.Roll
import YM.Needle.Stove
/-!
   Relative offsets and one-special-slot prices. Does NOT require the root cost held in
   an arbitrary offset background tiling. Big tile centres shift on the exact comparison plane.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) (d:ℕ)
local notation "S"=> C.S
set_option quotPrecheck false
-- Root shift accepts all slots. only one tracked orientation.W
namespace Roll
variable {c n f:Side}(g:Ratio c f)(l:Ratio f n)(G:Ratio c n)(he:Even c.val)(hl:Even f.val)(hg:Odd g.count.val)(hL:Odd l.count.val)
open Intag YM.Next.Rank.Station
variable {k:ℕ}(x:Fin k→Site n)(p:Site n)
include he hl hg hL
local notation "A"=> l.count.val
local notation "W"=> mural l hl p
variable (z:Site f)
local notation "Kᵢ"=>mural l hl (p+l.embed z)
local notation "Y"=>mural G he (p+l.embed z)
lemma graft (q:Site c)(hp:p ∈ (mural G he (p+l.embed z)).margin q l.count.val) (R:Regulator n 6)(hr:Goblet.Smoke (mural l hl p) R)(ht:R.Z≠0){X:Insertion n 6}{v:ℝ}(h: Gold R (mural l hl p) 0 X v) : Gold R (mural G he (p+l.embed z)) q X v:=by
     obtain ⟨L⟩:= Ladder.adorn g l G hg hL he hl (p+l.embed z); let k:= -z
     let v':= (0:Site f); have hz:z+k=(0:Site f):= add_neg_cancel z; have hx:(W).chamber (0:Site f)=(Kᵢ).chamber k:= by
          rw [←zero_margin _ _ (show (W).kind=.link from rfl), ←zero_margin _ _ (show (Kᵢ).kind=.link from rfl)]; exact Set.ext (fun i=>by have h:= Goblet.margV l hl p z k hL i 0; rw [hz] at h; exact h)
     have hQ:(mural l hl (p+l.embed z)).chamber k⊆ (Y).chamber q:= Ladder.here g l G hg hL he hl _ k q p (hx ▸ lies l hl hL p) hp
     obtain ⟨m,F,rfl,hF,hU⟩:= h; refine ⟨m,F,rfl,(fun i=>⟨(hF i).1.high (le_trans hx.le hQ), (hF i).2⟩),?_⟩
     -- hU stored W. apply ticks each
     refine le_trans (Finset.sum_le_sum (g:=fun i=>topH W R (F i) (0:Site f)) (fun i _=>?_)) hU
     let X(i:Fin m): Stud n 6:=⇑(F i); let V':Unit→Stud n 6:=fun _=>X i; have hp:= Ladder.ticks L R q [()] (fun _:Unit=>k) V' (List.nodup_singleton _) (fun i=> by simp) (Function.injective_of_subsingleton _) (fun _=>hQ) (fun _=>⟨hx ▸ (hF i).1,(hF i).2⟩) hr.real rfl (Ladder.fullC l hL hl (p+l.embed z)) hr.pos hr.cycle ht -- order ℓ. 
     have hw: topH W R (X i) (0:Site f)=topH Kᵢ R (X i) k:=by rw [← hz]; exact Goblet.repointed l hl p z R (X i) k (hF i).2 -- hazard runtime uses `W p 0` in p? p not.
     change topH (Y) R (X i) q ≤ topH W R (X i) (0:Site f); rw[hw]; simpa only[List.map_cons,List.map_nil, List.prod_cons,List.prod_nil,mul_one, Fintype.prod_unique] using hp
end Roll
variable {β ν:ℝ}(hC:C.Path β ν)
include hC
-- The only special-position thick estimator. All other placements assigned after.
lemma oneK {k:ℕ}(i j:ℕ)(z:Fin k)(u:Fin k→stalk C i)(v:Fin k→ℝ)(hy:∀ p,p≠z→ GreenP C i j (u p) (v p))(hu:FocusK C i (j+1) (u z) (v z))(f:Fin k→ Cover)(hF:seaM C i j f)(hg:k*8<(C.S.step j).L.val)(hk:j+1≤ C.N i): ‖readS C i u f‖ ≤ ∏ i,v i:=by
    let R:= (C.A i).regulator; let K:= (C.S).side (C.R i) (C.N i); let W:= Site ((C.S).side (C.R i) j); let g:=viewW C.S (C.R i) (show j≤j+1 from Nat.le_succ _); let l:=viewW C.S (C.R i) hk; let G:=viewW C.S (C.R i) (show j ≤ C.N i from Nat.le_of_lt hk)
    let hE:= evenW C.S (C.R i) (hC.even i) j; let he:=evenW C.S (C.R i) (hC.even i) (j+1); let X:= wrap K ∘ f; let t:=X z; have hL:g.count.val=(C.S.step j).L.val:=by change ratioTo C.S _ _=_; rw [step_factor (show j+1≤j+1 from le_rfl),Column.home_c,mul_one]
    obtain ⟨p,v',hM⟩:= Roll.windowZ g l G hE he (viewOdd ..) (viewOdd ..) X t (lt_of_lt_of_eq hg hL.symm)
    let T:=mural G hE (t+l.embed p); let S':=mural l he t; have hY:Injective v':=by intro k q he; by_contra hn; exact not_le_of_gt (hF k q hn) (T.extent (hM k).1 (show X q∈ T.chamber (v' k) from he.symm ▸ (show X q∈ T.chamber (v' q) from (hM q).1)))
    let Y(k':Fin k):= u k' (f k'); have hc:0 ≤R.β:=(hC.normalized i).beta_pos (Nat.le_refl _) |>.le; have h:= sideW hC i (C.N i)
    have hv(k':Fin k): Gold R T (v' k') (Y k') (v k'):=by
         by_cases ht:k'=z
         · subst k'; exact Roll.graft g l G hE he (viewOdd ..) (viewOdd ..) t p _ (Intag.padding G _ _ _ hE (viewOdd ..) (hM z) (by omega)) R ⟨rfl,h,rfl,hc,(engaged hC i)⟩ (engaged hC i) (hu hk (hC.even i) (f z))
         exact hy k' ht hk T rfl rfl _ (f k') (hM k')
    exact Gold.value (T:=T) v' hY Y v hv rfl rfl hc h (engaged hC i)
end YM.Massive.Needle
#print axioms YM.Massive.Needle.Roll.graft
#print axioms YM.Massive.Needle.oneK
