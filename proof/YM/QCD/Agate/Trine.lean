import YM.QCD.Agate.Mint
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f G K L: Side}{F i j:ℕ}{β t:ℝ} {D Y:Lot}
open Tide Flume YM.Next.Free
variable (P:Flight i j)(h:f.val=c.val*P.L.val){p:Site c}{U:Grid f}
lemma courseW (x:Cover)(s: Walk): visits x s = (visits (0:Cover) s).map fun y=> y+x:=by
   have h(z:Cover)(w: Walk): visits (z+x) w=(visits z w).map fun y=> y+x:=by
        induction w generalizing z with
        | nil=> rfl
        | cons a w ih =>simp only [visits,List.map_cons,add_right_comm z x,ih]
   simpa only [zero_add] using h 0 s
lemma course (x:Court D)(u:P.patch.Points)(o:Lattice.Order)(y:Cover)(hp:y∈ visits (P.L.val • x.val) (route 0 u.val o)):y∈rimH D P.patch:=by
   rw [courseW] at hp; obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hp; apply punch; refine box_larger (visitsB _ _ (center_box 0) z hz) ?_; have he := Push.Uniform.routeLe P.patch P.patch.center u o; have hk:0=(P.patch.center).val:=rfl; unfold fuel; rw [← hk] at he; omega
lemma kitchen (x:Court D)(p: Site c):window ((sliceL P h).embed (leap p x.val)) (fuel P.patch) ⊆ windows (rimH D P.patch) ((sliceL P h).embed p):=by
   rintro y ⟨z,hz,rfl⟩; refine ⟨z+P.L.val • x.val,punch _ x z hz,?_⟩; dsimp only; rw [embeddedH]; unfold leap; rw [map_add,add_assoc] -- test
lemma sight (x:Pad D F)(y:Modes f F)(hp: ater P h U (pens p x) y ≠ 0): y∈ Set.range (pens (D:=rimH D P.patch) ((sliceL P h).embed p)):=by
    have ht:=trains P h (F:=F); let k:= pens p x; let Y:= (sliceL P h).embed k.1.1; have hk:y.1.1∈ Kit.view Y (fuel P.patch):=by by_contra H; exact hp (ht.absent k y H U)
    obtain ⟨z,hz,H⟩:= kitchen P h x.1.1 p (mind Y (fuel P.patch) hk); exact ⟨((⟨z,hz⟩,y.1.2),y.2),Prod.ext (Prod.ext H rfl) rfl⟩
variable (Q:Site G)(H:K.val=G.val*P.L.val){V:Grid K}
variable (p:Site c)(hc: Fits f (rimH D P.patch))(hd:Fits K (rimH D P.patch))
variable (ht:stoke ((sliceL P h).embed p) (rimH D P.patch))(hu:stoke ((sliceL P H).embed Q) (rimH D P.patch))(hv:crest (D:=rimH D P.patch) ((sliceL P h).embed p) U=crest ((sliceL P H).embed Q) V)
include hv hc hd ht hu
lemma startled (x:Pad D F)(y:Pad (rimH D P.patch) F): let A:=pens p x; let B:=pens Q x; let i:= pens ((sliceL P h).embed p) y; let j:= pens ((sliceL P H).embed Q) y; ater P h U A i=ater P H V B j:=by
   intro A B i j; have he (u:P.patch.Points)(o:Lattice.Order): (scoop (sliceL P h)*routeM 0 U (route 0 u.val o)) A.1 i.1=(scoop (sliceL P H)*routeM 0 V (route 0 u.val o)) B.1 j.1:=by
        rw [shows,shows]; unfold A B i j mouth pens; dsimp only; rw [embeddedH,embeddedH]; exact hike _ hc _ _ _ (course P x.1.1 u o) _ _ y.1.1.2 _ _ _ hd ht hu hv
   have hh:tied P h 0 U A.1 i.1=tied P H 0 V B.1 j.1:=by
        unfold tied lineF; simp only [Matrix.smul_apply,Matrix.sum_apply,he]
   unfold ater choir; simp only [Matrix.blockDiagonal_apply,hh]; split
   next hX=> rw [if_pos (show B.2=j.2 from hX)]
   next hX=> rw [if_neg (show B.2≠j.2 from hX)]
end YM.QCD.Agate
