import YM.QCD.Tide.Fount
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Revolve
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c}{r:Ratio c f} {K:KernelChoices}
open Flume YM.Next.Free Jets
variable {i j:ℕ} (P:Flight i j)(hf:f.val=c.val*P.L.val)
noncomputable def tallH (R:Cells.Cut c)(x:Stud c F):Stud c F:= coat (simple R) (foldsT R (coat (simple R) x))
lemma tallC (x:Stud c F)(C: Lat.Cut c F)(hc:C.t=0): crown R C x=tallH R x:=by
    unfold crown tallH; rw [show mount R C=simple R by unfold mount simple; rw [hc]; rfl] -- let
lemma tallCost (x:Stud c F)(hp:Tide.Stays x): Tide.Stays (tallH R x):= coating _ _ (foldsPay _ (coating _ _ hp))
lemma huesT (x:Stud c F)(U:Grid c): tallH R x U = tilt (copies F (lens R)) (x (R.pullC su U)):= (lensF R _).symm
lemma utter (h:P.patch.Branches K su)(x:Stud c F)(hp:Tide.Stays x)(hv:R.kind=.link): tallH (gateH R (sliceL P hf)) (offer P K hf β x)=offer P K hf β (tallH R x):=by
    let S:=P.visit K hf; let T:=gateH R (sliceL P hf); let A:= copies F (lens R); let B:= copies F (lens T)
    have h1:star A=A:=by unfold A; rw [← copies_star,lens_star]
    have h2:A*A=1:=by unfold A; rw [← copies_mul,lens_sq,copies_one]
    have h3:star B=B:=by unfold B; rw [← copies_star,lens_star]
    have h4:B*B=1:=by unfold B; rw [← copies_mul,lens_sq,copies_one]
    let i:= T.pullC su; let j:= R.pullC su; let H:=ater P hf (F:=F)
    have he(U:Grid f): H (i U)=A*H U*B:=by
       change choir F (tied P hf 0 (i U))=_; rw [show tied P hf 0 (i U)=_ from towers P hf hv U, choir_mul,choir_mul]; rfl
    have hz(U:Grid f)(V:Grid c): S.density β (i U) (j V)= S.density β U V:=by
         have ht:= S.channel (G:=su) h R.flip R.slide β U V
         rw [show S.ratio.embed R.slide=_ from slippery R (sliceL P hf) hv P.odd] at ht; exact ht
    let Z:= brook S β x
    funext U; rw [huesT]; change tilt B (furnace (H (i U)) (Z (i U)))=furnace (H U) (brook S β (tallH R x) U)
    rw [frosts _ _ h1 h2 h3 h4]; rw [he, Matrix.mul_assoc A (A*_*B), Matrix.mul_assoc (A*_) B, h4,Matrix.mul_one, ← Matrix.mul_assoc A A, h2, Matrix.one_mul]; congr 1
    let M:=muter (tilt A) (tilt_cont _); have hm: (fun U=> M (x (j U)))=tallH R x:=funext fun U=> (huesT x U).symm; exact Eq.trans (bruM (S:=S) h x hp M U (i U) j (prior_pull ..) (hz U)) (congr_arg (fun x=> brook S β x U) hm)
lemma tallSite (x:Stud c F)(S T : Set (Site c))(hp:Uses S x)(he:Set.MapsTo R.reflect S T): Uses T (tallH R x):= coatS _ _ (foldsS _ (coatS _ _ hp) he)
-- margins(F shrink or choose d same)
noncomputable def longM (P:Patch):=40*(P.J+3)
lemma margin (P:Patch):longM P + fuel P ≤ longM P*P.L.val:=by
    unfold longM fuel Patch.radius; have hp:= P.coarse
    let X:=P.J+3; change 40*X+20*(X*_ ) ≤ 40 * X*_ ; nlinarith
noncomputable def eaves (R:Cells.Cut c)(d:ℕ): Set (Site c):={x | d ≤ R.distance x ∧ R.distance x +d < R.half.val}
lemma eaveH (d:ℕ)(h:R.kind=.link): eaves R d⊆ R.sector:=fun i hi=>by
     change R.kind.Strict R.half.val (R.distance i); rw [h]; exact lt_of_le_of_lt (Nat.le_add_right (R.distance i) _) hi.2
lemma slipstream (x:Site c)(p q:ℕ)(hu: p+q ≤ p*r.count.val)(hx:x ∈ eaves R p) : Push.GridApprox.window (r.embed x) q⊆ eaves (gateH R r) p:=by
     let v:=R.pos; let L:= r.count.val; let d:=r.count.val/2; let J:= R.distance x; let T:=gateH R r
     rintro y ⟨z,hz,rfl⟩; let M:=wrap f z+r.embed x
     have hv : M v - T.baseLine=(z v:ℤ)+ (↑(J*L+d):Per f):=by
         change ((z v:ℤ): Per f)+ _ - (perM r v R.baseLine-(d:Per f))=_ -- verify coercion
         rw [← per_root]; push_cast
         rw [show ((J:Per f) * (L: Per f)) = perM r v (x v-R.baseLine) from ?_,map_sub]; ring
         simpa only [Nat.cast_mul,v,J,L,Cells.Cut.distance] using (per_val r _ v).symm
     have ht:= box_test.mp (show z∈box _ from hz); have h1:= ht.1 R.pos; have h2:=ht.2 R.pos; obtain ⟨h,H⟩:=hx; change p≤J at h; change J+p< R.half.val at H; change p+q≤p*L at hu
     let D:ℤ:=z v + (↑(J*L+d):ℤ)
     have hh: (p:ℤ) ≤ D:=by
          have hp: p+q≤ J*L:= hu.trans (Nat.mul_le_mul_right L h); change -(q:ℤ) ≤ z v at h1; unfold D; omega
     have hk : D+(p:ℤ)< ((T.half.val:ℕ):ℤ):=by
         change D+_ < ((R.half*r.count:Side).val:ℤ); rw [PNat.mul_coe]
         have hm : J*L+p*L+L ≤ R.half.val*L:=by have he:= (Nat.mul_le_mul_right L H); calc
                         _=((J+p)+1)*L:=by ring
                         _ ≤ _:=he
         have he:= r.count.property; have he' : d < L:= by unfold d L; exact Nat.div_lt_self he (by omega)
         change z v≤(q:ℤ) at h2
         unfold D; change z v+_+_ < (↑(R.half.val*L):ℤ); omega
     have Hm:T.distance M=D.toNat:=by
         have hn:f.val=2*T.half.val:= T.even; have h1 : 0 ≤ D:=by omega
         unfold Cells.Cut.distance; change (M v-T.baseLine).val =_
         rw [hv,← ZMod.val_natCast_of_lt (show D.toNat<f.val by omega)]; apply congr_arg ZMod.val
         calc _=(D:Per f):=by unfold D; push_cast; rfl
              _= _:=by exact (congrArg (fun i:ℤ => (i:Per f)) (Int.toNat_of_nonneg h1).symm).trans (Int.cast_natCast ..) -- check rewrites
     change p≤T.distance M ∧ T.distance M+p< T.half.val; rw [Hm]; omega
lemma struts (x): ∀ hx:x∈ eaves R (longM P.patch), Push.GridApprox.window ((sliceL P hf).embed x) (fuel P.patch)⊆eaves (gateH R (sliceL P hf)) (longM P.patch):= fun hx=> slipstream x _ _ (margin P.patch) hx
end YM.QCD.Tide
