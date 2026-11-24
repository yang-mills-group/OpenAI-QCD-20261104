import YM.QCD.Agate.Concur
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f G K L: Side}{F i j:ℕ}{β t:ℝ} {D S:Lot}
open Tide Flume YM.Next.Free Kites
open Acre.Rails.IV
noncomputable def hat (c: Side)(he: Even c.val): Side:= ⟨c.val/2,by obtain ⟨a,ha⟩:=he; have H:= c.property; change 0 < c.val at H; change 0 <c.val/2; omega⟩
noncomputable def FaceR (W: Wall)(hc: Even c.val): Cells.Cut c:= ⟨hat c hc,by obtain ⟨r,hr⟩:=hc; change c.val=2*(c.val/2); omega,.link,W.axis,W.post+(origin c) W.axis⟩
variable (W: Wall)(he: Even c.val) (hm:W.Within D S)
include he
lemma silent (V:Wall): Signed.act V.mirror (origin c)= (origin c) := by -- needs he include; c even
    funext i; by_cases h:i=V.axis; · subst i; simp only [Wall.mirror,Signed.mirror,Signed.act, Equiv.refl_symm,Equiv.refl_apply]; simp; have H:= (FaceR V he).zeroLength; change 2*(origin c V.axis)=0 at H; linear_combination -H
    simp [origin,Wall.mirror,Signed.act,Signed.mirror,h,Ne.symm h]
include W
lemma nes : 2*(↑(hat c he).val: Per c)= 0:= (FaceR W he).zeroLength -- use W included?
lemma windW : (FaceR W he).slide=wrap c W.save:=by
    unfold Cells.Cut.slide Wall.save; rw [map_zsmul, wrap_step]; funext i
    change (2*( (W.post:Per c)+↑(hat c he).val)- ↑(Cells.Kind.shift .link))*(step W.axis i)= _ -- equiv scalar
    simp only [Pi.smul_apply]; by_cases h:i=W.axis
    · subst i; simp only [step_apply,if_true,mul_one,zsmul_eq_mul,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_one,Cells.Kind.shift,Nat.cast_one]; linear_combination nes W he
    simp [step_apply,h]
lemma lifting (i:Cover): leap (origin c) (W.walks i)=(FaceR W he).reflect (leap (origin c) i):=by
    simp only [Cells.Cut.reflect,FaceR, Cells.Cut.flip]; unfold Wall.walks leap affine; simp only [map_add,Signed.act_add,wrap_signed]; change _= (wrap c) (W.mirror.act i) + W.mirror.act (origin c) + (FaceR W he).slide; rw [silent he W,windW W he]; abel -- fix
omit he W
noncomputable def val0 (n:Side)(x:ℤ): Per n:= x
lemma vTime (x:ℤ)(hx:0≤x)(hu:x<c.val): val0 c x= (↑x.toNat:Per c) ∧ (val0 c x).val=x.toNat:=by
    have h: val0 c x=(↑x.toNat:Per c):=by unfold val0; nth_rw 1 [← Int.toNat_of_nonneg hx]; rw [Int.cast_natCast]
    refine ⟨h,?_⟩; rw [h,ZMod.val_natCast_of_lt (by omega)]
noncomputable def chrom (W:Wall):ℂ:= if W.post <0 then -1 else 1
-- seam sign here at local shop is global (both hands).
variable (s:ℕ→Side)(h:Tendsto (fun i=>(s i).val) atTop atTop)(hv:∀ i,Even (s i).val)
include W h hv
lemma stumpy (x: Cover): ∀ᶠ k in atTop, (Tide.simple (FaceR W (hv k))).stamp (leap (origin (s k)) x)=chrom W:=by
    let X:= x W.axis; let j:= W.post
    filter_upwards [h.eventually (eventually_ge_atTop (8*(X.natAbs+j.natAbs+2)))] with k hk; let c:=s k; let R:=FaceR W (hv k); let a:=hat _ (hv k); change _≤c.val at hk
    let t:ℤ:=X+↑a.val; have hh:c.val=2*a.val:= R.even; have he:0 ≤ t:=by unfold t; omega
    have hp:(leap (origin c) x W.axis).val=t.toNat:=by
         rw [show leap _ _ _=val0 c t from ?_]; exact (vTime t he (by unfold t; omega)).2
         change (X:Per c) + (↑a.val:Per c)= ((X+(a.val:ℤ):ℤ):Per c); rw [Int.cast_add, Int.cast_natCast]
    have hQ: Slice.Link.top R+1=(j:Per c):=by
         change ((j:Per c)+(↑a.val:Per c))+_ - _+_= _; have hz: 2*(↑a.val:Per c)=0:=R.zeroLength; rw [show R.half=a from rfl]; linear_combination hz
    unfold chrom; rw [strong]; change (if (leap _ _ W.axis).val < (Slice.Link.top R+1).val then _ else _)=(if j<0 then _ else _); rw [hp,hQ]; split_ifs with hp' h' h'
    · rfl
    · have h1: ((j:Per c)).val=j.toNat:= (vTime j (by omega) (by omega)).2; omega
    · exfalso; let u:ℤ:= j+(c.val:ℕ); have h₁: (j:Per c)=(u:Per c):=by unfold u Per; rw [Int.cast_add,Int.cast_natCast,ZMod.natCast_self,add_zero]
      have h₂: (u:Per c).val=u.toNat:=(vTime _ (by unfold u; omega) (by unfold u; omega)).2; rw [h₁,h₂] at hp'; unfold t u at hp'; omega -- hm.t p etc
    rfl
-- heights
noncomputable def stern (W:Wall)(D:Lot)(q:ℕ):Prop:=∀ x:Court D, W.post+(q:ℤ) ≤ x.val W.axis
lemma outH (q:ℕ)(hp: stern W D q): ∀ᶠ k in atTop, Set.MapsTo (leap (origin (s k))) D (eaves (FaceR W (hv k)) q):=by
    have he (x:Court D):∀ᶠ k in atTop,leap (origin _) x.val∈ eaves (FaceR W (hv k)) q:=by
        let t:=x.val W.axis-W.post; have hl:= hp x; change W.post+(q:ℤ) ≤ x.val W.axis at hl; have ht:t≥0:=by unfold t; omega
        filter_upwards [h.eventually (eventually_gt_atTop (2*(t.toNat+q)))] with k hk; change 2*(t.toNat+q)< (s k).val at hk; let A:= FaceR W (hv k); let n:=s k; have hh:n.val=2*A.half.val:= A.even; have hz: A.distance (leap (origin n) x.val)=t.toNat:=by
            unfold Cells.Cut.distance; change ((x.val W.axis:Per n)+(origin n) W.axis- (W.post+(origin n) W.axis)).val=_; rw [add_sub_add_right_eq_sub, ← Int.cast_sub]; change ((t:Per n)).val=t.toNat; have hh:t<(↑n.val:ℤ):=by have hk : t.toNat < n.val:= lt_of_le_of_lt (show t.toNat≤2*(t.toNat+q) from (by omega)) hk; omega
            exact (vTime t ht hh).2
        change q≤ A.distance _ ∧ A.distance _+ q< _; rw [hz]; have hkk : (q:ℤ) ≤ t:=by unfold t; omega
        change _ ∧ _< A.half.val; have hP: t.toNat+q<A.half.val:=by have hh := hk.trans_eq hh; omega
        exact ⟨by omega,hP⟩
    filter_upwards [eventually_all.mpr he] with k hk; exact fun i hi=> hk ⟨i,hi⟩
end YM.QCD.Agate
