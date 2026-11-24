import YM.QCD.Tide.Ingot
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Revolve
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C] {n c f : Side} {F : ℕ} {β:ℝ} (R:Cells.Cut c) (r:Ratio c f)
local notation "v"=> R.pos
local notation "L"=> r.count.val
local notation "d"=> L/2
local notation "T"=> gateH R r
-- stamp of mount zero, up to global - ; especially if crossing at seam. independent of masses
noncomputable def simple (R:Cells.Cut c): Tape c:=⟨R.pos,0,Slice.Link.top R+1⟩
lemma strong(x:Site c): (simple R).stamp x=(if (x R.pos).val < (Slice.Link.top R+1).val then -1 else 1):=by simp [simple,Tape.stamp]
lemma sets (x:Site c)(i:Axis): (r.embed x i).val=(x i).val*L:=by rw [coords0, ZMod.val_natCast_of_lt]; rw [r.exact_size]; exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt _) r.count.property
lemma setsF : ∃ w:ℂ,w*w=1∧∀ x: Site c,(simple T).stamp (r.embed x)= w*(simple R).stamp x:=by
    let J:= (Slice.Link.top R+1).val; let A:=Slice.Link.top T+1; have hv:A= (↑(J*L):Per f)-(↑(d):Per f):=by rw [show A=_ from stopH R r,per_val]
    have he: J < c.val:= ZMod.val_lt _; have hl:0<L:=r.count.property; have hh:d<L:=by omega
    have hJ:J * L<f.val:=r.exact_size.symm ▸ Nat.mul_lt_mul_of_pos_right he hl
    by_cases h:0<J
    · have hz : d ≤ J*L:= hh.le.trans (le_mul_of_one_le_left hl.le h)
      have ht:A.val= J*L-d:=by
        -- precedence parentheses!! d parser local notation likely okay? A
        rw [hv, ← Nat.cast_sub hz,ZMod.val_natCast_of_lt (by omega)]
      refine ⟨1,mul_one _,fun x=>?_⟩; rw [strong,strong,one_mul,show Slice.Link.top T+1=A from rfl, ht,sets]; let D:=(x R.pos).val
      change (if D*L<J*L-d then _ else _)=(if D<J then _ else _)
      by_cases H : D<J
      · rw [if_pos H, if_pos]; have hu : D*L+L≤J*L:=by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ H
        omega
      rw [if_neg H, if_neg]; have hr: J*L ≤ D*L:=by have hh: J ≤ D:= le_of_not_gt H; gcongr
      omega
    have ht:J=0:=Nat.eq_zero_of_not_pos h; by_cases hL: 0<d
    · refine ⟨-1,by simp,fun x=>?_⟩; rw [strong,strong,show Slice.Link.top T+1=A from rfl]; let D:=(x R.pos).val; have hh' : D < c.val:= ZMod.val_lt _
      have hu : D*L+L≤ f.val:= by rw [← Nat.succ_mul,r.exact_size]; exact Nat.mul_le_mul_right _ hh'
      rw [sets]; change (if D*L < A.val then _ else _) = -1 * if D<J then _ else _
      rw [ht]; simp only [Nat.not_lt_zero,if_false,mul_one]; rw [if_pos]; have hr:d ≤ f.val:=by omega
      have hx:A=(↑(f.val-d):Per f):=by rw [hv,ht,Nat.cast_sub hr]; simp [Per]
      rw [hx,ZMod.val_natCast_of_lt (by omega)]; omega
    refine ⟨1,mul_one _,fun x=>?_⟩; rw [strong,strong,one_mul,show Slice.Link.top T+1=A from rfl,show A=0 from by rw [hv,ht,show d=0 from Nat.eq_zero_of_not_pos hL]; simp, ZMod.val_zero, ← (show J=(Slice.Link.top R+1).val from rfl),ht]; simp
noncomputable def inc (R:Cells.Cut c)(x:Site c):=(simple R).stamp x*(simple R).stamp (R.reflect x)
lemma income(h:R.kind=.link)(ho:Odd L)(x:Site c): inc T (r.embed x)=inc R x:=by
   obtain ⟨w,hx,he⟩:=setsF R r; unfold inc; rw [← switchy R r h ho,he,he]
   linear_combination ((simple R).stamp x*(simple R).stamp (R.reflect x))*hx
lemma glances(h:R.kind=.link): Glare R.flip 0 0 R.slide (inc R):=by
   let u:= simple R; let y:= u.swap (⟨0,0,0⟩: Lat.Cut c 0); let z:=y.t
   refine ⟨fun i=>?_,fun i x=>?_⟩
   · change u.stamp i * u.stamp (R.reflect i)=1 ∨ _; unfold inc; rcases (simple R).sign i with h|h <;> rcases (simple R).sign (R.reflect i) with H|H <;> unfold u <;> rw [h,H] <;> norm_num
   have hu(a:Step)(x : Site c):u.stamp x*glint 0 x a*u.stamp (x+a.vec)=glint z x a:=by
       rcases a with ⟨a,_|_⟩
       · exact u.stamps (0:Site c) rfl x a
       let A:=posDir a; let p:=x-step a; have hv:p+A.vec=x:=by simp [p,A]
       change u.stamp x*glint 0 x A.rev*u.stamp (x+A.rev.vec)=glint z x A.rev
       rw [show x+A.rev.vec=p from by simp [p,A,sub_eq_add_neg]]
       rw [show glint 0 x A.rev=_ from hv ▸ glint_rev p 0 A,show glint z x A.rev=_ from hv ▸ glint_rev p z A]
       have hh: u.stamp p*glint 0 p A*u.stamp (p+step a) =glint z p A:=u.stamps _ rfl p a; rw [show p+step a=x from hv] at hh; rw [← hh]; change u.stamp x*_*u.stamp p=_; ring
   have he : veil R.flip R.slide z=z:=by
       funext i; by_cases h': i= R.pos
       · subst i; unfold veil; simp only [Cells.Cut.flip, Signed.mirror] -- R.flip field notation? 
         have he:z R.pos= R.baseLine+ R.half.val:=by change update (0:Site c) _ _ _=_; rw [show u.a= R.pos from rfl, update_self]; unfold u simple; simp [Slice.Link.top]
         simp [he,Cells.Cut.slide,h,Cells.Kind.shift]; have hx:=R.zeroLength; linear_combination -hx -- fix
       unfold veil; simp [Cells.Cut.flip,Signed.mirror,h',Ne.symm h',Cells.Cut.slide]
   let a:=posDir i; let p:=R.reflect x; let q:=x+step i
   have hx: p+(a.rotate R.flip).vec=R.reflect q:=(affine_add _ _ _ _).symm -- ambiguous
   have hX : glint z p (a.rotate R.flip)=glint z x a:= (glow_at R.flip R.slide x z i).trans (by rw [he]; rfl)
   have hS: u.stamp p*_ *u.stamp (R.reflect q)=glint z p (a.rotate R.flip):= hx ▸ hu (a.rotate R.flip) p
   have hT: u.stamp x*glint (0:Site c) x a *u.stamp q= glint z x a:=hu a x
   -- goal
   change glint (0:Site c) x a*(u.stamp q*u.stamp (R.reflect q))=(u.stamp x*u.stamp p)*glint 0 p (a.rotate R.flip)
   have hg: u.stamp p*glint 0 p (a.rotate R.flip)*u.stamp (R.reflect q) =u.stamp x *glint 0 x a*u.stamp q:= hS.trans (hX.trans hT.symm)
   calc
        _ = u.stamp x*(u.stamp x*glint 0 x a*u.stamp q)*u.stamp (R.reflect q):=by rw [← mul_assoc, ← mul_assoc,← mul_assoc,u.squared,one_mul,mul_assoc]
        _ = _ :=by rw [← hg]; simp only [mul_assoc,Tape.squared,mul_one]
end YM.QCD.Tide
