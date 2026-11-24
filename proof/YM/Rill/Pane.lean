import YM.Tarn.Switch
/-! Honest cut signs.Basal through seam. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry
variable {n:Side}(h:Even n.val)(a:Axis)
noncomputable def panH (h:Even n.val) (a:Axis):Cells.Cut n where
   half:= ⟨n.val/2,(by obtain ⟨p,hp⟩:=h; change 0 < n.val / 2; have he:0<n.val:= n.pos; omega)⟩
   even:= by obtain ⟨p,hp⟩:=h; simp only [PNat.mk_coe]; omega
   kind:= .link
   baseLine:=0
   pos:=a
section
local notation "Ω"=> panH h a
lemma crestPan : wrap n (-step a : Cover)=(Ω).slide:=by unfold Cells.Cut.slide; simp [panH,Cells.Kind.shift, wrap_step]
lemma robesW: Soot Ω (-step a) 0= -1:=by
     let p:=(-(step a:Cover)); rw [Soot]; change Patria.prism (Signed.mirror a) (0:Site n) * heat p _= _
     have he : Patria.prism (Signed.mirror a) (0:Site n)=1:=by unfold Patria.prism; rw [show Cylinder.sheet (0:Site n)=(0:Cover) from (by ext; simp [Cylinder.sheet]),Signed.act_zero]; simp [Cylinder.ap]
     rw [he,one_mul]; simp only [Lattice.affine, Signed.act_zero,zero_add]; unfold heat; rw [show TorusPCAC.Stencil.nonnegative (0: Site n)=(0:Cover) from (by ext; simp [TorusPCAC.Stencil.nonnegative]),zero_add]; have hp:p+step a=(0:Cover):= neg_add_cancel _; have hh:= thermal_step (n:=n) p a; rw[hp,show seam (0:Site n) (wrap n p) a= -1 from ?_, show TorusPCAC.thermal n (0:Cover)=1 from (by simp [TorusPCAC.thermal])] at hh; linear_combination hh -- check
     simp [p,map_neg,wrap_step,seam]
lemma earnedSign : CompleteP Ω (-step a):=by
    let v:= Ω; refine ⟨crestPan h a,rfl,?_⟩; rcases Romance.sign_glare (sootL _ _ (crestPan h a)) (glances v rfl) with he|he; exact he
    have hx: inc v 0 = -1:=by
         unfold inc; rw[strong,strong,show Slice.Link.top v + 1= _ from (show Slice.Link.top v+1=(v.half.val:Per n) from by unfold Slice.Link.top; change 0+_-_+_= _; ring )]; have hy:n.val=2*v.half.val:=v.even; have hz:0<v.half.val:=v.half.pos
         rw [show (v.reflect 0) v.pos= -(1:Per n) from (by rw [Cells.Cut.reflect_here]; simp [v,panH,Kind.shift]),show (0:Site n) v.pos=0 from rfl,ZMod.val_zero,ZMod.val_natCast_of_lt (by omega), if_pos hz]; rw [if_neg,mul_one]; have hL : (-1:Per n).val=n.val-1:= by
               have hk(m:ℕ)(he:m>0):(-1:ZMod m).val=m-1:=by cases m; omega; simp [ZMod.val_neg_one]
               exact hk _ n.pos
         omega
    have hp:= congr_fun he 0; rw [Pi.neg_apply,hx,show Soot v _ (0:Site n)= _ from robesW h a] at hp; norm_num at hp
end
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.earnedSign
