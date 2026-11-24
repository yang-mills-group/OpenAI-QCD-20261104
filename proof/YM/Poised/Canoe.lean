import YM.Poised.Horns
import YM.Poised.Stir
/-!
# AP from actual sheet/taper use
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource MultiNext.SignedSource.Lyre Place Lining Lining.Ferry QCD.Brick
lemma ap_one (n:Side)(x:Cover): ‖ap n x‖=1:=by unfold ap; simp [norm_prod]
lemma ap_sq (n:Side)(x:Cover): ap n x*ap n x=1:=by unfold ap; rw [←prod_mul_distrib]; simp_rw [← mul_zpow]; simp
private lemma seam_at (n:Side)(x:Site n)(i:Axis) : x i + 1 = 0 ↔ (x i).val+1=n.val:=by
   have hz:= ZMod.val_lt (x i)
   by_cases hv: n.val=1
   · have he:(x i).val=0:=by omega
     have h: (1: Per n)=0:=by have hh:(↑n.val: Per n)=0:= ZMod.natCast_self n.val; exact (by simpa only [Nat.cast_one] using congr_arg (fun k:ℕ=>(k:Per n)) hv.symm : (1:Per n)= ↑n.val)|>.trans hh
     rw [← ZMod.natCast_zmod_val (x i)] -- goal both sides
     simp [he,hv,h]
   have ht : 1<n.val:=by have hh:= n.property; omega
   have hx : (x i+1).val=((x i).val+1)%n.val :=by rw [ZMod.val_add, ZMod.val_one'' hv]
   have hX : n.val ∣ (x i).val+1 ↔ (x i).val+1=n.val:=by apply Iff.intro; intro h; exact le_antisymm (by omega) (Nat.le_of_dvd (by omega) h); intro h; rw [h]
   rw [← ZMod.val_eq_zero,hx,← Nat.dvd_iff_mod_eq_zero,hX]
lemma seam_tick (x:Cover)(i:Axis): ap c (x+Lattice.step i)=ap c x* seam 0 (wrap c x) i:=by
   let X := wrap c x
   let u:Cover:=sheet X; let v:Cover:= fun i=> x i/(c.val:ℤ); have he : u+c.val • v=x:=by funext j; unfold u; rw [Pi.add_apply,sheet_ref c x,Pi.smul_apply,nsmul_eq_mul]; exact Int.emod_add_mul_ediv (x j) c.val
   have hp : seam 0 X i=ap c (u+Lattice.step i):=by
      rw [ap,Finset.prod_eq_single i]; swap
      · intro j _ hj; rw [Pi.add_apply,step_apply,if_neg hj, add_zero,Int.ediv_eq_zero_of_lt (by change 0 ≤ (↑(X j).val:ℤ); positivity) (by change ((X j).val:ℤ)< c.val; exact_mod_cast ZMod.val_lt (X j)),zpow_zero]
      swap; · simp
      have hh:(0:ℤ) ≤ ↑(X i).val:=by positivity
      have hk: ((X i).val:ℤ)<c.val:=by exact_mod_cast ZMod.val_lt (X i)
      have hu: (u+ step i: Cover) i= ↑(X i).val+1:=by simp only [Pi.add_apply,step_apply,if_pos rfl]; rfl
      rw [hu,seam]; split
      next H=> have hs:((X i).val:ℤ)+1=c.val:=by exact_mod_cast (seam_at c X i).mp H
               rw [hs, Int.ediv_self (by omega)]; simp
      next H=> have hs:((X i).val:ℤ)+1<c.val:=by have:=mt (seam_at c X i).mpr H; omega
               rw [Int.ediv_eq_zero_of_lt (by linarith) hs,zpow_zero]
   change _=ap c x*seam 0 X i; rw [hp]; nth_rw 1 [← he, add_right_comm, ap_pace]; nth_rw 1 [← he]; rw [ap_pace,show ap c u=1 from sheet_pace ..,one_mul,mul_comm]
open QCD.Loom QCD.Flume QCD.Kit
abbrev R0:=VectorD (Site l) (Faces (Site c))
variable (b:Cover)(Z:Kit.Rail l c)
def rowsA (X:VectorD (Site l) B)(p:Cover) : Flet B:= (ap l (p+b)) • asks X (wrap l (p+b))
def flareV (Z:Kit.Rail l c):VectorD (Site l) (Faces (Site c)):= powerF (N:=6) Z
lemma APcome (i:Axis)(p:Cover) : rowsA b (flareV (Flume.after Z i)) p = Newt.jump (rowsA b (flareV Z)) i p:=by
    unfold Newt.jump rowsA; rw [show p+step i+b=p+b+step i by abel, seam_tick (p+b) i,map_add (wrap l) (p+b),wrap_step]
    funext j k; change ap l _ * powerF _ (stretch _ _) _=_; let u:= wrap l (p+b); have he x: stretch (Site l) (x,j)=pitchQ x (N:=6) j:=by cases j<;>rfl
    change ap _ _* powerF _ (stretch (Site l) (u,j)) k= (ap l _* seam 0 u i)*powerF Z (stretch _ (u+step i,j)) k - ap l _ * powerF Z (stretch _ (u,j)) k; rw [he,he,freezeW]; ring
lemma hike (x:List Axis): Newt.iterate (rowsA b (flareV Z)) x= rowsA b (flareV (oldDiff Z x.reverse)):=by
   have he(p:Cover→ Flet (Faces (Site c)))(l m:List Axis): Newt.iterate p (l++m)= Newt.iterate (Newt.iterate p l) m:=by
      induction l generalizing p with
      | nil=>rfl
      | cons a l ih=> rw [List.cons_append]; exact ih _
   induction x using List.reverseRecOn with
   | nil=>rfl
   | append_singleton x i ih=>rw [he,ih,List.reverse_append]; exact (funext (APcome b (oldDiff Z x.reverse) i)).symm
end Pipes
end YM.Massive.Poised
