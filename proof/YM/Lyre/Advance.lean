import YM.Lyre.Absolute
import YM.Lyre.Pillar
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open Transfer QCD.Cove
open scoped Topology BigOperators Classical ComplexOrder Matrix Matrix.Norms.Frobenius
open Patria Plum TorusPCAC.Geometry QCD.Revolve
variable {c:Side}(b w:Cover)(X:Stud c 6)(s t:Signed)(P Q:Spike)
noncomputable def seatS (s:Signed)(b:Cover)(x:Site c):ℂ:= prism s x * heat b (affine s 0 x)
local notation "Tn" => TorusPCAC.thermal c
lemma stamp (v:Cover): Tn (s.act v+b)= seatS (c:=c) s b (wrap c v) * Tn v:=by
    rw [heated,←wrap_signed]
    unfold seatS affine; rw[add_zero];
    have he:Tn (s.act v) = prism s (wrap c v)*Tn v:=by
         have hv:= Lining.Ferry.sheet_launch c v s; rw [mul_comm]; exact hv.symm -- inspect
    rw [he]; ring
noncomputable def scarf (s:Signed) (b: Cover) (P:Spike): Sheet c:= hues (wrap c b) s (seatS s b) P
lemma rideActs : scarf (c:=c) s b P * scarf t w Q = scarf (t*s) (t.act b+w) (Q*P):=by
    unfold scarf hues; rw [ride_mul];
    have H:(shiftE s (wrap c b)).trans (shiftE t (wrap c w))= shiftE (t*s) (wrap c (t.act b+w)):= Equiv.ext fun i=>by change affine t _ (affine s _ i)= affine _ _ _; unfold affine; rw[Signed.act_add,map_add,Signed.act_mul, ← wrap_signed]; exact add_assoc .. 
    rw [H]; congr 1; funext x; rw [Matrix.smul_mul, Matrix.mul_smul,star_mul,wave_mul]; rw [smul_smul]; have ht: seatS (t*s) (t.act b+w) x= seatS t w (affine s (wrap c b) x) * seatS s b x:=by
         let v:= lift x; let p:=s.act v+b; have hx: wrap c v=x:=wrap_lift _; have he:= stamp (c:=c) b s v; have hq:= stamp (c:=c) (t.act b+w) (t*s) v
         have hu:= stamp (c:=c) w t p; unfold p at hu; rw [hx] at he hq; rw [map_add,← wrap_signed,hx,he,←mul_assoc,show t.act (s.act v+b)+w=(t*s).act v+(t.act b+w) from (by rw [Signed.act_add,add_assoc,Signed.act_mul])] at hu; have hT: Tn v*Tn v=1:=thermal_norm _; exact mul_right_cancel₀ (show Tn v≠0 from fun h=>by simp [h] at hT) (hq.symm.trans hu)
    rw [ht,mul_comm (seatS s b x)]; rfl
lemma seat1 : seatS (c:=c) 1 b= heat b:=by funext x; unfold seatS; rw[affine,Signed.act_one,add_zero,show prism 1 x=1 from (?_),one_mul]; unfold prism; rw [Signed.act_one]; exact naked x
noncomputable def march_full (b:Cover): Sheet c:=hues (wrap c b) 1 (heat b) 1
local notation "M" b:arg=> Lat.copies 6 (march_full (c:=c) b)
lemma marches (V): march b X V=Kit.disguise (M b) (X (pull 1 (wrap c b) V)):=rfl
lemma marched : march w (march b X)= march (b+w) X :=by
    funext V; rw[marches,marches,marches, pull_pull,one_mul]; simp only [affine,Signed.act_one]; rw [map_add]; unfold Kit.disguise; rw[adapt_together, ← Matrix.transpose_mul,← star_mul,← copies_mul];
    have ht(y :Cover):march_full (c:=c) y=scarf 1 y 1:=by rw [scarf,seat1]; rfl
    rw [ht b,ht w,rideActs,Signed.act_one,one_mul,one_mul,←ht]
lemma march0 : march 0 X = X:=by
    funext V; rw[marches, map_zero, pull_id]; have hp : march_full (c:=c) 0=1:=by
        unfold march_full hues;
        rw [map_zero]; rw [show shiftE 1 (0:Site c)=Equiv.refl _ from Equiv.ext fun i=>by change affine 1 _ i=i; simp [affine]]
        rw [show (fun x:Site c=> heat 0 x • wave (star (1:Spike)))=fun _=> 1 from (?_),ridden]; funext i; simp only [heat,add_zero,naked,one_smul,wave_one,star_one]
    rw [hp,copies_one]; unfold Kit.disguise; simp
lemma movesM(x y:Stud c 6): march b (x*y)=march b x*march b y:=funext fun U=>map_mul _ _ _
lemma marchP (x:Stud c 6)(hx:Stays x) : Stays (march b x):=by let V:=Kit.disguise (M b); exact (hx.travel ((continuous_pull _ _).measurable)).flows (V.toLinearMap.continuous_of_finiteDimensional)
variable (C:Cells.Cut c)(hc:C.kind=.link)
local notation "A"=>C.flip
local notation "z"=> C.flip.act w
include hc
lemma commend(T: Grid c): tallH C (march w X) T=march z (tallH C X) T:=by
     obtain ⟨b,he⟩:= shone C hc
     let D:= Tide.lens C; let V:_:= copies 6 D
     have hz: D=scarf A b (gamma C.pos):=by unfold D Tide.lens scarf; rw[he.aligned,show seatS _ b=inc C from he.same]
     have hp(y:Cover): march_full (c:=c) y=scarf 1 y 1:=by rw[scarf,seat1]; rfl
     have ht: V*M z=M w * V:=by
         unfold V; rw [← copies_mul,← copies_mul,hp,hp, hz, rideActs,rideActs,one_mul,mul_one,one_mul,mul_one]; rw [Signed.act_one,add_comm]
     have hZ: pull 1 (wrap c w) (C.pullC su T)=C.pullC su (pull 1 (wrap c z) T):=by unfold Cells.Cut.pullC; rw [pull_pull,pull_pull,one_mul,mul_one]; unfold affine; rw [Signed.act_one, ←wrap_signed,add_comm _ C.slide]
     have hr:star V=V:=by unfold V; rw[← copies_star]; unfold D; rw[lens_star]
     rw [huesT,marches,marches,hZ,huesT]; exact tilt_through (M w) (M z) V V hr hr ht _
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.commend
#print axioms YM.Massive.Lyre.marched
