import YM.Profiles.Quills
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
variable (Q:I→Bool)(l:List I)
local notation "AR"=> Patio (A⊕Spine I)
-- use Crest at list
omit [Fintype I] in
lemma decal : l.toFinset=crest l.get:=by ext i; simp only [List.mem_toFinset,exists_fix]; exact List.mem_iff_get
lemma posture : armature Q l.get=(l.map fun i=>mono (burst Q ({i}:Finset I))).reverse.prod:=by
     unfold armature; congr 2; let g i:=mono (Ribbon.burst Q ({i}:Finset I)); exact Eq.trans (show List.ofFn (g ∘ l.get)=(List.ofFn l.get).map g from List.map_ofFn.symm) (congr_arg (List.map g) (List.ofFn_get l))
lemma mixes (k:List I) : armature Q (l++k).get=armature Q k.get*armature Q l.get:=by simp_rw [posture,List.map_append,List.reverse_append,List.prod_append]
variable (hl:l.Nodup)
include hl
lemma fare : Hom (shade (burst Q l.toFinset)) (armature Q l.get):=by
   rw [decal]; have ht:= Ribbon.healthy (burst Q (crest l.get)); rcases arc Q l.get (List.nodup_iff_injective_get.mp hl) with h|h; rw[h]; exact ht
   rw[h]; simpa using ht.smul (-1)
omit hl
lemma power (x:Patio (A ⊕ Spine I)): Hom (shade (burst Q l.toFinset)) ((numbered Q A l.get) x):=by
   rw[decal]; exact (serene _ (x.property)).smul _
lemma mates {q:Bool}{x:Alg A}(f:A→B)(h:Hom q x): Hom q (embed f x):=by cases q; exact (embed_grade ..).trans (congr_arg _ h); exact (embed_grade ..).trans ((congr_arg (embed f) (show grade x= -x from h)).trans (map_neg ..))
lemma joint_swap (x y a b:Alg A) {u v:Bool}(ha:Hom u a)(hy:Hom v y)(hb:Hom v b): x*a*(y*b)=x*y*(b*a):=by
     have h:=Hom.swap hy ha; have w:=Hom.swap hb ha
     calc
       _ = x*(a*y)*b := by simp only [mul_assoc]
       _ = _ := by
               rw[h]; split
               · rename_i h'; rw [if_pos h'] at w; have hw:b*a= -(a*b):=by rw[w,neg_neg]
                 rw [hw,mul_neg,mul_neg,neg_mul]; simp only[mul_assoc]
               rename_i h'; rw [if_neg h'] at w; rw [←w]; simp only[mul_assoc]
set_option maxHeartbeats 400000 in
lemma penalty (k:List I) (x y:AR)(hx:Polite Q l.toFinset x)(hy:Polite Q k.toFinset y)(hv:(l++k).Nodup) : numbered Q A (l++k).get (x*y)=numbered Q A l.get x*numbered Q A k.get y:=by
     have hk:k.Nodup:=(List.pairwise_append.mp hv).2.1
     have hl:l.Nodup:=(List.pairwise_append.mp hv).1
     rw[decal] at hx hy; let P' :=armature Q k.get; let Y':=numbered Q A k.get y; refine Quills.cuts A Q _ (List.nodup_iff_injective_get.mp hv) _ _ ?_
     rw [show (x*y).val=x.val*y.val from rfl,charge A Q l.get x hx (List.nodup_iff_injective_get.mp hl),charge A Q k.get y hy (List.nodup_iff_injective_get.mp hk),map_mul,mixes,map_mul]; exact joint_swap _ _ _ _ (mates _ (fare Q l hl)) (mates _ (power Q k y)) (mates _ (fare Q k hk))
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.penalty
