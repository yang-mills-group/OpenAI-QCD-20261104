import YM.QCD.Agate.Stool
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f G K L: Side}{F i j:ℕ}{β t:ℝ} {D Y:Lot}
open Tide Flume YM.Next.Free
noncomputable def stoke (p:Site c)(D:Lot): Prop:=∀ x:Court D,∀ a:Axis,seam (0:Site c) (leap p x.val) a=1
lemma leapt (h:Fits c D)(p:Site c)(x y:Court D): leap p x.val=leap p y.val ↔ x=y:= (pins h p).injective.eq_iff
lemma rule (x:Site c)(z u:Site c)(X:Sheet c)(g:Bundle)(H:Sheet c)(a b:Fiber)(hh:∀ y i,(X (x,a) (y,i))= if z=y then g a i else 0): (X*H) (x,a) (u,b)=∑ i:Fiber, g a i* H (z,i) (u,b):=by
    rw [Matrix.mul_apply,Fintype.sum_prod_type]; simp [hh,ite_mul]
lemma hike (p:Site c)(w:Fits c D)(s:Walk)(x y:Cover)(h:∀ j∈ visits x s,j∈D)(a b:Fiber)(hy:y∈D):
     let f(U:Grid c):=routeM 0 U s (leap p x,a) (leap p y,b); ∀ Q:Site G,∀ U:Grid c,∀ V:Grid G,Fits G D→ stoke p D → stoke Q D→crest (D:=D) p U=crest Q V → f U=routeM 0 V s (leap Q x,a) (leap Q y,b):=by
   intro f Q U V hv ht hu hh; change routeM 0 U s _ _= _; clear f
   have hk(u v:Cover)(hw:u∈D)(h1:v∈D):leap p u=leap p v ↔ leap Q u=leap Q v:=by rw [show (leap p u=leap p v) ↔ (⟨u,hw⟩:Court D)=⟨v,h1⟩ from leapt w p ⟨u,hw⟩ ⟨v,h1⟩]; exact (leapt hv Q ⟨u,hw⟩ ⟨v,h1⟩).symm
   have hf (i:Axis)(u:Cover)(hp:u∈D)(H:u+step i∈ D): Lat.thread 0 U i (leap p u)= Lat.thread 0 V i (leap Q u):=by
       unfold Lat.thread; rw [show seam (0:Site c) (leap p u) i=1 from ht ⟨u,hp⟩ i]
       rw [show seam 0 (leap Q u) i=_ from hu ⟨u,hp⟩ i]; exact congr_arg (fun g=> (1:ℂ) • colour g) (congr_fun hh (⟨(⟨u,hp⟩,i),H⟩: Pipe D))
   induction s generalizing x a with
   | nil=> have H:= hk x y (h x (by simp [visits])) hy; simp [routeM,Matrix.one_apply,H]
   | cons d s ih=>
      let z:= x+d.vec; have H(j)(hj:j∈visits z s):j∈D:=h _ (List.mem_cons_of_mem _ hj)
      have h1:= h x (List.mem_cons_self); have h2:z∈ D:= H _ (by cases s <;> simp [visits]); change (Kit.leg 0 U d *routeM 0 U s) _ _= (Kit.leg 0 V d* routeM 0 V s) _ _
      rcases d with ⟨i,_|_⟩
      · let g(C:Side)(T:Site C)(W:Grid C):=touch (Lat.thread (0:Site C) W i (leap T x)); have hg(C:Side)(T:Site C)(W:Grid C)(u:Site C)(v:Fiber): Kit.leg (0:Site C) W ⟨i,false⟩ (leap T x,a) (u,v)= if leap T z=u then g C T W a v else 0:=by
            unfold Kit.leg; rw [if_neg (by simp),Lat.shift,rr]; simp only; rw [show z=x+step i from rfl,leapS]; rfl
        rw [rule _ (leap p z) _ _ (g c p U) _ _ _ (hg c p U),rule _ (leap Q z) _ _ (g G Q V) _ _ _ (hg G Q V), show g c p U=g G Q V from congr_arg touch (hf i x h1 h2)]
        exact sum_congr rfl fun j _=> congr_arg (g G Q V a j * ·) (ih z H j)
      have hz': z=x-step i:=by rw [sub_eq_add_neg]; rfl
      let g(C:Side)(T:Site C)(W:Grid C):= touch (star (Lat.thread (0:Site C) W i (leap T z)))
      have he:x=z+step i:=by rw [hz',sub_add_cancel]
      have hg(C:Side)(T:Site C)(W:Grid C)(u:Site C)(v:Fiber): Kit.leg 0 W ⟨i,true⟩ (leap T x,a) (u,v)= if leap T z=u then g C T W a v else 0:=by
           have hlt:leap T x -step i=leap T z:=by nth_rw 1 [he]; rw [leapS,add_sub_cancel_right]
           unfold Kit.leg; rw [if_pos rfl,Lat.opp,rr]; simp only [Lat.back,hlt]; rfl -- name
      rw [rule _ (leap p z) _ _ (g c p U) _ _ _ (hg c p U),rule _ (leap Q z) _ _ (g G Q V) _ _ _ (hg G Q V), show g c p U=g G Q V from congr_arg (fun a:Mat=>touch (star a)) (hf i z h2 ((by rw [← he]; exact h1)))]
      exact sum_congr rfl fun j _=> congr_arg (g G Q V a j * ·) (ih z H j)
end YM.QCD.Agate
