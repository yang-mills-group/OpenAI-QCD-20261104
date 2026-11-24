import YM.DawnS.Groom
import YM.Avian.Icarus
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS Arise.Range
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical
variable {d e k:ℕ}(a b i l j:Axis)(x:Points 2)(hx:x∈conf 2)
-- cross-horizon
lemma step_eq (v:Multi d)(w:Multi e)(h: UV.power v = UV.power w):steps v= steps w:=by simp [steps,h]
lemma amen {V W:Type} [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W](X:V →L[ℝ] W)(x:V)(g:W→ℂ)(A:W)(ha:X x=A)(p:V)(Z:W)(hp:X p=Z)(h:DifferentiableAt ℝ g A)(c:ℂ): fderiv ℝ (fun t=> c*(g ∘ X) t) x p=c*(fderiv ℝ g A Z):=by
     subst A Z; rw [fderiv_const_mul (h.comp x X.differentiableAt), fderiv_comp x h X.differentiableAt]; exact congr_arg (fun M : V →L[ℝ] W => c*(fderiv ℝ g (X x) (M p))) (by exact X.hasFDerivAt.fderiv : fderiv ℝ X x=X)
local notation "P" => Points.direction (0:Fin 2) j
variable (p:Multi d)(p':Multi e)(q:SpinMode k) (s:Pinor)(u:Hue)(c:Flavor 6)(h: UV.power p'= update (UV.power p) j (UV.power p j+1))
include hx h
open Massive.Tawny Massive.Tawny.Cast Massive.Tawny.Cast.Drill
lemma sizes : (steps p').Perm (j :: steps p):=by
      apply List.perm_iff_count.mpr; intro b; rw[List.count_cons,Arise.spine_code,Arise.spine_code,h]; by_cases he:b=j <;> simp[he] <;> first|rfl|tauto
lemma over_leg : D P (fun x:Points 2=> leg ((p,s,u),c) q (x 0) (x 1)) x = leg ((p',s,u),c) q (x 0) (x 1):=by
     simp only[leg]; split; swap; · simp [D]
     let L:= steps p ++ steps q.1.1; let A:= x 0-x 1; let f:=dirac s q.1.2.1; have hp:A≠0:=sub_ne_zero.mpr ((show Injective x.ofLp from hx).ne (by decide : (0:Fin 2)≠1)); let X(i:Fin 2):Points 2 →L[ℝ] E4:= PiLp.proj 2 _ i; let V:= X 0-X 1; have hv: V P=basis j:=by simp [V,X,Points.direction]
     rw [show derivatives (steps p'++steps q.1.1) f A=D (basis j) (deriveL L f) A from commute_a Maxwell.open_away f (is_hot _ _) _ _ ((sizes j x hx p p' h).append_right _) A hp]; let g:=deriveL L f; have ht:DifferentiableAt ℝ g A:=(balla L f _ Maxwell.open_away (is_hot _ _) _ hp).differentiableAt (by simp)
     let z:ℂ:=(-1)^ (steps q.1.1).length
     change fderiv ℝ (fun t=> z*(g ∘ V) t) x P=z*(fderiv ℝ g A (basis j))
     exact amen V x g A rfl _ _ hv ht z
lemma after_leg : D P (fun x:Points 2=>leg q ((p,s,u),c) (x 1) (x 0)) x= leg q ((p',s,u),c) (x 1) (x 0):=by
     simp only [leg]; split; swap; · simp [D];
     let L:= steps q.1.1 ++ steps p; let A:=x 1-x 0; let f:=dirac q.1.2.1 s; have hp:A≠0:=sub_ne_zero.mpr ((show Injective x.ofLp from hx).ne (by decide : (1:Fin 2)≠0)); let X(i:Fin 2):Points 2 →L[ℝ]E4:=PiLp.proj 2 _ i; let V:=X 1-X 0; have hv:V P=-basis j:=by simp [V,X,Points.direction]
     have he:= sizes j x hx p p' h
     rw [show derivatives (steps q.1.1++steps p') f A=D (basis j) (deriveL L f) A from commute_a Maxwell.open_away _ (is_hot _ _) _ _ ((List.perm_append_comm ..).trans ((he.append_right _).trans (List.Perm.cons _ (List.perm_append_comm ..)))) _ hp, show (steps p').length=(steps p).length+1 from he.length_eq, pow_succ',neg_one_mul]; let g:=deriveL L f; have ht:DifferentiableAt ℝ g A:=(balla L f _ Maxwell.open_away (is_hot _ _) _ hp).differentiableAt (by simp)
     let z:ℂ:= (-1)^ (steps p).length
     change fderiv ℝ (fun t=> z*(g ∘ V) t) x P= -z*(fderiv ℝ g A (basis j))
     exact (amen V x g A rfl _ _ hv ht z).trans (by rw [map_neg, neg_mul, mul_neg])
end YM.Hail
#print axioms YM.Hail.after_leg
