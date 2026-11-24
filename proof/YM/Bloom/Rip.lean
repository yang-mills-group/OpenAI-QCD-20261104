import YM.Bank.Sour
import YM.Bank.Pic
import YM.Arise.Halo
/-! # column and stencil pricing: one rows, pins and pairs. bare unboosted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank
open Matrix Precision Exterior Avalon
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ComplexConjugate
open YM.Arise
variable {c f:Side}
local notation "θ"=> TypeFace 2
-- real columns true.Normal LOCAL
noncomputable def stalk (f:Side)(x:Cover)(p:θ): Parc→ₗ[ℝ] Matrix Unit (Co f θ) ℝ := Finsupp.linearCombination ℝ (fun y:Cover=>Matrix.of fun (_:Unit) (a:Co f θ)=> if (wrap f (x+y),p)=a then (1:ℝ) else 0)
variable (x y:Cover)(p:θ)(l:List Axis)
variable {H:Type}
lemma stroke (J: Matrix (Co f θ) H ℝ) (z:H): (stalk f x p (strike l y)*J) () z=(rocker f θ l*J) (wrap f (x+y),p) z:=by
    classical
    induction l generalizing y with
    | nil=> simp [strike, stalk, Matrix.mul_apply, rocker,Matrix.one_apply,ite_mul]
    | cons i l ih=> rw [strike,map_sub,Matrix.sub_mul,Matrix.sub_apply,ih,ih,rocker,Matrix.mul_assoc, lift_roller (rocker _ _ _ * J) i (wrap f (x+y)) p z,← add_assoc,map_add,wrap_step]
variable (A: Parc)
lemma taught(a:Co f θ) : stalk f x p A () a=sound (fun y=> if (wrap f (x+y),p)=a then 1 else 0) A:=by
   classical
   induction A using Finsupp.induction_linear with|zero=>simp|add i j h hp=>rw[map_add,map_add,Matrix.add_apply,h,hp]|single i a=>simp[stalk,sound]
lemma couple (J M: Matrix (Co f θ) (Co c θ) ℝ)(q:θ)(u v:Cover)(r:List Axis): (stalk f x p (strike l u)*J*(stalk f y q (strike r v)*M).transpose) () ()=((rocker f θ l*J)*(rocker f θ r*M).transpose) (wrap f (x+u),p) (wrap f (y+v),q):=by rw [Matrix.mul_apply,Matrix.mul_apply (k:=(wrap f (y+v),q))]; simp_rw [transpose_apply,stroke]

section Spi
open QCD QCD.Lat QCD.Flume QCD.Free
-- spin.real stencil at lift.
noncomputable def plume (f: Side)(x:Cover)(a:Fiber): Parc→ₗ[ℝ] Matrix Unit (Lat.Row f) ℂ:=Finsupp.linearCombination ℝ (fun y:Cover=>Matrix.of fun (_:Unit) (z:Lat.Row f)=>if (wrap f (x+y),a)=z then occ (0: Site f) (x+y) else 0)
lemma beep (r:Site f)(i:Axis):occ r (step i)= seam 0 r i:=by
    apply mul_right_cancel₀ (scarf_ne (0:Site f) (r+step i)); rw [scarf_a, ← wrap_step f, concord]
lemma windT (U:Matrix (Lat.Row f) (Lat.Row c) ℂ)(a:Fiber)(z): (plume f x a (strike l y)*U) () z =occ (0: Site f) (x+y)*oldDiff U l (wrap f (x+y),a) z:=by
    induction l generalizing y with
    | nil=> simp [strike,plume,Matrix.mul_apply,oldDiff,ite_mul]
    | cons i l ih=>rw [strike,map_sub,Matrix.sub_mul,Matrix.sub_apply,ih,ih,oldDiff,afterwards, ← add_assoc x y (step i), map_add,wrap_step,sign_rate,zero_add,beep]; ring
lemma reefs (a:Fiber)(z:Lat.Row f) : plume f x a A () z=sound (fun y=>if (wrap f (x+y),a)=z then occ (0:Site f) (x+y) else 0) A:=by
    induction A using Finsupp.induction_linear with|zero=>simp|add i j h hp=>rw [map_add,map_add,Matrix.add_apply,h,hp]|single i r=>simp[plume,sound]
lemma furls (a:Fiber)(z:Lat.Row f) : star (plume f x a A () z)=plume f x a A () z:=by
    induction A using Finsupp.induction_linear with
    | zero=>simp
    | add i j h hp=> rw [map_add,Matrix.add_apply,star_add,h,hp]
    | single i r=> simp only [reefs,sound,Finsupp.linearCombination_single, star_smul]; split_ifs; · exact congr_arg (r • ·) (realSeam ..).1
                   simp
lemma spoon (a:Fiber): (plume f x a A)ᴴ=(plume f x a A).transpose:=by ext i j; obtain ⟨⟩:=j; exact furls x A a i
lemma sells (U X:Matrix (Lat.Row f) (Lat.Row c) ℂ)(B:Sheet c)(a b:Fiber)(u v:Cover)(r:List Axis) : ((plume f x a (strike l u)*U)*B*(plume f y b (strike r v)*X)ᴴ) () ()= occ (0:Site f) (x+u)*occ (0:Site f) (y+v)*(oldDiff U l*B*(oldDiff X r)ᴴ) (wrap f (x+u),a) (wrap f (y+v),b):=by
      let P:=plume f x a (strike l u); let Q:=plume f y b (strike r v); rw [Matrix.mul_apply,Matrix.mul_apply (k:=(wrap f (y+v),b)),mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [Matrix.mul_apply,Matrix.mul_apply (i:=(wrap f (x+u),a)),conjTranspose_apply, conjTranspose_apply]; rw [windT,star_mul, show star (occ _ _)=occ _ _ from (realSeam ..).1]; simp_rw [windT]; rw [Finset.sum_mul,Finset.sum_mul,mul_sum]; apply sum_congr rfl; intro p _; ring
end Spi
lemma recovered (p:Option PlaqAxes)(l:List Axis)(h:ℕ)(X: Parc)(hx:l.length≤h)(ht:Rocky p l h X): X∈tails l.length (h+1):=by
    rw [show X=X-strike l 0+strike l 0 from (sub_add_cancel X _).symm]; exact Submodule.add_mem _ (tailUp (Nat.le_succ _) le_rfl ht.rest) (Submodule.subset_span ⟨l,0,le_rfl,hx.trans (Nat.le_succ _),rfl⟩)
end YM.Bloom
#print axioms YM.Bloom.sells
#print axioms YM.Bloom.couple
