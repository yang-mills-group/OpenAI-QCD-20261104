import YM.TorusPCAC.Spec.FieldsReg
import YM.QCD.Revolve.Shade

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# AP geometry of genuine History

This project uses seams in **all four** directions (same as QCD). `heat` is
the canonical transfer on the cover, which descends exactly even when the
level changes (need this precision for odd primaries, though sometimes a
±ambiguous rule suffices in the mass projection proof).
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Geometry
open QCD QCD.Grass QCD.Lat Lattice Wilson Finset MeasureTheory Function RG Revolve
open scoped Matrix Topology BigOperators Kronecker Matrix.Norms.Frobenius
variable {c f n : Side} {N : ℕ}

open Stencil
@[simp] lemma wrap_nonnegative (x : Site n) : wrap n (nonnegative x)=x:=by ext i; change ((↑((x i).val):ℤ):Per n)=_; exact_mod_cast ZMod.natCast_zmod_val (x i)
lemma nonnegative_val (x : Cover) (i : Axis) : nonnegative (wrap n x) i=x i % n.val:=by apply ZMod.val_intCast
lemma nonnegative_eq {x : Cover} (h : ∀ i, 0≤x i ∧ x i<(n.val:ℤ)) : nonnegative (wrap n x)=x:=by
  funext i; rw [nonnegative_val, Int.emod_eq_of_lt (h i).1 (h i).2]

def quotient (n : Side) (x : Cover) : Cover := fun i => x i/n.val
lemma recover (x : Cover) : nonnegative (wrap n x)+ n.val • quotient n x=x:=by
  funext i; simp_rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul,nonnegative_val,quotient,Int.emod_add_mul_ediv]

lemma slide_sign (x y : Cover) : thermal n (x+n.val • y)= thermal n x * ∏ i, (-1:ℂ)^ (y i) := by
  unfold thermal; rw [← Finset.prod_mul_distrib]; refine prod_congr rfl fun i _=>?_
  simp_rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]
  rw [Int.add_mul_ediv_left, zpow_add₀ (by norm_num)]
  exact_mod_cast n.property.ne'

lemma naked (x : Site n) : thermal n (nonnegative x)=1 := by
  unfold thermal; refine prod_eq_one fun i _=> ?_; rw [Int.ediv_eq_zero_of_lt,zpow_zero];
  · exact Int.natCast_nonneg _
  unfold nonnegative; exact_mod_cast (x i).val_lt
lemma seam_step (x : Site n) (i : Axis) : thermal n (nonnegative x+step i)=seam 0 x i := by
  unfold thermal seam
  rw [Finset.prod_eq_single i] -- inspect
  · let X:=(x i).val
    let w : Side := n
    have hb : X < n.val:= ZMod.val_lt _
    have hh : (x i)+(1:Per n)=(0:Site n) i ↔ X+1=n.val:= by
      rw [show x i+1=(↑(X+1):Per n) by push_cast; rw [show (↑X:Per n)=x i from ZMod.natCast_zmod_val _]]
      constructor
      · intro H; by_contra! h
        have hv := ZMod.val_natCast_of_lt (show X+1<n.val by omega)
        rw [H,Pi.zero_apply,ZMod.val_zero] at hv; omega
      intro h; simp [Per,h]
    rw [if_congr hh rfl rfl]; simp only [Pi.add_apply,step_apply, ↓reduceIte]
    change (-1:ℂ)^(((X:ℤ)+1)/n.val)=_
    split
    next h=> rw [show (X:ℤ)+1=n.val by exact_mod_cast h, Int.ediv_self (by exact_mod_cast n.property.ne'), zpow_one]
    next h=> rw [Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast (show X+1<n.val by omega)), zpow_zero]
  · intro j _ hj; simp only [Pi.add_apply,step_apply,if_neg hj,add_zero]; unfold nonnegative
    rw [Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast (x j).val_lt), zpow_zero]
  simp
lemma thermal_step (x : Cover) (i : Axis) : thermal n (x+step i)= thermal n x * seam (0:Site n) (wrap n x) i := by
  have he := recover (n:=n) x; set a:= nonnegative (wrap n x) with h; set b:= quotient n x with hQ
  nth_rw 1 [← he]; nth_rw 1 [show a+n.val • b+step i=(a+step i)+n.val • b by abel]; rw [slide_sign,h,seam_step];
  conv_rhs => arg 1; rw [← he,slide_sign,h,naked,one_mul]
  rw [mul_comm]
lemma thermal_norm (x : Cover) : thermal n x * thermal n x=1 := by
  unfold thermal; rw [← prod_mul_distrib]; refine prod_eq_one fun i _=> ?_; rw [← mul_zpow]; simp
lemma signs (x : Cover) : thermal n x=1 ∨ thermal n x= -1:=by
  let a:=thermal n x; have he : (a-1)*(a+1)=0:=by rw [show (a-1)*(a+1)=a*a-1 by ring, show a*a=1 from thermal_norm _,sub_self];
  exact Or.imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left (mul_eq_zero.mp he)

def moved (a : Cover) (x : Site n) := x+wrap n a
abbrev heat (a : Cover) (x : Site n) := thermal n (nonnegative x+a)
lemma heated (a v : Cover) : thermal n (v+a)=heat a (wrap n v)*thermal n v:=by
  let b:= quotient n v; let x:= nonnegative (wrap n v)
  have he:= show x+n.val • b=v from recover v
  nth_rw 1 [← he]; nth_rw 1 [show x+n.val • b+a=x+a+n.val • b by abel]; rw [slide_sign]
  conv_rhs => arg 2; rw [← he,slide_sign, show thermal n x=1 from naked _, one_mul];

lemma glares (a : Cover) : Glare 1 0 (0:Site n) (wrap n a) (heat a) := by
  refine ⟨fun x=>signs _,fun i x=>?_⟩
  let v:=nonnegative x; have hx : wrap n v=x:= wrap_nonnegative _
  have hy : heat a (x+step i) * thermal n (v+step i)= thermal n (v+a+step i):=by rw [← hx,← wrap_step n i,← map_add, ← heated]; rw [add_right_comm v];
  rw [Step.rotate_one,affine,Signed.act_one]; change seam _ x i*_ = _*seam _ _ i
  rw [thermal_step] at hy
  simp only [map_add,hx, thermal_step, show thermal n v=1 from naked _, one_mul] at hy
  rw [mul_comm]; exact hy

variable (g : Ratio c f)
lemma hop_child (x : Site c) : nonnegative (g.embed x)=g.count.val • nonnegative x := by
  conv_lhs=> rw [← wrap_nonnegative x,g.embed_wrap]
  refine nonnegative_eq (fun i=> ?_); simp only [Pi.smul_apply,nsmul_eq_mul,g.exact_size,Nat.cast_mul]; constructor
  · unfold nonnegative; positivity
  · rw [mul_comm (c.val:ℤ)]; apply mul_lt_mul_of_pos_left _ (by exact_mod_cast g.count.property); unfold nonnegative; exact_mod_cast (x i).val_lt
lemma degree_child (x : Cover) : thermal f (g.count.val • x)=thermal c x := by
  unfold thermal; refine prod_congr rfl fun i _=> ?_; simp only [Pi.smul_apply,nsmul_eq_mul,g.exact_size,Nat.cast_mul]
  rw [mul_comm (g.count.val:ℤ) (x i), Int.mul_ediv_mul_of_pos_left _ _ (by exact_mod_cast g.count.property)]
lemma heat_child (a : Cover) (x : Site c) : heat (g.count.val • a) (g.embed x)=heat a x:=by unfold heat; rw [hop_child,← smul_add,degree_child]
end YM.TorusPCAC.Geometry

#print axioms YM.TorusPCAC.Geometry.heat_child
