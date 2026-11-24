import YM.QCD.Lattice.Gamma

/-! # Spin lifts for signed lattice permutations. Use relation, not a homomorphic section. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Lat Function Finset
open scoped Matrix Matrix.Norms.Frobenius

structure Swing (s : Signed) (U : Spike) : Prop where
  unit : U∈unitary _
  sends (a) : U*gamma a=(if s.flip a then -gamma (s.perm a) else gamma (s.perm a))*U
namespace Swing
variable {s t : Signed} {U V : Spike}
lemma prod (h : Swing s U) (k : Swing t V) : Swing (s*t) (U*V) := by
  refine ⟨Submonoid.mul_mem _ h.unit k.unit,fun a=>?_⟩
  rw [mul_assoc,k.sends]; cases he : t.flip a <;> cases ha : s.flip (t.perm a) <;>
   simp only [he,Bool.false_eq_true,↓reduceIte,Signed.mul_perm_apply,Signed.mul_flip,ha,Bool.xor_self,Bool.true_xor,Bool.not_false,Bool.xor_true,Bool.not_true] <;>
   rw [← mul_assoc]; all_goals simp only [Bool.false_xor,if_true,mul_neg,neg_mul,h.sends,ha,Bool.false_eq_true,↓reduceIte,neg_neg,mul_assoc]
lemma none : Swing 1 1:=⟨Submonoid.one_mem _,fun a=> by rw [one_mul,mul_one]; rfl⟩
lemma veil (B : Spike) (h : star B=B) (he : B*B=1) : g5*B∈unitary _:= Submonoid.mul_mem _ ⟨by simp,by simp⟩ ⟨by rw [h,he],by rw [h,he]⟩

lemma mir (a : Axis) : Swing (Signed.mirror a) (g5*gamma a):=by
  refine ⟨veil (gamma a) (gamma_star _) (gamma_sq _),fun i=> ?_⟩ -- notation
  by_cases hi : a=i
  · subst i; simp only [Signed.mirror,decide_true, if_true,Equiv.refl_apply, ← mul_assoc]; rw [neg_mul,five,neg_neg]
  simp only [Signed.mirror,decide_eq_true_eq,if_neg hi,Equiv.refl_apply]
  rw [mul_assoc,clifford hi,mul_neg, ← mul_assoc, ← mul_assoc,five i,neg_mul]

def pearl : ℂ:= (((Real.sqrt 2):ℝ):ℂ)⁻¹
lemma priceP : pearl*pearl=(2:ℂ)⁻¹:=by
  rw [pearl,← mul_inv_rev,← Complex.ofReal_mul,Real.mul_self_sqrt (by norm_num)]; norm_num
lemma centre : star pearl=pearl := by simp [pearl]

def pure (s : Equiv.Perm Axis) : Signed:=⟨s,fun _=>false⟩
lemma switch (i j : Axis) (h : i≠j) : Swing (pure (Equiv.swap i j)) (g5*(pearl • (gamma i-gamma j))) := by
  let A:=gamma i; let B:=gamma j; let Z:=pearl • (A-B)
  have ht : A*B=-(B*A):= clifford h
  have ha : A*A=1:= gamma_sq _; have hb : B*B=1:= gamma_sq _
  have hx : Z*Z=1:=by
    rw [show Z=_ from rfl,Matrix.smul_mul, Matrix.mul_smul, smul_smul,priceP]
    rw [sub_mul, mul_sub, mul_sub,ha,hb,ht,show (1:Spike) - -(B*A)-(B*A-1)=(2:ℂ) • (1:Spike) by rw [two_smul]; abel, smul_smul,inv_mul_cancel₀ (by norm_num),one_smul]
  have hh : star Z=Z:=by unfold Z; rw [star_smul,centre,star_sub,gamma_star,gamma_star]
  refine ⟨veil Z hh hx,fun a=> ?_⟩
  suffices hk : Z*gamma a=-(gamma (Equiv.swap i j a)*Z) by
    simp only [pure,Bool.false_eq_true,↓reduceIte]; change g5*Z*gamma a=_; rw [mul_assoc,hk,mul_neg,← mul_assoc,← mul_assoc,five,neg_mul]
  unfold Z; rw [Matrix.smul_mul,Matrix.mul_smul,← smul_neg]
  congr 1
  by_cases he : a=i; · subst a; rw [Equiv.swap_apply_left,sub_mul,mul_sub,ha,hb,neg_sub]
  by_cases hv : a=j; · subst a; rw [Equiv.swap_apply_right,sub_mul,mul_sub,ha,hb,neg_sub]
  rw [Equiv.swap_apply_of_ne_of_ne he hv, sub_mul, mul_sub, clifford (Ne.symm he), clifford (Ne.symm hv)]; abel

def sunday (v : Finset Axis):Signed:=⟨Equiv.refl _, fun i=> decide (i∈v)⟩
lemma goes (s : Signed) : ∃ U : Spike, Swing s U:= by
  have he (s : Equiv.Perm Axis):∃ U,Swing (pure s) U:= by
    induction s using Equiv.Perm.swap_induction_on with
    | one=> exact ⟨1,none⟩
    | swap_mul f i j h ih=>
      obtain ⟨v,hv⟩:=ih; exact ⟨_,(switch i j h).prod hv⟩
  have hf (v : Finset Axis) : ∃ U,Swing (sunday v) U:=by
    induction v using Finset.induction_on with
    | empty=> rw [show sunday ∅=1 by apply Signed.ext rfl; funext; simp [sunday]]; exact ⟨1,none⟩
    | insert a v hv ih=>
      obtain ⟨V,H⟩:=ih; rw [show sunday (insert a v)=Signed.mirror a*sunday v from ?_]; exact ⟨_,(mir a).prod H⟩
      refine Signed.ext rfl ?_; funext i; simp only [sunday,Signed.mul_flip,Equiv.refl_apply,Signed.mirror,mem_insert]; by_cases hw:a=i <;> simp_all [Ne.symm]
  obtain ⟨U, H⟩:= hf (univ.filter (s.flip ·)); obtain ⟨V,K⟩:=he s.perm
  refine ⟨V*U,?_⟩; convert K.prod H using 1
  refine Signed.ext rfl ?_; funext i; simp only [sunday,Signed.mul_flip,pure,Bool.false_xor,mem_filter,mem_univ,true_and,decide_eq_true_eq]; simp
end Swing
end YM.QCD.Revolve
