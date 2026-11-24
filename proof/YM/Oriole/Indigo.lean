import YM.Oriole.Rust
/-! PC Pin eigenlines. Use ratio spinors, not absol. For proper sign scalar.Both cases. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)(g:Bool)
open Poised.Display Poised.Stative Module Finset Revolve
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
noncomputable def pulp (g:Bool):Spike:= if g then g5 else 1
local notation "G"=> pulp g
lemma P_sq : G*G=1:=by cases g <;> simp [pulp]
lemma P_adj : star G=G:=by cases g<;>simp[pulp]
lemma P_high : G∈unitary Spike:=⟨by rw[P_adj,P_sq],by rw[P_adj,P_sq]⟩
lemma P_ok : G≠0:=by intro h; have h':= P_sq g; rw[h,zero_mul] at h'; exact zero_ne_one h'
noncomputable def conjug (p:EuPin)(X:Spike):=p.matrix.val*X*p.matrix⁻¹.val
variable (U V:Spike)(s:Signed)(p:EuPin)(hp:p.Lifts s)
local notation "L" => conjug p
lemma inv2 : p.matrix⁻¹.val*p.matrix.val=1:=p.matrix.inv_val
lemma inv1 : p.matrix.val*p.matrix⁻¹.val=1:=p.matrix.val_inv
lemma E_star : p.matrix⁻¹.val=star p.matrix.val:=by
     have hv:=p.isUnitary; exact calc _= p.matrix⁻¹.val * (p.matrix.val *star p.matrix.val):=by rw [hv.2,mul_one]
                                      _=_:=by rw [← mul_assoc,inv2 p,one_mul]
lemma L_add : L (U+V)= L U+L V:=by unfold conjug; rw [mul_add,add_mul]
lemma L_up : L (U*V)= L U*L V:=by
     unfold conjug; symm; simp only [mul_assoc (p.matrix.val),mul_assoc U,mul_assoc p.matrix⁻¹.val]; rw [←mul_assoc p.matrix⁻¹.val p.matrix.val,inv2 p,one_mul] -- syntax inspect
lemma L_star : L (star U)= star (L U):=by unfold conjug; rw [E_star]; rw [star_mul,star_mul,star_star,mul_assoc]
include hp
lemma chirP : ∃ c:ℂ,L G=c • G:=by
     cases g
     · exact ⟨1,by simp only [conjug,pulp,Bool.false_eq_true,↓reduceIte,mul_one,one_smul,inv1 p]⟩
     obtain ⟨c,h,H⟩:= chir_line (EuPin.retains s hp); let X:=p.matrix.val; have hu:=p.isUnitary; change star X*g5*X=c • g5 at H; refine ⟨star c,?_⟩; rw [conjug,E_star]; change X*g5*star X=_; have hP:= congr_arg (fun x:Spike=>X*x*star X) H; change X*(star X*g5*X)*star X=X*(c • g5)*star X at hP; rw [← mul_assoc X, ←mul_assoc X,hu.2,one_mul,mul_assoc,hu.2,mul_one,Matrix.mul_smul,Matrix.smul_mul] at hP; exact Eq.symm (show star c • g5=_ from by nth_rw 1 [hP]; rw [smul_smul,h,one_smul])
lemma E_sigma (i:Axis): conjug p (gamma i)=(signT s i:ℂ) • gamma (s.perm i):=by
     let h:= EuPin.retains s hp; have he:= h.sends i; rw [conjug,he]; unfold signT; rw[mul_assoc, inv1 p, mul_one]; cases hs:s.flip i <;> simp
omit hp
variable (X:Spike)
lemma p_mag (c:ℂ)(h: L G=c • G): star c=c ∧ c*c=1:=by
     constructor
     · apply smul_left_injective ℂ (P_ok g); have hH:=L_star G p; rw [P_adj,h,star_smul, P_adj] at hH; exact hH.symm
     have h': L (1:Spike)=1:=by unfold conjug; rw [mul_one,inv1 p]
     have he:=L_up G G p; rw [P_sq,h',h,Matrix.smul_mul, Matrix.mul_smul,P_sq,smul_smul] at he; apply smul_left_injective ℂ (one_ne_zero' Spike); exact he.symm.trans (one_smul ℂ _).symm

-- fundamental fixed line for all discrete lifts. Gain via gamma axis mirror:
-- U commutes with gamma 0 gamma 1 gamma ...? Mirror is gamma_i*g5. Then U commutes gamma_i*g5 for all i, Clifford project via anticentral map uses revolve.scalar_spin with Gamma conjugated by (1+i*g5)/sqrt. identity use W and infer from 01 23 products.
private lemma y12 : sx*sy=Complex.I • sz:=by ext i j; fin_cases i <;> fin_cases j <;> simp [sx,sy,sz,Matrix.mul_apply,Fin.sum_univ_succ]
open scoped Kronecker
private lemma page : gamma 0*gamma 1*gamma 2*gamma 3= -g5:=by
  rw [show gamma 0=sx ⊗ₖ (1:Pauli) from rfl, show gamma 1=sy ⊗ₖ sx from rfl, show gamma 2=sy ⊗ₖ sy from rfl, show gamma 3=sy ⊗ₖ sz from rfl]; unfold g5; rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,one_mul,y12, Matrix.mul_assoc _ sy,yy,mul_one,Matrix.smul_mul,zz, Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,Complex.I_mul_I, neg_one_smul]
lemma shim (h:∀ (i:Axis)(p:EuPin),p.Lifts (Signed.mirror i) → conjug p U=U) : ∃ c:ℂ,U=c • 1:=by
     have hp(i: Axis):Commute U (gamma i*g5):=by
          obtain ⟨p,hp,hX⟩:= EuPin.optic i; have he:= h i p hp; unfold conjug at he; have hu:=congr_arg (· * p.matrix.val) he; rw [mul_assoc _ p.matrix⁻¹.val,inv2 p,mul_one,hX,Matrix.mul_smul,Matrix.smul_mul] at hu; exact smul_right_injective _ (show -Complex.I≠0 from neg_ne_zero.mpr Complex.I_ne_zero) hu.symm
     have h(i j:Axis): Commute U (gamma i * gamma j):=by
          have he:=(hp i).mul_right (hp j); rw [show gamma i*g5*(gamma j*g5)= -(gamma i*gamma j) from ?_] at he; simpa only [neg_neg] using he.neg_right
          rw [mul_assoc (gamma i),←mul_assoc g5,show g5*gamma j= -(gamma j*g5) by rw[five,neg_neg],neg_mul,mul_assoc _ g5,g5_sq,mul_one,mul_neg]
     have hz := (h 0 1).mul_right (h 2 3); rw [← mul_assoc,page] at hz; have hU: Commute U g5:= by simpa only [neg_neg] using hz.neg_right
     exact ⟨_,scalar_spin (fun i=>by have hp:=(hp i).mul_right hU; rwa [mul_assoc,g5_sq,mul_one] at hp)⟩
-- component eigenline at fixed reflection multipliers generalized unitary.M
lemma shine (h:U∈unitary Spike)(hV:∀ (i:Axis)(p:EuPin),p.Lifts (Signed.mirror i)→ ∃ c:ℂ, conjug p U=c • U ∧ conjug p V=c • V): ∃ v:ℂ,V=v • U := by
     obtain ⟨z,hz⟩:= shim (star U * V) (fun i p hp=>by
          obtain ⟨c,hp,hq⟩:= hV i p hp; have ht:= L_up (star U) U p; have h1:conjug p (1:Spike)=1:=by unfold conjug; rw [mul_one,inv1 p]
          rw [h.1,h1,L_star,hp,star_smul,Matrix.smul_mul,Matrix.mul_smul,h.1,smul_smul] at ht; rw [L_up,L_star,hp,hq,star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]; rw [show star c*c=1 from smul_left_injective ℂ (one_ne_zero' Spike) (ht.symm.trans (one_smul ℂ _).symm),one_smul])
     refine ⟨z,?_⟩; have hP:= congr_arg (U* ·) hz; rw [←mul_assoc,h.2,one_mul,Matrix.mul_smul,mul_one] at hP; exact hP
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.shine
