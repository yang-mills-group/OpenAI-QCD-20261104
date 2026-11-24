import YM.Kwick.Earn
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast.Rays
variable {L c:Side}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls
variable (e:ℤ)(a b:Axis)(p u v:Site c)(X:Sheet c)(F: Grid c→ Sheet c)
local notation "w"=> step (S:=ℤ) a
local notation "D"=> step (S:=Per c) a
local notation "T"=> shift 0 (1:Grid c) a
noncomputable def stave(c:Side)(P:Site c→ℂ)(i:Fiber)(x:Site c × Fiber) := if x.2=i then P x.1 else 0
variable (i j:Fiber)(P Q:Site c→ℂ)
local notation "W"=> pars c e b
open Matrix
lemma taeg (Y: Site c × Fiber→ℂ): star (stave c P i) ⬝ᵥ Y=∑ x:Site c,star (P x)*Y (x,i):=by
    unfold dotProduct; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro x _; rw[sum_eq_single i]; simp[stave]; intro j _ h; simp [stave,h]; simp
lemma wageR(x:Site c × Fiber): (X *ᵥ stave c P i) x= ∑ y:Site c,X x (y,i)*P y:=by
     unfold mulVec dotProduct; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro y _; rw [sum_eq_single i]; simp[stave]; intro j _ h; simp[stave,h]; simp
lemma nomenS : arityG c P Q i j X= star (stave c P i) ⬝ᵥ (X *ᵥ (stave c Q j)):=by rw[taeg]; simp_rw [wageR,Finset.mul_sum]; unfold arityG; simp only [LinearMap.coe_mk,AddHom.coe_mk]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=>by ring
local notation "Z"=> plenty c e b a
lemma pEve(x:Fiber): (T *ᵥ stave c W x)= Z • stave c W x:=by
     funext i; obtain ⟨v,i⟩:= i; rw [wageR,sum_eq_single (v+step a)]; rw [ridePlane,if_pos rfl]; change _= Z * (if i=x then _ else 0); by_cases h:i=x; rw [px_turn, h,Matrix.one_apply_eq,if_pos rfl,mul_one, ← mul_assoc,← mul_assoc,seam_sq,one_mul]; rw[if_neg h,Matrix.one_apply_ne h,mul_zero,mul_zero,zero_mul]
     intro j _ h; rw[ridePlane,if_neg h,zero_mul,zero_mul]; simp
lemma rEve : star (T) *ᵥ stave c W i= star (Z) • stave c W i:=by
    let Y:= stave c W i; have hz:= pEve (c:=c) e a b i; apply (show Function.Injective (Matrix.mulVec T) from ?_); rw [mulVec_mulVec, (Lat.shift_u ..).2,one_mulVec,Matrix.mulVec_smul,hz,smul_smul,riches,one_smul]
    intro x y h; have hy:= congr_arg (Matrix.mulVec (star T)) h; rw[mulVec_mulVec,mulVec_mulVec,(Lat.shift_u ..).1,one_mulVec,one_mulVec] at hy; exact hy
lemma dLVe(S:Sheet c) : arityG c W Q i j (T*S)= Z*arityG c W Q i j S:=by
     let f:=stave c W i; let y:=stave c Q j; let X:= S *ᵥ y; rw [nomenS,nomenS,← mulVec_mulVec]; change star f ⬝ᵥ (_ *ᵥ X)=Z*(star f ⬝ᵥ X)
     rw [dotProduct_mulVec]; -- (star f)ᵥ*T
     have he: (star f) ᵥ* T= Z • star f:=by
          have hz:= rEve (c:=c) e a b i; have hp:=congr_arg star hz; rw [star_smul,star_star] at hp; have h(A:Sheet c) : star (star A *ᵥ f)=star f ᵥ* A:=by funext x; simp only [Pi.star_apply,mulVec,vecMul,dotProduct]; rw [star_sum]; apply sum_congr rfl; intro i _; rw [star_mul,show star A x i=star (A i x) from rfl,star_star] 
          rw [← h]; exact hp
     rw [he,smul_dotProduct]; rfl
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.dLVe
