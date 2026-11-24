import YM.Kwick.PixelL
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
variable (e e':ℤ)(a b:Axis)(p u v:Site c)(X:Sheet c)(F: Grid c→ Sheet c)
local notation "T"=> shift 0 (1:Grid c) a
local notation "D"=> Stew.delta (1:Grid c) a
local notation "P"=> pars c e b
local notation "Q"=> pars c e' b
local notation "Z"=> plenty c e b a
open Matrix
variable (i j:Fiber)(x:Massive.Density c 6)
lemma dRVe : arityG c P Q i j (X*T)= plenty c e' b a * arityG c P Q i j X:=by rw [nomenS,nomenS, ← mulVec_mulVec,pEve,Matrix.mulVec_smul,dotProduct_smul]; rfl
lemma κR : arityG c P Q i j (X*star T)= star (plenty c e' b a) * arityG c P Q i j X:=by rw [nomenS,nomenS,← mulVec_mulVec,rEve,Matrix.mulVec_smul,dotProduct_smul]; rfl
lemma κL : arityG c P Q i j (star T*X)= star (plenty c e b a) * arityG c P Q i j X:=by
     let v:= arityG c P Q i j; apply mul_left_cancel₀ (show Z≠0 from fun ht=> by have he := riches (c:=c) e b a; rw [ht,mul_zero] at he; exact zero_ne_one he);
     change Z*v _=Z*(star Z*v X); rw [show v X =_ from (?_ : v X= v (T*(star T*X))), dLVe]; -- syntax.TZ
     · change Z*v _= Z*(star Z*(Z*v (star T*X))); rw[←mul_assoc (star Z),riches,one_mul]
     rw [←mul_assoc,(shift_u ..).2, one_mul]
noncomputable def slope (c:Side)(e:ℤ)(a b: Axis):ℂ:= (2:ℂ)⁻¹*(plenty c e a b-star (plenty c e a b))
lemma k_prev : arityG c P Q i j (D*X)= slope c e b a *arityG c P Q i j X:=by unfold Stew.delta slope; rw [Matrix.smul_mul, Matrix.sub_mul,map_smul,map_sub,κL,dLVe,smul_eq_mul]; ring
lemma k_next : arityG c P Q i j (X*D)= slope c e' b a *arityG c P Q i j X:=by unfold Stew.delta slope; rw [Matrix.mul_smul, Matrix.mul_sub,map_smul,map_sub,κR, dRVe,smul_eq_mul]; ring
lemma ξverse1 (p:Flavor 6): oracle1 e b p i j x= arityG c (pars c (-e) b) (pars c (-e) b) i j (piece p p (uncoat (x 1))):=by
     let X:=x 1; change (∑ u: Site c,∑ v': Site c,seek1 e b u v' *_)= ∑ u:Site c,∑ v':Site c,_; refine sum_congr rfl (fun u _=>sum_congr rfl fun v hv=>?_); have hp:star (pars c (-e) b u)*(pars c (-e) b v)= seek1 e b u v:=by simp only[pars,←starPoint,star_mul',star_star]; unfold seek1 quest; ring
     rw[hp]; rfl
lemma ξverse2 (p:Flavor 6)(g:su.Color) : oracle2 e a b p i j g x= arityG c (pars c e a) (pars c 0 a) i j (piece p p (uncoat (rub g x (waveZ e a b)))):=by
     change (∑ u:Site c,∑ v:Site c, seek2 _ _ u v *_)= ∑ i:Site c,∑ j:Site c,_; refine sum_congr rfl fun u _=>sum_congr rfl (fun v _=>?_); rw [show star (pars c e a u)*pars c 0 a v= seek2 e a u v from ?_]; rfl
     simp only [pars,gaze_nil,mul_one,star_mul']; unfold seek2 quest; ring
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.k_prev
#print axioms YM.Massive.Patria.Gall.ξverse1
#print axioms YM.Massive.Patria.Gall.ξverse2
