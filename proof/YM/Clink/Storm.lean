import YM.Clink.Night
/-! Tilt origin row lower cost at one stop. nonpert finite. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
open Next.Free QCD.Entr QCD.Entr.Meridian
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)(hi:i≤ N)
local notation "M"=> S.side R i
variable (a b:Flavor 6) (s t:Axis)(g:su.Color)(u:Averaging)(T:TaperHol)(W:QCD.Flume.Plan d)(H:Train d)(z:ℝ)
local notation "φ"=> A.density i
local notation "G"=> corm (i:=i) A d W H z a
local notation "Y"=> report A (G s) u i 0
local notation "P"=> rayC φ a
open QCD.Entr.Goals Patria.Gall.Seals
local notation "W'"=> cedar d W H z M
local notation "S₀"=> W' (1:Grid M)
local notation "X"=> totalR W'
-- exact totalR cedar at origin ANY. commutes with shift by Tempo turn H=V Seam
lemma doll (F:Sheet c)(h:Globe.Tempo F) : Stew.delta (1:Grid c) s*F= F*Stew.delta 1 s:=by
     let Q:=(shift 0 (1:Grid c) s); let o:=(0:Site c); let z:=rplus c s; let u(x:Site c):=seam 0 x s; let T:=Bay.Strut.haze z 1 u; have he:Q=T:=by
           unfold Q Lat.shift T; change rides _ _= rides _ _; congr 1
           funext i; change touch (thread (0:Site c) (1:Grid c) s i)=_; unfold thread; rw[show colour _ =1 from rfl ]; unfold u; unfold touch wave; simp only [star_one,Matrix.kronecker_smul,Matrix.one_kronecker_one]
     have hh:T∈unitary _:= Bay.Strut.trail (warrantL ..); have hm: Q*F=F*Q:= he ▸ Globe.standstill rfl T hh (h.turns _ _ _ (warrantL ..)) -- ambiguity arguments
     have hp:star Q*F=F*star Q:=by
            have hu: Q∈unitary _:= he ▸ hh; calc
              _= star Q * (F * (Q*star Q)):=by rw[hu.2,mul_one]
              _= F*star Q:=by rw[←mul_assoc F,← hm,mul_assoc Q,← mul_assoc,hu.1,one_mul]
     unfold Stew.delta; rw [Matrix.smul_mul,Matrix.mul_smul, Matrix.sub_mul,Matrix.mul_sub,hm,hp]
lemma sunP : totalR W' s (1:Grid M)=0:=by
      unfold totalR; rw[doll s,sub_self]; change Globe.Tempo (_+_); apply (Globe.savior ..).add ((Globe.Tempo.one (c:=M)).smul _)
local notation "D"=> Stew.delta (1:Grid M) s
local notation "O"=> punct (0:Site M)
local notation "V"=> foil φ Y
include hA hi
lemma scoreW (h:IsUnit (φ 1)): Oren.discs b (V 1)=if b=a then ((D*O)*(P-S₀)-(P-S₀)*(O*D)) else 0:=by
      let Gx:= marque A true a s (i:=i); let Z:= Gx 0; let K:=forkT a 0 s W'; have hz: V 1= foil φ Z 1+(K 1).val:=by
            rw [arrivesHere]; let v:= (A.density i) 1; change Ring.inverse v *(Z 1+ (actor A i 1)*(forkT _ _ _ _ _).val)=foil φ Z 1+(K 1).val; rw [mul_add, map_zero,show actor A i 1= φ 1 from congr_fun (act A hA hi) 1]; rw[←mul_assoc (Ring.inverse _),Ring.inverse_mul_cancel v h,one_mul]
      have hp : Z 1= applyMark false (keel (0:Site M) s a 1) (φ 1)- applyMark true (keelB 0 s a 1) (φ 1):=by change Wagon _ _ _ _=_; unfold Wagon PCAC.Oren.axle; simp only [map_zero, Complex.ofReal_one,one_smul,↓reduceIte]; rw [show actor A i 1= φ 1 from congr_fun (act A hA hi) 1]; rfl
      have he: K 1= - sourceT a 0 s W' 1:=by unfold K forkT; rw[Pi.sub_apply,aurasigmaMont,facesigmaX,facesigmaX,sunP,map_zero,map_zero,map_zero,map_zero,map_zero,add_zero,smul_zero,zero_sub] -- counts
      let J:= O*D; let L:= D*O; let α:=P; rw [hz,map_add,cove b _ _ _ _ _ h (hA.even hi 1) hp,show keel (0:Site M) s a 1=J ⊗ₖ spot a a from ?_,show keelB (0:Site M) s a 1=L ⊗ₖ spot a a from ?_,Ks,Sv,he,θB]; rotate_left
      · unfold keelB L; rw [←cashD,show copies 6 O= O ⊗ₖ 1 from QCD.Sway.choir_in ..,← Matrix.mul_kronecker_mul,mul_one]
      · unfold keel J; rw [←cashD,show copies 6 O= O ⊗ₖ 1 from QCD.Sway.choir_in ..,← Matrix.mul_kronecker_mul,one_mul]
      let K' := S₀*J-L*S₀; have hp: discs b ((-bouquet a K').val)= if b=a then K' else 0:=by
           change piece b b (uncoat (coat (_ ⊗ₖ spot a a)))=_; rw [coat_known]; ext i j; change (K' ⊗ₖ spot a a) _ _= _; split; next h=>simp [PCAC.spot,h]
           next h=> simp [PCAC.spot,h]
      rw[show discs b _= _ from hp]; split
      next h=>subst b; rw[mul_sub,sub_mul]; unfold K' L J Oriole.rayC; rw[Matrix.mul_smul,Matrix.smul_mul,smul_sub]; abel
      next _=>rw[sub_self,smul_zero,zero_add]
omit hA hi
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.scoreW
