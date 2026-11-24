import YM.Elms.Stony
/-! # Color rotor correspondence real gradient branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open LinearMap
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
local notation "M" => Mat
local notation "N" => Lat.Fields n 6
local notation "K" g:arg=>landsE n o g
local notation "T" g:arg=>stripe n o g U
noncomputable def bill (M0:ΔM)(U:Grid n):N:=∑ i:Dike, ∑ j:Dike, M0 i j • (beams false n o v U j * beams true n o w U i)
lemma settle (M0:ΔM): bill o w v M0 U=linkB (K w) (K v) (star (T w)* M0*T v):=by
    unfold bill linkB beams peggle lineT; simp_rw [if_true,Bool.false_eq_true,if_false]
    simp_rw [Finset.mul_sum,Finset.sum_mul,_root_.smul_mul_assoc,_root_.mul_smul_comm,Finset.smul_sum,smul_smul]
    let f(i j x y:Dike):N:= ((star (T w) x i*M0 i j)*(T v) j y) •(psi (place (K v) y)*bar (place (K w) x)); simp_rw [Matrix.mul_apply,Finset.sum_mul,sum_smul];
    calc _ = ∑ i:Dike,∑ j:Dike, ∑ x:Dike,∑ y:Dike, f i j x y := by
               apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; unfold f; simp only [Matrix.transpose_apply]; congr 1; ring
         _ = _ := by
             have he {X:Type} [AddCommGroup X] (F:Dike → Dike → Dike → Dike → X): ∑ i:Dike,∑ j:Dike,∑ k:Dike,∑ a:Dike,F i j k a=∑ k:Dike,∑ a:Dike,∑ j:Dike,∑ i:Dike,F i j k a:=by
                 conv_lhs=> rw [Finset.sum_comm]
                 simpa only [Fintype.sum_prod_type (α₁:=Dike) (α₂:=Dike)] using (Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (u v:Dike×Dike)=>F u.2 u.1 v.1 v.2)) -- arg names
             exact he f
lemma cob_conj (g:su.El)(A:su.Color): cob (su.adjoint g⁻¹ A)=star (colour g)* cob A * colour g:=by
    dsimp only [cob]; rw [su.mat_adjoint]; unfold Gauge.conjugate; simp; rfl
variable (A:su.Color)
noncomputable def dualSp (F:Grid n):N:= -bill o w (w++[posDir a]) (RP.down 6 a (cob A)) F - bill o (w++[posDir a]) w (RP.up 6 a (cob A)) F
lemma weight_move (h:P.t=0) : let g:=haloW n o w U; blux (pathDeriv U P (K w,a) (su.adjoint g⁻¹ A))= star (T w)*blux (cob A)*T (w++[posDir a]):=by
     intro g; rw [stripe_head]; unfold pathDeriv; rw [h,blux_mu]
     rw [← Matrix.mul_assoc _ (T w)]; congr 1
     rw [cob_conj,blux_mu,blux_mu,stripe,star_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,stripe_star,smul_smul,Poised.Pipes.ap_sq,one_smul,blux_star]
lemma Δ_reads (h:P.t=0) : dualSp o w a A U= ΔZ U P (K w,a) (su.adjoint (haloW n o w U)⁻¹ A):=by
   unfold dualSp; simp_rw [settle]; rw [land_head]; let A1:= cob A; let g:=haloW n o w U; let P1:=pathDeriv U P (K w,a) (su.adjoint g⁻¹ A); have he:= weight_move U P o w a A h
   unfold ΔZ RP.spans; change (-linkB (K w) (K w+ step a) _)-linkB _ _ _= -linkB (K w) (K w+step a) (RP.down 6 a P1)-linkB _ _ (RP.up 6 a P1);
   change blux P1= _ at he
   have hf:star (T w)* RP.down 6 a A1 * T (w++[posDir a])=RP.down 6 a P1:=by
       unfold down; rw [copies_mul,copies_mul]; change star (T w)*(mL (Lat.lo a)*blux A1)*_=mL _*blux P1; rw [← Matrix.mul_assoc,(starstripe U o w _).eq,he]; simp only [A1,Matrix.mul_assoc]
   have hg: star (T (w++[posDir a]))*RP.up 6 a A1*T w= RP.up 6 a P1:=by
       unfold RP.up; rw [copies_mul,copies_mul]; change star _*(mL (hi a)*blux (star A1))*_=mL _*blux (star P1); rw [← Matrix.mul_assoc,(starstripe U o (w++[posDir a]) _).eq,blux_star,blux_star,he]; simp only [star_mul,star_star,A1, Matrix.mul_assoc]
   rw [hf,hg]
end Arbor
end SparK
end YM.Massive.Elm
