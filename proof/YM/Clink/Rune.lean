import YM.Clink.Birds
import YM.Clink.Savor
/-!
  Whole adduct ribbons. actual BA invariances: only weight data and true Stoke stencil. Charge via transpose on cedar; leaf kept; flow by total.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite Tawny Tawny.Cast TorusPCAC.Geometry TorusPCAC.Ward Oriole
open Next.Free QCD.Flume TorusPCAC.Jet TorusPCAC.Spin TorusPCAC.Jet.Selector Switch AxisB
variable {c:Side}
variable (d:ℕ)(P:Plan d)(H:Train d)(m:ℝ)
variable (o:Site c)(a:Flavor 6)(x:Axis)(V:Grid c)
local notation "S"=> cedar d P H m c
local notation "A"=> S V
local notation "T" V:arg=> totalR S x V
local notation "Z"=> punct o
local notation "U"=> TorusPCAC.Stencil.conjGrid V
local notation "τ" V:arg=> delta V x
-- single sheet expression
noncomputable def peakZ (z:ℂ)(X Y K: Sheet c) : Sheet c:= z • (K*(X*Y-Y*X)+(X*Y-Y*X)*K) - (Y*(K*X)-(X*K)*Y)
local notation "Safe"=>-(2:ℂ)⁻¹
noncomputable def scans (Y:Grid c→Sheet c) (V:Grid c):= peakZ (-(2:ℂ)⁻¹) (τ V) (Y V) Z
local notation "Xr" i:arg=> scans o x S i
lemma yields (Y:Grid c→Sheet c) : forkT a o x Y V = bouquet a (scans o x Y V):=by
       let D:= totalR Y x V; have hf (q:Sheet c): Massive.PCAC.zone 6 o*capsΛ a q=capsΛ a (Z*q):=by
            change _*(q ⊗ₖ spot a a) = (Z*q)⊗ₖ spot a a; rw [← cashD,show copies 6 Z= Z⊗ₖ 1 from QCD.Sway.choir_in ..,← Matrix.mul_kronecker_mul,one_mul]
       have hh(q:Sheet c): capsΛ a q*Massive.PCAC.zone 6 o=capsΛ a (q*Z):=by
            change (q ⊗ₖ spot a a)*_=(q*Z)⊗ₖ spot a a; rw [←cashD,show copies 6 Z= Z⊗ₖ 1 from QCD.Sway.choir_in ..,← Matrix.mul_kronecker_mul,mul_one]
       unfold forkT; rw [Pi.sub_apply,θB,scans,peakZ,map_sub,map_sub,map_smul,map_add,map_sub]; change (-(2:ℂ)⁻¹) • (cream (Massive.PCAC.zone 6 o*capsΛ a D)+cream (capsΛ a D*Massive.PCAC.zone 6 o))-_= _; rw [hf,hh]; rfl
noncomputable def twistF : Sheet c→ₗ[ℂ]Sheet c := {
       toFun:=fun X=>(onSpin c Cmat⁻¹*X*onSpin c Cmat).transpose, map_add':=fun x y=>by rw[mul_add,add_mul,Matrix.transpose_add],map_smul':=fun s x=>by rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.transpose_smul]; rfl }
local notation "R"=> onSpin c Cmat
local notation "L"=> onSpin c Cmat⁻¹
local notation "Q"=> twistF (c:=c)
lemma chainR (X Y:Sheet c): Q (X*Y)= Q Y* Q X:=by
       let F(X:Sheet c):=L*X*R; have hr:R*L=1:=by rw[on_spin_mul,pays_C',on_spin_one]
       change (F (X*Y)).transpose= (F Y).transpose*(F X).transpose; rw[← Matrix.transpose_mul]; unfold F; congr 1; simp only [Matrix.mul_assoc]; rw[←Matrix.mul_assoc R L,hr,one_mul]

lemma antZ : Q Z=Z:=by
      have hh : Commute R Z:=by unfold Commute SemiconjBy; unfold punct Lat.onSpin; rw [ride_mul,ride_mul]; congr 1; funext i; split_ifs <;> try simp_all
      change (L*Z*R).transpose= Z; rw [mul_assoc, hh.eq.symm, ←mul_assoc, fee, one_mul]; ext ⟨p,i⟩ ⟨q,j⟩; rw [Matrix.transpose_apply,ζD,ζD]; by_cases hp:p=q<;> by_cases hi:i=j <;> split_ifs <;> simp_all [Matrix.one_apply] <;> grind
lemma τf : Q (τ U) = -delta V x:=by change (L*_ *R).transpose=_; rw [mul_assoc,(show Commute (τ U) R from Stew.Δ_spins ..).eq,←mul_assoc,fee,one_mul, δc]
lemma coinB(X: Sheet c) : TorusPCAC.Stencil.charge c (bouquet a X).val=(bouquet a (twistF X)).val:=by
       let Sr:= Jobs c 6 Cmat; let Tr:=Jobs c 6 Cmat⁻¹; unfold TorusPCAC.Stencil.charge; rw [shifted]; let D:= X ⊗ₖ spot a a; change shiftC Sr Tr (QCD.Grass.form D) = QCD.Grass.form ((_ :Sheet c) ⊗ₖ spot a a); rw [Switch.tune]; apply congr_arg; unfold D; rw[show Sr=R ⊗ₖ 1 from QCD.Sway.choir_in .., show Tr=L⊗ₖ 1 from QCD.Sway.choir_in ..,← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,mul_one,one_mul]; change (Q X) ⊗ₖ (spot a a).transpose= _; rw [spotT]
lemma coreB : TorusPCAC.Stencil.charge c (forkT a o x S U).val=(forkT a o x S V).val:=by
       rw[yields,yields,coinB]; congr 2; unfold scans peakZ; rw[map_sub,map_smul,map_add,map_sub,chainR,chainR,chainR,chainR,map_sub,chainR,chainR,chainR,chainR,show Q (S U)= A from alder d P H m V,τf,antZ]; simp; abel
lemma auraB(X Tr:Sheet c) (hv:Tr∈unitary _):
       Kit.disguise (copies 6 Tr) (bouquet a X).val= (bouquet a (star Tr*(X*Tr))).val:=by
       let G:=copies 6 Tr; let Y:= spot a a; change adapter G _ (QCD.Grass.form _) = QCD.Grass.form _; rw [form_map, Matrix.transpose_transpose]; apply congr_arg; change star G *((X ⊗ₖ Y)*G)= _; rw [show G=Tr ⊗ₖ 1 from QCD.Sway.choir_in ..,Lat.star_kr,← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul, star_one,one_mul,mul_one]; rfl -- maybe won't match. ext
lemma κfactor(u:ℂ)(p:ℂ)(X X' Y Y' K K' Tr: Sheet c)(hX:X*Tr= Tr*(p • X'))(hY:Y*Tr=Tr*Y')(hK:K*Tr=Tr*K')(hv:Tr∈unitary _): star Tr*(peakZ u X Y K*Tr) = p • (peakZ u X' Y' K'):=by
        let f:= LinearMap.mulLeft ℂ (star Tr) ∘ₗ LinearMap.mulRight ℂ Tr -- prove
        have ht(Sr Sr':Sheet c)(h:Sr*Tr=Tr*Sr'):f Sr=Sr':=by change star Tr * (Sr*Tr) =_; rw [h,←mul_assoc,hv.1,one_mul]
        have hp(G H): f (G*H)=f G* f H:=by change star Tr*(_*Tr)= (star Tr* (G*Tr)) * (star Tr*(H*Tr)); simp only[mul_assoc]; rw[←mul_assoc Tr (star Tr), hv.2,one_mul]
        change f _= _; unfold peakZ; simp only [map_sub,map_add,map_smul,hp,ht X _ hX,ht Y _ hY,ht K _ hK,Matrix.smul_mul,Matrix.mul_smul,← smul_sub, ← smul_add,←smul_assoc]; simp only[smul_add,smul_sub,smul_eq_mul,smul_smul,mul_comm p]
-- general transformation.Sp.Tide and Charge done separately. 
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.coreB
#print axioms YM.Massive.PCAC.Oren.auraB
#print axioms YM.Massive.PCAC.Oren.κfactor
