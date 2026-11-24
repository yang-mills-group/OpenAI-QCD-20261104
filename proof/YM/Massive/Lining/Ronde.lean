import YM.Massive.Lining.Boucle
/-! # Calibration of dimension-three probes, flavor arrows, odd baryons, normalized unit: raw stencils.

Here before RG transfer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining.Temper
open QCD QCD.Lat Lattice Wilson Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
open Purl Scan Cylinder Paper TensorProduct Ferry
variable {H:Source.Hol su}{d h:ℕ} (F:Flag H d h)(U: Kedge H d h)(t:Finset Cover) (n:Side)(b: Cover)
local notation "Q" => SpinMode d
local notation "T" => Nearest t 6
local notation "Y" => Modes n 6
variable (V:Grid n)
namespace Ronde
lemma engraved (L:Land)(i:↥t): emboss U t L 0 i=if i.val=0 then 1 else 0:=by
      unfold emboss; rw [central]; split; next hu=> rw [hu,U.home,touch_one, Complex.ofReal_one,one_smul]
      next hu=> rw [Complex.ofReal_zero,zero_smul]
lemma dock (ht:0∈t)(a:Fiber)(i:Flavor 6)(j:Y) : flower U t n 0 V ((0,a),i) j=if ((0,a),i)=j then 1 else 0:=by
   let e:↥t:=⟨0,ht⟩; have hL(x:Land)(v:T): start U t x ((0,a),i) v=if v=((e,a),i) then 1 else 0:=by
       rcases v with ⟨⟨j,b⟩,w⟩; unfold start; rw [imprints]; change (if i=w then emboss U t x 0 j a b else 0)=_; rw [engraved]; simp only [show j.val=0 ↔ j=e from ⟨fun h=> Subtype.ext h,fun h=>h ▸ rfl⟩]; by_cases hv:i=w <;> by_cases h:j=e <;> by_cases hz:b=a <;> simp [*,Matrix.one_apply,eq_comm] -- revise
   rw [flower,Matrix.mul_apply]; simp_rw [hL,ite_mul]; simp only [one_mul, zero_mul]; -- fold
   rw [sum_ite_eq']; simp only [mem_univ,if_true]; unfold belt lower; simp only [Matrix.of_apply,show e.val= (0:Cover) from rfl,map_zero,add_zero,ap_origin]
lemma dock_w (ht:0∈t)(a:Fiber)(i:Flavor 6)(j:Y): Mstar (flower U t n 0 V) ((0,a),i) j=if ((0,a),i)=j then 1 else 0:=by change star (flower U t n 0 V _ _)=_; rw [dock U t n V ht]; split <;> first|exact star_one ..|exact star_zero .. -- signature
lemma jp (ht:0∈t)(a:Fiber)(i:Flavor 6): dartSpin U t n 0 V (Grass.psi ((0,a),i))=Grass.psi ((0,a),i):=by unfold dartSpin; rw [adapt_psi]; simp_rw [dock U t n V ht]; simp [ite_smul]
lemma bj(ht:0∈t)(a:Fiber)(i:Flavor 6): dartSpin U t n 0 V (Grass.bar ((0,a),i))= Grass.bar ((0,a),i):=by unfold dartSpin; rw [adapt_bar]; simp_rw [dock_w U t n V ht]; simp [ite_smul]
lemma stars (x y:Flavor 6)(M:Spike)(ht:0∈t):
    dart F U t n 0 V (bilinear x y M 0 0) = ∑ i:Pinor, ∑ j:Pinor, ∑ k:Hue,
          M i j • (bar ((0,i,k),x) * psi ((0,j,k),y)):=by
    rw [bilinear,dart_at,map_one,one_smul]; simp_rw [map_sum,map_smul,map_mul,jp U t n V ht,bj U t n V ht]
lemma nightfall (F: Flag H 9 h)(U: Kedge H 9 h) (i j k:Pinor)(ht:0∈t):
    dart F U t n 0 V (baryon i j k)=∑ σ : Equiv.Perm Hue, Equiv.Perm.sign σ •
       (psi ((0,i,σ 0),0) * psi ((0,j,σ 1),1) * psi ((0,k,σ 2),2)):=by
    rw [baryon,dart_at,map_one,one_smul]; rw [map_sum]; apply sum_congr rfl; intro i _; simp only [Units.smul_def,map_zsmul,map_mul]; simp_rw [jp U t n V ht]
lemma sunlit : dart F U t n b V (UV.unit d)=1:=by rw [UV.unit,dart_at,map_one,map_one,one_smul]
end Ronde
end YM.Massive.Lining.Temper
#print axioms YM.Massive.Lining.Temper.Ronde.stars
#print axioms YM.Massive.Lining.Temper.Ronde.nightfall
