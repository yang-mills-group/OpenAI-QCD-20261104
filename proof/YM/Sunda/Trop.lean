import YM.Lobo.Fox
set_option maxHeartbeats 610000
set_option autoImplicit false
noncomputable section
namespace YM.Sunda
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Poised Massive.Poised.Display Massive.Poised.Stative Module Finset Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
variable {d:ℕ}
private noncomputable def zetaL:ℂ:=⟨-1/2,√3/2⟩
local notation "z₀"=> zetaL
lemma zetaC : star z₀*z₀=1∧z₀^3=1∧ z₀≠1:=by
      have he:= Real.sq_sqrt (show 0 ≤ (3:ℝ) from by norm_num)
      norm_num [Complex.ext_iff,zetaL,pow_succ,Complex.mul_re,Complex.mul_im]; constructor <;> try constructor <;> try nlinarith [show (√ (3:ℝ)) ^ 3 = (3:ℝ) * √(3:ℝ) by rw[pow_succ,he]]
lemma colorsU (A:Mat)(h:A∈unitary _)(ht:A.det=1): ∃ u:su.El,colour u=A:=⟨⟨⟨_,h⟩,ht⟩,rfl⟩
lemma fortune(z:ℂ)(hZ:star z*z=1)(h:z^3=1):∃ u:su.El,colour u=z • (1:Mat):=by
      apply colorsU; · constructor <;> (rw[star_smul,star_one,smul_mul_assoc,one_mul, smul_smul]; first | rw[hZ,one_smul]| rw[mul_comm z, hZ,one_smul])
      rw [Matrix.det_smul,Fintype.card_fin]; simp [h]
variable (u:su.El) (z:ℂ) (hy:star z*z=1)(hz:colour u= z • (1:Mat))
local notation "T"=>SpinMode d
local notation "Ae"=> Pairs T
local notation "S"=>colorAct (d:=d) u
include hz hy
lemma fixedG (A:su.Color): su.adjoint u A=A:=by
    apply Gauge.colorMat_injective; rw[Gauge.mat_adjoint]; change colour u* _*star (colour u)=_; rw[hz,star_smul,star_one,smul_mul_assoc,one_mul, mul_smul_comm,mul_one,smul_smul,hy,one_smul]
lemma wonP(i:GPol): Labels.changed (fun _=>Labels.Taylor.paint u) i=i:=by
      apply Labels.eval_ext; intro J; rw[Labels.eval_changed]; apply congr_arg (fun t:Labels.Jet su=> Labels.read t i); funext l; apply Labels.Taylor.value_ext; funext i zt; change Labels.Taylor.value (Labels.Taylor.paint u (J l)) i zt=_; rw [Labels.Taylor.paint_value,fixedG u z hy hz]
      -- use Taylor.value_ext
lemma sideW (g:GPol)(i:SpinPol d): S (g⊗ₜ[ℂ]i)=g⊗ₜ[ℂ]dyeS d u i:=by unfold colorAct; rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply,wonP u z hy hz]; rfl
omit hy
include hz
abbrev priceZ (z:ℂ)(a:Ae):ℂ:= Sum.elim (fun _:T=>z) (fun _:T=> star z) a
lemma tilt (a:Ae): dyeS d u (atom a)= priceZ z a • atom a:=by
      rcases a with ⟨⟨p,i,k⟩,q⟩|⟨⟨p,i,k⟩,q⟩
      · change dyeS d u (male p q i k)=_; rw [drizzle,hz]; rw [sum_eq_single k]; · rw [Matrix.smul_apply,Matrix.one_apply_eq, smul_eq_mul,mul_one]; rfl
        · intro l _ h; rw [Matrix.smul_apply,Matrix.one_apply_ne h.symm,smul_zero,zero_smul]
        simp
      change dyeS d u (other p q i k)=_; rw [drizzle_rev,hz]; rw[sum_eq_single k]; · rw [Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one]; rfl
      · intro l _ h; rw [Matrix.smul_apply,Matrix.one_apply_ne h.symm,smul_zero,star_zero,zero_smul]
      simp
include hy
lemma ions (p:PowerPair d):∃ t:ℂ,S (gen p)=t • gen p:=by
     unfold gen; rw[sideW u z hy hz]; obtain ⟨f,-,-,ht⟩:= expression p.2
     have hx(A: List Ae):∃ q:ℂ,dyeS d u (A.map atom).prod=q • (A.map atom).prod:=by
        induction A with
        | nil=>exact ⟨1,by simp⟩
        | cons i l ih=> obtain ⟨t,h⟩:=ih; refine ⟨priceZ z i*t,?_⟩; simp only [List.map_cons,List.prod_cons]; rw [map_mul,h, tilt u z hz, mul_smul]; rw[smul_mul_assoc,mul_smul_comm]
     have hp:= hx (List.ofFn f); simp only[List.map_ofFn,←ht] at hp; obtain ⟨t,h⟩:=hp; exact ⟨t,by rw [h,tmul_smul]⟩
omit hy hz
lemma dues(x:Label d)(hd:d≤8)(j:Rings d)(hc:coord j.val x.val≠0): j.val.2=∅∨∃ i k:T,j.val.2={.inr i,.inl k}:=by
      obtain ⟨Y,hz⟩:= fortune z₀ zetaC.1 zetaC.2.1; let t:=j.val.2
      have hp(r:ℂ)(h:colorAct Y (gen j.val)=r • gen j.val): r=1:= judge x j hc (colorAct Y) (ions Y z₀ zetaC.1 hz) (((label_law _).mp x.property).2 _) r h
      have hx':#t*3 ≤ ∑ i∈t,letterWeight i:=by rw[show #t*3=∑ _i∈t, (3:ℕ) from (by simp)]; exact sum_le_sum fun i _=> Nat.le_add_right ..
      have hQ: 2*Labels.height j.val.1+∑ i∈t, letterWeight i ≤ 8:= (upper j).trans hd
      rcases (show #t=0∨ #t=1∨ #t=2 from by omega) with h|h|h; · exact Or.inl (card_eq_zero.mp h)
      · obtain ⟨i,hi⟩:=card_eq_one.mp h; have ht:priceZ z₀ i=1:=by apply hp; change colorAct _ (_ ⊗ₜ[ℂ] mono t)=_ • (_⊗ₜ[ℂ]mono t); rw [sideW _ _ zetaC.1 hz, hi,mono_single,tilt _ z₀ hz,tmul_smul]
        exfalso; apply zetaC.2.2; cases i with
        | inl _=> exact ht
        | inr _=> change star z₀=1 at ht; rw [←star_star z₀,ht,star_one]
      right; obtain ⟨a,b,ha,he⟩:= card_eq_two.mp h
      have ht: priceZ z₀ a* priceZ z₀ b=1:=by
            apply hp; change colorAct _ (_⊗ₜ[ℂ]mono t)=_ • (_⊗ₜ[ℂ]mono t); rw [sideW _ _ zetaC.1 hz,he,←tmul_smul]; congr 1
            rcases bladeX a b ha with hv|hv; · rw[←hv,map_mul,tilt _ z₀ hz,tilt _ z₀ hz, smul_mul_assoc,mul_smul_comm,mul_smul]
            rw[show mono {a,b}= -(atom a* atom b) from by rw [hv,neg_neg],map_neg,map_mul,tilt _ z₀ hz,tilt _ z₀ hz, smul_mul_assoc,mul_smul_comm,mul_smul, smul_neg,smul_neg]
      have hm:z₀*z₀≠1:=by intro hv; apply zetaC.2.2; have hu:=zetaC.2.1; rw [pow_succ,pow_two,hv,one_mul] at hu; exact hu
      rcases a with a|a <;> rcases b with b|b; · exact False.elim (hm ht)
      · exact ⟨_,_,he.trans (Finset.pair_comm ..)⟩
      · exact ⟨_,_,he⟩
      change star z₀ * star z₀=1 at ht; rw [← star_mul] at ht; exact False.elim (hm (by rw [← star_star (_*_ :ℂ),ht,star_one]))
end YM.Sunda
#print axioms YM.Sunda.dues
