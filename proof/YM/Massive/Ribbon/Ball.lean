import YM.Massive.Ribbon.Graft
/-! # Flavor preserving and parity assignment in filtration, concrete RawSym unit frames. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Function Matrix Finset
open QCD QCD.Lat Lattice Grass TensorProduct
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ComplexOrder TensorProduct Kronecker Classical
variable {d:ℕ}(u v:FlavorTorus)
local notation "T" => SpinMode d
local notation "K" => starRingEnd ℂ
variable {A B:Type*}[DecidableEq A][DecidableEq B][Fintype A][Fintype B]
lemma flavor_color_mul (f:A→Flavor 6) : byFlavor u f*byFlavor v f=byFlavor (u*v) f:=by unfold byFlavor; rw [diagonal_mul_diagonal]; rfl
omit [Fintype A] in
lemma flavor_phase_one(f:A→Flavor 6): byFlavor 1 f=1:= rfl
lemma run_coil (f :A→Flavor 6)(g:B→Flavor 6)(S:Matrix A B ℂ)(h:∀ i j,f i≠g j→ S i j=0): byFlavor u f*S=S*byFlavor u g:=by
   ext i j; unfold byFlavor; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]; by_cases hh:f i=g j; swap; · rw [h i j hh,zero_mul,mul_zero]
   rw [hh,mul_comm]
omit [Fintype A] in
lemma phase_conj (f:A→Flavor 6): Mstar (byFlavor u f)=byFlavor u⁻¹ f:=by
   unfold byFlavor; ext i j; by_cases he:i=j; · subst i; rw [mstar]; simp only [Matrix.diagonal_apply_eq]; rfl
   simp only [mstar, Matrix.diagonal_apply_ne _ he,star_zero]
lemma coil_spin (d:ℕ)(k:su.El)(x:SpinPol d):
    let f:=byFlavor u (Prod.snd (α:=Multi d×Fiber)); let h:=byFlavor u⁻¹ (Prod.snd (α:=Multi d×Fiber)); let v:=colorTable (d:=d) k; adapter f h (adapter v (Mstar v) x)=adapter v (Mstar v) (adapter f h x):=by
    intro f h v; rw [adapt_together,adapt_together,show f*v=v*f from run_coil u Prod.snd Prod.snd v (fun i j h=>by simp [v,colorTable,h]),show h*Mstar v=Mstar v*h from run_coil u⁻¹ Prod.snd Prod.snd (Mstar v) (fun i j h=>by simp [v,colorTable,Mstar,h])]
lemma flavor_dance (x:Pol d)(k:su.El): flavorAct u (colorAct k x)=colorAct k (flavorAct u x):=by
   induction x using TensorProduct.induction_on with
   | zero=>simp
   | tmul x y=> unfold colorAct flavorAct; simp_rw [TensorProduct.map_tmul]; exact congr_arg₂ (tmul ℂ) rfl (coil_spin u _ k y)
   | add x y hx hy=> simp only [map_add,hx,hy]
lemma flavor_cap (x:Pol d)(h:x∈cap d): flavorAct u x∈cap d:=by
   unfold flavorAct; rw [show LinearMap.id= (Labels.rotated (G:=su) 1).toLinearMap from LinearMap.ext fun i=>(burns _).symm]; apply changeCap _ _ _ x h
   rintro (i|i) (j|j) ht; · change byFlavor _ _ i j=0; have he:i≠j:=fun hv=> ht (congr_arg (fun p:T=> UV.letterWeight (d:=d) (Sum.inl p)) hv); simp [byFlavor,he]
   · rfl
   · rfl
   change byFlavor _ _ i j=0; have he:i≠j:=fun hv=> ht (congr_arg (fun p:T=> UV.letterWeight (d:=d) (Sum.inr p)) hv); simp [byFlavor,he]
lemma flavor_coil (x:Pol d) : flavorAct u (flavorAct v x)= flavorAct (u*v) x:=by
   induction x using TensorProduct.induction_on with
   | zero=> simp
   | tmul x y=> unfold flavorAct; simp_rw [TensorProduct.map_tmul]; apply congr_arg₂ (tmul ℂ); rfl; simp only [AlgHom.toLinearMap_apply]; rw [adapt_together,flavor_color_mul,flavor_color_mul,mul_comm v u,_root_.mul_inv_rev]
   | add x y hx hy=> simp only [map_add,hx,hy]
lemma flavor_unit (x:Pol d): flavorAct 1 x=x:=by
   induction x using TensorProduct.induction_on with
   | zero=> simp
   | tmul x y=> unfold flavorAct; rw [TensorProduct.map_tmul]; simp only [AlgHom.toLinearMap_apply,inv_one,LinearMap.id_apply]; rw [flavor_phase_one]; simp
   | add x y hx hy=> simp [hx,hy]
lemma flavor_label (x:Label d): flavorAct u x.val∈labels d:=by
    have h:= (label_law _).mp x.property; exact (label_law _).mpr ⟨ flavor_cap u _ h.1,fun v=> (flavor_dance u _ v).symm.trans (by rw [h.2 v])⟩
noncomputable def flavorCore (d:ℕ):Label d≃ₗ[ℂ]Label d where
   toFun x:=⟨_,flavor_label u x⟩
   invFun x:=⟨_,flavor_label u⁻¹ x⟩
   left_inv x:=Subtype.ext (Eq.trans (flavor_coil u⁻¹ u x.val) (by simp [flavor_unit]))
   right_inv x:=Subtype.ext (Eq.trans (flavor_coil u u⁻¹ x.val) (by simp [flavor_unit]))
   map_add' x y:=Subtype.ext (map_add (flavorAct u) x.val y.val)
   map_smul' c x:=Subtype.ext (map_smul (flavorAct u) c x.val)

lemma parity_dance (x:Pol d)(k:su.El): parityAct (colorAct k x)=colorAct k (parityAct x):=by
   induction x using TensorProduct.induction_on with
   | zero=>simp
   | tmul x y=> unfold colorAct parityAct; simp_rw [TensorProduct.map_tmul]; exact congr_arg₂ (tmul ℂ) rfl (exterior_parity _ y)
   | add x y hx hy=> simp only [map_add,hx,hy]
lemma parity_cap (x:Pol d)(h:x∈cap d): parityAct x∈cap d:=by
   refine cabin («T»:=parityAct) ?_ x h; rintro ⟨i,j⟩ he; have h:parityAct (gen (i,j))=(-1:ℂ)^j.card • gen (i,j):=by unfold parityAct gen; rw [TensorProduct.map_tmul]; change _ = _ • ((MvPolynomial.monomial i 1) ⊗ₜ[ℂ] mono j); rw [←tmul_smul,← grade_mono]; rfl
   rw [h]; exact Submodule.smul_mem _ _ (pay_gen _ he)
lemma parity_twice (x:Pol d) : parityAct (parityAct x)=x:=by
   induction x using TensorProduct.induction_on with
   | zero=>simp
   | tmul x y=> unfold parityAct; simp_rw [TensorProduct.map_tmul]; exact congr_arg₂ (tmul ℂ) rfl (grade_twice y)
   | add x y hx hy=> simp [hx,hy]
lemma parity_label (x:Label d): parityAct x.val∈labels d:=by
    have h:= (label_law _).mp x.property; exact (label_law _).mpr ⟨ parity_cap _ h.1, fun u=> (parity_dance x.val u).symm.trans (by rw [h.2])⟩
noncomputable def parityCore(d:ℕ): Label d≃ₗ[ℂ]Label d where
   toFun x:=⟨_,parity_label x⟩
   invFun x:=⟨_,parity_label x⟩
   left_inv x:=Subtype.ext (parity_twice x.val)
   right_inv x:=Subtype.ext (parity_twice x.val)
   map_add' x y:=Subtype.ext (map_add parityAct x.val y.val)
   map_smul' c x:=Subtype.ext (map_smul parityAct c x.val)
lemma fuel (d:ℕ): unit d∈labels d:=by
   rw [label_law]; have hp:unit d=gen (0,∅):=by rw [gen]; simp [unit, MvPolynomial.C_1, ←MvPolynomial.C_apply]; -- infer
   constructor; rw [hp]; apply pay_gen; simp [weight,Labels.height]
   intro u; unfold unit colorAct; rw [TensorProduct.map_tmul]; simp
noncomputable def RawSym.exhibit : RawSym where
    flavor d u:= flavorCore u d
    pin d p:= pinCore d p
    charge d:= chargeCore d
    adj d a:= adjCore a d
    parity d:=parityCore d
    unit d:=⟨_,fuel d⟩
    flavorActs _ _ _:= rfl
    pinActs _ _ _:=rfl
    chargeActs _ _:= rfl
    parityActs _ _:= rfl
    adjActs _ _ _:= rfl
    unitActs _:= rfl
#print axioms RawSym.exhibit
end YM.Massive.UV
