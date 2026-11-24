import YM.Tawny.Bright
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
open Grass.Ward
noncomputable abbrev fog : Pol d→ₗ[ℂ]GPol:= linkOut ∅
noncomputable def skin (J:Labels.Jet su) : Pol d→ₗ[ℂ] W:= uncoat.comp (ready d J)
variable (J:Labels.Jet su) (X:GPol)
local notation "R"=>Labels.read J
local notation "T₀"=>SpinPol d
local notation "Y"=> ready d J
local notation "Δ"=> skin (d:=d) J
lemma unit_un : uncoat (1:T₀)=0:=by ext i j; change - -coef ∅ (vary (.inl j) (vary (.inr i) (1:SpinPol d)))=0; simp [vary_one]
lemma unit_fog : fog (X ⊗ₜ[ℂ] (1:T₀))=X:=by rw[apart, ← mono_empty, Grass.read,one_smul]
lemma unit_skin: Δ (X ⊗ₜ[ℂ] (1:T₀))=0:=by unfold skin; rw [LinearMap.comp_apply,ready_t,map_smul,unit_un,smul_zero]
lemma simple_single(i l:T) : Oriole.coat (Matrix.single i l 1)=bar i*psi l:=by
     have ht:= j_single i l 1; have hu:= congr_arg (ready d 0) ht; change (ready d 0) ((1:GPol)⊗ₜ[ℂ] Oriole.coat _)=(ready d 0) (_⊗ₜ[ℂ]_) at hu; rw [ready_t,ready_t,map_one,one_smul,one_smul,one_smul] at hu; exact hu -- J unused include
lemma bought_skin(i l:T) : Δ (X⊗ₜ[ℂ] (bar i*psi l))=R X • Matrix.single i l 1:=by
     unfold skin; rw [LinearMap.comp_apply,ready_t,map_smul,← simple_single,coat_known]
lemma mintSkin(u:W) : Δ (X⊗ₜ[ℂ]Oriole.coat u)= R X • u:=by unfold skin; rw [LinearMap.comp_apply,ready_t,map_smul,coat_known]
lemma cool_fog(i l:T): fog (X⊗ₜ[ℂ] (bar i*psi l))=0:=by
     rcases bladeX (Sum.inr i) (Sum.inl l) (by intro h; cases h) with hu|hu
     · unfold bar psi; rw [hu,apart,Grass.read_other,zero_smul]; exact Ne.symm (insert_ne_empty _ _)
     unfold bar psi; rw [hu,apart,map_neg,Grass.read_other,neg_zero,zero_smul]; exact Ne.symm (insert_ne_empty _ _)
lemma rawMintSkin(u:W):coef ∅ (Oriole.coat u)=0:=by
     change coef ∅ (- form u)=_; rw [map_neg,form, map_sum]; rw [sum_eq_zero]; rw [neg_zero]
     intro i _; rw [map_sum]; refine sum_eq_zero fun j _=>?_ ; rw [map_smul, psi, bar, atom_flip, map_neg,show coef _ _=0 from ?_,neg_zero,smul_zero]
     rcases bladeX (Sum.inr i) (Sum.inl j) (by intro h; cases h) with h|h; rw[h,Grass.read_other]; exact Ne.symm (insert_ne_empty _ _)
     rw[h,map_neg,Grass.read_other,neg_zero]; exact Ne.symm (insert_ne_empty _ _)
lemma mintFog(u:W): fog (X⊗ₜ[ℂ]Oriole.coat u)=0:=by rw[apart,rawMintSkin,zero_smul]
variable (j:Rings d)(x:Label d)(h:Quiet x.val)(hd:d≤10)
include h hd
lemma scheme (hp:coord j.val x.val ≠ 0) : let g:=gen j.val; Y g= R (fog g) • (1:SpinPol d)+ Oriole.coat (Δ g):=by
       intro g; let G:GPol:= MvPolynomial.monomial j.val.1 1; rcases orderR x j h hd hp with H|⟨i,k,hk,H⟩
       · rw [show g=G⊗ₜ[ℂ](1:T₀) from by unfold g UV.gen; rw[H,mono_empty], unit_fog,unit_skin,ready_t,map_zero,add_zero]
       rcases bladeX (Sum.inr i) (Sum.inl k) (by intro h; cases h) with he|he
       · rw [show g=G ⊗ₜ[ℂ] (bar i*psi k) from by unfold g UV.gen bar psi; rw [H,he],ready_t,bought_skin,cool_fog,map_zero,zero_smul,zero_add,map_smul,simple_single]
       rw [show g= -(G⊗ₜ[ℂ](bar i*psi k)) from by unfold g UV.gen; rw [H, ← tmul_neg,bar,psi,he,neg_neg],map_neg Y,map_neg fog,map_neg Δ,cool_fog,neg_zero,map_zero,zero_smul,zero_add,map_neg,bought_skin,map_smul,simple_single,ready_t]
lemma visualP : Y x.val = R (fog x.val) • (1:T₀)+ Oriole.coat (Δ x.val):=by
     rw [← quiet x.val ((label_law _).mp x.property).1]; simp only [Poised.Stative.line,LinearMap.coe_mk,AddHom.coe_mk]; rw [map_sum,map_sum,map_sum,map_sum,map_sum,sum_smul, ← Finset.sum_add_distrib]; refine sum_congr rfl fun j _=>?_; by_cases hp:coord j.val x.val=0; · rw[guide,hp]; simp
     rw [map_smul,map_smul,map_smul,map_smul,map_smul,scheme _ j x h hd hp,smul_add,smul_smul]; rfl
omit h hd
lemma upper (i:Rings d): weight i.val≤d:= (Set.Finite.mem_toFinset (weightFinite d)).mp i.property
lemma fog_cap : fog x.val∈Labels.limited su (d/2):=by
     have hz(j:Rings d): fog (gen j.val)∈ Labels.limited su (d/2):=by
         have ht:= upper j; have he:Labels.height j.val.1 ≤ d/2:=by unfold UV.weight at ht; omega
         unfold UV.gen; rw [apart]; apply Submodule.smul_mem; unfold Labels.limited; rw [MvPolynomial.restrictSupport_eq_span]; exact Submodule.subset_span ⟨_,he,rfl⟩
     rw [← quiet x.val ((label_law _).mp x.property).1]; simp only [Poised.Stative.line,LinearMap.coe_mk,AddHom.coe_mk]; rw [map_sum]; refine Submodule.sum_mem _ fun j _=>?_ ; rw [map_smul]; exact Submodule.smul_mem _ _ (hz _)
variable (u:su.El)
local notation "A"=> colorTable (d:=d) u
local notation "P"=> star A
include h hd
lemma diets : fog x.val∈ Labels.localFields su (d/2):=by
    refine ⟨fog_cap x,fun J u=>?_⟩; have hu:= visual u J x.val; rw [((label_law _).mp x.property).2] at hu; rw [← expected,← expected x.val, hu, visualP (Labels.colored u J) x h hd,map_add (luminous _ _),map_smul (luminous _ _),map_one (luminous _ _)]
    let p:= colorTable u (d:=d); have he: coef ∅ (luminous d u (Oriole.coat (skin (Labels.colored u J) x.val)))=0:=by
          change coef ∅ (adapter _ _ (-form _))=0; rw[map_neg,form_map]; exact rawMintSkin _
    simp_rw [map_add,he,rawMintSkin]
lemma token : Δ x.val=P*(skin (Labels.colored u J) x.val*A):=by
    have hu:= visual u J x.val; rw [((label_law _).mp x.property).2,visualP _ x h hd,visualP _ x h hd] at hu; rw [map_add,map_smul,map_one, (diets x h hd).2 J u] at hu -- diets args
    have he:= add_left_cancel hu; nth_rw 1 [← coat_known (Δ x.val)]; rw [he]; change uncoat (adapter _ _ (- form _))=_; rw[map_neg,form_map]; exact coat_known _
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.visualP
#print axioms YM.Massive.Tawny.token
