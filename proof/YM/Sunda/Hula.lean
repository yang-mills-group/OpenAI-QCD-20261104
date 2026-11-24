import YM.Sunda.Trop
set_option maxHeartbeats 610000
set_option autoImplicit false
noncomputable section
namespace YM.Sunda
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Poised Massive.Poised.Display Massive.Poised.Stative Module Finset Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
variable {d:ℕ}
open Grass.Ward
local notation "A"=> SpinMode d
local notation "T₀"=> SpinPol d
local notation "W"=> CensusA d
variable (J:Labels.Jet su)
local notation "Y"=> ready d J
local notation "R"=> Labels.read J
local notation "Δ"=> skin (d:=d) J
variable (j:Rings d)(x:Label d)(hd:d≤8)
include hd
lemma shapeP (hp:coord j.val x.val ≠ 0) : let g:=gen j.val; Y g= R (fog g) • (1:SpinPol d)+ Oriole.coat (Δ g):=by
       intro g; let G:GPol:= MvPolynomial.monomial j.val.1 1; rcases dues x hd j hp with H|⟨i,k,H⟩
       · rw [show g=G⊗ₜ[ℂ](1:T₀) from by unfold g UV.gen; rw[H,mono_empty], unit_fog,unit_skin,ready_t,map_zero,add_zero]
       rcases bladeX (Sum.inr i) (Sum.inl k) (by intro h; cases h) with he|he
       · rw [show g=G ⊗ₜ[ℂ] (bar i*psi k) from by unfold g UV.gen bar psi; rw [H,he],ready_t,bought_skin,cool_fog,map_zero,zero_smul,zero_add,map_smul,simple_single]
       rw [show g= -(G⊗ₜ[ℂ](bar i*psi k)) from by unfold g UV.gen; rw [H, ← tmul_neg,bar,psi,he,neg_neg],map_neg Y,map_neg fog,map_neg Δ,cool_fog,neg_zero,map_zero,zero_smul,zero_add,map_neg,bought_skin,map_smul,simple_single,ready_t]
lemma vistaL : Y x.val = R (fog x.val) • (1:T₀)+ Oriole.coat (Δ x.val):=by
     rw [← quiet x.val ((label_law _).mp x.property).1]; simp only [Poised.Stative.line,LinearMap.coe_mk,AddHom.coe_mk]; rw [map_sum,map_sum,map_sum,map_sum,map_sum,sum_smul, ← Finset.sum_add_distrib]; refine sum_congr rfl fun j _=>?_; by_cases hp:coord j.val x.val=0; · rw[guide,hp]; simp
     rw [map_smul,map_smul,map_smul,map_smul,map_smul,shapeP _ j x hd hp,smul_add,smul_smul]; rfl
local notation "B"=>colorTable (d:=d)
variable (u:su.El)
local notation "P"=>star (B u)
lemma sedge : fog x.val∈ Labels.localFields su (d/2):=by
    refine ⟨fog_cap x,fun J u=>?_⟩; have hu:= visual u J x.val; rw [((label_law _).mp x.property).2] at hu; rw [← expected,← expected x.val, hu, vistaL (Labels.colored u J) x hd,map_add (luminous _ _),map_smul (luminous _ _),map_one (luminous _ _)]
    let p:= colorTable u (d:=d); have he: coef ∅ (luminous d u (Oriole.coat (skin (Labels.colored u J) x.val)))=0:=by
          change coef ∅ (adapter _ _ (-form _))=0; rw[map_neg,form_map]; exact rawMintSkin _
    simp_rw [map_add,he,rawMintSkin]
lemma bet : Δ x.val=P*(skin (Labels.colored u J) x.val*B u):=by
    have hu:= visual u J x.val; rw [((label_law _).mp x.property).2,vistaL _ x hd,vistaL _ x hd] at hu; rw [map_add,map_smul,map_one, (sedge x hd).2 J u] at hu -- sedge args
    have he:= add_left_cancel hu; nth_rw 1 [← coat_known (Δ x.val)]; rw [he]; change uncoat (adapter _ _ (- form _))=_; rw[map_neg,form_map]; exact coat_known _
omit hd
local notation "T"=>SpinMode d
lemma splits_one (p : Powers) (hp : p≠0) : ∃ i : Labels.Key su,∃ q:Powers,p=q+Finsupp.single i 1 := by
  obtain ⟨i,h⟩ : p.support.Nonempty := by simpa using hp
  have ht : Finsupp.single i 1 ≤ p := by
    intro x; by_cases he : x=i
    · subst x; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)
    simp [Ne.symm he]
  exact ⟨i,p-Finsupp.single i 1,(tsub_add_cancel_of_le ht).symm⟩
variable (i k:SpinMode d)
private lemma enough (m:Powers)(p q:T): let Qx:PowerPair d:=(m,{Sum.inr p,Sum.inl q}); weight Qx=2*Labels.height m + (spinWeight p.1.1+spinWeight q.1.1):=by intro Q; unfold UV.weight; rw [show Q.2={Sum.inr p,Sum.inl q} from rfl, sum_pair (by intro h; cases h)]; rfl
structure Dew (v:Pol d):Prop where
      field : ∀ J:Labels.Jet su, skin J v= skin 0 v
      trim : ∀ i k:SpinMode d, skin 0 v i k≠0→ spinWeight i.1.1+spinWeight k.1.1≤ d
noncomputable def Reel (d:ℕ):Submodule ℂ (Pol d) where
      carrier:={x | Dew x}
      add_mem':=by
             intro x y hx hy; change Dew _ at hx hy; constructor; · intro J; rw [map_add,map_add,hx.field, hy.field]
             intro i k h; rw[map_add,Matrix.add_apply] at h; by_cases ht:skin 0 x i k=0; · rw [ht,zero_add] at h; exact hy.trim _ _ h
             exact hx.trim _ _ ht
      zero_mem':=⟨by simp, fun i k h=>False.elim (h (by rw[map_zero]; rfl))⟩
      smul_mem':=by
            intro z v h; change Dew _ at h; constructor; · intro J; rw [map_smul,map_smul,h.field]
            intro i k hn; exact h.trim _ _ (fun he=> hn (by rw[map_smul,Matrix.smul_apply,he,smul_zero]))
include hd
lemma rents(p:Powers)(h:weight (d:=d) (p,{Sum.inr i, Sum.inl k})≤d):p=0∧ spinWeight i.1.1+spinWeight k.1.1≤d:=by
         have he:= enough p i k; rw [show weight (p,{Sum.inr i,Sum.inl k})=2*Labels.height p+(spinWeight i.1.1+spinWeight k.1.1) from he] at h; have hX : p=0:=by
             by_contra ht; obtain ⟨b,t,h'⟩:= splits_one p ht; have hv: Labels.height p=Labels.height t+ (b.1+2):=by rw[h', Labels.height,map_add,Finsupp.weight_single,one_smul]; rfl
             have hz:= Oriole.low i.1.1; have hs:= Oriole.low k.1.1; omega
         exact ⟨hX, by omega⟩
lemma mumbles(h:spinWeight i.1.1+spinWeight k.1.1≤d):(1:GPol)⊗ₜ[ℂ](bar i*psi k) ∈ Reel d:=by
       refine ⟨?_,?_⟩; · intro J; rw [bought_skin,bought_skin,map_one,map_one]
       intro a c hv; rw[bought_skin,map_one,one_smul, Matrix.single_apply] at hv; split at hv; · rename_i H; obtain ⟨rfl,rfl⟩:=H; exact h
       exact False.elim (hv rfl)
lemma orbitX (hp:coord j.val x.val≠ 0):gen j.val∈ Reel d:=by
       rcases dues x hd j hp with h|⟨u,v,h⟩; · unfold UV.gen; rw [h,mono_empty]; refine ⟨fun J=>?_,fun i l h=>?_⟩; rw[unit_skin,unit_skin]; exact False.elim (h (by rw [unit_skin]; rfl))
       have he:j.val=(j.val.1,{ Sum.inr u,Sum.inl v}):=Prod.ext rfl h
       obtain ⟨hz,hr⟩:=rents hd u v j.val.1 (show weight (d:=d) (j.val.1,{Sum.inr u,Sum.inl v})≤ d from (by rw [← he]; exact upper _))
       unfold UV.gen; rw [hz,h]; rcases bladeX (Sum.inr u) (Sum.inl v) (by intro h; cases h) with ht|ht; · rw [← ht]; exact mumbles hd u v hr
       rw[show mono {Sum.inr u,Sum.inl v}= -(atom (Sum.inr u)* atom (Sum.inl v)) from by rw [ht,neg_neg], tmul_neg]; exact Submodule.neg_mem _ (mumbles hd _ _ hr)
lemma dewP : Dew x.val:=by
       change x.val∈ Reel d; rw [← quiet x.val ((label_law _).mp x.property).1]; change ∑ i:Rings d,_∈ Reel d; refine Submodule.sum_mem _ fun j _=>?_ ; by_cases ht:coord j.val x.val=0; rw [guide,ht,zero_smul]; exact Submodule.zero_mem _
       exact Submodule.smul_mem _ _ (orbitX j x hd ht)
variable(a b:Flavor 6)(p q:Multi d)
local notation "U"=> touch (colour u)
local notation "μ"=> gravel a b p q
local notation "X"=> skin (d:=d) (0:Labels.Jet su) x.val
lemma conveys : B u*X = skin (Labels.colored u (0:Labels.Jet su)) x.val*B u:=by
    calc
       _= B u*(P*(skin (Labels.colored u (0:Labels.Jet su)) x.val*B u)):=by nth_rw 1 [bet _ x hd u]
       _= _:=by rw[← mul_assoc,(pru _).2,one_mul]
lemma mirrorV : μ (skin (Labels.colored u (0:Labels.Jet su)) x.val)* U= U*μ X:=by
     ext i j; exact Eq.trans (Eq.symm (hue_right a b p q ..)) ((congr_fun (congr_fun (conveys x hd u).symm _) _).trans (hue_left ..))
lemma postage : μ X=wave (Stew.gold (μ X)):=by
     apply Stew.gilt; intro u; have he:= mirrorV x hd u a b p q; rw[show Labels.colored u (0:Labels.Jet su)=0 from funext fun i=> map_zero (Labels.Taylor.paint u)] at he; exact he.symm
noncomputable def lamp (a b:Flavor 6)(p q:Multi d): Pol d→ₗ[ℂ]Spike:= ingot ∘ₗ gravel a b p q ∘ₗ skin 0
lemma lacks (hZ:fog x.val=0)(he:∀ a b:Flavor 6,∀ p q:Multi d,spinWeight p+spinWeight q ≤ d→ lamp a b p q x.val=0):x=0:=by
      let D:= X; have h:= dewP x hd; have hp: D=0:=by
             ext ⟨⟨p,i⟩,a⟩ ⟨⟨q,j⟩,b⟩; by_contra H; have hx:= h.trim _ _ H; have hv: gravel a b p q D=0:=by unfold D; rw[postage x hd a b p q, show Stew.gold (gravel a b p q (skin 0 x.val))=0 from he a b p q hx]; ext ⟨p,w⟩ ⟨r,u⟩; simp [wave]
             exact H (congr_fun (congr_fun hv i) j)
      apply Subtype.ext; apply Poised.Display.distinct; intro J; rw [vistaL _ x hd,h.field,show X=0 from hp,hZ,map_zero,map_zero,zero_smul,zero_add]; exact Eq.symm (map_zero _)
end YM.Sunda
#print axioms YM.Sunda.lacks
#print axioms YM.Sunda.sedge
