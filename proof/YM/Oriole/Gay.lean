import YM.Oriole.Vireo
/-! UV.Label Form Count. color alignment; signed slot automorphisms. Gauge Color has no bare curvature in these slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
lemma soldF (i j:T) : let P:PowerPair d:= (0,{.inr i,.inl j}); let f:= jcoat (Matrix.single i j 1); UV.weight P=spinWeight i.1.1+ spinWeight j.1.1 ∧ (UV.gen P=f∨ UV.gen P= -f) :=by
    intro P f; have he: Sum.inr i≠ Sum.inl j:=by intro h; cases h
    constructor
    · unfold P UV.weight; rw [Labels.height,map_zero]; simp only [mul_zero,zero_add,sum_pair he]; rfl
    have hf:f=(1:GPol) ⊗ₜ[ℂ] (bar i*psi j):=by
         change (1:GPol)⊗ₜ[ℂ] (-form _)= _; congr 1; simp_rw [form,Matrix.single_apply]; -- `if`
         rw [sum_eq_single i]; · have hh: psi j*bar i= -(bar i*psi j):= atom_flip (Sum.inl j) (Sum.inr i); simp [ite_smul,hh]; -- row
         · intro k _ h; apply sum_eq_zero; intro u _; simp [h,h.symm]
         simp
    rw [hf,UV.gen]; simp only [← MvPolynomial.C_apply,MvPolynomial.C_1,←TensorProduct.tmul_neg]; rcases bladeX (Sum.inr i) (Sum.inl j) he with h|h
    · left; exact congr_arg (tmul ℂ 1) h.symm
    right; exact congr_arg (tmul ℂ 1) (show mono ({.inr i,.inl j}:Finset Ae)= -(bar i*psi j) from (by change _= -(atom _ * atom _); rw[h,neg_neg]))
variable (x:Label d)
abbrev snug (a b:Flavor 6)(m:W):= ∀ i j:T, m i j≠0 → i.2=a ∧ j.2=b ∧ spinWeight i.1.1+spinWeight j.1.1 ≤ d
local notation "u" i:arg => juncoat i
lemma feathers (hd:d≤8)(h:a≠b)(hx:CharmC a b x.val): jcoat (juncoat x.val)=x.val ∧ snug a b (juncoat x.val):=by
    let Y:=u x.val; have hQ(j:Rings d)(hp:coord j.val x.val≠0): jcoat (juncoat (gen j.val))=gen j.val ∧ snug a b (juncoat (gen j.val)):=by
         obtain ⟨v,w,hv,hw,h'⟩:=paired a b x h hx hd j hp
         obtain ⟨h1,h2⟩:= soldF v w; have he : spinWeight v.1.1+spinWeight w.1.1 ≤ d:= le_trans (Eq.ge h1) (h' ▸ (Set.Finite.mem_toFinset (weightFinite d)).mp j.property)
         rw [h']; rcases h2 with H|H
         · rw [H,j_coat]; refine ⟨rfl,fun i j hx=>?_⟩; rw [Matrix.single_apply] at hx; split at hx; next ht=> obtain ⟨rfl,rfl⟩:=ht; exact ⟨hv,hw,he⟩
           next _=>exact False.elim (hx rfl)
         rw [H,map_neg,j_coat,map_neg]; refine ⟨rfl,fun i j hx=>?_⟩; rw [Matrix.neg_apply,Matrix.single_apply] at hx; split at hx; next ht=> obtain ⟨rfl,rfl⟩:=ht; exact ⟨hv,hw,he⟩
         next _=>simp at hx
    rw [← quiet x.val ((label_law _).mp x.property).1]; change jcoat (juncoat (∑ k:Rings d,_))= _ ∧ snug _ _ (juncoat (∑ k:Rings d,_)); rw [map_sum,map_sum]; constructor
    · refine sum_congr rfl fun j _=>?_ ; by_cases he:coord j.val x.val=0
      · change jcoat (juncoat (_ • _))=_; rw[guide,he,zero_smul,map_zero,map_zero]
      rw[map_smul,map_smul,(hQ j he).1]
    intro i j hu; rw [Matrix.sum_apply] at hu -- sums linear
    by_contra hp; apply hu; refine sum_eq_zero fun k _=>?_ ; by_cases he:coord k.val x.val=0; · rw [guide,he,zero_smul,map_zero]; rfl
    rw [map_smul,Matrix.smul_apply]; rw [show juncoat _ i j=0 from by by_contra hv; exact hp ((hQ k he).2 i j hv), smul_zero]

-- Bundle coefficient cell. inherits color.Sand.Discrete stripes.
variable (p q:Multi d)(D:CensusA d)(g:su.El)(s:Signed)(w:EuPin)(hw:w.Lifts s)
local notation "F"=>Fiber
noncomputable def prism (a b:Flavor 6)(p q:Multi d)(D:W):Bundle:= Matrix.of fun i j=> D ((p,i),a) ((q,j),b)
local notation "Cg"=> colorTable g (d:=d)
local notation "V"=> touch (colour g)
lemma paints : colorAct g (jcoat D)=jcoat (star Cg*(D*Cg)):=by
     change colorAct g ((1:GPol) ⊗ₜ[ℂ] (- form D))=(1:GPol)⊗ₜ[ℂ] (- form _); rw [paint_weight]; rw [map_neg,dyeS,form_map]; rfl
lemma turning : let X:= turned w (wave w.matrix⁻¹.val) (d:=d); let Y := turned w (wave w.matrix.val.transpose) (d:=d); pinAct w (jcoat D)=jcoat (Y.transpose*(D*X)):=by
     intro X Y; change pinAct w ((1:GPol) ⊗ₜ[ℂ] (-form D))=(1:GPol)⊗ₜ[ℂ] (-form _); rw [pinAct,TensorProduct.map_tmul]; simp_rw [AlgHom.toLinearMap_apply,map_neg,map_one]; rw [form_map]
lemma pru : Cg∈unitary W:=by
     have ht:colorTable (d:=d) (conjugate g) = (star Cg).transpose:=mono_color g; let X:= touch (colour g); have hv : X∈unitary _:= touch_u (x:=colour g) ⟨su.mat_star_mul _,su.mat_mul_star _⟩
     have he:star Cg= colorTable g⁻¹:=by
          ext i j; rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]; rw [colorTable,colorTable,Matrix.of_apply,Matrix.of_apply]; by_cases h:i.2=j.2∧ i.1.1=j.1.1
          · rw [if_pos h,if_pos ⟨h.1.symm,h.2.symm⟩,colour_inv,← touch_star]; rfl
          have he : ¬(j.2=i.2∧j.1.1=i.1.1):=fun w=>h ⟨w.1.symm,w.2.symm⟩; rw [if_neg h,if_neg he,star_zero]
     constructor <;> rw [he,groom,groom,reel,colour_inv,← touch_star,← show X=V from rfl] <;> first|(rw [hv.1,mul_one,cool])|(rw [hv.2,mul_one,cool])
-- rectangular products by colors
lemma hue_left (i j:F) : (Cg*D) ((p,i),a) ((q,j),b)= (V*prism a b p q D) i j:=by
      rw [Matrix.mul_apply,Fintype.sum_prod_type, Fintype.sum_prod_type]; unfold colorTable; simp_rw [Matrix.of_apply]; -- simplify ∑ mask
      rw [sum_eq_single p]; simp [ite_mul]; rw [Matrix.mul_apply]; rfl
      · intro z _ h; simp [h.symm]
      simp
lemma hue_right (i j:F) : (D*Cg) ((p,i),a) ((q,j),b)= (prism a b p q D*V) i j:=by
      rw [Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_prod_type]; unfold colorTable; simp_rw [Matrix.of_apply]; rw [sum_eq_single q]; simp [mul_ite]; rw [Matrix.mul_apply]; rfl
      · intro z _ h; simp [h]
      simp
noncomputable def assay : Spike:= Stew.gold (prism a b p q D)
lemma king (h: jcoat D∈labels d): prism a b p q D=wave (assay a b p q D):=by
      apply Stew.gilt; intro u'; have hp:= (label_law _).mp h |>.2 u'; rw [paints] at hp; have h:=inj_coat hp; let Q:=colorTable u' (d:=d); have ht: Q*D=D*Q:= by nth_rw 1 [← h]; rw [←mul_assoc,(pru (d:=d) u').2,one_mul]; -- notation
      change _*_= _; ext i j; rw [←hue_left a b p q D, ← hue_right a b p q D]; exact congr_fun (congr_fun ht _) _
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.king
#print axioms YM.Massive.Oriole.feathers
