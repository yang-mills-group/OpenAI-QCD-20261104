import YM.Massive.Lining.Cameo
import YM.Massive.Target.Physics
/-! # Explicit physical observables in the calibration machinery, off-shell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Lattice Wilson RG Source Function QCD Lat Massive Lining Papyrus Filter Work.G05 Finset Matrix Labels Grass TensorProduct
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
variable {d:ℕ}(p: Multi d)(q: Flavor 6)(g: su.El)(i:Pinor)(k:Hue)
local notation "Q" => SpinMode d
abbrev dyeS (d:ℕ)(u:su.El): SpinPol d→ₐ[ℂ]SpinPol d:= adapter (colorTable u) (Mstar (colorTable u))
abbrev pigment (d:ℕ)(u:FlavorTorus): SpinPol d→ₐ[ℂ]SpinPol d:= adapter (byFlavor u (fun i=>i.2)) (byFlavor u⁻¹ (fun i=>i.2))
abbrev male (p:Multi d) (q:Flavor 6) (i:Pinor)(k:Hue): SpinPol d:= psi ((p,i,k),q)
abbrev other (p:Multi d) (q:Flavor 6) (i:Pinor)(k:Hue): SpinPol d:= bar ((p,i,k),q)
lemma keyColour (w:Q) : colorTable g ((p,i,k),q) w=if w.1.1=p ∧ w.1.2.1=i ∧ w.2=q then Lat.colour g k w.1.2.2 else 0:=by
   unfold colorTable; rcases w with ⟨⟨x,s,t⟩,v⟩; rw [Matrix.of_apply]; change (if q=v ∧ p=x then (1:Spike) i s *colour g k t else 0)= if x=p ∧ s=i ∧ v=q then colour g k t else 0; rw [Matrix.one_apply]; split_ifs <;> simp_all
lemma sum_hue {X:Type*}[AddCommMonoid X] (f:Q→X) : (∑ w:Q,if w.1.1=p ∧ w.1.2.1=i ∧ w.2=q then f w else 0) = ∑ k:Hue, f ((p,i,k),q):=by
   let v:Hue→Q:=fun k=> ((p,i,k),q); have hv: Injective v:=fun _ _ e=> congr_arg (fun x:Q=>x.1.2.2) e
   rw [← sum_filter]; rw [show (univ.filter _)=univ.image v from ?_]; rw [sum_image hv.injOn]
   ext ⟨⟨x,a,b⟩,c⟩; simp [v]; aesop
lemma drizzle : dyeS _ g (male p q i k)=∑ v:Hue, (colour g k v) • male p q i v:=by
   unfold dyeS male; rw [adapt_psi]; simp_rw [keyColour,ite_smul,zero_smul]; exact sum_hue p q i (fun w=> colour g k w.1.2.2 • psi w) -- regroup δ for spin/fiber/q then simpl.
lemma drizzle_rev : dyeS _ g (other p q i k)=∑ v:Hue, star (colour g k v) • other p q i v:=by
   unfold dyeS other; rw [adapt_bar]; simp_rw [mstar,keyColour, apply_ite (star:ℂ→ℂ),star_zero,ite_smul,zero_smul]; exact sum_hue p q i (fun w=>star (colour g k w.1.2.2) • bar w)
lemma pig_p (u:FlavorTorus):pigment d u (male p q i k)= (u q).val • male p q i k:=by unfold pigment male; rw [adapt_psi]; simp [byFlavor,Matrix.diagonal_apply,ite_smul]
lemma pig_b (u:FlavorTorus):pigment d u (other p q i k)= star (u q).val • other p q i k:=by unfold pigment other; rw [adapt_bar]; unfold byFlavor; simp_rw [Matrix.diagonal_apply, ite_smul, zero_smul,Finset.sum_ite_eq]; rw [if_pos (mem_univ _)]; rfl
lemma pig_weight (h:FlavorTorus)(x:GPol)(y:SpinPol d): flavorAct h (x ⊗ₜ[ℂ] y)=x ⊗ₜ[ℂ] pigment _ h y:=TensorProduct.map_tmul ..
lemma paint_weight (y:SpinPol d): colorAct g ((1:GPol) ⊗ₜ[ℂ] y)= 1 ⊗ₜ[ℂ] dyeS _ g y:=by unfold colorAct; rw [TensorProduct.map_tmul]; simp [dyeS]; rfl
lemma parity_weight (y:SpinPol d): parityAct ((1:GPol) ⊗ₜ[ℂ] y)=1 ⊗ₜ[ℂ] grade y:= TensorProduct.map_tmul ..
abbrev weightS {d:ℕ} (n:ℕ) := Rim.grains (Pairs (SpinMode d)) UV.letterWeight n
lemma q_male : male p q i k∈weightS (spinWeight p):= by change atom (A:=Pairs Q) (Sum.inl ((p,i,k),q)) ∈ weightS _; exact Rim.grains_atom letterWeight (Sum.inl ((p,i,k),q))
lemma q_other : other p q i k∈weightS (spinWeight p):= by change atom (A:=Pairs Q) (Sum.inr ((p,i,k),q)) ∈ weightS _; exact Rim.grains_atom letterWeight (Sum.inr ((p,i,k),q))
lemma cost_root (d:ℕ) : spinWeight (0:Multi d)=3:=by unfold spinWeight; simp_rw [UV.order,Purl.power_zero]; simp
lemma ivory (x:SpinPol d)(n:ℕ)(hv:n≤d)(h:x∈weightS n): (1:GPol) ⊗ₜ[ℂ] x∈ UV.cap d:=by
   refine UV.pump 1 x h ?_; intro t ht; rw [MvPolynomial.support_one] at ht; rw [mem_singleton] at ht; subst t; simpa only [Labels.height,map_zero,mul_zero,zero_add] using hv
end YM.Massive.UV
#print axioms YM.Massive.UV.drizzle
