import YM.Arise.Via
/-! # precise gauge/spin count relations in section lemma.P. controls sparse budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Range
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
open Labels Maxwell
variable {r n m i j k d D:ℕ}
variable {G:Gauge}
-- homogeneous strict. Weight carries gauge generation L+2 (once) and life and spin powers.Board.L
noncomputable def legwt (k:Tube G d):ℕ×ℕ:=(k.1.1.val+2,1)
open MvPolynomial
lemma guard (i:Labels.Key G)(v:Tube G d)(h:i.1≠v.1.1.val): Labels.coord (phone d G (Pi.single v 1)) i=0:=by
    let j:=i.1; let X: Tube G d→ℝ:= Pi.single v 1; have he: stripeJ G d j X=0:=by
        unfold stripeJ; split; next hp=>funext p; apply WithLp.ofLp_injective 2; funext k; change X (⟨⟨j,_⟩,p⟩,k)=0; unfold X; refine Pi.single_eq_of_ne (?_) _; intro hv; exact h (congr_arg (fun w:Tube G d=> w.1.1.val) hv)
        next h=>rfl
    unfold Labels.coord; dsimp only [phone]; rw [spinA,LinearMap.comp_apply,show scrim G d i.1 X=0 from he, map_zero,map_zero]; rfl
lemma safe_X (i: Labels.Key G): MvPolynomial.IsWeightedHomogeneous legwt (loCast G d (X i)) (Labels.bidegree i):=by
    rw [loCast,MvPolynomial.aeval_X]; apply IsWeightedHomogeneous.sum; intro p hp; by_cases h:i.1=p.1.1.val; swap; · rw [guard i p h,map_zero,zero_mul]; exact isWeightedHomogeneous_zero _ _ _
    apply IsWeightedHomogeneous.C_mul; rw [show Labels.bidegree i=legwt p from congr_arg (fun i=> (i+2,(1:ℕ))) h]; exact isWeightedHomogeneous_X ℂ _ _
lemma preserves (s:Key G→₀ℕ)(a:ℂ): IsWeightedHomogeneous legwt (loCast G d (monomial s a)) (Finsupp.weight bidegree s):=by
    rw [monomial_eq,map_mul,show loCast G d (C a) = C a from (loCast G d).commutes a]; apply IsWeightedHomogeneous.C_mul; rw [Finsupp.prod,Finsupp.weight_apply,Finsupp.sum,map_prod]; simp_rw [map_pow]; exact IsWeightedHomogeneous.prod _ _ _ fun i _=> (safe_X i).pow _
section
open Massive UV QCD Grass Poised Elm.Pulses
noncomputable abbrev Grimo (d:ℕ):=(Tube su d→₀ℕ) × Finset (Pairs (SpinMode d))
noncomputable def sketch (p:Grimo d):Bard d:= (MvPolynomial.monomial p.1 1) ⊗ₜ[ℂ] Grass.mono p.2
noncomputable def tagwt (m:Grimo d) : ((ℕ×ℕ)×ℕ):= let w:= Finsupp.weight legwt m.1; ((2*w.1 + ∑ i∈m.2,letterWeight i,w.2),m.2.card)
noncomputable def Rgl (d:ℕ) (n j m:ℕ):Submodule ℂ (Bard d):= Submodule.span ℂ (sketch '' {x|tagwt x=((n,j),m)})
noncomputable def Rtg (d:ℕ)(n j m:ℕ):Submodule ℂ (UV.Pol d):=Submodule.span ℂ (UV.gen '' {x| UV.weight x=n ∧ Poised.Sieve.life x.1=j ∧ x.2.card=m})
open TensorProduct
lemma canR (v:PowerPair d): introduce _ (UV.gen v)∈Rgl d (UV.weight v) (Sieve.life v.1) v.2.card:=by
    unfold UV.gen; rw [introduce,map_tmul]; let z:= loCast su d (monomial v.1 1); change z⊗ₜ[ℂ] Grass.mono v.2∈_; let V:=Rgl d (UV.weight v) (Sieve.life v.1) v.2.card
    rw [z.as_sum,sum_tmul]; apply Submodule.sum_mem
    intro i hi; have hh: monomial i (MvPolynomial.coeff i z)=(MvPolynomial.coeff i z) • (monomial i 1: Lily su d):=by rw [smul_monomial];simp
    rw [hh, ← _root_.TensorProduct.smul_tmul']; refine V.smul_mem _ (Submodule.subset_span ⟨(i,v.2),?_,rfl⟩)
    have hf:= MvPolynomial.mem_support_iff.mp hi; have he: Finsupp.weight legwt i=Finsupp.weight Labels.bidegree v.1:= preserves v.1 1 hf
    change tagwt _ = _; unfold tagwt; dsimp only; rw [he,weight_slot]; unfold UV.weight Sieve.life Finsupp.sum; rfl -- possibly QE
lemma introduced {u:UV.Pol d}(h:u∈Rtg d i j k): introduce d u∈ Rgl d i j k:=by
    refine Submodule.span_induction (p:=fun x _=> introduce d x∈ Rgl d i j k) ?_ (by simp) (fun u v _ _ h hp=>by rw [map_add]; exact Submodule.add_mem _ h hp) (fun a x _ h=>by rw [map_smul]; exact Submodule.smul_mem _ _ h) h
    rintro _ ⟨p,⟨rfl,rfl,rfl⟩,rfl⟩; exact canR p
lemma basisOne (p: UV.Label d): TensorProduct.map (rollK su d).toLinearMap LinearMap.id (introduce d p.val) = p.val := revive p.val p.property.1
end
end YM.Arise.Range
#print axioms YM.Arise.Range.basisOne
#print axioms YM.Arise.Range.introduced
#print axioms YM.Arise.Range.flare
