import YM.Poised.Starlit
/-! Generate eligibility even with repeated or skipped accounting grades.-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource MultiNext.SignedSource.Lyre
variable (P:BudgetPoint) (V:Support c) (b:Cover) [Fintype B] (x: Path c B)
variable (f : Faces (Site c) → ℝ) (g:B→ℝ){p C t:ℝ}
private lemma grown (a C:ℝ)(x y: Directions su c) {o:Site c} (ha: Sized a x P o)(hc :Sized C y P o): Sized (a+C) (x+y) P o:=by
    refine ⟨add_nonneg ha.1 hc.1,fun i=>?_⟩; rw [Pi.add_apply,add_mul]; exact (norm_add_le ..).trans (add_le_add (ha.2 _) (hc.2 _))
lemma Venture.adroit (y:Path c B)(h:Venture (P:=P) (o:=wrap c b) f g t x)(he:Venture (P:=P) (o:=wrap c b) f g C y): Venture (P:=P) (o:=wrap c b) f g (t+C) (x+y):=⟨grown P _ _ _ _ h.1 he.1,SeatD.additive _ _ _ _ _ _ h.2 he.2⟩
namespace Buoyant
open Place
lemma inertV : Buoyant (B:=B) 0 V b k:= by
   refine ⟨⟨0,Submodule.zero_mem _,fun _ _=>rfl⟩,⟨0,Submodule.zero_mem _,fun i hi=>?_⟩⟩; change 0=_ • (0:Flet B); rw [smul_zero]
lemma combined (y:Path c B)(h:Buoyant x V b k)(he: Buoyant y V b k): Buoyant (x+y) V b k:=by
   obtain ⟨⟨f,hf,ht⟩,z,hz,h⟩:=h; obtain ⟨⟨q,hq,hQ⟩,v,hv,he⟩:=he; refine ⟨⟨f+q,Submodule.add_mem _ hf hq,fun i hi=>?_⟩,z+v,Submodule.add_mem _ hz hv,fun i hi=>?_⟩
   · change _+_=f _ _+q _ _; rw [ht i hi,hQ i hi] -- ???
   change asks x.2 i+ asks y.2 i=frond b i • _; rw [h i hi,he i hi, ← smul_add]; rfl
lemma together (p:E→Path c B)(I: Finset E)(h:∀ i∈I,Buoyant (p i) V b k): Buoyant (∑ i∈I,p i) V b k:=by
   induction I using Finset.induction_on with
   | empty=> rw [sum_empty]; exact inertV ..
   | insert i I hi ih=>rw [sum_insert hi]; exact combined _ _ _ _ (h _ (by simp)) (ih fun j hj=>h j (mem_insert_of_mem hj))
end Buoyant
lemma assembleH (R:Finset E)(H:E→Path c B)(w:E→ℕ)(h:∀ i,2 ≤ w i)(ht:∀ i,Venture (P:=P) (o:=wrap c b) f g (C*p^w i) (H i))(hP:∀ i,w i< k→ Buoyant (H i) V b (w i)) (hp:0<p)(hp':p ≤1)(hC:0≤C) : Heritage P V b f g k (∑ i ∈ R,H i) p ((R.card:ℝ)*C):=by
    let v i : Fin (k+1):= ⟨min (w i-2) (k-2),by omega⟩
    let m(i: Fin (k+1)):= Finset.filter (fun j=> v j=i) R; refine ⟨fun i=>∑ j∈m i,H j,?_,?_,?_⟩
    · unfold m; simp_rw [Finset.sum_filter]; rw [sum_comm]; simp
    · intro i; apply Venture.absorbedM _ f g (Venture.togetherM f g H _ (m i) (fun j _=> ht j)); apply le_trans (b:=∑ _j∈m i, C*p^shareout i) (sum_le_sum fun j hj=> ?_)
      · rw [sum_const,nsmul_eq_mul]; have hm:m i⊆ R:=filter_subset ..; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hm)) hC) (by positivity) -- replace
      rw [← (mem_filter.mp hj).2]; exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp.le hp' (show shareout (v j) ≤ w j from by unfold shareout v; dsimp only; have:=h j; omega)) hC
    intro i hi; refine Buoyant.together _ _ _ _ fun j hj=>?_ ; have hx: v j=i:= (mem_filter.mp hj).2; have hq:shareout i=w j:=by rw [← hx] at hi ⊢; change 2+min (w j-2) (k-2) < k at hi; change 2+min (w j-2) (k-2)=w j; have:=h j; omega
    rw [hq]; exact hP j (hq ▸ hi)
lemma Heritage.plusK (y:Path c B)(h: Heritage P V b f g k x p t)(ht:Heritage P V b f g k y p C): Heritage P V b f g k (x+y) p (t+C):=by
    obtain ⟨A,rfl,hz,he⟩:=h; obtain ⟨Y,rfl,ht,h⟩:=ht; refine ⟨fun i=>A i+Y i,Finset.sum_add_distrib.symm,fun i=>?_,fun i hi=>Buoyant.combined _ _ _ _ (he i hi) (h i hi)⟩; rw [add_mul]; exact Venture.adroit _ _ _ _ _ _ (hz i) (ht i)
lemma Heritage.weak (h: Heritage P V b f g k x p t)(he:t≤C)(hp:0≤p): Heritage P V b f g k x p C:=by
   obtain ⟨z,hz,h,h'⟩:=h; exact ⟨z,hz,fun i=>Venture.absorbedM _ f g (h i) (mul_le_mul_of_nonneg_right he (pow_nonneg hp _)),h'⟩
lemma residual (h: Venture f g (P:=P) (o:=wrap c b) (C*p^(max k 2)) x)(he:0 ≤ C)(hp:0<p)(hp':p≤1): Heritage P V b f g k x p C:=by
   let T (_:Unit):=x
   simpa using assembleH P V b f g univ T (fun _=>max k 2) (fun _=>le_max_right ..) (fun _=>h) (fun i h=>by omega) hp hp' he
end Pipes
end YM.Massive.Poised
