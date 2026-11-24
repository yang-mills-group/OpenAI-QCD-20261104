import YM.TorusPCAC.Spec.Jet

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Horizon scope lemmas
Keep whole gauge-polynomial system. Use for all stencils and the
shell comparator. Doubling of weights, blade order and Poly multiplication.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Jet
open QCD QCD.Lat Function Finset MeasureTheory
open scoped BigOperators ContDiff TensorProduct Kronecker Pointwise
abbrev Index:= Labels.Key su →₀ ℕ

-- full monomial basis used by Wick
@[simp] lemma equals (x : Index) (s : Finset Letter) : monomial (x,s)=MvPolynomial.monomial x 1 ⊗ₜ[ℂ] fermBasis.ExteriorAlgebra s:=by simp [monomial]
lemma description (s : Finset Letter) : ∃ f : Fin s.card→Letter, Injective f ∧ (∀ i, i ∈ s ↔ i ∈ Set.range f) ∧
    fermBasis.ExteriorAlgebra s = (List.ofFn fun i=> ExteriorAlgebra.ι ℂ (point (f i))).prod:=by
  let q:= Set.powersetCard.ofCard (s:=s) rfl
  let f : Fin s.card ↪o Letter:= Set.powersetCard.ofFinEmbEquiv.symm q
  refine ⟨f,f.injective,fun i => (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem q i).symm,?_⟩
  rw [ExteriorAlgebra.basis_apply_ofCard fermBasis (show s.card=s.card from rfl)]; rfl
lemma blades (s : Finset Letter) (p : Index) : ∃ f : Fin s.card → Letter, Injective f ∧ (∀ i, i ∈ s ↔ i ∈ Set.range f) ∧
     monomial (p,s)=atPol (MvPolynomial.monomial p 1)*(List.ofFn (fun i=>slot (f i))).prod:=by
  obtain ⟨f,hi,h,e⟩:=description s
  refine ⟨f,hi,h,?_⟩
  have hv (l : List Letter) : (l.map slot).prod=(1:Bos) ⊗ₜ[ℂ] (l.map (fun i=>ExteriorAlgebra.ι ℂ (point i))).prod:=by
    induction l with
    | nil=> rfl
    | cons a l ih=>simp [List.map,slot,ih, Algebra.TensorProduct.tmul_mul_tmul]
  rw [equals,e,show (List.ofFn (fun i=>slot (f i)))=( (List.ofFn f).map slot) from (by rw [List.map_ofFn]; rfl),
    hv,List.map_ofFn,atPol,Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]; rfl
@[simp] lemma empty : fermBasis.ExteriorAlgebra ∅=1:=by obtain ⟨f,-,-,h⟩:=description ∅; rw [h]; simp
@[simp] lemma singleton (i : Letter):fermBasis.ExteriorAlgebra {i}=ExteriorAlgebra.ι ℂ (point i):=by
  obtain ⟨f,-,h,e⟩:=description {i}; have hp: ∀ j, f j=i:=fun j=> mem_singleton.mp ((h _).mpr ⟨j,rfl⟩); simp_rw [e,hp]; simp
lemma silicon (l : Letter): slot l=monomial (0,{l}):=by rw [slot,equals,singleton]; rfl
lemma off {s t : Finset Letter} (h:¬Disjoint s t): fermBasis.ExteriorAlgebra s*fermBasis.ExteriorAlgebra t=0:= ExteriorAlgebra.basis_mul_of_not_disjoint fermBasis (Set.powersetCard.ofCard (s:=s) rfl) (Set.powersetCard.ofCard (s:=t) rfl) h
lemma sign_of {s t : Finset Letter} (h:Disjoint s t) : ∃ v : ℤˣ, fermBasis.ExteriorAlgebra s*fermBasis.ExteriorAlgebra t=v • fermBasis.ExteriorAlgebra (s.disjUnion t h):=⟨_,ExteriorAlgebra.basis_mul_of_disjoint fermBasis (Set.powersetCard.ofCard (s:=s) rfl) (Set.powersetCard.ofCard (s:=t) rfl) h⟩
lemma units (s : Finset Letter) (t : Finset Letter) (h:Disjoint s t) (p q : Index): monomial (p,s)*monomial (q,t)=monomial (p+q,s∪t) ∨ monomial (p,s)*monomial (q,t)= -monomial (p+q,s∪t) :=by
  obtain ⟨v,e⟩:=sign_of h
  rcases Int.units_eq_one_or v with hv|hv <;> simp only [equals, Algebra.TensorProduct.tmul_mul_tmul,e,hv,MvPolynomial.monomial_mul, one_mul] <;> simp [Finset.disjUnion_eq_union,TensorProduct.tmul_neg]

lemma atomic (p : Index) (s : Finset Letter): monomial (p,s)∈ cap (orders (p,s)):=Submodule.subset_span ⟨(p,s),show orders (p,s) ≤ _ from le_rfl,rfl⟩
lemma rises : Monotone cap:=by intro a b h; exact Submodule.span_mono (Set.image_mono fun _ he=> le_trans he h)
lemma yields : Monotone admitted:= fun _ _ h=> inf_le_inf_right _ (rises h)

lemma scope_poly {p q : Index} {s t : Finset Letter} : monomial (p,s)*monomial (q,t)∈cap (orders (p,s)+orders (q,t)):=by
  by_cases h : Disjoint s t
  · have hv : orders (p,s)+orders (q,t)= orders (p+q,s∪t):=by
      unfold orders gOrder Labels.height; dsimp only; rw [map_add,mul_add,sum_union h]; omega
    rw [hv]; rcases units s t h p q with ht|ht <;> rw [ht]; exact atomic (p+q) (s∪t); exact Submodule.neg_mem _ (atomic (p+q) (s∪t))
  rw [equals,equals, Algebra.TensorProduct.tmul_mul_tmul,off h, TensorProduct.tmul_zero]; exact (cap _).zero_mem
lemma scope_mul {a b : ℕ} {v w : Pol} (ha : v∈cap a)(hb : w ∈ cap b): v*w∈cap (a+b):=by
  refine Submodule.span_induction (p:=fun v _ => v*w ∈ cap (a+b)) ?_ (by simp) (fun x y _ _ h h'=> by rw [add_mul]; exact (cap _).add_mem h h') (fun c i _ hx=> by rw [smul_mul_assoc]; exact (cap _).smul_mem _ hx) ha
  rintro x ⟨⟨p,s⟩,hp,rfl⟩;
  refine Submodule.span_induction (p:=fun w _=> monomial (p,s) * w ∈ cap (a+b)) ?_ (by simp) (fun u v _ _ hu hv=>by rw [mul_add]; exact (cap _).add_mem hu hv) (fun c u _ hu=>by rw [mul_smul_comm]; exact (cap _).smul_mem _ hu) hb
  rintro y ⟨⟨q,t⟩,ht,rfl⟩; exact rises (add_le_add (show orders (p,s) ≤ a from hp) (show orders (q,t) ≤ b from ht)) scope_poly
lemma canSlot (l : Letter) : slot l ∈ cap (spinOrder l):=by rw [silicon]; have he:=atomic 0 {l}; simpa only [orders,gOrder,Labels.height,map_zero,Nat.mul_zero,sum_singleton, zero_add] using he
lemma canOne : (1:Pol) ∈ cap 0:=by have he:=atomic 0 ∅; rw [equals,Jet.empty] at he; simpa [orders,gOrder,Labels.height,show (1:Bos) ⊗ₜ[ℂ] (1:GrassJet) = (1:Pol) from rfl] using he

lemma cap_sites {p : Index} {s : Finset Letter} : s.card*3 ≤ orders (p,s) := by
  have he:=sum_le_sum (s:=s) (fun i _=> show 3 ≤ spinOrder i from (by unfold spinOrder; omega))
  apply le_trans _ (Nat.le_add_left ..); rw [sum_const,nsmul_eq_mul] at he; exact he
lemma paint_fixed (p : Pol) : p∈invariant ↔ ∀ U, paint U p=p:=by simp [invariant,sub_eq_zero]

-- Options of spin/flavor formulas: no quotient yet
def leg (i : Flav) (s : Pinor) (k : Hue) (d : Order) := slot ⟨.col,i,s,k,d⟩
def rim (i : Flav) (s : Pinor) (k : Hue) (d : Order) := slot ⟨.row,i,s,k,d⟩

lemma both (x y : Letter) : slot x*slot y=-(slot y*slot x):=by unfold slot; simp_rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]; rw [← TensorProduct.tmul_neg]; exact congr_arg (fun x:GrassJet=> (1:Bos) ⊗ₜ[ℂ] x) (eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap ..))
end YM.TorusPCAC.Jet

#print axioms YM.TorusPCAC.Jet.both
