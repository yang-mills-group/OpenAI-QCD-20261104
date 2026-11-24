import YM.Next.EXTRACTION.Tails
import YM.Work.A15
import YM.Push.GRID_APPROXIMATION.Product

/-!
 Adapt YM.Push.GRID_APPROXIMATION.Product to reindexing statements.

# Two elementary product calculations for actual pullbacks

Split finite products by read sets: first probability Haar links reweighted
with independent (tag-conditional) noises and then weighted tag sums with
individual mass one. Use internally `integral_prod_mul`; keep envelope
hypotheses at the external integral ports so no integrability is in question.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.LocalCup
open YM.Push.GridApprox
open Function Set MeasureTheory RG
open scoped Topology BigOperators

variable {ι X : Type*} [Fintype ι]

section split
variable {s : Set ι} [DecidablePred (·∈s)]
private abbrev cutting (s : Set ι) [DecidablePred (·∈s)] :=
  Equiv.piEquivPiSubtypeProd (·∈s) (fun _ => X)

omit [Fintype ι] in
private lemma split_l {Y : Type*} {F : (ι → X) → Y} (h : Reads s F) (x) (y) (z) :
    F ((cutting (X:=X) s).symm (x,y)) = F ((cutting (X:=X) s).symm (x,z)) := by
  apply h _ _
  intro i hi
  simp [cutting, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

omit [Fintype ι] in
private lemma split_r {Y : Type*} {F : (ι → X) → Y} (h : Reads sᶜ F) (x) (y) (z) :
    F ((cutting (X:=X) s).symm (x,y)) = F ((cutting (X:=X) s).symm (z,y)) := by
  apply h _ _
  intro i hi
  simp [cutting, Equiv.piEquivPiSubtypeProd_symm_apply,show i ∉ s from hi]

private lemma parts_split (q : ι → X → ℂ) (F W : (ι → X) → ℂ)
    (hF : Reads s F) (hW : Reads sᶜ W) (a : Subtype (·∈s) → X) (b : Subtype (fun i => ¬ i ∈ s) → X)
    (x : Subtype (·∈s) → X) (y : Subtype (fun i => ¬ i ∈ s) → X) :
    let u := (cutting (X:=X) s).symm (x,y)
    (∏ i, q i (u i)) * (F u * W u) =
      ((∏ i : Subtype (·∈s), q i.val (x i)) * F ((cutting s).symm (x,b))) *
      ((∏ i : Subtype (fun i => ¬ i ∈ s), q i.val (y i)) * W ((cutting s).symm (a,y))) := by
  intro u
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i∈s)]
  have hl (i : Subtype (·∈s)) : u i.val=x i := by simp [u,cutting,Equiv.piEquivPiSubtypeProd_symm_apply, i.prop]
  have hr (i : Subtype (fun i => ¬ i∈s)) : u i.val=y i := by simp [u,cutting,Equiv.piEquivPiSubtypeProd_symm_apply, i.prop]
  have hv : F u = _ := split_l hF x y b; have he : W u = _ := split_r hW x y a
  simp only [hl,hr,hv,he]; ring
end split

section pi

variable [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

private lemma integrate_split (s : Set ι) [DecidablePred (·∈s)]
    (q : ι → X → ℂ) (F W : (ι → X) → ℂ)
    (hF : Reads s F) (hW : Reads sᶜ W) (a : Subtype (·∈s) → X) (b : Subtype (fun i => ¬ i ∈ s) → X) :
    (∫ u : ι → X, (∏ i, q i (u i)) * (F u * W u) ∂(Measure.pi fun _ => μ)) =
      (∫ x, (∏ i : Subtype (·∈s), q i.val (x i)) * F ((cutting s).symm (x,b)) ∂(Measure.pi fun _ => μ)) *
      (∫ y, (∏ i : Subtype (fun i => ¬ i∈s), q i.val (y i)) * W ((cutting s).symm (a,y)) ∂(Measure.pi fun _ => μ)) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (·∈s)
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ => μ) (·∈s)
  let p (u : ι → X) := (∏ i, q i (u i)) * (F u * W u)
  change (∫ u, p u ∂(Measure.pi fun _ => μ)) = _
  rw [← (MeasurePreserving.symm e he).integral_comp e.symm.measurableEmbedding p]
  have hh z : p (e.symm z) = ((∏ i : Subtype (·∈s), q i.val (z.1 i)) * F ((cutting s).symm (z.1,b))) *
      ((∏ i : Subtype (fun i => ¬ i∈s), q i.val (z.2 i)) * W ((cutting s).symm (a,z.2))) :=
    parts_split q F W hF hW a b z.1 z.2
  simp_rw [hh]; exact integral_prod_mul (fun x => (∏ i : Subtype (·∈s), q i.val (x i)) * F ((cutting s).symm (x,b)))
    (fun y => (∏ i : Subtype (fun i => ¬ i∈s), q i.val (y i)) * W ((cutting s).symm (a,y)))

variable {μ} {s t : Set ι} [Nonempty X] {F W : (ι → X) → ℂ} {q q' : ι → X → ℂ}

private lemma integrates (hF : Reads s F) (q : ι → X → ℂ) (hq : ∀ i, ∫ x, q i x ∂μ = 1)
    [DecidablePred (·∈s)] (b : Subtype (fun i => ¬ i ∈ s) → X) :
    (∫ u : ι → X, (∏ i, q i (u i)) * F u ∂(Measure.pi fun _ => μ)) =
      ∫ x, (∏ i : Subtype (·∈s), q i.val (x i)) * F ((cutting s).symm (x,b)) ∂(Measure.pi fun _ => μ) := by
  let a := fun _ : Subtype (·∈s) => Classical.arbitrary X
  simpa only [mul_one, integral_fintype_prod_eq_prod (fun i : Subtype (fun i => ¬ i∈s) => q i.val),
    hq, Finset.prod_const_one] using integrate_split μ s q F (fun _ => 1) hF (fun _ _ _ => rfl) a b

variable {D:Type*}[Fintype D] (r:D↪ι)

lemma shelf (F:(D→X)→ℂ)(p:ι→X→ℂ)(h:∀ i,∫ x,p i x ∂μ=1):
    (∫ x:ι→X,(∏ i,p i (x i))*F (x∘⇑r) ∂Measure.pi (fun _=> μ))=
    (∫ x:D→X,(∏ i,p (r i) (x i))*F x ∂Measure.pi (fun _=> μ)):=by
   classical
   let S:=Set.range r; let A:=Subtype (·∈S); let F':=fun x:ι→X=>F (x∘⇑r); letI : Fintype A:=Subtype.fintype _
   have H: Reads S F':=by intro x y hx; exact congr_arg F (funext fun i=> hx (show r i∈S from ⟨i,rfl⟩))
   let b:=fun _: Subtype (fun i=>¬i∈ S)=> Classical.arbitrary X
   rw [show _=(∫ x:ι→X,(∏ i,p i (x i))*F' x ∂ Measure.pi (fun _=>μ)) from rfl,integrates H p h b]
   let e:D≃ A:= Equiv.ofInjective r r.injective; let T:=MeasurableEquiv.piCongrLeft (fun _ : A=>X) e
   let g:=fun x:A→X=> (∏ i:A,p i.val (x i))*F' ((cutting S).symm (x,b)); change (∫ x, g x ∂ _) =_
   have hT:MeasurePreserving T (Measure.pi (fun _=>μ)) (Measure.pi (fun _=>μ)):=measurePreserving_piCongrLeft (fun _=>μ) e
   rw [← hT.integral_comp T.measurableEmbedding g]; apply integral_congr_ae; apply ae_of_all; intro x; dsimp only; unfold g
   have he(i:D): T x (e i)=x i:=MeasurableEquiv.piCongrLeft_apply_apply ..; rw [← e.prod_comp]; simp_rw [he]; congr 1
   apply congr_arg F; funext i; change ((cutting S).symm (T x,b)) ((e i).val)=x i; simp only [cutting, Equiv.piEquivPiSubtypeProd_symm_apply,Subtype.coe_prop,dif_pos]; exact he i
end pi
section sum
variable [Fintype X] [DecidableEq ι]

private lemma sum_split (s : Set ι) [DecidablePred (·∈s)]
    (q : ι → X → ℂ) (F W : (ι → X) → ℂ)
    (hF : Reads s F) (hW : Reads sᶜ W) (a : Subtype (·∈s) → X) (b : Subtype (fun i => ¬ i ∈ s) → X) :
    (∑ u : ι → X, (∏ i, q i (u i)) * (F u * W u)) =
      (∑ x, (∏ i : Subtype (·∈s), q i.val (x i)) * F ((cutting s).symm (x,b))) *
      (∑ y, (∏ i : Subtype (fun i => ¬ i∈s), q i.val (y i)) * W ((cutting s).symm (a,y))) := by
  let p (u : ι → X) := (∏ i, q i (u i)) * (F u * W u)
  change ∑ u, p u = _
  rw [← Equiv.sum_comp (cutting (X:=X) s).symm p,Fintype.sum_prod_type,Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => parts_split q F W hF hW a b x y

variable {s t : Set ι} [Nonempty X] {F W : (ι → X) → ℂ} {q q' : ι → X → ℂ}

private lemma sums (hF : Reads s F) (q : ι → X → ℂ) (hq : ∀ i, ∑ x, q i x = 1)
    [DecidablePred (·∈s)] (b : Subtype (fun i => ¬ i ∈ s) → X) :
    (∑ u : ι → X, (∏ i, q i (u i)) * F u) =
      ∑ x, (∏ i : Subtype (·∈s), q i.val (x i)) * F ((cutting s).symm (x,b)) := by
  let a := fun _ : Subtype (·∈s) => Classical.arbitrary X
  simpa only [mul_one, ← Fintype.prod_sum (fun i : Subtype (fun i => ¬ i∈s) => q i.val),
    hq, Finset.prod_const_one] using sum_split s q F (fun _ => 1) hF (fun _ _ _ => rfl) a b

variable {D:Type*}[Fintype D][DecidableEq D](r:D↪ι)
lemma plated (F:(D→X)→ℂ)(p:ι→X→ℂ)(h:∀ i,∑ x,p i x=1):
      (∑ x:ι→X,(∏ i,p i (x i))*F (x∘⇑r))=(∑ x:D→X,(∏ i,p (r i) (x i))*F x):=by
   classical
   let S:=Set.range r; let A:=Subtype (·∈S); let F':=fun x:ι→X=>F (x∘⇑r); letI : Fintype A:=Subtype.fintype _
   have H: Reads S F':=by intro x y hx; exact congr_arg F (funext fun i=> hx (show r i∈S from ⟨i,rfl⟩))
   let b:=fun _: Subtype (fun i=>¬ i∈ S)=> Classical.arbitrary X
   change (∑ x:ι→X,(∏ i,p i (x i))*F' x)=_
   rw [sums H p h b]
   let e:D≃ A:= Equiv.ofInjective r r.injective; let T:=Equiv.piCongrLeft (fun _ : A=>X) e
   let g:=fun x:A→X=> (∏ i:A,p i.val (x i))*F' ((cutting S).symm (x,b)); change (∑ x, g x) =_
   rw [← Equiv.sum_comp T g]; apply Finset.sum_congr rfl; intro x _; unfold g
   have he(i:D): T x (e i)=x i:=Equiv.piCongrLeft_apply_apply ..; rw [← e.prod_comp]; simp_rw [he]; congr 1
   apply congr_arg F; funext i; change ((cutting S).symm (T x,b)) ((e i).val)=x i; simp only [cutting,Equiv.piEquivPiSubtypeProd_symm_apply,Subtype.coe_prop,dif_pos]; exact he i
end sum
end YM.QCD.LocalCup
