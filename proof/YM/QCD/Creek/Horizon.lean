import YM.QCD.Creek.Ledge
/-! # exact grouping of independent insertions in the exterior contraction. Supports essential. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Creek
open Grass Ledge Function Finset Filter
open scoped BigOperators ContDiff Classical Topology
variable {A B ι: Type*} [Fintype A] [Fintype B]
-- Algebra adjoin or after? use projection wipe of others.
def region (U: Finset A) : Subalgebra ℂ (Alg A):=(embed (fun x:↥U=> (x:A))).range
lemma marked (i:A)(U :Finset A) (h:i∈U):atom i∈region U:=by refine ⟨atom (⟨i,h⟩: ↥U), embed_atom ..⟩
lemma regionMon {U T:Finset A}(h:U⊆T): region U ≤ region T :=by
  rintro x ⟨y,rfl⟩; let u (a:↥U):↥T:=⟨a,h a.property⟩; exact ⟨embed u y, (embed_comp ..).trans (by rfl)⟩
lemma lock (a:A) {U : Finset A}{x:Alg A}(h:x∈region U)(he:a∉U): v a x=0:=by
  obtain ⟨y,rfl⟩:=h; let e (x:↥U):A:=x; have hf (L:List ↥U) : v a (embed e (L.map atom).prod)=0:=by
    induction L with
    | nil=> simp [v,vary_one]
    | cons i L ih=> simp only [List.map_cons,List.prod_cons,map_mul,embed_atom]; change vary a (atom _*_)=0; rw [vary_mul,vary_off a _ (fun h=>he (h ▸ i.property)),zero_mul,show vary a (embed _ _)=0 from ih, mul_zero,add_zero]
  change v a (embed e y)=0; have hv i : v a (embed e (mono i))=0:=by obtain ⟨w,-,-,h⟩:= expression i; rw [h]; simpa only [List.map_ofFn] using hf (List.ofFn w)
  rw [← write y, map_sum,map_sum]; simp_rw [map_smul,hv,smul_zero,sum_const_zero]

lemma preserves (a:A){U:Finset A}{x:Alg A}(h:x∈region U): v a x ∈ region U:=by
  by_cases he:a∈U; swap; · rw [lock _ h he]; exact (region U).zero_mem
  obtain ⟨y,rfl⟩:=h; let q:↥U:=⟨a,he⟩; exact ⟨vary q y,(survives (f:=((↑) : ↥U→A)) Subtype.val_injective q y).symm⟩
lemma anti (a:A)(x:Alg A): v a (grade x)= -grade (v a x):=by
  have h (L:List A): v a (grade (L.map atom).prod)= -grade (v a (L.map atom).prod):=by
    induction L with
    | nil=> simp [v,vary_one]
    | cons i L ih=> simp only [List.map_cons,List.prod_cons]; change vary a (grade (atom i*_))=_; simp only [map_mul, grade_atom,neg_mul,map_neg, vary_head]; rw [show v a _= _ from vary_head a i (L.map atom).prod,show vary a (grade _)=_ from ih]; change _=-grade ((probe _ _ • _) - atom _ *_); simp only [map_sub,map_smul,map_mul,grade_atom,neg_mul]; rw [mul_neg]; rfl -- check
  have he i : v a (grade (mono i))=-grade (v a (mono i)):=by obtain ⟨w,-,-,hw⟩:= expression i; rw [hw]; simpa only [List.map_ofFn] using h (List.ofFn w)
  rw [← write x,map_sum,map_sum,map_sum,map_sum]; simp_rw [map_smul,he,smul_neg,sum_neg_distrib]

-- endo right property enough, preserve grade. rightM even map lower. use CLM.
def rightP (x:Alg A): EndA A:= (LinearMap.mulRight ℂ x).toContinuousLinearMap
def paint (A : Type*)[Fintype A]: EndA A:= (grade: Alg A→ₐ[ℂ] Alg A).toLinearMap.toContinuousLinearMap
structure Stays (F : EndA A)(Z:Finset A):Prop where
  evenG : Commute F (paint A)
  keeps {X:Finset A} : Z⊆X →∀ x∈region X, F x ∈region X
  parts {X: Finset A}: Disjoint X Z →∀ x∈region X,Commute F (rightP x)

lemma vcoat (i:A) {X: Finset A}(h:i∉X){x:Alg A}(hp:x∈region X): Commute (v i) (rightP x):=by refine ContinuousLinearMap.ext fun a=>?_ ; change vary i (a*x)=v i a*x; rw [vary_mul,show vary i x = 0 from lock _ hp h,mul_zero,add_zero]; rfl
lemma vill (i:A): v i*paint A=-(paint A*v i):=ContinuousLinearMap.ext (fun x=> anti ..)
lemma lament (i:A): l i*paint A=-(paint A*l i):= ContinuousLinearMap.ext (fun x=> by change atom i*_=-(grade (atom i*x)); rw [map_mul,grade_atom,neg_mul,neg_neg]; rfl) 
lemma levies (i:A)(x:Alg A): Commute (l i) (rightP x):=ContinuousLinearMap.ext (fun y=>(mul_assoc (atom i) y x).symm)
lemma gammaT {U: Finset A}{a b : A} (h:a∈U)(h':b∈U): Stays (v a*v b) U:=by
  refine ⟨(rotates _ _ _ ?_ ?_).symm,fun {X} _ i hi=>preserves _ (preserves b hi),fun {X} hx y hy=> (vcoat _ (fun h''=> Finset.disjoint_left.mp hx h'' h) hy).mul_left (vcoat _ (fun e=>Finset.disjoint_left.mp hx e h') hy)⟩
  · rw [vill a]; exact (neg_neg _).symm
  rw [vill b]; exact (neg_neg _).symm
lemma gammaL {U: Finset A}{a b : A} (h:a∈U)(h':b∈U): Stays (l a*v b) U:=by
  refine ⟨(rotates _ _ _ ?_ ?_).symm,fun {X} hx i hi=> Subalgebra.mul_mem (region X) (marked a X (hx h)) (preserves b hi),fun {X} hx y hy=> (levies a y).mul_left (vcoat _ (fun e=>Finset.disjoint_left.mp hx e h') hy)⟩
  · rw [lament a]; exact (neg_neg _).symm
  rw [vill b]; exact (neg_neg _).symm
end YM.QCD.Creek
