import YM.Massive.Mass.Half
import YM.Massive.Target.Tower
import YM.QCD.High.Stroll
/-!
# The bare or effective mass Hessian

No body scanning mistakes from taking the full integrated pressure
in place of the scalar coefficient; this measurement is local in *gauge field
space*. Keep the original flavor convention. The lemma about the second derivative
is for any flavor (e.g. need no equality premise on u_j).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Reading
open QCD QCD.Lat Lattice Wilson Function QCD.Grass QCD.Stew QCD.Globe QCD.Globe.HalfMass
open Cove Flume Finch Reggae
open High.PrismT
open Filter Finset
open scoped Topology ContDiff Classical Matrix BigOperators Matrix.Norms.L2Operator
variable {c f:Side} {A : Type*} [Fintype A] {j n N k : ℕ}
section any
lemma drop_degree (x : Alg A) (i:A) (h:x∈layer A n) : vary i x∈layer A (n-1):=by
  rw [← write x,map_sum]; apply Submodule.sum_mem; intro z _; rw [map_smul]; by_cases hx:z.card=n; · exact Submodule.smul_mem _ _ (hx ▸ (lowers i z))
  rw [spectrum h _ hx,zero_smul]; exact Submodule.zero_mem _
lemma absent (i:A) (v: Finset A)(h:i∉v): vary i (mono v)=0:=by
  have he (l:List A) (hp:i∉l): vary i (l.map atom).prod=0:=by
    induction l with
    | nil=> simp [vary_one]
    | cons a b ih=>
      have hi : i≠a:=fun h=>hp (by simp [h]); simp [vary_mul,vary_off _ _ hi,ih (fun h=>hp (List.mem_cons_of_mem _ h))]
  obtain ⟨f,hq,hm,hF⟩:=expression v; rw [hF]; simpa only [List.map_ofFn] using he (List.ofFn f) (by simpa [Set.mem_range] using (mt (hm i).2 h))

variable [DecidableEq A]
lemma mono_hessian (i k : A)(x : Finset (Pairs A)) :
    coef ∅ (vary (.inl k) (vary (.inr i) (mono x)))= - (grasp (mono x) i k):=by
   let l : Pairs A:=.inl k; let r : Pairs A:=.inr i
   by_cases he : x=tag i k
   · subst x
     have h : - (1:ℂ)=coef ∅ (vary l (vary r (psi k * bar i))):=by
        change -(1:ℂ)=coef ∅ (vary l (vary r (atom l * atom r))); simp only [vary_mul, grade_atom,vary_off r l (by simp [l,r]),vary_self,zero_mul,mul_one,zero_add,map_neg]; rw [← mono_empty (A:=Pairs A), Grass.read] -- rw might rew 1 lhs
     have hp:= plum k i -- switch
     change coef _ _= -(bit i k * coef _ _); rw [Grass.read,mul_one]; rcases plum i k with ha|ha
     · rw [ha] at h; rw [bit,ha,Grass.read]; exact h.symm
     rw [ha,map_neg,map_neg,map_neg] at h; rw [bit,ha,map_neg,Grass.read]; exact (neg_injective h).symm.trans (neg_neg _).symm -- maps signs?
   rw [show grasp (mono x) i k=0 from ?_,neg_zero]; swap; · simp [grasp,Grass.read_other (tag i k) x (Ne.symm he)]
   by_cases hr:r∈x; swap; · change coef _ (vary _ (vary r _))= _; rw [absent r x hr,map_zero,map_zero]
   change coef _ (vary l (vary r _))= _; by_cases hl:l∈x; swap; · rw [show vary l (vary r (mono x))=-(vary r (vary l (mono x))) from CliffordAlgebra.contractLeft_comm ..,absent l x hl]; simp
   have ht : 2<x.card := lt_of_eq_of_lt (show 2=(tag i k).card from Eq.symm (by simp [tag])) (card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨by simp only [tag,insert_subset_iff, singleton_subset_iff]; exact ⟨hl,hr⟩,Ne.symm he⟩))
   exact spectrum (drop_degree _ l (lowers r x)) ∅ (by simp only [card_empty]; omega)

lemma hessian (i k : A)(x : Dirac A):
    coef ∅ (vary (.inl k) (vary (.inr i) x))= - (grasp x i k):=by
  rw [← write x]; simp_rw [grasp,Matrix.of_apply] -- use lemma unfold later
  simp only [map_sum,map_smul,mono_hessian,grasp, Matrix.of_apply,smul_eq_mul,mul_sum]; rw [← sum_neg_distrib]; apply sum_congr rfl; intro j _; ring
end any

variable (i : Flavor N) (X : Grid c → EvenA c N)

lemma quadr (r k: Lat.Row c) : Run.negQuadratic (Cove.light _ ∘ X) (r,i) (k,i)= High.PrismT.fumes i (X 1) r k:=by
  unfold Run.negQuadratic; rw [hessian]; change - -(grasp _ _ _)/mud (X 1)=(mud (X 1))⁻¹ * grasp _ _ _; rw [neg_neg, div_eq_mul_inv, mul_comm]; rfl

lemma indistinguishable (x : EvenA c N) (h:Patron.Fit x) (j : Flavor N) : meter i x=meter j x ∧ fumes i x=fumes j x:=by
  have hl : ∀ (a b:Lat.Row c), meter i x a b=meter j x a b :=by
    intro a b; change grasp x.val (a,i) (b,i)= _; rw [legal x h j,copies,Matrix.blockDiagonal_apply, if_pos rfl]; rfl
  exact ⟨Matrix.ext hl,congr_arg (fun p:Sheet c=>(mud x)⁻¹ • p) (Matrix.ext hl)⟩
end YM.Massive.Reading
#print axioms YM.Massive.Reading.quadr
