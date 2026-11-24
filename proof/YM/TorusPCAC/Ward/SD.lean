import YM.TorusPCAC.Finite.Step

/-!
# Pushing Grassmann equations

Conventions as in `History` and QCD. Fine density on the LEFT. Partial
integration includes any even or ODD x; the integrating block has EVEN
top. All Grassmann derivatives here are *left* derivatives.
-/

set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Ward
open QCD QCD.Grass Finite Finset Function
open scoped Matrix Topology BigOperators

variable {I J A B : Type*} [Fintype I] [Fintype J] [Fintype A] [Fintype B]

lemma probe_ix [DecidableEq I] (i j : I) : probe i (thetaBasis I j)=if i=j then 1 else 0 := by
  by_cases h : i=j
  · subst j; simp [probe]
  simp [probe,h]

lemma anti_vary (x : Alg I) (i j : I) : vary i (vary j x) = -vary j (vary i x) := by
  have hh (l : List I) : vary i (vary j (l.map atom).prod) = -vary j (vary i (l.map atom).prod) := by
    induction l with
    | nil => simp [vary_one]
    | cons a l ih => simp only [List.map_cons,List.prod_cons,vary_head,map_sub,map_smul,ih,mul_neg]; abel
  have he (s : Finset I) : vary i (vary j (mono s)) = -vary j (vary i (mono s)) := by
    obtain ⟨f,-,-,e⟩:=expression s; rw [e]; simpa only [List.map_ofFn] using hh (List.ofFn f)
  rw [← write x]; simp only [map_sum,map_smul,he,smul_neg,sum_neg_distrib]

lemma embed_held (f : I → J) (x : Alg I) (i : J) (H : ∀ j, i≠f j) : vary i (embed f x)=0 := by
  have hh (l : List I) : vary i (embed f (l.map atom).prod)=0 := by
    induction l <;> simp [*,vary_one,vary_mul,vary_off _ _ (H _)]
  have hp (s : Finset I) : vary i (embed f (mono s))=0:=by
    obtain ⟨w,-,-,he⟩:=expression s; rw [he]; simpa only [List.map_ofFn] using hh (List.ofFn w)
  rw [← write x]; simp only [map_sum,map_smul,hp,smul_zero,sum_const_zero]

def warm (B : Type*) : Pairs A → Pairs (A ⊕ B) := Sum.map Sum.inl Sum.inl
def cool (A : Type*) : Pairs B → Pairs (A ⊕ B) := Sum.map Sum.inr Sum.inr

variable (A B) in lemma cool_silent (i : Pairs B) (x : Dirac A) : vary (cool A i) (near A B x)=0 :=
  embed_held (warm B) x _ (fun j=>by cases j <;> cases i <;> simp [cool,warm])

variable (A B) in lemma cool_survives (i : Pairs B) (x : Dirac B) : vary (cool A i) (far A B x)=far A B (vary i x):=
  Grass.survives (X:=Pairs B) (Y:=Pairs (A⊕B)) (f:=cool A) (Sum.map_injective.mpr ⟨Sum.inr_injective,Sum.inr_injective⟩) i x

variable (A B) in lemma warm_silent (i : Pairs A) (x : Dirac B) : vary (warm B i) (far A B x)=0 :=
  embed_held (cool A) x _ (fun j=>by cases j <;> cases i <;> simp [cool,warm])

variable (A B) in lemma warm_survives (i : Pairs A) (x : Dirac A) : vary (warm B i) (near A B x)=near A B (vary i x):=
  Grass.survives (X:=Pairs A) (Y:=Pairs (A⊕B)) (f:=warm B) (Sum.map_injective.mpr ⟨Sum.inl_injective,Sum.inl_injective⟩) i x

lemma marg_cools (i : Pairs B) (x : Dirac (A⊕B)) : marginal A B (vary (cool A i) x) = vary i (marginal A B x) := by
  have h (u : Dirac A) (v : Dirac B) : marginal A B (vary (cool A i) (near A B u*far A B v)) = vary i (marginal A B (near A B u*far A B v)):=by
    rw [vary_mul,cool_silent,cool_survives, zero_mul,zero_add,
      show grade (near A B u)=near A B (grade u) from pass_grade ..,margins,margins,Finite.vol_grade,map_smul]
  have ht (s : Finset (Pairs (A⊕B))) : marginal A B (vary (cool A i) (mono s))=vary i (marginal A B (mono s)):=by
    obtain ⟨u,v,hp|hp⟩:=split_mono A B s <;> simp only [hp,h,map_neg]
  rw [← write x]; simp only [map_sum,map_smul,ht]

lemma marg_kills (i : Pairs A) (x : Dirac (A⊕B)) : marginal A B (vary (warm B i) x)=0 := by
  apply (perfect B).injective; apply LinearMap.ext; intro y
  have hh := integration (x*far A B y) (warm B i); rw [vary_mul,warm_silent,mul_zero,add_zero] at hh
  rw [perfect_apply, perfect_apply,zero_mul,map_zero,marginal_test,hh]

lemma marg_atom (i : Pairs B) (x : Dirac (A⊕B)) : marginal A B (atom (cool A i)*x) = atom i * marginal A B x := by
  rw [atom,line_across (A:=Pairs (A⊕B)) _ x]; unfold Grass.atom; rw [line_across (A:=Pairs B),Finite.marginal_grade];
  change marginal A B (grade x * atom (cool A i))=marginal A B (grade x)*atom i
  rw [← show far A B (atom i)=atom (cool A i) from embed_atom (cool A) i, pullout]

lemma vary_maps (M : Matrix I J ℂ) (j : J) (x : Alg I) : vary j (changeVars M x) = ∑ i, M i j • changeVars M (vary i x) := by
  classical
  induction x using ExteriorAlgebra.induction with
  | algebraMap s => simp [Algebra.algebraMap_eq_smul_one, vary_one]
  | ι u =>
    have he (i : I) : vary j (changeVars M (atom i)) = ∑ k, M k j • changeVars M (vary k (atom i)) := by
      rw [change_atom,map_sum]; simp only [map_smul, vary_atom,probe_ix,map_one]; simp [ite_smul,smul_ite]
    rw [line_atoms]; simp_rw [map_sum,map_smul,smul_sum,he,smul_sum]; rw [sum_comm (s:=univ) (t:=univ) (f:=fun (k i : I)=> M k j • u i • (changeVars M) (vary k (atom i)))]; simp_rw [smul_comm (M _ _)]
  | add x y hx hy => simp only [map_add,hx,hy,smul_add,sum_add_distrib]
  | mul x y hx hy =>
    simp only [vary_mul,map_mul,map_add, hx,hy]; rw [show grade (changeVars M x)=changeVars M (grade x) from Grass.exterior_parity ..]; simp only [smul_add,sum_add_distrib,sum_mul,mul_sum,mul_smul_comm,smul_mul_assoc]
end YM.TorusPCAC.Ward
