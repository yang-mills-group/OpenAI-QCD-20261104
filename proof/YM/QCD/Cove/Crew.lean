import YM.QCD.Cove.Post
/-! # track simultaneous endpoint moments along with all reads -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Grass Creek NormedSpace Finset Function
open scoped Classical Topology ContDiff BigOperators
variable {A B C ι: Type*} [Fintype A][Fintype B]
variable {U:Finset A}{X: Finset B}
lemma effects (F:Alg A→ₐ[ℂ] Alg B)(h:∀ i∈U,F (atom i)∈ region X)(x:Alg A)(ht:x∈region U): F x∈region X:=by
  obtain ⟨u,rfl⟩:=ht; let v:↥U→A:=(↑); change F (Grass.embed v u)∈region X
  have he(l:List ↥U): F (embed v (l.map atom).prod)∈region X:=by
    induction l with
    | nil=> simp
    | cons i l ih=> simp only [List.map_cons,List.prod_cons,map_mul,embed_atom]; exact Subalgebra.mul_mem _ (h _ i.property) ih
  rw [← write u,map_sum,map_sum]; refine Subalgebra.sum_mem _ (fun i _=> ?_)
  rw [map_smul,map_smul]; refine Subalgebra.smul_mem _ ?_ _; obtain ⟨w,-,-,hw⟩:=expression i; rw [hw]; simpa only [List.map_ofFn] using he (List.ofFn w)
lemma ember (x: Alg A)(hx:x∈region U)(s:Finset A)(h: ¬ s⊆ U): coef s x=0:=by
  obtain ⟨y,rfl⟩:=hx; let v : ↥U↪ A:=Function.Embedding.subtype _
  change coef s (embed v y)=0; rw [← write y,map_sum,map_sum]; apply sum_eq_zero; intro i _; rw [map_smul,map_smul]; have hp:s≠ i.map v:= by intro he; subst s; apply h; rintro x hx; obtain ⟨u,hu,rfl⟩:= mem_map.mp hx; exact u.property
  rcases embed_blade v i with h|h <;> rw [h] <;> simp [read_other _ _ hp]
lemma load_zero (f:A→ℝ):load f (0:Alg A)=0:=by simp [load,wscale]
lemma load_one (f:A→ℝ): load f (1:Alg A)=1:=by simp [load,wscale]
lemma load_neg (f:A→ℝ)(x:Alg A): load f (-x)=load f x:=by simp [load,wscale]
lemma ferry {g:B→ℝ}{f:A→ℝ} (F : Alg A→ₐ[ℂ] Alg B) (hf:∀ i,0<f i)(hp:∀ i∈U, load g (F (atom i)) ≤ f i)
   (x:Alg A)(ht:x∈region U): load g (F x) ≤ load f x:=by
  have he(s:Finset A)(h:s⊆ U): load g (F (mono s))≤∏ i∈s,f i:=by
    induction s using Finset.induction_on with
    | empty=> rw [mono_empty,map_one,load_one,prod_empty]
    | insert i s hi ih=>
      have hv := ih (Finset.Subset.trans (Finset.subset_insert ..) h)
      have hs i₀(x y:Alg B)(he:load g x≤ f i₀)(ht:load g y≤∏ i∈s,f i): load g (x*y) ≤ f i₀*(∏ i∈s,f i):=(load_mul _ _ _).trans (mul_le_mul he ht (load_nn _ _) (hf _).le)
      have hy:= hs i (F (atom i)) (F (mono s)) (hp _ (h (mem_insert_self ..))) hv; rw [← map_mul] at hy
      have hh:= mono_mul_sign {i} s (by simp [hi]); rw [disjUnion_eq_union,singleton_union,mono_single] at hh; rw [prod_insert hi]
      rcases hh with hh|hh <;> rw [hh] at hy; · exact hy
      rwa [map_neg,load_neg] at hy
  conv_lhs=> rw [← write x,map_sum]
  apply (load_sum ..).trans
  rw [dry f hf]; apply sum_le_sum
  intro i _; rw [map_smul,load_scale]; by_cases H:i⊆U; · rw [mul_comm _ ‖_‖]; exact mul_le_mul_of_nonneg_left (he i H) (norm_nonneg _)
  rw [ember x ht i H,norm_zero,zero_mul,mul_zero]

def regionW (f:A→ℕ) (l:ℕ) (S:Finset A):ℝ:= (1+(↑(S.sup f):ℝ))^l
def weight (f:A→ℝ)(g:A→ℕ)(l:ℕ)(s:Finset A):ℝ:=regionW g l s*∏ i∈s,f i
def camp (f:A→ℝ)(g:A→ℕ)(l:ℕ)(x:Alg A):ℝ:=∑ s,weight f g l s* ‖coef s x‖
lemma weight_nn {f:A→ℝ}(hf:0≤f)(g:A→ℕ)(l:ℕ)(s:Finset A): 0 ≤ weight f g l s :=by unfold weight; exact mul_nonneg (by unfold regionW; positivity) (prod_nonneg (fun i _=> hf i))
lemma camp_nn {f:A→ℝ}(hf : 0 ≤ f) (g:A→ℕ)(l:ℕ) (x:Alg A): 0≤camp f g l x:= by unfold camp; exact sum_nonneg fun i _=>mul_nonneg (weight_nn hf g l i) (norm_nonneg _)
lemma floors {f:A→ℝ} (hf:∀ i,0<f i)(g:A→ℕ)(l:ℕ)(x:Alg A): load f x ≤ camp f g l x:=by
  rw [dry f hf]; apply sum_le_sum; intro i _; unfold weight; gcongr; refine le_mul_of_one_le_left ?_ ?_; · exact prod_nonneg (fun k _=> (hf k).le)
  unfold regionW; exact one_le_pow₀ (by simp)
lemma camps {f:A→ℝ} (hf:∀ i,0<f i)(g:A→ℕ)(l:ℕ)(x:Alg A)(ht:x ∈ region U)(d:ℕ)(h:∀ i∈U,g i≤d): camp f g l x ≤ (1+(d:ℝ))^l*load f x:=by
  rw [dry f hf,mul_sum]; refine sum_le_sum fun i _=>?_
  by_cases hi:i⊆U; swap; · rw [ember x ht i hi,norm_zero,mul_zero,mul_zero,mul_zero]
  unfold weight regionW; have hx: i.sup g≤ d:= Finset.sup_le fun k hk=> h k (hi hk)
  rw [← mul_assoc]; have he:0 ≤ ∏ j∈i,f j:=prod_nonneg fun k _=> (hf k).le; gcongr
end YM.QCD.Cove
