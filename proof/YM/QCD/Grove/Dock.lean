import YM.QCD.Grove.Stone
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type*}[Fintype I][Fintype J]{c f:Side}{N n:ℕ}
variable (g:I→V)
def held [DecidableEq V](v:V)(X:Finset I):ℕ:= #(X.filter fun i=>g i=v)
abbrev vote [DecidableEq V](v:V)(X:Finset I):ℝ:= (held g v X:ℝ)/(X.card:ℝ)
lemma income [DecidableEq V](v:V)(X:Finset I):0 ≤ vote g v X ∧ vote g v X ≤1:=by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),?_⟩
  rcases eq_empty_or_nonempty X with rfl|h; · simp [vote]
  exact (div_le_one (Nat.cast_pos.mpr (card_pos.mpr h))).2 (Nat.cast_le.mpr (card_le_card (filter_subset _ _)))
lemma board [Fintype V][DecidableEq V](X:Finset I)(hp:X.Nonempty):∑ v:V,vote g v X=1:=by
   unfold vote; rw [← sum_div,← Nat.cast_sum, show ∑ v:V, held g v X=_ from Finset.card_eq_sum_card_fiberwise (show Set.MapsTo g X ↑(univ:Finset V) from fun p _=>mem_univ _)|>.symm]; exact div_self (Nat.cast_ne_zero.mpr (card_pos.mpr hp).ne') -- check lemma
noncomputable def poker [DecidableEq V](v:V):Alg I→ₗ[ℂ]Alg I:= { toFun:=fun x=> ∑ i: Finset I,(↑(vote g v i):ℂ) • ((Grass.coef i x) • Grass.mono i), map_add':=fun x y=>by simp_rw [map_add,add_smul,smul_add,sum_add_distrib],map_smul':=fun k x=>by simp_rw [map_smul (coef _),smul_sum]; refine sum_congr rfl fun i _=>?_ ; change _ • ((k*Grass.coef i x) •_)=_; rw [mul_smul,smul_comm]; rfl }
lemma gateB [DecidableEq V](v:V)(X:Alg I)(s:Finset I): coef s (poker g v X)=(↑(vote g v s):ℂ)*coef s X:=by
    change coef s (∑ i:Finset I,(↑(vote g v i):ℂ) • _) =_; rw [map_sum,sum_eq_single s]
    · rw [map_smul,map_smul, Grass.read,smul_eq_mul,smul_eq_mul,mul_one]
    · intro i _ hi; rw [map_smul,map_smul,read_other _ _ hi.symm, smul_zero,smul_zero]
    simp
lemma loanP [DecidableEq V](v:V)(X:Finset I)(i:Alg I)(hp:∀ s,coef s i≠0→ vote g v s=vote g v X): poker g v i=(↑(vote g v X):ℂ) • i:=by
    apply (blades I).ext_elem (y:= (_:Alg I)); -- check name
    intro s; change coef s _=coef s _; rw [gateB,map_smul,smul_eq_mul]; by_cases he:coef s i=0; · rw [he]; simp
    rw [hp _ he]
lemma accentP [DecidableEq V](v:V)(X:Finset I): poker g v (mono X)=(↑(vote g v X):ℂ) • mono X:=loanP g v X (mono X) fun s hp=>congr_arg (vote g v) (not_not.mp (fun h=>hp (read_other _ _ h)))
lemma keep_plus [DecidableEq V](v:V)(x:Alg I)(hp: Plus x): Plus (poker g v x):=by
    suffices h: grade (poker g v x)=poker g v (grade x) from h.trans (congr_arg _ hp)
    rw [← write x]; simp_rw [map_sum,map_smul]; refine sum_congr rfl fun i _=>?_; rw [accentP,Grass.grade_mono,map_smul,map_smul,Grass.grade_mono,accentP,smul_comm (((-1):ℂ)^i.card)] -- exponent
lemma mono_member (i:Finset I)(S: Finset I)(h:i⊆ S): mono i ∈ region S:=by
    induction i using Finset.induction_on with
    | empty=> rw [mono_empty]; exact Subalgebra.one_mem _
    | insert i s he ih=> have hp:= mono_mul_sign {i} s (by simp [he]); rw [disjUnion_eq_union,singleton_union,mono_single] at hp; have hv : atom i*mono s∈ region S:= (region S).mul_mem (Creek.marked _ S (h (mem_insert_self ..))) (ih ((Finset.subset_insert ..).trans h)); rcases hp with hp|hp<;>rw [hp] at hv; · exact hv
                         simpa using (region S).neg_mem hv
lemma poker_mem [DecidableEq V](v:V)(x:Alg I)(S:Finset I)(h:x∈region S): poker g v x∈region S:=by
    change ∑ i:Finset I,_ ∈ region S; apply Subalgebra.sum_mem; intro i _; apply Subalgebra.smul_mem; by_cases he:i⊆ S; · exact Subalgebra.smul_mem _ (mono_member i S he) _ -- fill
    rw [ember x h i he,zero_smul]; exact Subalgebra.zero_mem _
lemma scoreB [Fintype V][DecidableEq V](x:Alg I): x= coef ∅ x • (1: Alg I)+∑ v:V,poker g v x:=by
    apply (blades I).ext_elem; intro s; change coef s _=coef s _; rw [map_add,map_smul,map_sum]; simp_rw [gateB]; rcases eq_empty_or_nonempty s with rfl|hs
    · rw [← mono_empty,Grass.read]; simp [vote]
    rw [← mono_empty,read_other _ _ (nonempty_iff_ne_empty.mp hs),smul_zero,zero_add,← sum_mul,← Complex.ofReal_sum, board g s hs,Complex.ofReal_one,one_mul]
-- all-site zeros.
lemma waiving [DecidableEq V](v:V)(U:Finset I)(he:∀ i∈U,g i≠v)(x:Alg I)(hp:x∈region U): poker g v x=0:=by
   change ∑ i:Finset I,_= 0; refine sum_eq_zero fun i _=>?_; by_cases h:i⊆ U
   · rw [show vote g v i=0 by unfold vote held; rw [show filter _ i=∅ from filter_eq_empty_iff.mpr (fun i hi=> he i (h hi))]; simp,Complex.ofReal_zero,zero_smul]
   rw [ember x hp i h,zero_smul,smul_zero]
lemma waxG (p:I→ ℝ)(x:Alg I)(s:Finset I): coef s (wscale p x)= (∏ i∈s,(p i:ℂ))*coef s x:=by
   rw [Creek.wax,map_sum,sum_eq_single s]
   · rw [map_smul,map_smul, Grass.read,smul_eq_mul,smul_eq_mul,mul_one]; exact mul_comm ..
   · intro j _ hj; rw [map_smul,map_smul,Grass.read_other _ _ hj.symm,smul_zero,smul_zero]
   simp
lemma bottled [DecidableEq V](v:V)(p:I→ℝ)(hp:∀ i,0<p i)(x:Alg I): load p (poker g v x) ≤ load p x:=by
    rw [Creek.dry p hp,Creek.dry p hp]; refine sum_le_sum fun i _=>mul_le_mul_of_nonneg_left ?_ (prod_nonneg (fun i _=>(hp i).le)); rw [gateB,norm_mul,Complex.norm_real,Real.norm_of_nonneg (income ..).1]; exact mul_le_of_le_one_left (norm_nonneg _) (income ..).2
end YM.QCD.Grove
