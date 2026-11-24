import YM.Massive.Brush.Floors
import YM.Massive.PCAC.Ideal
import YM.Massive.Mass.Kernels
/-! Arithmetic and support in grade 4 for the contact Lap.
Independent of lattice. In the general multi-scale E-bias a local error after the
first bias may be encoded by repeated uses of these, though no bound on its
propagated new factors is here. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ward
open Function Finset Module NormedSpace
open scoped BigOperators Topology Matrix Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C]
namespace Loft
open Stew
lemma traceT [DecidableEq A](x:Dirac A): traceP x= grasp x:=by ext i j; exact (show -(coef ∅ (vary (Sum.inl j) (vary (Sum.inr i) x)))=_ from (congr_arg (-·) (Massive.Reading.hessian i j x)).trans (neg_neg _))
lemma basic (X:Dirac A)(u:ℂ): traceP (u • X)=u • traceP X:=by ext i j; simp [traceP]
lemma minus (x y: Dirac A): traceP (x-y)=traceP x-traceP y:=by apply eq_sub_of_add_eq; rw [←trace_add, sub_add_cancel]
lemma trace0 : traceP (0:Dirac A)=0:=by ext i j; simp [traceP]
lemma rot (D:Sour A) : traceP (form D)=D:=by rw [traceT,gravid]
lemma gaussian (D M:Sour A)(h:Matrix.trace (D*M)=0) : traceP (lap D (gauss M))= M * D * M:=by
   rw [lap_gauss,h,zero_smul,sub_zero]; let Z:=M*D*M; let W:= form Z; have hv:gauss M*W-W∈ floor (Pairs A) 3:=by
       have h₁:= exhausted (wage (form_two M) le_rfl); have hT:= pays h₁ (wage (form_two Z) le_rfl); change exp (form M) * W - W∈ _; rw [show exp _ * W-W=(exp (form M)-1)*W from (by rw [sub_mul,one_mul])]; exact reduce hT (by decide)
   exact (unquote _ _ hv).trans (rot _)
-- Second derivative read on grade-zero body.
lemma ray_body (D:Sour A)(z:Dirac A)(h:coef ∅ z=0) (hk:Plus z)(hT: panel 2 z=form D) : z-form D ∈ floor (Pairs A) 4:=by -- D binder
   refine test.mpr fun s hs=>?_ ; rw [map_sub, sub_eq_zero]; have he(s':Finset (Pairs A))(ht:s'.card≠2): coef s' (form D)=0:= spectrum (form_two D) _ ht
   by_cases hp:s.card=0; · rw [card_eq_zero.mp hp,h, he ∅ (by simp)]
   by_cases ht:s.card=2; · rw [← hT,angel,if_pos ht]
   let Y:Cove.Patio (Pairs A):=⟨z,hk⟩; rw [he s ht]; exact Stew.measured s (by omega) Y
-- no-card extraction. Cost bound as TRUE uniform l1 of all places.
abbrev charge (x:Alg A):ℝ:=‖Stew.panel 4 x‖
lemma ride (i:A)(s:Finset A)(he:i∈s): vary i (mono s)=mono (s.erase i) ∨ vary i (mono s)= -(mono (s.erase i)):=by
    classical
    let t:=s.erase i; have ht:i∉t:=by simp [t]
    have hb:Disjoint {i} t:=by simp [ht]
    have hx: vary i (atom i*mono t)=mono t:=by rw [vary_mul,vary_self,Massive.Reading.absent i t ht,mul_zero,one_mul,add_zero];
    have hk:= mono_mul_sign _ _ hb; rw [disjUnion_eq_union,singleton_union,mono_single,show insert i t=s from insert_erase he] at hk; rcases hk with hx'| hx'; rw [hx'] at hx; exact Or.inl hx; rw [hx',map_neg] at hx; exact Or.inr (neg_eq_iff_eq_neg.mp hx)
-- counterterm full-charge chooses ALL slots at most 4^4. prove registered general k-order
noncomputable def slate (x:Alg A) : ℕ → ℝ | 0=> ‖coef ∅ x‖ | k+1=> ∑ i:A, slate (vary i x) k
lemma slate_sub (x y:Alg A)(n:ℕ) : slate (x+y) n≤ slate x n+slate y n:=by
    induction n generalizing x y with | zero=> unfold slate; rw [map_add]; exact norm_add_le .. | succ n ih=> rw [slate,slate,slate,← sum_add_distrib]; exact sum_le_sum fun i _=> (congr_arg (fun x=>slate x n) (map_add ..)).trans_le (ih ..) -- equality?
lemma slate_null(n:ℕ): slate (0:Alg A) n=0:=by induction n with | zero=> simp [slate] | succ n ih=> unfold slate; simp only [map_zero,ih,sum_const_zero]
lemma slate_scale (x:Alg A)(n:ℕ)(s:ℂ): slate (s • x) n=‖s‖*slate x n:=by induction n generalizing x with|zero=>simp [slate]|succ n ih=> rw [slate,slate,mul_sum]; simp_rw [map_smul]; exact sum_congr rfl fun i _=> ih _
lemma slate_neg (x:Alg A)(n:ℕ): slate (-x) n=slate x n:=by convert slate_scale x n (-1) using 1 <;> simp
lemma slate_price (x: Finset A)(n:ℕ): slate (mono x) n= if x.card=n then (n.factorial:ℝ) else 0:=by
   induction n generalizing x with
   | zero=> by_cases he:x=∅; · subst x; rw [slate,Grass.read]; simp
            rw [slate, read_other _ _ (Ne.symm he), if_neg (fun h=>he (card_eq_zero.mp h)),norm_zero]
   | succ n ih=>
       rw [slate]; have hx(i:A)(he:i∈x): slate (vary i (mono x)) n= if x.card=n+1 then (n.factorial:ℝ) else 0:=by
           have h: (x.erase i).card=n ↔ x.card=n+1:=by rw [card_erase_of_mem he]; have hh:=card_pos.mpr ⟨i,he⟩; omega
           rcases ride i x he with h'|h' <;> simp [h',slate_neg, ih,h]
       rw [← sum_subset (s₁:=x) (s₂:=univ) (by simp) (fun i _ h=>?_)] -- name
       · rw [sum_congr rfl (fun i hi=> hx i hi),sum_const]; split_ifs with h; · rw [h,nsmul_eq_mul,Nat.factorial_succ,Nat.cast_mul]
         simp
       rw [Massive.Reading.absent i x h, slate_null]
lemma slate_cost (x:Alg A)(n:ℕ): slate x n ≤ ↑(n.factorial) * ‖panel n x‖:=by
   let f(i:Finset A):= coef i x • mono i; have h(s:Finset (Finset A)): slate (∑ i∈s,f i) n≤∑ i∈s,slate (f i) n:=by
       induction s using Finset.induction_on with| empty=>simp [slate_null]| @insert i s h ih=> rw [sum_insert h,sum_insert h]; exact (slate_sub _ _ _).trans (add_le_add (le_refl _) ih)
   apply le_trans _ (le_of_eq ?_) (b:= ∑ i:Finset A,slate (f i) n)
   · conv_lhs=> rw [← write x]
     exact h univ -- indentation
   rw [Grass.norm_def,mul_sum]; apply sum_congr rfl; intro i _; unfold f; rw [slate_scale,angel,slate_price]; split <;> simp [mul_comm];
end Loft
end YM.QCD.Grass.Ward
#print axioms YM.QCD.Grass.Ward.Loft.gaussian
#print axioms YM.QCD.Grass.Ward.Loft.slate_cost
