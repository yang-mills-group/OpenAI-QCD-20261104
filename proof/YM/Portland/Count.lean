import YM.Portland.Dose
import YM.QCD.Creek.Cost
/-! Spin core derivatives sum-price via blocks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ovule
open Function Finset NormedSpace Creek
open scoped BigOperators Topology ContDiff Classical
variable {A I J:Type*}[Fintype A][Fintype I]
noncomputable def bins (A:Type*)[Fintype A](x:Alg A):ℕ→ℝ
|0=> ‖core A x‖
|n+1=> ∑ i:A,bins A (vary i x) n
local notation "Ic"=> core _
variable {m n:ℕ} {w:ℝ} (i:A)(x y:Alg A)
lemma r_zero (n:ℕ): bins A (0:Alg A) n=0:=by induction n with|zero=>simp [bins]|succ n ih=>simp [bins,map_zero,ih]
lemma r_const (n:ℕ)(z:ℂ):bins A (z • x) n = ‖z‖*bins A x n:=by induction n generalizing x with|zero=> simp only [bins,map_smul,norm_smul] |succ n ih=> simp only [bins,map_smul,ih,mul_sum]
lemma r_neg (n:ℕ):bins A (-x) n=bins A x n:=by simpa using r_const x n (-1)
lemma r_nn (n:ℕ): 0 ≤ bins A x n:=by induction n generalizing x with|zero=>exact norm_nonneg _|succ n ih=> exact Finset.sum_nonneg fun i h=>ih _
lemma r_tri (n:ℕ) : bins A (x+y) n≤bins A x n+bins A y n:=by induction n generalizing x y with|zero=>simp only [bins,map_add]; exact norm_add_le  _ _|succ n ih=> simp only [bins,map_add, ← sum_add_distrib]; exact sum_le_sum fun i _=>ih ..
lemma r_sum (t:Finset J)(f:J→Alg A)(n:ℕ): bins A (∑ i∈t,f i) n≤∑ i∈t,bins A (f i) n:=by
    induction t using Finset.induction_on with|empty=> rw [sum_empty,sum_empty,r_zero]|insert i t hi ih=>rw[sum_insert hi,sum_insert hi]; exact (r_tri ..).trans (add_le_add_right ih _)
lemma r_spt {s:Finset A}(h:i∉s):vary i (mono s)=0:=by
    have he(z:List A)(h:i∉ z): vary i (z.map atom).prod=0:=by
      induction z with|nil=> simp [vary_one]|cons k L ih=> simp only [List.mem_cons,not_or] at h; simp only [List.map_cons,List.prod_cons,vary_mul, vary_off _ _ h.1, ih h.2,mul_zero,zero_mul,add_zero]
    obtain ⟨u,-,hp,H⟩:= expression s; have hg:i∉List.ofFn u:=by simpa [(hp i)] using h
    rw [H]; simpa only [List.map_ofFn] using he _ hg
lemma wings (s:Finset A)(n:ℕ): bins A (mono s) n=if s.card=n then (n.factorial:ℝ) else 0:=by
    induction n generalizing s with
    | zero=>
        by_cases h:s=∅; · subst s; simp [bins]
        change ‖coef ∅ _‖= _; rw [read_other _ _ (Ne.symm h)]; simp [h] -- metavars
    | succ n ih=>
        have hS: bins A (mono s) (n+1)=∑ i∈s,bins A (vary i (mono s)) n:=by rw [bins]; exact (Finset.sum_subset (subset_univ s) fun i _ h=>by rw [r_spt i h,r_zero]).symm
        rw [hS]; have hx(i:A)(h:i∈s): bins A (vary i (mono s)) n=(if s.card=n+1 then (n.factorial:ℝ) else 0):=by
            let t:=s.erase i
            have hg:i∉t:= by simp [t]
            have h' : Disjoint ({i}:Finset A) t:=by simp [hg]
            have he:= mono_mul_sign _ _ h'; rw [disjUnion_eq_union,singleton_union,mono_single,show insert i t=s from insert_erase h] at he
            have hy: vary i (atom i*mono t)= mono t:=by rw [vary_mul,vary_self,one_mul,r_spt i hg,mul_zero,add_zero]
            have hC:t.card+1=s.card:= card_erase_add_one h
            rw [← ih t|>.trans (show (if t.card=n then (n.factorial:ℝ) else 0)=(if s.card=n+1 then (n.factorial:ℝ) else 0) from if_congr (by omega) rfl rfl)]
            rcases he with he|he <;> rw [he] at hy; · rw [hy]
            rw [map_neg] at hy; rw [←hy,r_neg]
        rw [sum_congr rfl hx]; split_ifs with h <;> simp [*,Nat.factorial_succ] -- syntax
noncomputable def priceD (x:Alg A)(n:ℕ):ℝ:= ∑ i∈univ.filter (fun i:Finset A=>i.card=n), ‖coef i x‖
lemma prices (n:ℕ): bins A x n≤(n.factorial:ℝ)*priceD x n:=by
    nth_rw 1 [←write x]; refine (r_sum ..).trans ?_
    simp_rw [r_const,wings, mul_ite,mul_zero]; unfold priceD; rw [mul_sum,sum_filter]; exact le_of_eq (sum_congr rfl fun i _=>by rw [mul_comm]) -- orientation
lemma peak (p:A→ℂ)(hp:∀ i,‖p i‖≤1)(n:ℕ):bins A (spr p x) n≤bins A x (n+1):=by rw [turns]; nth_rw 1 [show bins A x (n+1)= ∑ j:A,bins A (vary j x) n from by rw[bins]]; apply (r_sum ..).trans (sum_le_sum fun i _=>?_); rw [r_const]; exact mul_le_of_le_one_left (r_nn ..) (hp _) -- named arg pattern
lemma normBase(n:ℕ)(h: m≤n):0 ≤ priceD x m:= Finset.sum_nonneg fun _ _=>norm_nonneg _
lemma oneB (n:ℕ) : bins A (vary i x) n≤bins A x (n+1):= single_le_sum (s:=univ) (f:=fun i=>bins A (vary i x) n) (fun _ _=> r_nn ..) (mem_univ i)
lemma subset_ship (f:I ↪ A)(n:ℕ): (∑ i:I,bins A (vary (f i) x) n)≤bins A x (n+1):=by
    rw [show (∑ i:I,bins A (vary (f i) x) n)=∑ i∈ univ.map f, bins A (vary i x) n from (sum_map univ f (fun i=>bins A (vary i x) n)).symm,show bins A x (n+1) =∑ i:A,bins A (vary i x) n from by rw [bins]]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=>r_nn ..
-- prices from Env. normalize.
end YM.QCD.Grass.Ovule
#print axioms YM.QCD.Grass.Ovule.prices
#print axioms YM.QCD.Grass.Ovule.peak
