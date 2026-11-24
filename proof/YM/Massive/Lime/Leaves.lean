import YM.Massive.Lime.Tissue
import YM.Push.ABSOLUTE_SUMS.Copies

/-!
# Writing exact additive powers in the Euler style and undoing enhancement

Given a perturbing E exponent term (`off`), replace its exponential by an
infinite product of `1 + ` terms. Each new term is a perfectly homogeneous
monomial in `off`, itself at small Woven price. That is on its indicator.
Avoid any need for denominators or positivity on the failed supports: this
Euler partitioning step keeps *exactly the same support* and regular mask,
whatever the power. The `Tree` words index the countably many terms.
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lime
open NormedSpace Massive.Log
open Function Filter Lattice Wilson RG Source Next.Foundations Cove Send Stew Lat
open Push.AbsoluteSums Footprint Push.Local Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
abbrev Tw := List ℕ
-- true monetary price per mark
noncomputable def off {p:Side}{N:ℕ} (f:Grid p→EvenA p N) : Tw→Grid p→EvenA p N
  | []=>f
  | n::l=> (-Massive.Log.c (n+2)) • (off f l)^(n+2)
def digit : Tw → ℕ
 | [] => 1
 | n::l=> (n+2)* digit l
noncomputable def cost (w:ℝ) : Tw → ℝ
  | []=> w
  | n::l=> 4⁻¹*(1/2)^n * cost w l
lemma digit_pos (n:Tw):0<digit n:=by induction n with|nil=>exact Nat.zero_lt_one|cons n l ih=>exact Nat.mul_pos (by omega) ih
lemma digit_grew (n l): 2 ≤ digit (n::l) := le_trans (b:=2*1) (Nat.le_of_eq (by omega)) (Nat.mul_le_mul (by omega) (digit_pos l))
lemma cost_nn {w:ℝ}(hw:0≤w)(x:Tw):0≤cost w x:=by induction x with |nil=> exact hw|cons n l ih=> exact mul_nonneg (by positivity) ih
lemma cost_le {w:ℝ}(hw:0≤w)(x:Tw): cost w x ≤ w :=by
    induction x with
    | nil=> exact le_rfl
    | cons n l ih=> apply le_trans _ ih; exact mul_le_of_le_one_left (cost_nn hw _) ((mul_le_one₀ (by norm_num) (by positivity : (0:ℝ)≤ (1/2:ℝ)^n) (pow_le_one₀ (by norm_num) (by norm_num))))
-- Sum over list length grains.
lemma ledger {w:ℝ}(hw:0≤w):SumBudget (cost w) (2*w):=by
    have hf (l): SumBudget (fun n=>cost w (n::l)) ((1/2:ℝ)*cost w l):=by
      convert! budget_scale (show 0 ≤ 4⁻¹ * cost w l from mul_nonneg (by norm_num) (cost_nn hw _)) (show SumBudget (fun n:ℕ=> (1/2:ℝ)^n) 2 from ⟨fun _=>by positivity,summable_geometric_two,tsum_geometric_two.le⟩) using 1
      · funext p; rw [cost]; ring
      ring
    apply budget_loosen (budget_degrees List.length (cost_nn hw) hw (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1) ?_) (le_of_eq (by ring))
    intro k s hx; induction k generalizing s with
    | zero=> rw [pow_zero,mul_one]; apply le_trans (b:=∑ i∈ {([]:Tw)},cost w i) (sum_le_sum_of_subset_of_nonneg (fun i hi=> mem_singleton.mpr (List.eq_nil_of_length_eq_zero (hx i hi))) (fun i _ _=> cost_nn hw i)); rw [sum_singleton]; rfl
    | succ k ih=>
      let t:Finset Tw:=s.image List.tail; let u:=s.image (fun i=> i.headD 0)
      have hT:(∑ z∈t,cost w z) ≤ w*(1/2)^k:= ih t (fun z hz=>by obtain ⟨i,hi,rfl⟩:= mem_image.mp hz; simp [hx i hi])
      calc
       _ ≤ ∑ z∈ t.biUnion (fun i=>u.image (fun n=>n::i)), cost w z:=sum_le_sum_of_subset_of_nonneg (fun z hz=>by
         have hL:= hx z hz; apply mem_biUnion.mpr; refine ⟨z.tail,mem_image_of_mem _ hz, mem_image.mpr ⟨z.headD 0, mem_image_of_mem _ hz,?_⟩⟩
         cases z; · cases hL
         rfl)
         (fun z _ _=>cost_nn hw z)
       _ = ∑ z∈t,∑ k∈u,cost w (k::z):=by
          rw [sum_biUnion]; apply sum_congr rfl; intro z h; rw [sum_image]; exact fun x hx y hy he=>by simpa using he
          intro i _ j _ he; apply Finset.disjoint_left.mpr; intro z hz h; obtain ⟨n,_,hn⟩:=mem_image.mp hz; obtain ⟨m,_,hm⟩:=mem_image.mp h; exact he (List.cons.inj (hn.trans hm.symm)).2
       _ ≤ (1/2)*(w*(1/2)^k):=(sum_le_sum (fun i _=> budget_sum (hf i) u)).trans (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hT (by norm_num))
       _ =_:=by rw [pow_succ]; ring
lemma trees {A:Type*}[NormedAddCommGroup A][CompleteSpace A](f:A→A)(g:Tw→A) (hx:Summable g)(hq:Summable (fun i=>f (g i))) (heq:∀ s, ∑' i:ℕ,g (i::s)=g s-f (g s)): HasSum (fun s=> f (g s)) (g []) :=by
    let p : Tw×ℕ → Tw:=fun i=>i.2::i.1
    have hN:Function.Injective p:=by rintro ⟨a,b⟩ ⟨c,d⟩ hv; exact Prod.ext (List.cons.inj hv).2 (List.cons.inj hv).1
    have hh : Summable (fun i=>g (p i)):= hx.comp_injective hN
    have hy := hx.tsum_eq_add_tsum_ite ([]:Tw); let Q(n:Tw):=if n=[] then 0 else g n
    have hP : Function.support Q ⊆ Set.range p :=by
         intro q h₁; cases q with | cons l s=> exact ⟨(s,l),rfl⟩| nil=> exact (h₁ (if_pos rfl)).elim
    have he':(∑' i:Tw,Q i)= (∑' i:Tw,(g i-f (g i))):=by
         rw [← Function.Injective.tsum_eq hN hP, show (fun i=>Q (p i))=(fun i=>g (p i)) from funext (fun i=>if_neg (show ¬ p i=[] from List.cons_ne_nil i.2 i.1)), hh.tsum_prod]
         exact tsum_congr (fun i=> heq i)
    change (∑' i,g i)=g []+(∑' i,Q i) at hy
    rw [he',hx.tsum_sub hq] at hy
    change HasSum (fun i=> f (g i)) (g [])
    have hz : (∑' i,f (g i))=g []:= add_left_cancel (a:=(∑' i,g i)-(∑' i,f (g i))) (by rw [sub_add_cancel]; rw [add_comm]; exact hy)
    exact hz ▸ hq.hasSum
section
variable {p:Side}{B:BudgetPoint}{X:Support p}{o:Site p}{N:ℕ}{w u t:ℝ}{f:Grid p→ EvenA p N}{V:Grid p}
variable (h: Woven o X B t f w)(he:1≤t)(hp:w≤1/8)(hU:2^B.order*w ≤1/4)
include h
lemma powPay (hv:0 ≤ t)(i:ℕ) : Woven o X B t (f^(i+1)) ((2^B.order*w)^i*w):=by
   induction i with
   | zero=> simpa only [Nat.zero_add,pow_zero,pow_one,one_mul] using h
   | succ i ih=> rw [pow_succ f, pow_succ (2^B.order*w)]; refine (mullP ih h hv).stretches (Subset.refl _) (le_of_eq ?_); ring
include he hU
lemma tenure (s:Tw): Woven o X B t (off f s) (cost w s):=by
   induction s with
   | nil=> exact h
   | cons i l ih=>
      let e:=2^B.order*cost w l; have hu:= ((mul_le_mul_of_nonneg_left (cost_le h.travel l) (by positivity : (0:ℝ)≤2^B.order)).trans hU); have hz:0≤ e:= by unfold e; positivity [ih.travel]
      refine ((powPay ih (zero_le_one.trans he) (i+1)).byScalar _).stretches (Finset.Subset.refl _) ?_
      change ‖-c (i+2)‖*(e^(i+1)*_)≤ _; rw [norm_neg]; refine (mul_le_of_le_one_left (mul_nonneg (pow_nonneg hz _) (ih.travel)) (priced _)).trans ?_; refine mul_le_mul_of_nonneg_right ?_ ih.travel
      rw [pow_succ,mul_comm (e^i) e]; -- next e^i
      exact mul_le_mul (by rwa [← one_div]) (pow_le_pow_left₀ hz (hu.trans (by norm_num)) _) (pow_nonneg hz _) (by norm_num)
include hp
lemma logSpend (s:Tw): Woven o X B t (Massive.Log.log ∘ off f s) (2^B.order*cInv B.order*cost w s):= logP (tenure h he hU s) he ((cost_le h.travel _).trans hp)
lemma mayer (hv:Healthy B.threshold X V)(s:Tw): NormedSpace.exp ((log ∘ off f s) V)=1+off f s V:=by
    apply cancel; exact ((sen_norm (o:=o) t (off f s V) he).trans ((tenure h he hU s).sizeU V hv)).trans ((cost_le h.travel s).trans (hp.trans (by norm_num)))
-- no locality outside original. exact at every point IN mask. including
-- parameter values guaranteeing those Woven prices.
variable (hv:Healthy B.threshold X V)
include hv
set_option maxHeartbeats 700000 in
lemma expand : HasSum (fun s:Tw=> log (off f s V)) (f V):=by
    let c₁:=2^B.order*cInv B.order; have hc:0 ≤ c₁:=by unfold c₁; have he:=cInv_head B.order; positivity
    let g(s):=off f s V
    have hL(i): ‖g i‖ ≤ cost w i:= (sen_norm (o:=o) t _ he).trans ((tenure h he hU i).sizeU V hv)
    have ht(i): ‖log (g i)‖ ≤ c₁*cost w i:= (sen_norm (o:=o) t _ he).trans ((logSpend h he hp hU i).sizeU V hv)
    have hx : Summable g:= .of_norm_bounded ((ledger h.travel).2.1) hL
    have hq: Summable (log ∘ g):= .of_norm_bounded ((budget_scale hc (ledger h.travel)).2.1) ht
    have heq(s): ∑' i:ℕ,g (i::s)=g s-log (g s):=by
         let v (i:ℕ):= Massive.Log.c i • (g s)^i; have h' : Summable v := (afford ((hL _).trans_lt ((cost_le h.travel _).trans_lt (hp.trans_lt (by norm_num : (1/8:ℝ)<1))))).of_norm
         have hk: g s+ (∑' i:ℕ,v (i+2))=log (g s):=by
           rw [log_eq]; convert! h'.sum_add_tsum_nat_add 2 using 1; simp [v,Finset.sum_range_succ,Massive.Log.c]
         rw [show log (g s)=_ from hk.symm]; calc
             _= -(∑' i:ℕ,v (i+2)):=by rw [←tsum_neg]; apply tsum_congr; intro i; unfold g; simp only [off,Pi.smul_apply,Pi.pow_apply,neg_smul]; rfl
             _=_:=by abel
    apply trees log g hx hq heq
omit hv he h hU hp
lemma scaled (s:Tw)(z:ℂ)(f:Grid p→EvenA p N):off (z • f) s= z^digit s • off f s:=by
   induction s with
   | nil=> simp [off,digit]
   | cons n l ih=> funext x; simp only [off,ih,Pi.smul_apply,Pi.pow_apply,digit]; rw [smul_pow,smul_comm,← pow_mul, Nat.mul_comm (digit l) (n+2)]
end
end YM.QCD.Lime
#print axioms YM.QCD.Lime.expand
