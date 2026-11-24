import YM.QCD.Gas.Froof
import YM.Push.ABSOLUTE_SUMS.Distinct
/-! # Optional attachments disjoint except per catalogue. exact bank entries -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.GasP
open Push.AbsoluteSums Partition Relation Graph Ursell Finset Gas Function RG Lattice Wilson Trees
open Further.ShellBirth49.Fusing Collide
open scoped BigOperators Classical Topology
variable {ι K κ:Type*}[NormedCommRing K][NormOneClass K][NormedAlgebra ℚ K][NormedAlgebra ℝ K][CompleteSpace K]
variable {n:Side}(p d : ι→ Support n)(q:κ→ Support n) (W: Support n)(u:ι→K)(g:κ→K)
-- same site planet
open NormedSpace
local notation "X"=> Finset ι
local notation "J"=>ι⊕Support n
local notation "U"=>Finset J
-- density prior to attachment. Hard vs Soft exact
variable {T: κ→ℝ}{R: ι→ℝ}{B:ℕ}{μ ν γ a b c δ r A C s :ℝ}
-- cost for K.flag
lemma normE (x:K)(z:ℝ)(h:‖x‖≤z): ‖NormedSpace.exp x-1‖≤Real.exp z-1:=by
  let T (n:ℕ):= (n.factorial:ℝ)⁻¹ • x^n; let Z (n:ℕ):=(n.factorial:ℝ)⁻¹*z^n
  have hz:0≤z:=(norm_nonneg _).trans h; have ht : HasSum T (NormedSpace.exp x):=NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) x
  have hp : HasSum Z (Real.exp z):=by rw [Real.exp_eq_exp_ℝ]; exact exp_series_hasSum_exp' (𝕂:=ℝ) z
  rw [← hasSum_nat_add_iff' (k:=1),sum_range_one,show T 0=1 by simp [T]] at ht
  rw [← hasSum_nat_add_iff' (k:=1),sum_range_one,show Z 0=1 by simp [Z]] at hp
  have he n : ‖T n‖≤Z n:=by unfold T Z; rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤(n.factorial:ℝ)⁻¹)]; exact mul_le_mul_of_nonneg_left ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) h n)) (by positivity)
  exact le_of_tendsto_of_tendsto' ht.norm hp (fun s:Finset ℕ=> (norm_sum_le ..).trans (sum_le_sum fun k _=> he _))
lemma flash1 (x:ℝ)(hx: 0≤x)(hp:x≤1): Real.exp x-1 ≤ Real.exp 1*x:=by
   have hβ:=Real.add_one_le_exp (-x); rw [Real.exp_neg] at hβ; have hC:= mul_le_mul_of_nonneg_right hβ (Real.exp_pos x).le; rw [add_mul,inv_mul_cancel₀ (Real.exp_ne_zero x)] at hC; have hB:= mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp) hx; linarith
lemma capP (hp:∀ i,(q i).Nonempty)(hv:Trees.Ready q B T A c δ r)(ha:0 ≤ A): Ac.Hit id B (GasP.caps q T) A (c*(1-r)⁻¹):=by
   let W:= coversP q T; let p:= seatP q
   have he: Ac.Hit p B W A (c*(1-r)⁻¹):=by
      intro i; simpa only [coversP,seatP,p,W,currency,Nat.zero_le,true_and,pow_zero,mul_one] using! log_hit_tail (blocked q) q B (literal_test q hp) hv ha 0 i
   have hh i : 0≤ W i := clusters_nonneg (blocked q) hv.2.2.2.2.1 _
   intro i; refine ⟨fun j=> ?_, (hasSum_fintype _).summable,?_⟩
   · dsimp only; split; exact mul_nonneg (hat_nonneg W p hh _) (Real.exp_pos _).le; exact le_rfl
   let f (u:Support n)(a:Clusters κ):= if p a=u ∧ i∈u then W a * currency B A u else 0
   have hT (u: Support n) : Summable (f u):=by
      apply (he i).2.1.of_nonneg_of_le (fun j=> ?_) fun j=>?_
      · unfold f; split; exact mul_nonneg (hh _) (Real.exp_pos _).le; exact le_rfl
      unfold f; split
      next h=> rw [if_pos (show i∈p j from h.1 ▸ h.2),← h.1]; exact le_rfl
      next _=> exact (he i).1 j -- tactic edit
   have ht a : (if i∈a then GasP.caps q T a *currency B A a else 0)= ∑' v, f a v:=by
       split
       next h=> rw [caps, Cap,← tsum_mul_right]; refine tsum_congr fun j=>?_ ; unfold f; by_cases hh:p j=a
                · rw [if_pos hh, if_pos ⟨hh,h⟩]
                rw [if_neg hh, zero_mul, if_neg (fun h=>hh h.1)]
       next h=> simp [f,h]
   change (∑' a:Support n, if i∈a then caps q T a*currency B A a else 0 )≤_
   rw [tsum_fintype]; simp_rw [ht]; rw [← Summable.tsum_finsetSum (fun a _=> hT a)]; have hZ j: (∑ a,f a j)=if i∈p j then W j* currency B A (p j) else 0:=by
     unfold f; rw [sum_eq_single (p j)]; simp
     · intro a _ hk; rw [if_neg (fun h=> hk h.1.symm)]
     simp
   simp_rw [hZ]; exact (he i).2.2
lemma caps_one (hp:∀ i,(q i).Nonempty)(hv:Trees.Ready q B T A c δ r)(ha:0 ≤ A)(hx : c*(1-r)⁻¹ ≤ 1) (j:Support n): 0≤ GasP.caps q T j∧ GasP.caps q T j≤ 1:=by
   have hz:= hv.2.2.2.2.1; let c:= Cap (coversP q T) (seatP q) j; have he :0≤c:=hat_nonneg (coversP q T) (seatP q) (fun i=> clusters_nonneg (blocked q) hz _) _; refine ⟨he,?_⟩
   rcases eq_empty_or_nonempty j with h|⟨i,h⟩
   · subst j; unfold caps Cap; have hh i: seatP q i≠ ∅:=by obtain ⟨p,hp⟩:= hp (i.snd none); exact Nonempty.ne_empty ⟨p, mem_biUnion.mpr ⟨none,mem_univ _,hp⟩⟩
     simp_rw [if_neg (hh _)]; simp
   have hk:= budget_sum (capP q hp hv ha i) ({j}: Finset _)
   simp only [sum_singleton,id_eq, if_pos h] at hk
   exact le_trans (le_mul_of_one_le_right he (by exact Real.one_le_exp (mul_nonneg ha (show 0 ≤ (coverNumber _ _:ℝ) from Nat.cast_nonneg (coverNumber _ _))))) (hk.trans hx)

-- uptake from Broad includes tax mark. retains.
def compR (q:κ→Support n)(t:κ→ℝ)(R:ι→ℝ) : J→ℝ:= Sum.elim R (fun j=>Real.exp 1*GasP.caps q t j)
def taxed (p:ι→Support n)(R:ι→ℝ)(h:ℝ)(i:ι):= h^(p i).card*R i
def tenderW (s:U) (R:ι→ℝ) (T:κ→ℝ):ℝ:= if wagon p s then ∏ i∈s,compR q T R i else 0
lemma leaflet {K:ℝ}(hT:∀ i,(q i).Nonempty)(hp:Trees.Ready q B T (a+b) c δ r)(ha:0≤a)(ht:0<b)(he :∀ i, 0 ≤R i)(hR:Ac.Hit p B (taxed d R K) (a+b) s)(hK:1 ≤ K)(hg : s+ Real.exp 1*(c*(1-r)⁻¹) ≤ μ)(hu:0<μ)(hx : degreePrice B μ b ≤ ν)(hν : ν<1):Trees.Ready (facesP p) B (compR q T (taxed d R K)) a μ b ν:=by
   have hh:= capP q hT hp (add_nonneg ha ht.le)
   have hv: Ac.Hit id B (fun j=>Real.exp 1*GasP.caps q T j) (a+b) (Real.exp 1*(c*(1-r)⁻¹)):=by
       intro i; have hh:=budget_scale (Real.exp_pos 1).le (hh i)
       convert! hh using 1; ext i; split <;> ring
   refine ⟨hu,ht,hx,hν,?_,fun i=> budget_loosen (Labels.together _ _ _ hR hv i) hg⟩
   rintro (i|i); exact mul_nonneg (pow_nonneg (zero_le_one.trans hK) _) (he _); exact mul_nonneg (Real.exp_pos _).le (hat_nonneg _ _ (fun i=> clusters_nonneg _ hp.2.2.2.2.1 _) _)
lemma capsule {s:U}(he:∀ i,d i⊆p i)(hv:wagon p s): (sweep d s).card= ∑ i∈s.toLeft,(d i).card:= Finset.card_biUnion fun i hi j hj hh=>((close _ p s.toLeft).1 hv.2.2.1 hi hj hh).mono (he i) (he j)
lemma inheritsK {K:ℝ}(hB:Trees.Ready (facesP p) B (compR q T (taxed d R K)) a μ b ν)(ha:0≤a)(he:∀ i,d i⊆ p i): Ac.Hit (wound p) B (taxed (sweep d) (fun i=> tenderW p q i R T) K) a (μ*(1-ν)⁻¹):=by
   intro i; let t:= compR q T (taxed d R K); let u:= compR q T R
   have he' s (h:wagon p s): taxed (sweep d) (fun i=> tenderW p q i R T) K s= ∏ i∈s,t i:=by
      unfold taxed tenderW; dsimp only; rw [if_pos h,capsule p d he h,← prod_pow_eq_pow_sum]
      calc _ = (∏ i∈s.toLeft,K^(d i).card)*∏ i∈s,u i:=rfl
           _ = _ := by
            have hL : Finset.disjSum s.toLeft s.toRight=s:=by ext i; cases i <;> simp
            rw [show (∏ i∈s,u i)=(∏ i∈s.toLeft,R i)*∏ i∈s.toRight,u (.inr i) from by nth_rw 1 [← hL]; rw [prod_disjSum]; rfl]
            rw [← mul_assoc, ← Finset.prod_mul_distrib]; conv_rhs=> arg 1; rw [← hL]
            rw [prod_disjSum]; rfl
   have hf:= touch_tail (facesP p) B hB i 0
   simp only [Nat.zero_le,if_true,pow_zero,mul_one] at hf
   have ht s (hs: ¬wagon p s) : taxed (sweep d) (fun i=> tenderW p q i R T) K s=0:=by unfold taxed tenderW; dsimp only; rw [if_neg hs,mul_zero]
   refine budget_mono hf (fun s=> ?_) (fun s=> ?_)
   · split; swap; · exact le_rfl
     by_cases hh:wagon p s; swap; · rw [ht s hh,zero_mul]
     rw [he' s hh]; exact mul_nonneg (prod_nonneg fun i _=>hB.2.2.2.2.1 _) (Real.exp_pos _).le
   split
   next hx=>
     by_cases h : wagon p s; swap; · rw [ht s h,zero_mul]; exact hf.1 _
     rw [he' s h]; unfold touches; rw [if_pos ⟨h.2.1,hx⟩, prod_mul_distrib]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _=>hB.2.2.2.2.1 _);
     unfold currency; rw [← Real.exp_sum]; apply Real.exp_monotone; rw [← mul_sum, ← Nat.cast_sum]; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Ac.cover _ _ h.2.1)) ha
   next hx=> exact hf.1 _
lemma boothK (hp: Trees.Ready q B T a c δ r)(ht:∀ i,(q i).Nonempty)(ha:0≤a)(hr:c*(1-r)⁻¹≤1)(hv:∀ i, ‖u i‖ ≤R i)(hG:∀ i, ‖g i‖≤ T i) (s:U):‖motto p d q W u g s‖ ≤ tenderW p q s R T:=by
   have h j: ‖dropsP q g j‖ ≤ Real.exp 1*caps q T j:=by apply (normE _ (caps q T j) (by rw [norm_neg]; exact officer ht hp hG ha j)).trans; exact flash1 _ (caps_one q ht hp ha hr j).1 (caps_one q ht hp ha hr j).2
   have hh i: ‖samples q u g i‖ ≤compR q T R i:=by cases i; exact hv _; exact h _
   unfold motto tenderW; split
   next ht=> rw [if_pos ht.1]; exact (Finset.norm_prod_le ..).trans (prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> hh i))
   next ht=> rw [norm_zero]; split; exact prod_nonneg fun i _=> (norm_nonneg _).trans (hh i); exact le_rfl
end YM.QCD.GasP
