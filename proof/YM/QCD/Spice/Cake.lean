import YM.QCD.Jets.Deluxe
/-! # Prices for Δ actual operator.Height independent card Wick. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
section ground
variable {A B D E:Type*} [Fintype A] [Fintype B]{u w δ:ℝ}
variable {p:A→ℝ}{q:B→ℝ}{G F J : EndA A}
lemma spawnA (p:A→ℝ)(a b:Alg A): load p (a+b)≤ load p a+load p b:=by unfold Creek.load wscale; rw [map_add]; exact norm_add_le ..
lemma plus (hp:Pledge p F u)(hq:Pledge p G w): Pledge p (F+G) (u+w):=⟨add_nonneg hp.nn hq.nn,fun x=> ((spawnA (p) _ _).trans ((add_le_add (hp.rates x) (hq.rates x)).trans_eq (add_mul ..|>.symm)))⟩
lemma spinning (hp:Pledge p F u)(hq:Pledge p G u)(h:Pledge p (F-G) (u*δ))(n:ℕ)(he:0 ≤ δ): Pledge p (F^n-G^n) (n*(u^n*δ)):=by
   induction n with
   | zero=> simp only [pow_zero,sub_self,Nat.cast_zero,zero_mul]; refine ⟨le_rfl,fun x=>?_⟩; rw [ContinuousLinearMap.zero_apply,load_zero,zero_mul]
   | succ n ih=>
     have ht:Pledge p _ _:=plus (ih.combines hp) ((hq.powX n).combines h)
     have hm:F^(n+1)-G^(n+1)=(F^n-G^n)*F+G^n*(F-G):=by rw [sub_mul,mul_sub,pow_succ,pow_succ]; abel
     rw [hm]; apply ht.bumps; apply le_of_eq; push_cast; ring
set_option maxHeartbeats 500000 in
lemma whirl (hp:Pledge p F u)(hq:Pledge p G u)(h:Pledge p (F-G) (u*δ))(he:0≤δ): Pledge p (excess F-excess G) (Real.exp u*u*δ):=by
  have hu:=hp.nn; apply Pledge.mk (by positivity); intro x
  let f (d:EndA A) (n:ℕ):= ((n.factorial:ℂ)⁻¹) • d^n
  let a n:=(n.factorial:ℝ)⁻¹ *u^n
  let H d: HasSum (f d) (birth d):= exp_series_hasSum_exp' (𝕂:=ℂ) d
  have h₁ : HasSum (fun (n:ℕ)=> f F n - f G n) (excess F-excess G):=by unfold excess; rw [sub_sub_sub_cancel_right]; exact (H _).sub (H _)
  have h₂ : HasSum a (Real.exp u):=by rw [Real.exp_eq_exp_ℝ]; exact exp_series_hasSum_exp' (𝕂:=ℝ) u
  let t (n:ℕ):=f F (n+1)-f G (n+1)
  rw [← hasSum_nat_add_iff' (k:=1)] at h₁; simp only [sum_range_one,f,pow_zero,sub_self,sub_zero] at h₁
  have hh : ∀ n,Pledge p (t n) (a n*u*δ):=by
    intro k; rw [show t k = (↑((k+1).factorial):ℂ)⁻¹ •(F^(k+1) - G^(k+1)) from (smul_sub ..).symm]; have ht:=(spinning hp hq h (k+1) he).penny ((↑((k+1).factorial):ℂ)⁻¹); apply ht.bumps; apply le_of_eq
    rw [norm_inv]; have hQ:∀ n:ℕ,‖(↑n:ℂ)‖=↑n:=by simp
    dsimp only [a]; rw [hQ,pow_succ,Nat.factorial_succ]; push_cast; field_simp<;> ring
  let M:=load p x
  refine le_of_tendsto_of_tendsto' (payload p|>.continuousAt.tendsto.comp (show Tendsto (fun s: Finset ℕ=>∑ i∈s,t i x) atTop (𝓝 _) from (ContinuousLinearMap.apply ℂ _ x).hasSum h₁)) (show Tendsto (fun s:Finset ℕ=>∑ i∈s,a i*u*δ*M) atTop (𝓝 _) from ((h₂.mul_right u).mul_right δ|>.mul_right M)) (fun i=>?_)
  exact (load_sum ..).trans (sum_le_sum (fun j _=> (hh j).rates x))
-- telescope atom under bounded substitution. factor cardinal paid one.
variable (F₁ F₂ : Alg A →ₐ[ℂ] Alg B)(K:Finset A)
variable (h:∀ i∈K, load q (F₁ (atom i))≤p i) (g:∀ i∈K,load q (F₂ (atom i)) ≤ p i)(hv:∀ i∈K, load q (F₁ (atom i)-F₂ (atom i)) ≤ δ*p i)(hp:∀ i, 0<p i)(he:0≤ δ)
include hp in
lemma onMono (s:Finset A): load p (mono s)=∏ i∈s,p i:=by
    rw [dry _ hp,sum_eq_single s,Grass.read,norm_one,mul_one]; exact fun i _ h=>by rw [read_other _ _ h,norm_zero,mul_zero]
    simp
lemma cradle (s:Finset A)(ht:s⊆K): mono s∈ region K:=by
   induction s using Finset.induction_on with
   | empty=> rw [mono_empty]; exact Subalgebra.one_mem _
   | insert i s hi ih=>
      have he : atom i * mono s ∈ region K:= Subalgebra.mul_mem _ (marked i K (ht (mem_insert_self ..))) (ih (Subset.trans (subset_insert ..) ht)); have hh:= mono_mul_sign {i} s (by simp [hi]); rw [disjUnion_eq_union,singleton_union,mono_single] at hh; rcases hh with hh|hh <;> rw [hh] at he; exact he; exact neg_mem_iff.mp he
include h g hv hp he
lemma roughM (s:Finset A)(hx:s⊆K): load q (F₁ (mono s) - F₂ (mono s))≤ s.card*δ*∏ i∈s,p i:=by
  induction s using Finset.induction_on with
  | empty=> rw [mono_empty,map_one,map_one,sub_self,load_zero,card_empty,Nat.cast_zero,zero_mul,zero_mul]
  | insert i s hi ih=>
    have hS:s ⊆K:= Subset.trans (subset_insert ..) hx; let z:= mono s; let w:= ∏ i∈s,p i; have hw:0 ≤ w:=prod_nonneg fun i _=> (hp i).le; let v:= atom i
    have ht := (ferry F₂ hp g z (cradle K _ hS)).trans_eq (onMono hp s) -- q named g
    have hh:F₁ (v*z)-F₂ (v*z)=F₁ v*(F₁ z-F₂ z)+(F₁ v-F₂ v)*F₂ z:=by rw [map_mul,map_mul,mul_sub,sub_mul]; abel
    have hw':load q (F₁ (v*z)-F₂ (v*z))≤ p i*((s.card:ℝ)*δ*w)+δ*p i*w:=by rw [hh]; exact (spawnA ..).trans (add_le_add ((load_mul ..).trans (mul_le_mul (h i (hx (mem_insert_self ..))) (ih hS) (load_nn ..) (hp _).le)) ((load_mul ..).trans (mul_le_mul (hv i (hx (mem_insert_self ..))) ht (load_nn ..) (by have ht := hp i; positivity))))
    have hQ: p i*((s.card:ℝ)*δ*w)+δ*p i*w=(insert i s).card*δ*∏ i∈ insert i s,p i:=by rw [card_insert_of_notMem hi,prod_insert hi]; push_cast; unfold w; ring
    have ht':= hw'.trans_eq hQ; have hh:=mono_mul_sign {i} s (by simp [hi]); rw [disjUnion_eq_union,singleton_union,mono_single] at hh; unfold v z at ht'; rcases hh with hh|hh
    · rw [hh] at ht'; exact ht'
    rw [hh,map_neg,map_neg,show -F₁ _ - -F₂ _ = -(F₁ (mono (insert i s))- F₂ (mono (insert i s))) from ?_,load_neg] at ht'; exact ht'; abel
lemma roughG (x: Alg A)(hx:x∈region K): load q (F₁ x-F₂ x)≤ K.card*δ*load p x:=by
   conv_lhs=> rw [← write x,map_sum,map_sum,← sum_sub_distrib]
   refine (load_sum ..).trans ?_; rw [dry _ hp,mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [map_smul,map_smul,←smul_sub,load_scale]; by_cases hi:i⊆K
   swap; · rw [ember x hx i hi,norm_zero,zero_mul,mul_zero,mul_zero]
   have ht: (i.card:ℝ)*δ*∏ i∈i,p i ≤ K.card*δ*∏ i∈i,p i:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hi)) he) (prod_nonneg (fun i _=> (hp i).le))
   exact (mul_le_mul_of_nonneg_left ((roughM F₁ F₂ K h g hv hp he i hi).trans ht) (norm_nonneg _)).trans_eq (by ring)
end ground
end YM.QCD.Spice
