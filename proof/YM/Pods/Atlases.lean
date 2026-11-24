import YM.Pods.TargetX
import YM.Massive.Target.Euclidean
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry Chess.Fortuna
variable (S:Scheme){C:Sequence} {d:ℕ}
variable (Yv:ℝ) (Ht:SourceRead.TaperHol){Go:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Go)(sym:RawSym)(base:ℕ→ℕ) (U:Massive.Lining.Temper.Collage.Exhibit.CoreMix)
local notation "cK"=>C.S
local notation "ς" j:arg=>C.S.side (C.R j)
local notation "γ"=>clock cK
local notation "Pκ" => Uv.display C Ht sym U base
local notation "Ψ"=> Bloom Uv
variable (w:Label d)(q:Bool)(hp: moored w.val q)(hw:w ≠0)
-- bounds same fixed reference across all ≤24 rotations, convert budgets.All.Point.R.One.G minimal interior.fit. Y.Opacity.S
variable (hX:(Uv.display C Ht sym U base).System)
variable (hY:Spent C (Uv.display C Ht sym U base))
variable (e:ℝ)(he:0<e)
variable (hs:Sway C.S){β ν:ℝ}(hC:C.Path β ν)
local notation "V₁"=> rayM C.S d e
set_option quotPrecheck false
local notation "Ω" i:arg => (C.A i).regulator
variable {n:ℕ}(D: Fin n→ℕ)(u:(i:Fin n)→ Label (D i))(s: Fin n→ Bool)
local notation "η"=> metricP C Pκ D
local notation "Υ"=> pricedh C.S e D
local notation "Φ"=> watchH C Pκ D
-- consistent multiplication heights all arities. Signal Big.Gain selection clock. Margin guards.Proof.Vehicle for other uses.
-- mult.Grass model. discontinuity allowed support. arbitrary averaging family linear potent.
lemma skipU {I α:Type}[DecidableEq I]{l:List I}(f:I→α)(v:I)(x:α)(h:v∉l):l.map (update f v x)=l.map f:=by refine List.map_congr_left (fun i hi=>?_) ; exact update_of_ne (fun e=> by subst i; exact False.elim (h hi)) .. -- binder shadow.
lemma unwrap {X:Type}[Semiring X](l: List (Fin n))(f:Fin n→X)(x y:X)(i:Fin n)(hi:i∈ l)(hx:l.Nodup): (l.map (Function.update f i (x+y))).prod=(l.map (update f i x)).prod+(l.map (update f i y)).prod:=by
    induction l with
    | nil=> exact absurd hi (List.not_mem_nil)
    | cons j l ih=>
        have ht:= List.nodup_cons.mp hx; by_cases he:j=i
        · subst j; simp only [List.map_cons, List.prod_cons, update_self,skipU f i _ ht.1,add_mul]
        simp only [List.map_cons,List.prod_cons,update_of_ne he]; rw [ih ((List.mem_cons.mp hi).resolve_left (Ne.symm he)) ht.2,mul_add]
lemma each (P:Calibration C)(i j:ℕ)(s: Fin n)(x y:Label (D s))(f: Fin n→ Cover):metricP C P D (update u s (x+y)) i f= metricP C P D (update u s x) i f+metricP C P D (update u s y) i f:=by
    let F(t:Fin n):= ((P.candidate (D t) (C.S.side (C.R i) (C.N i)) (f t)).comp (P.mix (D t) none i).toLinearMap)
    have hz(t: Fin n) (x:Label (D t)):P.physical none i x (f t)= F t x:=rfl
    unfold metricP; simp_rw [hz]; rw [← map_add]; apply congr_arg; let L:= List.finRange n; let V(k):= F k (u k)
    have hf (x:Label (D s)) : (fun a=> F a (Function.update u s x a))= Function.update V s (F s x):=by ext1 i; by_cases h:i=s; subst i; simp; simp only [update_of_ne h]; rfl
    rw [hf,hf,hf,map_add,List.ofFn_eq_map,List.ofFn_eq_map,List.ofFn_eq_map]; exact unwrap _ _ _ _ s (List.mem_finRange s) (List.nodup_finRange n) -- arguments.C fill Nodup
include he hs hX hY hC
lemma inkPass :∃ c:ℝ,0 ≤ c∧∀ᶠ j in atTop,∀ᶠ i in atTop,Φ u j i (Υ j c):=by
    have h (A:Finset (Fin n))(u:(i:Fin n)→ Label (D i))(hs':∀ i,i∉ A→∃ p:Bool,moored (u i).val p):∃ c:ℝ,0 ≤ c∧∀ᶠ j in atTop,∀ᶠ i in atTop,Φ u j i (Υ j c):=by
       induction A using Finset.induction_on generalizing u with
       | empty=>
          choose p hp using fun i=> hs' i (Finset.notMem_empty _); exact pointPass Ht Uv sym base U hX hY e he hs hC D u p hp
       | insert a A ha ih=>
          let k(p:Bool):= facing sym p (u a); let X(p:Bool):= Function.update u a (k p); have hp(p:Bool)(j:Fin n)(hj:j∉ A): ∃ b:Bool,moored ((X p j).val) b:=by
               by_cases h:j=a; · subst j; unfold X; rw [update_self]; exact ⟨_,fronting sym _ _⟩
               unfold X; rw [update_of_ne h]; exact hs' j (by simp [h,hj])
          obtain ⟨c,hc,H⟩:= ih _ (hp true); obtain ⟨d,hd,hD⟩:= ih _ (hp false); refine ⟨c+d,add_nonneg hc hd,?_⟩
          filter_upwards [H,hD] with j hj hr; filter_upwards [hj,hr] with i hz ht x hV
          have ht':η u i x= η (X true) i x+ η (X false) i x:=by have h:= Hub.each D u Pκ i j a (k true) (k false) x; rw [show k true+k false=u a from (Depth.revelation ..).symm,Function.update_eq_self] at h; exact h
          rw [ht']; apply (norm_add_le ..).trans; apply le_trans (add_le_add (hz _ hV) (ht _ hV)); exact le_of_eq (by unfold pricedh; ring)
    exact h _ u (fun i hi=> False.elim (hi (Finset.mem_univ _)))
omit he hs hX hY hC
-- use with torus-sep; power clock for all thresholds.
lemma space0 (S:Scheme)(m:ℕ) :0 < S.spacing m:=by unfold Scheme.spacing; positivity
lemma footprint (m j:ℕ)(h:m≤ j): S.spacing j * ratioTo S j m= S.spacing m:=by unfold Scheme.spacing; rw [factorize h,Nat.cast_mul]; let n:= ratioTo S j m; have hn:0<n:=(odd_to h).pos; rw [mul_inv_rev]; let p:= (S.ratio m).val; change (n:ℝ)⁻¹*_ *_=_; field_simp; rfl
lemma spacing_antitone : Antitone S.spacing:=by
   intro i j h; rw [← footprint S i j h]; exact le_mul_of_one_le_right (space0 S j).le (by exact_mod_cast (show 1 ≤ _ from Odd.pos (odd_to h)))
abbrev localSep (C:Sequence)(i:ℕ)(f:Fin n→ Cover)(r:ℝ):= ∀ m k,m≠ k → r ≤ C.S.spacing (C.N i)*separation (wrap _ (f m)) (wrap (C.S.side (C.R i) (C.N i)) (f k))
noncomputable abbrev budgetD:= ∑ j, ((D j:ℝ)/2+e)
lemma priceTo (j:ℕ)(c:ℝ): pricedh C.S e D j c=c*Real.exp (budgetD e D * γ j):=by
   unfold pricedh budgetD Hub.rayM; simp only [one_mul]; rw [Finset.sum_mul, Real.exp_sum]
include hC
lemma shyness (r:ℝ)(he:0<r)(m:ℕ) : ∃ i≥m,C.S.spacing i<r:=by obtain ⟨i,h,H⟩:= ((tendsto_nhds_of_tendsto_nhdsWithin hC.physical|>.eventually_lt_const he).and (hC.uv.tendsto_atTop.eventually_ge_atTop m)).exists; exact ⟨_,H,h⟩
omit hC in
lemma tide (j i:ℕ) (x:Fin n→ Cover){r:ℝ}(hx:localSep C i x r)(hk:j ≤ C.N i)(hr:C.S.spacing j<r): seaM C i j x:=by intro u v hu; have h:= hr.trans_le (hx u v hu); rw [← footprint C.S j _ hk] at h; exact_mod_cast (lt_of_mul_lt_mul_left h (space0 C.S _).le) -- casts.
include he hX hY hs
lemma elementary :∃ (c:ℝ) (M:ℕ),0 ≤ c∧ ∀ r:ℝ, 0 < r → r ≤1→∀ᶠ i in atTop, ∀ f:Fin n→ Cover, localSep C i f r → ‖η u i f‖≤ c* r⁻¹^M:=by
    obtain ⟨c,hc,H⟩:= inkPass (C:=C) Ht Uv sym base U hX hY e he hs hC D u; obtain ⟨N,h⟩:= eventually_atTop.mp (H.and (hs.track 1 zero_lt_one))
    let b:= budgetD e D; have h₁:0 ≤ b:= Finset.sum_nonneg fun a _=>add_nonneg (by positivity) he.le
    obtain ⟨m,hm⟩:=exists_nat_gt (b*2); refine ⟨max c (Υ N c),m, hc.trans (le_max_left ..),fun r hr hr' =>?_⟩
    let q:= Nat.find (shyness hC r hr N); have hN := Nat.find_spec (shyness hC r hr N);
    have hV:Υ q c ≤ max c (Υ N c)*r⁻¹^m:=by
       have hψ : 1 ≤ r⁻¹^m:= one_le_pow₀ (one_le_inv₀ hr |>.mpr hr')
       by_cases he:q=N; rw [he]; exact (le_max_right ..).trans (le_mul_of_one_le_right (hc.trans (le_max_left ..)) hψ)
       let p:=q-1; have hp:N ≤ p:=by have h:N ≤ q:=hN.1; unfold p; omega
       have hh : q=p+1:=by unfold p; have h:N ≤ q:= hN.1; omega
       have ht : r ≤ C.S.spacing p:= le_of_not_gt fun h0=>by have hz:q ≤ p:= Nat.find_min' (shyness hC r hr N) ⟨hp,h0⟩; omega
       have hγ : γ p ≤ Real.log r⁻¹:= Real.log_le_log (inv_pos.mpr (space0 C.S _)) (inv_le_inv₀ (space0 C.S _) hr |>.mpr ht) -- inverse_le_inv arg order
       rw [priceTo]; apply (mul_le_mul_of_nonneg_left _ hc).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (zero_le_one.trans hψ)); rw [← Real.exp_log (pow_pos (inv_pos.mpr hr) m), Real.log_pow]; apply Real.exp_monotone; change b*clock C.S q ≤ _; rw [hh]; refine le_trans (mul_le_mul_of_nonneg_left (h p hp).2 h₁) ?_; have hp':(1+(1:ℝ))=2:=by norm_num
       rw [hp']; nlinarith only [mul_le_mul_of_nonneg_left hγ (mul_nonneg h₁ (by norm_num: (0:ℝ)≤2)),mul_le_mul_of_nonneg_right hm.le (Real.log_nonneg (one_le_inv₀ hr|>.mpr hr'))]
    filter_upwards [(h q hN.1).1,hC.uv.tendsto_atTop.eventually_ge_atTop q] with i hi hv f hx; exact (hi f (tide _ _ f hx hv hN.2)).trans hV
end YM.Massive.Patria.Hub
#print axioms YM.Massive.Patria.Hub.elementary
