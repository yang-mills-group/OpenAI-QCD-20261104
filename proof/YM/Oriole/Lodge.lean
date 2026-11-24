import YM.Oriole.Wrent
/-! norm(V.tap) bound on all labels using stencil paid. No cover poly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d n:ℕ}(a b:Flavor 6)(g:Bool){c:Side}
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria TorusPCAC.Geometry Cylinder
local notation "T" => SpinMode d
local notation "Q" => Massive.Run.plane
local notation "K" => Modes c 6
open Grass.Ward
section
variable {X:Type*}[Fintype X]
private lemma off (s:Finset X)(i:X)(h:i∉s): vary i (mono s)=0:=by
    have ht (z:List X)(h:i∉z): vary i (z.map atom).prod=0:=by induction z with|nil=>simp [vary_one]|cons k L ih=> simp only [List.mem_cons,not_or] at h; simp only [List.map_cons,List.prod_cons,vary_mul, vary_off _ _ h.1, ih h.2,mul_zero,zero_mul,add_zero]
    obtain ⟨u,-,hp,H⟩:= expression s; have hg:i∉List.ofFn u:=by simpa [(hp i)] using h
    rw [H]; simpa only [List.map_ofFn] using ht _ hg
variable [DecidableEq X]
lemma pray (s:Finset X)(i:X)(h:i∈s):∃ c:ℂ, ‖c‖=1∧ vary i (mono s)=c • mono (s.erase i):=by
      let t:=s.erase i; have hp:i∉t:=by simp[t];
      have hh : Disjoint {i} t:=by simp [hp]
      have he:=mono_mul_sign _ _ hh; rw [disjUnion_eq_union, singleton_union, mono_single,show insert i t=s from insert_erase h] at he
      have hb: vary i (atom i*mono t)=mono t:=by rw [vary_mul,vary_self,off t _ hp,mul_zero,one_mul,add_zero]
      rcases he with H|H
      · refine ⟨1,norm_one,?_⟩; rw [H] at hb; rw [hb,one_smul]
      rw [H,map_neg] at hb; refine ⟨-1,by simp,?_⟩; rw[neg_one_smul, show vary i (mono s)= -(mono t) from neg_eq_iff_eq_neg.mp hb]
lemma disjoint_price (i j : X)(h:i≠j)(x:Alg X): ‖(coef ∅) (vary j (vary i x))‖= ‖(coef {i,j}) x‖ :=by
   conv_lhs=> arg 1; rw [←write x]
   simp_rw [map_sum,map_smul]
   let t:Finset X:={i,j}; rw[sum_eq_single t]; rw [norm_smul]; obtain ⟨c,hc,hx⟩:=pray t i (by simp[t]); have he:t.erase i={j}:=by simp [t,h,h.symm]
   rw [hx,he,map_smul, mono_single,vary_self,map_smul,show coef (∅:Finset X) 1=1 from TorusPCAC.Ward.zeroR_one, norm_smul,hc]; simp [t]
   · intro s _ hu; by_cases hx:i∈s
     · obtain ⟨c,hc,hv⟩:=pray s i hx; rw[hv,map_smul,map_smul]; let s':=s.erase i; by_cases h':j∈s'
       · obtain ⟨e,hQ,hV⟩:=pray s' j h'; change _ • (c • coef ∅ (vary j (mono s')))=0; rw [hV,map_smul,read_other]; simp
         intro hI; have hL: s'={j}:=by
              conv_lhs=>rw[← insert_erase h']
              rw [← hI]; rfl
         apply hu; conv_lhs=>rw [← insert_erase hx]
         rw [show s.erase i= _ from hL]
       rw [off (s.erase i) j h']; simp
     rw[off s i hx]; simp
   simp
lemma ivory (x:Dirac X)(i j:X): ‖uncoat x i j‖= ‖coef {Sum.inr i,Sum.inl j} x‖:=by
     change ‖- - _‖= _; rw [neg_neg]; exact disjoint_price (Sum.inr i) (Sum.inl j) (by intro h; cases h) _
end
open QCD.Creek MassiveQCD.Plate
variable (x:Lat.Fields c 6)(r:ℝ)(hi:1 ≤ r)
open QCD.Run -- cell
local notation "R"=>piece a b (uncoat x)
lemma le_budget (i j:Fiber)(hi:1 ≤ r)(hy:1≤ n): ∑ p:Site c,∑ q: Site c, (pdist p+pdist q:ℝ)* ‖cell R p q i j‖ ≤ 2 * view 0 n x r:=by
    let f (p:Site c) : K:= ((p,i),a)
    let G(q:Site c): K:= ((q,j),b)
    let g : Site c × Site c → Finset (Pairs K):= fun x=>{Sum.inr (f x.1), Sum.inl (G x.2)}
    have hg: Injective g:=by
         intro p q he; have h1:(Sum.inr (f p.1))∈ g q:=he ▸ (by simp[g]:_∈g p); have h2:Sum.inl (G p.2)∈g q:=he ▸(by simp[g]:_∈g p); simp [g,f,G] at h1 h2; exact Prod.ext h1 h2
    let W(s:Finset (Pairs K)):= toll 0 n s r * ‖coef s x‖; let Y:= univ.image g
    apply le_trans (b:= 2*∑ s∈Y, W s)
    · rw [sum_image hg.injOn, Finset.mul_sum,Fintype.sum_prod_type]; refine sum_le_sum fun p _=> sum_le_sum fun q _=>?_
      let s:=g (p,q); change (pdist p+pdist q:ℝ)* ‖uncoat x _ _‖ ≤ 2*(toll _ _ s r * _); have hζ : ‖coef s x‖ = ‖uncoat x (f p) (G q)‖:=by rw [ivory]; congr; ext u; simp [g,s]
      rw [show ‖uncoat x ((p,i),a) ((q,j),b)‖=‖coef s x‖ from hζ.symm] -- wrong ←
      change _*‖coef s x‖ ≤ _; rw[←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      let E:=s.sup (Stew.lens (0:Site c)); have h1:pdist p≤ E:= le_trans (le_of_eq (show pdist p=Stew.lens (0:Site c) (Sum.inr (f p)) from (by change _=pdist (p-0); rw [sub_zero]))) (Finset.le_sup (f:=Stew.lens 0) (by simp [g,s]))
      have h2:pdist q≤ E:=le_trans (le_of_eq (show pdist q=Stew.lens (0:Site c) (Sum.inl (G q)) from (by change _=pdist (q-0); rw [sub_zero]))) (Finset.le_sup (f:=Stew.lens 0) (by simp [g,s])); have ht : (E:ℝ)≤toll (0:Site c) n s r:=by
          unfold toll; apply (le_trans (b:= (1+(E:ℝ))^n) ?_ (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hi))); apply (le_add_of_nonneg_left (show (0:ℝ)≤1 from zero_le_one)).trans; exact (pow_one ..).symm.le.trans (pow_le_pow_right₀ (by simp) hy)
      have h1:(pdist p:ℝ)≤ E:=by exact_mod_cast h1
      have h2:(pdist q:ℝ)≤ E:=by exact_mod_cast h2 -- line parsing
      linarith
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (f:=W) (s:=Y) (t:=(Finset.univ:Finset (Finset (Pairs K)))) (Finset.subset_univ _) (fun s _ _=> mul_nonneg (by unfold toll; positivity) (norm_nonneg _))) (by norm_num)
-- financial projected pointer on SpinTrace.
noncomputable def spread (D:Site c→Site c→ℂ)(M:Spike): Lat.Fields c 6→ₗ[ℂ]ℂ:=
    let f (x: Lat.Fields c 6):=∑ i:Site c,∑ j:Site c,D i j*((cell (piece a b (uncoat x)) i j* (wave M)).trace)
    { toFun:= f
      map_add' x y:=by unfold f; rw [map_add]; simp_rw [show ∀ i j:Site c,cell (piece a b (uncoat x+uncoat y)) i j=cell (piece a b (uncoat x)) i j+cell (piece a b (uncoat y)) i j from fun _ _=>rfl, add_mul,Matrix.trace_add,mul_add,sum_add_distrib]
      map_smul' z x:=by unfold f; rw [map_smul]; simp_rw [show ∀ i j:Site c, cell (piece a b (z • uncoat x)) i j=z • (cell (piece a b (uncoat x)) i j) from fun _ _=>rfl,Matrix.smul_mul,Matrix.trace_smul,mul_smul_comm, Finset.smul_sum]; rfl }
-- simpler direct rewrite cell equations.M. after compile
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.le_budget
