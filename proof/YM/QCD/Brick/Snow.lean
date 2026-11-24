import YM.QCD.Fawn.Price
import YM.QCD.Stew.Payday
/-! # one support-pole per monomial (not per Ferm atom)

Tame seminorm transfer using an augmentation without pairwise products of all endpoint distances. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{D E I:Type*}[Fintype D][Fintype E][Fintype I] {x y:Finset D}{p r q t :ℝ} {g:D→ℕ}{f:E→ℕ}
abbrev dryL (x:ℝ)(v:Alg D):ℝ:=load (fun _=>x) v
lemma health (s: Finset D)(k:ℕ)(h:∀ i∈s,g i≤k): pieD g s ≤ (1+k)^2 := Nat.pow_le_pow_left (Nat.add_le_add_left (Finset.sup_le h) _) _
lemma unitedD (x y:Finset D): pieD g (x∪y) ≤ pieD g x+pieD g y:=by
   unfold pieD; rw [sup_union]; rcases le_total (x.sup g) (y.sup g) with h|h
   · rw [sup_eq_right.mpr h]; exact Nat.le_add_left ..
   rw [sup_eq_left.mpr h]; exact Nat.le_add_right ..
lemma starJoin (h:0≤p)(x y:Finset D): visc g p (mono x*mono y) ≤ starch g p x* p^y.card + p^x.card* starch g p y:=by
   by_cases hp:Disjoint x y; swap
   · rw [mono_mul_zero _ _ hp,visc,map_zero,norm_zero]; exact add_nonneg (mul_nonneg (starch_pos _ h _) (pow_nonneg h _)) (mul_nonneg (pow_nonneg h _) (starch_pos _ h _))
   let v:= x.disjUnion y hp; have hv: visc g p (mono x*mono y)=starch g p v:=by
       rcases mono_mul_sign _ _ hp with h'|h'
       · rw [h']; exact sturdy g v h
       rw [h',visc,map_neg,norm_neg]; exact sturdy g v h
   rw [hv]; unfold starch; rw [show v.card=x.card+y.card from Finset.card_disjUnion ..,pow_add]; apply (mul_le_mul_of_nonneg_right (show (pieD g v:ℝ)≤ pieD g x+ (pieD g y:ℝ) from ?_) (mul_nonneg (pow_nonneg h _) (pow_nonneg h _))).trans; exact le_of_eq (by ring)
   rw [show v=x∪y from Finset.disjUnion_eq_union _ _ hp]; exact_mod_cast unitedD (g:=g) x y
lemma ledgers (W:Alg D)(h:0<p): dryL p W= ∑ s,p^s.card*‖coef s W‖:=by rw [dryL,dry _ (fun _=>h)]; simp only [prod_const]
lemma lightD (h:0<p)(x y:Alg D):visc g p (x*y) ≤ visc g p x *dryL p y+dryL p x*visc g p y:=by
   conv_lhs=> rw [← write x,← write y,Finset.sum_mul]
   simp_rw [mul_sum]; apply (vc_sum ..).trans; rw [pricesD g h.le x,pricesD g h.le y, ledgers y h,ledgers x h, Finset.sum_mul,Finset.sum_mul]; rw [← sum_add_distrib]; apply sum_le_sum; intro i hi; rw [Finset.mul_sum,Finset.mul_sum,← sum_add_distrib]; apply (vc_sum ..).trans; apply sum_le_sum; intro j hj; rw [smul_mul_assoc, mul_smul_comm,vc_scale,vc_scale]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (starJoin h.le i j) (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring) -- edit
lemma unitD (x:Finset D)(h:0<p):dryL p (mono x)=p^x.card:=by
   rw [ledgers _ h,sum_eq_single x]
   · simp
   · intro i _ hi; rw [read_other _ _ hi,norm_zero,mul_zero]
   simp
lemma reachA (i:D)(h:0≤p): visc g p (atom i) = (1+ (g i:ℝ))^2 * p:=by rw [←mono_single i,sturdy g _ h]; simp only [starch,pieD,sup_singleton,card_singleton,Nat.cast_pow,Nat.cast_add,Nat.cast_one,pow_one]
lemma vested (x y:Alg D) : visc g r (x+y)≤ visc g r x+visc g r y:=by unfold visc; rw [map_add]; exact norm_add_le ..
lemma vertex (x y:Alg D) : visc g r (x-y)≤ visc g r x+visc g r y:=by unfold visc; rw [map_sub]; exact norm_sub_le ..
lemma resist (h:0<p)(hp:1 ≤ q)(F :Alg D→ₐ[ℂ] Alg E) (L: List D)(hr:0 ≤ r)(he:∀ i∈L, dryL p (F (atom i))≤r∧ visc f p (F (atom i))≤ q*r): let X:=F (L.map atom).prod
    dryL p X≤ r^L.length ∧ visc f p X≤ q *(2*r)^L.length:=by
   induction L with
   | nil=> intro X; rw [show X=1 by simp [X]]; simp only [List.length_nil,pow_zero,mul_one]; rw [← mono_empty,unitD _ h,sturdy f _ h.le]; simp [starch,pieD,hp]
   | cons i l ih=>
     intro X; let U:= F (atom i); let Z:=F (l.map atom).prod; have hx:X=U*Z:=by unfold X; rw [List.map_cons,List.prod_cons,map_mul]
     obtain ⟨h1,h2⟩:= he i (List.mem_cons_self ..); obtain ⟨hb,hv⟩:= ih fun i hi=> he i (List.mem_cons_of_mem _ hi)
     have hA: dryL p U ≤ r:=h1
     have hY: r^l.length ≤ (2*r)^l.length:=pow_le_pow_left₀ hr (by linarith) _
     rw [hx,List.length_cons,pow_succ,pow_succ, mul_comm _ r]; refine ⟨(load_mul ..).trans (mul_le_mul hA hb (load_nn ..) hr), (lightD h U Z).trans ?_⟩
     exact (add_le_add (mul_le_mul h2 (hb.trans hY) (load_nn ..) (mul_nonneg (zero_le_one.trans hp) hr)) (mul_le_mul h1 hv (norm_nonneg _) hr)).trans_eq (by ring)
lemma monies (h:0<p)(hv:0≤r)(F: Alg D→ₐ[ℂ] Alg E)(S:Finset D)(he:∀ i∈S, dryL p (F (atom i))≤r ∧ visc f p (F (atom i))≤(1+(g i:ℝ))^2*r) : visc f p (F (mono S)) ≤ starch g (2*r) S:=by
   obtain ⟨L,hL,hs,hp⟩:= expression S
   let W:List D:=List.ofFn L; have ht i : i∈W ↔ i∈S:=by rw [hs]; simp [W,Set.mem_range]
   rw [hp,show List.ofFn (atom ∘ L)= W.map atom by rw [List.map_ofFn]]
   have hZ: 1 ≤ (pieD g S:ℝ):= Nat.one_le_cast.mpr (one_le_pow₀ (by omega))
   apply (resist h hZ F W hv ?_).2.trans
   · apply le_of_eq; rw [show W.length= S.card from List.length_ofFn]; rfl
   intro i h; have hi:= (ht i).1 h; refine ⟨(he i hi).1, (he i hi).2.trans ?_⟩; apply mul_le_mul_of_nonneg_right _ hv; unfold pieD; push_cast; gcongr; exact_mod_cast le_sup hi (f:=g)
lemma sprinkles (h:0<p) (hp:0≤ r) (F:Alg D→ₐ[ℂ] Alg E) (S:Finset D)(he:∀ i∈S, dryL p (F (atom i))≤r ∧ visc f p (F (atom i))≤(1+(g i:ℝ))^2*r)(x:Alg D)(hx: x∈region S) {L:ℕ} (hh:∀ i:Finset D,i.card<L→ coef i x=0)(ht:2*r=q*t)(hQ:0≤q)(hy:q≤1)(hg:0≤ t): visc f p (F x) ≤ q^L*visc g t x:=by
   conv_lhs=> rw [← write x,map_sum]
   apply (vc_sum ..).trans; rw [pricesD g hg,Finset.mul_sum]; apply sum_le_sum; intro i _; rw [map_smul,vc_scale]; by_cases hu:coef i x=0
   · rw [hu,norm_zero,zero_mul,mul_zero,mul_zero]
   have ha:S⊇i:=by_contra fun h=> hu (Cove.ember x hx i h); have hv: L≤ i.card:= le_of_not_gt fun h=> hu (hh _ h)
   refine (mul_le_mul_of_nonneg_left (monies h hp F i (fun i h=> he i (ha h))) (norm_nonneg _)).trans ?_; rw [ht,starch,mul_pow]; apply le_trans _ (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hQ hy hv) (mul_nonneg (starch_pos g hg _) (norm_nonneg _))); unfold starch; exact le_of_eq (by ring)
end YM.QCD.Brick
