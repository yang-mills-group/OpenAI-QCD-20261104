import YM.QCD.Ruby.Copper
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
/-! # single rooted large passenger sets. keep count soft by logs. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Trees
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}{a u v w A:ℝ} {B:ℕ}
variable (Y:Hue c N ι) (X:Rail c N β)
variable {p :ι→ℝ} {q:β→ℝ}
abbrev wig (p:ι→ℝ) (j:ι):ℝ:= Real.exp (p j)-1
lemma wig_nn (h:0≤p)(j:ι):0 ≤ wig p j:= sub_nonneg.mpr (Real.one_le_exp (h j))
def money (p:ι→ℝ)(q:β→ℝ)(v:Car Y X):ℝ:=q v.site*∏ i∈v.bag, wig p i
def metal (A:ℝ) := fun i:β=>Real.exp ((oriD X i).card*A) -- syntax currency
abbrev fare (q:β→ℝ)(i:β)(B:ℕ)(a:ℝ):= q i*currency B a (home X i)
variable (h:Ac.Hit Y.bud B p a A)(hv:0≤p)(hp:0 ≤ q)(ht: 0≤a)
variable (hr: Ac.Hit (home X) B ((metal X A)*q) a u)
include ht
lemma cab (i:Car Y X) : currency B a i.vat≤ currency B a (home X i.site)*∏ j∈i.bag,currency B a (Y.bud j):=by
    unfold currency; rw [← Real.exp_sum,← Real.exp_add]; apply Real.exp_monotone; rw [← mul_sum, ← mul_add,← Nat.cast_sum,← Nat.cast_add]; apply mul_le_mul_of_nonneg_left _ ht; apply Nat.cast_le.mpr; refine le_trans (Ac.cover _ _ i.shades) ?_; unfold Car.sleeper; rw [sum_disjSum,sum_singleton]; rfl
include hv hp
abbrev routing (i:Car Y X)(q:β→ℝ)(p:ι→ℝ) (B:ℕ)(a:ℝ) :ℝ:= fare X q i.site B a*pick Y X p B a i
lemma routing_nn (i:Car Y X):0≤ routing Y X i q p B a:=mul_nonneg (mul_nonneg (hp _) (Real.exp_pos _).le) (prod_nonneg fun i _ => mul_nonneg (wig_nn hv i) (Real.exp_pos _).le)
lemma cabs (i:Car Y X):money Y X p q i *currency B a i.vat ≤ routing Y X i q p B a:=by
    refine (mul_le_mul_of_nonneg_left (cab Y X ht i) (mul_nonneg (hp _) (prod_nonneg fun i _=> wig_nn hv i))).trans_eq ?_; unfold routing pick; rw [prod_mul_distrib]; unfold wig fare; ring
include h hr
lemma fromhome (U: Finset (Car Y X))(x:Site c)(hx:∀ i∈U,x∈home X i.site): ∑ j∈U, routing Y X j q p B a≤ u :=by
    let Z:= U.image Car.site; let S i:=U.filter (fun p=> p.site=i); let v i:= if x∈home X i then (metal X A i*q i)*currency B a (home X i) else 0
    have hp i (hi:i∈Z): ∑ j∈S i, routing Y X j q p B a ≤ v i:=by
       have hv' j (hh:j∈S i): (j:Car Y X).site=i:=(mem_filter.mp hh).2
       let f:= pick Y X p B a; rw [show ∑ j∈S i,routing Y X j q p B a=fare X q i B a*∑ j∈S i,f j from ?_,show v i=fare X q i B a*(metal X A i) from ?_]
       · exact mul_le_mul_of_nonneg_left (lead Y X (S i) ∅ h hv hv' ht).1 (mul_nonneg (hp i) (Real.exp_pos _).le)
       · unfold v; rw [if_pos]; · unfold fare; ring
         obtain ⟨u,hq,hr⟩:=mem_image.mp hi; exact hr ▸ hx u hq
       rw [mul_sum]; exact sum_congr rfl fun j hj=>congr_arg (fun i=>fare X q i B a*f j) (hv' j hj)
    calc _=∑ i∈Z, ∑ j∈ S i, routing Y X j q p B a := (sum_fiberwise_of_maps_to (fun i hi=> mem_image_of_mem Car.site hi) _).symm
         _ ≤ ∑ i∈Z,v i:=sum_le_sum hp
         _ ≤ u:=budget_sum (hr x) Z

lemma fromspur (j:ι)(U: Finset (Car Y X))(hh:∀ i∈U,j∈i.bag) : ∑ i∈U,routing Y X i q p B a ≤ (Y.bud j).card*(p j *currency B a (Y.bud j))*u :=by
   let T:=p j*currency B a (Y.bud j); have ht':0≤T:=mul_nonneg (hv _) (Real.exp_pos _).le; let g i:= routing Y X i q p B a
   let Z:=Y.bud j; let S (b:Site c):= U.filter fun i=> b∈home X i.site
   have hf x (he:x∈Z): ∑ i∈ S x,g i ≤ T*u:=by
       let V := (S x).image Car.site; let W b:=(S x).filter fun i=> i.site=b
       let v i:= if x∈home X i then (metal X A i*q i)*currency B a (home X i) else 0
       have HE i (hi:i∈V) : ∑ z∈ W i,g z≤ T*v i:=by
           have hu a (ha:a∈W i): (a:Car Y X).site=i:=(mem_filter.mp ha).2
           have hk i' (hi':i'∈W i):j ∈ (i':Car Y X).bag:= hh _ ((mem_filter.mp (mem_filter.mp hi').1).1)
           let C:=pick Y X p B a
           rw [show ∑ z∈ W i,g z=fare X q i B a*∑ z∈W i,C z from ?_,show v i=fare X q i B a* metal X A i from ?_]; rotate_left
           · unfold v; rw [if_pos]; · unfold fare; ring
             obtain ⟨y,hy,hH⟩:= mem_image.mp hi; exact hH ▸ (mem_filter.mp hy).2
           · rw [mul_sum]; exact sum_congr rfl fun z hz=> congr_arg (fun i=>fare X q i B a*C z) (hu z hz)
           rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left ((lead Y X (W i) ∅ h hv hu ht).2 j hk) (mul_nonneg (hp _) (Real.exp_pos _).le)
       calc _=∑ i∈V,∑ z∈W i,g z:=(sum_fiberwise_of_maps_to (fun i hi=> mem_image_of_mem Car.site hi) _).symm
            _≤ ∑ i∈V,T*v i:=sum_le_sum HE
            _≤ T*u:=budget_sum (budget_scale ht' (hr x)) V
   calc _≤∑ x∈Z,∑ i∈S x,g i:=by
             simp_rw [S,sum_filter]; rw [sum_comm]; refine sum_le_sum fun i hi=>?_ ; obtain ⟨z,hz,hj⟩:= not_disjoint_iff.mp (i.closeD j (hh _ hi)); refine le_trans ?_ (single_le_sum (f:=fun x:Site c=> if x∈home X i.site then g i else 0) (s:=Z) (a:=z) (fun i _=>ite_nonneg (routing_nn Y X hv hp ht _) le_rfl) hz); rw [if_pos (show z ∈home X i.site from ((X.addr _).part hj))]  -- possible
        _≤ ∑ _x∈Z,T*u:=sum_le_sum hf
        _= (Y.bud j).card*T*u:=by rw [sum_const,nsmul_eq_mul,← mul_assoc]

lemma toned {A':ℝ} (H:Ac.Hit Y.bud B p (a+1) A') :Ac.Hit (Car.vat (Y:=Y) (X:=X)) B (money Y X p q) a (u+u* Animals.ballCost B*A'):=by
    have hU:= budget_nonneg (hr 0)
    intro x
    let m:=money Y X p q; have hm (i:Car Y X): 0 ≤ m i:=mul_nonneg (hp _) (prod_nonneg fun _ _=>wig_nn hv _)
    let w i:=routing Y X i q p B a
    apply budget_of_sum; · intro i; split; exact mul_nonneg (hm _) (Real.exp_pos _).le; exact le_rfl
    intro Z
    rw [← sum_filter]; let V:= Z.filter fun i=> x∈Car.vat i
    let U:=V.filter fun i => x∈ home X i.site
    let S:=V\U; have he(i)(hi:i∈S):∃ j∈Car.bag i,x∈Y.bud j:=by
       obtain ⟨hj,hH⟩:=mem_sdiff.mp hi; obtain ⟨p,hy,hx⟩:=mem_biUnion.mp ((mem_filter.mp hj).2); cases p
       next p=> rw [mem_singleton.mp (inl_mem_disjSum.mp hy)] at hx; exact False.elim (hH (mem_filter.mpr ⟨hj,hx⟩))
       next p=> exact ⟨p,inr_mem_disjSum.mp hy,hx⟩
    change ∑ i∈V,m i*_ ≤ _; apply (sum_le_sum (s:=V) (fun i _=> cabs Y X hv hp ht i)).trans
    change ∑ i∈V,w i ≤ _; rw [← sum_sdiff (filter_subset _ _ : U⊆V)] -- replace
    have hZ : ∑ i∈U,w i≤u:=fromhome Y X h hv hp ht hr U x fun i hi=>(mem_filter.mp hi).2
    change (∑ i∈S,w i)+ ∑ i∈U,w i≤_
    rw [add_comm _ (∑ i∈U,w i)]
    apply add_le_add hZ
    let T:=(S.biUnion Car.bag).filter fun i=>x∈Y.bud i; let P j:=S.filter fun i=> j∈Car.bag i; let C:ℝ:=Animals.ballCost B
    have hx j (hj:j∈T): (∑ i∈P j,w i) ≤ (u*C) * (if x∈Y.bud j then p j*currency B (a+1) (Y.bud j) else 0):=by
       have he':=fromspur Y X h hv hp ht hr j (P j) (fun j hj=>(mem_filter.mp hj).2); rw [if_pos (mem_filter.mp hj).2]; apply he'.trans
       let V:=Y.bud j; let v:=coverNumber B V
       have h':(V.card:ℝ) ≤ v*C:= by unfold C; rw [← Nat.cast_mul]; exact Nat.cast_le.mpr (Corona.pays V B)
       have he'' :(V.card:ℝ) ≤C* Real.exp v:= h'.trans ((mul_comm _ C).le.trans (mul_le_mul_of_nonneg_left (((le_add_of_nonneg_right (zero_le_one : (0:ℝ) ≤ 1)).trans (Real.add_one_le_exp _))) (Nat.cast_nonneg _)))
       refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he'' (mul_nonneg (hv _) (Real.exp_pos _).le)) hU) (le_of_eq ?_)
       unfold currency; rw [add_mul, Real.exp_add, one_mul]; unfold v V; ring
    calc _≤∑ j∈T,∑ i∈P j,w i:=by
            simp_rw [P,sum_filter]; rw [sum_comm]; apply sum_le_sum; intro i hi; obtain ⟨j,hj,hT⟩:=he i hi; apply le_trans _ (single_le_sum (f:=fun k=> if k∈i.bag then w i else 0) (a:=j) (fun i _=>ite_nonneg (routing_nn Y X hv hp ht _) le_rfl) (mem_filter.mpr (And.intro (mem_biUnion.mpr ⟨i,hi,hj⟩) hT))); rw [if_pos hj]
         _≤_:= (sum_le_sum hx).trans (budget_sum (budget_scale (mul_nonneg hU (Nat.cast_nonneg _)) (H x)) _)
end YM.QCD.Ruby
