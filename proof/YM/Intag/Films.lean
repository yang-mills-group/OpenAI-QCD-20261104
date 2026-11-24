import YM.Intag.Ground
import YM.Magi.Rest
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Set Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Romance QCD MassiveQCD.Cupola MassiveQCD.Cape MassiveQCD.Cape.LampV
open scoped BigOperators Classical
namespace Film
variable {p q l:Side}(r:Ratio p q)(s:Ratio q l)(g:Ratio p l)(he:Odd s.count.val)
-- no pressure alignment assumptions. sticker leases budget by tile.Be covered at chamber interior.
include he
lemma chin (x y:Site l) : s.count.val*separation (s.parent x) (s.parent y) ≤ s.count.val+separation x y:=by
   rw [← both]; let p:=s.embed (s.parent x); let q:=s.embed (s.parent y); have hp:2*separation x p < _:= midway _ he x; have hh:2*separation y q < _:= midway _ he y; have h:=separation_triangle p x q; rw [separation_comm p x] at h; have hv:= separation_triangle x y q; change separation p q ≤ _; omega
lemma drum (x y:Site l) : separation x y ≤ s.count.val + s.count.val*separation (s.parent x) (s.parent y):=by
   rw [← both]; let p:=s.embed (s.parent x); let q:=s.embed (s.parent y); have hp:2*separation x p < _:= midway _ he x; have hh:2*separation y q < _:= midway _ he y; have h:=separation_triangle x p y; have hv:= separation_triangle p q y; rw [separation_comm q y] at hv; change separation _ _ ≤ _ +separation p q; omega
open Finset
variable {I: Type}[Fintype I](X: I→ Site l)(f:I→Site p)(hw:Even p.val)(hn:Odd g.count.val)(z:Site l){M:ℕ}
variable (hM:∀ i,X i∈ (mural g hw z).margin (f i) M)
-- pressure t.Any projections capacities precharged by only polygon cardinal BEFORE L. no L.P factor.
include hM he hn r
lemma near (i j:I)(h:s.parent (X i)=s.parent (X j)): separation (f i) (f j) ≤ 2:=by
    let a:=z+g.embed (f i); let b:=z+g.embed (f j); let d:=g.count.val; have ha:d*separation (f i) (f j)=separation a b:=by unfold a b; rw [add_comm z,add_comm z,separation_translate,both]
    have hi: separation (X i) a +M ≤ d/2:= (key_margin g z (X i) _ hw hn M).mp (hM i); have hj: separation (X j) b+M ≤ d/2:=(key_margin _ _ _ _ hw hn M).mp (hM j); have ht:= drum s he (X i) (X j); rw [h,separation_self,mul_zero,add_zero] at ht; have hv:s.count.val ≤ d:=by unfold d; rw [size_comp r s]; exact Nat.le_mul_of_pos_right _ r.count.property
    apply Nat.le_of_mul_le_mul_left _ (show 0<d from g.count.property)
    rw [ha]; have hx:=separation_triangle a (X i) b; rw [separation_comm a (X i)] at hx; have hy:=separation_triangle (X i) (X j) b; omega
-- Ω partition universal. Orientation paths l. tuple separation only needed via htM margin.
variable {k b B:ℕ}
lemma ports (hc:Fires f k) (hi:k*625 ≤ b) : Fires (s.parent ∘ X) b:=by
     intro i
     let t:=univ.filter (fun j:I=>(s.parent ∘ X) j=i)
     change t.card ≤ b; by_cases ht:t.Nonempty; swap; · rw [Finset.not_nonempty_iff_eq_empty.mp ht,Finset.card_empty]; omega
     obtain ⟨j,hj⟩:= ht
     let A:= halo 2 {f j}; let P (k: Site p) := univ.filter (fun i => f i=k)
     have hv:t⊆ A.biUnion P:=by
         intro y hy; refine mem_biUnion.mpr ⟨f y,halo_spec.mpr ⟨f j,mem_singleton_self _, near r s g he X f hw hn z hM j y (((mem_filter.mp hj).2).trans ((mem_filter.mp hy).2).symm)⟩,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
     have hw:A.card ≤ 625:=by apply le_trans (Corona.halo_size _ _); norm_num
     exact le_trans ((Finset.card_le_card hv).trans ((card_biUnion_le ..).trans ((sum_le_sum (g:=fun _=>k) (fun i _=>hc i)).trans (by rw [sum_const,nsmul_eq_mul']; exact Nat.mul_le_mul_left _ hw)))) hi -- simp nsmul'
omit hM he hn r
include he
lemma apert_ineq {x y:Site l} (hx: s.count.val*(B+1) ≤ separation x y): B ≤ separation (s.parent x) (s.parent y):=by -- need x,y variable
    have ht:= hx.trans (drum s he x y); rw [mul_add,mul_one,add_comm s.count.val] at ht; exact Nat.le_of_mul_le_mul_left (le_of_add_le_add_right ht) s.count.property
include he hM hn
lemma garden (Y:Finset (Finset I))(hx:∀ v∈Y, v.card≤ k)(hs:Fires f k)(hz:∀ s:Finset I,s.Nonempty→(s.image f).card ≤1→ s∈Y)(h:s.count.val*(B*B+1) ≤2*M) : ClusteredE f Y k B (s.parent ∘ X):=by
    refine ⟨hx,hs,hz,fun i j hi=> apert_ineq s he (h.trans (le_of_lt ?_))⟩
    have ht:=crimp g z (f i) hw hn (hM i) (hM j) hi; rwa [two_mul]
omit hM hn
open MassiveQCD.Play.Camp
lemma sparks (Y:Finset (Finset I))(α:ℕ)(hp:∀ v∈Y,∀ i∈v,∀ j∈v,separation (X i) (X j)≤ s.count.val)(hα: 2≤ α) (t:Finset I)(hh:t∈ Y)(hx:t.Nonempty): Ac.Spark (Ray (s.parent∘ X) α) t:=by
      refine ⟨hx,fun i hi j hj=>.single ⟨hi,hj, (s.parent∘X) j,(portion ..).mpr ?_,by apply (portion ..).mpr; rw [separation_self]; omega⟩⟩
      apply le_trans _ hα; apply Nat.le_of_mul_le_mul_left (le_trans (chin s he (X i) (X j)) ?_) s.count.property
      rw [mul_two]; exact Nat.add_le_add_left (hp t ‹_› i hi j hj) _
end Film
end YM.Intag
#print axioms YM.Intag.Film.sparks
#print axioms YM.Intag.Film.ports
#print axioms YM.Intag.Film.garden
