import YM.QCD.Ruby.Cash
/-! # sparks again; choices for COUNTING only -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}
variable (Y:Hue c N ι) (X:Rail c N β)
-- one anchor canonical assignment
structure Car where
 site : β
 bag : Finset ι
 closeD (j:ι) : j∈bag→ ¬ Disjoint (Y.bud j) (oriD X site)
namespace Car
variable {X Y} (T:Car Y X)
def sleeper : Cart ι β := disjSum {T.site} T.bag
def vat : Support c:=scopeK Y X T.sleeper
lemma shades : Ac.Spark (footD Y X) T.sleeper:= by
    let v:= T.sleeper; let Z:=footD Y X; let p: Stamp ι β:= .inl T.site; have hp:p ∈ v:=by simp [p,v,sleeper]
    have hv i (hi:i∈v): Ac.chain Z v p i:=by
       cases i with
       | inl i=>
          have h:i=T.site:=by simpa [v,sleeper] using hi
          rw [h]; exact .refl
       | inr i=> obtain ⟨j,hj,hk⟩:=not_disjoint_iff.mp (T.closeD i (inr_mem_disjSum.mp hi)); exact .single ⟨hp,hi,j,(X.addr _).part hk,hj⟩
    exact ⟨⟨_,hp⟩,fun i hi j hj=> Relation.ReflTransGen.trans (Ac.swaps _ (hv i hi)) (hv j hj)⟩ -- names inspect
lemma vice : gemD Y X T.sleeper:=by
    rw [gemD]; refine ⟨?_,by simp [sleeper],T.shades⟩; unfold suit; dsimp only [sleeper]; rw [toLeft_disjSum,toRight_disjSum]; refine ⟨?_,fun i hi=>?_⟩
    · intro i hi j hj he; exact False.elim (he (by rw [mem_singleton.mp hi,mem_singleton.mp hj]))
    simpa only [badgeK,toLeft_disjSum,singleton_biUnion] using T.closeD i hi -- name
end Car
section savvy
variable {Y X} (T: Plot Y X)
lemma person (j:↥T.1.toRight):∃ i:↥(T.1.toLeft), ¬Disjoint (Y.bud j.val) (oriD X i.val):=by
    obtain ⟨a,hx,hy⟩:=Finset.not_disjoint_iff.mp (T.2.1.2 j j.2) -- syntax
    obtain ⟨i,hi,hy⟩:=mem_biUnion.mp hy; exact ⟨⟨i,hi⟩, Finset.not_disjoint_iff.mpr ⟨_,hx,hy⟩⟩
noncomputable def scout (j:↥T.1.toRight): ↥T.1.toLeft:=(person T j).choose
noncomputable def auto (i:↥(T.1.toLeft)): Car Y X:=
   {site:=i.val
    bag:=(univ.filter (fun j=>scout T j=i)).image Subtype.val
    closeD:=fun j hj=>by obtain ⟨u,hu,rfl⟩:=mem_image.mp hj; exact (mem_filter.mp hu).2 ▸ (person T u).choose_spec }
def trip : Finset (Car Y X):= univ.image (auto T)
lemma tracked: (trip T).biUnion Car.sleeper= T.1 :=by
    ext i; simp only [trip,image_biUnion,mem_biUnion,mem_univ,true_and,comp_apply]; rcases i with i|i
    · constructor
      · rintro ⟨i',hi⟩; exact mem_toLeft.mp ((mem_singleton.mp (inl_mem_disjSum.mp hi)) ▸ i'.2)
      intro h; let w : ↥(T.1.toLeft):= ⟨i,mem_toLeft.mpr h⟩; exact ⟨w, inl_mem_disjSum.mpr (mem_singleton_self _)⟩
    simp only [Car.sleeper,auto,inr_mem_disjSum,mem_image,mem_filter,mem_univ,true_and]; constructor
    · rintro ⟨i',j,-,rfl⟩; exact mem_toRight.mp j.2
    intro hi; let j: ↥(T.1.toRight):= ⟨i,mem_toRight.mpr hi⟩; exact ⟨scout T j,j,rfl,rfl⟩
lemma isolation : (trip T:Set (Car Y X)).PairwiseDisjoint Car.sleeper:=by
    intro i hi j hj hn; obtain ⟨i,-,rfl⟩:=mem_image.mp hi; obtain ⟨j,-,rfl⟩:=mem_image.mp hj; refine Finset.disjoint_left.mpr (fun k hk hl=>?_); apply hn; apply congr_arg; rcases k with k|k
    · exact Subtype.ext ((mem_singleton.mp (inl_mem_disjSum.mp hk)).symm.trans (mem_singleton.mp (inl_mem_disjSum.mp hl)))
    obtain ⟨u,hu,hx⟩:=mem_image.mp (inr_mem_disjSum.mp hk); obtain ⟨v,hv,hy⟩:=mem_image.mp (inr_mem_disjSum.mp hl); have he:u=v:=Subtype.ext (hx.trans hy.symm); exact (mem_filter.mp hu).2.symm.trans (he.symm ▸ (mem_filter.mp hv).2)
lemma regiment : Ac.Spark (Car.vat (Y:=Y) (X:=X)) (trip T) :=by
    let A i:=Car.vat (Y:=Y) (X:=X) i
    let U:=T.val; let Z:=footD Y X; let t:=trip T; have hx:t.biUnion Car.sleeper=U:= tracked T
    have hP(c: Car Y X)(hc:c∈ t){i}(hi:i∈c.sleeper):i∈ U:=by rw [← hx]; exact mem_biUnion.mpr ⟨c,hc,hi⟩
    have hk:t.Nonempty:=by obtain ⟨u,hu⟩:=T.2.2.1; exact ⟨_,mem_image.mpr ⟨⟨u,hu⟩,mem_univ _,rfl⟩⟩
    refine ⟨hk,fun i hi j hj=>?_⟩
    obtain ⟨u,hu⟩:= (Car.shades i).1; obtain ⟨v,hv⟩:= (Car.shades j).1
    have he : ∀ l, Ac.chain Z U u l→∀ s: Car Y X,s∈ t→ l∈s.sleeper→Ac.chain A t i s:=by
       intro l H; induction H with
       | refl=> intro a ha he; suffices h:i=a from h ▸ .refl
                exact by_contra (fun hn=> Finset.disjoint_left.mp (isolation T hi ha hn) hu he) -- binder
       | @tail k b H h IH=>
          intro s hs ht; obtain ⟨hW,hM,w,hw,hv⟩:=h; rw [← hx] at hW; obtain ⟨x,hx,hk⟩:=mem_biUnion.mp hW; exact .tail (IH x hx hk) ⟨hx, hs,w, mem_biUnion.mpr ⟨k,hk,hw⟩, mem_biUnion.mpr ⟨b,ht,hv⟩⟩
    exact he v (T.2.2.2.2 u (hP i hi hu) v (hP j hj hv)) j hj hv
end savvy
end YM.QCD.Ruby
