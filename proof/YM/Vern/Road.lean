import YM.Vern.Plush
import YM.Vern.Pier
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Filter Set
open scoped Topology BigOperators Classical ComplexOrder InnerProductSpace
variable {W:Type*}[AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W]
variable (G D:Tide W)
def Twin (P Q:Module.End ℂ W):Prop:=∀ x y,G.knot (P x) y= G.knot x (Q y)
lemma wheels :∃ E:W≃ₗ[ℂ]W, (∀ x y,D.knot (E x) (E y)=G.knot x y)∧ ∀ X Y:Module.End ℂ W, Twin G X Y→ Twin D X Y →∀ x,E (X x) = X (E x):=by
      let c:= G.coreP; letI : InnerProductSpace.Core ℂ W:= c
      letI :NormedAddCommGroup W:= c.toNormedAddCommGroup
      letI :PreInnerProductSpace.Core ℂ W:=c.toCore
      letI :InnerProductSpace ℂ W:= .ofCore c.toCore
      obtain ⟨P,hp,h⟩:= coins D; obtain ⟨E,hE,hs⟩:= barG D P hp h; refine ⟨E,hE,fun X Y hu hY=>hs X (fun x=>?_)⟩
      -- because symmetric positive. detect difference
      suffices hv:∀ v:W, G.knot (P (X x)-X (P x)) v=0 by
           apply sub_eq_zero.mp; exact ((inner_self_eq_zero (𝕜:=ℂ)).mp (hv _))
      intro v
      have hz:G.knot (P (X x)) v=G.knot (X (P x)) v:=by
                 rw [show G.knot (P (X x)) v=_ from (h _ _).symm,hY x v,hu (P x) v]; exact h _ _
      rw[sub_eq_add_neg,G.other,show G.knot (-X (P x)) v= -(G.knot (X (P x)) v) from ?_,hz,add_neg_cancel]; nth_rw 1 [← neg_one_smul ℂ]; rw [G.seals]; simp
-- conclusion Qk iso X→W such that G0 measure.Knows g.Stab. close original for X.V. uses trans K. choose subseq.
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][FiniteDimensional ℂ X]
variable {I:Type*}(S:ℕ→Tide W)(G0:Tide X)(B:ℕ→ X≃ₗ[ℂ] W) (p: I→Module.End ℂ W) (q:I→Module.End ℂ X)
variable (hS:∀ i:I, ∃ t:Module.End ℂ W,∀ k,Twin (S k) (p i) t)
variable (hB:∀ x y:X,Tendsto (fun k=> (S k).knot (B k x) (B k y)) atTop (𝓝 (G0.knot x y)))(ht:∀ i x,Tendsto (fun k=>(B k).symm (p i (B k x))) atTop (𝓝 (q i x)))
noncomputable def Tide.pullX (T:Tide W)(F:X≃ₗ[ℂ] W): Tide X:=by
    refine { knot:=fun x y=>T.knot (F x) (F y), positive:=fun x hx=>T.positive _ (fun h=> hx (F.injective (h.trans (F.map_zero).symm))), con:=fun x y=>T.con _ _,add:=fun x y z=>?_,sep:=fun c x y=>?_} <;> first|(rw [_root_.map_add,T.add])|(rw [_root_.map_smul,T.sep])
include hS hB ht
lemma tides:∃ (f:ℕ→ℕ)(F:ℕ→ X ≃ₗ[ℂ] W),StrictMono f ∧ (∀ x,Tendsto (fun k=>(B (f k)).symm (F k x)) atTop (𝓝 x)) ∧ (∀ x,Tendsto (fun k=>(F k).symm (B (f k) x)) atTop (𝓝 x)) ∧ (∀ i j: X,∀ k,(S (f k)).knot (F k i) (F k j)= G0.knot i j)∧∀ k i x,F k (q i x)=p i (F k x):=by
      choose E hE hπ using fun k=> wheels (S 0) (S k)
      let Tp(i):= (E i).trans (B i).symm; have he(k:ℕ)(i:I)(x:W): p i (E k x)= E k (p i x):=by obtain ⟨u,h⟩:=hS i; exact (hπ k _ u (h 0) (h k) x).symm
      obtain ⟨f,Q,hf,hQ,h⟩:= tended G0 (S 0) (fun k=>(S k).pullX (B k)) (fun x y=>hB x y) Tp (fun i x y=>by
                 change (S i).knot (B i ((B i).symm _)) (B i ((B i).symm _))=_; rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]; exact hE i x y)
      let A(k i):Module.End ℂ X:= (B (f k)).symm.toLinearMap ∘ₗ p i ∘ₗ (B (f k)).toLinearMap
      have hs(i:I)(x:W):q i (Q x)=Q (p i x):=by
           apply tendsto_nhds_unique (Iceberg.follows_L (fun k=>A k i) (q i) (fun v=>(ht i v).comp hf.tendsto_atTop) _ _ (hQ x)); refine (hQ (p i x)).congr' (Eventually.of_forall fun k=>?_); change _= (B _).symm (p i (B _ ((B _).symm _))); rw [LinearEquiv.apply_symm_apply]; exact congr_arg ((B _).symm) (he _ i x).symm
      let Ψ(k:ℕ):= Q.symm.trans (E (f k)); let U(k:ℕ):= (Ψ k).trans (B (f k)).symm; have hv(x:X):Tendsto (fun k=> (U k) x) atTop (𝓝 x):= by
                have hh:=hQ (Q.symm x); rwa [Q.apply_symm_apply] at hh
      refine ⟨f,Ψ,hf,hv,fun x=>?_,fun i j k=>?_,fun k i x=>?_⟩
      · let u:=(fun k=> (U k).symm x); have hp: Tendsto u atTop (𝓝 x):=by
           let B:=Module.finBasis ℂ X
           refine Iceberg.costW (fun j k=>B.coord j ∘ₗ (U k).toLinearMap) B.coord ?_ ?_ u x ?_
           · intro i p; exact (B.coord i).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hv p)
           · intro v h; rw [←B.sum_repr v]; change ∑ i,(B.coord i v) • _= _; simp[h]
           intro i; apply tendsto_const_nhds.congr'; apply Eventually.of_forall; intro k; change _= B.coord i (U k (u k)); unfold u; rw [LinearEquiv.apply_symm_apply]
        exact hp
      · change (S _).knot (E _ _) (E _ _)=_; rw [hE, ←h]; change G0.knot (Q (Q.symm i)) (Q (Q.symm j))= _; rw[Q.apply_symm_apply,Q.apply_symm_apply]
      obtain ⟨x,rfl⟩:= Q.surjective x; rw[hs]; simp [Ψ,he]
end YM.Vern
#print axioms YM.Vern.tides
