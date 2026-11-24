import YM.Kly.Olla
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open Fields (pointMoment distinct)
open OS (Cross)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff
variable {F:Fields}{S:F.Kernel}{V:Chamber S timeAxis} (P: Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S) (R:Angular S)
variable (hr: Involutive (F.adj timeAxis)) (hi:Involutive F.parity)(ha:∀ x:F.W,F.adj timeAxis (F.parity x)= F.parity (F.adj timeAxis x))
abbrev M₀(P:Spread V)(w:Pack F):P.algebra:=M P w.val w.property
abbrev dotP(x:Pack F):Pack F:= ⟨reflect x.val timeAxis,reflects timeAxis x.property⟩
include H Y hr
lemma travelled (x:Cluster F)(h:distinct x)(b:E4): M P x h=M P (carry x b) (still h b):=by
     obtain ⟨s,d,hs⟩:=Spread.place_exists (still h b); rw[overline P H _ (still h b) s hs]; have he:=overline P H _ h (b+s) (show Slab timeAxis d (carry x (b+s)) from paths x _ _ ▸ hs); exact he.trans (by congr 1; rw [paths])
lemma starM (x:Pack F) : star (M₀ P x)=M₀ P (dotP x):=by
     obtain ⟨s,d,hs⟩:=Spread.place_exists x.property
     have hS : opposite timeAxis d (carry x.val s)= carry (dotP x).val (Ortho.move (Signed.reflect timeAxis) s + (d:ℝ) • basis timeAxis):=by unfold opposite raised; rw[refl_over,paths]
     unfold M₀; rw [overline P H _ _ s hs]; have he: star (P.slot _ _ hs)=P.slot _ _ (mirrorsSlab hs):=by
            apply Subtype.ext; change ContinuousLinearMap.adjoint (P.atom _ _) = P.atom _ _; unfold Spread.atom; rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,P.adjoints hs Y hr, Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto]; rfl
     rw[he]; refine Eq.trans ?_ (overline P H _ _ _ (hS ▸ mirrorsSlab hs : Slab timeAxis d (carry (dotP x).val _))).symm; congr 1
include R
lemma toil (x y: Pack F)(B C:List (Vose F))(hb:Light B)(hc:Light C)(hB:plain B=x.val)(hC:plain C=y.val): M₀ P x*M₀ P y=bin (starb B) (starb C) • (M₀ P y*M₀ P x):=by
     let A:= M₀ P x; let D:= M₀ P y; let Fz:= bin (starb B) (starb C); let W:=Fz • (D*A)
     have he: DenseRange (V.D.orthogonalProjectionOnto ∘ V.GNS.stems) :=
        (show DenseRange _ from (show Surjective V.D.orthogonalProjectionOnto from
              fun p : V.D => ⟨_,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p⟩).denseRange).comp V.GNS.whole V.D.orthogonalProjectionOnto.continuous
     let L:= V.D.orthogonalProjectionOnto.toLinearMap.comp V.GNS.stems
     have hx(p: Future F timeAxis) : L (Finsupp.single p 1) = (M P p.val p.property.1).val V.omega0:=by unfold L; rw [LinearMap.comp_apply,Kernel.Gram.stems,Finsupp.linearCombination_single, one_smul, almost P H]; rfl
     have hp(p q:Voice F timeAxis): inner ℂ (L p) ((A*D).val (L q))=inner ℂ (L p) (W.val (L q)):=by
          induction q using Finsupp.induction_linear with
          | add i j hi hj=> simp only [map_add,inner_add_right,hi,hj]
          | zero=>simp
          | single i c=>
            rw [show Finsupp.single i c=c • Finsupp.single i (1:ℂ) from (by simp)]; simp only[map_smul,inner_smul_right,hx]; congr 1
            induction p using Finsupp.induction_linear with
            | add i j hi hj=> simp only [map_add,inner_add_left,hi,hj]
            | zero=>simp
            | single j s=>
               rw [show Finsupp.single j s=s • Finsupp.single j (1:ℂ) from (by simp),map_smul,inner_smul_left,inner_smul_left,hx]; let G:Pack F:=⟨_,j.property.1⟩; congr 1
               rw[← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_right ((M _ _ _).val), show (M P _ j.property.1).val.adjoint=(M₀ P (dotP G)).val from congr_arg Subtype.val (starM P H Y hr G)]; unfold W; change _= inner ℂ V.omega0 ((M₀ P (dotP G)).val (Fz • _)); rw [map_smul,inner_smul_right]; have he:=exchanges P H Y R (dotP G) x y (⟨_,i.property.1⟩) B C hb hc hB hC
               simp only[stage,starU,List.map_cons,List.prod_cons,List.prod_nil,List.map_nil,mul_one] at he; exact he
     apply Subtype.ext; refine DFunLike.coe_injective (he.equalizer (A*D).val.continuous W.val.continuous (funext fun x=>he.eq_of_inner_right ℂ fun y=> hp y x))
-- reflected odd
omit H Y R hr
include ha
abbrev doll (y:List (Vose F)):List (Vose F):= y.reverse.map fun i=> (Ortho.move (Signed.reflect timeAxis) i.1,F.adj timeAxis i.2.1,i.2.2)
lemma spotD (y:List (Vose F))(h:Light y): Light (doll y):=by
      intro p hp; obtain ⟨x,hx,rfl⟩:= List.mem_map.mp hp; have he:= h _ (List.mem_reverse.mp hx); rcases x with ⟨i,v,u⟩; cases u
      · change F.parity v=v at he; change F.parity _=_; rw[← ha,he]
      change F.parity v= -v at he; change F.parity _=_; rw [← ha,he,map_neg]
omit ha
lemma spotX (y:List (Vose F)): plain (doll y)=reflect (plain y) timeAxis:=by simp only [doll,plain,reflectedPoint,List.map_map,← List.map_reverse]; rfl
lemma billR(y:List (Vose F)): starb (doll y)=starb y:=by
     have h (x:Vose F)(l:List (Vose F)):starb (l++[x])=xor (starb l) x.2.2:=by
            induction l with
            | nil=>simp [starb]
            | cons i l ih=> change xor i.2.2 (starb (l++[x])) = xor (xor i.2.2 (starb l)) _; rw [ih]; cases h1:starb l <;> cases x.2.2 <;> cases i.2.2 <;> simp
     induction y with
     | nil=> rfl
     | cons i l ih=> unfold doll; simp only[List.reverse_cons, List.map_append,List.map_cons,List.map_nil]; rw [h]; change xor (starb (doll l)) i.2.2=xor i.2.2 (starb l); rw [ih]; cases starb l <;> cases i.2.2 <;>rfl
include H Y R ha hr
lemma odds (x: Pack F)(B:List (Vose F))(hb:Light B)(hB:plain B=x.val)(hQ:starb B=true): M₀ P x=0:=by
     have he:= toil P H Y R hr x (dotP x) B (doll B) hb (spotD ha B hb) hB (show plain (doll B)=_ from (spotX _).trans (by rw [hB]))
     rw [billR,hQ, show bin true true= (-1:ℂ) from rfl, neg_one_smul ℂ,← starM P H Y hr] at he
     let K:V.VacuumOp:= (M₀ P x).val
     have ht : K*K.adjoint=-(K.adjoint*K):= congr_arg Subtype.val he
     apply Subtype.ext; refine ContinuousLinearMap.ext fun i=>?_ ; have hx:inner ℂ (K i) (K i)=-(inner ℂ (K.adjoint i) (K.adjoint i)):=by rw [← ContinuousLinearMap.adjoint_inner_right K.adjoint, ← ContinuousLinearMap.adjoint_inner_right K]; simp only [ContinuousLinearMap.adjoint_adjoint]; change _= -(inner ℂ i ((K*K.adjoint) i)); rw[ht,ContinuousLinearMap.neg_apply,inner_neg_right,neg_neg]; rfl
     change K i=0; apply (re_inner_self_nonpos (𝕜:=ℂ)).mp; rw [hx,map_neg]; exact neg_nonpos.mpr inner_self_nonneg
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.odds
#print axioms YM.Massive.Bridge.Kly.starM
#print axioms YM.Massive.Bridge.Kly.toil
