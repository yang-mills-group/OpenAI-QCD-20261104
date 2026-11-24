import YM.Kly.Scad
import YM.MassiveBridge.Small
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
open Spread
variable (l r: Cluster F)(p:E4)(x:F.W)(hp: distinct (l++ (p,x):: r))
local notation "Sx" y:arg=> l++(p,y)::r
local notation "a"=> timeAxis
include hp
lemma spotsL(y:F.W): distinct (Sx y):=by
      apply locations.mpr; have hx:=locations.mp hp; simp only[List.map_append,List.map_cons] at hx ⊢; exact hx
lemma allotL :∃ t:E4,∃ d:ℝ≥0, ∀ y:F.W, Slab a d (carry (Sx y) t):=by
      obtain ⟨t,d,h⟩:= Spread.place_exists hp
      -- placement positions same; inherit
      have he(y:F.W): List.map Prod.fst (carry (Sx y) t) = List.map Prod.fst (carry (Sx x) t):=by simp only [carry,List.map_append,List.map_cons]
      refine ⟨t,d,fun y=> ⟨h.1,⟨?_,?_⟩,?_⟩⟩
      · exact still (spotsL l r p x hp y) _
      · intro i hi; have ht:i.1∈ List.map Prod.fst (carry (Sx x) t):=he y ▸ List.mem_map_of_mem (f:=Prod.fst) hi; obtain ⟨u,hu,h⟩:= List.mem_map.mp ht; rw[← h]; exact ‹Slab _ _ _›.2.1.2 u hu
      intro i hi; have ht: i.1 ∈ List.map Prod.fst (carry (Sx x) t):=he y ▸ List.mem_map_of_mem (f:=Prod.fst) hi; obtain ⟨u,hu,h⟩:=List.mem_map.mp ht; rw [← h]; exact ‹Slab _ _ _›.2.2 u hu
omit hp
lemma pinRe (t:E4)(d:ℝ≥0)(hx:Slab a d (carry (Sx x) t)) (u y:Future F a) : inner ℂ (V.GNS.plant u) (P.place d (carry (Sx x) t) (V.GNS.plant y))= oneIn (reflect u.val a ++ carry l t) (carry r t ++ raised a d y.val) (p+t) S x:=by
      rw [P.reads hx,V.GNS.measure]; change pointMoment S _=pointMoment S _; change pointMoment S (reflect u.val a++linked a d (carry _ _) _)=_; simp only [linked, distribute, List.append_assoc]; rfl
include H hp
lemma inL :∃ L:F.W→ₗ[ℂ]P.algebra,∀ y,L y=M P _ (spotsL l r p x hp y):=by
     obtain ⟨t,d,ht⟩:=allotL l r p x hp
     let L(y:F.W):=P.slot _ _ (ht y)
     refine ⟨{toFun:=L,map_add':=?_,map_smul':=?_},fun y=> (overline P H _ (spotsL l r p x hp y) t (ht y)).symm⟩
     · intro y z; have he : P.place d (carry (Sx (y+z)) t)= P.place d (carry (Sx y) t)+ P.place d (carry (Sx z) t):=by
           apply MatrixCap.op_ext; intro i j; rw [ContinuousLinearMap.add_apply,inner_add_right,pinRe P _ _ _ _ t d (ht _) i j,pinRe P _ _ _ _ t d (ht _) i j,pinRe P _ _ _ _ t d (ht _) i j,map_add]
       apply Subtype.ext; ext1 v; change V.D.orthogonalProjectionOnto (P.place d (carry _ t) _)= V.D.orthogonalProjectionOnto (P.place _ _ _)+ V.D.orthogonalProjectionOnto (P.place _ _ _); rw[he, ContinuousLinearMap.add_apply,map_add]
     intro s y; have he : P.place d (carry (Sx (s • y)) t)=s • P.place d (carry (Sx y) t):=by
           apply MatrixCap.op_ext; intro i j; rw [ContinuousLinearMap.smul_apply,inner_smul_right,pinRe P _ _ _ _ t d (ht _) i j,pinRe P _ _ _ _ t d (ht _) i j,map_smul]; rfl -- not.
     apply Subtype.ext; ext1 v; change V.D.orthogonalProjectionOnto (P.place d (carry (Sx (s • y)) t) _)= s • V.D.orthogonalProjectionOnto (P.place _ _ _); rw[he,ContinuousLinearMap.smul_apply,map_smul]
omit hp H
include hi
lemma mild (x:F.W):∃ p q:F.W,p+q=x∧ F.homogeneous false p∧ F.homogeneous true q:=by
     let c:ℂ:=2⁻¹; have h:= hi x
     refine ⟨c • (x+F.parity x),c • (x-F.parity x),?_,?_,?_⟩
     · rw[← smul_add,show x+F.parity x+(x-F.parity x)= (2:ℂ) • x from by rw[two_smul]; abel,smul_smul]; norm_num [c]
     · change F.parity _=_; rw[map_smul,map_add,h,add_comm]
     change F.parity _= -_; rw [map_smul,map_sub,h,←smul_neg, neg_sub]
include H
lemma growP(K:Submodule ℂ P.algebra)(hk:∀ x:List (Vose F),Light x →∀ h:distinct (plain x),M P (plain x) h∈ K)(v:Pack F):M₀ P v∈ K:=by
     suffices he:∀ r:Cluster F,∀ l:List (Vose F),Light l→∀ h:distinct (plain l++r),M P _ h∈K by exact he v.val [] (by simp[Light]) _
     intro r; induction r with
     | nil => intro l hl h; have hz: distinct (plain l):= List.append_nil (plain l) ▸ h; exact (show M P _ h=M P _ hz from by congr 1; simp) ▸ hk l hl hz
     | cons i r ih=>
          rintro l hl h; rcases i with ⟨p,x⟩; obtain ⟨L,hL⟩:=inL P H (plain l) r p x h
          have he(x₁:F.W)(b:Bool)(ho: F.homogeneous b x₁) : L x₁∈K:=by
               let w:= l++[(p,x₁,b)]; have hw:Light w:=by
                        intro i hi; obtain ht|hv:= List.mem_append.mp hi; exact hl _ ht; rw [List.mem_singleton.mp hv]; exact ho
               have hz:plain w++r=plain l++ (p,x₁)::r:=by unfold w plain; simp only[List.map_append,List.map_cons,List.map_nil, List.append_assoc,List.cons_append,List.nil_append]
               have h₀:= spotsL _ _ p x h x₁; rw [hL]
               exact (show M P _ (hz.symm ▸ h₀ : distinct (plain w ++ r))=M P _ h₀ from by congr 1) ▸ ih w hw _
          rw [←hL]; obtain ⟨y,z,hq,h1,h2⟩:=mild hi x; rw [←hq,map_add]; exact K.add_mem (he y false h1) (he z true h2)
omit hi
include ha hr R Y
lemma paceX (x y:List (Vose F))(hx:Light x)(hy:Light y)(hX:distinct (plain x))(hY:distinct (plain y)) :Commute (M P _ hX) (M P _ hY):=by
       by_cases ht:starb x=true
       · have h: M₀ P (⟨plain x,hX⟩:Pack F)=0:=odds P H Y R hr ha (⟨plain x,hX⟩:Pack F) x hx rfl ht; change Commute (M₀ P ⟨plain x,hX⟩) _; rw [h]; exact Commute.zero_left _
       have he:= toil P H Y R hr (⟨_,hX⟩) (⟨_,hY⟩) x y hx hy rfl rfl; simp only[show bin _ _=1 from (show bin (starb x) (starb y)=1 from (by cases starb y<;> simp [bin,Bool.eq_false_iff.mpr ht])), one_smul] at he; exact he
include hi
lemma pang (x y:Pack F):Commute (M₀ P x) (M₀ P y):=by
      let L(u:P.algebra):P.algebra→ₗ[ℂ] P.algebra:= LinearMap.mulLeft ℂ u-LinearMap.mulRight ℂ u
      have hp(u v:P.algebra): Commute u v↔v∈ (L u).ker:=by change _ ↔ u*v-v*u =0; rw[sub_eq_zero]; rfl
      have hv(i:List (Vose F))(h:Light i)(H':distinct (plain i)):Commute (M P _ H') (M₀ P x):= (hp ..).mpr (growP P H hi ((L (M P _ H')).ker) (fun z hz hT=> (hp ..).mp (paceX P H Y R hr ha i z h hz H' hT)) x)
      exact (hp ..).mpr (growP P H hi _ (fun z hz hT=> (hp ..).mp (hv z hz hT).symm) y)
lemma possible (x y:P.algebra):x*y=y*x:=by
    have hp (x y: V.VacuumOp)(hx:x∈P.generators)(hy:y∈P.generators) : x*y=y*x:=by
       obtain ⟨w,i,hx,h⟩:= hx; obtain ⟨u,t,hy,h'⟩:= hy; subst x y; have he:= (pang P H Y R hr hi ha ⟨_,hx.2.1.1⟩ ⟨_,hy.2.1.1⟩).eq; change (M P _ hx.2.1.1)* M P _ hy.2.1.1=_ at he; change M P _ hx.2.1.1*M P _ hy.2.1.1=M P _ hy.2.1.1*M P _ hx.2.1.1 at he; rw [spots P H hx,spots P H hy] at he; exact congr_arg Subtype.val he
    let U := StarAlgebra.adjoin ℂ P.generators
    haveI : IsMulCommutative U := StarAlgebra.isMulCommutative_adjoin ℂ (fun _ hx _ hy => hp _ _ hx hy)
       (fun _ hx y hy=>hp _ _ hx (by
            obtain ⟨w,i,h,hx⟩:=hy; rw [hx]; refine ⟨_,_, mirrorsSlab h,?_⟩; change ContinuousLinearMap.adjoint _= _; unfold Spread.atom; rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp, P.adjoints h Y hr, Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto]; rfl))
    letI:= U.commSemiringTopologicalClosure (fun i j=> IsMulCommutative.is_comm.comm i j); exact mul_comm (show U.topologicalClosure from x) (show U.topologicalClosure from y)
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.possible
#print axioms YM.Massive.Bridge.Kly.inL
