import YM.Kly.Girt
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open OS (Cross)
open Fields (pointMoment distinct)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder
open MassiveTwoEstimates Spinor Spinor.Lift
variable {F:Fields} {S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){X:Bases F}{M':Momentum F}(U:X.Content C M')
variable {n:ℕ}(x:Points n)(v:Fin n→F.W)
local notation "t₀"=>timeAxis
local notation "Ω"=> P.algebra
variable (A:V.VacuumOp →L[ℂ]ℂ) (X': P.algebra→⋆ₐ[ℂ]ℂ)(hX:Continuous X')
local notation "G"=> bloom P H X'
variable (ha:∀ x:F.W,F.adj t₀ (F.parity x)=F.parity (F.adj t₀ x))
variable (hL:∀ i:Axis,∃ p:EuPin,Leads F i p)
include Y H P
lemma virgin : M₀ P (⟨[],(air t₀ (F:=F)).property.1⟩:Pack F)=1:=by
      unfold M₀; rw [spots P H (vacuum_width (d:=1) zero_lt_one)]; apply Subtype.ext; change P.atom [] 1=1; unfold Spread.atom; rw[P.blank zero_lt_one]; ext1 x; change V.D.orthogonalProjectionOnto (V.flow.E 1 x.val)=x; rw[(V.flow.fixed _).1 x.property]; exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
lemma nilE: (G 0 0 0)=1:=by
      rw [←readAt,Simp_nil, bless P H X' [] (air t₀ (F:=F)).property.1,show M P [] _= _ from virgin P H Y,map_one]
where Simp_nil : realize (n:=0) (F:=F) 0 0=[]:=by simp [realize]
lemma wins (l L:Cluster F)(x y:Plant F)(h: distinct (l++ x::y::L))(p q:Bool)(hp:F.homogeneous p x.2)(hq:F.homogeneous q y.2): pointMoment G (l++x::y::L)= (if p&&q then -1 else 1)*pointMoment G (l++y::x::L):=by
     let A:=l++x::y::L; let B:=l++y::x::L; have hB:distinct B:=locations.mpr ((List.Perm.map Prod.fst (show A.Perm B from List.Perm.append_left _ (List.Perm.swap ..))).nodup (locations.mp h)); let k:= bin p q
     rw [bless P H X' A h,bless P H X' B hB,show M P A h=k • M P B hB from ?_, show X' (k • _)= _ from X'.toAlgHom.toLinearMap.map_smul k (M P B hB)]; rfl
     obtain ⟨b,d,hd⟩:= Spread.place_exists h; let f:=carry A b; let g:=carry B b; have hg:Slab t₀ d g:=by
           have he:f.Perm g:=(List.Perm.append_left _ (show (x::y::L).Perm (y::x::L) from List.Perm.swap ..)).map _; exact ⟨hd.1,⟨still hB b,fun i hi=>hd.2.1.2 i (he.mem_iff.mpr hi)⟩,fun i hi=>hd.2.2 i (he.mem_iff.mpr hi)⟩
     rw [overline P H A h b hd, overline P H B hB b hg]; apply Subtype.ext; have ht:P.place d f = k • P.place d g:=by
           apply MatrixCap.op_ext; intro i j; rw [ContinuousLinearMap.smul_apply,inner_smul_right,P.reads hd,P.reads hg,V.GNS.measure,V.GNS.measure]; let w:=reflect i.val t₀; let r:=raised t₀ d j.val; let X':Plant F:=(x.1+b,x.2); let Y':Plant F:=(y.1+b,y.2); have hA:w++(entering hd j).val=(w++carry l b)++X'::Y'::(carry L b++r):=by simp only[w,entering,A,linked,distribute,List.append_assoc]; rfl
           have hS:w++(entering hg j).val=(w++carry l b)++Y'::X'::(carry L b++r):=by simp only[w,entering,g,B,linked,distribute,List.append_assoc]; rfl
           change pointMoment S (w++ (entering hd _).val)=_*pointMoment S (w++(entering hg j).val); rw[hA,hS]; exact Y.swap _ _ X' Y' (hA ▸ twoSides i.property (entering hd j).property) p q hp hq
     change Cpr (P.place d f)= k • (Cpr (P.place d g)); rw [ht,map_smul]
include E
lemma trivialUnit (l:Cluster F)(x:E4)(h: distinct ((x,F.unit)::l)): pointMoment G ((x,F.unit)::l)=pointMoment G l:=by
     let z:= (x,F.unit)::l; have hv:distinct l:=locations.mpr (List.Nodup.of_cons (locations.mp h)); obtain ⟨s,d,ht⟩:= Spread.place_exists h; let w:= carry l s; have hE:carry z s=(x+s,F.unit)::w:=rfl; have he: Slab t₀ d w:=⟨ht.1,⟨still hv s,fun p hp=> ht.2.1.2 p (hE ▸ List.mem_cons_of_mem _ hp)⟩,fun p hp=> ht.2.2 p (hE ▸ List.mem_cons_of_mem _ hp)⟩
     rw[bless P H X' _ h,bless P H X' l hv,overline P H _ h s ht,overline P H l hv s he]; refine congr_arg _ (Subtype.ext (show P.atom (carry z s) d=_ from ?_))
     have hQ:P.place d (carry z s)= P.place d w:=by
          refine MatrixCap.op_ext fun i j=>?_ ; rw [P.reads ht,P.reads he,V.GNS.measure,V.GNS.measure]; exact Unary.unit_point E Y (reflect i.val t₀) (w++raised t₀ d j.val) (x+s) (twoSides i.property (entering ht j).property)
     unfold Spread.atom; rw [hQ]; rfl
lemma cardOne(x:Points (n+1))(h:x∈conf _): G _ x (Fin.cons F.unit v)= G n (Points.tail x) v:=by
     rw [← readAt,← readAt]; have hP: realize (Fin.cons F.unit v) x=(x 0,F.unit)::realize v (Points.tail x):=by unfold realize; simp[List.ofFn_succ]; rfl
     rw[hP]; apply trivialUnit P H Y E X' _ _ (hP ▸ (realized ..).2 h)
include U R ha
lemma voyage (p:EuPin)(u:p.IsRotation)(hx:x∈ conf _): G _ (points fun i=> Ortho.move p.coord (x i)) (F.action p ∘ v)= G n x v:=by
     have h:= hail P H Y R E U X' ha p (realize v x) ((realized _ _).2 hx) u; rw [← readAt,← readAt]; refine (congr_arg (pointMoment G) (show realize _ _= _ from (?_ : realize (F.action p ∘ v) (points fun i=> Ortho.move p.coord (x i))=rotate (realize v x) p))).trans h; unfold rotate realize; rw[List.map_ofFn]; rfl
lemma foldT (hx:x∈conf n) : G _ x (F.parity ∘ v)=G _ x v:=by
     obtain ⟨p,hp,hz⟩:= SpinGeometry.geometry.euBoth 1; change (1:Ortho)=p.coord at hp; change p.matrix= -1 at hz; rw [← E.sign _ hp.symm hz]; have h:= voyage P H Y R E U x v X' ha p (show p.IsRotation from (show older p.coord=1 from by rw[←hp,older_one])) hx; apply Eq.trans ?_ h; apply congr_arg (fun x:Points n=>G n x (_)); ext i; simp[← hp]
include hL
lemma refl (p:Cluster F)(hx:distinct p)(i:Axis): pointMoment G (Fields.reflect (F:=F) i p)=star (pointMoment G p):=by
     obtain ⟨g,hg⟩:= hL i; change pointMoment G (Bridge.reflect p i)=_
     rw [← hail P H Y R E U X' ha g p hx hg.crest,← hail P H Y R E U X' ha g (reflect p i) (reflects _ hx) hg.crest, rotR R hg]; let v:= rotate p g; have ht:distinct v:= (trans R hx g).1; change pointMoment G (reflect v t₀)=star (pointMoment G v); rw[bless P H X' _ (reflects _ ht),bless P H X' _ ht,show M P _ _=star (M P v ht) from (starM P H Y (E.reflected _) ⟨_,ht⟩).symm, map_star]
include hX
lemma rising (hF:∀ x:F.W, x≠0 →∃ r:ℝ,0<r∧0<G 2 (points ![0,r • basis t₀]) ![F.adj t₀ x,x]): Fields.Euclidean G:=by refine ⟨fun n x hx s v=>travels P H x v X' hx s,fun n x hx p hu v=>voyage P H Y R E U _ v X' ha p hu hx,fun i x h=>refl P H Y R E U X' ha hL x h i,fun n x hx v=>foldT P H Y R E U x v X' ha hx, wins P H Y X',nilE P H Y X', fun n x hx v=> cardOne P H Y E v X' x hx, fun n u x hx=>(cross P H Y E _ u _ hX hx).contDiffWithinAt, fun n u j=>echelon P H Y E u _ hX j, fun n u i x hx b=>elements P H Y E _ u _ hX (i,b) hx, fun i=>incense P H Y R E U X' ((hL i).choose_spec) ha, fun i=>sober P H Y R E U X' ((hL i).choose_spec) ha, hF⟩
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.rising
