import YM.Intag.Reclaim
/-!
# exterior commercial expression and acl sum budgets.Exact correction inverse. Word independent of volume profile.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber Apron Cupola
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
open YM.Arise.Bill YM.Arise.Count YM.Massive YM.Massive.UV Quills.Eden
variable {A B I J:Type}[Fintype A][Fintype B][Fintype I][Fintype J]{n:ℕ}
namespace Clover
variable (Q:I→Bool)(v:I→ℕ)(P: ∀ i:I, Arise.Bill.Cups (v i) (Q i))(p:I→ E4)
local notation "Z"=> pays (U:=A) Q v p P
-- canonical spine-only coefficients.Meet actual metrics whenever injective.Inter.Ar.
variable (i:Finset I) -- remove
local notation "R"=> Spine I
local notation "Kv" i:arg=> Quills.tour i
noncomputable def freeCost (i:Finset I):ℂ:= UV.Free.moment (v∘ Quills.tour i) (points (p∘ Quills.tour i)) (fun j=> meaning _ _ (P (tour i j)))
noncomputable def arms (i:Finset I): Alg (Spine I) := freeCost Q v P p i • armature Q (tour i)
lemma fingers (hp:Set.InjOn p (i:Set I))(A:Type)[Fintype A]: ((pays (U:=A) Q v p P) i).val= quill A (arms Q v P p i):=by
      let s:=tour i; have ht: crest s=i:=club i; have hi(j:Fin i.card):s j ∈ i:=ht ▸ (exists_fix ..).2 ⟨j,rfl⟩
      have hv:points (p∘s)∈conf i.card:=fun x y h=> snug i (hp (hi _) (hi _) h)
      have h:= colored Q v p s P (snug i) hv (U:=A); rw [ht] at h; change _=quill A (_•_); unfold pays; rw [h,map_smul,map_one,smul_mul_assoc,one_mul,map_smul]; rfl -- lhs reduction issue
private lemma backup (i:Alg (Spine I)): embed (Sum.elim (Fin.elim0 (α:=Spine I)) id) (quill (Fin 0) i)=i:=by rw [quill,embed_comp]; change embed id i=_; rw [embed_id]; rfl
lemma arms_up(hp:Set.InjOn p (i:Set I)): Plus (arms Q v P p i):=by
    let W:= pays (U:=Fin 0) Q v p P i; let Y:= arms Q v P p i; have hz:quill (Fin 0) Y=W.val:=(fingers Q v P p i hp (Fin 0)).symm; have he:quill (Fin 0) (grade Y)=quill (Fin 0) Y:= (embed_grade ..).symm.trans (hz ▸ W.property)
    change grade Y=Y; nth_rw 1 [← backup (grade Y)]; rw [he,backup]
noncomputable def cupZ (i:Finset I) : Patio (Spine I):= if h:Set.InjOn p (i:Set I) then ⟨arms Q v P p i,arms_up Q v P p i h⟩ else 0
variable (T:Finset I)(h:Set.InjOn p T)
local notation "F"=> cupZ Q v P p
include h
lemma earn_l (ht:i⊆ T):Honest Q i ((cupZ Q v P p) i)∧∀ (A:Type)[Fintype A], qraft A _ ((cupZ Q v P p) i)=(pays (U:=A) Q v p P i):=by -- binder incorrect
     have hh:Set.InjOn p (i:Set I):= h.mono ‹_›
     have hx(A:Type)[Fintype A]: qraft A _ ((cupZ Q v P p) i)=(pays (U:=A) Q v p P i):=by rw [cupZ,dif_pos hh]; exact Subtype.ext (fingers Q v P p i hh A).symm
     refine ⟨fun A b=> (?_),hx⟩; rw[hx]; exact canon Q p P T h i ‹_›
lemma cents (L:Finset I)(ht:L⊆ T): Honest Q L (cetacea (cupZ Q v P p) L)∧ ∀ (A:Type)[Fintype A],qraft A _ (cetacea (cupZ Q v P p) L)=cetacea (pays (U:=A) Q v p P) L:=by
    have he(A:Type)[Fintype A]:= honorG Q T (cupZ Q v P p) (fun i h'=> (earn_l Q v P p i T h h').1) L ht ∅ A (pays (U:=A) Q v p P) (fun i hi=> (earn_l Q v P p i T h hi).2 A|>.symm);
    exact ⟨(he Unit).1,fun A h=>(he A).2.symm⟩
omit h
-- part typed lists.Space. cost decomposition ANY subword. norm estimates symbolic in Wick continuum.Measures.
noncomputable def fareZ (i:Finset I): Patio (Spine I):= NormedSpace.exp (∑ t∈ i.powerset.erase ∅, -cetacea (cupZ Q v P p) t)
local notation "B!"=> fareZ Q v P p
noncomputable def scalarZ (X: Patio (Spine I))(i:Finset I):ℂ:= signG Q (tour i)*QCD.Grass.coef (burst Q i) X.val
noncomputable def compZ (L:List I)(t: Finset I) : ℂ:= spliceG Q L.get t * scalarZ Q (fareZ Q v P p L.toFinset) (L.toFinset\ t)
lemma chambers (J:Patio (Spine I))(i: Finset I)(A:Type)[Fintype A]: numbered Q A (tour i) (qraft A _ J)= scalarZ Q J i • (1:Alg A):=by
     let X:= J.val; let V(t):= scrape A t (fiber (Spine I) (1:Alg A) * quill A X); change signG Q _ • pluck A _ _ = _
     rw [show crest (tour i)=i from club i]; let z:=burst Q i
     change signG Q _ • scrape A z (quill A X) = _; rw [show quill A X=fiber R (1:Alg A)*quill A X from (by rw[map_one,one_mul]), plucks A, smul_smul]; rfl
include h
lemma purse_h : qraft A _ (fareZ Q v P p T)= NormedSpace.exp (∑ t∈ T.powerset.erase ∅, -cetacea Z t):=by
     let b:= qraft A (Spine I); unfold fareZ; rw [map_exp b b.toLinearMap.toContinuousLinearMap.continuous,map_sum]; apply congr_arg; refine sum_congr rfl fun i hi=>?_; rw [map_neg]; exact congr_arg _ ((cents Q v P p T h i (mem_powerset.mp (mem_of_mem_erase hi))).2 A)
lemma reality : ValidPieces A Q T (qraft A _ (fareZ Q v P p T)):=by
     have h':ValidPieces A Q T (kits T (fun _=> 0) (fun i=>-cetacea Z i)):=by
           apply tracked _ _ _ _ (?_) (?_)
           · intro i hi; exact ⟨0,(map_zero _).trans rfl⟩
           intro i hi; obtain ⟨hp,hz⟩:= cents Q v P p T h i (mem_powerset.mp i.property); change Polite Q i.val _; rw [← hz A]; exact (hp A).minus
     rw[purse_h Q v P p T h]; unfold kits at h'; rwa [sum_const_zero, NormedSpace.exp_zero,one_mul] at h'
omit h
variable (L:List I)(hL:L.Nodup)(U:I→Alg A)(hU:∀ i,Hom (Q i) (U i))(ht:Set.InjOn p L.toFinset)
local notation "Q!"=> wordA Q p v U hU P L
local notation "Xt"=> L.toFinset
include hL ht
lemma testH : Q! = ∑ i∈ L.toFinset.powerset, compZ Q v P p L i • (List.ofFn (U ∘tour i)).prod:=by
     let S:=L.get; let x(j:I):= if j∈Xt then U j else 0; have hx(j:I):Hom (Q j) (x j):=by
           unfold x; split; next h=> exact hU _
           next h=> cases Q j <;> simp [Hom,Plus,Minus]
     let y(j:I):= YM.Massive.Lyre.emitK Q j (x j) (hx j); let V:=qraft A _ (fareZ Q v P p Xt); have hv :Q! = numbered Q A S (NormedSpace.exp (∑ j:I,y j)*V):=by
          unfold wordA kits chants; rw [show V= _ from purse_h Q v P p Xt ht]; apply congr_arg; congr 2
          rw [← sum_subset (f:=y) (Finset.subset_univ Xt)]; · exact sum_congr rfl (fun j hj=> by apply Subtype.ext; exact congr_arg (stake A _) (show U j=x j from (if_pos hj).symm))
          intro i hi hp; apply Subtype.ext; change stake A _ _=_; rw [show x i=0 from if_neg hp,map_zero]; rfl
     have hp:=Quills.serveV A Q S y x V (fun _=>rfl) ((reality Q v P p Xt ht (A:=A)).raise (Finset.subset_univ Xt)); have hz: crest S=Xt:= tops L; rw [hv, hp,hz]; apply sum_congr rfl; intro i hi; rw [chambers Q];
     have hκ(j:Fin i.card): tour i j∈ i:= (i.equivFin.symm j).property
     rw [show List.ofFn (fun j=>x (tour i j))=List.ofFn (U∘tour i) from congr_arg (fun s: Fin i.card→Alg A=>List.ofFn s) (funext fun j=>if_pos ((mem_powerset.mp hi) (hκ j)))]; rw [mul_smul_comm,mul_one,smul_smul]; rfl
end Clover
end YM.MassiveQCD.Sample.Quills
#print axioms YM.MassiveQCD.Sample.Quills.Clover.testH
