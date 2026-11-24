import YM.Lyre.Pillar
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills.Eden
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open QCD.Cove
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden Ribbon Cupola Plum Finset NormedSpace
open FlareV
variable {I J G A B:Type}[Fintype I][Fintype A](l:List J)(V:J→List I)(F:I→ Patio (A⊕Spine I))(K: Finset I→Patio (A⊕Spine I))(X: Patio A)(Q:I→Bool)
-- Tile correction lane operator
noncomputable def bindV (p:List I):= (p.toFinset.powerset.erase ∅)
noncomputable def allV (l: List J)(V:J→ List I):Finset (Finset I):=l.toFinset.biUnion (bindV∘V)
private lemma tl (x:J): allV (x::l) V=bindV (V x) ∪ allV l V:=by simp only [allV,List.toFinset_cons, biUnion_insert]; rfl
private lemma tlJ (x:J)(hv: (V x ++ (l.flatMap V)).Nodup): Disjoint (V x).toFinset (l.flatMap V).toFinset:= Finset.disjoint_left.mpr fun a h he=> (List.nodup_append.mp hv).2.2 _ (List.mem_toFinset.mp h) _ (List.mem_toFinset.mp he) rfl
lemma city (i:Finset I)(he:i∈ allV l V): i.Nonempty ∧ i ⊆ (l.flatMap V).toFinset:=by
   obtain ⟨u,hu,hz⟩:=mem_biUnion.mp he; change _ ∈bindV _ at hz; refine ⟨nonempty_iff_ne_empty.mpr (ne_of_mem_erase hz),fun x hx=>?_⟩; exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨_,List.mem_toFinset.mp hu,List.mem_toFinset.mp (mem_powerset.mp (mem_of_mem_erase hz) hx)⟩)
private lemma tlX (x:J)(hv: (V x++ (l.flatMap V)).Nodup): Disjoint (bindV (V x)) (allV l V):=by
   apply Finset.disjoint_left.mpr; intro i hi hp; obtain ⟨p,h⟩:=(city _ _ _ hp).1; exact Finset.disjoint_left.mp (tlJ l V x hv) (mem_powerset.mp (mem_of_mem_erase hi) h) ((city _ _ _ hp).2 h)
lemma packages (h:(l.flatMap V).Nodup):
     NormedSpace.exp (∑ i∈(l.flatMap V).toFinset,F i)* NormedSpace.exp (∑ t ∈ allV l V, K t) = (l.map fun j=> kits (V j).toFinset F K).prod:=by
   induction l with
   | nil=> simp [allV] -- layouts
   | cons a l ih=>
        rw [List.flatMap_cons] at h ⊢ ; rw [List.map_cons,List.prod_cons,kits,List.toFinset_append,tl,sum_union (tlJ l V a h), sum_union (tlX l V a h), ← ih (List.nodup_append.mp h).2.1,exp_add,exp_add]; unfold bindV; ring
lemma songC (h:(l.flatMap V).Nodup)(hp:(l.flatMap V).toFinset=univ)(hf:∀ i,Polite Q {i} (F i))(he:∀ i∈allV l V,Polite Q i (K i)):
   chants Q (l.flatMap V) A (rootR (Spine I) A X * NormedSpace.exp (∑ i:I,F i) * NormedSpace.exp (∑ t∈allV l V,K t))=
    (l.map fun j=> chants Q (V j) A (kits (V j).toFinset F K)).prod * X.val:=by
      let z:=rootR (Spine I) A X; let U:=NormedSpace.exp (∑ i:I,F i); let w:= NormedSpace.exp (∑ t∈allV l V,K t); let V₀ j:=kits (V j).toFinset F K
      have hP(i)(hi:i∈l): ValidPieces A Q (V i).toFinset (V₀ i):= tracked Q _ _ _ (fun i _=>hf i) (fun p h=>he _ (mem_biUnion.mpr ⟨i,List.mem_toFinset.mpr hi,mem_erase.mpr ⟨h.ne_empty,p.property⟩⟩)) -- defin membership
      have hZ: U*w=(l.map V₀).prod:=by have hx:=packages l V F K h; rw [hp] at hx; exact hx
      change chants Q _ _ (z*U*w)=_; rw [mul_assoc, hZ,mul_comm]; exact song Q l V _ hP h X -- elaborate
lemma correcting (hv:(l.flatMap V).Nodup)(hp:(l.flatMap V).toFinset=univ)(hf:∀ i,Polite Q {i} (F i))(he:∀ i∈allV l V, Polite Q i (K i))(w r:I→ℝ):
   chants Q (l.flatMap V) A (capstone A r (capstone A w (rootR (Spine I) A X* exp (∑ i:I,F i))) * exp (∑ t∈ allV l V,(give r t * give w t) • K t)) = (give r univ * give w univ) • ((l.map fun j=> chants Q (V j) A (kits (V j).toFinset F K)).prod * X.val):=by
   let L:= l.flatMap V; let t:= L.toFinset; have hL: crest L.get= univ:= (tops L).trans hp
   let W(v:I→ℝ):= capstone A v; let i:=allV l V; let Kx:= ∑ j∈i,K j; let X':= exp Kx
   have h (j:Finset I)(hj:j∈i): W r (W w (K j))=(give r j * give w j) • K j:=by
         unfold W; rw [patrol_open _ Q _ _ (he _ hj),map_smul,patrol_open _ Q _ _ (he _ hj),attuned,attuned,mul_smul,smul_comm (give ..)] -- sig
   let u:=rootR (Spine I) A X*exp (∑ i:I,F i); have hz: W r (W w X')=exp (∑ t∈ allV l V,(give r t * give w t) • K t):=by
         unfold X' Kx; rw [map_exp (W w) (W w).toLinearMap.toContinuousLinearMap.continuous, map_exp (W r) (W r).toLinearMap.toContinuousLinearMap.continuous, map_sum,map_sum]; apply congr_arg; exact sum_congr rfl h
   rw [← hz, ← songC l V F K X Q hv hp hf he]; change chants Q L A (W r (W w u)*W r (W w X'))= _ • chants Q L A (u*X')
   rw[← map_mul,←map_mul]; unfold chants W; rw [scale_read, scale_read,hL,mul_smul]
end YM.MassiveQCD.Sample.Quills.Eden
#print axioms YM.MassiveQCD.Sample.Quills.Eden.songC
#print axioms YM.MassiveQCD.Sample.Quills.Eden.correcting
