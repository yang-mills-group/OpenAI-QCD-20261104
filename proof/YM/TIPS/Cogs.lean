import YM.TIPS.Bing
import YM.TIPS.Fall
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby
open YM.QCD YM.MassiveQCD
open Function MeasureTheory Filter Lattice Finset Kit
open QCD Kites Lat Ribbon Plate Grass QCD.Cove MassiveQCD.Sample MassiveQCD.Sample.Quills Cupola
open scoped Topology BigOperators ContDiff Classical
variable {I J:Type} [Fintype I]{N n k:ℕ}{c:Side}
variable (q:I→Bool)(R:I→Grid c→ Lat.Fields c 6)(W:Tones c I)(w:I→ℝ)
-- one source contract without RIP.Area.T.Temp
lemma sift1 (f:Fin 1→I) (s:Finset I)(h:s⊆Quills.crest f):Quills.spliceG q f s=1:=by
   let x:= f 0; have hp:Quills.crest f={x}:=by simp [crest,x]
   have hx(f':Fin 1→I): signG q f'=1:=by simp [signG,crest,armature] -- adapt
   have he(a:Finset I): Quills.armature q (tour a) = _root_.id (Quills.armature q (tour a)):=rfl
   have h₁ : armature q f= mono (burst q (Quills.crest f)):=by have hg:= (arm_bill q f (fun _ _ _=>Subsingleton.elim ..)).2.2; rw [hx,one_smul] at hg; exact hg.symm
   have ho:armature q (tour ({x}:Finset I))= mono (burst q {x}):=by
       let a:=(tour ({x}:Finset I)); have ha:signG q a=1:=hx (a)
                                                                          -- avoid var dependencies.Abst universal Fin lengths
       have ht:= (arm_bill q a (snug _)).2.2; rw [show crest a={x} from club _,ha,one_smul] at ht; exact ht.symm
   have hh: armature q (tour (∅:Finset I))=1:=by simp [armature]
   -- avoid rw hp under tour depends.Gen ok
   unfold spliceG; rw [hx,one_mul,hp]; rcases Finset.subset_singleton_iff.mp (hp ▸ h) with hl|hl <;> subst s; · rw [sdiff_empty,hh,ho,mul_one]; exact Grass.read ..
   rw [sdiff_self,show (⊥:Finset I)=∅ from rfl,ho,hh,one_mul]; exact Grass.read ..
-- use direct data RW C sees.Of.Tr.T Comparison.
lemma faceT (f:Fin 1→I) : nurture c q R W 1 f = W 1 f+R (f 0)*W 0 (fun i:Fin 0=>Fin.elim0 i) :=by
    funext V; let x:= f 0; let T:=Quills.crest f; have hp:T={x}:=by simp [T,x,Quills.crest]
    unfold nurture; rw [show crest f =_ from hp]; rw [show ({x}:Finset I).powerset={∅,{x}} from ?_]; swap; · ext i; simp only [mem_insert,mem_powerset,mem_singleton,Finset.subset_singleton_iff]
    rw [sum_insert (show (∅:Finset I)∉ ({ {x}}:Finset (Finset I)) from (by simp)),sum_singleton, sift1 q f ∅ (empty_subset _), sift1 q f {x} (show {x}⊆ Quills.crest f from subset_of_eq hp.symm), one_smul,one_smul]; rw [sdiff_empty,sdiff_self,show (⊥:Finset I)=∅ from rfl]
    have hv: (tour {x}) = f:= by
       funext i; have hk: tour {x} i∈ Quills.crest (tour {x}):=mem_image_of_mem _ (mem_univ _); rw [club] at hk; exact (mem_singleton.mp hk).trans (show x=f i from congr_arg _ (Subsingleton.elim ..))
    have he: (tour (∅:Finset I))=fun i=> (Fin.elim0 i):=by ext i; exact Fin.elim0 i -- name
    change (List.ofFn (n:=0) _).prod* W 1 _ V+(List.ofFn (n:=1) _).prod * W 0 _ V= W 1 f V+R x V* _
    rw [show W 1 _ V=W 1 f V from (congr_arg (fun v:Fin 1→I=> W 1 v V) hv), show W 0 _ V=_ from congr_arg (fun v:Fin 0→I=> W 0 v V) he]; change (List.ofFn (n:=0) _).prod * _ + (List.ofFn (n:=1) (fun i=>R (tour {x} i) V)).prod * _= _; simp only [hv,List.ofFn_zero,List.prod_nil,one_mul,List.ofFn_succ, List.prod_cons,mul_one]; rfl
-- scaling if s inj
lemma peeks (f:Fin k→I) (h:Injective f) : Talent.realize w f= ∏ i∈crest f,(↑(w i):ℂ):=by unfold Talent.realize crest; rw [prod_image h.injOn]
lemma pure_tones (s:Fin n→I)(V:Grid c)(X:I→ℝ): (List.ofFn (fun i=> (X (s i):ℂ) • R (s i) V)).prod= Talent.realize X s • (List.ofFn (fun i=> R (s i) V)).prod:=by
    induction n with
    | zero=>simp [Talent.realize]
    | succ n ih=> rw[List.ofFn_succ,List.prod_cons,List.ofFn_succ (n:=n),List.prod_cons,show (List.ofFn (fun i:Fin n=> (X (s i.succ):ℂ) • R (s i.succ) V)).prod=_ from ih (Fin.tail s),show Talent.realize X s= (↑(X (s 0)):ℂ)* Talent.realize X (Fin.tail s) from Fin.prod_univ_succ _,smul_mul_assoc,mul_smul_comm,mul_smul]; rfl -- edit
lemma tonnage (s:Fin n→I)(ht:Injective s): (Talent.scale w (nurture c q R W)) n s=nurture c q (fun i=> (w i:ℂ) • R i) (Talent.scale w W) n s:=by
    funext V; unfold nurture Talent.scale; rw [Pi.smul_apply,smul_sum]; apply sum_congr rfl; intro t ht'; rw [smul_comm]; apply congr_arg
    let u:=Quills.crest s \ t; let m:=u.card; let s₀:=Quills.tour t; let s₁:=Quills.tour u
    have hf:Talent.realize w s=Talent.realize w s₁*Talent.realize w s₀:= by rw [peeks _ _ ht,peeks _ _ (snug _),peeks _ _ (snug _), show Quills.crest s₁=u from club _, show crest s₀=t from club _]; exact (prod_sdiff (f:=fun i=>(↑(w i):ℂ)) (mem_powerset.mp ht')).symm
    simp_rw [Pi.smul_apply]; rw [show (List.ofFn _).prod = _ from pure_tones R s₀ V w]; change Talent.realize _ _ • _ = (Talent.realize w s₀ • (List.ofFn (fun i=>R (s₀ i) V)).prod)*(Talent.realize w s₁ • W m s₁ V); rw [hf,mul_smul,← smul_mul_assoc,mul_smul_comm]
end YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.faceT

#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.tonnage
