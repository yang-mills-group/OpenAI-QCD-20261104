import YM.Lyre.Path
/-! replicate seminorm on physical bare placements -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter QCD QCD.Lat QCD.RP QCD.Tide QCD.Grass Lattice Wilson NormedSpace
open Chess Cells Romance Plum Finset
open scoped Topology ComplexOrder BigOperators Matrix.Norms.L2Operator Classical
variable {A:Type*}{F:ℕ}{n:Side} (T:Cells.Tiling n)(R:Regulator n F)
noncomputable def loom (T:Cells.Tiling n)(f:T.Cell→Stud n F):Stud n F:= (Finset.univ.toList.map f).prod
noncomputable abbrev topH (x:Stud n F)(p:T.Cell):ℝ:= Lyre.Array.root (T:=T) R (fun (_:Unit)=> palmH T x p) ()
lemma top_nn (x:Stud n F)(p:T.Cell):0 ≤ topH T R x p:=Real.rpow_nonneg (norm_nonneg _) _
lemma top_blank(p:T.Cell)(h:R.Z≠0):topH T R 1 p=1:=by
   unfold topH Array.root Array.cost Array.use; simp [palmH,road_one, blank R h]
lemma top_power(p:T.Cell)(x:Stud n F):topH T R x p^Fintype.card T.Cell=‖valueH R (loom T (palmH T x p))‖:=Lyre.Array.powering _
lemma manyH(h:T.kind=.link)(x:T.Cell→ Stud n F)(he:∀ i,Fence (T.chamber i) (x i) ∧ Lyre.Potion (x i))(hp:R.t=0)(hR:0 ≤ R.β)(hL:4 ≤ n.val):‖valueH R (loom T x)‖ ≤ ∏ i:T.Cell,topH T R (x i) i:=by
     let X(i v:T.Cell):= palmH T (x i) i v; have hZ:=Lyre.Array.tiles (T:=T) (K:=X) id (booked T R h id x (fun i=>(he i).1) (fun i=>(he i).2)) hp h hR hL; unfold Array.cost Array.use at hZ; rw [show (fun i=>X (id i) i)=x from funext fun i=>palm_at (x i) T i] at hZ; exact hZ
variable (hp:T.kind=.link)
variable [Fintype A] (x:A→Stud n F) (c:A→T.Cell)
include hp
lemma wardsP (hc : Injective c)(L:List A)(hr:L.Nodup)(hk:∀ i,i∈L)(hx:∀ i,Plum.Fence (T.chamber (c i)) (x i) ∧ Lyre.Potion (x i))(hR:R.t=0)(he:0 ≤ R.β)(hL:4≤ n.val)(hv:R.Z≠0): ‖valueH R (L.map x).prod‖ ≤ ∏ i:A, topH T R (x i) (c i):=by
   let f (i:T.Cell):Stud n F:= if h:∃ j,c j=i then x (Classical.choose h) else 1
   have hf(i): f (c i)= x i:=by unfold f; rw [dif_pos ⟨i,rfl⟩]; exact congr_arg x (hc (Classical.choose_spec (show ∃ j,c j=c i from ⟨i,rfl⟩)))
   let s:=univ.image c
   have h(i:T.Cell)(ht:i∉s): f i=1:= dif_neg (fun ⟨j,hj⟩=> ht (mem_image.mpr ⟨_,mem_univ j,hj⟩))
   have hP(i:T.Cell): Fence (T.chamber i) (f i) ∧ Lyre.Potion (f i):=by
       by_cases ht:i∈s
       · obtain ⟨j,-,rfl⟩:=mem_image.mp ht; rw [hf]; exact hx j
       rw [h i ht]; exact ⟨Plum.Fence.one,false, fun i=> by simp [Hom, Plus]⟩
   let C:=(sᶜ).toList;
   have h1:List.Perm ((L.map c) ++ C) (univ:Finset T.Cell).toList:=by -- syntax replace
       refine (List.perm_ext_iff_of_nodup (List.nodup_append.mpr ⟨hr.map hc,nodup_toList _,?_⟩) (nodup_toList _)).2 ?_
       · intro i hi j hj he; subst j; obtain ⟨j,-,rfl⟩:= List.mem_map.mp hi; have hu:=mem_compl.mp (mem_toList.mp hj); exact hu (mem_image.mpr ⟨j,mem_univ j,rfl⟩)
       intro i; by_cases hz:i∈s
       · obtain ⟨j,-,rfl⟩:= mem_image.mp hz; exact iff_of_true (List.mem_append.mpr (.inl (List.mem_map.mpr ⟨j,hk j,rfl⟩))) (by simp)
       exact iff_of_true (List.mem_append.mpr (.inr (mem_toList.mpr (mem_compl.mpr hz)))) (by simp)
   let B (i:T.Cell)(j:T.Cell):= palmH T (f i) i j
   have h₂ (l:List T.Cell): Lyre.Array.use T l B id=(l.map f).prod:= by
       unfold Lyre.Array.use; congr 2; funext i; exact palm_at ..
   have h₃ : (C.map f).prod=1:=List.prod_eq_one (by rintro i hi; obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hi; exact h v (mem_compl.mp (mem_toList.mp hv))) -- name?
   have h₄: Chess.SignedEq (L.map x).prod (loom T f):= by
       have hL:= Lyre.Array.rearrange id (K:=B) (booked T R hp id f (fun i=>(hP i).1) (fun i=>(hP i).2)) _ _ h1; rw [h₂,h₂,List.map_append,List.prod_append,List.map_map, h₃,mul_one,(show f∘c=x from funext hf)] at hL; exact hL --  namespace
   rw [signsV R h₄]; apply (manyH T R hp f hP hR he hL).trans_eq; rw [← Finset.prod_subset (Finset.subset_univ s)]; change (∏ i∈univ.image c,topH T R (f i) i)=_; rw [Finset.prod_image hc.injOn]; simp_rw [hf]
   intro i hi he; rw [h i he, top_blank T R i hv] -- replace
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.wardsP
