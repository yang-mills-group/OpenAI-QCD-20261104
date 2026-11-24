import YM.Eole.Bloc
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
variable (A)(q:I→Bool) (W: Bloc I J) (l: List J)
namespace Bloc
local notation "u"=> W.flag q
local notation "X"=>Patio (A⊕Spine I)
local notation "Y"=>Patio (A⊕Spine J)
local notation "bp"=> Ribbon.burst u l.toFinset
set_option quotPrecheck false
local notation "L"=> numbered q A (W.twins l).get
local notation "t"=> signG u l.get
noncomputable def sector : Patio (A⊕Spine I) →L[ℂ] Patio (A⊕Spine J):= LinearMap.toContinuousLinearMap (((stake A (burst (W.flag q) l.toFinset)).comp ( (signG (W.flag q) l.get) • (numbered q A (W.twins l).get))).toLinearMap.codRestrict ((roomA (A⊕Spine J)).toSubmodule) (fun i=>
     even_stake _ _ (W.tape q l.toFinset |>.symm ▸ W.stowed l ▸ ((power q (W.twins l) i).smul _))))
local notation "Lk"=>sector A q W
lemma nice (x:X): Polite u l.toFinset (sector A q W l x):= ⟨_,rfl⟩
lemma liver (x:X): pluck A bp (Lk l x)= t • L x:= quid ..
variable (hl:l.Nodup)
include hl
lemma decalEq (x:X): numbered u A l.get (Lk l x)=numbered q A (W.twins l).get x:=by
    let P:= L x; let h:= arm_bill u _ (List.nodup_iff_injective_get.mp hl); change t • pluck A _ _ = _; rw [← decal,liver, ←mul_smul,h.2.1,one_smul]
lemma barrel (x:X) : (Lk l x).val=Ribbon.fiber (Spine J) (L x)*quill A (armature u l.get):=by rw [← decalEq A q W l hl x]; exact charge A u l.get _ (decal l ▸ nice A q W l x) (List.nodup_iff_injective_get.mp hl)
omit hl in
lemma singleton_eval (Q:I→Bool)(i:List I)(x y:X)(hx:Polite Q i.toFinset x) (hy:Polite Q i.toFinset y) (hz:i.Nodup)(hp: numbered Q A i.get x=numbered Q A i.get y):x=y:=Subtype.ext (by rw [charge A Q i.get _ (decal i ▸ hx) (List.nodup_iff_injective_get.mp hz),charge A Q i.get _ (decal i ▸ hy) (List.nodup_iff_injective_get.mp hz),hp]) -- include hl remove.
variable (k:List J)
lemma linkedE (h:l.Perm k) : Lk l=Lk k:=by
    obtain ⟨v,-,h1,h2⟩:= W.signpost q l k h hl
    have ht:crest (W.twins l).get=crest (W.twins k).get:=by rw [← decal,← decal,W.stowed,W.stowed]; exact congr_arg _ (List.toFinset_eq_of_perm _ _ h)
    have hv : t= v • signG u k.get:=by unfold signG; rw [← decal l,← decal k,(List.toFinset_eq_of_perm _ _ h),h1,map_smul]
    have he : signG q (W.twins l).get=v • signG q (W.twins k).get:=by unfold signG; rw [ht,h2,map_smul]
    let h':=arm_bill u l.get (List.nodup_iff_injective_get.mp hl); let hx:=arm_bill u k.get (List.nodup_iff_injective_get.mp (h.nodup hl)); have hT:v*v=1:=by have hz:=h'.2.1; rw [hv,smul_eq_mul,show v*_*_= (v*v)*(signG u k.get * signG u k.get) by ring,hx.2.1,mul_one] at hz; exact hz
    ext1 x; apply Subtype.ext; rw [barrel A q W l hl,barrel A q W k (h.nodup hl),h1]; unfold numbered; simp only [ContinuousLinearMap.smul_apply]; rw [he,ht,smul_eq_mul,mul_smul,map_smul (quill A),map_smul (Ribbon.fiber _),smul_mul_assoc,mul_smul_comm,smul_smul,hT,one_smul]
omit hl
lemma append (hx:X)(hy:X)(h1:Polite q (W.plant l.toFinset) hx)(h2:Polite q (W.plant k.toFinset) hy)(hk:(l++k).Nodup) : Lk (l++k) (hx*hy)= Lk l hx * Lk k hy:=by
    have hd:= (List.pairwise_append.mp hk); have he:W.twins (l++k)=W.twins l++W.twins k:=List.flatMap_append
    apply singleton_eval A u (l++k) _ _ (nice A q W _ _)
    · rw[List.toFinset_append]; exact (nice A q W _ _).attached (nice A q W _ _)
    exact hk
    rw [decalEq _ _ _ _ hk, penalty u l k _ _ (nice A q W l hx) (nice A q W k hy) hk,decalEq _ _ _ _ hd.1, decalEq _ _ _ _ hd.2.1,he]; exact penalty q _ _ _ _ ((W.stowed l).symm ▸ h1) ((W.stowed k).symm ▸ h2) (he ▸ W.tightened _ hk)
noncomputable abbrev lane (s: Finset J) := Lk s.toList
lemma arranged (h:l.Nodup): lane A q W l.toFinset=Lk l:=by
    let s:= l.toFinset; exact linkedE A q W s.toList s.nodup_toList l (List.perm_of_nodup_nodup_toFinset_eq s.nodup_toList h (toList_toFinset s)) -- inspect
lemma overlay (s:Finset J)(hx: X) : Polite u s (lane A q W s hx):= by simpa [lane] using nice A q W s.toList hx
lemma ribs (s v:Finset J)(h:Disjoint s v)(x y:X)(hx: Polite q (W.plant s) x)(hy:Polite q (W.plant v) y) : lane A q W (s∪v) (x*y)=lane A q W s x*lane A q W v y:=by
     let i:=s.toList; let j:=v.toList; have hh : (i++j).Nodup:=List.pairwise_append.mpr ⟨s.nodup_toList,v.nodup_toList,fun _ hp _ ht he=> disjoint_left.mp h (he ▸ mem_toList.mp hp) (mem_toList.mp ht)⟩
     have hg:(i++j).toFinset=s∪v:=by simp[i,j]
     rw [show lane A q W (s ∪ v)=Lk (i++j) from (congr_arg _ hg.symm).trans (arranged A q W _ hh)]
     apply append _ _ _ _ _ _ _ _ _ hh; simp only [i,toList_toFinset]; exact hx
     simp only [j,toList_toFinset]; exact hy
end Bloc
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Bloc.decalEq
#print axioms YM.MassiveQCD.Sample.Eole.Bloc.ribs
