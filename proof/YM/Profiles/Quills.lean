import YM.Oars.Mountain
import YM.Profiles.Sparkle
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D' :Type}[Fintype I][Fintype J]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j:ℕ}
namespace Quills
open ProfileL
variable {n' :ℕ} {A:Type}[Fintype A](q:I→Bool) (s:Fin n→I)
local notation "K"=>Spine I
-- precise sign including braid through odd x's. reversed glyph order deliberate (tail even)
noncomputable def crest (x:Fin n→I):Finset I:=Finset.univ.image x
noncomputable def armature (u:Fin n→I): Alg (Spine I):=(List.ofFn fun i:Fin n=>Grass.mono (burst q ({u i}:Finset I))).reverse.prod
set_option quotPrecheck false
local notation "bp"=> burst q (crest s)
local notation "X"=> Patio (A⊕K)
noncomputable def signG (s: Fin n→I) : ℂ:= Grass.coef (burst q (crest s)) (armature q s)
noncomputable def numbered (A:Type)[Fintype A](s:Fin n→I): Patio (A⊕Spine I)→L[ℂ] Alg A:= signG q s • pluck A (burst q (crest s))
local notation "H"=> numbered q A s
omit [Fintype I] in
lemma exists_fix (j:I):j∈crest s ↔ ∃ k,s k=j:=by simp [crest]
lemma crest_next (s:Fin (n+1)→I) : crest s= insert (s 0) (crest (Fin.tail s)):=by
   ext j; rw [mem_insert,exists_fix,exists_fix]; constructor; · rintro ⟨k,rfl⟩; exact Fin.cases (.inl rfl) (fun i=>.inr ⟨_,show Fin.tail s i=s i.succ from rfl⟩) k
   rintro (h|⟨k,rfl⟩); exact ⟨0,h.symm⟩; exact ⟨k.succ,rfl⟩
lemma arm (s:Fin (n+1)→I): armature q s=armature q (Fin.tail s)*mono (burst q {s 0}):=by
    unfold armature; rw [List.ofFn_succ,List.reverse_cons,List.prod_append,List.prod_singleton]; rfl -- singleton.
lemma arc (hF:Injective s): let g:=mono bp; armature q s=g∨armature q s=-g:=by
    induction n with
    | zero=>left; simp [armature,crest,Ribbon.burst_absent] -- inspect
    | succ n ih=>
       let z:=insert (s 0) (crest (Fin.tail s)); rw [arm,crest_next]; let X':=Fin.tail s; have hX:s 0 ∉ crest X':=fun hx=>
           ((exists_fix X' _).1 hx).elim fun i hi=>Fin.succ_ne_zero i (hF hi)
       let P₀:=crest X'; let x:=burst q ({s 0}:Finset I); let v:=burst q P₀; have hd: Disjoint v x:=(Ribbon.crossedR q P₀ {s 0}).2 (disjoint_singleton_right.mpr hX); have hP:= Grass.mono_mul_sign _ _ hd; rw [Finset.disjUnion_eq_union,show v ∪ x=burst q z by rw [show v∪x=burst q (P₀∪{s 0}) from (Ribbon.pulver ..).symm]; exact congr_arg (burst q) (by rw [union_comm,singleton_union])] at hP -- may not find concrete
       rcases ih X' (hF.comp (Fin.succ_injective _)) with hx|hx <;> change mono _*_= _ ∨ mono _*_ = _ at hP <;> change armature q X' * _ = _ ∨ armature q X' *_ = _ -- prepare
       · rw [hx]; exact hP
       rw [hx,neg_mul]; rcases hP with hP|hP; exact Or.inr (congr_arg (-·) hP); exact Or.inl ((neg_eq_iff_eq_neg).2 hP)
lemma arm_bill (hF:Injective s) : ‖signG q s‖=1 ∧ signG q s * signG q s=1 ∧ mono bp=signG q s • armature q s:=by
    rcases arc q s hF with hx|hx <;> simp only [signG,hx, Grass.read,map_neg] <;> simp
variable (A)
lemma emptyN (s:Fin 0→I)(x:Patio (A⊕Spine I)) : numbered q A s x= pluck A ∅ x:=by
    unfold numbered signG crest armature; simp only [List.ofFn_zero,List.reverse_nil,List.prod_nil]; simp [Ribbon.burst_absent, ← mono_empty] -- simp loops?
lemma singleN (s:Fin 1→I) (x:Patio (A⊕Spine I)): numbered q A s x=pluck A (burst q ({s 0})) x:=by
    unfold numbered signG; simp [armature,crest] -- adjust
lemma charge (x:X)(hp: Polite q (crest s) x)(hF:Injective s): x.val=fiber K (H x)*quill A (armature q s):=by
    let X':=armature q s; let h:= arm_bill q s hF; nth_rw 1 [← hp.exact]; unfold numbered; rw [markedOut,h.2.2,map_smul]; change _= fiber K ((signG q s) • pluck _ _ x)* _; rw [map_smul,mul_smul_comm,smul_mul_assoc]; rfl
-- coefficient pluck by reading product of even material right quills reversed.
lemma cuts (s:Fin n→I)(h:Injective s)(u:X)(x:Alg A) (hu:u.val=fiber K x*quill A (armature q s)): numbered q A s u=x:=by
    have hT:= arm_bill q s h; let z:=signG q s; let v:= pluck A (burst q (crest s)) u; have hp:z • v=x:=by
        have he: z • u.val= stake A (burst q (crest s)) x:=by rw [hu,markedOut,hT.2.2,map_smul,mul_smul_comm]
        exact ((map_smul (scrape _ _) z u.val).symm.trans (congr_arg _ he)).trans (quid ..)
    exact hp
end Quills
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Quills.charge
