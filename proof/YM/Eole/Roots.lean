import YM.Eole.Flight
import YM.Eole.Rate
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
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
local notation "N"=> E⊕K
-- nodes indexed full exponent E and fully decomposed forced.
open QCD.GasP QCD.Struck
variable (W:Bloc I J) (g:E⊕K→ Finset I) (Y:K→Hat c)
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
local notation "κ"=> Keys c 6
variable (q:I→ Bool) {P:BudgetPoint} {v α b t:ℝ}
open Further.ShellBirth49.Fusing Collide
variable (o:I→Site c)(p:J→Site c)
-- E raw footprint and common extensions
local notation "M"=> Patio ((Keys c 6)⊕Spine I)
local notation "Mt"=> Patio ((Keys c 6)⊕Spine J)
local notation "λt"=>W.flag q
variable (old:E→Support c)(a:E⊕K→Support c)(f:E⊕K→ Grid c→ Patio ((Keys c 6)⊕Spine I))(z:E⊕K→ℝ)
local notation "P₀"=> Grid c
set_option quotPrecheck false
local notation "T"=>P.threshold
local notation "A'"=>day f
local notation "H'"=>night old f T
local notation "S'"=> Support c
include W
variable (h:Setting W g Y q o p old a f z P t)
include h
open ConnectedActivityE6 Blaze King
local notation "L"=> Cand W g Y
local notation "G"=> Hard W g Y
local notation "Jr"=>journal W g q f
local notation "μ"=> lunarZ W g q old f
variable {ν w β δ y:ℝ}
local notation "F'"=> feather W g Y q o p old a f z h
local notation "Z₀"=> hats W g Y
local notation "WZ"=> Stretch.Basin (feather W g Y q o p old a f z h) (hats W g Y) P.threshold
local notation "FP"=> Stretch.Vital
local notation "ρ"=> token
local notation "χ"=> ample 6 J
local notation "V!"=> vacR (Spine J) κ
local notation "X!"=> withdraw 6 p t
variable {η T' μs:ℝ}
open Push.AbsoluteSums.Trees
variable (hv:1 ≤ t)
include hv
lemma dawnV (i:Hard W g Y)(hx:(glowT W g i.val).Nonempty)(U:Grid c) : V! (X! ((F').warp i U))=0 :=by exact Stags.lifter 6 p (W.flag q) t _ hx _ (coinV W g Y q o p old a f z h (zero_lt_one.trans_le hv) i U)
-- K0 produced by vac of old. Input j with g(.inr j)=∅ actual.L.Volume all
abbrev Rootπ(W:Bloc I J) (g:E⊕K→ Finset I):= {j:K // g (.inr j)=∅} -- W unused
noncomputable abbrev seeds(j: Rootπ W g) : Hard W g Y:= ⟨{Sum.inr j.val},by
     have hd:g (.inr j.val)=∅:= j.property
     refine ⟨⟨(?_:spark _ _),?_ ,?_⟩,⟨_,mem_toRight.mpr (mem_singleton_self _)⟩⟩ -- type inferred
     · exact ⟨singleton_nonempty _,fun i hi k hk=> by rw[mem_singleton.mp hi,mem_singleton.mp hk]; exact Relation.ReflTransGen.refl⟩
     · simp[mural,bins,Bloc.plant,glowT,Bloc.core,hd]
     intro i hp k ht he; rw [mem_coe,mem_toRight,mem_singleton] at hp ht; exact False.elim (he (Sum.inr_injective (hp.trans ht.symm)))⟩
noncomputable def ridgeQ : Rootπ W g ↪ Hard W g Y:= ⟨seeds W g Y,fun i j h=> Subtype.ext (Sum.inr_injective (Finset.singleton_injective (Subtype.ext_iff.mp h)))⟩
lemma identifies (i:G) (hi: i ∉ Set.range (ridgeQ W g Y)) : (glowT W g i.val).Nonempty:=by
    by_contra hz; have hx:= not_nonempty_iff_eq_empty.mp hz; rw [← tiles] at hx; obtain ⟨k,hk⟩:= i.2.2; let A:=i.val; have hk':Sum.inr k∈A:=mem_toRight.mp hk
    have hF j (hp:j∈A): g j=∅:=eq_empty_iff_forall_notMem.mpr (fun x' h=> by have hk : W.unit_ x'∈ _ :=mem_biUnion.mpr (show ∃ i∈A,W.unit_ x'∈tags W g i from ⟨j,hp,mem_image_of_mem W.unit_ h⟩); change W.unit_ x'∈ A.biUnion (tags W g) at hk; rw[hx] at hk; exact notMem_empty _ hk)
    have hh (j)(hj:j∈A): Sum.inr k=j:=by
         have ht:= i.2.1.1.2 _ hk' j hj; let Px:= tags W g
         generalize hh:Sum.inr (α:=E) k=l at ht ⊢
         induction ht with
         | refl=>rfl
         | tail _ h _=> obtain ⟨h1,h2,x,u,v⟩:= h; simp [tags,Bloc.core,hF _ h1] at u
    apply hi; let j:Rootπ W g:= ⟨k,hF _ hk'⟩; refine ⟨j,Subtype.ext ?_⟩; ext i; rw [show (ridgeQ W g Y j).val= {Sum.inr k} from rfl,mem_singleton]; exact ⟨fun hi=> hi.symm ▸ hk',fun ht=>(hh _ ht).symm⟩
-- any root.O support equals
variable (hp_root:∀ (j:Rootπ W g),a (.inr j.val)=(Y j.val).place)
include hp_root
lemma rootedT (j:Rootπ W g): (feather W g Y q o p old a f z h).addr (ridgeQ W g Y j)= Y j.val∧ (hats W g Y (ridgeQ W g Y j))= Y j.val:=by
    have he (A B:Hat c)(H:A.place=B.place)(V:A.inv=B.inv):A=B:=by cases A; cases B; congr
    have hx: flagsOf Y {(Sum.inr j.val:E⊕K)}=(Y j.val).inv:=by unfold flagsOf; rw[show ({Sum.inr j.val}:Finset (E⊕K)).toRight= {j.val} from by ext; simp, singleton_biUnion]
    exact ⟨he _ _ ((singleton_biUnion ..).trans (hp_root j)) hx, he _ _ (show dimK Y {(Sum.inr j.val:E⊕K)} =_ from by unfold dimK; rw[show ({Sum.inr j.val}:Finset (E⊕K)).toRight= {j.val} from by ext; simp,singleton_biUnion]) hx⟩
noncomputable def tails (h:Setting W g Y q o p old a f z P t): Patron.Rail c (ample 6 J) (Rootπ W g):= ⟨fun i=> Y i.val,fun i=> (feather W g Y q o p old a f z h).warp (ridgeQ W g Y i)⟩
variable {J₀:Type}(Ku: Patron.Rail c 6 J₀)
local notation "AX"=> tails W g Y q o p old a f z h
lemma retains (he:(tails W g Y q o p old a f z h).Reg T)(ht:Correspond (faultK 6 p t (tails W g Y q o p old a f z h)) Ku)(hh: ∀ U:Grid c,Summable fun i=> ‖(Stretch.Basin (feather W g Y q o p old a f z h) (hats W g Y) P.threshold).warp i U‖) : Correspond (faultK 6 p t WZ) Ku:= by
     let R i:= rootedT W g Y q o p old a f z h hv hp_root i
     exact Stretch.cring 6 p (F') Z₀ (ridgeQ W g Y) AX (fun i=> (R _).1.trans (R _).2.symm) (fun i=> (R _).1) (fun i=>rfl) (fun j hi U=> dawnV W g Y q o p old a f z h hv j (identifies W g Y q o p old a f z h hv j hi) U) Ku ht he hh -- order h=Stems?
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.retains
