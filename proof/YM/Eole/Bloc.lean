import YM.Eole.Acre
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
-- gather disjoint nonempty subarms. Carrier input and output alphabets use their actual orientation.
structure Bloc (I J:Type)[Fintype I][Fintype J] where
      unit_ : I→ J
      arm: J → List I
      active j: (arm j)≠ []
      scoop j: (arm j).Nodup
      complete i j: i∈arm j ↔ unit_ i=j
namespace Bloc
variable (U:Bloc I J)
abbrev plant (s:Finset J):Finset I:= s.biUnion fun j=>(U.arm j).toFinset
abbrev core (s:Finset I):Finset J:=s.image U.unit_
lemma belongs (i:I)(s:Finset J): i∈U.plant s↔U.unit_ i ∈s:=by simp only [mem_biUnion,List.mem_toFinset,U.complete]; exact ⟨fun ⟨j,h,e⟩=>e.symm ▸ h,fun h=>⟨_,h,rfl⟩⟩
lemma planted (s:Finset J): U.core (U.plant s)=s:=by
    ext x; constructor
    · intro h; obtain ⟨k,hk,rfl⟩:=mem_image.mp h; exact (U.belongs k s).mp hk
    intro h; obtain ⟨k,hk⟩:=List.exists_mem_of_ne_nil _ (U.active x); exact mem_image.mpr ⟨k,mem_biUnion.mpr ⟨x,h,(List.mem_toFinset).mpr hk⟩,(U.complete k x).mp hk⟩
abbrev twins (l:List J):List I:= l.flatMap U.arm
lemma stowed (l:List J): (U.twins l).toFinset=U.plant l.toFinset:=by ext x; simp[plant,twins]
lemma tightened (l:List J)(h:l.Nodup) : (U.twins l).Nodup:=by
       induction l with
       | nil=>simp[twins]
       | cons i l ih=> rw[List.nodup_cons] at h; unfold twins; simp only[List.flatMap_cons]; refine List.pairwise_append.mpr ⟨U.scoop i,ih h.2,?_⟩; rintro k hk _ he rfl; have hx := List.mem_toFinset.mpr he; change k∈(U.twins l).toFinset at hx; rw [U.stowed,U.belongs,(U.complete k i).1 hk] at hx; exact h.1 (List.mem_toFinset.mp hx)
variable (Q:I→Bool)
abbrev flag (j:J):Bool:= Ribbon.shade (burst Q ((U.arm j).toFinset))
local notation "W"=> U.flag Q
lemma shade_glow {J:Type}[Fintype J][DecidableEq J](s t:Finset J)(he:Disjoint s t) : Ribbon.shade (s∪t)= (Ribbon.shade s ^^ Ribbon.shade t):=by
    classical
    unfold Ribbon.shade; rw [card_union_of_disjoint he]; by_cases ht:Odd s.card 
    · by_cases hk:Odd t.card; · rw[decide_eq_true ht,decide_eq_true hk,decide_eq_false (Nat.not_odd_iff_even.mpr (ht.add_odd hk))]; rfl
      rw[decide_eq_true ht,decide_eq_false hk,decide_eq_true (ht.add_even (Nat.not_odd_iff_even.mp hk))]; rfl
    by_cases hk:Odd t.card; · rw[decide_eq_false ht,decide_eq_true hk,decide_eq_true (Even.add_odd (Nat.not_odd_iff_even.mp ht) hk)]; rfl
    rw[decide_eq_false ht,decide_eq_false hk,decide_eq_false (Nat.not_odd_iff_even.mpr ((Nat.not_odd_iff_even.mp ht).add (Nat.not_odd_iff_even.mp hk)))]; rfl
lemma gleam (s t:Finset I)(h:Disjoint s t): Ribbon.shade (burst Q (s∪t))= (Ribbon.shade (burst Q s) ^^ Ribbon.shade (burst Q t)):=by rw [pulver]; exact shade_glow _ _ ((crossedR Q s t).2 h) 
lemma tape (s:Finset J): Ribbon.shade (burst W s)= Ribbon.shade (burst Q (U.plant s)):=by
   induction s using Finset.induction_on with
   | empty=> rw [show U.plant ∅= ∅ from biUnion_empty]; simp[Ribbon.burst_absent]; rfl
   | insert j s hj ih=>
      have he: Disjoint {j} s:=disjoint_singleton_left.mpr hj; have hv:Disjoint (U.arm j).toFinset (U.plant s):= disjoint_left.mpr fun i hv ht=>hj ((U.complete i j|>.1 (List.mem_toFinset.mp hv)) ▸ ((U.belongs i s).mp ht)); let X:= (insert j s); rw [show U.plant _= _ from (show U.plant (insert j s)=(U.arm j).toFinset∪ U.plant s from by unfold plant; rw[biUnion_insert]),show insert j s={j}∪s from (singleton_union ..).symm]; rw [gleam W _ _ he,gleam Q _ _ hv,ih,flavor]; -- rfl
lemma signpost (l k:List J) (H:l.Perm k)(hl:l.Nodup): ∃ v:ℂ, (v=1 ∨ v= -1)∧ armature W l.get=v • armature W k.get ∧ armature Q (U.twins l).get= v • armature Q (U.twins k).get:=by
      induction H with
      | nil=> exact ⟨1,.inl rfl,(one_smul ..).symm,(one_smul ..).symm⟩
      | cons j hp ih=>
         obtain ⟨v,H,h0,h1⟩:= ih (List.nodup_cons.mp hl).2; refine ⟨v,H,?_,?_⟩ <;> rename_i l k
         · rw [show (j::l)=[j]++l from rfl,show (j::k)=[j]++k from rfl,mixes,mixes,h0,smul_mul_assoc] -- dummy
         · rw [show U.twins (j::l)=_ from (List.flatMap_cons: U.twins (j::l)=U.arm j ++ U.twins l), show U.twins (j::k) = U.arm j ++ U.twins k from List.flatMap_cons,mixes,mixes,h1,smul_mul_assoc]
      | swap a b l=>
          let x:=U.arm a; let y:=U.arm b; let z:=U.twins l; let P:=(b::a::l); let R:=(a::b::l)
          have hv:U.twins (b::a::l)= y++x++z:=by unfold twins y x z; simp [twins]
          have hW:U.twins (a::b::l)= x++y++z:=by unfold twins z; simp [twins,x,y]
          let X:= armature Q x.get; let Y:= armature Q y.get; have h:Hom (W a) X:=fare Q x (U.scoop a); have h':Hom (W b) Y:=fare Q y (U.scoop b); let x':=[a]; let y':=[b]; let X':=armature W x'.get; let Y':=armature W y'.get; have hU :Hom (W a) X':=by have hz:=fare W x' (by simp[x']); rw [show x'.toFinset={a} from by simp [x'], Ribbon.flavor] at hz; exact hz
          have hV :Hom (W b) Y':=by have hz:=fare W y' (by simp[y']); rw [show y'.toFinset={b} from by simp[y'],Ribbon.flavor] at hz; exact hz
          have he:=h'.swap h; have hf:=hV.swap hU
          rw [hv,hW,show (b::a::l)=y'++x'++l from rfl,show (a::b::l)=x'++y'++l from rfl]; simp_rw [mixes]
          split at he; next h=> rw [if_pos h] at hf; exact ⟨-1,.inr rfl,by change _ * (X'*Y') = (-1:ℂ) • (_ * (Y'*X')); rw [hf, mul_neg,neg_one_smul], by change _*(X*Y)= (-1:ℂ) • (_*(Y*X)); rw[he,mul_neg,neg_one_smul]⟩
          next h=> rw[if_neg h] at hf; exact ⟨1,.inl rfl,by change _*(X'*Y')=(1:ℂ) • (_*(Y'*X')); rw[hf,one_smul],by change _*(X*Y)=(1:ℂ) • (_*(Y*X)); rw[he,one_smul]⟩
      | trans h ht ih ig=>
         obtain ⟨v,hv,h0,h1⟩:= ih hl; obtain ⟨w,hw,h2,h3⟩:= ig (h.nodup hl); refine ⟨v*w,?_,by rw[h0,h2,mul_smul],by rw[h1,h3,mul_smul]⟩; rcases hv with hi|hi <;> rcases hw with hj|hj <;> simp[hi,hj]
end Bloc
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Bloc.signpost
#print axioms YM.MassiveQCD.Sample.Eole.Bloc.tape
