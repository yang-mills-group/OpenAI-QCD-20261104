import YM.Pollen.Bean
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical
variable {c f:Side}{n N j k F:ℕ}
open Onsite Tide QCD.Cove Creek
open Finset
open MassiveQCD MassiveQCD.Ribbon MassiveQCD.Cupola
variable {C:ℝ}{I:Type}[Fintype I]
variable (o:I→Site c)(p:I→Lat.Fields c N→L[ℂ]Lat.Fields c N) (H:∀ i, Bean (p i))
local notation "X"=> Keys c N
local notation "S"=> Spine I
local notation "P" => Patio (Keys c N⊕Spine I)
local notation "q"=> traceI I
local notation "B!"=> burst q
include H
-- finlist version avoids commutation if options coincide / different equations. ALL subset fees.
variable (a:I→ℂ)
local notation "T"=> (traceI I)
noncomputable def actU : List I→ P →ₐ[ℂ] P
| [] => AlgHom.id ℂ P
| i::s=> ((H i).incline (a i) i).comp (actU s)
local notation "Ω"=> actU p H a
noncomputable def effU: List I→ P→L[ℂ] P
| []=> ContinuousLinearMap.id ℂ P
| i::s=> ((H i).dies (a i) i).comp (effU s)
local notation "Φ"=> effU p H a
lemma act_consU (i:I)(s:List I)(x:P) : Ω (i::s) x= Ω s x+(H i).dies (a i) i (Ω s x):=rfl
lemma eff_consU (i:I)(s: List I)(x:P) : Φ (i::s) x=(H i).dies (a i) i (Φ s x):=rfl
lemma pay_pieceU (s:List I){x:P}{u:Finset I}(hy:Polite T u x):Polite T (s.toFinset∪u) (Φ s x):=by
   induction s with
   | nil=> rw [List.toFinset_nil, empty_union]; exact hy
   | cons i s ih=>rw [eff_consU,List.toFinset_cons,← singleton_union, Finset.union_assoc]; exact (H _).diesPiece _ _ ih -- syntax
lemma paysU (s:List I)(hx:s.Nodup)(x:P): Ω s x=∑ A∈s.toFinset.powerset, Φ (s.filter fun i=> i∈A) x:=by
    induction s with
    | nil=> simp [actU,effU]
    | cons i s ih=>
        rw [act_consU]; obtain ⟨hx,hN⟩:=List.nodup_cons.mp hx; rw [ih hN,map_sum,List.toFinset_cons, Finset.powerset_insert]; let PP (A:Finset I):= s.filter fun i=>i∈A
        let f:= s.toFinset.powerset; have he(A)(h:A∈f): i∉ A:=fun he=>hx (List.mem_toFinset.mp (mem_powerset.mp h he)); have hh(A)(h:A∈f): (i::s).filter (·∈A) = PP A:=by simp [he _ h,PP]
        have hr(A:Finset I):PP (insert i A)= PP A:=by
              unfold PP; apply List.filter_congr; intro j hj; have hz:j ≠ i:=fun hp=> hx (hp ▸hj); simp [hz]
        have hd:Disjoint f (f.image (insert i)):=disjoint_left.mpr fun j hv hz=> by obtain ⟨v,hv',rfl⟩:=mem_image.mp hz; exact he _ hv (mem_insert_self ..)
        rw [sum_union hd,sum_image]; swap
        · exact fun x hx y hy h=> by
                 apply Finset.ext; intro j; by_cases hz:j=i
                 · subst j; simp only [he _ hx,he _ hy]
                 have hv:j∈insert i x↔ j∈insert i y:=h ▸ Iff.rfl; simpa [hz] using hv
        apply congr_arg₂ (·+·); · exact sum_congr rfl fun i h=> ((congr_arg (fun t=>Φ t x) (hh _ h))).symm
        exact sum_congr rfl fun i' _=> by
              rw [List.filter_cons_of_pos]
              · change _= Φ (i::PP (insert i i')) x; rw [hr,eff_consU]
              simp
-- L consensus.ts
lemma actsPoleU (s: List I)(x y: P)(t:Finset I)(hz:shutter X t x=shutter X t y): shutter X t (Ω s x)= shutter X t (Ω s y):=by
      induction s with| nil=>exact hz| cons i s ih=> rw [act_consU,act_consU,map_add,map_add,Bean.restrict_at,Bean.restrict_at,ih]
lemma validpU (s: List I)(x:P)(h: ValidPieces X q univ x): ValidPieces X q univ (Ω s x):=by
    induction s with
    | nil=> exact h
    | cons i s ih=>rw [act_consU]; apply ih.plus; rw [ih.wholeV,map_sum]; exact ValidPieces.cost _ _ fun t _=> ValidPieces.role _ ((H i).diesPiece _ _ (choseTuft ..)) (subset_univ _)
lemma waivedU (s: List I)(x:P)(h:ValidPieces X q univ x): pluck X ∅ (Ω s x)=pluck X ∅ x:=by
    induction s with
    | nil=> exact rfl
    | cons i s ih=> have hh:= validpU p H a s x h; let z:= Ω s x; have hf:pluck X ∅ ((H i).dies (a i) i z)=0:=by unfold z; rw [hh.wholeV,map_sum,map_sum]; exact sum_eq_zero fun t _=> ((H i).diesPiece _ _ (choseTuft X q t (Ω s x))).spectral _ ((burstPos T (singleton_nonempty i|>.mono subset_union_left )).ne_empty.symm)
                    rw [act_consU,map_add,hf,ih,add_zero]
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.paysU
#print axioms YM.Massive.PCAC.waivedU
