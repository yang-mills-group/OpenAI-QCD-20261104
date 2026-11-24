import YM.Profiles.Quills
import YM.Clays.Inks
import YM.Pollen.Acts
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
variable (p:I→Lat.Fields c N→L[ℂ]Lat.Fields c N) (H:∀ i, Bean (p i))
local notation "X"=> Keys c N
local notation "S"=> Spine I
local notation "P" => Patio (Keys c N⊕Spine I)
local notation "q"=> traceI I
local notation "B!"=> burst q
include H
variable (a:I→ℂ)
local notation "Ω"=> actU p H a
local notation "Φ"=> effU p H a
open MassiveQCD.Sample.Quills
local notation "ω₀"=> numbered (traceI I) X
-- ANY piece. payload.L moves even Billing.Log.All measured.C.
include H
lemma recurrentU (s:List I)(t:Fin n→I)(x:P)(hr:∀ i x,ber _ (p i x)=0): ber _ (numbered q X t (Ω s x))= ber _ (numbered q X t x):=by
     induction s with
     | nil=> rfl
     | cons i s ih=>
          let F:= Ω s x; let q':= H i; let A:= q'.twirl I F; let B:= echoI X i; let M:=numbered (traceI I) X t; rw [act_consU,map_add,map_add,ih]; apply add_eq_left.mpr; rw [Bean.fate, map_smul, map_smul]; refine Eq.trans (congr_arg _ ?_) (smul_zero ..); change ber _ (M (B*A))=0
          have ht:q'.twirl I B=0:=by apply Subtype.ext; change carry S (p i) (stake X (burst q {i}) 1)=0; rw [speaks S,q'.vanishes,map_zero]
          rw [show B*A=q'.twirl I (B*F) from (Eq.trans (q'.twirls ..) (by rw [ht,zero_mul,zero_add])).symm]; unfold M numbered; rw [ContinuousLinearMap.smul_apply,Bean.onPiece, map_smul,hr i,smul_zero]
-- arbitrary waves λ. single projection need Valid pieces or shutter Y. prove for Valid any → doesn't assume outside field stage.Witness Pit.Res.Payment. zero mode.
omit H in
lemma echoOneU (x:Alg X)(j:I): stake X ∅ x * (echoI X j).val=stake X (burst (traceI I) {j}) x:= by rw [quiet]; change Ribbon.fiber S x * stake X _ _ = _; rw [sticker_add,mul_one]
lemma untwirlU (c:P)(i j:I) (h:ValidPieces X (traceI I) univ c) : pluck X (burst (traceI I) {j}) ((H i).dies (a i) i c)= if i=j then a i • p i (pluck X ∅ c) else 0 :=by
     let V:= Finset.univ.filter (fun t=> t∈ ((Finset.univ:Finset I).powerset:Set (Finset I))); let f:= fun t:Finset I=> Cupola.pick X (traceI I) t c; let F: X→ℝ:=fun _=>1; let t:= B! ({j}:Finset I); let Q:=(H i).dies (a i) i
     have hf(u:Finset I): Polite (traceI I) u (f u):=choseTuft ..
     have hQ(u): Polite (traceI I) ({i}∪u) (Q (f u)):=(H i).diesPiece _ _ (hf _)
     nth_rw 1 [h.wholeV]; rw [map_sum,map_sum]; by_cases hp:i=j
     · subst j; rw [if_pos rfl,sum_eq_single ∅]; rotate_left
       · intro k _ hj; by_cases h:i∈k
         · let V':=(H i).twirl I (f k); have hv: Polite (traceI I) k V':= politeStep _ (hf k) rfl; have hh:Polite (traceI I) {i} (echoI X i):= itOwn i; have hz: Q (f k)=0:=by unfold Q; change a i • (_ * V')=0; rw [hh.nilpotent hv (by simp [h]),smul_zero]
           rw [hz,map_zero]
         exact ((hQ k).spectral _ (fun he=>hj (by have hx:=burstUnique (traceI I) he; ext x; have ht : x∈ ({i}:Finset I)↔ x∈{i} ∪ k:= hx ▸ Iff.rfl; simp only [mem_union,mem_singleton] at ht; simp only [notMem_empty,iff_false]; intro hz; exact h ((ht.mpr (Or.inr hz)) ▸ hz)))) -- hx tautology via rw brittle.
       · simp
       let X':=(H i).twirl I (f ∅); have hm(f0:P)(hf:Polite (traceI I) ∅ f0):f0.val= stake X (∅:Finset S) (pluck X ∅ f0):=by have he:=hf.exact.symm; rwa [burst_absent] at he
       have hv:X'.val= stake X (∅:Finset S) (p i (pluck X ∅ c)):= (hm _ (politeStep _ (hf _) rfl)).trans (congr_arg _ (Eq.trans ((H i).onPiece I (f ∅) _) (congr_arg (p i) (by unfold f Cupola.pick; rw [burst_absent,many,if_pos rfl]))))
       change pluck X _ ((a i) • (echoI X i * X'))=_; rw [map_smul, mul_comm]; exact congr_arg _ (show scrape X _ (X'.val*(echoI X i).val)=p i (pluck X ∅ c) by rw [hv,echoOneU,quid])
     rw [if_neg hp]; exact sum_eq_zero fun k _=> (hQ k).spectral _ (fun he=> hp (by have h:=burstUnique (traceI I) he; apply mem_singleton.mp; rw [h]; exact mem_union_left _ (mem_singleton_self _)))
lemma tippleU (s: List I)(x:P)(j:I)(hs:s.Nodup)(hx:ValidPieces X (traceI I) univ x): pluck X (burst (traceI I) {j}) (Ω s x)= pluck X (burst (traceI I) {j}) x + if j∈s then a j • p j (pluck X ∅ x) else 0:=by
     induction s with
     | nil=> simp only [List.not_mem_nil,↓reduceIte,add_zero]; rfl
     | cons i s ih=> rw [act_consU,map_add,untwirlU p H a (Ω s x) i j (validpU p H a s x hx)]; obtain ⟨ha,hb⟩:=List.nodup_cons.mp hs; rw [ih hb]; by_cases h:i=j
                     · subst j; rw [waivedU p H a s x hx]; simp [ha]
                     simp only [if_neg h,add_zero,List.mem_cons,Ne.symm h,false_or,not_false_eq_true]
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.recurrentU
#print axioms YM.Massive.PCAC.tippleU
