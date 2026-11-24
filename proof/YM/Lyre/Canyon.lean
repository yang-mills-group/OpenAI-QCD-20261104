import YM.Lyre.Tongue
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills.Eden
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber Apron Cupola
open FlareV
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
variable {A B I J:Type}[Fintype A][Fintype B][Fintype I][Fintype J]{n:ℕ}
-- universal mark emission.Banks
variable (Q:I→Bool)(W:J→Bool)(a:List I) (u:I↪ J)(h:∀ i,W (u i)=Q i)
local notation "ZI"=> Patio (A⊕Spine I)
local notation "ZJ"=>Patio (B⊕Spine J)
variable (M:Matrix A B ℂ)(S: Matrix (Spine I) (Spine J) ℂ)(hP:∀ i:I, staysM S (mono (burst Q {i}))=grade (mono (burst W {u i})))
local notation "θ" => Matrix.fromBlocks M 0 0 S
variable (s:Fin n→I)(hs:Injective s)
local notation "sJ"=> u ∘ s ∘ (Fin.rev : Fin n→ Fin n)
include h hP
lemma equipped (i:Finset I)(x:Patio (A⊕Spine I))(hp:Polite Q i x): Polite W (i.map u) (antiE θ x):=by
    let f:=tour i; have ht:crest f=i:=club i
    let g:=u ∘ f ∘ Fin.rev; have he: crest g=i.map u:= (crestM u f).trans (congr_arg (fun i:Finset I=>i.map u) ht)
    have hh: Polite Q (crest f) x:= ht.symm ▸ hp
    let Y:=staysM M (numbered Q A f x); have hY: (antiE θ x).val=fiber (Spine J) Y * quill B (armature W g):=proceed Q W u h M S hP f (snug i) hh
    rcases arc W g (u.injective.comp ((snug i).comp Fin.rev_injective)) with hx|hx
    · apply Eq.mp _ (show Polite W (crest g) (antiE θ x) from ⟨Y,(hY.trans (congr_arg (fun y => fiber (Spine J) Y* quill B y) hx)).symm⟩); rw [he] -- simp check
    have hp : armature W g= -mono (burst W (i.map u)):=by rw[show i.map u= crest g from he.symm]; exact hx
    refine ⟨-Y,?_⟩; change stake B _ (-Y) = (antiE θ x).val; rw[markedOut,hY,hp,map_neg,map_neg,mul_neg,neg_mul]
lemma pickV (v: Finset I)(x:Patio (A⊕Spine I))(hp:ValidPieces A Q v x) (p: Finset I): antiE θ (pick A Q p x)=pick B W (p.map u) (antiE θ x):=by
    rw[hp.wholeV,map_sum,map_sum,map_sum,map_sum]; refine sum_congr rfl fun j hj=> ?_; let y:=pick A Q j x; have ht := choseTuft A Q j x; have h':=equipped Q W u h M S hP _ y ht; by_cases he:p=j; · subst j; rw [eq_pick _ _ _ _ ht, eq_pick _ _ _ _ h']
    have hu:pick A Q p y=0:=by apply Subtype.ext; change stake A _ (pluck A _ y)= 0; rw [show pluck A (burst Q p) y=0 from Polite.spectral ht _ ((burstUnique Q).ne he),map_zero]
    rw [show pick A Q p _=0 from hu,map_zero]; apply Subtype.ext; symm; change stake B _ (pluck B _ (antiE θ y))= 0; rw [show pluck B (burst W (p.map u)) _=0 from Polite.spectral h' _ ((burstUnique W).ne ((markL u).ne he)),map_zero]
lemma textR (x:Patio (A⊕Spine I))(hp:ValidPieces A Q (crest s) x)(hs:Injective s) : numbered W B sJ (antiE θ x)=staysM M (numbered Q A s x):=by
    have h':=backedE Q W u h M S hP s hs (pick A Q (crest s) x) (choseTuft ..);
    have hg(T J:Type)[Fintype T][Fintype J](Q:J→ Bool)(s:Fin n→J)(x:Patio (T ⊕Spine J)): numbered Q T s (pick T Q (crest s) x)=numbered Q T s x:=by
         change signG Q s • pluck _ _ _=signG Q s • Cupola.pluck _ _ x; unfold pick; rw[many, if_pos rfl]
    rw[pickV Q W u h M S hP _ x hp,←crestM u s,hg,hg] at h'; exact h'
omit h hP
-- valid generator pol products
noncomputable def kits (X: Finset I)(P:I→ Patio (A⊕Spine I))(F:Finset I→ Patio (A⊕Spine I)) : Patio (A⊕Spine I) := NormedSpace.exp (∑ i∈ X,P i) * NormedSpace.exp (∑ i∈ X.powerset.erase ∅, F i) -- erase zero later
variable (X: Finset I)(P:I→ Patio (A⊕Spine I))(F: Finset I→Patio (A⊕Spine I))
variable (hp:∀ i∈X,Polite Q {i} (P i))(hF:∀ p:powerset X, p.val.Nonempty→Polite Q p.val (F p.val))
include hp hF
lemma tracked : ValidPieces A Q X (kits X P F):=by
    let T:= X.powerset.erase ∅; have he: ValidPieces A Q X (∑ i ∈X,P i):=ValidPieces.cost _ _ (fun i hi=> ValidPieces.role _ (hp i hi) (singleton_subset_iff.mpr hi)); have hZ:= ValidPieces.exponent (ValidPieces.cost (A:=A) (q:=Q) (U:=X) T F (fun i hi=>ValidPieces.role _ (hF ⟨i,mem_of_mem_erase hi⟩ (Finset.nonempty_iff_ne_empty.mpr (ne_of_mem_erase hi))) (mem_powerset.mp (mem_of_mem_erase hi)))); simpa only [kits,sub_zero] using ValidPieces.mul he.exponent hZ
omit hp hF
variable (P':J→Patio (B⊕Spine J))(F': Finset J→Patio (B⊕Spine J))
variable (hΦ:∀ i∈X,antiE (Matrix.fromBlocks M 0 0 S) (P i)=P' (u i))(hG:∀ i⊆ X,i.Nonempty→antiE (Matrix.fromBlocks M 0 0 S) (F i)=F' (i.map u))
include h hP
lemma echoesC (v:Alg A)(j:I)(U:ZI)(hp:U.val=stake A (burst Q {j}) v): (antiE θ U).val= stake B (burst W {u j}) ((staysM M) v):=by
    let s:=fun (_:Fin 1)=>j
    have hz: crest s={j}:=by simp [s,crest]
    let Y:= u∘s∘ (Fin.rev : Fin 1→Fin 1)
    have hk : Polite Q {j} U := ⟨_,hp.symm⟩
    have hU :numbered Q A s U=v:=by rw [singleN]; change scrape _ _ U.val=v; rw[hp]; exact quid ..
    have he:= proceed Q W u h M S hP s (fun _ _ _=>Subsingleton.elim ..) (hz.symm ▸ hk)
    rw [he, hU, show armature W Y=mono (burst W {u j}) from (by simp [armature,Y,s])]; rfl
omit h hP
include hΦ hG
lemma sealedH: kits (X.map u) P' F'=antiE θ (kits X P F):=by
    unfold kits; rw [anti_m,anti_exp,anti_exp,map_sum,map_sum]; congr 1; · simp only [sum_map]; exact congr_arg _ (sum_congr rfl fun j hj=>(hΦ j hj).symm)
    rw [erase_v, sum_image ((markL u).injOn)]; exact congr_arg _ (sum_congr rfl fun j hj=> (hG _ (mem_powerset.mp (mem_of_mem_erase hj)) (nonempty_iff_ne_empty.mpr (ne_of_mem_erase hj))).symm)
end YM.MassiveQCD.Sample.Quills.Eden
#print axioms YM.MassiveQCD.Sample.Quills.Eden.textR
#print axioms YM.MassiveQCD.Sample.Quills.Eden.sealedH
#print axioms YM.MassiveQCD.Sample.Quills.Eden.echoesC
#print axioms YM.MassiveQCD.Sample.Quills.Eden.tracked
