import YM.Intag.Opal
/-! # Universal marks and corrected literal independent of unused tiles.
    compare projections with different supports/equal Wick reads at a given horizon
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber Apron Cupola
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
open YM.Arise.Bill YM.Arise.Count YM.Massive YM.Massive.UV Quills.Eden
variable {A B I J:Type}[Fintype A][Fintype B][Fintype I][Fintype J]{n:ℕ}
namespace Clover
variable (Q:I→Bool)(W:J→Bool)(u:I↪ J)(h:∀ i,W (u i)=Q i)
local notation "Y"=>Spine J
local notation "T" i:arg=> mono (burst Q ({i}:Finset I))
local notation "V" i:arg=> mono (burst W ({u i}:Finset J))
include h
lemma tiltH (j:I):∃ c:ℝ,(c=1∨ c= -1)∧ embed (surgeM u) (T j)= (c:ℂ) • (V j):=by
      have ho:(burst Q {j}).map (surgeM u)=burst W {u j}:=by rw [burstsM Q W u h,Finset.map_singleton]
      rcases embed_blade (surgeM u) (burst Q {j}) with hx|hx<;> rw [ho] at hx; exacts [⟨1,Or.inl rfl,by simpa using hx⟩, ⟨-1,Or.inr rfl,by simpa using hx⟩]
lemma cards : ∃ M:Matrix (Spine I) (Spine J) ℂ, ∀ i:I,changeVars M (T i)=V i :=by
   choose t hx H using tiltH Q W u h; obtain ⟨X,hX⟩:= tracksM (surgeM u); let a:= prismScale (den t); refine ⟨a*X,fun i=>?_⟩
   rw [change_mul,AlgHom.comp_apply, ← hX, show changeVars a (T i)=_ from tuition Q t i,map_smul,H]; rcases hx i with h|h <;> simp[h]
omit h
variable (S: Matrix (Spine I) (Spine J) ℂ)(hs:∀ i:I,changeVars S (mono (burst Q {i}))=mono (burst W {u i}))
local notation "R"=> Spine I
local notation "L'" => Spine J
noncomputable def jetP (A:Type)[Fintype A] (S: Matrix I J ℂ) : Patio (A⊕I)→ₐ[ℂ] Patio (A⊕J):=QCD.Cove.car (changeVars (Matrix.fromBlocks 1 0 0 S)) (by intro x h; unfold Plus; rw [changeVars,exterior_parity,h])
local notation "M₀"=> Matrix.fromBlocks (1:Matrix A A ℂ) 0 0 S
local notation "M"=> changeVars M₀
local notation "λJ"=> jetP A S
lemma rightJ (x:Alg (Spine I)): changeVars M₀ (quill A x)=quill A (changeVars S x):=by
    let X:=(M).comp (quill A); let K:= (quill A).comp (changeVars S); have he:X=K:=ext_atoms (fun i=>by
          change changeVars M₀ (embed Sum.inr (atom i))=embed Sum.inr (changeVars S (atom i)); rw[embed_atom,change_atom,change_atom,map_sum]; simp[Fintype.sum_sum_type]); exact AlgHom.congr_fun he x
lemma leftJ (x:Alg A): changeVars M₀ (fiber R x) = fiber L' x:=by
    let f:=(M).comp (fiber R); have he:f=fiber L' := ext_atoms (fun i=> by
         change changeVars _ (embed Sum.inl (atom i))=embed Sum.inl (atom i); rw [embed_atom,change_atom,embed_atom]; simp [Fintype.sum_sum_type, Matrix.one_apply,eq_comm,ite_smul]); exact AlgHom.congr_fun he x
-- orientation equality via retrieval of armature not sign.L.M.
variable (s: Fin n→ I)
local notation "g"=> u∘s
lemma burstM : crest (u ∘ s)= (crest s).map u:=by ext i; simp only [exists_fix,Finset.mem_map, comp_apply]; aesop
include hs
lemma porter : changeVars S (armature Q s) = armature W (u ∘ s):=by
    unfold armature; rw [map_list_prod]
    simp_rw [List.map_reverse,List.map_ofFn]; simp only [Function.comp_def, hs]
lemma lamp (j:I) (x:Alg A): changeVars M₀ (stake A (burst Q {j}) x)= stake A (burst W {u j}) x:=by
     rw [markedOut,markedOut,map_mul,leftJ,rightJ,hs]
variable (l:List I)(x:Patio (A⊕ Spine I))
local notation "p"=> crest s
local notation "Lv"=> (l.map u)
lemma peg (hσ:Injective s)(hp:Polite Q (crest s) x) : ((jetP A S) x).val= fiber (Spine J) (numbered Q A s x)*quill A (armature W (u ∘s)):=by change changeVars _ x.val=_; rw [Quills.charge _ _ _ _ hp hσ,map_mul,leftJ, rightJ,porter Q W u S hs]
lemma song (hσ: Injective s)(hp: Polite Q (crest s) x): numbered W A (u∘s) ((jetP A S) x) = numbered Q A s x:= Quills.cuts A W _ (u.injective.comp hσ) _ _ (peg Q W u S hs s x hσ hp)
lemma rooted (i:Finset I)(hp:Polite Q i x): Polite W (i.map u) ((jetP A S x)):=by
    let f:=tour i; have hv: crest f=i:=club i; let U:= numbered Q A f x; let t:= armature W (u∘f); have hh:t=t:= rfl; have hx: ((jetP A S x)).val=fiber (Spine J) U * quill A t:=peg Q W u _ hs f x (snug i) (hv.symm ▸ hp)
    rcases (Quills.arc W (u∘f) (u.injective.comp (snug i))) with ht|ht
    · rw [show t=mono (burst W (i.map u)) from (?_)] at hx; exact ⟨U,hx.symm⟩; rw [← hv, ← burstM]; exact ht
    rw [show t= -mono (burst W (i.map u)) from (?_)] at hx; refine ⟨-U,?_⟩; change stake A _ (-U)= ((jetP A S x)).val; rw[markedOut,hx,map_neg,map_neg,neg_mul,mul_neg]; rw[← hv,← burstM]; exact ht
-- natural sector marks.State. `(jetP A S x).V`. projection of others before counting ok. s independent.Approval O.W.C
lemma rankView (hp:ValidPieces A Q (crest s) x) (t: Finset I): jetP A S (pick A Q t x)=pick A W (t.map u) (jetP A S x):=by
    rw[hp.wholeV,map_sum,map_sum,map_sum,map_sum]; refine sum_congr rfl fun j hj=>?_ ; let y:=pick A Q j x; have ht:= choseTuft A Q j x; have h':=rooted Q W u S hs y j ht
    by_cases he:t=j; · subst j; rw [eq_pick _ _ _ _ ht,eq_pick _ _ _ _ h']
    have hu:pick A Q t y=0:=by apply Subtype.ext; change stake A _ (pluck A _ y)=0; rw [show pluck A _ y=0 from Polite.spectral ht _ ((burstUnique Q).ne he),map_zero]
    rw [show pick A Q t _=0 from hu,map_zero]; apply Subtype.ext; symm; change stake A _ (pluck A _ ((jetP A S y)))= 0; rw[show pluck A _ _=0 from Polite.spectral h' _ ((burstUnique W).ne ((markL u).ne he)),map_zero]
omit hs in
lemma pickN (x:Patio (A⊕ Spine I)): numbered Q A s (pick A Q (crest s) x)=numbered Q A s x:=by
   change signG Q s • pluck _ _ _= signG Q s • pluck _ _ _; unfold pick; rw[many, if_pos rfl]
lemma verse (hσ:Injective s)(hp:ValidPieces A Q (crest s) x): numbered W A (u ∘ s) (jetP A S x)=numbered Q A s x:=by
    have hG:= song Q W u S hs s (pick A Q _ x) hσ (choseTuft ..); rw [rankView Q W u S hs s x hp, ← burstM] at hG; -- pickN kept include
    rw[pickN] at hG -- likely args errors
    rw[pickN] at hG; exact hG
lemma readV (hx:l.Nodup)(hp:ValidPieces A Q l.toFinset x): chants W (l.map u) A (jetP A S x)=chants Q l A x:=by
    rw [show l.map u= List.ofFn (u ∘ l.get) from by rw [←List.map_ofFn,List.ofFn_get], Lyre.verses]; exact verse Q W u S hs _ _ (List.nodup_iff_injective_get.mp hx) ((tops l).symm ▸ hp)
end Clover
end YM.MassiveQCD.Sample.Quills
#print axioms YM.MassiveQCD.Sample.Quills.Clover.readV
#print axioms YM.MassiveQCD.Sample.Quills.Clover.cards
