import YM.Lyre.Ledger
import YM.TIPS.Stir
/-! # Reflected patterns on FULL common marker charge arena. Can compare any two cells.
     Additive maps reverse EXACT signs, include the sign costs internally. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills.Eden
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter
open MassiveQCD.Ribbon
open scoped Topology ContDiff BigOperators Classical
variable {A B I J :Type}[Fintype A][Fintype B][Fintype I][Fintype J]{n:ℕ}
lemma physical_sign (v:Finset A): ∃ t:ℝ,(t=1∨t= -1) ∧ dagger (mono v)=(t:ℂ) • mono v:=by
    obtain ⟨u,h,hx,he⟩:=expression v
    let T:= List.ofFn u
    have hh(l:List A): dagger (l.map atom).prod=(l.reverse.map atom).prod:=by induction l with| nil=> simp [dagger_one]| cons a l ih=> simp [dagger_mul,dagger_atom,ih]
    have hv:T.toFinset=v:=by ext i; rw [hx]; simp [T]
    have he' : dagger (mono v)=(T.reverse.map atom).prod:=by rw [he]; convert hh T using 2; simp [T]
    rcases sign_product T.reverse (show T.reverse.Nodup from (by simp [T,List.nodup_ofFn_ofInjective h])) with hp|hp <;> rw [List.toFinset_reverse,hv] at hp; exact ⟨1,Or.inl rfl, by rw [he',hp,Complex.ofReal_one,one_smul]⟩; exact ⟨-1,Or.inr rfl,by rw [he',hp]; simp⟩
variable (q:I→Bool)(q':J→Bool)(u:I↪ J)(h:∀ i,q' (u i)=q i)
noncomputable abbrev staysM (X:Matrix A B ℂ): Alg A→ₛₗ[starRingEnd ℂ] Alg B:= (changeVars X).toLinearMap.comp dagger
local notation "U"=> Spine I
local notation "V"=> Spine J
noncomputable abbrev surgeM (u:I↪J): Spine I↪ Spine J:= Embedding.prodMap (Embedding.prodMap u (Embedding.refl _)) (Embedding.refl _)
include h
lemma burstsM (s:Finset I): (burst q s).map (surgeM u)=burst q' (s.map u):=by
    ext w; rcases w with ⟨⟨i,b⟩,k⟩; unfold surgeM burst post; cases b <;> simp
    constructor; rintro ⟨a,⟨ha,hx⟩,rfl⟩; exact ⟨⟨a,ha,rfl⟩, (h a).trans hx⟩; rintro ⟨⟨a,ha,rfl⟩,hx⟩; exact ⟨a,⟨ha,(h a).symm.trans hx⟩,rfl⟩
local notation "T" i:arg=> mono (burst q ({i}:Finset I))
noncomputable def prismScale (x:A→ℝ) := Matrix.diagonal fun i=>(x i:ℂ)
local notation "Tz" i:arg=> mono (burst q' ({u i}:Finset J))
lemma tallL (i:I): ∃ t:ℝ,(t=1∨t= -1) ∧ embed (surgeM u) (dagger (T i))= (t:ℂ) • (Tz i):=by
    obtain ⟨t,hx,he⟩:= physical_sign (burst q {i}); have hf:(burst q {i}).map (surgeM u)= burst q' {u i}:=by rw [burstsM q q' u h,map_singleton];
    rcases embed_blade (surgeM u) (burst q {i}) with hg|hg <;> rw [hf] at hg
    · exact ⟨t,hx,by rw[he,map_smul,hg]⟩
    exact ⟨-t,by rcases hx with hx|hx<;> simp [hx],by rw[he,map_smul,hg]; simp⟩
omit h
variable (F:I↪ J)
lemma tracksM : ∃ X:Matrix I J ℂ, embed (F: I→J)=changeVars X:=by
   let X:=Matrix.of fun i j=> if F i=j then (1:ℂ) else 0; refine ⟨X, ext_atoms fun i=>?_⟩; rw[embed_atom,change_atom]; simp [X,ite_smul]
noncomputable def den (p: I→ℝ)(x:Spine I):ℝ:= if x.1.2=false ∧ x.2=0 then p x.1.1 else 1
lemma tuition(p:I→ℝ)(i:I): wscale (den p) (T i)=(p i:ℂ) • T i:=by
    rw [wscale_mono]; apply congr_arg (fun z:ℂ=>z • T i); let X:U:=((i,false),0); rw [Finset.prod_eq_single X]
    · simp [X,den]
    · intro j hj hv; unfold den; obtain hx:=located q _ _ hj; rw [mem_singleton] at hx; split_ifs with ht; exfalso; exact hv (Prod.ext (Prod.ext hx ht.1) ht.2); simp
    intro h; exact False.elim (h ((place q i {i}).1 (by simp)))
-- MARK columns choice.Exact act.Stakes for ANY F.Pose.L.
include h
lemma expense : ∃ X:Matrix (Spine I) (Spine J) ℂ, ∀ i:I, staysM X (T i)= grade (Tz i):=by
    choose t hx ht using tallL q q' u h
    choose k hk hL using fun i:I=> physical_sign (burst q {i});
    let p(i:I):ℝ:=(if q i then - t i else t i); let M:=surgeM u
    obtain ⟨X,hX⟩:=tracksM M; let VA:=prismScale (den p); refine ⟨VA*X,fun i=>?_⟩
    change changeVars (VA*X) _= _; rw [change_mul, AlgHom.comp_apply,← hX, hL, map_smul]
    rw[ show changeVars VA (T i)=_ from tuition q p i]; have he: k i=1∨ k i= -1:= hk _
    rw [smul_comm (k i:ℂ), ← hL i,map_smul]; change (p i:ℂ) • (embed M (dagger (T i)))=_; rw [ht,smul_smul]; have hz:Hom (q i) (Tz i):=by rw [← h, ← flavor q' (u i)]; exact Ribbon.healthy _ -- name
    cases hx0 : q i <;> unfold p <;> rcases hx i with H|H <;> rw [hx0] at hz ⊢ <;> simp only [H,Bool.false_eq_true,↓reduceIte] <;> rw[show grade _=_ from hz] <;> simp
end YM.MassiveQCD.Sample.Quills.Eden
#print axioms YM.MassiveQCD.Sample.Quills.Eden.expense
