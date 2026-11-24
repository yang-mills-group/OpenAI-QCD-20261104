import YM.Lyre.Pear
/-! # Literal character symbols under thermal mirrors -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills.Eden
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter
open MassiveQCD.Ribbon
open scoped Topology ContDiff BigOperators Classical
variable {A B C D I J:Type}[Fintype A][Fintype B][Fintype C][Fintype D][Fintype I][Fintype J]{n:ℕ}
section
variable (X: Matrix A B ℂ)
noncomputable def antiE : Patio A→ₛₗ[starRingEnd ℂ] Patio B := ((staysM X).comp (light A).toLinearMap).codRestrict (roomA B).toSubmodule (fun x=> (show Plus (changeVars X (dagger x.val)) from by unfold Plus changeVars; rw [exterior_parity, dagger_parity,show grade x.val=x.val from x.property]))
lemma anti_m (x y:Patio A): antiE X (x*y)=antiE X x * antiE X y:=by
    rw [mul_comm x]; apply Subtype.ext; change changeVars X (dagger (y.val*x.val))=_; rw [dagger_mul,map_mul]; rfl
lemma anti_mul (x y:Alg A): staysM X (x*y)=staysM X y* staysM X x:=by change changeVars X _=_; rw [dagger_mul,map_mul]; rfl
lemma anti_one : antiE X 1=1:=by apply Subtype.ext; exact (congr_arg (changeVars X) dagger_one).trans (map_one _)
lemma anti_exp (x : Patio A): antiE X (NormedSpace.exp x)=NormedSpace.exp (antiE X x):=by
     apply Subtype.ext; change staysM X (light _ (NormedSpace.exp x))=light _ _; simp only [light_exp,map_weight,staysM, LinearMap.comp_apply, AlgHom.toLinearMap_apply,dagger_exp]; rfl
lemma anti_grade (x: Alg A): staysM X (grade x)=Grass.grade (staysM X x):=by change changeVars X _=Grass.grade (changeVars _ _); unfold changeVars; rw [exterior_parity,dagger_parity]
variable (Y:Matrix C D ℂ)
local notation "Θ"=>Matrix.fromBlocks X 0 0 Y
lemma anti_l (x: Alg A): staysM Θ (fiber C x)= fiber D (staysM X x):=by
   let L:=(staysM Θ).comp (fiber C (A:=A)).toLinearMap; let Q:= (fiber D).toLinearMap.comp (staysM X)
   have h:L=Q:=ext_reversing (fun a b=>by simp [L,dagger_mul]) (fun a b=>by simp [Q,dagger_mul]) (by simp [L,Q,staysM,dagger_one]) (fun i=> by
         change staysM Θ (embed Sum.inl (atom i))=_; rw [embed_atom]; change changeVars Θ (dagger (atom _))=embed _ (changeVars X (dagger (atom i))); rw [dagger_atom,dagger_atom,change_atom,change_atom,map_sum]; simp [Fintype.sum_sum_type])
   exact LinearMap.congr_fun h x
lemma anti_r (x:Alg C): staysM Θ (quill A x)= quill B (staysM Y x):=by
   let L:=(staysM Θ).comp (quill A (B:=C)).toLinearMap; let Q:= (quill B).toLinearMap.comp (staysM Y)
   have h:L=Q:=ext_reversing (fun a b=>by simp [L,dagger_mul]) (fun a b=>by simp [Q,dagger_mul]) (by simp [L,Q,staysM,dagger_one]) (fun i=> by
         change staysM Θ (embed Sum.inr (atom i))=_; rw [embed_atom]; change changeVars Θ (dagger (atom _))=embed _ (changeVars Y (dagger (atom i))); rw [dagger_atom,dagger_atom,change_atom,change_atom,map_sum]; simp [Fintype.sum_sum_type])
   exact LinearMap.congr_fun h x
end
variable (Q:I→Bool)(W:J→Bool)(u:I↪ J)(h:∀ i,W (u i)=Q i)
local notation "PI"=> Spine I
local notation "PJ"=> Spine J
local notation "T" i:arg=> mono (burst Q ({i}:Finset I))
local notation "Tz" i:arg=> mono (burst W ({u i}:Finset J))
variable (M:Matrix A B ℂ)(S: Matrix (Spine I) (Spine J) ℂ)(hP:∀ i:I, staysM S (mono (burst Q {i}))=grade (mono (burst W {u i})))
local notation "θ"=>Matrix.fromBlocks M 0 0 S
variable (s:Fin n→I)(hs:Injective s)
local notation "b"=> crest s
local notation "R"=> (Fin.rev :Fin n→ Fin n)
local notation "p"=> (u ∘s ∘ R)
lemma crestM : crest p=(crest s).map u:=by ext i; rw [exists_fix,Finset.mem_map]; constructor; rintro ⟨k,rfl⟩; exact ⟨s (R k),(exists_fix s _).2 ⟨R k,rfl⟩,rfl⟩; rintro ⟨j,hj,rfl⟩; obtain ⟨i,rfl⟩:= (exists_fix s j).1 hj; exact ⟨R i,congr_arg u (congr_arg s (Fin.rev_rev i))⟩
lemma n_stars (x:Patio (A⊕Spine I)): Hom (shade (burst Q b)) (numbered Q A s x):= (serene _ x.property|>.smul _) -- syntax
include hs
lemma armG : Hom (shade (burst Q b)) (armature Q s):=by
    rcases Quills.arc Q s hs with hx|hx
    · change _=mono _ at hx; rw [hx]; exact Ribbon.healthy _
    change _ = -mono _ at hx; rw [hx,← neg_one_smul ℂ]; exact Hom.smul (Ribbon.healthy _) _
omit hs
include hP
lemma assured : staysM S (armature Q s)=grade (armature W p):=by
    unfold armature; let X(i:Fin n):= mono (burst Q {s i}); let Y(i:Fin n):= Tz (s i)
    have h (l:List (Fin n)): staysM S (l.reverse.map X).prod=grade (l.map Y).prod:=by
       induction l with| nil=> simp [staysM,dagger_one]| cons a l ih=> rw [List.reverse_cons,List.map_append,List.prod_append,anti_mul,List.map_cons,List.map_cons,List.map_nil,List.prod_singleton,ih,hP (s a),List.prod_cons,map_mul]
    change staysM S _=grade (List.ofFn (Y ∘R)).reverse.prod; rw [Massive.UV.Free.Lyre.reversesV,List.reverse_reverse]; convert h (List.finRange n) using 2 <;> simp [List.finRange,List.map_reverse,List.map_ofFn,X,Y, Function.comp_def]; -- edit
section
include hs h
lemma proceed {x:Patio (A⊕Spine I)}(hp:Polite Q (crest s) x):
    (antiE θ x).val=fiber PJ (staysM M (numbered Q A s x))*quill B (armature W p):=by
    let K:= staysM M (numbered Q A s x); let Z:=armature W p
    have hf:Injective p:= u.injective.comp (hs.comp Fin.rev_injective)
    have hk : shade (burst W (crest p))=shade (burst Q (crest s)):=by unfold shade; rw [crestM u s,←burstsM Q W u h, card_map]
    have hG : Hom (shade (burst W (crest p))) K:=by
         have H:= n_stars Q s x; rw [← hk] at H; cases he : shade (burst W (crest p)) <;> rw[he] at H; exact (anti_grade ..).symm.trans (congr_arg _ H); exact (anti_grade ..).symm.trans ((congr_arg (staysM M) H).trans (map_neg ..))
    change staysM θ x.val=_; rw [Quills.charge A Q s x hp hs, anti_mul, anti_l, anti_r,assured _ _ _ _ hP];
    have Hz : Hom (shade (burst W (crest p))) Z:= armG W p hf
    change quill B (grade Z)*fiber PJ K=_; cases he : shade (burst W (crest p)) <;> rw [he] at Hz hG
    · have Ht: Plus (quill B Z):= (embed_grade ..).trans (congr_arg _ Hz); rw [show grade Z= Z from Hz]; exact (Ht.central _).symm.eq
    have Hv: Minus (quill B Z):= (embed_grade ..).trans ((congr_arg (quill B) Hz).trans (map_neg ..))
    rw [show grade Z= -Z from Hz,map_neg]; change _ = fiber PJ K * _; rw [Hv.slides,show grade (fiber PJ K)=fiber PJ (grade K) from embed_grade .., show grade K= -K from hG,map_neg, neg_mul, mul_neg]
lemma backedE (x:Patio (A⊕Spine I))(hp: Polite Q (crest s) x): numbered W B p (antiE θ x)=staysM M (numbered Q A s x) := cuts B W p (u.injective.comp (hs.comp Fin.rev_injective)) _ _ (proceed Q W u h M S hP s hs hp)
end
end YM.MassiveQCD.Sample.Quills.Eden
#print axioms YM.MassiveQCD.Sample.Quills.Eden.anti_exp
#print axioms YM.MassiveQCD.Sample.Quills.Eden.proceed
#print axioms YM.MassiveQCD.Sample.Quills.Eden.backedE
