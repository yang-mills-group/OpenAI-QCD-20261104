import YM.MassiveQCD.Cupola.Shutter
/-!
 Marker relabeling on graded variables. Uses right-stamps. Choose signs canonically on singleton bursts (to implement actual translation averaging with positive weights), but for higher stamps preserve the inherited order (hence sign).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Function Finset Ribbon Cupola
open scoped Topology BigOperators ContDiff Classical
variable {A B C I J :Type}[Fintype A][Fintype B][Fintype C][Fintype I][Fintype J]
variable (q:I→Bool)(p:J→Bool)
local notation "R"=>Spine I
local notation "S"=>Spine J
-- partial assignments bound only per admissible set.Launched.
lemma hueEq (i:I)(j:J)(hq:q i=p j): (burst q {i}).image (fun b=>((j,b.1.2),b.2))= burst p {j}:=by
    ext ⟨⟨j',y⟩,s⟩; simp only [mem_image]; constructor
    · rintro ⟨⟨⟨u,a⟩,z⟩,hx,h⟩; change ((j,a),z) = ((j',y),s) at h; obtain ⟨hV,rfl⟩:= Prod.mk.inj h; obtain ⟨rfl,rfl⟩:=Prod.mk.inj hV; have hp:u=i:=mem_singleton.mp (Ribbon.located q {i} _ hx); subst u; simpa [burst,post,hq] using hx
    intro hx; have ht:j'=j:=mem_singleton.mp (Ribbon.located p {j} _ hx); subst j'; exact ⟨((i,y),s),by simpa [burst,post,hq] using hx,rfl⟩
lemma brightInj (i:I)(j:J) : Set.InjOn (fun b: Spine I=>((j,b.1.2),b.2)) ((burst q {i}):Set (Spine I)):=by
    rintro ⟨⟨i',v⟩,s⟩ hi ⟨⟨u,w⟩,z⟩ hu h; have hx:i'=i:=mem_singleton.mp (Ribbon.located q {i} _ hi); have he:u=i:=mem_singleton.mp (Ribbon.located q {i} _ hu); change ((j,v),s)=((j,w),z) at h; obtain ⟨e,rfl⟩:=Prod.mk.inj h; rw [hx,he,(Prod.mk.inj e).2]
lemma stampSet [DecidableEq B] (f:A→B)(x:Finset A)(h:Set.InjOn f (x:Set A)): embed f (mono x)=mono (x.image f) ∨ embed f (mono x) = -mono (x.image f):=by
   obtain ⟨w,hw,he,hB⟩:= expression x; let g:= f ∘ w; let L:=List.ofFn g
   have ht:embed f (mono x)=(L.map atom).prod:=by rw [hB,map_list_prod]; simp [L,g,Function.comp_def]
   rw [ht, show x.image f=L.toFinset from (by ext; simp [he,L,g])]; exact sign_product L (List.nodup_ofFn_ofInjective (fun i j e=> hw (h ((he _).2 ⟨_,rfl⟩) ((he _).2 ⟨_,rfl⟩) e))) -- Fin params
noncomputable def voteR (i:I)(j:J):Spine I→Spine J:= fun b=>((j,b.1.2),b.2)
noncomputable def dirSign (i:I)(j:J):ℝ:=if embed (voteR i j) (mono (burst q {i})) = mono (burst p {j}) then 1 else -1
lemma reMon (i:I)(j:J)(h:q i=p j) : embed (voteR i j) (mono (burst q {i}))=(↑(dirSign q p i j):ℂ) • mono (burst p {j}):=by
     have hv:(burst q {i}).image (voteR i j)= burst p {j}:=hueEq q p i j h
     unfold dirSign; split
     next he=> simp only [he,Complex.ofReal_one,one_smul]
     next he=>
       simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_smul,one_smul]; let y:=mono (burst p {j}); rcases stampSet (voteR i j) (burst q {i}) (brightInj ..) with h1|h1
       · exact (he (h1.trans (congr_arg mono hv))).elim
       exact h1.trans (congr_arg (fun x=>-mono x) hv)
lemma signAbs (i:I)(j:J):|dirSign q p i j|=1:=by unfold dirSign; split<;> norm_num
variable (f:I→Option J) (g:I→J→ℝ) -- factor real, callers
noncomputable def stencil (a:Spine I)(b:Spine J):ℂ:= if f a.1.1= some b.1.1 ∧ b=voteR a.1.1 b.1.1 a then 1 else 0
variable (A)
noncomputable def blot : Matrix (A⊕Spine I) (A⊕Spine J) ℂ:= Matrix.fromBlocks 1 0 0 (stencil f)
noncomputable def slot : I→ℝ:=fun i=> (f i).elim 1 (fun j=> (dirSign q p i j)*g i j)
noncomputable def leaves : Alg (A⊕Spine I)→ₐ[ℂ] Alg (A⊕Spine J):=(changeVars (blot A f)).comp (vscale A (slot q p f g)) -- vscale uses real
noncomputable def flame : Patio (A⊕Spine I) →ₐ[ℂ] Patio (A⊕Spine J):= car (leaves A q p f g) (fun x h=> (exterior_parity (substitution (blot A f)) _).trans (congr_arg _ (show Grass.grade (vscale A (slot q p f g) x)=vscale A (slot q p f g) x from (scaler A (slot q p f g) (⟨x,h⟩:Patio (A⊕Spine I))).property))) -- adjust binder
lemma blot_left (x:Alg A): changeVars (blot A f) (fiber R x)=fiber S x:=by
    have h:(changeVars (blot A f)).comp (fiber R)=fiber S (A:=A):=by apply ext_atoms; intro i; rw [AlgHom.comp_apply,embed_atom,embed_atom,change_atom,Fintype.sum_sum_type]; simp [blot,Matrix.one_apply,ite_smul]
    exact DFunLike.congr_fun h _
lemma allot (i:I)(j:J)(h:f i=some j)(x: Spine I)(hx:x.1.1=i): changeVars (blot A f) (atom (Sum.inr x))=atom (Sum.inr (voteR i j x)):=by
   rw [change_atom,Fintype.sum_sum_type]; simp only [blot,Matrix.fromBlocks_apply₂₁,Pi.zero_apply,Matrix.zero_apply,zero_smul,sum_const_zero,zero_add,Matrix.fromBlocks_apply₂₂]; rw [sum_eq_single (voteR i j x)]; simp [stencil,hx,voteR,h]; intro b _ hh; rw [stencil,if_neg,zero_smul]; exact fun ⟨e,r⟩=> hh (by rw [hx,h] at e; rw [hx,← Option.some.inj e] at r; exact r) -- b projections.Subst error
   simp
lemma leaving (i:I)(j:J)(h:f i=some j)(hp:q i=p j) : leaves A q p f g (quill A (mono (burst q {i})))=(↑(g i j):ℂ) • quill A (mono (burst p {j})):=by
   have hx(s:Finset R) : vscale A (slot q p f g) (quill A (mono s))=pole (slot q p f g) s • (quill A (mono s)):=by simpa only [markedOut,map_one,one_mul] using tarStake A (slot q p f g) 1 s
   have hh: changeVars (blot A f) (quill A (mono (burst q {i})))=quill A (embed (voteR i j) (mono (burst q {i}))):=by
      obtain ⟨w,_,he,e⟩:= expression (burst q {i}); rw [e,map_list_prod,map_list_prod,map_list_prod,map_list_prod]; apply congr_arg List.prod; simp only [List.map_ofFn]; congr 1; funext k; change changeVars _ (quill _ (atom (w k)))=quill _ (embed _ (atom (w k))); rw [embed_atom,embed_atom,embed_atom]; exact allot A f i j h _ (mem_singleton.mp (Ribbon.located _ _ _ ((he _).mpr ⟨_,rfl⟩))) -- direction
   rw [leaves,AlgHom.comp_apply,hx,sensed q, prod_singleton,map_smul,hh,reMon _ _ _ _ hp,map_smul, smul_smul]; apply congr_arg (fun z:ℂ=> z • quill A (mono (burst p {j}))) -- edit
   unfold slot; rw [h,Option.elim_some,Complex.ofReal_mul]; unfold dirSign; split<;> simp
end YM.MassiveQCD.Sample
