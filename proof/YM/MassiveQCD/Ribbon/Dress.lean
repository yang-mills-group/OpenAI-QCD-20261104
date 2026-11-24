import YM.MassiveQCD.Ribbon.Sham
/-! # Actual color tensors for the extended dictionary -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Ribbon
open QCD QCD.Grass QCD.Lat QCD.Cove QCD.Creek Function Finset Lattice RG Wilson
open scoped Topology BigOperators ContDiff Classical Kronecker Matrix Matrix.Norms.L2Operator
variable {c:Side}{I:Type}[Fintype I]
variable (N:ℕ) (o:I→Site c)(k:Lat.Frame c)
local notation "S"=> Spine I
local notation "K"=> Keys c N
local notation "M"=> ample N I
lemma color_psi (x : Site c)(b:Flavor N)(p:Pinor)(z:Hue): slots N k (psi ((x,(p,z)),b))=∑ i:Hue, colour (k x) z i • psi ((x,(p,i)),b):=by
   unfold slots; rw [adapt_psi]; unfold Lat.rotates copies siteRot rides touch; simp [Matrix.blockDiagonal_apply, Lat.Fiber, Row,Matrix.one_apply, Fintype.sum_prod_type, ite_smul,ite_mul]
lemma color_bar (x : Site c)(b:Flavor N)(p:Pinor)(z:Hue): slots N k (bar ((x,(p,z)),b))=∑ i:Hue, colour (k x)⁻¹ i z • bar ((x,(p,i)),b):=by
   rw [slots,adapt_bar]; simp_rw [Lat.rotates,← copies_star,siteRot_star]; unfold copies siteRot rides touch; simp [Matrix.blockDiagonal_apply,Lat.Fiber, Row,Matrix.one_apply, Fintype.sum_prod_type,ite_smul,ite_mul]
lemma gaze (k: Lat.Frame c) (x:Alg K)(I:Type)[Fintype I]: slots (ample N I) k (embed (shapeE N I c) x)= embed (shapeE N I c) (slots N k x):=by
   let m:= ample N I; let f:Modes c N→Modes c m:=Prod.map id (scroll N I∘Sum.inl); have hp : (slots m k).comp (pass f)=(pass f).comp (slots N k):=by
      apply ext_atoms; rintro (⟨⟨x,p,z⟩,b⟩|⟨⟨x,p,z⟩,b⟩)
      · change slots m k (pass f (psi _))=pass f (slots N k (psi _)); rw [pass_psi,color_psi]
        rw [color_psi, map_sum]; exact sum_congr rfl fun i _=> by rw [map_smul,pass_psi]; rfl
      change slots m k (pass f (bar _))=pass f (slots N k (bar _)); rw [pass_bar,color_bar]; rw [color_bar,map_sum]; exact sum_congr rfl fun i _=> by rw [map_smul,pass_bar]; rfl
   exact DFunLike.congr_fun hp x
lemma sparkle (v:su.El) : changeVars (colour v) (mono univ)=mono univ:=by
   have ht:= top_change (colour v) (mono univ); rw [show (colour v).det=1 from det_su _,Grass.read,one_mul] at ht; exact (Grass.ceiling (exterior_layer (substitution (colour v)) (homogeneous _))).trans (by unfold changeVars at ht; rw [ht,one_smul])
noncomputable def ray (i:I×Bool): Hue↪Spine I:=⟨fun z=>(i,z),fun _ _ he=> congr_arg Prod.snd he⟩
lemma trio (t:I × Bool): slots (ample N I) k (embed ((ray t).trans (swipeE N o)) (mono univ))= embed ((ray t).trans (swipeE N o)) (mono univ):=by
    let X:= colour (k (o t.1)); let f:= (ray t).trans (swipeE N o); have h : (slots M k).comp (embed f)=(embed f).comp (changeVars X):=by
       apply ext_atoms; intro i; rw [AlgHom.comp_apply, AlgHom.comp_apply,change_atom,embed_atom]; change slots M k (psi ((o t.1,(placket t.2,i)),(scroll N I) (.inr t.1)))=_; rw [color_psi,map_sum]; exact sum_congr rfl fun i _=> by rw [map_smul,embed_atom]; rfl
    exact (DFunLike.congr_fun h (mono univ)).trans (congr_arg (embed f) (sparkle ..)) -- note sparkle params?
lemma lively (s:Finset (I×Bool)): slots M k (embed (swipeE N o) (mono (s×ˢ univ)))=embed (swipeE N o) (mono (s×ˢ univ)):=by
   let X:Alg S→ₐ[ℂ] Fields c M:=(slots M k).comp (embed (swipeE N o)); let Y:= embed (swipeE N o); change X _ = _; induction s using Finset.induction_on with
   | empty=>simp
   | insert i s hi ih=>
      let v:=univ.map (ray i); let r:Finset S:= s×ˢuniv; have he(a):a∈v↔a.1=i:= ⟨fun h=>by obtain ⟨x,h,rfl⟩:= mem_map.mp h; rfl, fun h=> mem_map.mpr ⟨a.2,mem_univ _,Prod.ext h.symm rfl⟩⟩
      have hd:Disjoint v r:= Finset.disjoint_left.mpr (fun a ha hu=>hi ((he _).1 ha ▸ (mem_product.mp hu).1))
      have hx:(insert i s)×ˢuniv=v∪r:= by ext i; simp [he,r]
      have hA: X (mono v)=Y (mono v):=by
         have hY:X (embed (ray i) (mono univ))=Y (embed (ray i) (mono univ)):=by
            change slots M k (embed _ (embed _ _))=embed _ (embed _ _); rw [embed_comp]; exact trio ..
         rcases embed_blade (ray i) univ with h|h <;>rw [h] at hY; exact hY; rw [map_neg,map_neg] at hY; exact neg_injective hY
      rw [hx]; have hX:X (mono v*mono r)= Y (mono v* mono r):=by rw [map_mul,map_mul,hA]; exact congr_arg _ ih
      rcases mono_mul_sign _ _ hd with hp|hp<;>rw [Finset.disjUnion_eq_union] at hp<;>rw [hp] at hX; exact hX; rw [map_neg,map_neg] at hX; exact neg_injective hX
variable (q:I→Bool)(s:Finset I)(a:ℝ)
lemma signal (x: Alg K): slots M k (pen N o a (stake _ (burst q s) x))=pen N o a (stake _ (burst q s) (slots N k x)):=by
   simp only [pen,AlgHom.comp_apply, stretches,map_smul];
   let i:=burst q s; rw [markedOut,markedOut]; simp only [map_mul];
   let H:=quill K (mono i); have hf x:embed (territory N o) (fiber S x)= embed (shapeE N I c) x:= embed_comp .. ; have ht:embed (territory N o) H= embed (swipeE N o) (mono i):=embed_comp ..
   simp only [hf,gaze]; rw [ht]; unfold i burst; rw [lively N o k (post q s)] -- def notation
lemma penkin (x:Alg K) (ha:0<a) (v:Finset S): load (fun _=>a) (pen N o a (stake _ v x))=load (fun _=>a) x:=by
    let w:= (fun _: Keys c M=>a); rw [pen,AlgHom.comp_apply,transplant (q:=fun _=>a) (k:=fun _=>ha)]; -- edit
    rw [show (fun _=> a) ∘ ⇑(territory N o)=expRate (p:=fun _=>a) (q:=fun _=>a) from funext fun i=>by cases i<;>rfl,stretches,stakesBill (p:=fun _=>a) (q:=fun _=>a) (fun _=>ha) (fun _=>ha),Finset.prod_const,load_scale,norm_pow,Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr ha).le]; rw [← mul_assoc,← mul_pow, mul_inv_cancel₀ ha.ne',one_pow,one_mul]
end YM.MassiveQCD.Ribbon
