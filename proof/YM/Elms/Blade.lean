import YM.Elms.Leaf
/-! # Port of central grading to projected weighted capacities, real algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace PrismD
variable (H: SourceRead.TaperHol)
open QCD.Kites Beacon -- glowing conflicts.
lemma dry (x:Pol d)(J:Labels.Jet su): SourceRead.Agrees (SourceRead.desired x J) (SourceRead.desired (setas d x).val J):=by
    rw [← funext (observe _ x),← funext (observe _ _)]; refine ⟨(painted ..).contDiffAt,(painted ..).contDiffAt,?_⟩; intro i hi; rw [order_test,order_test]; rw [show geometry i (setas d x).val=geometry i x from drips_geom i d x hi]
lemma plusA (X Y: Insertion n 6)(x y:Mini d) (hp:ActionTest H o X x.val)(hq: ActionTest H o Y y.val): ActionTest H o (X+Y:Insertion n 6) (x+y:Mini d).val:=by
   refine Poised.Plans.Orientation.actsPlus H o d X Y _ _ hp hq
lemma constA(t:ℂ)(X:Insertion n 6)(x:Mini d)(hp:ActionTest H o X x.val): ActionTest H o (t • X:Insertion n 6) (t • x:Mini d).val:= Poised.Plans.Orientation.acting H o d X x.val hp t
noncomputable abbrev foldP (d:ℕ)(x:Mini d)(y:Mini d):= setas d (x.val*y.val)
lemma mulA(X Y:Insertion n 6)(x y: Mini d)(hp: ActionTest H o X x.val)(hq:ActionTest H o Y y.val): ActionTest H o ⇑(X*Y) (foldP d x y).val:=by
    intro J; let f:=Poised.Beacon.moment (d:=d) H o J X; let g:=moment (d:=d) H o J Y; let sx:=SourceRead.desired x.val J; let sy:=SourceRead.desired y.val J; have hx:=hp J; have hy:=hq J
    rw [show moment (d:=d) H o J ⇑(X*Y)= f*g from funext fun i=>map_mul (adapter ..) ..]; have hr : SourceRead.Agrees (sx*sy) (SourceRead.desired (foldP d x y).val J):=by
      rw [show sx*sy=SourceRead.desired (x.val*y.val) J from funext fun i=>by unfold sx sy; rw [Pi.mul_apply,← observe,← observe,← observe,observe_prod]]; exact dry ..
    refine ⟨hx.1.mul hy.1,hr.2.1,fun i hi=>?_⟩; rw [←hr.2.2 _ hi]; rw [iteratedDeriv_mul (hx.1.of_le ?_) (hy.1.of_le ?_),iteratedDeriv_mul (hx.2.1.of_le ?_) (hy.2.1.of_le ?_)] -- spinpol not ℝ NormedAlgebra? ok
    apply Finset.sum_congr rfl; intro j hj; rw [hx.2.2 _ (by simp only [Finset.mem_range] at hj; omega), hy.2.2 _ (by omega)] -- may minted m uses f in goal
    all_goals exact_mod_cast hi
noncomputable def prism (t v:ℝ)(d:ℕ): Mini d →ₗ[ℂ] Mini d:= (setas d).comp ((widths t v).comp (cap d).subtype)
lemma measures (x:Mini d)(t v:ℝ): (prism t v d x).val=widths t v x.val:=drips_identity _ (sizes_cap _ _ _ x.property)
lemma widthMul (x y:Pol d)(t v:ℝ): widths t v (x*y)=widths t v x * widths t v y:=by apply Display.distinct; intro J; rw [← one_scene,observe_prod,countingG,countingG,countingG,observe_prod,map_mul]
lemma widthDry (x:Pol d)(t v:ℝ): widths t v (drips d x)=drips d (widths t v x):=by
   refine DFunLike.congr_fun (f:=(widths t v).comp (drips d)) (g:=(drips d).comp (widths t v)) ?_ x; apply (zBasis d).ext; intro j
   rw [minted,LinearMap.comp_apply,LinearMap.comp_apply,drips_gen,widths_m,map_smul,drips_gen]; split; · exact widths_m ..
   rw [smul_zero,map_zero]
lemma prism_set (x:Pol d)(t v:ℝ): prism t v d (setas d x)=setas d (widths t v x):= by apply Subtype.ext; rw [measures]; exact widthDry x t v
lemma prism_fold (x y:Mini d)(t v:ℝ): prism t v d (foldP d x y)=foldP d (prism t v d x) (prism t v d y):=by rw [foldP,prism_set,widthMul,←measures,←measures]
noncomputable def foldW(d:ℕ): Mini d→ₗ[ℂ] Mini d→ₗ[ℂ] Mini d:= by
   let F : Mini d →ₗ[ℂ] Pol d := (cap d).subtype
   refine { toFun:= fun x=> (setas d).comp ((LinearMap.mulLeft ℂ x.val).comp F), map_add':=fun x y=> LinearMap.ext (fun t=>?_), map_smul':=fun c y=>LinearMap.ext (fun t=>?_) }
   · change setas d ((x.val+y.val)*t.val)=_; rw [add_mul,map_add]; rfl
   change setas d ((c • y.val)*t.val)=_; rw [_root_.smul_mul_assoc,map_smul]; rfl
lemma foldH {V: Type*}(X Y:V → Mini d)(x y:Mini d)(l:Filter V)(hX:Tendsto X l (𝓝 x))(hY:Tendsto Y l (𝓝 y)): Tendsto (fun i=>foldP d (X i) (Y i)) l (𝓝 (foldP d x y)):=by
     let F:Mini d →ₗ[ℂ] (Mini d→L[ℂ] Mini d):= LinearMap.toContinuousLinearMap.toLinearMap.comp (foldW d)
     let P:= fun z : Mini d × Mini d => F z.1 z.2; have h: Continuous P:= ((F.continuous_of_finiteDimensional).comp continuous_fst).clm_apply continuous_snd
     exact (h.tendsto _).comp (hX.prodMk_nhds hY)
lemma fold_taps (x y:Pol d): foldP d (setas d x) (setas d y)=setas d (x*y):=Subtype.ext ((mulDry_left d d x _).trans (mulDry_right d d x y))
lemma fold_scale(x y:Mini d)(t v:ℂ): foldP d (t • x) (v • y)= (t*v) • foldP d x y:=by unfold foldP; change setas d ((t • x.val)*(v • y.val))=_; rw [_root_.smul_mul_assoc,_root_.mul_smul_comm,map_smul,map_smul,smul_smul]
-- spin terrain accounts:
variable {x:Insertion n 6}{p: Mini d}
lemma reading (t v:ℝ)(J:Labels.Jet su)(hp:ActionTest H o x p.val): SourceRead.Agrees ((engine v (Letters d)) ∘ (Poised.Beacon.moment (d:=d) H o (t • J) x)) (SourceRead.desired (prism t v d p).val J):=by
    let M:=(engine v (Letters d)).toLinearMap.toContinuousLinearMap.restrictScalars ℝ; have hv :SourceRead.desired (prism t v d p).val J=M∘ SourceRead.desired p.val (t • J) :=by
        funext i; change SourceRead.desired _ J i=M (SourceRead.desired _ _ i); rw [← observe,← observe,measures,countingG]; rfl
    have ht:=hp (t • J); rw [hv]; refine ⟨M.contDiff.contDiffAt.comp _ ht.1,M.contDiff.contDiffAt.comp _ ht.2.1,fun i hi=>?_⟩; change iteratedDeriv i (M∘ _) 0= _; rw [clm_step _ _ _ (ht.1.of_le ?_),clm_step _ _ _ (ht.2.1.of_le ?_),ht.2.2 _ hi] <;> exact_mod_cast hi
lemma sizedSpin (Y:Drape)(p:Mini d)(e g:ℕ)(h:Draft Y g e)(hX:∀ (n:Side)(u:Cover)(U:Grid n), Y n u U∈ Grass.layer (Pairs (Modes n 6)) e)(hp:ActionTest H o (Y n o) p.val) (v t:ℝ): prism t v d p=(v:ℂ)^e • prism t 1 d p:=by
    apply Subtype.ext; apply Display.unique _ _ (Submodule.coe_mem _) (Submodule.coe_mem _); intro J; let f:= Poised.Beacon.moment (d:=d) H o (t • J) (Y n o); have hY:∀ x,f x∈ layer (Pairs (SpinMode d)) e:= fun x=> Grass.exterior_layer _ (hX ..) -- annotation
    let x:=prism t v d p; let y:= prism t 1 d p; let u:ℂ:= (v:ℂ)^e; let g:=SourceRead.desired y.val J
    have hF(v:ℝ): engine v (Letters d)∘ f=(v:ℂ)^e • f:= funext fun i=> nominate _ _ _ (hY i)
    have hm: SourceRead.Agrees (u • f) (SourceRead.desired x.val J) :=by unfold u x; rw [← hF]; exact reading o H t v J hp
    have hg : SourceRead.Agrees f g := by
       have he: engine 1 (Letters d)∘ f=f:=by rw [hF]; simp
       rw [← he]; exact reading o H t 1 J hp
    rw [show SourceRead.desired (u • y:Mini d).val J=u • g from funext fun i=> by unfold g; rw [← observe,Submodule.coe_smul_of_tower,map_smul,observe]; rfl]
    refine ⟨hm.2.1,(hg.2.1).const_smul u,fun i hi=>?_⟩; change iteratedDeriv i (SourceRead.desired x.val _) _=_; rw [← hm.2.2 _ hi]; exact scales f g u i (hg.1.of_le (by exact_mod_cast hi)) (hg.2.1.of_le (by exact_mod_cast hi)) (hg.2.2 i hi)
 where
    scales (f g : ℝ→SpinPol d)(t:ℂ)(i:ℕ)(hx:ContDiffAt ℝ i f 0)(hz: ContDiffAt ℝ i g 0)(he:iteratedDeriv i f 0=iteratedDeriv i g 0): iteratedDeriv i (t • f) 0=iteratedDeriv i (t • g) 0:=by let L:=(t • (ContinuousLinearMap.id ℂ (SpinPol d))).restrictScalars ℝ; change iteratedDeriv i (L∘f) 0= iteratedDeriv i (L∘g) 0; rw [clm_step _ _ _ hx,clm_step _ _ _ hz,he]
end PrismD
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PrismD.sizedSpin
