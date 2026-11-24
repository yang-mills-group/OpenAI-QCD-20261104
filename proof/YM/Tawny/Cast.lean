import YM.Tawny.Fleur
import YM.Tawny.Went
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
open Pane TensorProduct Revolve UV.Free KeysP BendR
namespace Cast
variable {I:Type}
variable (K:Signed→ I→ I)(A:Signed→ I→ ℝ)(Cw:I→I)(e:ℂ)
-- Generic Family.Both before lift.Burn. readout funding via ℝ wrappers
structure Meaning (d:ℕ)(x:I→Label d):Prop where
   light i: Quiet (x i).val
   coal i: chargeAct (x i).val=(x i).val
   ringo (s:Signed)(w:EuPin)(h:w.Lifts s) i: pinAct w (x i).val=(↑(A s i):ℂ) • (x (K s i)).val
   sym i:x (Cw i)=e • x i
noncomputable def Steno (d:ℕ):Submodule ℂ (I→ Label d) where
   carrier:={x|Meaning K A Cw e d x}
   zero_mem':= by refine ⟨fun i=>⟨map_zero _,fun u=> map_zero _⟩,fun i=>map_zero _,fun s w hw i=>by simp,fun i=>by simp⟩
   add_mem':= by
       intro x y hx hy; change Meaning _ _ _ _ d _ at hx hy; refine ⟨fun i=>⟨?_,fun u=>?_⟩,fun i=>?_,fun s w h i=>?_,fun i=>?_⟩
       · simp only[Pi.add_apply,Submodule.coe_add,map_add,(hx.light _).1,(hy.light _).1]
       · simp only[Pi.add_apply,Submodule.coe_add,map_add,(hx.light _).2,(hy.light _).2]
       · simp only [Pi.add_apply,Submodule.coe_add,map_add,hx.coal,hy.coal]
       · simp only [Pi.add_apply,Submodule.coe_add,map_add,hx.ringo _ _ h,hy.ringo _ _ h,smul_add]
       simp only [Pi.add_apply,hx.sym,hy.sym,smul_add]
   smul_mem':= by
       intro z x hx; change Meaning _ _ _ _ d x at hx; refine ⟨fun i=>⟨?_,fun u=>?_⟩,fun i=>?_,fun s w h i=>?_,fun i=>?_⟩
       · simp only [Pi.smul_apply, Submodule.coe_smul,map_smul,(hx.light _).1]
       · simp only [Pi.smul_apply, Submodule.coe_smul,map_smul,(hx.light _).2]
       · simp only [Pi.smul_apply, Submodule.coe_smul,map_smul,hx.coal]
       · simp only [Pi.smul_apply, Submodule.coe_smul,map_smul,hx.ringo _ _ h]; rw [smul_comm]
       simp only [Pi.smul_apply,hx.sym]; rw [smul_comm]
local notation "Y"=> Steno K A Cw e d
noncomputable def book : Steno K A Cw e d →ₗ[ℂ] (I→GPol):= LinearMap.pi fun i:I=> fog ∘ₗ (UV.labels d).subtype ∘ₗ (LinearMap.proj i) ∘ₗ (Y).subtype
noncomputable def valet (hd:d≤10): Y →ₗ[ℂ] StressFlux.Offer.spectral (G:=su) (d:=d/2) K A where
  toFun x:=⟨fun i=>⟨fog (x.val i).val,diets (x.val i) ((show Meaning _ _ _ _ d _ from x.property).light i) hd⟩,by
       intro s i; obtain ⟨w,h⟩:=EuPin.choice s; have ht:=show Meaning _ _ _ _ d _ from x.property; have he:= wrought w s h (x.val i) (ht.light i) hd
       apply Subtype.ext; rw[ht.ringo _ _ h _, map_smul] at he; exact he.symm⟩
  map_add' x y:=Subtype.ext (funext fun i=>Subtype.ext (map_add fog _ _)) -- infer
  map_smul' z x:=Subtype.ext (funext fun i=>Subtype.ext (map_smul fog _ _))
open StressFlux.Offer (acts marks Vc)
noncomputable abbrev RawTensor (e:ℂ) (d:ℕ):= Steno acts marks Prod.swap e d
noncomputable abbrev RawVec (d:ℕ):= Steno Vc signT id 1 d
variable (p q:Multi d)
noncomputable def ingot : Bundle→ₗ[ℂ]Spike:= { toFun:=Stew.gold,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
noncomputable def prism0 : Pol d→ₗ[ℂ]Spike:= ingot ∘ₗ gravel a a p q ∘ₗ skin 0
lemma probed (x:Pol d) : prism0 a p q x=silver a p q x:=rfl
variable (u v:Axis)
-- mixed pick.B with actual profile.named e
noncomputable abbrev Gpick := ruby_pick.choose
noncomputable abbrev Rpick := su.colorMat Gpick
lemma findSlot : ∃ i j:Hue,Rpick i j≠0:=by by_contra! h; apply gem Gpick ruby_pick.choose_spec; ext i j; exact h _ _
noncomputable abbrev iPick:Hue:=findSlot.choose
noncomputable abbrev jPick:Hue:=findSlot.choose_spec.choose
noncomputable def gold2 : Bundle→ₗ[ℂ]Spike:= (Rpick iPick jPick)⁻¹ • (show _ from {
    toFun:=fun B:Bundle=> fun i j=> B (i,iPick) (j,jPick),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }: Bundle→ₗ[ℂ]Spike)
noncomputable def prism1 : Pol d→ₗ[ℂ]Spike:= gold2 ∘ₗ gravel a a p q ∘ₗ ray (StressFlux.leg0 u v Gpick)
open scoped Kronecker
lemma gilt2 (M:Spike): gold2 (M ⊗ₖ ore Gpick)=M:=by
    ext i j; have he :Rpick iPick jPick≠0:= findSlot.choose_spec.choose_spec
    change (Rpick iPick jPick)⁻¹ * (M i j*Rpick iPick jPick)= M i j; field_simp
lemma probedT (x:Label d)(h:Quiet x.val)(hd:d≤10) : prism1 a p q u v x.val=twin a a x h hd p q u v:=by
    change gold2 (gravel _ _ _ _ (ray _ x.val))=_; rw [pare a a x h hd]; exact gilt2 _
-- Reconstruction
lemma denovo(x:Label d)(h:Quiet x.val)(hd:d≤10)(hZ:fog x.val=0)(he:∀ a:Flavor 6,∀ p q:Multi d,spinWeight p+spinWeight q ≤ d → prism0 a p q x.val=0)(hT:∀ a:Flavor 6,∀ p q:Multi d,spinWeight p+spinWeight q+4 ≤ d →∀ u v:Axis, prism1 a p q u v x.val=0) : x=0:=by
     let D:= skin 0 x.val; let L:=glow x h hd; have hP : D = 0:=by
          ext ⟨⟨p,i⟩,a⟩ ⟨⟨q,j⟩,b⟩; by_contra hN; obtain ⟨hx,hk⟩:= (stocks x h hd).lean _ _ hN; change a=b at hx; subst b; have he : gravel a a p q D = 0:=by unfold D; rw[root_color a a p q x h hd, show Stew.gold (gravel a a p q (skin 0 x.val))=0 from he a p q hk]; ext ⟨p,w⟩ ⟨r,u⟩; simp [wave]
          exact hN (congr_fun (congr_fun he i) j)
     have hp (u v:Axis)(z:su.Color): L (StressFlux.leg0 u v z)=0:=by
          set X:=StressFlux.leg0 u v z; ext ⟨⟨p,i⟩,a⟩ ⟨⟨q,j⟩,b⟩; by_contra hN; obtain ⟨hx,hk⟩:= (stocks x h hd).loop.choose_spec.2 X _ _ hN; change a=b at hx; subst b; have he:gravel a a p q (L (StressFlux.leg0 u v z))=0:=by unfold L; rw [← glean x h hd,pare a a x h hd,← probedT,hT a p q hk u v]; ext; simp; rfl -- proof?
          exact hN (congr_fun (congr_fun he i) j)
     apply Subtype.ext; apply Poised.Display.distinct; intro J; have hJ: J 0=(2:ℝ)⁻¹ • ∑ i:Axis, ∑ j:Axis, StressFlux.leg0 i j (StressFlux.curl0 i j (J 0)):=by rw [StressFlux.sum_legs0,smul_smul]; norm_num
     have hL:L (J 0)=0:=by nth_rw 1[hJ]; simp only [map_smul,map_sum,hp,sum_const_zero,smul_zero]
     rw [visualP _ x h hd,hZ,map_zero,zero_smul, zero_add, shiny _ x h hd, show glow x h hd (J 0)=0 from hL, add_zero, show skin 0 x.val=0 from hP,map_zero]; exact Eq.symm (map_zero _)
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.valet
#print axioms YM.Massive.Tawny.Cast.denovo
