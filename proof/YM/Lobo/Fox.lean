import YM.Lobo.Tyre
import YM.Extra.WEAK_SCALING_ACTLAW.Pairs
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole TableT Pane Massive.Poised.Plans.Stamp
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open StressFlux (pair curl0)
open Finset
variable (u:Flavor 6)(M:Spike)(a b:Axis)
local notation "L"=>Label 8
local notation "U"=>(0:Multi 8)
noncomputable abbrev Sx(f:Flavor 6)(t:Spike):Label 8:=solstice f t U U (by rw [cost_root]; decide)
noncomputable abbrev Pa(f:Flavor 6)(t:Spike)(i:Axis):Label 8:=solstice f t (UV.first i) U (by rw[juicy,cost_root])
noncomputable abbrev Ai(f:Flavor 6)(t:Spike)(i:Axis):Label 8:=solstice f t U (UV.first i) (by rw[juicy,cost_root])
noncomputable abbrev Qa(d:ℕ):Submodule ℂ (Label d):=by
     refine {carrier:={x|Quiet x.val},add_mem':=?_,zero_mem':=?_,smul_mem':=?_} -- order
     · rintro x y ⟨h,h'⟩ ⟨e,e'⟩; change Quiet (x+y).val; rw [Submodule.coe_add]; exact ⟨(map_add ..).trans (by rw[h,e]),fun u=>(map_add ..).trans (by rw[h',e'])⟩
     · exact ⟨map_zero _,fun _=>map_zero _⟩
     rintro c x ⟨h,h'⟩; change Quiet (_ • x.val); refine ⟨?_,fun u=>?_⟩; · rw [map_smul,h]
     rw[map_smul,h']
open Extra.WeakScaling.Color
lemma pairWise (c k:Axis) : pairLabel su a b c k=pair su a b c k:=by
     have h(A:Labels.Taylor su 0)(i j:Axis):strength A i j=curl0 i j A:=by
          rw [StressFlux.curl0_value]; have he:= Extra.WeakScaling.Color.skew A i j; unfold strength at *; have ht:A.value j (basis i)= - A.value i (basis j):=by apply smul_right_injective (M:=su.Color) (two_ne_zero (α:=ℝ)); simpa only [smul_neg] using he
          rw [ht]; module
     apply Subtype.ext; apply Labels.eval_ext; intro J; rw[show (pairLabel su a b c k).val=pairPol su a b c k from rfl,pair_eval, h,h]; exact (StressFlux.pair_value ..).symm
variable (x:Label 8)(hx:Quiet x.val) (B:Submodule ℂ (Label 8)) (s:RawSym)
local notation "P"=> (B)
lemma ceo(g:Labels.Label su 4)(h:s.unit 8∈B)(hr:∀ a b c t:Axis,GG a b c t∈ B) : dowry (d:=8) g∈ B:=by
     obtain ⟨x,p,H⟩:= inputs QCD.simple g; rw[H]; let F: Labels.Label su 4→ₗ[ℂ]L := {toFun:=(fun x => dowry (d:=8) (show Labels.Label su (8/2) from x)),map_add':=fun u v=>Subtype.ext (map_add (Perla.plain 8) u.val v.val),map_smul':=fun z u=>Subtype.ext (map_smul (Perla.plain 8) z u.val) }
     change F _ ∈ _; simp_rw[pairWise,map_add,map_sum,map_smul]; have ht : F (Labels.unit su 4)=s.unit 8:=Subtype.ext (s.unitActs _).symm; exact B.add_mem (B.smul_mem _ (ht ▸ h)) (B.sum_mem (fun i _=> B.sum_mem (fun j _=>B.smul_mem _ (hr ..))))
include hx
lemma grove (h:s.unit 8∈B)(hr:∀ a b c t:Axis,GG a b c t∈B)(he:∀ (a:Flavor 6)(M:Spike), Sx a M ∈ B ∧∀ i:Axis,Pa a M i∈B ∧ Ai a M i∈B) : x∈ B:=by
     let Q:=Qa 8; let I:Finset (Multi 8 × Multi 8):= univ.filter fun i=> spinWeight i.1 + spinWeight i.2 ≤ 8; let f(a:Flavor 6)(i:I):Label 8:= solstice a (prism0 a i.val.1 i.val.2 x.val) i.val.1 i.val.2 ((mem_filter.mp i.property).2)
     let Y:=∑ a:Flavor 6,∑ i:↥I,f a i; let g:Labels.Label su 4:=⟨fog x.val,diets x hx (by norm_num)⟩; let D:= dowry (d:=8) g
     have hW(i:I)(a:Flavor 6): f a i∈ Q:=(show Quiet _ from flora _ (prism0 a i.val.1 i.val.2 x.val) i.val.1 i.val.2 ((mem_filter.mp i.property).2))
     have hh : Y∈Q:= Q.sum_mem (fun a _=> Q.sum_mem (fun i _=>hW i a))
     have hZ:D∈Q:= plainQ ..
     let W:= x-(D+Y); have ht:W=0:=by
          apply denovo W (Q.sub_mem hx (Q.add_mem hZ hh)) (by norm_num)
          · unfold W D Y; simp only [Submodule.coe_sub, Submodule.coe_add, AddSubmonoidClass.coe_finsetSum,_root_.map_sum,map_sub,map_add]; simp only [show fog (dowry (d:=8) g).val= fog x.val from unit_fog _, show ∀ a i,fog (f a i).val=0 from fun _ _=> bareFog .., sum_const_zero,add_zero,sub_self]
          · intro a p q ht; unfold W D Y; simp only[Submodule.coe_sub, Submodule.coe_add, AddSubmonoidClass.coe_finsetSum,_root_.map_sum,map_sub,map_add]; rw [show prism0 a p q (dowry (d:=8) g).val=0 from clear_P .., zero_add]; simp only[show ∀ b i,(f b i).val =bilinear b b (prism0 b i.val.1 i.val.2 x.val) i.val.1 i.val.2 from (fun b i=>rfl),fun b i j M=> bareB a b M p q i j] -- arg order
            rw [sum_eq_single a (fun i _ h=>by simp [Ne.symm h]) (by simp)]; let i:↥I:=⟨(p,q),mem_filter.mpr ⟨mem_univ _,ht⟩⟩; rw [sum_eq_single i]
            · rw [if_pos ⟨rfl,rfl,rfl⟩]; exact sub_self _
            · intro j _ h; rw [if_neg (by rintro ⟨r,h₀,h'⟩; exact (show j≠ i from h) (Subtype.ext (Prod.ext h₀.symm h'.symm)))] -- shadows
            simp
          intro a p q h; unfold spinWeight at h; omega
     rw [show x=D+Y from sub_eq_zero.mp ht]; apply B.add_mem (ceo B s g h hr); refine B.sum_mem (fun i _=>B.sum_mem (fun v _=>?_)); let a':= v.val.1; let t':= v.val.2; obtain hp|⟨j,hp⟩|⟨j,hp⟩ := (twoL a' t' (mem_filter.mp v.property).2) -- inspect
     · let M:=prism0 i a' t' x.val; apply Eq.mp (congr_arg (fun x:L=>x∈B) (?_ : Sx i M=f i v)) ((he i M).1); apply Subtype.ext; change bilinear i i M U U=bilinear i i M a' t'; rw [hp.1,hp.2]
     · let M:=prism0 i a' t' x.val; apply Eq.mp (congr_arg (fun x:L=>x∈B) (?_ : Pa i M j=f i v)) (((he i M).2 j).1); apply Subtype.ext; change bilinear i i M (UV.first j) U=bilinear i i M a' t'; rw [hp.1,hp.2]
     let M:=prism0 i a' t' x.val; apply Eq.mp (congr_arg (fun x:L=>x∈B) (?_ : Ai i M j=f i v)) (((he i M).2 j).2); apply Subtype.ext; change bilinear i i M U (UV.first j)=bilinear i i M a' t'; rw [hp.1,hp.2]
end YM.Lobo
#print axioms YM.Lobo.ceo
#print axioms YM.Lobo.Qa
#print axioms YM.Lobo.grove
