import YM.Sunda.Cup
import YM.Sunda.Himal
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx Massive.Tarn.ChargeQ
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
local notation "X0"=> equip T ρ A.jet
open Sunda Lobo
open Sunda Lobo Finset UV.Pearl Massive.Oriole
local notation "q"=> K.focus none 9
local notation "f"=> clipF
abbrev leftA (p:RawSym)(a: Flavor 6)(x: Label 9):Label 9:=p.flavor 9 (clipF a) x - x
abbrev subA(p:RawSym)(a:Flavor 6)(x: Label 9):Label 9:=p.flavor 9 (ic a) x-(-Complex.I) • x
noncomputable def goR(p:RawSym)(x:Label 9):Label 9:= subA p 0 (subA p 1 (subA p 2 (leftA p 0 (leftA p 1 (leftA p 2 x)))))
lemma hull(p:RawSym)(x:Label 9): (goR p x).val∈ heapZ:=by
      let v:= (goR p x); have hx(a:Flavor 6)(x:Label 9): (leftA p a x).val= flipU a x.val:= by simp only [leftA,LinearMap.sub_apply,Module.End.one_apply,LinearEquiv.coe_coe,Submodule.coe_sub,p.flavorActs]
      have ht(a:Flavor 6)(x:Label 9): (subA p a x).val=subU a x.val:=by simp only [subA,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,LinearEquiv.coe_coe, Submodule.coe_sub, Submodule.coe_smul,p.flavorActs]
      have he:v.val=oily x.val:=by unfold v goR; change (subA p 0 (subA p 1 (subA p 2 (leftA p 0 (leftA p 1 (leftA p 2 x)))))).val=_; rw[ht,ht,ht,hx,hx,hx]; rfl
      have hs: v.val∈Peak:= he ▸ stockL x
      have hu: shoal (keels v.val)∈heapZ:= quotes hs
      let a:ℂ:=↑(Fintype.card (Equiv.Perm Hue)); have hA:a≠0:= Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
      have hv(y:Label 9)(i:Hue):rimP i y.val=(2:ℂ) • y.val:=by change colorAct _ _ + y.val=_; rw [((label_law _).mp y.property).2,two_smul] -- notation y.Val
      have hY: shoal v.val=a • v.val:=by unfold shoal; simp only [LinearMap.sum_apply,fun j=> ((label_law _).mp v.property).2 (shrine j), sum_const, card_univ]; exact (Nat.cast_smul_eq_nsmul ℂ ..).symm
      unfold keels at hu; simp only [Module.End.mul_apply,hv,map_smul,hY] at hu
      simpa only [heapZ.smul_mem_iff hA, heapZ.smul_mem_iff (two_ne_zero (α:=ℂ))] using hu
variable (w:Label 9)(u:ℂ)(b:Flavor 6)
local notation "p"=> P.sym
include T
lemma nightLeft(x:K.W)(h:q w=u • x)(hx:∀ y, T.flavor y x=Pearl.lit y • x)(ht:Pearl.lit (clipF b)= -1): q (leftA P.sym b w)= (u*(-1-1)) • x:=by
      change q ((P.sym.flavor _ (clipF b) w) - w)=_; rw [show q ((P.sym.flavor _ (clipF b) w)-w)=_ from map_sub q (P.sym.flavor _ (clipF b) w) w,← T.f,h,map_smul,hx,ht]; module
lemma nightRight(x:K.W)(h:q w=u • x)(hx:∀ y,T.flavor y x=Pearl.lit y • x)(ht:Pearl.lit (ic b)=Complex.I): q (subA P.sym b w)= (u*(Complex.I- - Complex.I)) • x:=by change q ((P.sym.flavor _ (ic b) w) - (-Complex.I) • w) =_; rw [show q ((P.sym.flavor _ (ic b) w) - (-Complex.I) • w) =_ from map_sub q (P.sym.flavor _ (ic b) w) ((-Complex.I) • w),← T.f,map_smul,h,map_smul,hx,ht]; module
include J JQ
lemma cometZ: ∃ i j k: Pinor,q (rock i j k)≠0:=by
     let F:= X.frame 0 9; let z:=rock 0 0 0; let v:K.W := (F (projection z)).val; have hv: v≠0:=by intro hz; exact UV.Free.Harbor.pearl_visible 0 0 0 (F.injective (show F _=F 0 from (Subtype.ext hz).trans (map_zero F).symm))
     have h : v∈ K.level 9:= Subtype.property (F _); rw [← JQ.h.tops none] at h; obtain ⟨y,(hy:q y=v)⟩:= h; have hp(w:FlavorTorus): T.flavor w v=Pearl.lit w • v:=by
           rw [show T.flavor w v = _ from (X.leaders 0 9).turns z w]; rw [show P.sym.flavor 9 w z=_ from rockF 0 0 0 p w,map_smul,map_smul,Submodule.coe_smul]
     let t:=-1-(1:ℂ); let s:=(Complex.I- -Complex.I); let w:= goR P.sym y
     have h₀:= nightLeft (T:=T) y 1 2 v (show q y=(1:ℂ) • v from by rw[one_smul,hy]) hp (by norm_num [Pearl.lit,clipF,mnA,Fin.ext_iff])
     have h₁:= nightLeft (T:=T) _ _ 1 v h₀ hp (by norm_num[Pearl.lit,clipF,mnA,Fin.ext_iff]); have h₂:=nightLeft (T:=T) _ _ 0 v h₁ hp (by norm_num [Pearl.lit,clipF,mnA,Fin.ext_iff]); have h₃:= nightRight (T:=T) _ _ 2 v h₂ hp (by norm_num [Pearl.lit,ic,Fin.ext_iff]); have h₄:= nightRight (T:=T) _ _ 1 v h₃ hp (by norm_num [Pearl.lit,ic,Fin.ext_iff]); have h₅:q w=(1*t*t*t*s*s*s) • v:= nightRight (T:=T) _ _ 0 v h₄ hp (by norm_num[Pearl.lit,ic,Fin.ext_iff])
     have ht:t≠0:=by norm_num[t]
     have hs:s≠0:=by unfold s; intro h; have he:=congr_arg Complex.im h; norm_num at he
     have hc : q w≠0:= by rw [h₅]; exact smul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero one_ne_zero ht) ht) ht) hs) hs) hs) hv
     by_contra! hN; have he: heapZ≤ (LinearMap.ker q).map (labels 9).subtype := Submodule.span_le.mpr fun _ ⟨⟨i,j,k⟩,e⟩=>⟨rock i j k,hN ..,e⟩
     obtain ⟨x,hv,hx⟩:= he (hull P.sym y); exact hc (show q w=0 from Eq.subst (motive:=fun v:Label 9=>q v=0) (Subtype.ext hx : x=w) hv)
lemma oddL : ∃ i j k:Pinor,∃ x:Label 9,x.val = UV.baryon i j k∧ (equip T ρ A.jet).quotient none 9 x ≠0 ∧ (equip T ρ A.jet).homogeneous true ((equip T ρ A.jet).quotient none 9 x)∧∀ y:FlavorTorus,(equip T ρ A.jet).flavor y ((equip T ρ A.jet).quotient none 9 x)=Pearl.lit y • (equip T ρ A.jet).quotient none 9 x:=by
      obtain ⟨i,j,k,he⟩:=cometZ J JQ; exact ⟨i,j,k,rock i j k,rfl,he, (show T.parity _= -_ from (T.p ..).trans (by rw [rockW]; exact map_neg q (rock i j k))), fun y=> (T.f ..).trans (by rw[rockF,map_smul])⟩
end YM.Mako
#print axioms YM.Mako.oddL
