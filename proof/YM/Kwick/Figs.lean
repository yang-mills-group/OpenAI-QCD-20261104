import YM.Kwick.Bower
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.TableT Tawny.Pane Tawny.BendR -- Bend?
open Oriole Counting Counting.Click PCAC Patria.Gall.Seals Patria.Gall
local notation "Z"=> RawVec 10
variable (x y:Z)(p q:Multi 10)(a b:Flavor 6)(j t:Fiber)
local notation "B"=> bee
local notation "L₀"=> (0:Multi 10)
local notation "Ξ"=> leadR
-- lower Φ1 uses actual sign.Be lane foils
lemma coinedP : chipK p q a (x.val (0:Axis))=wave (qv a p q x):=by
     let v:=x.val (0:Axis); have hh : Quiet v.val:= (show Meaning _ _ _ _ _ _ from x.property).light _; have he: Oriole.prism a a p q (skin 0 v.val) = _ := root_color a a p q v hh (by decide); exact he -- order
lemma trophy : (truck (qv a p q x))= qv a q p x:=let ht:=show Meaning _ _ _ _ _ _ from x.property; roleL a p q _ _ _ _ x (by decide) 0 -- namespace
local notation "G0"=> gamma (0:Axis) * gamma 1
variable (u:Values 7)(c:Fin 3→ℂ)
lemma us1 : lookB (plaza (u,c)) a (j,t)= (-2:ℂ)*(u a 1)*(wave (G0)) j t:=by
    let P:= plaza (u,c); change point1 1 a j t (P.val _) = _; unfold point1; rw [LinearMap.sub_apply]; change chipK (Ξ 1) L₀ a (P.val (0:Axis)) j t-chipK L₀ (Ξ 1) a (P.val (0:Axis)) j t=_; have hh : qv a L₀ (Ξ 1) P=u a 1 • (G0) := (life_v a u c).2.1; rw[coinedP,coinedP,← trophy, hh, truck_v,truck_double (0:Axis) 1 (by decide)]; simp only[wave,Matrix.smul_kronecker,Matrix.smul_apply, Matrix.neg_apply]; simp; ring
local notation "W"=> Values 7
local notation "F₀"=>Flavor 6→ℂ
lemma wind_h : ∃ j t:Fiber, (wave (G0)) j t≠0:=by
     have hz: wave (G0) ≠0:=by
          intro h'; have ht: (wave (G0))*wave (gamma 1*gamma (0:Axis))=1:=by rw[wave_mul,mul_assoc (gamma 0), ←mul_assoc (gamma 1), gamma_sq,one_mul, gamma_sq, wave_one]
          rw [h',zero_mul] at ht; exact zero_ne_one ht
     by_contra! h; exact hz (by ext i j; exact h _ _)
noncomputable def ax1:= wind_h.choose
noncomputable def ax2:= wind_h.choose_spec.choose
noncomputable def pay1 : Memory →ₗ[ℂ](Flavor 6→ℂ):= ((-(2:ℂ)*wave (G0) ax1 ax2)⁻¹) • LinearMap.pi (fun i=>(LinearMap.proj (ax1,ax2)) ∘ₗ LinearMap.proj i)
lemma paysU : pay1 (lookB (plaza (u,c)))=fun i:Flavor 6=> u i 1 :=by
     funext i; change (-(2:ℂ)*wave (G0) ax1 ax2)⁻¹ * lookB _ i (ax1,ax2)=u i 1; rw [us1]; have he : wave (G0) ax1 ax2 ≠0:= wind_h.choose_spec.choose_spec; field_simp -- maybe ring
noncomputable def bodyS : Z→ₗ[ℂ](Values 7 × (Fin 3 →ℂ)):= (LinearEquiv.ofBijective TableT.plaza certified).symm.toLinearMap
lemma bodyι: bodyS (plaza (u,c))=(u,c):=(LinearEquiv.ofBijective ..).symm_apply_apply _ -- inverse ordering
noncomputable def axM (k:Fin 7): Z →ₗ[ℂ](Flavor 6→ℂ):= LinearMap.pi fun i:Flavor 6=> (LinearMap.proj k) ∘ₗ LinearMap.proj i ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ bodyS
lemma baseA : pay1 ∘ₗ lookB=axM 1:=by apply LinearMap.ext; intro i; obtain ⟨⟨f,s⟩,rfl⟩:= certified.2 i; funext j; change pay1 (lookB _) j=((bodyS (plaza (f,s))).1 j 1); rw [paysU, bodyι]
lemma βread (x:Z): (axM 1) (bet 0 x)=axM 1 x ∧ (axM 0) (bet 0 x)=axM 0 x:=by
     obtain ⟨⟨f,p⟩,rfl⟩:=certified.2 x; unfold bet; rw [vaultE]; constructor; all_goals ext1 j; change (bodyS _).1 _ _=(bodyS _).1 _ _; rw [bodyι,bodyι]; simp [tierQ,τ7]
-- choose U2 scaled by t..Gpick. Want dominance with high columns. formula decomposition.
local notation "G1"=> Zinc.whirl Gpick (gamma (1:Axis))
lemma trad : ∃ j t:Fiber, G1 j t≠0:= by by_contra! h; exact charged_r (detected _ h)
noncomputable def aux1:= trad.choose
noncomputable def aux2:=trad.choose_spec.choose
noncomputable def pay2 : Memory →ₗ[ℂ] (Flavor 6→ℂ):= (G1 aux1 aux2)⁻¹ • LinearMap.pi fun i:Flavor 6=> LinearMap.proj (aux1,aux2) ∘ₗ LinearMap.proj i
lemma pays2 : pay2 (lookQ (Zinc.starV a))= Pi.single a 1:=by
     funext i; change (G1 aux1 aux2)⁻¹* seekC i aux1 aux2 _=_; rw[selected]; by_cases h:i=a; · rw [if_pos h,h,Pi.single_eq_same]; exact inv_mul_cancel₀ trad.choose_spec.choose_spec
     rw [if_neg h,mul_zero,Pi.single_eq_of_ne h]
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.baseA
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.pays2
