import YM.Oriole.Stoop
/-! converge μ of charged direction VISA on projection. norms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open Function Lattice RG Wilson Filter Finset
open scoped BigOperators ContDiff Topology Matrix Matrix.Norms.L2Operator Classical
variable {c:Side}{n k:ℕ}
open UV PCAC QCD QCD.Lat QCD.Grass SourceRead Patria Patria.Depth Patria.Rolls Cylinder Massive.Poised Plans Stamp
variable (p q:Flavor 6)(i:Axis)(M:Spike)
noncomputable def achromatic : Submodule ℂ (Label 8) where
 carrier:={x| CharmC p q x.val}
 zero_mem' := fun i=> by change flavorAct i 0= _ • (0:Pol 8); rw [map_zero,smul_zero]
 add_mem' := by intro x y hx hy i; change flavorAct i (x.val + y.val) = _ • (x.val+y.val); exact (map_add ..).trans ((congr_arg₂ HAdd.hAdd (hx i) (hy i)).trans (smul_add ..).symm)
 smul_mem' := by intro v x hx u; change flavorAct u (v • x.val)= _ • (v • x.val); rw [map_smul,hx u, smul_comm]
lemma chroma : stereo p q i M∈achromatic p q:=by
     let X:= UV.bilinear (d:=8) p q M (UV.first i) 0; let Y:= UV.bilinear (d:=8) p q M 0 (UV.first i)
     exact (achromatic p q).add_mem (show satin _ _ _ _ M (show _ from (by rw[juicy,cost_root]))∈achromatic p q from charm p q (UV.first i) 0 _) (show satin _ _ _ _ M (show _ from (by rw[cost_root,juicy]))∈achromatic p q from charm p q 0 (UV.first i) _)
abbrev Carton:= SpinMode 8 × SpinMode 8
noncomputable def rate (p q: Flavor 6): Label 8→L[ℂ](Carton→ℂ):= LinearMap.toContinuousLinearMap { toFun:=fun x z=> juncoat x.val z.1 z.2,map_add':=fun x y=> funext fun z=>congr_fun (congr_fun (map_add juncoat x.val y.val) z.1) z.2,map_smul':=fun c x=> funext fun z=> congr_fun (congr_fun (map_smul juncoat c x.val) z.1) z.2 }
local notation "A" => achromatic p q
local notation "T" => Lat.Fiber
lemma accordP (hp:p≠q):∃ K:ℝ,0 ≤ K ∧ ∀ (x:A)(C:ℝ),0 ≤ C → (∀ (X Y: Multi 8), heart X Y →∀ i j:T,‖Oriole.prism p q X Y (juncoat x.val.val) i j‖ ≤ C) → ‖x.val‖≤ K*C:=by
     let f:=rate p q
     let L:= (rate p q).comp ((achromatic p q).subtypeL)
     have hz: ∀ x:A,L x=0→ x=0:=by
          intro x hx; apply Subtype.ext; apply Subtype.ext
          obtain ⟨hf,hp⟩:= feathers p q x.val le_rfl hp x.prop; change x.val.val=0; have h : juncoat x.val.val=0:=by ext i j; exact congr_fun hx (i,j)
          rw [← hf,h,map_zero]
     obtain ⟨K,hK,h⟩:= Massive.Poised.Costs.budget_probes (ι:=Unit) (fun _=>L.restrictScalars ℝ) (fun x hx=>hz x (hx ())) (fun _=>1) (fun _=>zero_le_one)
     refine ⟨K,hK.le,fun x C hc hx=> h C hc x ?_⟩; intro i; rw [one_mul]; let D:= juncoat x.val.val; change ‖L x‖ ≤ C; apply (pi_norm_le_iff_of_nonneg hc).mpr; intro a; change ‖D a.1 a.2‖≤ C; by_cases hu:D a.1 a.2=0; rw [hu,norm_zero]; exact hc
     obtain ⟨he,hm,hp⟩:= (feathers p q x.val le_rfl hp x.prop).2 a.1 a.2 hu; refine le_trans (le_of_eq (show ‖D a.1 a.2‖= ‖Oriole.prism p q a.1.1.1 a.2.1.1 D a.1.1.2 a.2.1.2‖ from ?_)) (hx _ _ hp _ _); unfold Oriole.prism; rw[Matrix.of_apply]; apply congr_arg; rw [show ((a.1.1.1,a.1.1.2),p) = a.1 from Prod.ext rfl he.symm, show ((a.2.1.1,a.2.1.2),q)=a.2 from Prod.ext rfl hm.symm]
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.accordP
