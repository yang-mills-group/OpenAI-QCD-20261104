import YM.Mako.Reef
import YM.Mako.Flight
set_option maxHeartbeats 650000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Vern Module
open scoped Topology Classical BigOperators
variable {W V:Type*} [NormedAddCommGroup W][NormedSpace ℂ W][FiniteDimensional ℂ W]
variable [AddCommGroup V][Module ℂ V][FiniteDimensional ℂ V]
local notation "M"=> W →ₗ[ℂ] V
variable {ι:Type*}(F:ℕ→ W≃ₗ[ℂ]V) (g:ι→ End ℂ W)(G:ι→ End ℂ V)
variable (h:∀ j:ι,∀ x:W,Tendsto (fun i:ℕ=>(F i).symm (G j (F i x))) atTop (𝓝 (g j x)))
def Pace (u:ℕ→ W→ₗ[ℂ] V) (v:End ℂ W) :Prop:=∀ x:W,Tendsto (fun i:ℕ=>(F i).symm (u i x)) atTop (𝓝 (v x))
include h
lemma port (z:End ℂ M)(hp:Fet (range fun i=> power (g i) (G i)) z) (u:ℕ→ W→ₗ[ℂ]V)(v:W→ₗ[ℂ] W)(hu:Pace F u v):∃ a:End ℂ W,Pace F (fun i=> z (u i)) a ∧ ((v=1∨v=0) →a=0):=by
     induction hp generalizing u v with
     | mem a ha=>
         obtain ⟨j,rfl⟩:=ha
         let Tt(i:ℕ):End ℂ W:= (F i).symm.toLinearMap ∘ₗ G j ∘ₗ (F i).toLinearMap; refine ⟨clip (g j) v,fun x=>?_,?_⟩
         · let X(i):=(F i).symm (u i x); have hp:= Iceberg.follows_L Tt (g j) (h j) _ _ (hu x); apply (hp.sub (hu (g j x))).congr'; apply Eventually.of_forall; intro i; dsimp only; rw[power_app,map_sub]; unfold Tt; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
         rintro (rfl|rfl) <;> simp [clip]
     | zero=> exact ⟨0,fun x=>by simpa using tendsto_const_nhds (x:=(0:W)),fun _=>rfl⟩
     | times a b _ _ h ih=>
           obtain ⟨y,hy,hh⟩:= ih u v hu; obtain ⟨B,H,hp⟩:= h _ y hy; exact ⟨B,H,fun hx=>hp (Or.inr (hh hx))⟩
     | add a b _ _ h ih=>
           obtain ⟨y,hy,ht⟩:= h u v hu; obtain ⟨X,hX,hZ⟩:= ih u v hu; refine ⟨y+X,fun x=>?_,fun ha=>?_⟩; · simp_rw [LinearMap.add_apply,map_add]; exact (hy x).add (hX x)
           rw [ht ha,hZ ha,add_zero]
     | smul r a _ h =>
           obtain ⟨y,H,hp⟩:= h u v hu; refine ⟨r • y,fun x=>?_,fun ha=>?_⟩; · simp_rw[LinearMap.smul_apply,map_smul]; exact tendsto_const_nhds.smul (H x)
           rw[hp ha,smul_zero]
lemma pulse (z:End ℂ M)(hp:Fet (range fun i=> power (g i) (G i)) (z-1)): Pace F (fun t=> z (F t).toLinearMap) 1:=by
     let u(t:ℕ):= (F t).toLinearMap; obtain ⟨a,ha,hA⟩:= port F g G h (z-1) hp u 1 (fun x=>by simpa [u] using (tendsto_const_nhds (x:=x))); have hf:=hA (Or.inl rfl); intro x; have hv:=ha x; simp only [hf,LinearMap.zero_apply, LinearMap.sub_apply,u,map_sub,End.one_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hv; exact (tendsto_sub_nhds_zero_iff.mp hv) -- is lemma?
omit h
lemma earns_h (u:ℕ→ W→ₗ[ℂ]V)(h:Pace F u 1): ∀ᶠ k in atTop, Bijective (u k):=by
     let B:= finBasis ℂ W; let U(k:ℕ):End ℂ W:= (F k).symm.toLinearMap ∘ₗ u k; let Tt(k:ℕ):= LinearMap.toMatrix B B (U k); have hx:Tendsto Tt atTop (𝓝 (LinearMap.toMatrix B B (1: End ℂ W))):= by
            refine tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mpr fun j=>?_); unfold Tt; simp_rw [LinearMap.toMatrix_apply]; exact ((B.coord i).continuous_of_finiteDimensional.continuousAt.tendsto.comp (h (B j)))
     rw[LinearMap.toMatrix_one] at hx; have he := ((show Continuous fun x:Matrix (Fin (finrank ℂ W)) (Fin (finrank ℂ W)) ℂ=>x.det from continuous_id.matrix_det).continuousAt.tendsto.comp hx); rw [Matrix.det_one] at he
     filter_upwards [he.eventually_ne one_ne_zero] with i hi; let X:= LinearEquiv.ofIsUnitDet (v:=B) (v':=B) (f:=U i) (isUnit_iff_ne_zero.mpr hi); let A:=X.trans (F i); refine (show u i = A.toLinearMap from ?_) ▸ (show Bijective (A.toLinearMap) from A.bijective); ext1 x; apply (F i).symm.injective; change _= (F i).symm (F i (X x)); rw[LinearEquiv.symm_apply_apply]; exact DFunLike.congr_fun (show X.toLinearMap=U i from LinearEquiv.coe_ofIsUnitDet _).symm x
lemma uturn(L:ℕ→W≃ₗ[ℂ] V)(h:∀ x:W,Tendsto (fun i=> (F i).symm (L i x)) atTop (𝓝 x)):∀ x:W, Tendsto (fun i=> (L i).symm (F i x)) atTop (𝓝 x):=by
    intro x; let u(t:ℕ) := (L t).trans (F t).symm; let v:=fun t=> (u t).symm x; change Tendsto v atTop (𝓝 x)
    let B:=finBasis ℂ W; refine Iceberg.costW (fun j k=>B.coord j ∘ₗ (u k).toLinearMap) B.coord ?_ ?_ v x ?_
    · intro i p; exact (B.coord i).continuous_of_finiteDimensional.continuousAt.tendsto.comp (h p)
    · intro v h; rw[←B.sum_repr v]; change ∑ i,(B.coord i v) • _= _; simp[h]
    intro i; apply tendsto_const_nhds.congr'; apply Eventually.of_forall; intro k; change _= B.coord i (u k (v k)); unfold v; rw[LinearEquiv.apply_symm_apply]
end YM.Mako
#print axioms YM.Mako.pulse
#print axioms YM.Mako.earns_h
#print axioms YM.Mako.uturn
