import YM.QCD.Sparks.Electric

/-! # Outer-root laws for canonical vertices
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Cost Run Revolve Metric Push.Uniform
open Eyrie Quarry Tree RG Precision Rudder Flume Pine Finset Set
open YM.Further.PhysicalPeriodLimitF933 Macrame Jacobi Stationary Tavern
open scoped Topology Matrix BigOperators Classical ContDiff
section useMat
open scoped Matrix.Norms.Frobenius
lemma regard_arm {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{n:Side} (b:X→Lat.Frame n)(h:Army b 0)(i:Site n)(a c : Hue): ContDiffAt ℝ ω (fun x=>colour (b x i) a c) 0:=by
  let L : su.Mat →ₗ[ℝ] ℂ:= { toFun:=fun z=>z a c,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}; exact L.toContinuousLinearMap.contDiff.contDiffAt.comp _ (h i)
end useMat
open scoped Matrix.Norms.L2Operator
variable {c C n N: Side} {k m M:ℕ} {P:SparkMesh}
structure Priest (F:trackG n) : Prop where
  ready : ContDiffAt ℝ ω F 0
  covenant (x : Site n) : ∃ d:Site n→ℂ, Quaint (parallel x) d ∧
    ∀ᶠ U in 𝓝 0,F (spaceShift x U)*stream (parallel x) d= stream (parallel x) d*F U
  color (u:su.El): ∀ᶠ U in 𝓝 0,F (stain u U) = aura (siteRot (fun _=>u)) (F U)
  forced : ∀ᶠ z : Swatch su n in 𝓝 0,F (moveField z)=aura (siteRot (switchSite z.1)) (F z.2)

structure Clan (S:SparkMesh) (F:S.Field) : Prop where
  way i: Priest (F i)
  order i j (h:i≤j) : ∃ (d : Site (S.n j)→ℂ), Quaint (S.vista i j h) d ∧
    ∀ᶠ x in 𝓝 0,F j (expandC (S.vista i j h) x) * stream (S.vista i j h) d=stream (S.vista i j h) d * F i x

variable {J : trackG n}
def EmptyThrough (F:trackG n)(k:ℕ): Prop:= ∀ i:ℕ,i<k→iteratedFDeriv ℝ i F 0=0

def surge {k:ℕ} (J:trackG n)(x:Fin k→Cnr n):=iteratedFDeriv ℝ k J 0 x
lemma surge_stain (h:Priest J)(x:Fin k→Cnr n)(u:su.El): surge J (stain u ∘ x)=aura (siteRot (fun _=>u)) (surge J x):=by
  let H :=siteRot (fun _:Site n=>u); let L: Sheet n→L[ℝ] Sheet n:=LinearMap.toContinuousLinearMap {
    toFun:=aura H,map_add':=fun x y=>aura_add ..,map_smul':=fun x y=>by unfold aura; rw [Matrix.mul_smul,Matrix.smul_mul]; rfl }
  have he: (J ∘ stain u)=ᶠ[𝓝 0] L∘J:= h.color u
  have ht: iteratedFDeriv ℝ k (J ∘ stain u) 0 x=iteratedFDeriv ℝ k (L ∘ J) 0 x:=by rw [(he.iteratedFDeriv ℝ _).eq_of_nhds]
  have hy : ContDiffAt ℝ k J (stain (m:=n) u 0):= by rw [map_zero]; exact h.ready.of_le le_top
  rw [iter_lin_at (L:=stain u) hy,map_zero, L.iteratedFDeriv_comp_left h.ready le_top] at ht; exact ht

-- boundary Ward uses product at variable, charge when F(root field) vanishes thru k-1.
lemma station_spin {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (b:X→Lat.Frame n) (h:Army b 0):
    ContDiffAt ℝ ω (fun z=> siteRot (b z)) 0:=by
  apply matrix_g; rintro ⟨i,a,e⟩ ⟨j,c,d⟩
  unfold siteRot touch
  simp_rw [rr]; simp only [Equiv.refl_apply]; split
  · simp_rw [Matrix.kroneckerMap_apply]
    exact ContDiffAt.mul (𝕜:=ℝ) contDiffAt_const (regard_arm b h i e d)
  exact contDiffAt_const

lemma move_left (v: BaseSites su n)(x:Cnr n) : fderiv ℝ (moveField) 0 (v,x)=x-gradientA su n v:=moveField_rate _
lemma paidWard (h:Priest J)(he : EmptyThrough J k)(hk:k≤2)(v : Fin k→BaseSites su n)(x:Fin k→Cnr n):
    surge J (fun i=> x i-gradientA su n (v i))=surge J x :=by
  let g := fun y:Swatch su n=>J y.2
  let c := fun y:Swatch su n=> siteRot (switchSite y.1)
  have H:=h.forced
  have hh : J ∘ moveField (m:=n) (G:=su)=ᶠ[𝓝 0] (fun z=> c z*g z*star (c z)):=H
  let L := ContinuousLinearMap.snd ℝ (BaseSites su n) (Cnr n)
  have h0 : L 0=0:=map_zero _
  have hg : ContDiffAt ℝ ω g 0:= h.ready.comp (f:=Prod.snd) 0 contDiffAt_snd
  have hc : ContDiffAt ℝ ω c 0:= station_spin _ (Army.powG (v:=Prod.fst) contDiffAt_fst)
  have hT: c 0=1:=by unfold c; rw [Prod.fst_zero,switch_zero,rot_one]
  have hs : ContDiffAt ℝ ω (fun x=>star (c x)) 0:= (show Sheet n ≃L[ℝ] Sheet n from starL ℝ).contDiff.contDiffAt.comp (f:=c) _ hc
  let w i:Swatch su n:=(v i,x i)
  have hw := DFunLike.congr_fun ((hh.iteratedFDeriv ℝ k).eq_of_nhds) w
  rw [quiet_comp _ moveField_analytic (by rw [moveField_zero]; exact h.ready.analyticAt) (fun i hi _=> by rw [moveField_zero]; exact he i hi),moveField_zero] at hw
  have he1: fderiv ℝ moveField (0:Swatch su n) ∘ w=(fun i=> x i-gradientA su n (v i)):= funext fun i=>move_left ..
  rw [he1] at hw; unfold surge; refine hw.trans (Eq.trans ?_ (show iteratedFDeriv ℝ k g 0 w=_ from ?_))
  swap
  · rw [show g=J∘ ⇑L from rfl,iter_lin_at (L:=L) (by rw [map_zero]; exact h.ready.of_le le_top),map_zero]; rfl
  have hn q (v:Fin q→ Swatch su n)(hi:q<k) : iteratedFDeriv ℝ q g 0 v=0:=by
    unfold g; change iteratedFDeriv ℝ q (J∘ ⇑L) _ _= _; rw [iter_lin_at (L:=L) (by rw [map_zero]; exact h.ready.of_le le_top),map_zero,he _ hi]; rfl
  generalize hd : (fun z=> star (c z))=V at hs
  change iteratedFDeriv ℝ k ((c*g)*(star c)) _ _= _; have hv : V=star c:=hd.symm
  interval_cases k
  · rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply]; simp [hT]
  · have hG : g 0=0:=by simpa only [iteratedFDeriv_zero_apply] using hn 0 ![] (by omega)
    simp only [iteratedFDeriv_one_apply]; change blade _ (fun x=> c x*g x*(star c) x) _ = _
    rw [made _ (hc.mul hg) (hv ▸ hs),made _ hc hg]; simp [hT,hG]
  have hG : g 0=0:=by simpa only [iteratedFDeriv_zero_apply] using hn 0 ![] (by omega)
  have hF (p:Swatch su n): blade p g 0=0:=by simpa [blade] using hn 1 ![p] (by omega)
  let C:=fun y=>c y*g y; have hc' : ContDiffAt ℝ ω C 0:=hc.mul hg; have hx : V 0=1:=by rw [hv]; change star (c 0)=_; rw [hT,star_one]
  rw [← hv]; change iteratedFDeriv ℝ 2 (fun x=> C x*V x) _ _= _
  rw [show w=![w 0,w 1] from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩),← iter _ _ (show ContDiffAt ℝ ω (fun x=> C x*V x) 0 from hc'.mul hs), ← iter _ _ hg]
  rw [rotate_area _ _ hc' hs]; unfold C at *; rw [rotate_area _ _ hc hg,made _ hc hg,made _ hc hg]; simp [hG,hT,hF,hx]
end YM.QCD.Sparks
